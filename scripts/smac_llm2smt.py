#!/usr/bin/env python3
"""Tune llm2smt command-line options with SMAC3.

Examples:
    python scripts/make_smac_instances.py \
        sandbox/non-incremental/QF_UF/NEQ sandbox/non-incremental/QF_UF/PEQ \
        -o smac-instances/qf_uf_neq_peq.txt

    python scripts/smac_llm2smt.py evaluate \
        --solver build-workspace-rel/bin/llm2smt \
        --instance sandbox/non-incremental/QF_UF/PEQ/PEQ018_size5.smt2 \
        --config-json '{"preprocess_passes": 0}'

    python scripts/smac_llm2smt.py tune \
        --solver build-workspace-rel/bin/llm2smt \
        --instances smac-instances/qf_uf_neq_peq.txt \
        --cutoff 120 --trials 500 --workers 8 \
        --output-dir smac-runs/qf_uf_neq_peq
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


STATUS_RE = re.compile(r"^\s*\(set-info\s+:status\s+(sat|unsat|unknown)\s*\)", re.M)
VALID_RESULTS = {"sat", "unsat"}


def _as_plain_dict(config: Any) -> dict[str, Any]:
    if isinstance(config, dict):
        raw = config
    else:
        raw = dict(config)
    return {str(key): _plain_scalar(value) for key, value in raw.items()}


def _plain_scalar(value: Any) -> Any:
    if hasattr(value, "item"):
        try:
            return value.item()
        except (TypeError, ValueError):
            pass
    return value


def build_configspace(seed: int = 1):
    try:
        from ConfigSpace import (
            CategoricalHyperparameter,
            ConfigurationSpace,
            UniformIntegerHyperparameter,
        )
    except ImportError as exc:
        raise SystemExit(
            "SMAC/ConfigSpace could not be imported. Install compatible "
            "dependencies with:\n"
            "  python -m pip install -r scripts/requirements-smac.txt\n"
            f"Import error: {exc}"
        ) from exc

    cs = ConfigurationSpace(seed=seed)
    hyperparameters = [
        UniformIntegerHyperparameter("preprocess_passes", 0, 4, default_value=0),
        CategoricalHyperparameter("nary", [True, False], default_value=True),
        CategoricalHyperparameter("flatten", [True, False], default_value=True),
        CategoricalHyperparameter("nnf", [False, True], default_value=False),
        CategoricalHyperparameter("nnf_memo", [False, True], default_value=False),
        CategoricalHyperparameter("eq_bridge", [False, True], default_value=False),
        CategoricalHyperparameter("finite_domain_amo", [True, False], default_value=True),
        CategoricalHyperparameter("finite_domain_eq_defs", [True, False], default_value=True),
        CategoricalHyperparameter("theory_prop", [True, False], default_value=True),
        CategoricalHyperparameter("prop_interval", [1, 2, 4, 8, 16, 32, 64, 128],
                                  default_value=32),
        CategoricalHyperparameter("prop_assign_threshold",
                                  [0.0, 0.1, 0.25, 0.5, 0.75, 1.0],
                                  default_value=0.25),
        CategoricalHyperparameter("prop_delivery_budget",
                                  [0, 100, 500, 1000, 5000, 20000],
                                  default_value=1000),
    ]
    cs.add(hyperparameters)
    return cs


def solver_args_from_config(config: Any) -> list[str]:
    cfg = _as_plain_dict(config)
    args = ["--quiet", "--stats"]

    passes = int(cfg.get("preprocess_passes", 0))
    if passes:
        args += ["--preprocess-passes", str(passes)]

    if not bool(cfg.get("nary", True)):
        args.append("--no-nary")
    if not bool(cfg.get("flatten", True)):
        args.append("--no-flatten")
    if bool(cfg.get("nnf", False)):
        args.append("--nnf")
        if bool(cfg.get("nnf_memo", False)):
            args.append("--nnf-memo")
    if bool(cfg.get("eq_bridge", False)):
        args.append("--eq-bridge")
    if not bool(cfg.get("finite_domain_amo", True)):
        args.append("--no-finite-domain-amo")
    if not bool(cfg.get("finite_domain_eq_defs", True)):
        args.append("--no-finite-domain-eqdefs")
    if not bool(cfg.get("theory_prop", True)):
        args.append("--no-theory-prop")

    args += ["--prop-interval", str(int(cfg.get("prop_interval", 32)))]
    args += ["--prop-assign-threshold", str(float(cfg.get("prop_assign_threshold", 0.25)))]
    args += ["--prop-delivery-budget", str(int(cfg.get("prop_delivery_budget", 1000)))]
    return args


def read_instances(path: Path) -> list[str]:
    instances: list[str] = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            instances.append(line)
    if not instances:
        raise SystemExit(f"no instances in {path}")
    return instances


def instance_features(instances: list[str]) -> dict[str, list[float]]:
    denom = max(1, len(instances) - 1)
    features: dict[str, list[float]] = {}
    for idx, instance in enumerate(instances):
        try:
            size = Path(instance).stat().st_size
        except OSError:
            size = 0
        features[instance] = [idx / denom, math.log1p(size)]
    return features


def expected_status(instance: str, expected_map: dict[str, str] | None = None) -> str | None:
    if expected_map:
        path = Path(instance)
        for key in (instance, str(path), path.name):
            if key in expected_map:
                return expected_map[key]
    try:
        text = Path(instance).read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return None
    match = STATUS_RE.search(text)
    if match and match.group(1) in VALID_RESULTS:
        return match.group(1)
    return None


def parse_stats(stderr: str) -> dict[str, int]:
    stats: dict[str, int] = {}
    for line in stderr.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("[") or stripped.startswith("--"):
            continue
        parts = stripped.split()
        if len(parts) == 2 and parts[1].isdigit():
            stats[parts[0]] = int(parts[1])
    return stats


def append_jsonl(path: Path | None, record: dict[str, Any]) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    data = (json.dumps(record, sort_keys=True) + "\n").encode("utf-8")
    fd = os.open(path, os.O_APPEND | os.O_CREAT | os.O_WRONLY, 0o644)
    try:
        os.write(fd, data)
    finally:
        os.close(fd)


def _config_key(config: dict[str, Any]) -> str:
    return json.dumps(config, sort_keys=True, separators=(",", ":"))


class RunSummary:
    def __init__(self, path: Path | None = None) -> None:
        self.path = path
        self._groups: dict[str, dict[str, Any]] = {}
        self.completed_runs = 0

    def add(self, record: dict[str, Any]) -> dict[str, Any]:
        self.completed_runs += 1
        cfg = _as_plain_dict(record.get("config", {}))
        key = _config_key(cfg)
        group = self._groups.setdefault(
            key,
            {
                "config": cfg,
                "cost_total": 0.0,
                "count": 0,
                "statuses": {},
                "instances": {},
            },
        )
        cost = float(record.get("cost", 0.0))
        group["cost_total"] += cost
        group["count"] += 1
        status = str(record.get("status", "unknown"))
        group["statuses"][status] = int(group["statuses"].get(status, 0)) + 1
        instance = str(record.get("instance", ""))
        if instance:
            group["instances"][instance] = cost
        summary = self.to_dict()
        if self.path is not None:
            write_json_atomic(self.path, summary)
        return summary

    def to_dict(self) -> dict[str, Any]:
        groups = []
        for group in self._groups.values():
            count = int(group["count"])
            cost_total = float(group["cost_total"])
            cfg = _as_plain_dict(group["config"])
            groups.append(
                {
                    "avg_cost": cost_total / count if count else float("inf"),
                    "config": cfg,
                    "count": count,
                    "cost_total": cost_total,
                    "instances": dict(sorted(group["instances"].items())),
                    "solver_args": solver_args_from_config(cfg),
                    "statuses": dict(sorted(group["statuses"].items())),
                }
            )
        groups.sort(key=lambda item: (item["avg_cost"], -item["count"]))
        max_count = max((int(item["count"]) for item in groups), default=0)
        max_coverage = [item for item in groups if int(item["count"]) == max_count]
        max_coverage.sort(key=lambda item: item["avg_cost"])
        return {
            "completed_runs": self.completed_runs,
            "configs_seen": len(groups),
            "best_observed": groups[0] if groups else None,
            "best_seen_on_most_instances": max_coverage[0] if max_coverage else None,
            "configs": groups,
        }


def summarize_run_log(path: Path) -> dict[str, Any]:
    summary = RunSummary()
    if not path.exists():
        return summary.to_dict()
    for raw in path.read_text(encoding="utf-8").splitlines():
        if not raw.strip():
            continue
        try:
            record = json.loads(raw)
        except json.JSONDecodeError:
            continue
        summary.add(record)
    return summary.to_dict()


def write_json_atomic(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tmp.replace(path)


class Llm2SmtTarget:
    def __init__(
        self,
        *,
        solver: Path,
        cutoff: float,
        run_log: Path | None,
        best_observed_path: Path | None,
        expected_map: dict[str, str] | None = None,
        timeout_penalty: float = 10.0,
        wrong_penalty: float = 10.0,
        unknown_penalty: float = 10.0,
    ) -> None:
        self.solver = solver
        self.cutoff = cutoff
        self.run_log = run_log
        self.best_observed_path = best_observed_path
        self.expected_map = expected_map
        self.timeout_penalty = timeout_penalty
        self.wrong_penalty = wrong_penalty
        self.unknown_penalty = unknown_penalty

    def __call__(self, config: Any, seed: int = 0, instance: str | None = None) -> float:
        if instance is None:
            raise ValueError("SMAC did not provide an instance")
        result = evaluate_config(
            solver=self.solver,
            instance=instance,
            config=config,
            cutoff=self.cutoff,
            expected_map=self.expected_map,
            timeout_penalty=self.timeout_penalty,
            wrong_penalty=self.wrong_penalty,
            unknown_penalty=self.unknown_penalty,
        )
        result["seed"] = seed
        append_jsonl(self.run_log, result)
        if self.run_log is not None and self.best_observed_path is not None:
            write_json_atomic(self.best_observed_path, summarize_run_log(self.run_log))
        return float(result["cost"])


def evaluate_config(
    *,
    solver: Path,
    instance: str,
    config: Any,
    cutoff: float,
    expected_map: dict[str, str] | None,
    timeout_penalty: float,
    wrong_penalty: float,
    unknown_penalty: float,
) -> dict[str, Any]:
    cfg = _as_plain_dict(config)
    cmd = [str(solver)] + solver_args_from_config(cfg) + [instance]
    started = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=cutoff)
    except subprocess.TimeoutExpired:
        timed_out = True
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=2.0)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            stdout, stderr = proc.communicate()
    elapsed = time.monotonic() - started

    lines = [line.strip() for line in stdout.splitlines() if line.strip()]
    answer = lines[-1] if lines else ""
    expected = expected_status(instance, expected_map)
    stats = parse_stats(stderr)
    status = "ok"
    cost = elapsed

    if timed_out:
        status = "timeout"
        cost = cutoff * timeout_penalty
    elif proc.returncode != 0:
        status = "error"
        cost = cutoff * wrong_penalty
    elif answer == "unknown":
        status = "unknown"
        cost = cutoff * unknown_penalty
    elif answer not in VALID_RESULTS:
        status = "bad-output"
        cost = cutoff * wrong_penalty
    elif expected is not None and answer != expected:
        status = "wrong-answer"
        cost = cutoff * wrong_penalty

    return {
        "answer": answer,
        "cmd": cmd,
        "config": cfg,
        "cost": cost,
        "elapsed": elapsed,
        "expected": expected,
        "instance": instance,
        "returncode": proc.returncode,
        "stats": stats,
        "status": status,
        "timed_out": timed_out,
    }


def load_expected_map(path: Path | None) -> dict[str, str] | None:
    if path is None:
        return None
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise SystemExit("--expected-json must contain a JSON object")
    return {str(k): str(v) for k, v in data.items()}


def cmd_evaluate(args: argparse.Namespace) -> int:
    result = evaluate_config(
        solver=args.solver,
        instance=args.instance,
        config=json.loads(args.config_json),
        cutoff=args.cutoff,
        expected_map=load_expected_map(args.expected_json),
        timeout_penalty=args.timeout_penalty,
        wrong_penalty=args.wrong_penalty,
        unknown_penalty=args.unknown_penalty,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result["status"] == "ok" else 1


def cmd_summarize(args: argparse.Namespace) -> int:
    summary = summarize_run_log(args.run_log)
    if args.output is not None:
        write_json_atomic(args.output, summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0 if summary["completed_runs"] else 1


def cmd_tune(args: argparse.Namespace) -> int:
    try:
        from smac import HyperparameterOptimizationFacade, Scenario
    except ImportError as exc:
        raise SystemExit(
            "SMAC could not be imported. Install compatible dependencies with:\n"
            "  python -m pip install -r scripts/requirements-smac.txt\n"
            f"Import error: {exc}"
        ) from exc

    dask_client = None
    if args.workers > 1:
        try:
            from distributed import Client
        except ImportError as exc:
            raise SystemExit(
                "Parallel SMAC runs require dask.distributed. Install compatible "
                "dependencies with:\n"
                "  python -m pip install -r scripts/requirements-smac.txt\n"
                f"Import error: {exc}"
            ) from exc

    instances = read_instances(args.instances)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    cs = build_configspace(seed=args.seed)
    walltime_limit = float("inf") if args.walltime_limit <= 0 else float(args.walltime_limit)
    scenario = Scenario(
        cs,
        deterministic=True,
        instances=instances,
        instance_features=instance_features(instances),
        n_trials=args.trials,
        n_workers=1 if args.workers > 1 else args.workers,
        seed=args.seed,
        output_directory=str(args.output_dir),
        walltime_limit=walltime_limit,
    )

    if args.workers > 1:
        # SMAC creates a process-based Dask client by default and closes it from
        # DaskParallelRunner.__del__.  On some servers that close can time out
        # during interpreter shutdown.  Owning a threaded client here is enough
        # because each target evaluation launches llm2smt as a subprocess, and
        # it lets us close Dask deterministically before exiting.
        dask_client = Client(
            n_workers=args.workers,
            threads_per_worker=1,
            processes=False,
            local_directory=str(args.output_dir),
        )

    evaluator = Llm2SmtTarget(
        solver=args.solver,
        cutoff=args.cutoff,
        run_log=args.output_dir / "llm2smt-runs.jsonl",
        best_observed_path=args.output_dir / "best-observed.json",
        expected_map=load_expected_map(args.expected_json),
        timeout_penalty=args.timeout_penalty,
        wrong_penalty=args.wrong_penalty,
        unknown_penalty=args.unknown_penalty,
    )

    def target(config: Any, seed: int = 0, instance: str | None = None) -> float:
        return evaluator(config, seed=seed, instance=instance)

    smac = HyperparameterOptimizationFacade(
        scenario,
        target,
        dask_client=dask_client,
        overwrite=args.overwrite,
    )
    incumbent = None
    interrupted = False
    try:
        incumbent = smac.optimize()
    except KeyboardInterrupt:
        interrupted = True
        print("Interrupted; writing best-observed summary from completed runs.", file=sys.stderr)
    finally:
        if dask_client is not None:
            try:
                dask_client.close(timeout=10)
            except TypeError:
                dask_client.close()
            except Exception as exc:
                print(f"warning: failed to close Dask client cleanly: {exc}", file=sys.stderr)

    observed_summary = summarize_run_log(args.output_dir / "llm2smt-runs.jsonl")
    write_json_atomic(args.output_dir / "best-observed.json", observed_summary)

    incumbent_dict = _as_plain_dict(incumbent) if incumbent is not None else None
    incumbent_args = solver_args_from_config(incumbent_dict) if incumbent_dict is not None else None
    summary = {
        "incumbent": incumbent_dict,
        "solver_args": incumbent_args,
        "best_observed": observed_summary.get("best_observed"),
        "best_seen_on_most_instances": observed_summary.get("best_seen_on_most_instances"),
        "completed_runs": observed_summary.get("completed_runs", 0),
        "interrupted": interrupted,
        "solver": str(args.solver),
        "cutoff": args.cutoff,
        "trials": args.trials,
        "walltime_limit": args.walltime_limit,
        "workers": args.workers,
        "instances": instances,
    }
    write_json_atomic(args.output_dir / "incumbent.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 130 if interrupted else 0


def add_common_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--solver", type=Path, default=Path("build/bin/llm2smt"),
                        help="llm2smt binary")
    parser.add_argument("--cutoff", type=float, default=120.0,
                        help="per-run timeout in seconds")
    parser.add_argument("--expected-json", type=Path,
                        help="optional mapping from instance path or basename to sat/unsat")
    parser.add_argument("--timeout-penalty", type=float, default=10.0,
                        help="cost multiplier for timeouts")
    parser.add_argument("--wrong-penalty", type=float, default=10.0,
                        help="cost multiplier for crashes and wrong answers")
    parser.add_argument("--unknown-penalty", type=float, default=10.0,
                        help="cost multiplier for unknown")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    eval_parser = sub.add_parser("evaluate", help="run one configuration on one instance")
    add_common_args(eval_parser)
    eval_parser.add_argument("--instance", required=True, help="SMT2 instance")
    eval_parser.add_argument("--config-json", default="{}",
                             help="JSON object with configuration values")
    eval_parser.set_defaults(func=cmd_evaluate)

    tune_parser = sub.add_parser("tune", help="run SMAC optimization")
    add_common_args(tune_parser)
    tune_parser.add_argument("--instances", type=Path, required=True,
                             help="instance-list file")
    tune_parser.add_argument("--trials", type=int, default=200,
                             help="SMAC trial budget")
    tune_parser.add_argument("--walltime-limit", type=float, default=3600.0,
                             help="overall SMAC wall-clock budget in seconds; 0 disables the limit")
    tune_parser.add_argument("--workers", type=int, default=1,
                             help="SMAC worker count")
    tune_parser.add_argument("--seed", type=int, default=1,
                             help="SMAC and ConfigSpace seed")
    tune_parser.add_argument("--output-dir", type=Path, default=Path("smac-runs/llm2smt"),
                             help="SMAC output directory")
    tune_parser.add_argument("--overwrite", action="store_true",
                             help="allow SMAC to overwrite an existing run directory")
    tune_parser.set_defaults(func=cmd_tune)

    summarize_parser = sub.add_parser("summarize", help="summarize a JSONL run log")
    summarize_parser.add_argument("run_log", type=Path,
                                  help="llm2smt-runs.jsonl from a tuning run")
    summarize_parser.add_argument("-o", "--output", type=Path,
                                  help="optional JSON summary output path")
    summarize_parser.set_defaults(func=cmd_summarize)

    args = parser.parse_args()
    if hasattr(args, "solver"):
        if not args.solver.exists():
            raise SystemExit(f"solver does not exist: {args.solver}")
        if not os.access(args.solver, os.X_OK):
            raise SystemExit(f"solver is not executable: {args.solver}")
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())
