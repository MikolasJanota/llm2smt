#!/usr/bin/env python3
"""Run a disciplined QF_LRA performance-candidate loop.

The loop intentionally compares a candidate option set against the current
default on the same benchmark suites and records the decision data in one
markdown report.  It is meant for local iteration before a full SLURM campaign.
"""

from __future__ import annotations

import argparse
import datetime as dt
from pathlib import Path
import shlex
import subprocess
import sys
from typing import Iterable


VERIFY_COMMANDS = [
    "cmake --build build-workspace-rel -j4",
    "ctest --test-dir build-workspace-rel --output-on-failure -R 'lra|Lra|Rational|DeltaRational' -j4",
    "bash scripts/build_docs.sh",
]


def run(cmd: str, cwd: Path, dry_run: bool) -> int:
    print(f"+ {cmd}", flush=True)
    if dry_run:
        return 0
    return subprocess.run(cmd, cwd=cwd, shell=True, check=False).returncode


def parse_summary(path: Path) -> dict[str, str]:
    data: dict[str, str] = {}
    with path.open() as f:
        for line in f:
            line = line.strip()
            if not line or "=" not in line:
                continue
            key, value = line.split("=", 1)
            data[key] = value
    return data


def as_int(data: dict[str, str], key: str) -> int:
    return int(data.get(key, "0"))


def as_float(data: dict[str, str], key: str) -> float:
    return float(data.get(key, "0"))


def eval_stem(candidate: str, suite: str, kind: str) -> str:
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    safe = "".join(c if c.isalnum() or c in "-_" else "-" for c in candidate)
    return f"loop-{safe}-{suite}-{kind}-{stamp}"


def eval_cmd(
    solver: str,
    timeout: float,
    suite: str,
    stem: str,
    jobs: int,
    opts: str,
) -> str:
    parts = [
        "python3 scripts/qf_lra_eval.py",
        f"--solver {shlex.quote(solver)}",
        f"--timeout {timeout:g}",
        f"--suite {shlex.quote(suite)}",
        f"--stem {shlex.quote(stem)}",
        f"--jobs {jobs}",
    ]
    if opts:
        parts.append(f"--opts={shlex.quote(opts)}")
    return " ".join(parts)


def verdict_for(defaults: list[dict[str, str]], candidates: list[dict[str, str]]) -> str:
    any_worse_solved = False
    any_better_solved = False
    any_worse_par2 = False
    any_better_par2 = False
    any_error = False

    for base, cand in zip(defaults, candidates):
        b_ok, c_ok = as_int(base, "ok"), as_int(cand, "ok")
        b_err, c_err = as_int(base, "error"), as_int(cand, "error")
        b_par2, c_par2 = as_float(base, "par2"), as_float(cand, "par2")
        any_error = any_error or c_err > b_err
        any_worse_solved = any_worse_solved or c_ok < b_ok
        any_better_solved = any_better_solved or c_ok > b_ok
        any_worse_par2 = any_worse_par2 or c_par2 > b_par2
        any_better_par2 = any_better_par2 or c_par2 < b_par2

    if any_error or any_worse_solved:
        return "reject-or-keep-option-only"
    if any_better_solved and not any_worse_par2:
        return "consider-default-after-full-eval"
    if any_better_par2 and not any_worse_par2:
        return "candidate-for-full-eval"
    if any_better_par2 and any_worse_par2:
        return "mixed-keep-option"
    return "no-demonstrated-gain"


def report_table(suites: Iterable[str],
                 defaults: list[dict[str, str]],
                 candidates: list[dict[str, str]]) -> str:
    lines = [
        "| Suite | Default solved | Candidate solved | Default PAR2 | Candidate PAR2 | Delta PAR2 |",
        "| --- | ---: | ---: | ---: | ---: | ---: |",
    ]
    for suite, base, cand in zip(suites, defaults, candidates):
        b_par2 = as_float(base, "par2")
        c_par2 = as_float(cand, "par2")
        lines.append(
            f"| `{suite}` | {as_int(base, 'ok')} / {as_int(base, 'total')} | "
            f"{as_int(cand, 'ok')} / {as_int(cand, 'total')} | "
            f"{b_par2:.3f} | {c_par2:.3f} | {c_par2 - b_par2:+.3f} |"
        )
    return "\n".join(lines)


def write_report(args: argparse.Namespace,
                 default_stems: list[str],
                 candidate_stems: list[str],
                 defaults: list[dict[str, str]],
                 candidates: list[dict[str, str]],
                 returncodes: list[tuple[str, int]]) -> Path:
    out_dir = Path(args.report_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = dt.datetime.now().strftime("%Y%m%d-%H%M%S")
    safe = "".join(c if c.isalnum() or c in "-_" else "-" for c in args.candidate)
    path = out_dir / f"{stamp}-{safe}.md"
    verdict = verdict_for(defaults, candidates)

    failed = [cmd for cmd, code in returncodes if code != 0]
    status = "blocked" if failed else verdict

    with path.open("w") as f:
        f.write(f"# QF_LRA Candidate: {args.candidate}\n\n")
        f.write(f"- Date: {dt.datetime.now().astimezone().isoformat(timespec='seconds')}\n")
        f.write(f"- Solver: `{args.solver}`\n")
        f.write(f"- Candidate opts: `{args.opts}`\n")
        f.write(f"- Timeout: `{args.timeout:g}s`\n")
        f.write(f"- Suites: `{', '.join(args.suites)}`\n")
        f.write(f"- Hypothesis: {args.hypothesis or 'TBD'}\n")
        f.write(f"- Decision hint: `{status}`\n\n")
        f.write("## Results\n\n")
        f.write(report_table(args.suites, defaults, candidates))
        f.write("\n\n## Artifacts\n\n")
        for suite, base, cand in zip(args.suites, default_stems, candidate_stems):
            f.write(f"- `{suite}` default: `eval_results/{base}.tsv`\n")
            f.write(f"- `{suite}` candidate: `eval_results/{cand}.tsv`\n")
        f.write("\n## Verification\n\n")
        for cmd, code in returncodes:
            marker = "PASS" if code == 0 else "FAIL"
            f.write(f"- `{marker}` `{cmd}`\n")
        f.write("\n## Decision\n\n")
        if failed:
            f.write("Do not evaluate performance until verification failures are fixed.\n")
        elif verdict == "consider-default-after-full-eval":
            f.write("Run full evaluation and compare against Z3/OpenSMT before making this default.\n")
        elif verdict == "candidate-for-full-eval":
            f.write("Run full evaluation; do not default yet without aggregate confirmation.\n")
        elif verdict == "mixed-keep-option":
            f.write("Keep behind an option unless a target-specific mode is desired.\n")
        elif verdict == "reject-or-keep-option-only":
            f.write("Reject as default. Keep only if it is useful for a documented target cluster.\n")
        else:
            f.write("No demonstrated gain; revert unless it is needed for another accepted change.\n")
    return path


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidate", required=True, help="Short candidate name for artifacts")
    parser.add_argument("--opts", default="", help="Candidate solver options")
    parser.add_argument("--hypothesis", default="", help="Expected mechanism and metric movement")
    parser.add_argument("--solver", default="build-workspace-rel/bin/llm2smt --quiet")
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--suite", dest="suites", action="append", choices=["quick", "hard", "full"])
    parser.add_argument("--skip-verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    parser.add_argument("--report-dir", default="eval_results/loop_reports")
    args = parser.parse_args()

    root = Path(".").resolve()
    args.suites = args.suites or ["quick", "hard"]

    returncodes: list[tuple[str, int]] = []
    if not args.skip_verify:
        for cmd in VERIFY_COMMANDS:
            code = run(cmd, root, args.dry_run)
            returncodes.append((cmd, code))
            if code != 0:
                report = write_report(args, [], [], [], [], returncodes)
                print(f"verification failed; wrote {report}", file=sys.stderr)
                return code

    default_stems: list[str] = []
    candidate_stems: list[str] = []
    defaults: list[dict[str, str]] = []
    candidates: list[dict[str, str]] = []

    for suite in args.suites:
        base_stem = eval_stem(args.candidate, suite, "default")
        cand_stem = eval_stem(args.candidate, suite, "candidate")
        default_stems.append(base_stem)
        candidate_stems.append(cand_stem)

        for stem, opts in [(base_stem, ""), (cand_stem, args.opts)]:
            cmd = eval_cmd(args.solver, args.timeout, suite, stem, args.jobs, opts)
            code = run(cmd, root, args.dry_run)
            returncodes.append((cmd, code))
            if code != 0:
                report = write_report(args, default_stems, candidate_stems, defaults, candidates, returncodes)
                print(f"evaluation failed; wrote {report}", file=sys.stderr)
                return code

        if not args.dry_run:
            defaults.append(parse_summary(root / "eval_results" / f"{base_stem}.summary"))
            candidates.append(parse_summary(root / "eval_results" / f"{cand_stem}.summary"))
        else:
            defaults.append({"total": "0", "ok": "0", "error": "0", "par2": "0"})
            candidates.append({"total": "0", "ok": "0", "error": "0", "par2": "0"})

    report = write_report(args, default_stems, candidate_stems, defaults, candidates, returncodes)
    print(f"wrote {report}")
    if not args.dry_run:
        print(report_table(args.suites, defaults, candidates))
        print(f"decision hint: {verdict_for(defaults, candidates)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
