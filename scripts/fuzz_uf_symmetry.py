#!/usr/bin/env python3
"""Targeted differential fuzzer for the UF symmetry-breaking experiment.

This fuzzer stresses the fragile boundary between sound value-precedence
clauses and unsound ordering of terms that move under the value permutation.
It generates satisfiable QF_UF instances and compares llm2smt with
``--uf-symmetry-breaking`` against the same solver without that option.  A
reference solver can be supplied as an additional oracle.
"""

from __future__ import annotations

import argparse
import random
import shlex
import subprocess
import tempfile
from dataclasses import dataclass
from pathlib import Path

from gen_uf_symmetry_seeds import disequalities, domain_assert, header, sexpr_or


@dataclass(frozen=True)
class Case:
    kind: str
    text: str
    moving_terms: bool


@dataclass
class RunResult:
    status: str
    stdout: str
    stderr: str
    returncode: int
    timeout: bool
    clauses: int | None
    rejected: int | None


def left_assoc(op: str, items: list[str]) -> str:
    if len(items) < 2:
        return items[0]
    out = f"({op} {items[0]} {items[1]})"
    for item in items[2:]:
        out = f"({op} {out} {item})"
    return out


def choose_size(rng: random.Random, max_size: int) -> int:
    return rng.randint(2, max_size)


def make_fixed_choice(rng: random.Random, max_size: int) -> Case:
    size = choose_size(rng, max_size)
    terms = rng.randint(size, max(size, size + 5))
    values = [f"v{i}" for i in range(size)]
    xs = [f"x{i}" for i in range(terms)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += [f"(declare-fun {x} () U)" for x in xs]
    lines += ["(declare-fun P (U) Bool)"]
    lines += disequalities(values)
    if rng.random() < 0.7:
        lines.append(f"(assert {sexpr_or([f'(P {value})' for value in values])})")
    for x in xs:
        shuffled = values[:]
        rng.shuffle(shuffled)
        lines.append(domain_assert(x, shuffled))
    # Plant a partial assignment that is compatible with value precedence.
    for i, x in enumerate(xs[: rng.randint(0, min(terms, size))]):
        lines.append(f"(assert (= {x} {values[min(i, size - 1)]}))")
    lines += ["(check-sat)", ""]
    return Case("fixed-choice", "\n".join(lines), moving_terms=False)


def make_moving_unary(rng: random.Random, max_size: int) -> Case:
    size = choose_size(rng, max_size)
    values = [f"v{i}" for i in range(size)]
    fn = rng.choice(["f", "g"])
    shift = rng.randint(1, size - 1)
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += [f"(declare-fun {fn} (U) U)"]
    lines += disequalities(values)
    order = values[:]
    for value in values:
        rng.shuffle(order)
        lines.append(domain_assert(f"({fn} {value})", order))
    for i, value in enumerate(values):
        lines.append(f"(assert (= ({fn} {value}) {values[(i + shift) % size]}))")
    if rng.random() < 0.4:
        lines.append(f"(assert (not (= ({fn} {values[0]}) ({fn} {values[1]}))))")
    lines += ["(check-sat)", ""]
    return Case("moving-unary", "\n".join(lines), moving_terms=True)


def make_moving_binary(rng: random.Random, max_size: int) -> Case:
    size = choose_size(rng, max_size)
    values = [f"v{i}" for i in range(size)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += ["(declare-fun op (U U) U)"]
    lines += disequalities(values)
    order = values[:]
    for left in values:
        for right in values:
            rng.shuffle(order)
            lines.append(domain_assert(f"(op {left} {right})", order))
    offset = rng.randint(0, size - 1)
    for i, left in enumerate(values):
        for j, right in enumerate(values):
            lines.append(
                f"(assert (= (op {left} {right}) {values[(i + j + offset) % size]}))"
            )
    lines += ["(check-sat)", ""]
    return Case("moving-binary", "\n".join(lines), moving_terms=True)


def make_latin_square(rng: random.Random, max_size: int) -> Case:
    size = choose_size(rng, min(max_size, 5))
    values = [f"v{i}" for i in range(size)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += ["(declare-fun op (U U) U)"]
    lines += disequalities(values)
    for left in values:
        for right in values:
            lines.append(domain_assert(f"(op {left} {right})", values))
    for left in values:
        row = [f"(op {left} {right})" for right in values]
        lines.append(f"(assert {left_assoc('and', [f'(not (= {a} {b}))' for i, a in enumerate(row) for b in row[i + 1:]])})")
    for right in values:
        col = [f"(op {left} {right})" for left in values]
        lines.append(f"(assert {left_assoc('and', [f'(not (= {a} {b}))' for i, a in enumerate(col) for b in col[i + 1:]])})")
    offset = rng.randint(0, size - 1)
    for i, left in enumerate(values):
        for j, right in enumerate(values):
            lines.append(
                f"(assert (= (op {left} {right}) {values[(i + j + offset) % size]}))"
            )
    lines += ["(check-sat)", ""]
    return Case("latin-square", "\n".join(lines), moving_terms=True)


def make_case(rng: random.Random, max_size: int) -> Case:
    makers = [make_fixed_choice, make_moving_unary, make_moving_binary, make_latin_square]
    weights = [2, 4, 3, 2]
    maker = rng.choices(makers, weights=weights, k=1)[0]
    return maker(rng, max_size)


def parse_stat(stderr: str, name: str) -> int | None:
    for line in stderr.splitlines():
        parts = line.split()
        if len(parts) == 2 and parts[0] == name:
            try:
                return int(parts[1])
            except ValueError:
                return None
    return None


def run_solver(cmd: list[str], smt2: Path, timeout: float) -> RunResult:
    try:
        proc = subprocess.run(
            [*cmd, str(smt2)],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=timeout,
            check=False,
        )
        status = "unknown"
        for line in proc.stdout.splitlines():
            word = line.strip()
            if word in {"sat", "unsat", "unknown"}:
                status = word
                break
        return RunResult(
            status=status,
            stdout=proc.stdout,
            stderr=proc.stderr,
            returncode=proc.returncode,
            timeout=False,
            clauses=parse_stat(proc.stderr, "preproc.uf_symmetry_clauses"),
            rejected=parse_stat(proc.stderr, "preproc.uf_symmetry_rejected_noninvariant"),
        )
    except subprocess.TimeoutExpired as exc:
        return RunResult(
            status="timeout",
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
            returncode=124,
            timeout=True,
            clauses=None,
            rejected=None,
        )


def write_failure(save_dir: Path, index: int, case: Case, reason: str, details: str) -> Path:
    save_dir.mkdir(parents=True, exist_ok=True)
    path = save_dir / f"uf_sym_{index:06d}_{case.kind}_{reason}.smt2"
    path.write_text(
        f"; reason: {reason}\n; details: {details}\n{case.text}",
        encoding="utf-8",
    )
    return path


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--solver", default="build-uf-sym/bin/llm2smt")
    parser.add_argument(
        "--base-options",
        default="--quiet --stats --preprocess-passes 4 --eq-bridge "
                "--prop-interval 32 --prop-assign-threshold 0.25 "
                "--prop-delivery-budget 1000",
    )
    parser.add_argument("--sym-option", default="--uf-symmetry-breaking")
    parser.add_argument("--ref", default="", help="optional reference solver command")
    parser.add_argument("--count", type=int, default=1000)
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--timeout", type=float, default=5.0)
    parser.add_argument("--max-size", type=int, default=5)
    parser.add_argument("--save-fails", type=Path, default=Path("fuzz_fails/uf_symmetry"))
    parser.add_argument("--keep-all", type=Path, default=None,
                        help="optional directory for every generated instance")
    args = parser.parse_args()

    rng = random.Random(args.seed)
    solver = shlex.split(args.solver)
    base = shlex.split(args.base_options)
    sym = shlex.split(args.sym_option)
    ref = shlex.split(args.ref) if args.ref else []

    failures = 0
    moving_cases = 0
    fixed_cases = 0
    sym_clause_cases = 0

    with tempfile.TemporaryDirectory(prefix="uf_sym_fuzz_") as tmp:
        tmp_dir = Path(tmp)
        for index in range(args.count):
            case = make_case(rng, args.max_size)
            moving_cases += int(case.moving_terms)
            fixed_cases += int(not case.moving_terms)
            smt2 = tmp_dir / f"case_{index:06d}.smt2"
            smt2.write_text(case.text, encoding="utf-8")
            if args.keep_all is not None:
                args.keep_all.mkdir(parents=True, exist_ok=True)
                (args.keep_all / smt2.name).write_text(case.text, encoding="utf-8")

            off = run_solver([*solver, *base], smt2, args.timeout)
            on = run_solver([*solver, *base, *sym], smt2, args.timeout)
            if on.clauses and on.clauses > 0:
                sym_clause_cases += 1

            reason = ""
            details = ""
            if off.status != on.status:
                reason = "sym_disagreement"
                details = f"off={off.status} on={on.status}"
            elif off.returncode != 0 or on.returncode != 0:
                reason = "solver_error"
                details = f"off_rc={off.returncode} on_rc={on.returncode}"
            elif case.moving_terms and on.clauses not in (0, None):
                reason = "moving_terms_got_clauses"
                details = f"kind={case.kind} clauses={on.clauses}"
            elif ref:
                ref_result = run_solver(ref, smt2, args.timeout)
                if ref_result.status in {"sat", "unsat"} and on.status != ref_result.status:
                    reason = "ref_disagreement"
                    details = f"ref={ref_result.status} on={on.status}"

            if reason:
                failures += 1
                path = write_failure(args.save_fails, index, case, reason, details)
                print(f"FAIL {index}: {reason}: {details}: saved {path}")
                print(f"  off: status={off.status} rc={off.returncode}")
                print(f"  on:  status={on.status} rc={on.returncode} "
                      f"clauses={on.clauses} rejected={on.rejected}")
                if not args.keep_all:
                    return 1

            if (index + 1) % 100 == 0:
                print(
                    f"checked={index + 1} failures={failures} "
                    f"fixed={fixed_cases} moving={moving_cases} "
                    f"sym_clause_cases={sym_clause_cases}"
                )

    print(
        f"done checked={args.count} failures={failures} "
        f"fixed={fixed_cases} moving={moving_cases} "
        f"sym_clause_cases={sym_clause_cases}"
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
