#!/usr/bin/env python3
"""Compare native Z3-shaped stats with Z3 -st counters for one SMT-LIB file."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import shlex
import subprocess
import sys


COUNTERS = [
    "mk-bool-var",
    "mk-clause",
    "mk-clause-binary",
    "units",
    "num-checks",
    "final-checks",
    "arith-conflicts",
    "arith-bound-propagations-lp",
    "arith-lower",
    "arith-upper",
    "arith-fixed-eqs",
    "arith-offset-eqs",
    "arith-make-feasible",
    "arith-max-rows",
    "arith-max-columns",
]


def run(cmd: list[str], cwd: Path, timeout: float) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=cwd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
        check=False,
    )


def parse_native(stderr: str) -> dict[str, str]:
    stats: dict[str, str] = {}
    for line in stderr.splitlines():
        m = re.match(r"\s*([A-Za-z0-9_.-]+)\s+([0-9]+)\s*$", line)
        if m:
            stats[m.group(1)] = m.group(2)
    return stats


def parse_z3(text: str) -> dict[str, str]:
    stats: dict[str, str] = {}
    for key, value in re.findall(r":([A-Za-z0-9_.-]+)\s+([0-9]+)", text):
        stats[key] = value
    return stats


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--root", default=".", type=Path)
    ap.add_argument("--native", default="build-workspace-rel/bin/llm2smt --quiet --stats")
    ap.add_argument("--z3", default=".venv-z3/bin/z3 -st")
    ap.add_argument("--timeout", type=float, default=30.0)
    args = ap.parse_args()

    root = args.root.resolve()
    native_cmd = shlex.split(args.native) + [args.file]
    z3_cmd = shlex.split(args.z3) + [args.file]

    try:
        native = run(native_cmd, root, args.timeout)
        z3 = run(z3_cmd, root, args.timeout)
    except subprocess.TimeoutExpired as exc:
        print(f"timeout running: {' '.join(exc.cmd)}", file=sys.stderr)
        return 124

    native_stats = parse_native(native.stderr)
    z3_stats = parse_z3(z3.stdout + "\n" + z3.stderr)
    native_answer = native.stdout.splitlines()[0].strip() if native.stdout.splitlines() else "ERROR"
    z3_answer = z3.stdout.splitlines()[0].strip() if z3.stdout.splitlines() else "ERROR"

    print(f"native\t{native_answer}\treturncode={native.returncode}")
    print(f"z3\t{z3_answer}\treturncode={z3.returncode}")
    print("counter\tnative\tz3")
    for key in COUNTERS:
        print(f"{key}\t{native_stats.get(key, '-')}\t{z3_stats.get(key, '-')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
