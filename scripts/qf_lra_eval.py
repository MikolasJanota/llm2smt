#!/usr/bin/env python3
"""Run QF_LRA benchmark subsets and write llm2smt-style TSV summaries."""

from __future__ import annotations

import argparse
import concurrent.futures
import datetime as dt
import os
from pathlib import Path
import shlex
import subprocess
import sys
import time


FULL_DIRS = [
    "sandbox/non-incremental/QF_LRA/check",
    "sandbox/non-incremental/QF_LRA/keymaera",
    "sandbox/non-incremental/QF_LRA/spider_benchmarks",
    "sandbox/non-incremental/QF_LRA/tta_startup",
]

QUICK_FILES = [
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_5nodes.bug.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_10nodes.missing.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_12nodes.abstract.base.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_12nodes.synchro.base.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_14nodes.abstract.base.smt2",
]

HARD_FILES = [
    "sandbox/non-incremental/QF_LRA/spider_benchmarks/op_seen_less2.base.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_3nodes.bug.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_4nodes.missing.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_5nodes.bug.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_5nodes.missing.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_10nodes.missing.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_12nodes.abstract.base.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_12nodes.abstract.induct.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_14nodes.abstract.base.smt2",
    "sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_14nodes.abstract.induct.smt2",
]


def rel(path: Path, root: Path) -> str:
    return path.relative_to(root).as_posix()


def files_from_dirs(root: Path, dirs: list[str]) -> list[str]:
    files: list[str] = []
    for d in dirs:
        files.extend(rel(p, root) for p in sorted((root / d).glob("*.smt2")))
    return files


def files_from_tsv(tsv: Path, statuses: set[str], min_seconds: float) -> list[str]:
    out: list[str] = []
    with tsv.open() as f:
        header = f.readline().rstrip("\n").split("\t")
        try:
            i_file = header.index("file")
            i_status = header.index("status")
            i_seconds = header.index("seconds")
        except ValueError as exc:
            raise SystemExit(f"{tsv}: expected file/status/seconds columns") from exc
        for line in f:
            cols = line.rstrip("\n").split("\t")
            if len(cols) <= max(i_file, i_status, i_seconds):
                continue
            try:
                seconds = float(cols[i_seconds])
            except ValueError:
                seconds = 0.0
            if cols[i_status] in statuses or seconds >= min_seconds:
                out.append(cols[i_file])
    return out


def run_one(root: Path, solver: list[str], timeout: float, file: str) -> tuple[str, str, float, str]:
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            solver + [file],
            cwd=root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout,
            check=False,
        )
        elapsed = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return file, "timeout", timeout, "timeout"

    answer = proc.stdout.splitlines()[0].strip() if proc.stdout.splitlines() else "ERROR"
    if proc.returncode == 0 and answer in {"sat", "unsat", "unknown"}:
        return file, "ok", elapsed, answer
    return file, "error", elapsed, answer


def write_results(
    out_dir: Path,
    stem: str,
    rows: list[tuple[str, str, float, str]],
    timeout: float,
    opts: str,
) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    tsv = out_dir / f"{stem}.tsv"
    summary = out_dir / f"{stem}.summary"

    with tsv.open("w") as f:
        f.write("file\tstatus\tseconds\tanswer\n")
        for file, status, seconds, answer in rows:
            f.write(f"{file}\t{status}\t{seconds:.3f}\t{answer}\n")

    total = len(rows)
    ok = sum(1 for _, status, _, _ in rows if status == "ok")
    timeouts = sum(1 for _, status, _, _ in rows if status == "timeout")
    errors = sum(1 for _, status, _, _ in rows if status == "error")
    par2 = sum(seconds if status == "ok" else 2 * timeout for _, status, seconds, _ in rows)
    avg_par2 = par2 / total if total else 0.0
    tta_ok = sum(
        1
        for file, status, _, _ in rows
        if status == "ok" and "/tta_startup/" in f"/{file}"
    )

    with summary.open("w") as f:
        f.write(f"total={total}\n")
        f.write(f"ok={ok}\n")
        f.write(f"timeout={timeouts}\n")
        f.write(f"error={errors}\n")
        f.write(f"tta_startup_ok={tta_ok}\n")
        f.write(f"timeout_s={timeout:g}\n")
        f.write(f"par2={avg_par2:.3f}\n")
        f.write(f"opts={opts}\n")
        f.write(f"finished={dt.datetime.now().astimezone().isoformat(timespec='seconds')}\n")

    print(summary.read_text(), end="")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default=".", type=Path)
    parser.add_argument("--solver", default="build-slurm-rel/bin/llm2smt --quiet")
    parser.add_argument("--timeout", type=float, default=20.0)
    parser.add_argument("--jobs", type=int, default=max(1, os.cpu_count() or 1))
    parser.add_argument("--out-dir", default="eval_results", type=Path)
    parser.add_argument("--stem", required=True)
    parser.add_argument("--suite", choices=["full", "quick", "hard"], default="full")
    parser.add_argument("--file", action="append", default=[])
    parser.add_argument("--from-tsv", type=Path)
    parser.add_argument("--tsv-status", action="append", default=["timeout", "error"])
    parser.add_argument("--tsv-min-seconds", type=float, default=15.0)
    parser.add_argument("--opts", default="")
    args = parser.parse_args()

    root = args.root.resolve()
    solver = shlex.split(args.solver) + shlex.split(args.opts)
    if not solver:
        raise SystemExit("--solver must not be empty")

    if args.file:
        files = args.file
    elif args.from_tsv:
        files = files_from_tsv(args.from_tsv, set(args.tsv_status), args.tsv_min_seconds)
    elif args.suite == "quick":
        files = QUICK_FILES
    elif args.suite == "hard":
        files = HARD_FILES
    else:
        files = files_from_dirs(root, FULL_DIRS)

    missing = [f for f in files if not (root / f).is_file()]
    if missing:
        raise SystemExit(f"missing benchmark files: {missing[:5]}")

    print(f"running {len(files)} files with timeout={args.timeout:g}s jobs={args.jobs}", file=sys.stderr)
    rows: list[tuple[str, str, float, str]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [pool.submit(run_one, root, solver, args.timeout, f) for f in files]
        for fut in concurrent.futures.as_completed(futs):
            row = fut.result()
            rows.append(row)
            print(f"{row[0]}\t{row[1]}\t{row[2]:.3f}\t{row[3]}", file=sys.stderr, flush=True)

    rows.sort(key=lambda r: r[0])
    write_results(args.out_dir, args.stem, rows, args.timeout, args.opts or args.solver)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
