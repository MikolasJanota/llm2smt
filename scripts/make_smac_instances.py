#!/usr/bin/env python3
"""Create instance lists for SMAC tuning runs.

The output format is a plain text file with one SMT2 path per line.  Blank
lines and lines starting with '#' are ignored by scripts/smac_llm2smt.py.
"""

from __future__ import annotations

import argparse
import random
import re
from pathlib import Path


_SIZE_RE = re.compile(r"_size(\d+)\.smt2$")


def _size_key(path: Path) -> tuple[str, int, str]:
    match = _SIZE_RE.search(path.name)
    size = int(match.group(1)) if match else -1
    family = path.name[: match.start()] if match else path.stem
    return family, size, path.name


def _collect(inputs: list[Path]) -> list[Path]:
    out: list[Path] = []
    for item in inputs:
        if item.is_dir():
            out.extend(sorted(item.rglob("*.smt2"), key=_size_key))
        elif item.is_file():
            out.append(item)
        else:
            raise SystemExit(f"missing input: {item}")
    return out


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("inputs", nargs="+", type=Path,
                        help="SMT2 files or directories to include")
    parser.add_argument("-o", "--output", type=Path, required=True,
                        help="output instance-list path")
    parser.add_argument("--limit", type=int, default=0,
                        help="maximum number of instances after ordering/shuffle")
    parser.add_argument("--shuffle", action="store_true",
                        help="shuffle instances before applying --limit")
    parser.add_argument("--seed", type=int, default=1,
                        help="shuffle seed")
    parser.add_argument("--relative-to", type=Path, default=Path.cwd(),
                        help="write paths relative to this directory when possible")
    args = parser.parse_args()

    instances = _collect(args.inputs)
    seen: set[Path] = set()
    unique: list[Path] = []
    for path in instances:
        resolved = path.resolve()
        if resolved not in seen:
            seen.add(resolved)
            unique.append(path)

    if args.shuffle:
        random.Random(args.seed).shuffle(unique)
    else:
        unique.sort(key=_size_key)

    if args.limit > 0:
        unique = unique[: args.limit]

    base = args.relative_to.resolve()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as out:
        for path in unique:
            resolved = path.resolve()
            try:
                text = str(resolved.relative_to(base))
            except ValueError:
                text = str(resolved)
            out.write(text + "\n")

    print(f"wrote {len(unique)} instances to {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
