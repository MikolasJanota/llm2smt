#!/usr/bin/env python3
"""Generate targeted QF_UF seeds for UF symmetry-breaking fuzzing.

The generated corpus is intentionally small and structured.  It covers:

* fixed-choice terms, where value-precedence symmetry breaking is expected to
  emit clauses;
* moving terms such as f(a), f(b), ... and op(a,b), where the terms themselves
  contain permuted values and must be rejected by the static recognizer.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def sexpr_or(items: list[str]) -> str:
    if not items:
        raise ValueError("empty disjunction")
    if len(items) == 1:
        return items[0]
    out = f"(or {items[0]} {items[1]})"
    for item in items[2:]:
        out = f"(or {out} {item})"
    return out


def disequalities(values: list[str]) -> list[str]:
    return [
        f"(assert (not (= {values[i]} {values[j]})))"
        for i in range(len(values))
        for j in range(i + 1, len(values))
    ]


def domain_assert(term: str, values: list[str]) -> str:
    return f"(assert {sexpr_or([f'(= {term} {value})' for value in values])})"


def header(status: str = "sat") -> list[str]:
    return [
        "(set-info :smt-lib-version 2.6)",
        "(set-logic QF_UF)",
        f"(set-info :status {status})",
        "(declare-sort U 0)",
    ]


def fixed_choice_seed(size: int, terms: int) -> str:
    values = [f"v{i}" for i in range(size)]
    xs = [f"x{i}" for i in range(terms)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += [f"(declare-fun {x} () U)" for x in xs]
    lines += ["(declare-fun P (U) Bool)"]
    lines += disequalities(values)
    lines += [f"(assert {sexpr_or([f'(P {value})' for value in values])})"]
    lines += [domain_assert(x, values) for x in xs]
    lines += ["(check-sat)", ""]
    return "\n".join(lines)


def moving_unary_seed(size: int) -> str:
    values = [f"v{i}" for i in range(size)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += ["(declare-fun f (U) U)"]
    lines += disequalities(values)
    lines += [domain_assert(f"(f {value})", values) for value in values]
    for i, value in enumerate(values):
        lines.append(f"(assert (= (f {value}) {values[(i + 1) % size]}))")
    lines += ["(check-sat)", ""]
    return "\n".join(lines)


def mixed_fixed_moving_seed(size: int, fixed_terms: int) -> str:
    values = [f"v{i}" for i in range(size)]
    xs = [f"x{i}" for i in range(fixed_terms)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += [f"(declare-fun {x} () U)" for x in xs]
    lines += ["(declare-fun f (U) U)"]
    lines += disequalities(values)
    lines += [domain_assert(x, values) for x in xs]
    lines += [domain_assert(f"(f {value})", values) for value in values]
    lines += ["(check-sat)", ""]
    return "\n".join(lines)


def moving_binary_seed(size: int) -> str:
    values = [f"v{i}" for i in range(size)]
    lines = header()
    lines += [f"(declare-fun {value} () U)" for value in values]
    lines += ["(declare-fun op (U U) U)"]
    lines += disequalities(values)
    for left in values:
        for right in values:
            lines.append(domain_assert(f"(op {left} {right})", values))
    for i, left in enumerate(values):
        for j, right in enumerate(values):
            lines.append(
                f"(assert (= (op {left} {right}) {values[(i + j) % size]}))"
            )
    lines += ["(check-sat)", ""]
    return "\n".join(lines)


def latin_square_seed(size: int) -> str:
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
        lines += [
            f"(assert (not (= {row[i]} {row[j]})))"
            for i in range(size)
            for j in range(i + 1, size)
        ]
    for right in values:
        col = [f"(op {left} {right})" for left in values]
        lines += [
            f"(assert (not (= {col[i]} {col[j]})))"
            for i in range(size)
            for j in range(i + 1, size)
        ]
    for i, left in enumerate(values):
        for j, right in enumerate(values):
            lines.append(
                f"(assert (= (op {left} {right}) {values[(i + j) % size]}))"
            )
    lines += ["(check-sat)", ""]
    return "\n".join(lines)


def parse_sizes(text: str) -> list[int]:
    sizes = []
    for chunk in text.split(","):
        size = int(chunk.strip())
        if size < 2:
            raise argparse.ArgumentTypeError("sizes must be at least 2")
        sizes.append(size)
    return sizes


def write_seed(out_dir: Path, name: str, content: str) -> tuple[str, int]:
    path = out_dir / name
    path.write_text(content, encoding="utf-8")
    return name, path.stat().st_size


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("tests/fuzz/uf_symmetry"),
        help="directory for generated .smt2 files and manifest.tsv",
    )
    parser.add_argument("--sizes", type=parse_sizes, default=parse_sizes("2,3,4"))
    parser.add_argument("--fixed-terms", type=int, default=5)
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    manifest = [
        "file\tkind\tstatus\texpected_uf_symmetry_clauses\tnote\tsize_bytes"
    ]

    for size in args.sizes:
        name, bytes_ = write_seed(
            args.out_dir,
            f"fixed_choice_n{size}_t{args.fixed_terms}.smt2",
            fixed_choice_seed(size, args.fixed_terms),
        )
        manifest.append(
            f"{name}\tfixed-choice\tsat\tpositive\tterms do not contain values\t{bytes_}"
        )

        name, bytes_ = write_seed(
            args.out_dir,
            f"moving_unary_cycle_n{size}.smt2",
            moving_unary_seed(size),
        )
        manifest.append(
            f"{name}\tmoving-unary\tsat\t0\tterms contain permuted values\t{bytes_}"
        )

        name, bytes_ = write_seed(
            args.out_dir,
            f"mixed_fixed_moving_n{size}_t{args.fixed_terms}.smt2",
            mixed_fixed_moving_seed(size, args.fixed_terms),
        )
        manifest.append(
            f"{name}\tmixed-fixed-moving\tsat\tpositive\tkeep fixed terms and drop moving terms\t{bytes_}"
        )

        name, bytes_ = write_seed(
            args.out_dir,
            f"moving_binary_table_n{size}.smt2",
            moving_binary_seed(size),
        )
        manifest.append(
            f"{name}\tmoving-binary\tsat\t0\tbinary terms contain permuted values\t{bytes_}"
        )

    for size in args.sizes:
        if size > 4:
            continue
        name, bytes_ = write_seed(
            args.out_dir,
            f"latin_square_fixed_n{size}.smt2",
            latin_square_seed(size),
        )
        manifest.append(
            f"{name}\tlatin-square\tsat\t0\tQG-like moving table terms\t{bytes_}"
        )

    (args.out_dir / "manifest.tsv").write_text("\n".join(manifest) + "\n",
                                               encoding="utf-8")
    print(f"wrote {len(manifest) - 1} seeds to {args.out_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
