#!/usr/bin/env python3
"""
Fuzzer: generates random QF_UF problems and compares llm2smt against a reference solver.

Usage:
    python fuzz.py [options]
    python fuzz.py --ref cvc5 --count 1000 --seed 42
    python fuzz.py --ref z3 --n-consts 6 --n-assert 10

The reference solver (--ref) must accept an SMT-LIB2 file as its last argument and
print "sat" or "unsat" on stdout.  Both cvc5 and z3 work out of the box.

Our solver is invoked as:  timeout <T> <our-solver> <file>
The reference is invoked as: timeout <T> <ref-cmd...> <file>
"""

import argparse
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path


# ---------------------------------------------------------------------------
# Random QF_UF problem generator
# ---------------------------------------------------------------------------

def gen_term(rng: random.Random, consts: list[str],
             unary_fns: list[str], binary_fns: list[str],
             depth: int = 0) -> str:
    """Recursively generate a random term of sort U."""
    # Leaf with higher probability the deeper we go
    leaf_prob = 0.4 + depth * 0.3
    if rng.random() < leaf_prob or (not unary_fns and not binary_fns):
        return rng.choice(consts)

    roll = rng.random()
    if roll < 0.55 and unary_fns:
        fn  = rng.choice(unary_fns)
        arg = gen_term(rng, consts, unary_fns, binary_fns, depth + 1)
        return f"({fn} {arg})"
    elif binary_fns:
        fn = rng.choice(binary_fns)
        a  = gen_term(rng, consts, unary_fns, binary_fns, depth + 1)
        b  = gen_term(rng, consts, unary_fns, binary_fns, depth + 1)
        return f"({fn} {a} {b})"
    else:
        fn  = rng.choice(unary_fns)
        arg = gen_term(rng, consts, unary_fns, binary_fns, depth + 1)
        return f"({fn} {arg})"


def gen_qf_uf(rng: random.Random, *,
              n_consts: int   = 4,
              n_unary: int    = 2,
              n_binary: int   = 1,
              n_assert: int   = 6,
              diseq_prob: float = 0.3) -> str:
    """Generate a complete random QF_UF benchmark as a string."""
    lines = ["(set-logic QF_UF)", "(declare-sort U 0)"]

    consts = [f"c{i}" for i in range(n_consts)]
    for c in consts:
        lines.append(f"(declare-fun {c} () U)")

    unary_fns = [f"f{i}" for i in range(n_unary)]
    for fn in unary_fns:
        lines.append(f"(declare-fun {fn} (U) U)")

    binary_fns = [f"g{i}" for i in range(n_binary)]
    for fn in binary_fns:
        lines.append(f"(declare-fun {fn} (U U) U)")

    for _ in range(n_assert):
        lhs = gen_term(rng, consts, unary_fns, binary_fns)
        rhs = gen_term(rng, consts, unary_fns, binary_fns)
        if rng.random() < diseq_prob:
            lines.append(f"(assert (not (= {lhs} {rhs})))")
        else:
            lines.append(f"(assert (= {lhs} {rhs}))")

    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Solver runner
# ---------------------------------------------------------------------------

def run_solver(cmd: list[str], filepath: str, timeout: float) -> str:
    """
    Run `cmd + [filepath]` and return 'sat', 'unsat', 'timeout', or 'error'.
    """
    full_cmd = ["timeout", str(timeout)] + cmd + [filepath]
    try:
        result = subprocess.run(
            full_cmd,
            capture_output=True,
            text=True,
            timeout=timeout + 2,   # outer Python timeout slightly longer
        )
        # timeout(1) exits with code 124
        if result.returncode == 124:
            return "timeout"
        for line in result.stdout.splitlines():
            line = line.strip()
            if line in ("sat", "unsat"):
                return line
        return "error"
    except subprocess.TimeoutExpired:
        return "timeout"
    except Exception:
        return "error"


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="QF_UF differential fuzzer",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("--our-solver", default="build-dbg/bin/llm2smt",
                        help="Path to our solver binary")
    parser.add_argument("--ref", default="cvc5",
                        help="Reference solver command (e.g. 'cvc5' or 'z3 -smt2')")
    parser.add_argument("--count", type=int, default=500,
                        help="Number of random tests")
    parser.add_argument("--seed", type=int, default=0,
                        help="Random seed (deterministic)")
    parser.add_argument("--timeout", type=float, default=5.0,
                        help="Per-solver timeout in seconds")
    parser.add_argument("--save-fails", default="fuzz_fails",
                        help="Directory to save failing .smt2 files")
    parser.add_argument("--n-consts", type=int, default=4,
                        help="Number of constant symbols")
    parser.add_argument("--n-unary", type=int, default=2,
                        help="Number of unary function symbols")
    parser.add_argument("--n-binary", type=int, default=1,
                        help="Number of binary function symbols")
    parser.add_argument("--n-assert", type=int, default=6,
                        help="Number of assertions per problem")
    parser.add_argument("--diseq-prob", type=float, default=0.3,
                        help="Probability of each assertion being a disequality")
    parser.add_argument("--stop-on-first-fail", action="store_true",
                        help="Stop after the first mismatch")
    args = parser.parse_args()

    our_cmd = [args.our_solver]
    ref_cmd = args.ref.split()

    save_dir = Path(args.save_fails)
    save_dir.mkdir(parents=True, exist_ok=True)

    rng = random.Random(args.seed)

    n_ok = n_mismatch = n_our_err = n_ref_err = 0

    print(f"Fuzzing {args.count} random QF_UF problems "
          f"(seed={args.seed}, timeout={args.timeout}s)")
    print(f"  Our solver : {args.our_solver}")
    print(f"  Reference  : {args.ref}")
    print(f"  Size       : consts={args.n_consts} unary={args.n_unary} "
          f"binary={args.n_binary} assert={args.n_assert}")
    print()

    try:
        for i in range(args.count):
            smt2 = gen_qf_uf(
                rng,
                n_consts=args.n_consts,
                n_unary=args.n_unary,
                n_binary=args.n_binary,
                n_assert=args.n_assert,
                diseq_prob=args.diseq_prob,
            )

            # Write to a temporary file (both solvers accept filename args)
            fd, tmpfile = tempfile.mkstemp(suffix=".smt2")
            try:
                with os.fdopen(fd, "w") as fh:
                    fh.write(smt2)
                our = run_solver(our_cmd, tmpfile, args.timeout)
                ref = run_solver(ref_cmd, tmpfile, args.timeout)
            finally:
                os.unlink(tmpfile)

            if our == "error":
                n_our_err += 1
            elif ref in ("error", "timeout"):
                n_ref_err += 1
            elif our != ref:
                n_mismatch += 1
                fail_path = save_dir / f"fail_{i:06d}_ours_{our}_ref_{ref}.smt2"
                fail_path.write_text(smt2)
                print(f"[MISMATCH #{n_mismatch}] test {i}: "
                      f"ours={our} ref={ref}  saved → {fail_path}")
                if args.stop_on_first_fail:
                    break
            else:
                n_ok += 1
                if (i + 1) % 100 == 0:
                    print(f"  {i+1:5d}/{args.count}  "
                          f"ok={n_ok}  mismatch={n_mismatch}  "
                          f"our_err={n_our_err}  ref_err={n_ref_err}")

    except KeyboardInterrupt:
        print("\nInterrupted.")

    print()
    print(f"Results: ok={n_ok}  mismatch={n_mismatch}  "
          f"our_err={n_our_err}  ref_err={n_ref_err}")
    if n_mismatch:
        print(f"Failing cases saved in: {save_dir}/")
    return 0 if n_mismatch == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
