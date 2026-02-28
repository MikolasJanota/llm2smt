#!/usr/bin/env python3
"""
Fuzzer: generates random QF_UF problems and compares llm2smt against a reference solver.
Optionally verifies the model produced by our solver when it returns SAT.

The generator covers the full SMT-LIB Core theory (Core.smt2):
  Bool connectives : not, and, or, =>, xor, ite, = (biconditional), distinct
  U-sorted terms   : constants, unary/binary/ternary UFs, ite (U-sorted)
  Predicates       : UFs with Bool return sort (U → Bool, U U → Bool)
  Bool-arg UFs     : UFs that take a Bool argument (exercises compound-Bool-as-UF-arg)
  Bool constants   : 0-ary Bool-sorted declared symbols

Usage:
    python scripts/fuzz.py [options]
    python scripts/fuzz.py --ref cvc5 --count 1000 --seed 42
    python scripts/fuzz.py --ref cvc5 --check-model --count 500

    # Richer vocabulary
    python scripts/fuzz.py --n-ternary 1 --n-predicate 2 --n-bool-arg 1

    # Model checking only (skip result-comparison, just verify models)
    python scripts/fuzz.py --check-model --count 200

The reference solver (--ref) must accept an SMT-LIB2 file as its last argument
and print "sat" or "unsat" on stdout.  Both cvc5 and z3 work out of the box.

Our solver is invoked as:  timeout <T> <our-solver> <file>
The reference is invoked as: timeout <T> <ref-cmd...> <file>
"""

import argparse
import concurrent.futures
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from _model_check import check_model_correct


# ---------------------------------------------------------------------------
# Generation context — avoids threading 8 lists through every recursive call
# ---------------------------------------------------------------------------

class _Ctx:
    """Vocabulary for one random problem instance."""
    __slots__ = ("rng", "consts", "bool_consts", "unary_fns", "binary_fns",
                 "ternary_fns", "bool_arg_fns", "predicates")

    def __init__(self, rng, consts, bool_consts, unary_fns, binary_fns,
                 ternary_fns, bool_arg_fns, predicates):
        self.rng         = rng
        self.consts      = consts       # list[str]  — U-sorted constants
        self.bool_consts = bool_consts  # list[str]  — Bool-sorted 0-ary symbols
        self.unary_fns   = unary_fns    # list[str]  — U → U
        self.binary_fns  = binary_fns   # list[str]  — U U → U
        self.ternary_fns = ternary_fns  # list[str]  — U U U → U
        self.bool_arg_fns = bool_arg_fns  # list[str] — Bool → U
        self.predicates  = predicates   # list[(str, int)] — (name, arity), Bool return


# ---------------------------------------------------------------------------
# Mutual recursion: U-sorted term ↔ Bool-sorted formula
# ---------------------------------------------------------------------------

def _gen_term(ctx: _Ctx, depth: int = 0) -> str:
    """Generate a random U-sorted term."""
    rng = ctx.rng
    all_u_fns = ctx.unary_fns + ctx.binary_fns + ctx.ternary_fns
    leaf_prob = 0.40 + depth * 0.30

    if rng.random() < leaf_prob or (not all_u_fns and not ctx.bool_arg_fns):
        return rng.choice(ctx.consts)

    roll = rng.random()

    # ite(Bool, U, U) → U  — uses a Bool formula as condition
    if depth <= 2 and roll < 0.12:
        cond = _gen_fml(ctx, depth + 1)
        t    = _gen_term(ctx, depth + 1)
        e    = _gen_term(ctx, depth + 1)
        return f"(ite {cond} {t} {e})"

    # Bool-arg UF: (fn Bool) → U  — exercises compound-Bool-as-UF-arg path
    if ctx.bool_arg_fns and roll < 0.22:
        fn  = rng.choice(ctx.bool_arg_fns)
        arg = _gen_fml(ctx, depth + 1)
        return f"({fn} {arg})"

    if ctx.unary_fns and roll < 0.55:
        fn  = rng.choice(ctx.unary_fns)
        arg = _gen_term(ctx, depth + 1)
        return f"({fn} {arg})"

    if ctx.binary_fns and roll < 0.78:
        fn = rng.choice(ctx.binary_fns)
        a  = _gen_term(ctx, depth + 1)
        b  = _gen_term(ctx, depth + 1)
        return f"({fn} {a} {b})"

    if ctx.ternary_fns:
        fn = rng.choice(ctx.ternary_fns)
        a  = _gen_term(ctx, depth + 1)
        b  = _gen_term(ctx, depth + 1)
        c  = _gen_term(ctx, depth + 1)
        return f"({fn} {a} {b} {c})"

    # Fallback to whatever is available
    if ctx.unary_fns:
        return f"({rng.choice(ctx.unary_fns)} {rng.choice(ctx.consts)})"
    if ctx.binary_fns:
        fn = rng.choice(ctx.binary_fns)
        return f"({fn} {rng.choice(ctx.consts)} {rng.choice(ctx.consts)})"
    return rng.choice(ctx.consts)


def _gen_fml(ctx: _Ctx, depth: int = 0) -> str:
    """
    Generate a random Bool-sorted formula using all Core theory operators:
      not, and, or, =>, xor, ite (Bool-sorted), = (biconditional), distinct,
      = (U-sorted equality atom), predicate applications, Bool constants.
    """
    rng = ctx.rng
    leaf_prob = 0.40 + depth * 0.22

    if rng.random() < leaf_prob:
        roll = rng.random()

        # Declared Bool constant (0-ary propositional atom)
        if ctx.bool_consts and roll < 0.15:
            return rng.choice(ctx.bool_consts)

        # SMT-LIB built-in Bool literals
        if roll < 0.22:
            return rng.choice(["true", "false"])

        # Predicate application  (U... → Bool)
        if ctx.predicates and roll < 0.42:
            name, arity = rng.choice(ctx.predicates)
            args = " ".join(_gen_term(ctx, depth + 1) for _ in range(arity))
            return f"({name} {args})"

        # distinct (pairwise ≠ for 2–3 U-sorted terms)
        if roll < 0.58:
            n     = rng.randint(2, 3)
            terms = " ".join(_gen_term(ctx, depth + 1) for _ in range(n))
            return f"(distinct {terms})"

        # U-sorted equality atom — binary or chained (= t1 t2 [t3])
        n_eq = 2 if rng.random() < 0.75 else 3
        terms = " ".join(_gen_term(ctx, depth + 1) for _ in range(n_eq))
        return f"(= {terms})"

    # ── Compound formula using Core connectives ──────────────────────────
    op = rng.choice(["not", "and", "or", "=>", "xor", "ite", "bool_eq"])

    if op == "not":
        return f"(not {_gen_fml(ctx, depth + 1)})"

    if op in ("and", "or"):
        n    = rng.randint(2, 4)
        args = " ".join(_gen_fml(ctx, depth + 1) for _ in range(n))
        return f"({op} {args})"

    if op == "=>":
        # right-associative; generate 2–3 antecedents + one consequent
        n    = rng.randint(2, 3)
        args = " ".join(_gen_fml(ctx, depth + 1) for _ in range(n))
        return f"(=> {args})"

    if op == "xor":
        # occasionally generate 3-arg xor (left-assoc: (xor (xor a b) c))
        n_xor = 3 if rng.random() < 0.20 else 2
        args = " ".join(_gen_fml(ctx, depth + 1) for _ in range(n_xor))
        return f"(xor {args})"

    if op == "ite":
        # Bool-sorted ite: (ite Bool Bool Bool)
        c = _gen_fml(ctx, depth + 1)
        t = _gen_fml(ctx, depth + 1)
        e = _gen_fml(ctx, depth + 1)
        return f"(ite {c} {t} {e})"

    if op == "bool_eq":
        # Bool–Bool equality = propositional biconditional  (= φ ψ)
        a = _gen_fml(ctx, depth + 1)
        b = _gen_fml(ctx, depth + 1)
        return f"(= {a} {b})"

    # Unreachable, but safe fallback
    t1 = _gen_term(ctx, depth + 1)
    t2 = _gen_term(ctx, depth + 1)
    return f"(= {t1} {t2})"


# ---------------------------------------------------------------------------
# Problem builder
# ---------------------------------------------------------------------------

def gen_qf_uf(rng: random.Random, *,
              n_consts: int       = 4,
              n_bool_const: int   = 2,
              n_unary: int        = 2,
              n_binary: int       = 1,
              n_ternary: int      = 0,
              n_bool_arg: int     = 1,
              n_predicate: int    = 1,
              n_assert: int       = 6,
              compound_prob: float = 0.40,
              diseq_prob: float   = 0.30) -> str:
    """Generate a complete random QF_UF benchmark as an SMT-LIB2 string."""
    lines = ["(set-logic QF_UF)", "(declare-sort U 0)"]

    # ── Declarations ──────────────────────────────────────────────────────
    consts = [f"c{i}" for i in range(n_consts)]
    for c in consts:
        lines.append(f"(declare-fun {c} () U)")

    bool_consts = [f"p{i}" for i in range(n_bool_const)]
    for p in bool_consts:
        lines.append(f"(declare-fun {p} () Bool)")

    unary_fns = [f"f{i}" for i in range(n_unary)]
    for fn in unary_fns:
        lines.append(f"(declare-fun {fn} (U) U)")

    binary_fns = [f"g{i}" for i in range(n_binary)]
    for fn in binary_fns:
        lines.append(f"(declare-fun {fn} (U U) U)")

    ternary_fns = [f"t{i}" for i in range(n_ternary)]
    for fn in ternary_fns:
        lines.append(f"(declare-fun {fn} (U U U) U)")

    bool_arg_fns = [f"b{i}" for i in range(n_bool_arg)]
    for fn in bool_arg_fns:
        lines.append(f"(declare-fun {fn} (Bool) U)")

    predicates = []   # list of (name, arity)
    for i in range(n_predicate):
        arity     = rng.randint(1, 2)
        name      = f"h{i}"
        arg_sorts = " ".join(["U"] * arity)
        lines.append(f"(declare-fun {name} ({arg_sorts}) Bool)")
        predicates.append((name, arity))

    ctx = _Ctx(rng, consts, bool_consts, unary_fns, binary_fns,
               ternary_fns, bool_arg_fns, predicates)

    # ── Assertions ────────────────────────────────────────────────────────
    for _ in range(n_assert):
        if rng.random() < compound_prob:
            # Rich Bool formula using Core connectives
            fml = _gen_fml(ctx)
        else:
            # Simple U-sorted equality or disequality
            t1  = _gen_term(ctx)
            t2  = _gen_term(ctx)
            fml = (f"(not (= {t1} {t2}))" if rng.random() < diseq_prob
                   else f"(= {t1} {t2})")
        lines.append(f"(assert {fml})")

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
        if result.returncode == 124:   # timeout(1) exit code
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
# Per-test worker (called from thread pool)
# ---------------------------------------------------------------------------

def _run_one_test(i: int, seed: int, args, our_cmd: list, ref_cmd: list,
                  save_dir: Path) -> dict:
    """
    Generate and run a single fuzz test.  Safe to call from multiple threads
    (each invocation uses its own RNG and temp file).

    Returns a dict with keys:
      i, our, ref, smt2, model_ok (bool), model_reason (str)
    """
    rng = random.Random(seed)
    smt2 = gen_qf_uf(
        rng,
        n_consts      = args.n_consts,
        n_bool_const  = args.n_bool_const,
        n_unary       = args.n_unary,
        n_binary      = args.n_binary,
        n_ternary     = args.n_ternary,
        n_bool_arg    = args.n_bool_arg,
        n_predicate   = args.n_predicate,
        n_assert      = args.n_assert,
        compound_prob = args.compound_prob,
        diseq_prob    = args.diseq_prob,
    )

    fd, tmpfile = tempfile.mkstemp(suffix=".smt2")
    try:
        with os.fdopen(fd, "w") as fh:
            fh.write(smt2)
        our = run_solver(our_cmd, tmpfile, args.timeout)
        ref = run_solver(ref_cmd, tmpfile, args.timeout)
    finally:
        os.unlink(tmpfile)

    model_ok     = True
    model_reason = ""
    if our == "sat" and args.check_model:
        model_ok, model_reason = check_model_correct(smt2, our_cmd, ref_cmd,
                                                     args.timeout)

    return dict(i=i, our=our, ref=ref, smt2=smt2,
                model_ok=model_ok, model_reason=model_reason)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    parser = argparse.ArgumentParser(
        description="QF_UF differential fuzzer — full Core theory vocabulary",
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
    parser.add_argument("-j", "--jobs", type=int, default=1,
                        metavar="N",
                        help="Number of parallel worker threads")

    # ── Vocabulary size ───────────────────────────────────────────────────
    voc = parser.add_argument_group("vocabulary")
    voc.add_argument("--n-consts",     type=int, default=4,
                     help="U-sorted constants")
    voc.add_argument("--n-bool-const", type=int, default=2,
                     help="Bool-sorted 0-ary symbols (propositional atoms)")
    voc.add_argument("--n-unary",      type=int, default=2,
                     help="Unary UFs  (U → U)")
    voc.add_argument("--n-binary",     type=int, default=1,
                     help="Binary UFs (U U → U)")
    voc.add_argument("--n-ternary",    type=int, default=0,
                     help="Ternary UFs (U U U → U)")
    voc.add_argument("--n-bool-arg",   type=int, default=1,
                     help="Bool-arg UFs (Bool → U), exercises compound-Bool-as-UF-arg")
    voc.add_argument("--n-predicate",  type=int, default=1,
                     help="Predicates (U^k → Bool, k ∈ {1,2})")
    voc.add_argument("--n-assert",     type=int, default=6,
                     help="Number of assertions per problem")

    # ── Formula shape ─────────────────────────────────────────────────────
    shp = parser.add_argument_group("formula shape")
    shp.add_argument("--compound-prob", type=float, default=0.40,
                     help="Fraction of assertions that are compound Bool formulas "
                          "(vs. flat equality / disequality)")
    shp.add_argument("--diseq-prob", type=float, default=0.30,
                     help="Probability of a flat assertion being a disequality")

    # ── Run control ───────────────────────────────────────────────────────
    parser.add_argument("--stop-on-first-fail", action="store_true",
                        help="Stop after the first mismatch or model failure")
    parser.add_argument("--check-model", action="store_true",
                        help="When our solver says SAT, verify the model is correct "
                             "by injecting it into the problem and re-checking with "
                             "the reference solver")
    args = parser.parse_args()

    our_cmd = args.our_solver.split()
    ref_cmd = args.ref.split()

    save_dir = Path(args.save_fails)
    save_dir.mkdir(parents=True, exist_ok=True)

    # Pre-derive one seed per test from the master RNG so results are
    # deterministic for the same --seed regardless of --jobs.
    master_rng = random.Random(args.seed)
    test_seeds = [master_rng.randint(0, 2**32) for _ in range(args.count)]

    n_ok = n_mismatch = n_our_err = n_ref_err = n_model_fail = 0
    n_done = 0

    print(f"Fuzzing {args.count} random QF_UF problems "
          f"(seed={args.seed}, timeout={args.timeout}s, jobs={args.jobs})")
    print(f"  Our solver  : {' '.join(our_cmd)}")
    print(f"  Reference   : {args.ref}")
    print(f"  Vocabulary  : consts={args.n_consts}  bool_const={args.n_bool_const}  "
          f"unary={args.n_unary}  binary={args.n_binary}  ternary={args.n_ternary}  "
          f"bool_arg={args.n_bool_arg}  predicate={args.n_predicate}")
    print(f"  Assertions  : {args.n_assert}  "
          f"(compound={args.compound_prob:.0%}  diseq={args.diseq_prob:.0%})")
    print(f"  Check model : {'yes' if args.check_model else 'no'}")
    print()

    try:
        with concurrent.futures.ThreadPoolExecutor(
                max_workers=args.jobs) as executor:
            futures = {
                executor.submit(_run_one_test, i, test_seeds[i], args,
                                our_cmd, ref_cmd, save_dir): i
                for i in range(args.count)
            }

            for fut in concurrent.futures.as_completed(futures):
                res = fut.result()
                i   = res["i"]
                our = res["our"]
                ref = res["ref"]
                smt2 = res["smt2"]
                n_done += 1
                stop = False

                if our == "error":
                    n_our_err += 1
                    fail_path = save_dir / f"error_{i:06d}.smt2"
                    fail_path.write_text(smt2)
                    print(f"[ERROR #{n_our_err}] test {i}: our solver returned error  "
                          f"saved → {fail_path}")
                    stop = args.stop_on_first_fail
                elif ref in ("error", "timeout"):
                    n_ref_err += 1
                elif our != ref:
                    n_mismatch += 1
                    fail_path = save_dir / f"fail_{i:06d}_ours_{our}_ref_{ref}.smt2"
                    fail_path.write_text(smt2)
                    print(f"[MISMATCH #{n_mismatch}] test {i}: "
                          f"ours={our} ref={ref}  saved → {fail_path}")
                    stop = args.stop_on_first_fail
                else:
                    n_ok += 1
                    if not res["model_ok"]:
                        n_model_fail += 1
                        fail_path = save_dir / f"model_fail_{i:06d}.smt2"
                        fail_path.write_text(smt2)
                        print(f"[MODEL FAIL #{n_model_fail}] test {i}: "
                              f"{res['model_reason']}  saved → {fail_path}")
                        stop = args.stop_on_first_fail

                if n_done % 100 == 0:
                    print(f"  {n_done:5d}/{args.count}  "
                          f"ok={n_ok}  mismatch={n_mismatch}  "
                          f"model_fail={n_model_fail}  "
                          f"our_err={n_our_err}  ref_err={n_ref_err}")

                if stop:
                    for f in futures:
                        f.cancel()
                    break

    except KeyboardInterrupt:
        print("\nInterrupted.")

    print()
    print(f"Results: ok={n_ok}  mismatch={n_mismatch}  model_fail={n_model_fail}  "
          f"our_err={n_our_err}  ref_err={n_ref_err}")
    if n_mismatch or n_model_fail or n_our_err:
        print(f"Failing cases saved in: {save_dir}/")
    return 0 if (n_mismatch == 0 and n_model_fail == 0 and n_our_err == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
