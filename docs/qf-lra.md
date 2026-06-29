# QF_LRA

`QF_LRA` uses a separate theory path from EUF. Boolean structure is still
encoded into CaDiCaL with Tseitin clauses, but arithmetic atoms are registered
with `src/theories/lra`.

## Scope

The implementation supports pure quantifier-free linear real arithmetic:

- Real constants declared with `declare-fun`;
- rational numerals, decimals, `+`, `-`, `/` by rational constants, and `*`
  with at most one non-constant factor;
- `=`, `<`, `<=`, `>`, `>=`, and arithmetic `ite`;
- Boolean structure over arithmetic atoms.

Mixed `QF_UFLRA` is intentionally unsupported. Lean proof output remains
`QF_UF` only; `--proof` with `QF_LRA` fails with a clear error.

## Mapping To Dutertre/de Moura

The parser normalizes arithmetic terms into linear expressions over exact
rationals backed by `boost::multiprecision::cpp_int`.

The current native checker follows the DPLL(T) shape of Chapter 3 but uses a
complete exact Fourier-Motzkin feasibility check at final-model callbacks
instead of the incremental tableau pivot loop from Figure 3.2. Conflict
clauses are sound explanations over the currently active LRA literals. Small
conflicts are deletion-minimized by rechecking candidate subsets, which matches
the Section 3.2.2 interface but does not yet compute Farkas coefficients.

Strict inequalities are tracked explicitly during elimination. Combining two
bounds preserves strictness if either input was strict, corresponding to the
Section 3.3 infinitesimal view.

Disequality is not handled inside the arithmetic core. The parser rewrites
`(not (= s t))` and `(distinct s t)` into a disjunction of strict inequalities,
following the report's zero-detection avoidance advice.

Backtracking is cheap: the LRA solver keeps a per-level trail count and restores
the active literal trail in `notify_backtrack`, as in Section 3.2.4.

## Native Tuning Knobs

The native path is deliberately kept tunable while the implementation moves
toward a competitive incremental simplex solver.

```sh
build/bin/llm2smt --quiet \
  --lra-fm-elim-order min-fill \
  --lra-conflict-minimize-limit 64 \
  input.smt2
```

`--lra-fm-elim-order` controls the variable order used by the complete
Fourier-Motzkin checker:

- `min-fill` is the default. At each elimination step it chooses the variable
  with the smallest product of lower and upper bounds, reducing projected
  inequality growth.
- `name` uses the stable name-sorted order retained for ablations and
  regression comparisons.

`--lra-conflict-minimize-limit N` controls exact deletion minimization of LRA
conflict clauses. `0` disables minimization. The default, `64`, keeps compact
clauses for small formulas while avoiding repeated full Fourier-Motzkin checks
on large industrial assignments.

## External Backend Mode

For competitive benchmarking against large pure `QF_LRA` files, the driver can
delegate `QF_LRA` inputs to an external solver while leaving the native `QF_UF`
path unchanged:

```sh
build/bin/llm2smt --quiet --lra-backend z3 input.smt2
```

The command after `--lra-backend` is executed with the SMT-LIB file path
appended. The option requires an input file and is rejected with `--proof`.
It is intended for controlled benchmarking and cluster campaigns while the
native LRA engine is improved. It does not affect non-`QF_LRA` files.

## Models

For `sat`, `get-model` prints declared Real constants. The initial model
assignment is conservative and currently defaults unconstrained variables to
`0`; it is intended as a basic model surface rather than a full witness
reconstruction for every eliminated variable.

## Performance Note

The checker is exact and complete for the encoded linear constraints, but the
v1 final-check strategy and coarse conflict clauses are not competitive with an
incremental simplex tableau on large Boolean/arithmetic benchmarks. Small
regressions and several smoke benchmarks complete quickly; some industrial TTA
and spider benchmarks currently time out under short cutoffs on the native path.

The intended path to a competitive native solver is:

1. replace final-check-only Fourier-Motzkin with an incremental tableau that
   maintains bounds during SAT search;
2. explain conflicts from bound dependencies instead of full active-literal
   clauses;
3. preserve the current CLI tuning flags as ablation controls while adding
   simplex-specific knobs only when they are measurable.
