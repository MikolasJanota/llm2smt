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

The current v1 checker follows the DPLL(T) shape of Chapter 3 but uses a
complete exact Fourier-Motzkin feasibility check at final-model callbacks
instead of the incremental tableau pivot loop from Figure 3.2. Conflict
clauses are sound coarse explanations over the currently active LRA literals,
matching the Section 3.2.2 interface but not yet minimized by Farkas
coefficients.

Strict inequalities are tracked explicitly during elimination. Combining two
bounds preserves strictness if either input was strict, corresponding to the
Section 3.3 infinitesimal view.

Disequality is not handled inside the arithmetic core. The parser rewrites
`(not (= s t))` and `(distinct s t)` into a disjunction of strict inequalities,
following the report's zero-detection avoidance advice.

Backtracking is cheap: the LRA solver keeps a per-level trail count and restores
the active literal trail in `notify_backtrack`, as in Section 3.2.4.

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
and spider benchmarks currently time out under short cutoffs.
