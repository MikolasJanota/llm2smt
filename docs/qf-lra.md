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
rationals backed by `boost::multiprecision::cpp_int`. Each SAT-visible
arithmetic atom is reduced to an elementary lower or upper bound on one internal
arithmetic variable. For a compound term, the LRA layer introduces a tableau row
for the term variable and reuses the row when the same normalized expression is
seen again.

The native checker follows Chapter 3's incremental simplex architecture:

- fixed rows `x_i = c + Σ a_ij x_j` are kept in a tableau;
- original Real variables start non-basic, term variables start basic;
- `notify_assignment` updates a bound stack for elementary atoms;
- Figure 3.1-style `update` / `pivotAndUpdate` repairs assignments;
- Figure 3.2 `Check` uses a deterministic Bland-style smallest-variable choice;
- Section 3.2.2 conflict clauses are built from the violated row's active bound
  sources;
- Section 3.2.4 backtracking restores only bound-stack entries and leaves the
  tableau, basis, and current assignment in place.

Strict inequalities use the Section 3.3 symbolic infinitesimal representation
`c + kδ`. The final printed model chooses a positive rational value for `δ` and
substitutes it into declared Real constants.

Arithmetic equality is encoded as a SAT-level definition over two elementary
bounds. Its negation is therefore handled by Boolean structure instead of a
non-convex disequality branch inside the arithmetic core. `(distinct s t)` and
explicit `(not (= s t))` remain disjunctions of strict inequalities.

The IPASIR-UP propagation callback also serves LRA implications. It currently
performs cheap unate bound propagation for stronger active bounds; the existing
`--no-theory-prop` flag disables these LRA propagations as well as EUF
propagations.

## Native Compatibility Knobs

The native path is the incremental tableau solver. These options remain for
CLI compatibility with earlier benchmark scripts:

```sh
build/bin/llm2smt --quiet \
  --lra-fm-elim-order min-fill \
  --lra-conflict-minimize-limit 64 \
  input.smt2
```

`--lra-fm-elim-order` is obsolete for the native tableau path. Accepted values
are still parsed so old scripts do not fail.

`--lra-conflict-minimize-limit N` is retained for debug/minimization helpers and
legacy tests. The primary conflict explanations now come from tableau bound
sources.

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
assignment defaults unconstrained variables to `0` and substitutes a concrete
positive rational for the symbolic `δ` used by strict bounds.

## Performance Note

The checker is exact for the encoded linear constraints and now maintains the
tableau incrementally across SAT callbacks. Propagation is intentionally cheap:
it starts with unate bound implications and can be extended with row-bound
refinement when benchmarks show the extra callback traffic is worthwhile.
