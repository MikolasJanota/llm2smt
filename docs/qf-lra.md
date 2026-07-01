# QF_LRA

`QF_LRA` follows the standard SMT split between the SAT solver and a theory
solver. The SAT solver owns Boolean structure and search. The LRA theory solver
does not inspect arbitrary Boolean formulas; it only observes assignments to
registered arithmetic literals, checks whether the active bounds are feasible,
and returns conflicts or theory propagations with reasons.

Arithmetic atoms are therefore not translated into EUF nodes. They are lowered
to bound literals and registered with `src/theories/lra`.

## Reference

The native LRA design follows:

Bruno Dutertre and Leonardo de Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)*,
CSL Technical Report SRI-CSL-06-01, May 23, 2006.

References below to Chapter 3, Figure 3.1, Figure 3.2, and Sections 3.2.2,
3.2.4, and 3.3 are references to that report.

## Scope

The implementation supports pure quantifier-free linear real arithmetic:

- Real constants declared with `declare-fun`;
- rational numerals, decimals, `+`, `-`, `/` by rational constants, and `*`
  with at most one non-constant factor;
- `=`, `<`, `<=`, `>`, `>=`, and arithmetic `ite`;
- Boolean structure over arithmetic atoms.

Mixed `QF_UFLRA` is intentionally unsupported. Lean proof output remains
`QF_UF` only; `--proof` with `QF_LRA` fails with a clear error.

## Encoding Pipeline

The LRA parser path lowers formulas directly from the SMT-LIB parse tree. This
is parser/SAT encoding work, not theory solving:

1. Arithmetic terms are normalized into linear expressions over exact rationals
   backed by `boost::multiprecision::cpp_int`.
2. Compound linear terms get an internal arithmetic variable. The LRA solver
   adds a fixed tableau row for that variable and reuses the row when the same
   normalized expression appears again.
3. Each arithmetic atom that can become a SAT literal is exposed as an
   elementary lower or upper bound on one internal arithmetic variable.
4. The surrounding Boolean formula is encoded into CaDiCaL. The LRA solver only
   receives callbacks when CaDiCaL assigns one of the arithmetic literals.

`QF_LRA` does not use the EUF-oriented `NodeId` preprocessor. Instead, the
parse-tree encoder performs a small LRA-local preprocessing pass while lowering:
it expands `let` and 0-arity `define-fun`, folds constant arithmetic relations,
canonicalizes lower-bound atoms to equivalent upper-bound atoms for sharing,
reuses repeated arithmetic atoms and equality/disequality definitions, and
expands n-ary arithmetic `distinct` into pairwise disequality constraints.
Repeated Boolean compound definitions in the LRA parser path are also shared by
default. Use `--no-lra-bool-cache` to disable all of that sharing for ablation,
or `--no-lra-bool-cache-and`, `--no-lra-bool-cache-or`, and
`--no-lra-bool-cache-eq` to isolate one Boolean connective class.

Arithmetic equality is encoded as a SAT-level definition over two elementary
bounds:

```text
s = t  means  (s - t >= 0) and (s - t <= 0)
```

Its negation is handled by Boolean structure instead of by a non-convex
disequality branch inside the arithmetic core:

```text
s != t  means  (s - t < 0) or (s - t > 0)
```

`(distinct s t)` and explicit `(not (= s t))` use that same strict-inequality
disjunction. N-ary arithmetic `distinct` expands to all pairwise disequalities.
Simple one-variable equalities such as `x = 1` and `x = 2` produce SAT-level
at-most-one clauses by default; `--no-finite-domain-amo` disables this LRA-local
strengthening as well as the EUF finite-domain AMO pass.

## Tableau Solver

The native checker follows Dutertre and de Moura's Chapter 3 incremental
simplex architecture:

- fixed rows `x_i = c + Σ a_ij x_j` are kept in a tableau;
- a variable is **basic** when it owns one tableau row and its value is computed
  from that row; a variable is **non-basic** when it is assigned directly and can
  be moved to satisfy bounds;
- original Real variables start non-basic, while auxiliary term variables start
  basic because each auxiliary is introduced precisely to own the row for one
  linear expression;
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

The IPASIR-UP propagation callback also serves LRA implications. It performs
unate bound propagation for stronger active bounds and row-bound propagation
from the current tableau: when the active bounds on the variables in a row imply
a lower or upper bound on the basic variable, the solver propagates matching
elementary arithmetic literals with a reason clause built from the contributing
bound-source literals. The existing `--no-theory-prop` flag disables these LRA
propagations as well as EUF propagations.

## Current Limits

The LRA-local preprocessing is intentionally conservative. It removes constants
and repeated arithmetic definitions before SAT encoding, but it does not yet
build a separate theory-level DAG for linear terms and bounds. Consequently,
these theory-side optimizations are still incomplete in the native path:

- global sharing and simplification across all normalized linear expressions;
- row-bound tightening before SAT search starts;
- a full preprocessing statistics breakdown for LRA formulas.

## Models

For `sat`, `get-model` prints declared Real constants. The initial model
assignment defaults unconstrained variables to `0` and substitutes a concrete
positive rational for the symbolic `δ` used by strict bounds.

## Performance Notes

The checker is exact for the encoded linear constraints and maintains the
tableau incrementally across SAT callbacks. Propagation discovery normally scans
only arithmetic variables whose active bounds changed since the previous scan;
after a backtrack, currently bounded variables are marked for conservative
rediscovery. Use `--no-lra-incremental-prop-scan` to restore the older full-atom
scan for benchmarking.

Row-bound propagation is implemented but disabled by default because current
benchmarks show mixed effects: it helps some induction cases and slows some base
cases. `--lra-row-bound-prop` enables it for ablation,
`--lra-row-bound-prop-budget N` limits the number of row-bound atom candidates
inspected per discovery call (`0` means unlimited), and
`--lra-row-bound-dirty-scan` enables an experimental cheaper scan that only
visits rows touching recently changed bounds. The dirty-row scan can miss useful
propagations after pivots, so it is a benchmarking knob rather than the default
path.

`--stats` prints LRA counters for assignments, simplex checks, pivots,
conflicts, conflict-clause literals, delivered propagations, propagation
candidates considered, registered elementary atoms, tableau term variables, Real
variables, row-bound candidates, row-bound propagations, and LRA-local cache
hits. It also prints SAT encoding size counters. Extra propagation traffic can
speed up hard bound-heavy cases but can also slow the SAT search, so PAR2 is
tracked alongside solved counts when comparing these options.

### SLURM QF_LRA Progress Log

Native LRA changes are tracked against Z3 4.16.0 on the same SLURM machine and
the same 137-file pure `QF_LRA` set:

- `sandbox/non-incremental/QF_LRA/check`;
- `sandbox/non-incremental/QF_LRA/keymaera`;
- `sandbox/non-incremental/QF_LRA/spider_benchmarks`;
- `sandbox/non-incremental/QF_LRA/tta_startup`.

PAR2 counts each timeout as twice the timeout budget. At 60 seconds, one
timeout contributes 120 seconds; at 20 seconds, one timeout contributes 40
seconds. The progress table records the timeout with each row so 20-second and
60-second runs are not compared as raw PAR2 equivalents.

Append new rows after each completed campaign with: date, solver/configuration,
timeout, solved files, `tta_startup` solved files, timeouts, errors, PAR2,
artifact stem, and the decision made from the run.

| Date | Solver / configuration | Timeout | Solved | `tta_startup` solved | Timeouts | Errors | PAR2 | Artifact | Decision |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 2026-06-30 | native after let-bound equality fix | 60 s | 77 / 137 | 12 / 72 | 60 | 0 | 55.416 s | `lra-eval-106840` | Baseline native run after parser/runtime errors were removed. |
| 2026-06-30 | Z3 4.16.0 reference | 60 s | 128 / 137 | 63 / 72 | 9 | 0 | 8.869 s | `z3-lra-eval-106853` | Reference target; the native gap is concentrated in `tta_startup`. |
| 2026-07-01 | native after equality, Boolean cache, and incremental propagation scan tuning | 20 s | 86 / 137 | 21 / 72 | 51 | 0 | 16.679 s | `lra-eval-107582` | Short-timeout baseline for iteration. |
| 2026-07-01 | same native build as previous row | 60 s | 93 / 137 | 28 / 72 | 44 | 0 | 42.146 s | `lra-eval-107583` | Confirms extra time mainly buys more `tta_startup` cases. |
| 2026-07-01 | row-bound propagation enabled immediately | 20 s | 83 / 137 | 18 / 72 | 54 | 0 | 17.195 s | `llm2smt-lra-row20-107585` | Rejected as the default; it helps a few induction cases but loses more base cases. |
| 2026-07-01 | row-bound propagation disabled, current default | 20 s | 87 / 137 | 22 / 72 | 50 | 0 | 16.515 s | `llm2smt-lra-norow20-107586` | Accepted as the default; one more solved file than `lra-eval-107582`. |
| 2026-07-01 | adaptive row-bound threshold 500 | 20 s | 84 / 137 | 19 / 72 | 53 | 0 | 16.972 s | `llm2smt-lra-adapt20-107598` | Rejected and reverted; worse than the current default. |

All native rows in this log solve `check`, `keymaera`, and `spider_benchmarks`
completely; the moving metric is `tta_startup`. Where compared, no answer
disagreements with Z3 were observed on commonly solved files. Row-bound
propagation remains available by CLI option because it uniquely solves some
induction instances, but it is not the default because the current PAR2 and
solved-count results are worse.

The next optimization targets should be chosen from fast-Z3/slow-native
`tta_startup` files, for example:

- `simple_startup_10nodes.missing.induct.smt2`;
- `simple_startup_12nodes.abstract.base.smt2`;
- `simple_startup_14nodes.abstract.base.smt2`.

Raw artifacts for the rows above are kept in the workspace as matching
`eval_results/*.tsv` and `eval_results/*.summary` files.
