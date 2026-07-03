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
folds constant Boolean connectives before Tseitin encoding, simplifies
arithmetic `ite` terms with constant conditions or equal normalized branches,
canonicalizes lower-bound atoms to equivalent upper-bound atoms for sharing,
uses unconditional top-level arithmetic equalities to eliminate variables before
later atom registration, reuses repeated arithmetic atoms and
equality/disequality definitions, and expands n-ary arithmetic `distinct` into
pairwise disequality constraints.
Use `--no-lra-const-simplify` to disable the local constant/connective
simplifier for ablation.
Finite-domain choices such as `x = 0`, `x = 1`, ... are linked to simple bound
atoms on the same variable by default, so a bound assignment can remove
incompatible choices and a chosen value can imply trivial bounds. Use
`--no-lra-finite-domain-bounds` to disable those links. When a variable equality
is asserted over two finite-domain Real variables, matching choice literals are
linked by default in the equality-implies-choice direction. This avoids the
old full equality definition that made equality true from matching choices and
hurt SAT search. Use `--no-lra-finite-domain-eqdefs` to disable these links.
Finite-domain choice literals can also be offered as SAT branch hints with
`--lra-finite-domain-branch`; the current implementation only hints value `2`
choices. This is off by default because one quick run solved
`simple_startup_10nodes.missing.induct.smt2` and improved the 5-file quick PAR2
to 6.389, but a repeat run timed out on the same file and regressed PAR2 to
10.269. Use `--no-lra-finite-domain-branch` for explicit ablation when the flag
is enabled by a script.
Positive arithmetic equalities asserted directly at top level can be registered
as direct LRA equality atoms with `--lra-direct-eq-atoms`. This is experimental:
guarded or negated equality still uses the existing strict-bound disjunction
encoding because `e != 0` is not a single linear bound. The option is kept for
diagnostics, not as a default, because the current quick `tta_startup` eval
regresses from 4/5 solved, PAR2 10.943, to 3/5 solved, PAR2 17.954.
Repeated Boolean compound definitions in the LRA parser path are also shared by
default. Use `--no-lra-bool-cache` to disable all of that sharing for ablation,
or `--no-lra-bool-cache-and`, `--no-lra-bool-cache-or`, and
`--no-lra-bool-cache-eq` to isolate one Boolean connective class.
Normalized arithmetic term results are cached by parse-tree node as well; this
is especially important for arithmetic `ite`, where repeated uses of the same
SMT-LIB term should reuse one auxiliary Real variable. Use
`--no-lra-term-cache` to disable this cache for ablation.

Equality elimination is deliberately conservative. It only consumes arithmetic
equalities asserted unconditionally at top level, either as direct assertions or
as children of a top-level `and`; it does not use equalities guarded by `or`,
`=>`, Boolean `ite`, or negation, and it skips arithmetic equalities whose terms
contain arithmetic `ite`. Rows are processed with exact rational arithmetic into
a substitution map, dependent rows are ignored, inconsistent rows add an
immediate empty SAT clause, and `get-model` reconstructs eliminated declared
Real constants from the remaining LRA model. The pass is on by default; use
`--no-lra-eq-elim` to disable it and `--lra-eq-elim-limit N` to cap the number
of equality rows processed.

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

The LRA-local preprocessing is intentionally conservative. It folds constant
relations and local constant Boolean structure, simplifies trivial arithmetic
`ite` terms, eliminates only unconditional top-level equalities, reuses repeated
atoms and equality definitions, links finite-domain choices to simple bounds,
shares repeated Boolean compounds, flattens right-nested constant-valued
arithmetic `ite` chains into one auxiliary, and caches normalized arithmetic
terms by parse-tree node.
It still does not build a global, algebraic theory DAG for all linear terms and
bounds before SAT encoding. Consequently, these theory-side optimizations are
still incomplete in the native path:

- global sharing and simplification across equivalent normalized linear
  expressions that arise from different parse-tree nodes;
- propagation of let-bound constants and aliases through the whole assertion
  before LRA encoding;
- row-bound tightening before SAT search starts;
- default-on symmetry breaking for finite-domain LRA variables; this needs a
  proof that variable/value permutations preserve the formula before adding
  ordering constraints.

## Evaluation Notes

The current full QF_LRA evaluation artifacts from 2026-07-03 are:

- native: `eval_results/full-rational-sign-fastpaths-20260703.tsv`;
- Z3 reference: `eval_results/full-z3-20260703-093850.tsv`.

Both runs use the 137-file suite from `scripts/qf_lra_eval.py` with a 20s
per-file timeout. Native solves 116/137 with 21 timeouts, no errors,
51 `tta_startup` solves, and average PAR2 7.290. Z3 solves 127/137 with
10 timeouts, no errors, 62 `tta_startup` solves, and average PAR2 3.402.
There are no answer disagreements on the files solved by both solvers.

All native timeouts are in `QF_LRA/tta_startup`. Compared with the previous
20s full artifact `eval_results/full-rational-fastpaths-20260703.tsv`, the
current solver improves from 110 to 116 solved files with no lost solves and no
answer changes. The six newly solved files are all `tta_startup` inductive
instances: `6nodes.bug`, `9nodes.missing`, `10nodes.synchro`, `11nodes.bug`,
`11nodes.missing`, and `12nodes.missing`.

Major QF_LRA solver changes should also be followed by a bounded YinYang
fuzzing pass against a reference solver before treating the change as accepted.
Use `scripts/yinyang_fuzz.sh` locally for quick smoke fuzzing, or submit the
same wrapper through SLURM for longer seed-directory runs. At minimum, fuzz the
QF_LRA `check` seeds after parser/theory changes; when the change affects
preprocessing, equality handling, finite-domain encodings, or theory
propagation, also fuzz `keymaera`, `spider_benchmarks`, and representative
`tta_startup` seeds. Preserve the SLURM logs and any `yinyang_bugs` artifacts
with the evaluation notes so performance changes are paired with differential
correctness evidence.

When a target instance or benchmark run takes long enough to drive an
optimization, collect old-fashioned profiler evidence before committing to a
hypothesis. Run the native solver under a sampling profiler such as `perf`,
`gprof`, or Callgrind on the slow SMT-LIB file, keep the command and top hot
functions with the evaluation notes, and use the profile to decide whether the
next change belongs in SAT encoding, arithmetic preprocessing, CaDiCaL search,
simplex checking, propagation, or model construction. Native `--stats` counters
are useful context, but they are not a substitute for a CPU profile when the
wall time is dominated by an unknown hotspot.

The 2026-07-03 CPU profiles in `profile_results/qflra-20260703` showed that
the slow `tta_startup` cases were dominated by exact rational arithmetic during
simplex pivoting, especially `Rational::normalize()` called through
`LraSolver::recompute_basic_values()`. The accepted fix removes that full
post-pivot recomputation: an algebraic pivot preserves the current assignment,
so `pivot_and_update` only moves the old basic variable after it becomes
nonbasic.

The same change was followed by SLURM YinYang jobs `107621` through `107626`,
with logs synced under `slurm_logs/qflra-pivot-*`. The `check` and `keymaera`
seed directories completed with 0 bug triggers. The `spider_benchmarks` and
`tta_startup` runs hit the 300s fuzzing budget before completing all seeds, but
produced no bug artifacts in `yinyang_bugs`.

A follow-up profile of `simple_startup_9nodes.missing.induct.smt2` after the
pivot fix still showed `Rational::normalize()` and multiprecision arithmetic
as the main hotspots, this time mostly inside row rewriting in `pivot()` and
incremental `update()`. The accepted rational fast paths avoid gcd/modulus work
for already-canonical zero, integer, one, and minus-one arithmetic.
This change was followed by SLURM YinYang job `107627` on the QF_LRA `check`
seeds; it processed 2 valid seeds and found 0 bug triggers.

A second bounded profile of the same target after the first rational fast paths
still spent most sampled time under `LraSolver::check()`, with
`Rational::normalize()`, multiprecision multiplication, and `std::map` row
lookups inside `pivot()` and `update()` as the dominant leaf costs. The next
accepted arithmetic fast path avoids constructing normalized temporaries for
sign flips and subtraction, and short-circuits same-denominator and opposite
sign comparisons. This makes `simple_startup_9nodes.missing.induct.smt2` solve
inside the 20s cutoff and improves the full 137-file PAR2 from 8.731 to 7.290.
This change was followed by SLURM YinYang job `107629` on the QF_LRA `check`
seeds; it processed 2 valid seeds and found 0 bug triggers.

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

Row-bound propagation is enabled by default with the dirty-row scan: it visits
only rows touching recently changed bounds and propagates matching elementary
arithmetic atoms implied by those row-derived bounds. `--no-lra-row-bound-prop`
disables this mode for ablation, `--lra-row-bound-prop-budget N` limits the
number of row-bound atom candidates inspected per discovery call (`0` means
unlimited), and `--lra-row-bound-dirty-scan` is accepted explicitly for scripts.

`--stats` prints LRA counters for assignments, simplex checks, pivots,
conflicts, conflict-clause literals, delivered propagations, propagation
candidates considered, registered elementary atoms, tableau term variables, Real
variables, row-bound candidates, row-bound propagations, equality-elimination
rows/variables/contradictions, local constant folds, arithmetic `ite`
simplifications, finite-domain bound/equality-definition clauses, and LRA-local
cache hits. It also prints SAT encoding size counters. Extra propagation traffic can speed up hard bound-heavy cases but can
also slow the SAT search, so PAR2 is tracked alongside solved counts when
comparing these options.
The stats output also includes a `z3-shaped` section with native approximations
of common Z3 `-st` counters such as `mk-bool-var`, `mk-clause-binary`,
`arith-fixed-eqs`, `arith-offset-eqs`, and `arith-max-columns`. Use
`scripts/compare_z3_stats.py` to run native `--stats` and Z3 `-st` on the same
file and print those counters side by side.

### SLURM QF_LRA Progress Log

Native LRA changes are tracked against Z3 4.16.0 on the same SLURM machine and
the same 137-file pure `QF_LRA` set:

- `sandbox/non-incremental/QF_LRA/check`;
- `sandbox/non-incremental/QF_LRA/keymaera`;
- `sandbox/non-incremental/QF_LRA/spider_benchmarks`;
- `sandbox/non-incremental/QF_LRA/tta_startup`.

The table reports average PAR2 per instance: solved files contribute their
runtime, each timeout or error contributes twice the timeout budget, and the sum
is divided by the 137 files in the benchmark set. At 60 seconds, one timeout
contributes 120 seconds to the sum; at 20 seconds, one timeout contributes 40
seconds to the sum. The progress table records the timeout with each row so
20-second and 60-second runs are not compared as raw PAR2 equivalents.

Append new rows after each completed campaign with: date, solver/configuration,
timeout, solved files, `tta_startup` solved files, timeouts, errors, average PAR2,
artifact stem, and the decision made from the run.

For local iteration, `scripts/qf_lra_eval.py` provides three fixed suites:
`--suite quick` runs five fast feedback cases, `--suite hard` runs ten
representative fast-Z3/slow-native cases from the current QF_LRA gap, and
`--suite full` runs the 137-file set.  Use `--from-tsv PREVIOUS.tsv` to create
an ad hoc suite from files that timed out or exceeded `--tsv-min-seconds` in an
earlier run.

| Date | Solver / configuration | Timeout | Solved | `tta_startup` solved | Timeouts | Errors | Avg PAR2 | Artifact | Decision |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 2026-06-30 | native after let-bound equality fix | 60 s | 77 / 137 | 12 / 72 | 60 | 0 | 55.416 s | `lra-eval-106840` | Baseline native run after parser/runtime errors were removed. |
| 2026-06-30 | Z3 4.16.0 reference | 60 s | 128 / 137 | 63 / 72 | 9 | 0 | 8.869 s | `z3-lra-eval-106853` | Reference target; the native gap is concentrated in `tta_startup`. |
| 2026-07-01 | native after equality, Boolean cache, and incremental propagation scan tuning | 20 s | 86 / 137 | 21 / 72 | 51 | 0 | 16.679 s | `lra-eval-107582` | Short-timeout baseline for iteration. |
| 2026-07-01 | same native build as previous row | 60 s | 93 / 137 | 28 / 72 | 44 | 0 | 42.146 s | `lra-eval-107583` | Confirms extra time mainly buys more `tta_startup` cases. |
| 2026-07-01 | row-bound propagation enabled immediately | 20 s | 83 / 137 | 18 / 72 | 54 | 0 | 17.195 s | `llm2smt-lra-row20-107585` | Rejected as the default; it helps a few induction cases but loses more base cases. |
| 2026-07-01 | row-bound propagation disabled, current default | 20 s | 87 / 137 | 22 / 72 | 50 | 0 | 16.515 s | `llm2smt-lra-norow20-107586` | Accepted as the default; one more solved file than `lra-eval-107582`. |
| 2026-07-01 | adaptive row-bound threshold 500 | 20 s | 84 / 137 | 19 / 72 | 53 | 0 | 16.972 s | `llm2smt-lra-adapt20-107598` | Rejected and reverted; worse than the current default. |
| 2026-07-02 | equality elimination default on | 20 s | 91 / 137 | 27 / 72 | 46 | 0 | 15.201 s | `llm2smt-lra-eqelim20-107611` | Improves over the previous native 20 s row, but the paired ablation below shows equality elimination itself is neutral on this run. |
| 2026-07-02 | `--no-lra-eq-elim` ablation | 20 s | 91 / 137 | 27 / 72 | 46 | 0 | 15.189 s | `llm2smt-lra-noeq20-107616` | Same solved count and marginally lower PAR2 than equality elimination; treat equality elimination as not yet a demonstrated aggregate performance win. |
| 2026-07-03 | native after finite-domain equality propagation | 20 s | 99 / 137 | 34 / 72 | 38 | 0 | 11.758 s | `full-current-20260703-093619` | Accepted baseline before profiling; all remaining timeouts are in `tta_startup`. |
| 2026-07-03 | no full post-pivot beta recomputation | 20 s | 107 / 137 | 42 / 72 | 30 | 0 | 9.602 s | `full-no-recompute-pivot-20260703` | Accepted; profile-driven simplex change gains 8 `tta_startup` inductive files, loses none, and has no Z3 answer disagreements. |
| 2026-07-03 | rational zero/integer/unit fast paths | 20 s | 110 / 137 | 45 / 72 | 27 | 0 | 8.731 s | `full-rational-fastpaths-20260703` | Accepted; exact arithmetic fast paths gain 3 more `tta_startup` inductive files, lose none, and have no Z3 answer disagreements. |
| 2026-07-03 | rational sign/subtraction/comparison fast paths | 20 s | 116 / 137 | 51 / 72 | 21 | 0 | 7.290 s | `full-rational-sign-fastpaths-20260703` | Accepted; profile-driven exact arithmetic fast paths gain 6 more `tta_startup` inductive files, lose none, and have no Z3 answer disagreements. |

Most native rows in this log solve `check`, `keymaera`, and
`spider_benchmarks` completely; the moving metric is usually `tta_startup`.
The 2026-07-03 20-second rows solve `spider_benchmarks` completely while
continuing to improve `tta_startup` inductive cases. Where compared, no answer
disagreements with Z3 were observed on commonly solved files. Row-bound
propagation is kept as the default in its dirty-row form because it contributes
useful theory literals on the current aggregate run, while the older immediate
full-row scan remains rejected by the 2026-07-01 ablation row.

The next optimization targets should be chosen from fast-Z3/slow-native
`tta_startup` files, for example:

- `simple_startup_9nodes.missing.induct.smt2`;
- `simple_startup_9nodes.bug.induct.smt2`;
- `simple_startup_11nodes.synchro.induct.smt2`;
- `simple_startup_12nodes.bug.induct.smt2`.

Raw artifacts for the rows above are kept in the workspace as matching
`eval_results/*.tsv` and `eval_results/*.summary` files.
