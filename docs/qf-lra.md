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
simplifier for ablation. Direct Boolean encoding for equalities against
arithmetic `ite` terms is enabled by default; it reduces LRA auxiliaries on
TTA-startup instances and improved repeated full-suite PAR2 in July 2026. Use
`--no-lra-ite-eq-direct` for ablation.
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
SMT-LIB term should reuse one auxiliary Real variable. Arithmetic `ite` terms
also have a structural cache keyed by the condition literal and normalized
branch expressions, so identical `ite` subterms reached through different
parse-tree nodes can share the same auxiliary. Use `--no-lra-term-cache` to
disable both caches for ablation.

Equality elimination is deliberately conservative. It only consumes arithmetic
equalities asserted unconditionally at top level, either as direct assertions or
as children of a top-level `and`; it does not use equalities guarded by `or`,
`=>`, Boolean `ite`, or negation, and it skips arithmetic equalities whose terms
contain arithmetic `ite`. Here an equality row is the normalized linear equation
`c + a1*x1 + ... + an*xn = 0` produced from one equality, stored as one constant
plus exact rational coefficients for variables. These rows are processed into a
substitution map, dependent rows are ignored, inconsistent rows add an immediate
empty SAT clause, and `get-model` reconstructs eliminated declared Real
constants from the remaining LRA model. The pass is on by default; use
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
- Figure 3.2 `Check` uses a deterministic Bland-style smallest-variable choice
  by default, with experimental option-controlled pivot alternatives;
- Section 3.2.2 conflict clauses are built from the violated row's active bound
  sources;
- Section 3.2.4 backtracking restores only bound-stack entries and leaves the
  tableau, basis, and current assignment in place.

Strict inequalities use the Section 3.3 symbolic infinitesimal representation
`c + kδ`. The final printed model chooses a positive rational value for `δ` and
substitutes it into declared Real constants.

### Exact Rational Arithmetic

All arithmetic in the LRA solver uses canonical exact rationals. A `Rational`
value is expected to satisfy these invariants after every public operation:
zero is represented as `0/1`, denominators are positive, and numerator and
denominator are reduced by their gcd unless the denominator is already `1`.
`DeltaRational` preserves the same invariant independently for both the real
part and the infinitesimal `δ` coefficient.

The simplex hot path creates many short-lived rationals while pivoting rows,
updating non-basic assignments, comparing bounds, and discovering row-bound
propagations. Profiles on `tta_startup` showed that avoidable normalization and
cross-multiplication can dominate these cases. The rational implementation
therefore includes fast paths for operations that provably preserve the
canonical form without a gcd call:

- adding, multiplying, or dividing by zero, one, and minus one;
- integer-only addition and multiplication;
- unary sign flips and subtraction from already-canonical operands;
- comparisons with matching denominators or operands of different signs.

These fast paths must not change the mathematical value or leave a
non-canonical representation behind. When extending them, add unit coverage in
`tests/test_lra_solver.cpp` that checks both equality and the stored denominator
for representative non-integer rationals, then rerun the QF_LRA eval because
small arithmetic-cost changes can move several `tta_startup` instances across a
20s timeout boundary.

The IPASIR-UP propagation callback also serves LRA implications. It performs
unate bound propagation for stronger active bounds and row-bound propagation
from the current tableau: when the active bounds on the variables in a row imply
a lower or upper bound on the basic variable, the solver propagates matching
elementary arithmetic literals with a reason clause built from the contributing
bound-source literals. The existing `--no-theory-prop` flag disables these LRA
propagations as well as EUF propagations.

## LRA Opportunities

Start new LRA performance work by classifying the benchmark shape, then choose a
technique that matches the dominant structure. The current 60s native TSV
`eval_results/full-rational-sign-fastpaths-60s-20260703.tsv` and Z3 TSV
`eval_results/full-z3-60s-20260703.tsv` show that the remaining native gap is
not spread evenly across QF_LRA. The 15 native timeouts are all generated
`tta_startup` files, and 13 native-slow/Z3-fast cases are also in
`tta_startup`.

A lightweight S-expression classifier over the 137-file suite gives this shape:

| Set | Files | Avg linear atoms | Avg arithmetic `ite` | Avg finite-domain choices | Unary/two-variable linear atoms |
| --- | ---: | ---: | ---: | ---: | ---: |
| Full QF_LRA suite | 137 | 902 | 71 | 159 | 92.2% |
| Native 60s timeouts | 15 | 2,799 | 159 | 430 | 90.2% |
| Native slow, Z3 <= 5s | 13 | 2,357 | 139 | 394 | 91.1% |

The hardest files are therefore not dense arbitrary LRA instances. They are
large Boolean encodings with thousands of `and`/`or` nodes, many arithmetic
`ite` terms, hundreds of small finite-domain equalities such as `x = 0`,
`x = 1`, ..., and mostly unary or two-variable linear atoms. Width-3 atoms still
occur, so pure difference logic is not enough, but the high fraction of
two-variable constraints makes a difference-logic/UTVPI recognizer worth
testing before deeper simplex rewrites.

Promising opportunities, in priority order:

- **Difference-logic and UTVPI fast paths.** Detect formulas or connected
  components whose linear atoms are unary or two-variable constraints and route
  them through graph-style consistency/propagation. Z3 uses specialized engines
  for RDL/IDL/UTVPI-style fragments, while the native path currently sends all
  general atoms through simplex. The first native step is a default-on
  pre-encoding UNSAT check for pure top-level unary/DL/UTVPI assertion batches;
  it is intentionally one-sided and falls back to normal encoding for SAT/model
  cases and for guarded or wider atoms.
- **Finite-domain SAT compilation.** Extend the existing finite-domain AMO and
  equality-definition work toward exactly-one clauses, value-ordering or
  symmetry-breaking constraints under a flag, and stronger guarded implications
  from domain choices to simple bounds. This matches the hundreds of repeated
  value choices in the hard `tta_startup` files.
- **ITE-aware preprocessing.** Continue reducing arithmetic `ite` chains before
  LRA registration. The hard cases average more than 100 arithmetic `ite` terms,
  so missed sharing or missed constant/domain simplification can create many
  unnecessary auxiliary rows and guarded atoms. The current term cache includes
  structural sharing for arithmetic `ite` terms with the same condition and
  normalized branches; the micro-regression
  `lra38_structural_ite_term_cache.smt2` ensures two separate identical
  subterms allocate one auxiliary. On 2026-07-04 the 20s hard sample was
  essentially neutral but in the right direction, 8/10 solved and PAR2 8.658 s
  with the cache versus 8/10 and PAR2 9.896 s with `--no-lra-term-cache`.
- **Indexed cheap bound propagation.** Z3 emphasizes direct and row-derived
  bound propagation using indexes from variables to bound atoms. Native
  row-bound propagation exists, but the aggregate result depends heavily on scan
  cost. The next version should focus on reverse indexes, hit-rate counters, and
  strict candidate budgets rather than broader full-row scans.
- **Simplex pivot and sparse-row engineering.** If shape-specific
  preprocessing does not remove the gap, profile the remaining slow cases for
  pivot count, row density, and rational normalization. Candidate work includes
  pivot choices that reduce fill-in/coefficient growth and, as a larger
  option-controlled experiment, a sum-of-infeasibilities simplex mode for
  pivot-heavy instances.
- **Theory-aware SAT branching.** The finite-domain branch hint is currently
  narrow. A better callback should prefer literals that decide small-domain
  values or strong bounds in the current LRA component, and should be evaluated
  against the native-slow/Z3-fast `tta_startup` subset before becoming default.

### DL/UTVPI Fast Paths

`--no-lra-dl-fast-path` disables the default parser-local graph precheck for
top-level QF_LRA assertions. The precheck accepts only unconditional assertions
and direct children of top-level `and`; it rejects guarded atoms under `or`,
`=>`, Boolean `ite`, negation, or `let`. Accepted arithmetic atoms must be
unary, difference-logic (`x - y <= c`), or UTVPI (`±x ± y <= c`) constraints
over exact rationals. Equalities are expanded to both non-strict directions.

The pass is deliberately one-sided: it may emit an empty SAT clause when the
accepted graph has a negative cycle, but it never returns SAT and never prints a
model. If the graph is consistent, or if any assertion is outside the fragment,
the parser falls back to the existing SAT/LRA encoding. This keeps model
printing and mixed LRA completeness in the Dutertre/de Moura-style simplex core
while avoiding SAT variables, LRA rows, checks, and pivots for pure graph
contradictions.

The encoding uses the standard signed-variable UTVPI reduction. Unary bounds
are represented both as zero-node DL edges and as signed-variable edges, so
simple contradictions such as `x <= 0`, `x >= 1` and UTVPI contradictions such
as `x + y <= 1`, `x >= 1`, `y > 0` are caught before simplex.

On the current benchmark set this is expected to be neutral-to-small: the
shape scan found no purely relational DL files and only 14 tiny pure
unary/DL-with-equality files, all already solved in a few milliseconds. The
value of the pass is therefore mostly as infrastructure for component-level
fragment detection, and as protection for synthetic or future pure DL/UTVPI
inputs. Focused regressions show the intended effect: the pure DL and UTVPI
UNSAT examples now report `lra.dl_fast_path_unsats=1`, `sat.vars=0`,
`lra.check_calls=0`, and `lra.pivots=0`; `--no-lra-dl-fast-path` restores the
normal simplex path.

### Simple Graph Propagation

`--lra-simple-graph-conflicts` enables conflict-only graph reasoning for the
same unary, difference-logic, and UTVPI subset recognized by the parser
precheck. The solver maintains active graph edges incrementally as graph-shaped
arithmetic literals are assigned and removed on backtrack, and it runs
negative-cycle detection only when those active edges have changed or during a
final model check. This avoids the repeated full active-edge rebuild that made
the first graph propagation experiment expensive.

`--lra-simple-graph-prop` enables an experimental auxiliary graph reasoner for
the simple-constraint subset. It recognizes unary bounds, difference-logic
atoms such as `x - y <= c`, and UTVPI-shaped atoms such as `x + y <= c` by
building difference edges over signed variables. The propagation flag implies
the conflict-only checks. `--lra-simple-graph-budget N`
limits the number of graph atom candidates inspected per discovery call
(`0` means unlimited).

This is deliberately not a replacement for simplex. The graph reasoner only
uses currently active SAT-assigned literals, can add sound conflict or
propagation clauses derived from the simple subset, and then leaves the mixed
LRA problem to the existing Dutertre/de Moura-style incremental simplex core.
This matters because the `tta_startup` files still contain width-3 atoms, so a
graph-satisfiable subset does not imply full LRA satisfiability.

The design follows the standard split used in SMT arithmetic solvers: keep a
complete LRA simplex engine for the mixed problem, but exploit specialized
fragments when the formula shape allows it. The relevant references are
Dutertre and de Moura, *A Fast Linear-Arithmetic Solver for DPLL(T)*, for the
simplex core and exact strict-bound treatment; Bjørner and Nachmanson,
*Arithmetic Solving in Z3*, for fragment-specialized arithmetic engines in Z3;
and Lahiri and Musuvathi, *An Efficient Decision Procedure for UTVPI
Constraints*, for the signed-variable graph reduction, which represents
`±x ± y <= c` as difference constraints over `x` and `-x`.

The first implementation is intentionally default-off. On 2026-07-04, the 20s
quick suite regressed from 5/5 solved and PAR2 1.077 to 4/5 solved and PAR2
10.032 with `--lra-simple-graph-prop`; the 20s hard suite regressed from 8/10
solved and PAR2 8.681 to 6/10 solved and PAR2 19.412. Smaller candidate
budgets of 100 and 1000 were also worse on quick. After review, pure DL
negative-cycle conflicts were made cheaper and can avoid simplex entirely on a
synthetic 201-edge chain, but mixed-instance propagation still does too much
repeated shortest-path work. The next graph iteration should reduce that work
and add a stronger hit-rate guard before any default-on evaluation.

The conflict-only incremental edge-cache variant is also default-off. It fixes
the assignment-time rebuild problem and preserves pure graph UNSAT tests, but
on 2026-07-04 it still regressed the 20s quick suite from 5/5, PAR2 1.333 s to
5/5, PAR2 1.887 s, and the 20s hard suite from 8/10, PAR2 9.023 s to 5/10,
PAR2 21.905 s. Treat it as a diagnostic option for pure graph-heavy cases, not
as a mixed-`tta_startup` default candidate.

### RDL Cotton/Maler Propagation

`--lra-rdl-prop=cotton` enables a narrower, default-off propagation experiment
for real difference logic (RDL). It recognizes only atoms reducible to one
edge `x - y <= c`, plus unary bounds encoded through a zero node; UTVPI remains
on the older `--lra-simple-graph-prop` path. `--lra-rdl-prop=off` is the
default, and `--lra-rdl-prop-budget N` limits candidate inspections per
propagation callback (`0` means unlimited).

The design follows Scott Cotton and Oded Maler, *Fast and Flexible Difference
Constraint Propagation for DPLL(T)*, SAT 2006; see `sandbox/dl_cotton.pdf`.
The implementation keeps Cotton/Maler-style literal labels: `Lambda` for
unassigned graph literals, `Sigma` for assigned but not yet propagated edges,
`Pi` for assigned and propagated edges, and `Delta` for implied literals
queued to the SAT solver but not yet assigned. It is lazy: assignment callbacks
only append active edges and mark them `Sigma`; shortest-path propagation is
performed when the IPASIR-UP propagation callback asks the theory for work.

Candidate filtering uses the paper's relevancy idea. For each new `Sigma`
edge, the solver runs the two relevant shortest-path searches around that edge
and inspects only candidate atoms whose endpoints can be affected by those
searches. A candidate that passes the filter is still validated by an exact
shortest-path implication check over the active edge set, and its reason clause
is built from the source literals along the actual paths. Negative-cycle
conflicts are reported as theory clauses before the simplex core is used.

This is intentionally not an exhaustive Nieuwenhuis/Oliveras-style propagation
baseline that scans all implied bounds after every assignment. It is a scoped
experiment meant to avoid the repeated all-pairs behavior that made the broad
simple-graph propagator regress. The complete mixed LRA solver remains the
Dutertre/de Moura simplex core, and the RDL option should stay default-off
until quick and hard PAR2 evidence shows a win or a clearly isolated
benchmark-family benefit. The stats `lra.rdl_prop_*` expose active edges,
`Sigma` queue size, candidate counts, relevant candidates, enqueues,
duplicates, conflicts, budget cutoffs, and shortest-path relaxations.

The first local 20s quick run on 2026-07-05 rejected this as a default
candidate: current defaults solved 5/5 with PAR2 1.051 s, while
`--lra-rdl-prop=cotton` solved 4/5 with PAR2 10.200 s and timed out on
`simple_startup_10nodes.missing.induct.smt2`. Do not run hard or full promotion
experiments for this version without first reducing callback candidate and
shortest-path cost.

After tightening RDL reasons so future unprocessed `Sigma` edges are masked
out, the focused tests and full CTest suite passed, but the performance result
remained a rejection: the 2026-07-05 quick rerun solved 5/5 with PAR2 1.243 s
by default and 3/5 with PAR2 16.146 s under `--lra-rdl-prop=cotton`.
SLURM YinYang job `107632` fuzzed the QF_LRA `check` seeds with
`--lra-rdl-prop=cotton` against Z3, processed 2 valid seeds, and found 0 bug
triggers. Logs were collected as `slurm_logs/llm2smt-rdl-yinyang-check-107632.*`.

### Pivot Heuristics

`--lra-pivot-heuristic min-var|min-column` controls the entering-variable choice
inside simplex `Check`. The default `min-var` preserves the current
Dutertre/de Moura Figure 3.2 behavior: choose the smallest eligible non-basic
variable. This is deterministic and Bland-style, so it is the trusted baseline
for correctness and termination.

`min-column` is an experimental local heuristic inspired by the implementation
discussion in King, Barrett, and Dutertre, *Simplex with Sum of Infeasibilities
for SMT*. It chooses the eligible entering variable with the shortest active
tableau column and breaks ties by variable id. The goal is to reduce pivot
fallout and row-update work on pivot-heavy checks while leaving the tableau
algorithm, exact rational arithmetic, and conflict explanations unchanged.

`--lra-pivot-bland-after N` switches a single check call back to `min-var` after
`N` pivots (`0` disables the cap). This keeps non-Bland experiments bounded by
the known Bland-style fallback. The stats `lra.pivot_candidates`,
`lra.pivot_min_column_choices`, `lra.pivot_bland_fallbacks`, and
`lra.check_max_pivots` are intended for comparing pivot behavior before looking
at aggregate PAR2.

The first min-column implementation is default-off. On 2026-07-04 with
`--lra-pivot-heuristic min-column --lra-pivot-bland-after 1000`, the 20s quick
suite stayed at 5/5 solved but regressed PAR2 from 1.333 s to 2.758 s, and the
20s hard suite stayed at 8/10 solved but regressed PAR2 from 9.023 s to
10.349 s. The combined min-column plus graph-conflict candidate was worse
again on quick, solving only 3/5 with PAR2 16.238 s. Keep this as an
instrumented profiling knob until a target file shows lower pivot count and
lower wall time together.

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
  ordering constraints;
- component-level DL/UTVPI extraction when only part of the formula fits the
  graph fragment; the current default fast path is whole-batch and one-sided;
- default-on simple-graph propagation for assigned unary/DL/UTVPI atoms; the
  implementation exists behind `--lra-simple-graph-prop` and needs aggregate
  PAR2 evidence before promotion.

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
`--lra-row-bound-indexed-dirty-scan` enables an experimental reverse row index
for this dirty scan. The indexed mode is default-off because it improves some
long-tail induction instances but regressed quick and hard PAR2 samples in the
July 2026 evaluation.

The propagation scanner also keeps per-variable lower-bound and upper-bound atom
lists. This is not a theory-strengthening heuristic: it preserves the same
unate and row-bound implications as the older `atoms_by_var_` scan, but avoids
an unordered-map lookup and a bound-kind branch for each inspected atom. A
2026-07-05 A/B against commit `f3c6145` was mildly positive but small: quick
PAR2 moved from 2.677 s to 2.395 s, and hard PAR2 moved from 9.673 s to
9.624 s, with the same solved counts on both suites.

`--lra-row-bound-min-hit-rate N` and `--lra-row-bound-hit-window N` are
diagnostic controls for disabling row-bound propagation after a low queued-literal
rate (`N` is measured per million inspected candidates). They are default-off.
The first 2026-07-05 trial rejected the cutoff as a default candidate: quick
PAR2 regressed from 1.323 s to 3.007 s, and hard regressed from 8/10 solved,
PAR2 9.136 s, to 7/10 solved, PAR2 12.252 s.

A 2026-07-08 frame-pointer `perf` pass on
`simple_startup_10nodes.missing.induct.smt2` and
`simple_startup_15nodes.missing.induct.smt2` found the remaining hot path in
incremental simplex work rather than parsing or SAT encoding. On the 10-node
case, about two thirds of sampled time was under `pivot_and_update`, with
`std::map` row operations, exact-rational arithmetic, and row-bound propagation
visible in the flat profile. The 15-node case made 54,717 LRA checks, 14,758
pivots, and inspected 4,349,011 row-bound candidates before solving in about
53 seconds locally. Treat sparse-tableau representation and cheaper pivot row
updates as the next high-value implementation experiments.

The same profiling pass tried lazy row-bound reason construction: compute row
bounds first, skip already-known candidate literals, and build the source vector
only for an actual enqueue or conflict. This was rejected for now. It did reduce
eager reason materialization, but the profiled startup cases often did enqueue
from inspected rows, so the extra row walk offset the saved allocation
(`10nodes` stayed near 4.6 s and `15nodes` moved from about 53.2 s to about
54.1 s). The retained low-risk part is reserving row-bound source vectors to the
row width before filling them.

Follow-up implementation probes from the same 2026-07-08 pass:

- Pivot variable lists no longer sort the whole `basic_vars_` and
  `nonbasic_vars_` vectors after every pivot. The replacement variable is erased
  and reinserted with `lower_bound`, preserving the order expected by the
  min-variable pivot heuristic. This is retained as a small default-on cleanup:
  the local quick suite solved 5/5 with PAR2 1.196 s, and the local hard suite
  solved 8/10 with PAR2 8.742 s.
- A stored-position reverse row index for `--lra-tableau-row-index` was tried
  and rejected. It removed the linear search in `unregister_row_coeffs`, but the
  added per-row hash-map maintenance made the indexed 15-node startup case worse
  at about 78 s. The indexed mode remains default-off with the older simpler
  maintenance.
- An ordered-map merge update for pivot-affected rows was tried and rejected.
  It replaced repeated `std::map::operator[]` updates with a single sorted merge
  into a fresh map, but rebuilding maps cost more than the saved lookups:
  `simple_startup_15nodes.missing.induct.smt2` moved to about 56.7 s with
  identical solver counters. A real sparse-vector tableau row representation is
  still the relevant larger experiment; rebuilding `std::map` rows is not it.

`--lra-unate-lemmas` enables an experimental static arithmetic-lemma pass
inspired by cvc5's unate arithmetic lemmas. It emits SAT-visible binary clauses
between already-created simple literals on the same variable, for example
`x <= 1 -> x <= 2`; equality-to-bound and finite-domain choice exclusions are
left to the existing finite-domain encodings when those are enabled. The current
implementation emits adjacent upper-bound and lower-bound chains rather than all
pairwise implications, because the pairwise variant added too much CNF. This is
default-off: on the 2026-07-08 local quick suite it kept 5/5 solved but regressed
PAR2 from 2.732 s to 3.615 s, and on the hard suite it kept 8/10 solved but
regressed PAR2 from 9.360 s to 9.899 s. It did reduce pivots on selected
`tta_startup` instances, but not enough to justify enabling it by default.

`--lra-tableau-row-index` enables a separate experimental reverse row index for
simplex `update` and `pivot` scans. The intended target is pivot-heavy problems
where scanning every basic row dominates the profile. It is default-off: on the
2026-07-04 quick suite it solved 5/5 but regressed PAR2 from 1.016 s to 1.813 s,
while the hard suite stayed mixed at 8/10 solved and PAR2 8.838 s. Keep it as an
engineering experiment for profiled sparse-tableau cases rather than a default
heuristic.

`--stats` prints LRA counters for assignments, simplex checks, pivots,
conflicts, conflict-clause literals, delivered propagations, propagation
candidates considered, enqueue attempts, duplicate/already-known propagated
literals, propagation conflicts, registered elementary atoms, tableau term variables, Real
variables, row-bound candidates, row-bound enqueue attempts, row-bound
duplicates, row-bound propagations, row-bound hit-rate cutoffs, equality-elimination
rows/variables/contradictions, local constant folds, arithmetic `ite`
simplifications, finite-domain bound/equality-definition clauses, simple-graph
atoms/edges/candidates/propagations/conflicts/budget cutoffs, and LRA-local
cache hits. The DL/UTVPI precheck counters report attempts, UNSAT hits,
fallbacks, accepted atoms, and rejected batches. It also prints SAT encoding
size counters. Extra propagation traffic can speed up hard bound-heavy cases but can
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
| 2026-07-03 | local loop default, paired with `--lra-ite-eq-direct` candidate | 20 s | 114 / 137 | 49 / 72 | 23 | 0 | 7.589 s | `loop-ite-eq-direct-ref-full-full-default-20260703-223749` | Baseline leg for the reference-backed loop run. |
| 2026-07-03 | `--lra-ite-eq-direct` candidate, reference-backed loop | 20 s | 116 / 137 | 51 / 72 | 21 | 0 | 6.937 s | `loop-ite-eq-direct-ref-full-full-candidate-20260703-223749` | Promising default candidate; no Z3/OpenSMT answer disagreements on 116 commonly solved files, and the loop ranks remaining fast-reference/native-slow targets. |
| 2026-07-03 | local loop default, repeat 1 | 20 s | 113 / 137 | 48 / 72 | 24 | 0 | 7.842 s | `loop-ite-eq-direct-repeat-1-full-default-20260703-225957` | Repeated timing check for the direct-ITE candidate. |
| 2026-07-03 | `--lra-ite-eq-direct` candidate, repeat 1 | 20 s | 116 / 137 | 51 / 72 | 21 | 0 | 6.919 s | `loop-ite-eq-direct-repeat-1-full-candidate-20260703-225957` | Repeats the full-suite gain; no Z3/OpenSMT disagreements on commonly solved files. |
| 2026-07-03 | local loop default, repeat 2 | 20 s | 116 / 137 | 51 / 72 | 21 | 0 | 7.374 s | `loop-ite-eq-direct-repeat-2-full-default-20260703-230538` | Stronger default run shows solved-count noise at the 20 s cutoff. |
| 2026-07-03 | `--lra-ite-eq-direct` candidate, repeat 2 | 20 s | 116 / 137 | 51 / 72 | 21 | 0 | 6.943 s | `loop-ite-eq-direct-repeat-2-full-candidate-20260703-230538` | Solved count ties the strongest default repeat while preserving a PAR2 win; promoted to the default on 2026-07-04 with `--no-lra-ite-eq-direct` retained as the ablation. |
| 2026-07-04 | DL/UTVPI fast path default on | 20 s | 114 / 137 | 49 / 72 | 23 | 0 | 7.478 s | `full-dlfast-default-20260704` | Accepted as default-on but small; the pure graph regressions avoid SAT/LRA rows, and the paired ablation below shows one extra local `tta_startup` solve with no Z3 answer disagreements. |
| 2026-07-04 | `--no-lra-dl-fast-path` ablation | 20 s | 113 / 137 | 48 / 72 | 24 | 0 | 7.604 s | `full-dlfast-off-20260704` | Slightly worse than the default-on run; keep the disable flag because the current benchmark set has few pure DL/UTVPI instances and timing near the cutoff is noisy. |
| 2026-07-08 | local hard suite, default | 20 s | 8 / 10 | 7 / 9 | 2 | 0 | 9.360 s | `scripts/qf_lra_eval.py --suite hard` | Baseline for static unate lemma experiment. |
| 2026-07-08 | local hard suite, `--lra-unate-lemmas` | 20 s | 8 / 10 | 7 / 9 | 2 | 0 | 9.899 s | `scripts/qf_lra_eval.py --suite hard --opts=--lra-unate-lemmas` | Rejected as a default candidate; same solved count, worse PAR2 despite lower pivot counts on selected instances. |
| 2026-07-08 | local hard suite, pivot-list replacement cleanup | 20 s | 8 / 10 | 7 / 9 | 2 | 0 | 8.742 s | `local-retained-pivot-sort-hard-20260708` | Retained as a small default-on cleanup; avoids sorting two basis vectors on every pivot. |

Most native rows in this log solve `check`, `keymaera`, and
`spider_benchmarks` completely; the moving metric is usually `tta_startup`.
The 2026-07-03 20-second rows solve `spider_benchmarks` completely while
continuing to improve `tta_startup` inductive cases. Where compared, no answer
disagreements with Z3 were observed on commonly solved files. Row-bound
propagation is kept as the default in its dirty-row form because it contributes
useful theory literals on the current aggregate run, while the older immediate
full-row scan remains rejected by the 2026-07-01 ablation row.

The repeated `--lra-ite-eq-direct` loop runs show a stable PAR2 signal despite
borderline solved-count noise. Across the three completed full runs, the
candidate improved average PAR2 by 0.652 s, 0.923 s, and 0.431 s respectively.
The strongest default repeat tied the candidate at 116 solved files, but still
had higher PAR2. The largest consistent common-solved speedups were in
`tta_startup`, including `9nodes.missing.induct`, `8nodes.missing.induct`,
`4nodes.abstract.induct`, `7nodes.missing.induct`, and `6nodes.bug.induct`.
No Z3/OpenSMT answer disagreements were observed on the candidate's commonly
solved files in any completed repeat. Direct ITE equality encoding is therefore
enabled by default after these runs, with `--no-lra-ite-eq-direct` kept for
ablation and regression checks.

The next optimization targets should be chosen from fast-Z3/slow-native
`tta_startup` files, for example:

- `simple_startup_12nodes.synchro.induct.smt2`;
- `simple_startup_12nodes.missing.induct.smt2`;
- `simple_startup_12nodes.bug.induct.smt2`;
- `simple_startup_15nodes.bug.induct.smt2`;
- `simple_startup_14nodes.synchro.induct.smt2`.

Raw artifacts for the rows above are kept in the workspace as matching
`eval_results/*.tsv` and `eval_results/*.summary` files.
