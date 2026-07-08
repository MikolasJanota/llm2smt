# Preprocessing

Preprocessing operates over `NodeId` formulas before SAT encoding. It is
controlled by `PreprocOptions` and invoked from
`Smt2Visitor::flush_pending_fmls()`.

## Flush Pipeline

For accumulated assertions, the flush pipeline is:

1. optional NNF conversion;
2. top-level conjunction splitting when simplification is disabled;
3. top-level disequality collection for finite-domain strengthening;
4. optional disjunction equality bridging;
5. optional simplifier passes;
6. proof snapshot after simplification;
7. finite-domain AMO and equality-definition encoding;
8. final formula-to-CNF encoding.

The order is deliberate. Disequality facts are collected before simplification
because simplification can fold asserted disequalities to `true`; finite-domain
AMO needs the original disequality information.

## NNF

`src/preprocessor/nnf.h` converts formulas to negation normal form. It supports
the Boolean connectives stored in `NodeManager`: `not`, `and`, `or`,
`implies`, `xor`, `iff`, and Bool `ite`.

`--nnf-memo` enables memoization over `(node, polarity)`. This helps DAG-heavy
inputs but can slow tree-shaped inputs due to hash-map overhead, so it is
opt-in.

## Simplifier

`src/preprocessor/simplifier.*` performs repeated passes over assertions.

Implemented simplifications:

- constant folding through Boolean connectives;
- unit propagation for atoms and negated atoms;
- equality normalization with a small union-find over `NodeId`s;
- known-disequality folding;
- optional flattening of nested `and` and `or`.

Forced positive equality atoms are registered as permanent EUF equalities
rather than SAT unit clauses. Other forced atoms become SAT units. In proof
mode, forced atoms are also appended to the proof snapshot so later theory
clauses have visible hypotheses.

## Disjunction Equality Bridge

`src/preprocessor/disjunction_bridge.*` looks inside `or` subformulas. For each
branch, it computes the equality closure from conjunctions of equality atoms.
If an equality is implied by every branch, the pass derives it as a unit fact.

Example:

```text
(x = y and y = z) or (x = w and w = z)
```

Both branches imply `x = z`, so the bridge derives `x = z`.

This targets diamond-shaped QF_UF benchmarks where lazy search otherwise
explores exponentially many branch combinations. Caps on branch count and pair
checks avoid spending too much preprocessing time on wide disjunctions.

In proof mode, the bridge records the source top-level formula and source `or`
node so the Lean emitter can generate implication-form bridge lemmas.

## Finite-Domain AMO

The finite-domain AMO pass recognizes terms constrained to equal one of several
distinct values. Top-level disequalities among EUF values justify SAT-level
at-most-one clauses among the value-choice literals. In the QF_LRA parser path,
simple equalities over one Real variable, such as `x = 1`, `x = 2`, and
`x = 3`, also get SAT-level at-most-one clauses directly.

This is enabled by default and disabled with:

```sh
--no-finite-domain-amo
```

The pass was added for NEQ-style finite-model benchmarks where generic EUF
search spends too much time rediscovering simple domain-choice exclusivity, and
for QF_LRA encodings that model small numeric domains with equality
disjunctions.

## Finite-Domain Equality Definitions

When finite-domain choices are available for two terms, the solver can define
the equality between those terms using matching value choices. This adds SAT
clauses tying:

```text
x = y
```

to the disjunction of cases where `x` and `y` choose the same finite-domain
value.

This is enabled by default when finite-domain AMO is enabled, and disabled with:

```sh
--no-finite-domain-eqdefs
```

It is skipped in proof mode because the proof pipeline currently reasons about
the original EUF clauses and theory lemmas rather than these SAT-level derived
definitions.

## Finite-Domain Static Symmetry Avoidance

QF_UF has an experimental finite-domain value-precedence pass, enabled with:

```sh
--finite-domain-value-precedence
```

The pass is inspired by the static symmetry reduction used in Paradox-style
finite model finding and by the MACE-style value-precedence clauses formalized
by Reger, Riener, and Suda. It is deliberately default-off: this solver remains
a DPLL(T)-style SMT solver, not a SAT-reduction finite-model finder, and the
effect of static symmetry clauses needs benchmark evidence before promotion.

The implementation reuses finite-domain choice disjunctions of the form:

```text
(or (= p v0) (= p v1) ... (= p vn))
```

where the values are pairwise distinct by asserted disequalities. Terms are
grouped only when they have the same value set. Within an accepted group, terms
and values are ordered by stable `NodeId`, and the pass adds value-precedence
clauses:

- term `p_i` may use only values `v_0 ... v_i`;
- if `p_i = v_j` for `j > 0`, some earlier term `p_k` must use `v_{j-1}`.

Existing finite-domain ALO clauses from the original disjunctions and AMO
clauses from `--no-finite-domain-amo`'s default-on counterpart provide the
exact-one semantics; this pass adds only the static symmetry restrictions.

The value constants must be uninterpreted and undistinguished. A candidate group
is rejected if any value appears outside the domain-choice equalities and
value-disequality facts, for example as an argument to a predicate or function.
This keeps the transformation scoped to genuinely interchangeable domain
elements.

The pass is disabled in proof mode. Term definitions, incremental model-size
search, full sort inference, and Paradox's broader finite-model search strategy
are intentionally out of scope for this branch.

## SMT-Native QF_UF Symmetry Breaking

```text
--uf-symmetry-breaking
```

This default-off pass follows the SMT-native symmetry-breaking direction used
by veriT and exposed by Yices as `break-symmetries`.  It is inspired by
Déharbe, Fontaine, Merz, and Woltzenlogel Paleo's constant-permutation theorem:
if a formula is invariant under permutations of uninterpreted constants
`c0 ... cn`, and a term is known to take one of those values, the solver can add
a restriction that keeps only one representative of the symmetric search space.
SyMT-style graph automorphism is deliberately not implemented here; this pass
uses a cheap syntactic invariance check over the existing `NodeId` formula DAG.

The pass reuses the same finite-domain choice facts as the MACE-style pass:

```text
(or (= t c0) (= t c1) ... (= t cn))
```

with pairwise disequalities between all values.  Unlike
`--finite-domain-value-precedence`, the values may appear elsewhere in the
formula, including in predicate and function applications.  The candidate value
set is accepted only if the whole accumulated formula is unchanged, modulo
commutativity of `and`, `or`, and equality, under both the cycle and first-swap
generators for the value constants.  Top-level assertions are compared as a
multiset, so a permutation may swap two asserted formulas.

For each accepted value set, eligible finite-domain terms are processed in
stable `NodeId` order and the pass emits full value-precedence clauses over the
term sequence.  Term `p_i` may use only the first `i+1` values, and
`p_i = v_j` for `j > 0` implies that some earlier `p_k` used `v_{j-1}`.  The
existing finite-domain ALO/AMO clauses still provide exact-one semantics; this
pass only removes value-renaming representatives.  This is stronger than the
earlier cumulative-constant prototype and is closer to the Paradox/Reger
principal-term ordering clauses.

One important soundness condition is that the ordered finite-domain terms must
not themselves contain the permuted values.  For example, the group
`(f c0), (f c1), ...` over values `c0, c1, ...` is not a fixed ordered term
sequence under a value permutation; the terms move with the values.  A QG-style
table such as `(op c_i c_j)` has the same issue.  The recognizer therefore
drops moving terms from the ordered sequence even if the formula as a whole is
invariant under value permutations.  If an invariant value set also contains
fixed finite-domain terms, such as extra constants whose definitions do not
mention the values, those fixed terms can still receive value-precedence
clauses.  If no fixed term remains, the candidate is rejected.

The new stats are:

- `preproc.uf_symmetry_sets`
- `preproc.uf_symmetry_values`
- `preproc.uf_symmetry_terms`
- `preproc.uf_symmetry_clauses`
- `preproc.uf_symmetry_rejected_noninvariant`

The pass is disabled in proof mode and remains experimental.

On the local QF_UF smoke/performance set (`tests/smt2` plus the available
`sandbox/non-incremental/QF_UF/NEQ` and `PEQ` samples), a 20-second paired SLURM
run on July 7, 2026 produced:

```text
files=209
disagreements=0
default.ok=171
default.timeout=38
default.par2=8.492046
candidate.ok=195
candidate.timeout=14
candidate.par2=3.798648
candidate.uf_symmetry_active_files=101
candidate.sum.preproc.uf_symmetry_clauses=513
```

The same candidate also completed a YinYang QF_UF fuzz run over the combined
209-file seed directory with 124 valid seeds and no bug triggers.  These numbers
are promising enough to justify broader evaluation, but the option remains
default-off until it has more benchmark and fuzz coverage.

After strengthening the emitted clauses to full value precedence,
`sandbox/non-incremental/QF_UF/PEQ/PEQ018_size6.smt2` changed from a 30-second
timeout to `unsat` in about 5.7 seconds under the tuned UF command line
(`--preprocess-passes 4 --eq-bridge --prop-interval 32
--prop-assign-threshold 0.25 --prop-delivery-budget 1000
--uf-symmetry-breaking`).  The same run emitted 255 UF symmetry clauses for 51
finite-domain terms over 6 values.

### UF Symmetry Fuzzing

The symmetry pass has two dedicated test artifacts:

- `scripts/gen_uf_symmetry_seeds.py` writes a deterministic corpus in
  `tests/fuzz/uf_symmetry`.
- `scripts/fuzz_uf_symmetry.py` is a randomized differential fuzzer for the
  fragile recognizer boundary.

The deterministic corpus contains fixed-choice cases that should emit symmetry
clauses, moving-term cases that must emit zero clauses, and mixed fixed/moving
cases that should keep only the fixed terms.  The CTest
`smt2/uf_symmetry_generated_seed_corpus` checks all generated seeds and prevents
both the QG moving-term bug and the NEQ fixed-term regression from coming back.

The randomized fuzzer compares the tuned solver with and without
`--uf-symmetry-breaking`, and can optionally compare against a reference solver:

```bash
python3 scripts/fuzz_uf_symmetry.py --count 1000 --seed 7
python3 scripts/fuzz_uf_symmetry.py --count 1000 --seed 7 --ref 'z3 model_validate=true'
```

It generates satisfiable fixed-choice, moving-unary, mixed fixed/moving,
moving-binary, and Latin-square-like QF_UF instances.  For moving-only cases,
it checks that `preproc.uf_symmetry_clauses` stays zero; for fixed and mixed
cases, it checks that some symmetry clauses are emitted.  Counterexamples are
saved under `fuzz_fails/uf_symmetry` by default.

The initial local run after adding the moving-term guard checked 2,000 generated
instances with no disagreements:

```text
checked=2000
failures=0
fixed=318
moving=1682
sym_clause_cases=367
```

## QF_LRA Equality Elimination

Most of this page describes the generic `NodeId` preprocessor. QF_LRA also has
parser-local preprocessing in `Smt2Visitor`, because arithmetic atoms are lowered
directly into SAT and LRA objects instead of first becoming generic `NodeId`
formulas.

The main parser-local arithmetic pass is Gaussian-elimination-style equality
elimination. Before registering later LRA atoms, the parser collects linear
equalities that are asserted unconditionally at top level, either as direct
assertions or as children of an already flattened top-level `and`. Each equality
is converted to an exact rational linear row: a normalized equation of the form
`c + a1*x1 + ... + an*xn = 0`, stored as one constant plus rational
coefficients for variables. These are called rows because the pass treats them
like rows of a linear system during Gaussian elimination. The pass chooses a pivot variable,
preferring internal `__lra_` auxiliaries before declared Real constants, and
stores a substitution for that pivot. Later rows and arithmetic atoms are
rewritten through the substitution map.

The pass is deliberately conservative:

- guarded equalities under `or`, `=>`, Boolean `ite`, or negation are ignored;
- arithmetic equalities containing arithmetic `ite` terms are ignored;
- dependent rows are ignored;
- inconsistent rows immediately add an empty SAT clause;
- eliminated declared Real constants are reconstructed for model printing.

This is enabled by default and disabled with:

```sh
--no-lra-eq-elim
```

The number of processed rows is capped with:

```sh
--lra-eq-elim-limit N
```

## QF_LRA DL/UTVPI Precheck

After equality elimination and before normal SAT/LRA registration, the QF_LRA
parser runs a conservative graph precheck for unconditional top-level
unary, difference-logic, and UTVPI atoms. It uses exact rational arithmetic and
the standard signed-variable UTVPI graph encoding. The pass is one-sided: a
negative cycle emits an empty SAT clause, while graph-consistent or unsupported
batches fall back to the normal encoding.

This precheck is enabled by default and disabled with:

```sh
--no-lra-dl-fast-path
```

It intentionally ignores guarded atoms under Boolean structure other than
top-level `and`, and it does not attempt to produce SAT answers or models.

See [](qf-lra.md) for the QF_LRA-specific performance notes and ablation
results.

## Important Ordering Constraints

Several regressions in this solver came from changing preprocessing order:

- finite-domain AMO must see top-level disequalities before simplification can
  fold them away;
- generated top-level conjunctions should not be split into thousands of
  pending assertions when simplifier passes are enabled;
- proof snapshots must be taken after simplification so atom shapes match the
  SAT encoding;
- Bool symbols should be bridged into EUF only when they appear in U-sorted
  term position;
- QF_LRA equality elimination must run before later arithmetic atom
  registration so atoms see the rewritten linear expressions;
- QF_LRA DL/UTVPI prechecking must run after equality elimination but before
  arithmetic atom registration, because it may emit an immediate UNSAT clause
  without creating SAT literals or LRA tableau rows.
