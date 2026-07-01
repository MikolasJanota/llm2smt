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

## Important Ordering Constraints

Several regressions in this solver came from changing preprocessing order:

- finite-domain AMO must see top-level disequalities before simplification can
  fold them away;
- generated top-level conjunctions should not be split into thousands of
  pending assertions when simplifier passes are enabled;
- proof snapshots must be taken after simplification so atom shapes match the
  SAT encoding;
- Bool symbols should be bridged into EUF only when they appear in U-sorted
  term position.
