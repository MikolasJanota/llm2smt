# Proofs And Models

The solver has optional Lean 4 proof output for UNSAT results and basic model
printing for SAT results.

## Lean Proof Output

Proof generation is enabled with:

```sh
build/bin/llm2smt --proof proof.lean input.smt2
```

The driver enables EUF proof recording before parsing and solving. After an
UNSAT result, it calls `LeanEmitter::emit()`.

The proof consists of two layers:

1. standalone EUF theory lemmas proved by `grind`;
2. a final propositional contradiction proved by `bv_decide`.

The theory lemmas include:

- conflict clauses from EUF explanations;
- transitivity/congruence lemmas;
- ITE helper lemmas;
- equality-bridge lemmas;
- clauses involving permanent preprocessing equalities.

The final theorem imports these lemmas and the problem hypotheses, then lets
`bv_decide` close the propositional skeleton.

## Proof Snapshot

`Smt2Visitor` stores `proof_fmls_`, the assertions used as Lean hypotheses.
When preprocessing is active, the snapshot is taken after simplification. This
is important because SAT literals and proof atoms must have the same normalized
shape.

Forced atoms from preprocessing are appended to the proof snapshot. Otherwise
the EUF may use them as premises in theory lemmas without corresponding Lean
hypotheses.

## Congruence Steps

`CC::explain()` returns leaf equation ids that justify a congruence. In proof
mode it can also emit raw congruence steps:

```text
result_lhs = result_rhs
because fn_lhs = fn_rhs and arg_lhs = arg_rhs
```

`EufSolver` resolves those premise pairs to SAT literals and permanent equality
dependencies. The Lean emitter turns them into standalone `cong_N` lemmas.

## Proof Minimization

`--proof-minimize` records original SAT clauses and then runs
`minimize_proof_conflicts()` after UNSAT. The minimizer uses a fresh CaDiCaL
instance and activation literals to keep only theory conflict clauses that are
needed for an UNSAT core.

Use:

```sh
build/bin/llm2smt --proof proof.lean --proof-minimize input.smt2
```

Minimization is useful when the raw EUF lemma set is large, but it adds another
SAT solve.

## Model Printing

`get-model` is implemented in `Smt2Visitor::print_model()`. It uses:

- the flattener's original-to-flat mapping;
- CC representatives for abstract U-sort values;
- SAT model values for Bool atoms and Bool-as-term bridges;
- recorded function applications from parsing.

The model printer assigns abstract values to CC representatives lazily. For
function interpretations, it prints entries for applications observed during
parsing.

Bool-valued terms need special care. If a compound Bool formula is passed as a
UF argument, the model must use the SAT literal value associated with that
formula, not just a syntactic node identity.

## Current Limits

The proof and model paths are pragmatic developer tools, not a complete
industrial SMT-LIB implementation:

- proof output is focused on QF_UF UNSAT cases covered by the regression tests;
- proof mode disables finite-domain equality definitions;
- model printing reports observed applications rather than synthesizing a
complete total function table for every possible argument tuple.
