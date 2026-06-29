# Architecture

`llm2smt` implements a DPLL(T)-style solver for quantifier-free uninterpreted
functions. The SAT layer owns Boolean search and calls an EUF theory plugin via
IPASIR-UP style callbacks. The EUF layer maintains congruence closure,
discovers conflicts, optionally propagates implied equalities, and explains
theory lemmas back to the SAT solver.

## Main Components

| Area | Files | Responsibility |
| --- | --- | --- |
| Driver | `src/main.cpp` | Command-line options, parser setup, solver objects, proof emission, stats. |
| Core IR | `src/core/node*.{h,cpp}`, `src/core/symbol_table.h` | Hash-consed `NodeId` DAG and declared symbols/sorts. |
| Parser/encoder | `src/parser/smt2_visitor*.{h,cpp}` | SMT-LIB commands, formula construction, preprocessing flush, SAT clauses, model printing. |
| Preprocessor | `src/preprocessor/*` | NNF, simplification, equality bridging, finite-domain encodings. |
| SAT backend | `src/sat/cadical_solver*.{h,cpp}`, `src/sat/ipasir_up.h` | CaDiCaL wrapper and external propagator interface. |
| EUF theory | `src/theories/euf/*` | Term flattening, congruence closure, conflicts, propagation, explanations. |
| Proofs | `src/proof/*` | Lean proof generation and optional theory-lemma minimization. |
| Tests | `tests/*` | Unit tests and SMT2 end-to-end regression tests. |

## Solver Lifecycle

The executable starts in `src/main.cpp`.

1. Parse command-line flags into `PreprocOptions` and solver controls.
2. Construct `Stats`, `NodeManager`, `EufSolver`, and `CaDiCaLSolver`.
3. Connect the EUF solver as CaDiCaL's external propagator.
4. Parse SMT-LIB2 with ANTLR and visit commands through `Smt2Visitor`.
5. Declarations populate the symbol table.
6. Assertions are either encoded directly or accumulated as `NodeId` formulas
   and flushed through preprocessing.
7. `check-sat` invokes CaDiCaL.
8. CaDiCaL drives EUF callbacks during search.
9. The visitor prints `sat`, `unsat`, or `unknown`.
10. Optional model/proof/stat output is emitted after solving.

## End-To-End Data Flow

```text
SMT-LIB2 input
    |
    v
ANTLR parser
    |
    v
Smt2Visitor
    |             +----------------+
    | NodeId DAG  | NodeManager    |
    +------------>| hash-consed IR |
                  +----------------+
    |
    +--> optional preprocessing over NodeId formulas
    |
    +--> SAT clauses and EUF equality atoms
            |
            v
      CaDiCaL + EufSolver external propagator
            |
            v
      sat / unsat / unknown
```

The important design choice is that formulas and terms share the same `NodeId`
storage. Boolean connectives are represented as special built-in symbols in
`NodeManager`; user predicates are Bool-sorted application nodes.

## Command-Line Surface

The user-facing options are declared in `src/main.cpp` and map into
`PreprocOptions` or `EufSolver` controls.

Core options:

- `--quiet`: suppress provenance diagnostics.
- `--stats`: print counters and timings to stderr.
- `--version`: print solver, git, build, and SAT backend version.

Preprocessing and encoding options:

- `--preprocess-passes N`
- `--no-nary`
- `--no-flatten`
- `--nnf`
- `--nnf-memo`
- `--eq-bridge`
- `--no-finite-domain-amo`
- `--no-finite-domain-eqdefs`

Theory propagation options:

- `--no-theory-prop`
- `--prop-interval N`
- `--prop-assign-threshold X`
- `--prop-delivery-budget N`

Proof options:

- `--proof FILE`
- `--proof-minimize`

## Stats

`Stats` is defined in `src/core/stats.h`. Counters are collected cheaply during
normal execution and printed only with `--stats`. The stats are grouped into:

- total and preprocessing timings;
- preprocessing formula/bridge/finite-domain counters;
- EUF assignment, conflict, and propagation counters.

The SIGTERM handler prints `unknown` and uses an `atexit` handler so timeout
runs can still produce stats when `--stats` is active.
