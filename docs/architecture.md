# Architecture

`llm2smt` implements DPLL(T)-style paths for quantifier-free uninterpreted
functions and pure linear real arithmetic. The SAT layer owns Boolean search and
calls theory plugins via IPASIR-UP style callbacks. The EUF layer maintains
congruence closure, discovers conflicts, optionally propagates implied
equalities, and explains theory lemmas back to the SAT solver. The LRA layer
uses exact rational arithmetic and final-model feasibility checks over active
linear atoms.

## Main Components

| Area | Files | Responsibility |
| --- | --- | --- |
| Driver | `src/main.cpp` | Command-line options, parser setup, solver objects, proof emission, stats. |
| Core IR | `src/core/node*.{h,cpp}`, `src/core/symbol_table.h` | Hash-consed `NodeId` DAG and declared symbols/sorts. |
| Parser/encoder | `src/parser/smt2_visitor*.{h,cpp}` | SMT-LIB commands, formula construction, preprocessing flush, SAT clauses, model printing. |
| Preprocessor | `src/preprocessor/*` | NNF, simplification, equality bridging, finite-domain encodings. |
| SAT backend | `src/sat/cadical_solver*.{h,cpp}`, `src/sat/ipasir_up.h` | CaDiCaL wrapper and external propagator interface. |
| EUF theory | `src/theories/euf/*` | Term flattening, congruence closure, conflicts, propagation, explanations. |
| LRA theory | `src/theories/lra/*` | Exact rationals, linear atoms, feasibility checks, LRA conflict clauses. |
| Proofs | `src/proof/*` | Lean proof generation and optional theory-lemma minimization. |
| Tests | `tests/*` | Unit tests and SMT2 end-to-end regression tests. |

## Solver Lifecycle

The executable starts in `src/main.cpp`.

1. Parse command-line flags into `PreprocOptions` and solver controls.
2. Construct `Stats`, `NodeManager`, `EufSolver`, `LraSolver`, and `CaDiCaLSolver`.
3. Connect a combined external propagator that dispatches to EUF and LRA.
4. Parse SMT-LIB2 with ANTLR and visit commands through `Smt2Visitor`.
5. Declarations populate the symbol table.
6. Assertions are either encoded directly or accumulated as `NodeId` formulas
   and flushed through preprocessing.
7. `check-sat` invokes CaDiCaL.
8. CaDiCaL drives theory callbacks during search.
9. The visitor prints `sat`, `unsat`, or `unknown`.
10. Optional model/proof/stat output is emitted after solving.

## Memory Lifetime

The solver is designed around one SMT-LIB run per process. Most long-lived
storage is append-oriented and is reclaimed when the process exits, not during
search:

- `NodeManager` hash-conses `NodeId` terms in vectors and lookup tables; nodes
  are never individually deleted.
- `Smt2Visitor` caches parse-time encodings, Boolean literals, finite-domain
  information, model-printing records, and LRA-local atom definitions until the
  visitor is destroyed.
- `CaDiCaLSolver` owns the underlying CaDiCaL instance through RAII; clauses and
  variables stay in CaDiCaL for the lifetime of that solver object.
- `EufSolver` and `LraSolver` keep registered atoms, flattening/tableau data,
  explanation caches, and propagation queues for the lifetime of the solver
  object.

Backtracking restores logical state rather than compacting memory. EUF pops
congruence-closure merges and active disequalities back to the requested
decision level. LRA restores bound-stack entries while keeping the tableau,
basis, and current assignment from the last successful check. SAT backtracking
undoes assignments inside CaDiCaL, but learned/input clauses and variable
storage remain owned by the SAT solver.

Short-lived temporary vectors and maps inside preprocessing passes or callbacks
are freed normally when they go out of scope. The important operational
consequence is that peak memory tracks the largest encoded formula/search state
seen in the current process; there is no arena compaction or per-assertion
garbage collection.

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
    +--> SAT clauses and EUF equality atoms or LRA atoms
            |
            v
      CaDiCaL + combined theory external propagator
            |
            v
      sat / unsat / unknown
```

For `QF_UF`, formulas and terms share the same `NodeId` storage. Boolean
connectives are represented as special built-in symbols in `NodeManager`; user
predicates are Bool-sorted application nodes. For `QF_LRA`, the parser bypasses
the EUF preprocessor and directly encodes Boolean structure plus linear
arithmetic atoms.

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
- `--no-lra-bool-cache`
- `--no-lra-bool-cache-and`
- `--no-lra-bool-cache-or`
- `--no-lra-bool-cache-eq`

Theory propagation options:

- `--no-theory-prop`
- `--no-lra-incremental-prop-scan`
- `--prop-interval N`
- `--prop-assign-threshold X`
- `--prop-delivery-budget N`

LRA options:

- `--lra-print-conflict-size`

Proof options:

- `--proof FILE`
- `--proof-minimize`

Proof output is `QF_UF` only. `QF_LRA` with `--proof` is rejected.

## Stats

`Stats` is defined in `src/core/stats.h`. Counters are collected cheaply during
normal execution and printed only with `--stats`. The stats are grouped into:

- total and preprocessing timings;
- preprocessing formula/bridge/finite-domain counters;
- QF_LRA local encoding cache counters;
- SAT encoding size counters;
- EUF assignment, conflict, and propagation counters.
- LRA assignment, check, conflict, propagation, and tableau-size counters.

The SIGTERM handler prints `unknown` and uses an `atexit` handler so timeout
runs can still produce stats when `--stats` is active.
