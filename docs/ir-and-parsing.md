# IR And Parsing

The central representation is `NodeId`, a compact integer index into
`NodeManager`. `NodeManager` stores immutable `NodeData` entries and hash-conses
them, so structurally equal terms and formulas share the same identifier.

## Node Storage

`src/core/node.h` defines:

- `NodeId`: node identifier;
- `SymbolId`: declared or built-in symbol identifier;
- `SortId`: sort identifier;
- `NodeData`: symbol plus child vector.

`src/core/node_manager.h` provides builders for:

- user constants and applications: `mk_const`, `mk_app`;
- Boolean constants: `mk_true`, `mk_false`;
- Boolean connectives: `mk_not`, `mk_and`, `mk_or`, `mk_implies`, `mk_xor`,
  `mk_iff`, `mk_ite_bool`;
- EUF equality atoms: `mk_eq`.

`mk_eq(a, b)` canonicalizes argument order, so equality atoms are stable under
commutation. `mk_and` and `mk_or` have binary and n-ary variants. The n-ary
forms use identity simplifications for zero and one child.

## Sorts And Symbols

`SymbolTable` stores names, arities, and return sorts. `BOOL_SORT` is the one
built-in sort; user-declared sorts get other ids. The parser also tracks sort
names in `Smt2Visitor::sym_to_sort_` because SMT-LIB declarations and U-sorted
ITE terms need branch-sort checks.

Boolean expressions are represented in two categories:

- built-in Boolean connective nodes, recognized by `NodeManager::is_and`,
  `is_or`, `is_not`, and similar predicates;
- user-declared Bool-returning applications, recognized by
  `NodeManager::is_atom_node`.

This distinction matters because user predicates are SAT atoms, while built-in
connectives must be encoded structurally.

## Parser Visitor

`Smt2Visitor` in `src/parser/smt2_visitor.cpp` handles SMT-LIB commands:

- declarations and sort declarations;
- `define-fun` macros;
- `assert`;
- `check-sat`;
- `get-model`;
- proof-related finalization through the driver.

There are two important expression paths:

`visit_term`
: Builds a U-sorted or Bool-as-term `NodeId`. This path is used for terms that
  occur inside equality atoms, UF arguments, and U-sorted ITEs.

`build_fml`
: Builds a Bool-sorted formula `NodeId` over the unified IR. This path is used
  when preprocessing is active and formulas are accumulated before encoding.

When preprocessing is inactive, assertions can be encoded directly with
`assert_formula`, `eval_lit`, and `collect_clause_lits`.

## Let And Define-Fun

`let` bindings are cached separately for formula and term use. This avoids
revisiting large parse subtrees when the same binding is expanded repeatedly,
while preserving the difference between:

- formula position, where a Bool expression is encoded into SAT; and
- U-sorted position, where a Bool expression may need a concrete EUF Boolean
  value node.

`define-fun` support is limited to 0-arity macros. The visitor expands these
inline wherever the defined name is referenced.

## Bool Terms In EUF

SMT-LIB permits Bool-sorted expressions to appear as arguments to functions
that accept Bool. The solver bridges these into EUF with explicit Boolean value
nodes:

- `get_bool_term_node(true)`
- `get_bool_term_node(false)`

For a Bool term node and its SAT literal, the visitor adds clauses connecting:

- literal true -> term equals the EUF true node;
- literal false -> term equals the EUF false node.

Pure propositional constants are not eagerly bridged into EUF. They are bridged
only when they occur in U-sorted term position. This avoids polluting the EUF
trail for Boolean-circuit-heavy inputs.

## Formula Encoding

The encoder maps formulas to SAT clauses:

- top-level `and`: recursively assert all children;
- top-level `or`: add one clause over child literals;
- `not`: assert the negated literal, with a special direct encoding for
  `not(and(...))`;
- `implies`, `xor`, `iff`, and Bool `ite`: add small CNF encodings;
- equality atoms: register with `EufSolver` and use the returned SAT literal;
- user predicate atoms: allocate or reuse a SAT literal through `SmtContext`.

`lit_of_fml` creates Tseitin literals for sub-formulas and caches them in
`fml_lit_cache_` for reuse during a flush.
