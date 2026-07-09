# SAT And EUF Integration

The SAT solver is CaDiCaL 3.x, wrapped by `CaDiCaLSolver`. The EUF solver is
registered as an external propagator. This lets the SAT search remain
propositional while the theory solver observes equality assignments and adds
conflicts or propagations.

## SAT Wrapper

`src/sat/ipasir_up.h` defines a small abstraction:

- `SatSolver`: allocate variables, add clauses, solve, query model values;
- `ExternalPropagator`: assignment, backtrack, propagation, and external-clause
  callbacks.

`src/sat/cadical_solver.cpp` adapts this interface to CaDiCaL's C++ API.
CaDiCaL batches assignment notifications; the adapter fans them out one literal
at a time to the EUF solver.

Before solving, `CaDiCaLSolver::solve()` registers observed variables. The EUF
solver may return a non-empty `observed_vars()` list, which avoids observing
irrelevant SAT variables. If the list is empty, the wrapper observes all
variables for compatibility.

## Equality Atoms

`EufSolver::register_equality(lhs, rhs)` returns a positive SAT literal for the
atom `lhs = rhs`. Positive assignment means equality; negative assignment means
disequality.

Registration performs key setup:

1. flatten both original terms into CC constants;
2. register generated application equations permanently in CC;
3. remember the original and flat endpoints;
4. map both original and flat unordered pairs to the SAT literal;
5. add the literal to observed variables.

`register_permanent_equality(lhs, rhs)` is used for equalities forced by
preprocessing. These are merged directly into the congruence closure at level 0
and do not create SAT variables.

## Term Flattening

The congruence closure module stores only flat constants and binary application
equations. `Flattener` converts arbitrary `NodeId` terms into this form.

For an n-ary application:

```text
g(t1, t2, ..., tn)
```

the flattener curries through the internal apply symbol `@`:

```text
@(@(@(g, t1), t2), ..., tn)
```

Each intermediate application gets a fresh flat constant and a CC application
equation:

```text
result = fn(arg)
```

The flattener caches original-to-flat mappings and records reverse mappings for
full original applications. Reverse mappings are needed for model printing and
Lean proof rendering.

## Congruence Closure

`CC` in `src/theories/euf/cc.*` follows the Nieuwenhuis-Oliveras style:

- `repr_`: representative of each node;
- `class_list_`: nodes in each equivalence class;
- `use_list_`: flat application equations that mention a class;
- `lookup_`: congruence lookup from `(fn_rep, arg_rep)` to application eq;
- `pending_`: merge queue.

It also maintains:

- a proof forest for explanations;
- a trail for backtracking;
- a changed-node list for theory propagation candidate discovery.

`add_equation` merges two constants. `add_app_equation` registers a flat
application. Congruence is discovered when two application equations have
equivalent function and argument representatives.

## Search Callbacks

The EUF propagator reacts to SAT search as follows:

`notify_assignment`
: Positive equality literals are merged into CC. Negative equality literals are
  stored as active disequalities. All assignments update level-local counters
  used for backtracking and propagation throttling.

`notify_new_decision_level`
: Opens a new CC level and records current sizes of per-level vectors.

`notify_backtrack`
: Pops CC state and EUF-side vectors back to the requested level.

`cb_check_found_model`
: Checks active disequalities against the final CC state. If a disequality is
  violated, a theory conflict clause is prepared.

`cb_has_external_clause` and `cb_add_external_clause_lit`
: Serve prepared conflict clauses back to CaDiCaL.

`cb_propagate` and `cb_add_reason_clause_lit`
: Optionally deliver theory-implied equality literals and their reason clauses.

## Conflicts And Explanations

When an active disequality `a != b` is violated because `a` and `b` are
congruent in CC, the EUF solver asks `CC::explain(a, b)` for the equations that
justify the congruence. Those equations are converted back to SAT literals.

The external conflict clause has the shape:

```text
not premise_1 or not premise_2 or ... or disequality_lit
```

where `disequality_lit` is the negative literal that caused the contradiction.

`CC::explain()` also reports raw congruence steps when proof recording is
enabled, so the Lean emitter can produce standalone congruence lemmas.

## Theory Propagation

Theory propagation is enabled by default but throttled. It can be disabled with
`--no-theory-prop`.

Controls:

- `--prop-interval N`: process candidates every N discovery calls, then
  adaptively double the interval up to 1024.
- `--prop-assign-threshold X`: skip candidate processing when the assigned
  variable fraction reaches the threshold. `0` disables this guard.
- `--prop-delivery-budget N`: stop discovery after N delivered propagated
  literals. `0` means unlimited.

Candidate discovery is based on flat nodes whose CC class changed. The solver
uses an occurrence index from flat endpoint node to equality literals, so it
does not scan every equality atom after every merge.

The main EUF propagation shape is a triangle equality:

```text
a = b, b = c  ==>  a = c
```

More generally, when CC has already made the two endpoints of a registered
equality atom congruent, `cb_propagate` can return that equality literal. The
reason clause is the implied literal plus the negation of the equality literals
returned by `CC::explain(lhs, rhs)`, for example:

```text
(or (= a c) (not (= a b)) (not (= b c)))
```

This is deliberately implemented as theory propagation, not as an eager
preprocessing pass that materializes all transitivity triangles. The occurrence
index keeps discovery local to recently changed flat endpoints; without it,
checking all registered equality atoms after every merge regresses on formulas
with many unrelated equalities.
