# Claude Code Guidelines for llm2smt

## Running the solver

Running the solver directly on a file is fine for debugging:

```bash
timeout 5 build-dbg/bin/llm2smt file.smt2
```

**ALWAYS use a `timeout` prefix.** Solver inputs can trigger exponential search behaviour.

A 5-second timeout is the default. Use a longer timeout (e.g. 60 s) only for deliberate
performance benchmarking.

## Building

```bash
cmake --build build-dbg        # debug + ASAN/UBSan (default for correctness work)
cmake --build build-dbg-noasan # debug without ASAN (e.g. for valgrind or perf)
cmake --build build-rel        # release build (throughput measurement only)
```

Configure once:
```bash
cmake -B build-dbg-noasan -DCMAKE_BUILD_TYPE=Debug -DLLM2SMT_ASAN=OFF
```

The debug build enables AddressSanitizer and UBSan by default (`LLM2SMT_ASAN=ON`).

Always prefer `build-dbg` for correctness work; `build-rel` only for throughput measurement.

## Running tests

```bash
ctest --test-dir build-dbg --output-on-failure
```

All 60+ unit tests must pass before committing.

## Minimizing failing inputs

**Always use `scripts/minimize_smt2.py` as the first step when investigating a crash or wrong answer.**
Do not manually bisect assertions — the minimizer does it automatically.

```bash
# Crash (match on SEGV or any non-zero exit):
python scripts/minimize_smt2.py \
    --cmd 'build-dbg/bin/llm2smt --preprocess-passes 1' \
    --input failing.smt2 --output minimal.smt2 --match SEGV -v

# Wrong answer (match on unexpected output):
python scripts/minimize_smt2.py \
    --cmd 'build-dbg/bin/llm2smt' \
    --input failing.smt2 --output minimal.smt2 --match 'wrong_string' -v

# Lean proof wrong (solver says unsat but proof checker rejects it):
python scripts/minimize_smt2.py \
    --cmd 'scripts/oracle_proof_fail.sh --preprocess-passes 1' \
    --input failing.smt2 --output minimal.smt2 -v
```

Use `/minimize` to invoke this as a skill.

## Testing policy

**For every bug found, add a regression test before closing the investigation.**
- Unit test in `tests/test_cc.cpp` for CC-level bugs (use the `CCFixture` helper).
- SMT2 test in `tests/smt2/tNN_*.smt2` + entry in `tests/CMakeLists.txt` for end-to-end bugs.
- The test must FAIL on the buggy code and PASS after the fix.

**After each bug fix (with passing tests), commit immediately.**
Do not batch multiple bug fixes into one commit.

## Versioning

The version is defined in **one place**: `CMakeLists.txt` line 2 (`project(llm2smt VERSION X.Y.Z ...)`).
Every release commit must have a matching annotated git tag `vX.Y.Z`.

**Bump + tag workflow:**
```bash
# 1. Edit CMakeLists.txt: increment patch (or minor/major as appropriate)
# 2. Commit the version bump
git commit -m "Bump to vX.Y.Z"
# 3. Create an annotated tag on that commit
git tag -a vX.Y.Z -m "vX.Y.Z"
```

Rules:
- The tag name must exactly match the `VERSION` field: `v` + the three-part number.
- Never create the tag before the bump commit; always tag the bump commit itself.
- Patch bumps (`Z`) for bug fixes; minor bumps (`Y`) for new features; major (`X`) for breaking changes.

## Lean proof checking

Always use `~/git/llm2smt/sandbox/check_proof.sh` to verify generated Lean proofs:

```bash
timeout 120 ~/git/llm2smt/sandbox/check_proof.sh /tmp/proof.lean
```

No output = success. Any output = Lean error.

## Lean proof generation

The proof has two layers:

1. **EUF theory lemmas** (`cl_k`, `ite_pos_k`, `ite_neg_k`, `ite_bridge_k`,
   `trans_k`, `cong_k`, `eq_bridge_k`) — emitted as **standalone `theorem`
   declarations** proved by `grind`.  Each lemma is a small EUF tautology
   (2–5 atoms); `grind` handles congruence closure over Prop equalities.

2. **`theorem contradiction`** — loads all standalone theorems and hypothesis
   axioms via `have`, then closes with `bv_decide`.  This is a propositional
   SAT problem; `bv_decide` calls CaDiCaL and scales to hundreds of clauses.

Equalities are emitted as Prop-level (`a = b`), not Bool-wrapped.
The Lean import is `import Mathlib.Tactic`.
`open Classical` (or per-sort `noncomputable instance : DecidableEq S := Classical.decEq S`)
must appear in the preamble so that `bv_decide` can treat opaque equalities as
atomic Boolean variables.

```lean
-- Theory lemmas: standalone, proved by grind (small EUF tautologies).
theorem cl_0 : a = c ∨ ¬(a = b) ∨ ¬(b = c) := by grind
-- Lemmas that need a problem hypothesis load only the specific hyp needed:
theorem cl_4 : c3 = c0 ∨ ¬(c1 = c0) := by
  have hyp3 := hyp3
  grind

-- Contradiction: load everything, then bv_decide for propositional closure.
theorem contradiction : False := by
  have hyp1 := hyp1
  ...
  have cl_0 := cl_0
  have cl_1 := cl_1
  ...
  bv_decide
```

**Rules:**
- `grind` for theory lemmas; `bv_decide` for `theorem contradiction`. Never swap these.
  `grind` does NOT scale to large propositional problems.
- The past SIGSEGV from `bv_decide` was a `TMPDIR` sandbox issue (now fixed in
  `scripts/check_lean.sh`), NOT a `bv_decide` incompatibility with UF atoms.
- All EUF equalities are emitted as Prop (`a = b`), not Bool-wrapped.
- Theory lemmas are standalone, NOT inline `have`s inside contradiction.
- For theory lemmas, load only the specific hypothesis needed — not all hyps.
- `grind` cannot see global `axiom` declarations without an explicit `have h := h`.

## C++ style notes

- Prefer `.contains(x)` over `.count(x) > 0` or `.count(x)` in boolean context (C++20, works on `std::unordered_set`, `std::unordered_map`, `std::set`, `std::map`).

## Architecture notes

- The CC module (`src/theories/euf/cc.cpp`) must only store **flat** nodes (constants or single-level applications).
- Structural (app) equations are registered at level 0 (inside `register_equality`, never inside `notify_assignment`) so they are permanent and never undone on backtrack.
- `re_register_all()` was intentionally removed; do not reintroduce it.

## Performance investigation notes

These are observed hotspots / likely inefficiencies to revisit with benchmark data:

- `EufSolver::record_cong_steps()` in `src/theories/euf/euf_solver.cpp`
  recursively calls `cc_.explain()` for each congruence premise pair. In proof
  mode this can duplicate work across repeated premise pairs. Consider memoizing
  premise explanations for the duration of one proof-recording batch.
- `let` / 0-arity `define-fun` expansion is lazy and re-visits the stored parse
  subtree at each use. Hash-consing avoids duplicate `NodeId`s, and the existing
  Tseitin caches help for some formula contexts, but repeated uses still redo
  parse traversal, sort checks, and clause-generation checks. If large macros
  appear in benchmarks, cache expanded `NodeId` / literal results per binding
  where side effects are safe and already idempotent.
- `bridge_disjunctions()` in `src/preprocessor/disjunction_bridge.cpp` has an
  intentional O(branches × shared-nodes²) pair check. This is useful for diamond
  instances but can become expensive on wide disjunctions with many shared
  equality terms. A future implementation could iterate equivalence classes from
  one branch and test only pairs within those classes, rather than all shared
  node pairs.
- NEQ finite-model benchmarks such as
  `sandbox/non-incremental/QF_UF/NEQ/NEQ027_size11.smt2` remain hard after the
  finite-domain AMO preprocessing. Size11 has about 20k top-level clauses and
  gets 17,886 AMO clauses; a 30s release run still times out. Selectively
  observing only EUF equality variables in CaDiCaL reduces useless external
  propagation callbacks and is a small general win. Eager U-function Ackermann
  clauses reduced some EUF work but regressed size9 and did not solve size11;
  Bool-function Ackermann clauses produced too many clauses. `--eq-bridge`
  helps size11 but does not close it. The remaining opportunity is likely a
  finite-domain-aware encoding/search strategy rather than more pairwise AMO.
- `NEQ027_size10.smt2` solves with the finite-domain AMO preprocessing but is
  still slow without stronger finite-domain encoding (~42-46s release on this
  workspace): about 12,430 AMO clauses, 52k EUF conflicts, and 23M
  equality/disequality assignment notifications. Disabling AMO times out at 60s
  with many more conflicts. More aggressive theory-propagation schedules
  (`--prop-interval 4/8`, threshold 1, unlimited delivery budget) were worse.
- The finite-domain equality-definition pass in `Smt2Visitor` recognizes
  explicit domain closure clauses `(or (= t c0) ... (= t cn))` whose values are
  known distinct, records the existing choice literals, and for equality atoms
  between two such finite-domain terms adds SAT clauses tying equality to
  matching value choices. It is enabled by default and can be disabled with
  `--no-finite-domain-eqdefs`; it also requires finite-domain AMO to be enabled.
  A conservative domain-size threshold of 10 avoids regressions on small cases
  (`NEQ004_size7`, `NEQ027_size9`) while targeting the hard NEQ027 cases.
  Measured release results after the pass: `NEQ027_size10` ~26s with 900
  equality-definition clauses versus ~46s with `--no-finite-domain-eqdefs`;
  `NEQ027_size11` solves in ~93s with 1,089 definition clauses, while the
  ablation timed out at 120s.
- Since the NEQ instances are UNSAT, an external unsat core can guide the next
  preprocessing pass. The files currently contain one giant assertion, so a core
  over the original file is useless. Split the top-level conjunction under the
  nested `let`s into separately named assertions, run a fast solver with
  `:produce-unsat-cores true`, and inspect whether the core is dominated by
  domain-membership clauses, predicate clauses, or UF congruence clauses. A
  small core would point to input reduction/minimization; a large core with many
  repeated domain choices would point to a finite-domain-aware encoding/search
  strategy rather than more generic EUF propagation tuning.
- `scripts/smt2_unsat_core.py` implements that split using assumption guards
  rather than duplicating all nested `let` bindings. With Z3 4.16 from the local
  `.venv-z3`, `NEQ027_size10` has a core of 3,520 / 15,369 top-level conjuncts;
  `NEQ027_size11` has a core of 4,408 / 19,985. The core is not small. It keeps
  ~74-75% of the domain membership clauses (`or/N[eq:N]`) and ~75-91% of the
  ternary Horn-like clauses involving one predicate plus equality/disequality
  literals. This supports focusing on a finite-domain/Horn-style encoding or
  search strategy, not just trimming irrelevant assertions.
- Smaller same-family instances are useful testbeds. `NEQ004_size7` has a Z3
  core of 586 / 1,145 top-level conjuncts. The core keeps all 57 domain
  membership clauses (`or/7[eq:7]`) and all clauses in several predicate/equality
  families. Our solver still takes about the same time on the core-only file
  (~2.9s release, 74k EUF conflicts), so the core preserves the pathological
  search behavior while being much smaller than the original benchmark.
- The `2018-Goel-hwbench` firewire-tree SAT instances are Boolean-circuit-heavy
  QF_UF files: almost every assertion is a definition over 0-ary Bool symbols
  (`= p (not q)`, `= p (and q r)`) plus a smaller number of UF term definitions.
  Do not bridge 0-ary Bool symbols into EUF merely because they appear in formula
  position. They only need `p = __bool_true` / `p = __bool_false` bridge clauses
  when `visit_term` sees them in a U-sorted position, such as an argument to a UF.
  Bridging every propositional constant polluted the observed EUF trail and made
  `QF_UF_firewire_tree.5.prop3_ab_reg_max.smt2` take ~208s release. Keeping pure
  propositional constants in SAT reduced that case to ~43s; smaller siblings
  also improved (`size4` ~11.4s to ~3.6s, `size1` ~6.9s to ~1.4s).
