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

## Architecture notes

- The CC module (`src/theories/euf/cc.cpp`) must only store **flat** nodes (constants or single-level applications).
- Structural (app) equations are registered at level 0 (inside `register_equality`, never inside `notify_assignment`) so they are permanent and never undone on backtrack.
- `re_register_all()` was intentionally removed; do not reintroduce it.
