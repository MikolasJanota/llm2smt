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
cmake --build build-dbg   # debug build (assertions + ASAN/UBSan enabled)
cmake --build build-rel   # release build
```

The debug build enables AddressSanitizer and UBSan by default (`LLM2SMT_ASAN=ON`).
Disable with `-DLLM2SMT_ASAN=OFF` if a clean Debug build is needed (e.g. valgrind).

Always prefer `build-dbg` for correctness work; `build-rel` only for throughput measurement.

## Running tests

```bash
ctest --test-dir build-dbg --output-on-failure
```

All 60+ unit tests must pass before committing.

## Testing policy

**For every bug found, add a regression test before closing the investigation.**
- Unit test in `tests/test_cc.cpp` for CC-level bugs (use the `CCFixture` helper).
- SMT2 test in `tests/smt2/tNN_*.smt2` + entry in `tests/CMakeLists.txt` for end-to-end bugs.
- The test must FAIL on the buggy code and PASS after the fix.

## Architecture notes

- The CC module (`src/theories/euf/cc.cpp`) must only store **flat** nodes (constants or single-level applications).
- Structural (app) equations are registered at level 0 (inside `register_equality`, never inside `notify_assignment`) so they are permanent and never undone on backtrack.
- `re_register_all()` was intentionally removed; do not reintroduce it.
