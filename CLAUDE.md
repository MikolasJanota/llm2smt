# Claude Code Guidelines for llm2smt

## Running the solver

**ALWAYS run the solver with a timeout.** Solver inputs can trigger exponential search behaviour.
Never invoke the binary without a `timeout` prefix:

```bash
# correct
timeout 5 build-dbg/bin/llm2smt file.smt2

# correct – batch loop
for f in benchmarks/*.smt2; do
    timeout 5 build-dbg/bin/llm2smt "$f" && echo "ok: $f" || echo "fail/timeout: $f"
done

# WRONG – never do this
build-dbg/bin/llm2smt file.smt2
```

A 5-second timeout (`timeout 5`) is the default for interactive testing.
Use a longer timeout (e.g. 60 s) only for deliberate performance benchmarking runs.

## Building

```bash
cmake --build build-dbg   # debug build (assertions enabled)
cmake --build build-rel   # release build
```

Always prefer `build-dbg` for correctness work; `build-rel` only for throughput measurement.

## Running tests

```bash
ctest --test-dir build-dbg --output-on-failure
```

All 51+ unit tests must pass before committing.

## Architecture notes

- The CC module (`src/theories/euf/cc.cpp`) must only store **flat** nodes (constants or single-level applications).
- Structural (app) equations are registered at level 0 (inside `register_equality`, never inside `notify_assignment`) so they are permanent and never undone on backtrack.
- `re_register_all()` was intentionally removed; do not reintroduce it.
