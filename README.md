# llm2smt
smt solver written by LLMs

An SMT solver for the QF_UF (Quantifier-Free Uninterpreted Functions) logic,
implementing DPLL(T) with a congruence closure theory solver
(Nieuwenhuis–Oliveras 2007) and CaDiCaL 3.x as the SAT backend via IPASIR-UP.

## Requirements

- CMake ≥ 3.20
- C++20 compiler (GCC ≥ 12 or Clang ≥ 15)
- Java runtime (for ANTLR4 grammar code generation)
- GNU Make
- Python 3 (for ANTLR4 build scripts)
- Internet access on first configure (fetches ANTLR4 runtime and GoogleTest)
- cvc5 on `$PATH` — optional, only needed for `scripts/compare.sh`

## Build

```sh
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(nproc)
```

The binary is placed at `build/bin/llm2smt`.

CaDiCaL is vendored under `third_party/cadical/` and built automatically
via its own `./configure && make` system during the first build.

### Debug build

```sh
cmake -B build-dbg -DCMAKE_BUILD_TYPE=Debug
cmake --build build-dbg -j$(nproc)
```

### compile_commands.json

CMake exports `compile_commands.json` automatically into the build directory.
Symlink it to the repo root for IDE/tooling support:

```sh
ln -sf build/compile_commands.json compile_commands.json
```

## Usage

```sh
# Solve an SMT-LIB2 file
build/bin/llm2smt problem.smt2

# Read from stdin
echo '(set-logic QF_UF)(check-sat)' | build/bin/llm2smt

# Print version
build/bin/llm2smt --version
```

Output is `sat`, `unsat`, or `unknown` on stdout.

## Running tests

```sh
ctest --test-dir build -j$(nproc)
```

## Comparing against cvc5

```sh
# Usage: scripts/compare.sh <dir> [timeout_s] [solver_binary]
bash scripts/compare.sh sandbox/non-incremental/QF_UF/20170829-Rodin 10 build/bin/llm2smt
```

Prints per-file `OK` / `MISMATCH` / `ERROR` and a summary line.
Exits 1 if any MISMATCH is found.
