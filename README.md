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

## Developer documentation

The solver internals are documented as a Jupyter Book under `docs/`.

```sh
python3 -m venv .venv-docs
. .venv-docs/bin/activate
python -m pip install -r docs/requirements.txt
jupyter-book build docs
```

## Comparing against cvc5

```sh
# Usage: scripts/compare.sh <dir> [timeout_s] [solver_binary]
bash scripts/compare.sh sandbox/non-incremental/QF_UF/20170829-Rodin 10 build/bin/llm2smt
```

Prints per-file `OK` / `MISMATCH` / `ERROR` and a summary line.
Exits 1 if any MISMATCH is found.

## Tuning options with SMAC3

The optional SMAC harness tunes solver command-line options over a list of SMT2
instances.  It penalizes `unknown`, timeouts, crashes, and wrong answers.

```sh
python3 -m venv .venv-smac
. .venv-smac/bin/activate
python -m pip install -r scripts/requirements-smac.txt

cmake -B build-rel -DCMAKE_BUILD_TYPE=Release
cmake --build build-rel -j$(nproc)

python scripts/make_smac_instances.py \
  sandbox/non-incremental/QF_UF/NEQ sandbox/non-incremental/QF_UF/PEQ \
  -o smac-instances/qf_uf_neq_peq.txt

python scripts/smac_llm2smt.py tune \
  --solver build-rel/bin/llm2smt \
  --instances smac-instances/qf_uf_neq_peq.txt \
  --cutoff 120 --trials 500 --workers 8 --walltime-limit 3600 \
  --output-dir smac-runs/qf_uf_neq_peq
```

`--cutoff` is the per-solver-call timeout.  `--walltime-limit` is the overall
SMAC run budget in seconds; pass `0` only for an intentionally unbounded run.
Each solver call is logged immediately to `llm2smt-runs.jsonl`, and
`best-observed.json` is refreshed from completed calls during the run.  The
final SMAC incumbent and replayable command-line arguments are written to
`incumbent.json`.

If a run is interrupted before `incumbent.json` is written, recover a summary
from the JSONL log:

```sh
python3 scripts/smac_llm2smt.py summarize \
  smac-runs/qf_uf_neq_peq/llm2smt-runs.jsonl \
  -o smac-runs/qf_uf_neq_peq/recovered.json
```
