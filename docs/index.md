# llm2smt Solver Notes

This book documents the current `llm2smt` implementation. It is intended for
developers who need to change the solver, debug regressions, or tune benchmark
performance.

`llm2smt` is a QF_UF SMT solver built around:

- a hash-consed term/formula DAG in `src/core`;
- an SMT-LIB2 parser and encoder in `src/parser`;
- CaDiCaL 3.x as the SAT backend in `src/sat`;
- an external EUF propagator in `src/theories/euf`;
- optional formula preprocessing in `src/preprocessor`;
- optional Lean 4 proof output in `src/proof`;
- benchmark and tuning scripts in `scripts`.

The executable returns one SMT-LIB style result on stdout:

```text
sat
unsat
unknown
```

Unless `--quiet` is passed, it also prints provenance information on stderr:
the `llm2smt` version, git commit, SAT backend, and SAT backend version.

## Build The Book

Install the optional documentation dependency and build from the repository
root:

```sh
python3 -m venv .venv-docs
. .venv-docs/bin/activate
python -m pip install -r docs/requirements.txt
jupyter-book build docs
```

The generated HTML is written under `docs/_build/html`.

## Reading Order

Start with [](architecture.md) for the end-to-end solving pipeline. Then read
[](ir-and-parsing.md), [](sat-euf.md), and [](preprocessing.md) for the main
implementation details. [](proofs-models.md) covers optional proof and model
paths. [](operations.md) captures practical build, test, benchmark, and tuning
workflows.
