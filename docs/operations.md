# Operations

This chapter collects practical commands for building, testing, debugging, and
tuning the solver.

## Build

Release build:

```sh
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build -j$(nproc)
```

Debug build:

```sh
cmake -B build-dbg -DCMAKE_BUILD_TYPE=Debug
cmake --build build-dbg -j$(nproc)
```

Debug builds enable AddressSanitizer and UBSan by default. Disable them with:

```sh
cmake -B build-dbg-noasan -DCMAKE_BUILD_TYPE=Debug -DLLM2SMT_ASAN=OFF
```

## Run

Always use an external timeout when running unknown benchmark files:

```sh
timeout 30s build/bin/llm2smt --stats --quiet input.smt2
```

`SIGTERM` is handled by printing `unknown`; with `--stats`, the atexit handler
prints whatever counters are available.

## Tests

Run the CTest suite:

```sh
ctest --test-dir build --output-on-failure -j$(nproc)
```

Test categories:

- C++ unit tests for `NodeManager`, `CC`, `EufSolver`, and preprocessing;
- end-to-end SMT2 regression tests in `tests/smt2`;
- focused `QF_LRA` SMT2 regressions named `lra*`;
- proof-generation tests that grep generated Lean output for expected lemmas.

Run just the LRA regressions:

```sh
ctest --test-dir build -R 'smt2/lra' --output-on-failure
```

Build the Jupyter Book documentation:

```sh
bash scripts/build_docs.sh
```

## QF_LRA Smoke Benchmarks

Use short external timeouts for the current LRA implementation:

```sh
for f in \
  sandbox/non-incremental/QF_LRA/keymaera/division_dijkstra-node701.smt2 \
  sandbox/non-incremental/QF_LRA/keymaera/square_root_zuse-node902.smt2 \
  sandbox/non-incremental/QF_LRA/check/bignum_lra1.smt2 \
  sandbox/non-incremental/QF_LRA/check/bignum_lra2.smt2 \
  sandbox/non-incremental/QF_LRA/meti-tarski/Chua/1/VC2/U/Chua-1-VC2-U-chunk-0108.smt2
do
  timeout 10s build/bin/llm2smt --quiet "$f"
done
```

The TTA and spider smoke benchmarks are useful performance targets for the
native incremental tableau solver. Short cutoffs should be treated as
performance measurements, not as completeness checks. Conflict-size printing
remains a useful smoke diagnostic:

```sh
timeout 60s build/bin/llm2smt --quiet \
  --lra-print-conflict-size \
  sandbox/non-incremental/QF_LRA/tta_startup/simple_startup_3nodes.abstract.base.smt2
```

For comparison against another solver, run that solver directly on the same
SMT-LIB file and use the same timeout policy.

## Compare Against cvc5

```sh
bash scripts/compare.sh sandbox/non-incremental/QF_UF/20170829-Rodin 10 build/bin/llm2smt
```

The script runs every `.smt2` file in a directory, compares stdout with cvc5,
and exits nonzero on mismatch.

## Minimize Failing Inputs

Use `scripts/minimize_smt2.py` for crashes and wrong answers. It repeatedly
removes assertions while preserving the failure condition.

Example:

```sh
python3 scripts/minimize_smt2.py \
  --cmd 'build-dbg/bin/llm2smt --preprocess-passes 1' \
  --input failing.smt2 \
  --output minimal.smt2 \
  --match SEGV \
  -v
```

## YinYang Fuzzing

YinYang is the preferred replacement for the handwritten random SMT-LIB
generator when mutating existing benchmark seeds. Install it separately:

```sh
python3 -m pip install yinyang
```

Run a bounded seed-mutation campaign against `llm2smt` and a reference solver:

```sh
scripts/yinyang_fuzz.sh \
  --seeds sandbox/non-incremental/QF_LRA/check \
  --solver 'build-workspace-rel/bin/llm2smt --quiet' \
  --ref 'z3 model_validate=true' \
  --seconds 600 \
  --iterations 100
```

Useful knobs:

- `--seeds`: a single `.smt2` file or a directory of seeds;
- `--solver`: the `llm2smt` command and flags to test;
- `--ref`: reference solver command, usually Z3 or cvc5;
- `--solver-timeout`: per-solver timeout passed to YinYang;
- `--bugs`: where YinYang stores discrepancy/crash artifacts;
- `--scratch`: where temporary mutants are written;
- `--keep-mutants`: preserve generated mutants for later inspection.

For `QF_UF`, use `tests/smt2` or a `sandbox/non-incremental/QF_UF/*`
directory as seeds. For `QF_LRA`, start with smaller directories such as
`sandbox/non-incremental/QF_LRA/check` before moving to industrial benchmark
families.

The SLURM head node is on the private CIIRC network. Reach it through the data
jump host; direct SSH to `10.35.125.63` from outside that network times out.
Use this SSH config entry or the equivalent `ssh -J` command:

```text
Host llm2smt-slurm
  HostName 10.35.125.63
  User janotmik
  ProxyJump janotmik@data.ciirc.cvut.cz
```

If a non-interactive environment cannot write `~/.ssh/known_hosts`, create a
temporary known-hosts file for both the jump host and the target:

```sh
KNOWN=/tmp/llm2smt_slurm_known_hosts
rm -f "$KNOWN"
ssh-keyscan -H data.ciirc.cvut.cz >> "$KNOWN"
ssh -o UserKnownHostsFile="$KNOWN" \
  -o StrictHostKeyChecking=yes \
  janotmik@data.ciirc.cvut.cz \
  'ssh-keyscan -H 10.35.125.63' >> "$KNOWN"

cat > /tmp/llm2smt_slurm_ssh_config <<EOF
Host llm2smt-slurm
  HostName 10.35.125.63
  User janotmik
  ProxyJump janotmik@data.ciirc.cvut.cz
  UserKnownHostsFile $KNOWN
  StrictHostKeyChecking yes
  BatchMode yes
Host data.ciirc.cvut.cz
  UserKnownHostsFile $KNOWN
  StrictHostKeyChecking yes
  BatchMode yes
EOF
```

Check reachability before syncing or submitting:

```sh
ssh -F /tmp/llm2smt_slurm_ssh_config llm2smt-slurm \
  'hostname && command -v sbatch && command -v squeue'
```

The practical SLURM workflow is then:

```sh
rsync -az --delete -e 'ssh -F /tmp/llm2smt_slurm_ssh_config' \
  --exclude .git --exclude build --exclude 'build-*' \
  --exclude .venv-docs --exclude docs/_build \
  --exclude .venv-build --exclude .venv-yinyang \
  --exclude vendor --exclude logs --exclude yinyang_bugs \
  --exclude yinyang_scratch --exclude slurm_logs \
  --exclude eval_results --exclude profile_results \
  --exclude node_modules --exclude sandbox \
  ./ llm2smt-slurm:~/llm2smt-fuzz/

ssh -F /tmp/llm2smt_slurm_ssh_config llm2smt-slurm \
  'cd ~/llm2smt-fuzz && sbatch yinyang_lra_selected.sbatch'
ssh -F /tmp/llm2smt_slurm_ssh_config llm2smt-slurm 'squeue -u janotmik'
ssh -F /tmp/llm2smt_slurm_ssh_config llm2smt-slurm \
  'tail -n 80 ~/llm2smt-fuzz/logs/llm2smt-yinyang-*.out'
```

Use bounded jobs, collect `logs/`, `bench_results/`, and `yinyang_bugs*`, and
never delete bug artifacts before copying them locally.

## Unsat Cores From External Solvers

`scripts/smt2_unsat_core.py` can split a single large assertion into guarded
subassertions and ask Z3 for a core. This is useful for families where the
original SMT-LIB file contains one giant top-level conjunction.

## SMAC Tuning

Create an instance list:

```sh
python3 scripts/make_smac_instances.py \
  sandbox/non-incremental/QF_UF/NEQ sandbox/non-incremental/QF_UF/PEQ \
  -o smac-instances/qf_uf_neq_peq.txt
```

The instance-list helper recursively walks input directories and follows
symlinked directories. It deduplicates files by resolved path.

Install SMAC dependencies:

```sh
python3 -m venv .venv-smac
. .venv-smac/bin/activate
python -m pip install -r scripts/requirements-smac.txt
```

Run a bounded tuning job:

```sh
python3 scripts/smac_llm2smt.py tune \
  --solver build/bin/llm2smt \
  --instances smac-instances/qf_uf_neq_peq.txt \
  --cutoff 120 \
  --trials 500 \
  --workers 8 \
  --walltime-limit 7200 \
  --output-dir smac-runs/qf_uf_neq_peq
```

Semantics:

- `--cutoff`: timeout for one solver subprocess;
- `--trials`: total SMAC target-evaluation budget;
- `--workers`: concurrent target evaluations, not threads inside `llm2smt`;
- `--walltime-limit`: total optimizer wall-clock budget, with `0` meaning
  intentionally unbounded.

Partial results:

- `llm2smt-runs.jsonl` is appended after every completed solver call;
- `best-observed.json` is refreshed during the run;
- `incumbent.json` is written when SMAC exits normally or after a handled
  interrupt.

Recover from an interrupted run:

```sh
python3 scripts/smac_llm2smt.py summarize \
  smac-runs/qf_uf_neq_peq/llm2smt-runs.jsonl \
  -o smac-runs/qf_uf_neq_peq/recovered.json
```

## Performance Investigation Notes

Use [](performance-loop.md) for the standard candidate loop: hypothesis,
verification, default/candidate quick and hard evals, report generation, and
decision rules. The notes below are the lightweight checklist for individual
changes.

The persistent investigation notes live in `CLAUDE.md`. They include measured
behavior for NEQ, PEQ, firewire-tree, finite-domain preprocessing, equality
bridging, and theory propagation schedules.

When adding a new optimization:

1. record the exact benchmark, flags, timeout, and build type;
2. add a focused regression test when the change fixes a bug;
3. keep ablation flags for risky heuristics where practical;
4. keep promising but workload-sensitive optimizations behind an option until
   aggregate evaluation justifies making them default;
5. compare both default behavior and the intended tuned flag set.
