# Performance Loop

This page defines the repeatable loop for solver performance work. The goal is
to avoid stacking partial results and to make room for genuinely new ideas, not
only local tuning.

## Candidate Loop

Every performance candidate should move through the same stages:

1. Record a hypothesis before editing.
   State the expected mechanism and the counters that should move, for example
   fewer SAT clauses, fewer LRA rows, fewer pivots, fewer propagation
   candidates, or lower PAR2 on a named suite.
2. Implement narrowly.
   If the idea is workload-sensitive or uncertain, put it behind an option.
3. Verify correctness first.
   Run focused tests and documentation checks before interpreting performance.
4. Evaluate default and candidate on the same suites.
   Compare solved count, timeouts, errors, `tta_startup` solved count, and PAR2.
5. Decide explicitly.
   Accept as default, keep behind an option, reject/revert, or send to full
   evaluation.
6. Select the next target from reference deltas.
   When Z3/OpenSMT TSVs are available, rank files where a reference is fast and
   native remains slow. Use that ranked list to choose the next diagnosis target.

Use the local loop helper:

```sh
python3 scripts/qf_lra_perf_loop.py \
  --candidate no-ite-eq-direct \
  --opts='--no-lra-ite-eq-direct' \
  --hypothesis 'Ablate direct Real ITE equality encoding; expect more LRA auxiliaries.'
```

By default this runs:

- `cmake --build build-workspace-rel -j4`;
- focused LRA `ctest`;
- `bash scripts/build_docs.sh`;
- `scripts/qf_lra_eval.py --suite quick` for default and candidate;
- `scripts/qf_lra_eval.py --suite hard` for default and candidate.

Reports are written under `eval_results/loop_reports/`. The report contains the
commands, artifacts, PAR2 deltas, and a decision hint. If reference TSVs are
provided, the report also includes a ranked next-target table with rough
formula-shape counters. The hint is advisory; the maintainer decision is still
based on correctness, aggregate behavior, and code quality.

Useful variants:

```sh
# Run only quick feedback while developing.
python3 scripts/qf_lra_perf_loop.py \
  --candidate my-idea \
  --opts='--my-flag' \
  --suite quick \
  --skip-verify

# Include the full 137-file local suite when a candidate survives quick/hard.
python3 scripts/qf_lra_perf_loop.py \
  --candidate my-idea \
  --opts='--my-flag' \
  --suite quick \
  --suite hard \
  --suite full

# Add reference TSVs so the report says what to inspect next.
python3 scripts/qf_lra_perf_loop.py \
  --candidate my-idea \
  --opts='--my-flag' \
  --suite full \
  --ref-tsv Z3=eval_results/full-z3-60s-20260703.tsv \
  --ref-tsv OpenSMT=eval_results/full-opensmt292-60s-20260703.tsv

# Print commands without running them.
python3 scripts/qf_lra_perf_loop.py \
  --candidate my-idea \
  --opts='--my-flag' \
  --dry-run
```

For expensive campaigns, use the same candidate name and option set on SLURM,
then append the result to the QF_LRA progress table in [](qf-lra.md).

## Decision Rules

Correctness blocks performance work. Any SAT/UNSAT disagreement, crash, parser
error, model failure, or failing regression test must be fixed before using the
performance numbers.

Default promotion requires at least:

- no answer disagreements against Z3/OpenSMT on commonly solved files;
- no worse solved count on quick and hard suites;
- no material quick/hard PAR2 regression;
- full-suite PAR2 improvement, or a clear solved-count gain with acceptable
  PAR2;
- a focused regression test or stats-gate when the change affects encoding.

Option-only retention is appropriate when:

- a technique helps a specific cluster but hurts quick/hard/full aggregate PAR2;
- the result is noisy but mechanically plausible and cheap when disabled;
- the option is useful for future experiments or as an ablation.

Reject or revert when:

- the mechanism does not fire on the target counters;
- it adds maintenance cost without a demonstrated win;
- it creates a larger encoding and worsens PAR2 without a compensating solved
  count gain;
- it makes later diagnosis harder.

## Exploration Lane

Every few exploitation iterations, run an exploration pass whose explicit goal
is new ideas. Do not start from the current patch. Start from one of these
sources:

- Reference-solver delta:
  pass Z3 and OpenSMT TSVs with `--ref-tsv`; choose a file where a reference is
  fast and native is slow; classify the formula shape and native counters.
- Stats mismatch:
  use `scripts/compare_z3_stats.py` on one target and look for missing native
  analogues of Z3 activity, such as fixed equalities, offset equalities, bound
  propagation, or final-check behavior.
- Synthetic probes:
  build or minimize small formulas that isolate one structure: finite-domain
  choices, arithmetic `ite`, guarded aliases, dense difference constraints,
  strict bounds, disequality branches, or repeated linear terms.
- Solver-feature scan:
  inspect Z3/OpenSMT/CVC5 papers, docs, or code for one preprocessing or LRA
  feature and translate it into a conservative experiment.

Each exploration pass should produce one of:

- a candidate implementation behind an option;
- a minimized benchmark that demonstrates a native weakness;
- a rejected-idea note explaining why the technique does not fit this solver.

## Idea Record Template

Use this template in the candidate report or in a short note before coding:

```text
Idea:
Source:
Target files:
Native symptom:
Reference behavior:
Expected mechanism:
Expected counters:
Correctness risks:
Default or option:
Quick/hard/full result:
Decision:
```

This keeps exploratory work concrete enough to evaluate while still encouraging
ideas that are not just local tweaks.
