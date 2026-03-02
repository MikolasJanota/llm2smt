#!/usr/bin/env bash
# Oracle for minimize_smt2.py: exits non-zero when the solver returns "unsat"
# AND the generated Lean proof fails verification.
#
# Usage (from the repo root):
#   python scripts/minimize_smt2.py \
#       --cmd 'scripts/oracle_proof_fail.sh --preprocess-passes 1' \
#       --input failing.smt2 --output minimal.smt2
#
# Arguments:
#   [solver-flags...]  any flags accepted by llm2smt (before the smt2 file)
#   <file.smt2>        the SMT-LIB2 file to test (must be the last argument)
#
# Environment (optional):
#   ORACLE_SOLVER     path to the llm2smt binary (default: build-dbg/bin/llm2smt)
#   ORACLE_CHECK      path to the proof-checker script (default: sandbox/check_proof.sh)
#   ORACLE_PROJECT    --lean-project name forwarded to the solver (default: Experiments3)

set -euo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
SOLVER="${ORACLE_SOLVER:-$REPO/build-dbg/bin/llm2smt}"
CHECK="${ORACLE_CHECK:-$REPO/sandbox/check_proof.sh}"
PROJECT="${ORACLE_PROJECT:-Experiments3}"

# All args except the last are extra solver flags; the last arg is the smt2 file.
if [[ $# -lt 1 ]]; then
    echo "Usage: $0 [solver-flags...] <file.smt2>" >&2
    exit 2
fi

EXTRA_FLAGS=("${@:1:$#-1}")   # everything except last arg
SMT2_FILE="${!#}"              # last arg

PROOF=$(mktemp /tmp/oracle_XXXXXX.lean)
trap 'rm -f "$PROOF"' EXIT

# Step 1: run the solver.
result=$(timeout 10 "$SOLVER" "${EXTRA_FLAGS[@]}" --proof "$PROOF" \
         --lean-project "$PROJECT" "$SMT2_FILE" 2>/dev/null || true)

[[ "$result" != "unsat" ]] && exit 0  # not unsat → not a proof case

# Step 2: run the proof checker from its own directory.
CHECK_DIR="$(dirname "$CHECK")"
if bash "$CHECK" "$PROOF" >/dev/null 2>&1; then
    exit 0   # proof passed → not interesting
else
    exit 1   # proof failed → bug reproduced
fi
