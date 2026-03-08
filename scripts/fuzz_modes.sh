#!/usr/bin/env bash
# Run the fuzzer in several solver-flag modes.
# Usage:  scripts/fuzz_modes.sh [extra fuzz.py args...]
#
# Each mode gets its own --save-fails directory so failing cases don't
# overwrite each other.  All other fuzz.py options (--count, --ref,
# --check-proof, --seed, etc.) can be passed as extra arguments and are
# forwarded to every mode.
#
# Example (correctness + proof checking, 200 cases per mode):
#   scripts/fuzz_modes.sh --ref cvc5 --count 200 --seed 42 \
#       --check-proof sandbox/check_proof.sh
#
# Example (correctness only, parallel):
#   scripts/fuzz_modes.sh --ref cvc5 --count 500 -j 4

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FUZZ="$SCRIPT_DIR/fuzz.py"
SOLVER="build-dbg/bin/llm2smt"

run_mode() {
    local label="$1"
    local solver_cmd="$2"
    local save_dir="fuzz_fails_${label}"
    shift 2
    echo "════════════════════════════════════════════════════"
    echo "  Mode: $label"
    echo "  Solver: $solver_cmd"
    echo "════════════════════════════════════════════════════"
    python "$FUZZ" \
        --our-solver "$solver_cmd" \
        --save-fails "$save_dir" \
        "$@"
    echo
}

EXTRA=("$@")

# Mode 1: plain (no preprocessing)
run_mode "plain"           "$SOLVER"                              "${EXTRA[@]}"

# Mode 2: preprocess-passes 1
run_mode "preproc1"        "$SOLVER --preprocess-passes 1"        "${EXTRA[@]}"

# Mode 3: preprocess-passes 1 + NNF
run_mode "preproc1_nnf"   "$SOLVER --preprocess-passes 1 --nnf"  "${EXTRA[@]}"

# Mode 4: eq-bridge
run_mode "eq_bridge"      "$SOLVER --eq-bridge"                 "${EXTRA[@]}"
