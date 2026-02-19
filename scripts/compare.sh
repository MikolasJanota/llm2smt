#!/usr/bin/env bash
# compare.sh — run our solver on a directory of .smt2 files and compare against cvc5.
#
# Usage:
#   scripts/compare.sh <dir> [timeout_s] [solver_binary]
#
# Defaults:
#   timeout_s     = 2
#   solver_binary = build/src/llm2smt   (relative to repo root)
#
# Output: one line per file, then a summary.  Exit code 0 iff no MISMATCHes.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

DIR="${1:?Usage: $0 <dir> [timeout_s] [solver]}"
TIMEOUT="${2:-2}"
SOLVER="${3:-$REPO_ROOT/build/src/llm2smt}"

if [[ ! -x "$SOLVER" ]]; then
    echo "Solver not found or not executable: $SOLVER" >&2
    exit 1
fi

pass=0; fail=0; error=0; skip=0

for f in "$DIR"/*.smt2; do
    [[ -e "$f" ]] || { echo "No .smt2 files in $DIR" >&2; exit 1; }
    name=$(basename "$f")

    ours=$(timeout "${TIMEOUT}s" "$SOLVER" "$f" 2>/dev/null) || rc=$?
    rc=${rc:-0}

    if [[ $rc -eq 124 ]]; then
        skip=$((skip+1))
        continue
    fi

    if [[ -z "$ours" ]]; then
        error=$((error+1))
        printf "%-55s ours=%-10s\n" "$name" "ERROR"
        continue
    fi

    cvc5_out=$(timeout 10s cvc5 "$f" 2>/dev/null | head -1) || true

    if [[ "$ours" == "$cvc5_out" ]]; then
        pass=$((pass+1))
        printf "%-55s ours=%-10s cvc5=%-10s OK\n" "$name" "$ours" "$cvc5_out"
    else
        fail=$((fail+1))
        printf "%-55s ours=%-10s cvc5=%-10s MISMATCH\n" "$name" "$ours" "$cvc5_out"
    fi
done

echo ""
echo "$(basename "$DIR"): pass=$pass  fail=$fail  error=$error  skip=$skip (timeout=${TIMEOUT}s)"

[[ $fail -eq 0 ]]
