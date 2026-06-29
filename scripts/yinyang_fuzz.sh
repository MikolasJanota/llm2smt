#!/usr/bin/env bash
# Run YinYang/typefuzz against llm2smt and a reference SMT solver.
#
# YinYang is intentionally seed-based and long-running. This wrapper adds
# bounded runs, repo-local output directories, and defaults that match the
# existing llm2smt fuzz workflow.

set -euo pipefail

SEEDS="tests/smt2"
SOLVER="build-dbg/bin/llm2smt --quiet"
REF="z3 model_validate=true"
SECONDS=300
ITERATIONS=50
SOLVER_TIMEOUT=8
BUGS="yinyang_bugs"
SCRATCH="yinyang_scratch"
FILE_SIZE_LIMIT=20000
TYPEFUZZ="${TYPEFUZZ:-typefuzz}"
DIAGNOSE=0
KEEP_MUTANTS=0
EXTRA_ARGS=()

usage() {
    cat <<'EOF'
Usage: scripts/yinyang_fuzz.sh [options] [-- extra typefuzz args...]

Options:
  --seeds PATH             SMT-LIB seed file or directory (default: tests/smt2)
  --solver CMD             llm2smt command (default: build-dbg/bin/llm2smt --quiet)
  --ref CMD                reference solver command (default: z3 model_validate=true)
  --seconds N              wall-clock limit for typefuzz (default: 300)
  --iterations N           YinYang mutations per seed (default: 50)
  --solver-timeout N       per-solver timeout in seconds (default: 8)
  --bugs DIR               bug output directory (default: yinyang_bugs)
  --scratch DIR            scratch directory (default: yinyang_scratch)
  --file-size-limit N      max seed size in bytes (default: 20000)
  --typefuzz PATH          typefuzz executable (default: $TYPEFUZZ or typefuzz)
  --diagnose               forward solver output to stdout
  --keep-mutants           keep generated mutants in scratch
  -h, --help               show this help

Install:
  python3 -m pip install yinyang

Example:
  scripts/yinyang_fuzz.sh \
    --seeds sandbox/non-incremental/QF_LRA/check \
    --solver 'build-workspace-rel/bin/llm2smt --quiet' \
    --ref 'z3 model_validate=true' \
    --seconds 600 --iterations 100
EOF
}

while (($#)); do
    case "$1" in
        --seeds) SEEDS="$2"; shift 2 ;;
        --solver) SOLVER="$2"; shift 2 ;;
        --ref) REF="$2"; shift 2 ;;
        --seconds) SECONDS="$2"; shift 2 ;;
        --iterations) ITERATIONS="$2"; shift 2 ;;
        --solver-timeout) SOLVER_TIMEOUT="$2"; shift 2 ;;
        --bugs) BUGS="$2"; shift 2 ;;
        --scratch) SCRATCH="$2"; shift 2 ;;
        --file-size-limit) FILE_SIZE_LIMIT="$2"; shift 2 ;;
        --typefuzz) TYPEFUZZ="$2"; shift 2 ;;
        --diagnose) DIAGNOSE=1; shift ;;
        --keep-mutants) KEEP_MUTANTS=1; shift ;;
        -h|--help) usage; exit 0 ;;
        --) shift; EXTRA_ARGS=("$@"); break ;;
        *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    esac
done

if ! command -v "$TYPEFUZZ" >/dev/null 2>&1; then
    cat >&2 <<EOF
Error: '$TYPEFUZZ' not found.

Install YinYang first:
  python3 -m pip install yinyang

Or pass --typefuzz /path/to/typefuzz.
EOF
    exit 127
fi

if [[ ! -e "$SEEDS" ]]; then
    echo "Error: seed path does not exist: $SEEDS" >&2
    exit 1
fi

mkdir -p "$BUGS" "$SCRATCH"

cmd=(
    "$TYPEFUZZ"
    -i "$ITERATIONS"
    -t "$SOLVER_TIMEOUT"
    -b "$BUGS"
    -s "$SCRATCH"
    -L "$FILE_SIZE_LIMIT"
)

if ((DIAGNOSE)); then
    cmd+=(-d)
fi
if ((KEEP_MUTANTS)); then
    cmd+=(-km)
fi
cmd+=("${EXTRA_ARGS[@]}")
cmd+=("$SOLVER;$REF" "$SEEDS")

echo "YinYang command:"
printf '  %q' timeout "$SECONDS" "${cmd[@]}"
echo

timeout "$SECONDS" "${cmd[@]}"
