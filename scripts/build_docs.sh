#!/usr/bin/env bash
# Build the Jupyter Book developer documentation.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
VENV="${LLM2SMT_DOCS_VENV:-$REPO_ROOT/.venv-docs}"

cd "$REPO_ROOT"

if [[ ! -x "$VENV/bin/python" ]]; then
    python3 -m venv "$VENV"
fi

"$VENV/bin/python" -m pip install -r docs/requirements.txt
"$VENV/bin/python" -c '
import sys
from jupyter_book.cli.main import main
main(args=["build", "docs"] + sys.argv[1:], standalone_mode=True)
' "$@"
