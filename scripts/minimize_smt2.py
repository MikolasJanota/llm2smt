#!/usr/bin/env python3
"""
Heuristic SMT2 minimizer.

Repeatedly removes or replaces top-level assertions while the target command
still triggers the same failure mode (detected by exit code and/or output
pattern).  Uses a greedy delta-debugging approach: each pass tries dropping
each remaining assertion; passes continue until stable.

Usage:
    python scripts/minimize_smt2.py \\
        --cmd 'build-dbg/bin/llm2smt --preprocess-passes 1 --selectors' \\
        --input fuzz_fails/error_000067.smt2 \\
        --output minimal.smt2

    # Match on a specific string in stderr (default: any non-zero exit code)
    python scripts/minimize_smt2.py \\
        --cmd 'build-dbg/bin/llm2smt' \\
        --input fail.smt2 \\
        --match 'SEGV'
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path


# ---------------------------------------------------------------------------
# S-expression parser (just enough to extract top-level commands)
# ---------------------------------------------------------------------------

def _top_level_sexps(text: str) -> list[str]:
    """Return all top-level balanced S-expressions, stripping ; comments."""
    result: list[str] = []
    depth = 0
    start = -1
    in_str = False
    i = 0
    while i < len(text):
        c = text[i]
        if in_str:
            if c == '\\':
                i += 2
                continue
            if c == '"':
                in_str = False
        elif c == '"':
            in_str = True
            if depth == 0:
                start = i
        elif c == ';':
            while i < len(text) and text[i] != '\n':
                i += 1
            continue
        elif c == '(':
            if depth == 0:
                start = i
            depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0 and start >= 0:
                result.append(text[start:i + 1])
                start = -1
        i += 1
    return result


def _head(sexp: str) -> str:
    return sexp.lstrip('(').split()[0] if sexp.lstrip('(').split() else ''


# ---------------------------------------------------------------------------
# Failure oracle
# ---------------------------------------------------------------------------

def _run(cmd: list[str], content: str, timeout: float) -> tuple[int, str, str]:
    """Write content to a temp file, run cmd on it; return (returncode, stdout, stderr)."""
    fd, path = tempfile.mkstemp(suffix='.smt2')
    try:
        with os.fdopen(fd, 'w') as f:
            f.write(content)
        r = subprocess.run(
            cmd + [path],
            capture_output=True, text=True, timeout=timeout + 2,
        )
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return -1, '', 'timeout'
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def make_oracle(cmd: list[str], match: str | None, timeout: float):
    """Return a function content -> bool that is True when the failure is present."""
    def oracle(content: str) -> bool:
        rc, stdout, stderr = _run(cmd, content, timeout)
        combined = stdout + stderr
        if match:
            return match in combined
        # Default: any non-zero exit (but not a parse error that hides the real crash)
        return rc != 0
    return oracle


# ---------------------------------------------------------------------------
# SMT2 assembly
# ---------------------------------------------------------------------------

def _assemble(preamble: list[str], asserts: list[str], footer: list[str]) -> str:
    return '\n'.join(preamble + asserts + footer) + '\n'


# ---------------------------------------------------------------------------
# Minimization passes
# ---------------------------------------------------------------------------

def _minimize_assertions(preamble: list[str], asserts: list[str],
                          footer: list[str], oracle, verbose: bool) -> list[str]:
    """
    Greedy single-removal pass: try dropping each assertion.
    Repeat until no further reduction is found.
    """
    changed = True
    while changed:
        changed = False
        i = 0
        while i < len(asserts):
            candidate = asserts[:i] + asserts[i + 1:]
            if oracle(_assemble(preamble, candidate, footer)):
                if verbose:
                    print(f"  Removed assertion {i}: {asserts[i][:60]}")
                asserts = candidate
                changed = True
                # don't increment i — the list shifted
            else:
                i += 1
    return asserts


def _minimize_assert_to_true(preamble: list[str], asserts: list[str],
                              footer: list[str], oracle, verbose: bool) -> list[str]:
    """
    Try replacing each assertion body with 'true' (simplest possible assertion).
    Useful when the formula structure itself matters.
    """
    changed = True
    while changed:
        changed = False
        for i, a in enumerate(asserts):
            if a == '(assert true)':
                continue
            candidate = asserts[:i] + ['(assert true)'] + asserts[i + 1:]
            if oracle(_assemble(preamble, candidate, footer)):
                if verbose:
                    print(f"  Replaced assertion {i} with (assert true): {a[:60]}")
                asserts = candidate
                changed = True
                break  # restart scan after any change
    return asserts


def _minimize_declarations(preamble: list[str], asserts: list[str],
                            footer: list[str], oracle, verbose: bool) -> list[str]:
    """
    Try dropping individual declare-fun / declare-sort lines from the preamble
    (only non-logic lines, not set-logic / declare-sort U 0).
    """
    # Only attempt to remove declare-fun for constants / functions.
    # Removing declare-sort and set-logic would break parsing.
    droppable = [i for i, s in enumerate(preamble)
                 if _head(s) == 'declare-fun']
    changed = True
    while changed:
        changed = False
        for idx in list(droppable):
            if idx >= len(preamble):
                continue
            candidate_pre = preamble[:idx] + preamble[idx + 1:]
            if oracle(_assemble(candidate_pre, asserts, footer)):
                if verbose:
                    print(f"  Removed declaration: {preamble[idx][:60]}")
                preamble = candidate_pre
                # Rebuild droppable list since indices shifted
                droppable = [i for i, s in enumerate(preamble)
                             if _head(s) == 'declare-fun']
                changed = True
                break
    return preamble


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description='Heuristic SMT2 minimizer — shrinks a failing input.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    ap.add_argument('--cmd', required=True,
                    help='Solver command (space-separated, file appended at end)')
    ap.add_argument('--input', required=True,
                    help='Failing SMT2 input file')
    ap.add_argument('--output', default=None,
                    help='Output path for minimized file (default: print to stdout)')
    ap.add_argument('--match', default=None,
                    help='String that must appear in combined stdout+stderr to '
                         'confirm the failure (default: any non-zero exit code)')
    ap.add_argument('--timeout', type=float, default=5.0,
                    help='Per-run timeout in seconds')
    ap.add_argument('-v', '--verbose', action='store_true',
                    help='Print each successful reduction')
    args = ap.parse_args()

    cmd = args.cmd.split()
    text = Path(args.input).read_text()
    oracle = make_oracle(cmd, args.match, args.timeout)

    # Confirm the original file triggers the failure.
    if not oracle(text):
        print('ERROR: the original file does NOT trigger the failure.', file=sys.stderr)
        print('  Check --cmd and --match.', file=sys.stderr)
        return 1

    all_sexps = _top_level_sexps(text)

    preamble: list[str] = []
    asserts:  list[str] = []
    footer:   list[str] = []

    saw_assert = False
    for s in all_sexps:
        h = _head(s)
        if h == 'check-sat':
            footer.append(s)
        elif h == 'assert':
            saw_assert = True
            asserts.append(s)
        elif not saw_assert:
            preamble.append(s)
        else:
            footer.insert(len(footer) - 1 if footer else 0, s)

    orig_n = len(asserts)
    print(f'Starting with {orig_n} assertion(s). Minimizing...')

    # Pass 1: drop assertions
    asserts = _minimize_assertions(preamble, asserts, footer, oracle, args.verbose)
    print(f'After assertion removal: {len(asserts)} assertion(s) '
          f'(removed {orig_n - len(asserts)})')

    # Pass 2: replace assertion bodies with true
    asserts = _minimize_assert_to_true(preamble, asserts, footer, oracle, args.verbose)
    trivial = sum(1 for a in asserts if a == '(assert true)')
    print(f'After simplification: {trivial} trivial, '
          f'{len(asserts) - trivial} non-trivial assertion(s)')

    # Pass 3: drop unused declarations
    preamble = _minimize_declarations(preamble, asserts, footer, oracle, args.verbose)

    result = _assemble(preamble, asserts, footer)

    # Sanity check: still triggers.
    if oracle(result):
        print('Minimization complete — failure still reproduced.')
    else:
        print('WARNING: minimized file no longer triggers the failure!', file=sys.stderr)

    if args.output:
        Path(args.output).write_text(result)
        print(f'Written to: {args.output}')
    else:
        print('\n--- Minimized file ---')
        print(result)

    return 0


if __name__ == '__main__':
    sys.exit(main())
