#!/usr/bin/env python3
"""
check_model.py — verify that SAT models produced by llm2smt are correct.

For each SMT2 file:
  1. Append (get-model) and run our solver.
  2. If the result is SAT, parse the (model ...) block.
  3. Build a modified SMT2 file where every declare-fun for a modelled symbol
     is replaced by the corresponding define-fun from the model, then add
     (check-sat) at the end.
  4. Run a reference solver (cvc5 by default) on the modified file.
     A correct model must make the reference solver return SAT.

Usage:
    python scripts/check_model.py file.smt2 [file2.smt2 ...]
    python scripts/check_model.py tests/smt2/*.smt2
    python scripts/check_model.py --our-solver build-rel/bin/llm2smt --ref cvc5 f.smt2

Exit code: 0 if every checked model passes, 1 if any model is wrong.
"""

import argparse
import os
import sys
from pathlib import Path

sys.path.insert(0, os.path.dirname(__file__))
from _model_check import (
    extract_defines, build_check_content,
    run_solver_full,
)


def check_file(
    path: str,
    our_cmd: list[str],
    ref_cmd: list[str],
    timeout: float,
    verbose: bool,
    save_fails: str | None,
) -> str:
    """Check the model for one file.  Returns 'ok', 'skip', or 'fail'."""
    with open(path) as f:
        original = f.read()

    # Step 1 — run our solver with (get-model) appended.
    content_with_gm = original.rstrip() + '\n(get-model)\n'
    output = run_solver_full(our_cmd, content_with_gm, timeout)

    if not output:
        if verbose:
            print(f'  skip (no output): {path}')
        return 'skip'

    first_line = output.split('\n', 1)[0].strip()
    if first_line != 'sat':
        if verbose:
            print(f'  skip ({first_line}): {path}')
        return 'skip'

    model_text = output.split('\n', 1)[1] if '\n' in output else ''
    if not model_text.strip():
        print(f'FAIL {path}: solver returned SAT but produced no model')
        return 'fail'

    # Step 2 — parse the model.
    defines = extract_defines(model_text)
    if not defines:
        print(f'FAIL {path}: could not parse any define-fun from model output')
        if verbose:
            print('  model output:', repr(model_text[:300]))
        return 'fail'

    if verbose:
        print(f'  modelled symbols: {sorted(defines)}')

    # Step 3 — build modified file with model injected.
    check_content = build_check_content(original, defines)

    # Step 4 — reference solver must say SAT.
    ref_output = run_solver_full(ref_cmd, check_content, timeout)
    ref_verdict = ref_output.split('\n', 1)[0].strip() if ref_output else ''

    if ref_verdict == 'sat':
        if verbose:
            print(f'  OK: {path}')
        return 'ok'

    print(f'FAIL {path}: reference returned {ref_verdict!r} on model-injected file')
    if verbose:
        print('  Raw model output:')
        print(model_text[:400])
        print('  Modified file fed to reference:')
        print(check_content[:700])

    if save_fails:
        os.makedirs(save_fails, exist_ok=True)
        stem = Path(path).stem
        fail_path = os.path.join(save_fails, f'{stem}_model_fail.smt2')
        with open(fail_path, 'w') as f:
            f.write('; Original: ' + path + '\n')
            f.write('; Modified file fed to reference:\n')
            f.write(check_content)
        print(f'  Saved to: {fail_path}')

    return 'fail'


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    ap.add_argument('files', nargs='+', help='SMT2 files to test')
    ap.add_argument(
        '--our-solver', default='build-dbg/bin/llm2smt',
        help='Path to our solver (default: build-dbg/bin/llm2smt)',
    )
    ap.add_argument(
        '--ref', default='cvc5',
        help='Reference solver (default: cvc5)',
    )
    ap.add_argument(
        '--timeout', type=float, default=5.0,
        help='Per-solver timeout in seconds (default: 5)',
    )
    ap.add_argument('-v', '--verbose', action='store_true')
    ap.add_argument(
        '--save-fails', metavar='DIR',
        help='Save failing model-check files to DIR for inspection',
    )
    args = ap.parse_args()

    our_cmd = args.our_solver.split()
    ref_cmd = args.ref.split()

    ok_count = skip_count = fail_count = 0

    for path in args.files:
        result = check_file(path, our_cmd, ref_cmd, args.timeout,
                            args.verbose, args.save_fails)
        if result == 'ok':
            ok_count += 1
        elif result == 'skip':
            skip_count += 1
        else:
            fail_count += 1

    total = ok_count + skip_count + fail_count
    print(f'\nResults: {ok_count} ok, {skip_count} skipped (unsat/unknown), '
          f'{fail_count} failed  [{total} files]')

    sys.exit(1 if fail_count else 0)


if __name__ == '__main__':
    main()
