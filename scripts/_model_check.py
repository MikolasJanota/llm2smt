"""
Shared helpers for model injection and verification.
Used by both check_model.py and fuzz.py.
"""

import os
import re
import subprocess
import tempfile

# Pattern matching abstract value terms: (as @k SortName)
_AV_PAT = re.compile(r'\(as\s+@(\d+)\s+(\w+)\)')


def extract_top_level_sexps(text: str) -> list[str]:
    """Return all top-level balanced S-expressions in *text* (handles ; comments)."""
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


def _sexp_head(s: str) -> str:
    toks = s.lstrip('(').split()
    return toks[0] if toks else ''


def _sexp_name(s: str) -> str:
    toks = s.lstrip('(').split()
    return toks[1] if len(toks) > 1 else ''


def extract_defines(model_text: str) -> dict[str, str]:
    """Parse (model ...) output → {symbol_name: define-fun-sexp}."""
    defines: dict[str, str] = {}
    for model_sexp in extract_top_level_sexps(model_text):
        if _sexp_head(model_sexp) != 'model':
            continue
        inner_start = model_sexp.find('(', 1)
        if inner_start < 0:
            continue
        inner = model_sexp[inner_start:-1]
        for df in extract_top_level_sexps(inner):
            if _sexp_head(df) == 'define-fun':
                name = _sexp_name(df)
                if name:
                    defines[name] = df
    return defines


def concretize_model(defines: dict[str, str]) -> tuple[dict[str, str], list[str]]:
    """Replace (as @k Sort) abstract values with fresh constant names.

    Returns (new_defines, av_declarations).
    Rationale: reference solvers accept (as @k Sort) only in their own model
    output, not as input terms.  Fresh uninterpreted constants are equivalent:
    the reference solver finds values for them that satisfy the asserted
    constraints, which is possible iff the model is consistent.
    """
    av_map: dict[tuple[str, str], str] = {}
    all_text = '\n'.join(defines.values())
    for m in _AV_PAT.finditer(all_text):
        key = (m.group(1), m.group(2))
        if key not in av_map:
            av_map[key] = f'__av_{m.group(1)}'

    decls = [
        f'(declare-fun {name} () {sort})'
        for (k_str, sort), name in sorted(av_map.items(), key=lambda x: int(x[0][0]))
    ]

    def replace(m: re.Match) -> str:
        return av_map.get((m.group(1), m.group(2)), m.group(0))

    new_defines = {sym: _AV_PAT.sub(replace, df) for sym, df in defines.items()}
    return new_defines, decls


def build_check_content(original: str, defines: dict[str, str]) -> str:
    """Build a modified SMT2 file with the model injected.

    Layout:
      1. (set-logic) and (declare-sort) commands from original
      2. (declare-fun __av_k () Sort)  — abstract value witnesses
      3. (define-fun ...) — model definitions (replaces declare-fun)
      4. (assert ...) and other remaining commands from original
      5. (check-sat)
    """
    concrete_defines, av_decls = concretize_model(defines)

    preamble: list[str] = []
    rest: list[str] = []

    for sexp in extract_top_level_sexps(original):
        head = _sexp_head(sexp)
        if head in ('check-sat', 'get-model'):
            continue
        if head == 'declare-fun' and _sexp_name(sexp) in concrete_defines:
            continue
        if head in ('set-logic', 'declare-sort'):
            preamble.append(sexp)
        else:
            rest.append(sexp)

    out = preamble + av_decls + list(concrete_defines.values()) + rest + ['(check-sat)']
    return '\n'.join(out) + '\n'


def run_solver_full(cmd: list[str], content: str, timeout: float) -> str:
    """Write *content* to a temp file, run *cmd*, return full stdout (stripped)."""
    fd, path = tempfile.mkstemp(suffix='.smt2')
    try:
        with os.fdopen(fd, 'w') as f:
            f.write(content)
        proc = subprocess.run(
            cmd + [path],
            capture_output=True, text=True, timeout=timeout,
        )
        return proc.stdout.strip()
    except subprocess.TimeoutExpired:
        return 'timeout'
    except FileNotFoundError:
        raise
    finally:
        try:
            os.unlink(path)
        except OSError:
            pass


def check_model_correct(
    original_smt2: str,
    our_cmd: list[str],
    ref_cmd: list[str],
    timeout: float,
) -> tuple[bool, str]:
    """Run our solver with (get-model) on *original_smt2* and verify via *ref_cmd*.

    Returns (passed, reason) where *reason* is a diagnostic string on failure.
    Call this only when our solver previously returned 'sat'.
    """
    content_with_gm = original_smt2.rstrip() + '\n(get-model)\n'
    output = run_solver_full(our_cmd, content_with_gm, timeout)

    if not output or output.split('\n', 1)[0].strip() != 'sat':
        return False, f'solver did not return sat on second run (got {output[:60]!r})'

    model_text = output.split('\n', 1)[1] if '\n' in output else ''
    if not model_text.strip():
        return False, 'solver produced no model output'

    defines = extract_defines(model_text)
    if not defines:
        return False, f'could not parse define-fun from model: {model_text[:120]!r}'

    check_content = build_check_content(original_smt2, defines)
    ref_output = run_solver_full(ref_cmd, check_content, timeout)
    ref_verdict = ref_output.split('\n', 1)[0].strip() if ref_output else ''

    if ref_verdict == 'sat':
        return True, ''
    return False, f'reference returned {ref_verdict!r} on model-injected file'
