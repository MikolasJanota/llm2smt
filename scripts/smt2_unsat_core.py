#!/usr/bin/env python3
"""Split one large conjunctive SMT2 assertion into assumptions and ask Z3 for a core."""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path
from typing import Iterable

sys.setrecursionlimit(200_000)

Expr = str | list["Expr"]


def tokenize(text: str) -> list[str]:
    toks: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c in "()":
            toks.append(c)
            i += 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    j += 1
                    break
                j += 2 if text[j] == "\\" and j + 1 < n else 1
            toks.append(text[i:j])
            i = j
        elif c == "|":
            j = i + 1
            while j < n:
                if text[j] == "|":
                    j += 1
                    break
                j += 2 if text[j] == "\\" and j + 1 < n else 1
            toks.append(text[i:j])
            i = j
        else:
            j = i
            while j < n and not text[j].isspace() and text[j] not in "();":
                j += 1
            toks.append(text[i:j])
            i = j
    return toks


def parse_tokens(toks: list[str]) -> list[Expr]:
    pos = 0

    def parse_expr() -> Expr:
        nonlocal pos
        if pos >= len(toks):
            raise ValueError("unexpected end of input")
        tok = toks[pos]
        pos += 1
        if tok != "(":
            if tok == ")":
                raise ValueError("unexpected ')'")
            return tok
        xs: list[Expr] = []
        while pos < len(toks) and toks[pos] != ")":
            xs.append(parse_expr())
        if pos >= len(toks):
            raise ValueError("missing ')'")
        pos += 1
        return xs

    exprs: list[Expr] = []
    while pos < len(toks):
        exprs.append(parse_expr())
    return exprs


def atom_text(x: Expr) -> str:
    if not isinstance(x, str):
        raise TypeError(f"expected atom, got {x!r}")
    return x


def sexpr(x: Expr) -> str:
    if isinstance(x, str):
        return x
    return "(" + " ".join(sexpr(y) for y in x) + ")"


def peel_lets(expr: Expr) -> tuple[list[list[Expr]], Expr]:
    frames: list[list[Expr]] = []
    cur = expr
    while isinstance(cur, list) and len(cur) == 3 and cur[0] == "let":
        bindings = cur[1]
        if not isinstance(bindings, list):
            break
        frames.append(bindings)
        cur = cur[2]
    return frames, cur


def wrap_lets(frames: list[list[Expr]], body: Expr) -> Expr:
    cur = body
    for bindings in reversed(frames):
        cur = ["let", bindings, cur]
    return cur


def collect_let_env(frames: Iterable[list[Expr]]) -> dict[str, Expr]:
    env: dict[str, Expr] = {}
    for frame in frames:
        for binding in frame:
            if isinstance(binding, list) and len(binding) == 2 and isinstance(binding[0], str):
                env[binding[0]] = binding[1]
    return env


def resolve(expr: Expr, env: dict[str, Expr], depth: int = 0) -> Expr:
    while isinstance(expr, str) and expr in env and depth < 100:
        expr = env[expr]
        depth += 1
    return expr


def classify(expr: Expr, env: dict[str, Expr]) -> str:
    expr = resolve(expr, env)
    if isinstance(expr, str):
        return "atom/ref"
    if not expr:
        return "empty"
    op = expr[0]
    if op == "or":
        kinds = [classify(c, env) for c in expr[1:]]
        if all(k in {"eq", "not-eq", "pred", "not-pred", "atom/ref"} for k in kinds):
            from collections import Counter

            counts = Counter(kinds)
            detail = ",".join(f"{k}:{counts[k]}" for k in sorted(counts))
            return f"or/{len(expr)-1}[{detail}]"
        return "or/compound"
    if op == "=":
        return "eq"
    if op == "distinct":
        return "distinct"
    if op == "not" and len(expr) == 2:
        k = classify(expr[1], env)
        if k == "eq":
            return "not-eq"
        if k.startswith("pred"):
            return "not-pred"
        return "not-" + k
    if isinstance(op, str) and op.startswith("p"):
        return "pred"
    return str(op)


def transform(forms: list[Expr]) -> tuple[list[Expr], dict[str, tuple[int, str, Expr]]]:
    out: list[Expr] = []
    core_map: dict[str, tuple[int, str, Expr]] = {}
    core_names: list[str] = []
    inserted_option = False
    transformed = False
    next_id = 0

    for form in forms:
        if not isinstance(form, list) or not form:
            out.append(form)
            continue

        head = form[0]
        if head == "set-logic":
            out.append(form)
            out.append(["set-option", ":produce-unsat-cores", "true"])
            inserted_option = True
            continue
        if head in {"check-sat", "exit", "get-unsat-core"}:
            continue
        if head != "assert" or len(form) != 2 or transformed:
            out.append(form)
            continue

        frames, body = peel_lets(form[1])
        if not (isinstance(body, list) and body and body[0] == "and"):
            out.append(form)
            continue

        env = collect_let_env(frames)
        guarded: list[Expr] = ["and"]
        for child in body[1:]:
            name = f"__core_{next_id}"
            next_id += 1
            core_names.append(name)
            core_map[name] = (next_id - 1, classify(child, env), child)
            out.append(["declare-fun", name, [], "Bool"])
            guarded.append(["=>", name, child])
        out.append(["assert", wrap_lets(frames, guarded)])
        transformed = True

    if not inserted_option:
        out.insert(0, ["set-option", ":produce-unsat-cores", "true"])
    if not transformed:
        raise RuntimeError("no single top-level conjunctive assertion was transformed")
    out.append(["check-sat-assuming", core_names])
    out.append(["get-unsat-core"])
    out.append(["exit"])
    return out, core_map


def filter_to_core(forms: list[Expr], keep_indices: set[int]) -> list[Expr]:
    out: list[Expr] = []
    transformed = False
    for form in forms:
        if not isinstance(form, list) or not form:
            out.append(form)
            continue
        if form[0] in {"get-unsat-core"}:
            continue
        if form[0] != "assert" or len(form) != 2 or transformed:
            out.append(form)
            continue
        frames, body = peel_lets(form[1])
        if not (isinstance(body, list) and body and body[0] == "and"):
            out.append(form)
            continue
        kept = [child for i, child in enumerate(body[1:]) if i in keep_indices]
        if not kept:
            out.append(["assert", "true"])
        elif len(kept) == 1:
            out.append(["assert", wrap_lets(frames, kept[0])])
        else:
            out.append(["assert", wrap_lets(frames, ["and", *kept])])
        transformed = True
    return out


def parse_core(stdout: str) -> list[str]:
    lines = [ln.strip() for ln in stdout.splitlines() if ln.strip()]
    if not lines or lines[0] != "unsat":
        return []
    core_text = " ".join(lines[1:])
    if not core_text.startswith("("):
        return []
    parsed = parse_tokens(tokenize(core_text))
    if not parsed or not isinstance(parsed[0], list):
        return []
    return [atom_text(x) for x in parsed[0]]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("--out", type=Path, help="write transformed SMT2 here")
    ap.add_argument("--z3", default=".venv-z3/bin/z3")
    ap.add_argument("--run", action="store_true", help="run Z3 and summarize the returned core")
    ap.add_argument("--core-out", type=Path, help="write a core-only SMT2 file after running Z3")
    ap.add_argument("--show", type=int, default=20, help="number of core entries to show")
    args = ap.parse_args()

    forms = parse_tokens(tokenize(args.input.read_text()))
    transformed, core_map = transform(forms)
    text = "\n".join(sexpr(f) for f in transformed) + "\n"

    out = args.out or args.input.with_suffix(args.input.suffix + ".core.smt2")
    out.write_text(text)
    print(f"wrote {out}")
    print(f"tracked conjuncts: {len(core_map)}")

    if not args.run:
        return 0

    proc = subprocess.run([args.z3, str(out)], text=True, capture_output=True, check=False)
    if proc.stderr:
        print(proc.stderr, file=sys.stderr)
    print(proc.stdout.splitlines()[0] if proc.stdout else f"z3 exited {proc.returncode}")
    core = parse_core(proc.stdout)
    if not core:
        print(proc.stdout)
        return proc.returncode

    if args.core_out:
        keep = {core_map[name][0] for name in core if name in core_map}
        args.core_out.write_text("\n".join(sexpr(f) for f in filter_to_core(forms, keep)) + "\n")
        print(f"wrote core-only file: {args.core_out}")

    from collections import Counter

    counts = Counter(core_map[name][1] for name in core if name in core_map)
    total_counts = Counter(kind for _, kind, _ in core_map.values())
    print("all classes:")
    for kind, count in total_counts.most_common():
        print(f"  {kind:32s} {count}")
    print(f"core size: {len(core)}")
    print("core classes:")
    for kind, count in counts.most_common():
        total = total_counts[kind]
        pct = 100.0 * count / total if total else 0.0
        print(f"  {kind:32s} {count:5d} / {total:<5d} ({pct:5.1f}%)")
    print("sample core entries:")
    for name in core[: args.show]:
        idx, kind, child = core_map[name]
        print(f"  {name} idx={idx} kind={kind} expr={sexpr(child)[:240]}")
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
