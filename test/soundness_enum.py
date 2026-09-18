#!/usr/bin/env python3
"""Independent ground truth for the sharing-sensitive test files.

Lin's DUP sharing was unsound: every fan carried the empty gauge, so two
*independent* sharing points annihilated against each other and merged their
values.  The test suite did not catch it because it *asserted* the resulting
values -- `test/sat_verify.lin` even labels its own wrong answer a
"superposition collapse false negative" while asserting the correct value for
the explicitly-desugared form of the same formula.

This checker pins those files to an independent oracle.  For every top-level
expression it can evaluate it computes the value by ordinary lambda evaluation
over {true,false} -- no interaction nets, no fans, no sharing -- and requires the
engine's readback to agree.  A sharing change that reintroduces the collapse (or
any other unsoundness on these formulas) fails here even if the expected-value
comments were edited to match the engine.

What is compared: boolean outcomes (SAT/UNSAT decisions and certificate
verification).  Structural readback (pairs, models) is not compared textually, so
those lines are reported as skipped.

usage: soundness_enum.py <lin-binary> <std-dir> <file.lin> [<file.lin> ...]
"""

import os
import re
import subprocess
import sys

DIRECTIVES = {"load", "namespace", "open", "export", "datatype", "define", "define!"}


# ---------------------------------------------------------------- S-expressions

def tokenize(src):
    toks, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c == ';':                                  # comment to end of line
            while i < n and src[i] != '\n':
                i += 1
        elif c in ' \t\r\n':
            i += 1
        elif c in '()':
            toks.append(c)
            i += 1
        elif c == '"':                                # string literal
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == '\\' else 1
            toks.append(src[i:j + 1])
            i = j + 1
        else:
            j = i
            while j < n and src[j] not in ' \t\r\n()':
                j += 1
            toks.append(src[i:j])
            i = j
    return toks


def parse_all(toks):
    forms, i = [], 0

    def parse(i):
        assert toks[i] == '('
        i += 1
        out = []
        while toks[i] != ')':
            if toks[i] == '(':
                sub, i = parse(i)
                out.append(sub)
            else:
                out.append(toks[i])
                i += 1
        return out, i + 1

    while i < len(toks):
        if toks[i] == '(':
            form, i = parse(i)
            forms.append(form)
        else:
            i += 1
    return forms


# --------------------------------------------------------------------- evaluator

class Unknown(Exception):
    """The expression uses something this oracle does not model."""


# Church booleans are *functions* here: they are applied to thunks
# (`((or x1) (not x1))`, `(a tru)`), so they must never be collapsed to a Python
# bool during evaluation -- only interpreted at the end.
TRUE = lambda t: (lambda f: t)
FALSE = lambda t: (lambda f: f)


def truth(v):
    """Interpret an evaluated value as a boolean, or None if it is not one."""
    try:
        r = v(True)(False)
    except Exception:
        return None
    return r if isinstance(r, bool) else None


class World:
    """Definitions collected from a file and everything it loads."""

    def __init__(self, std_dir):
        self.std_dir = std_dir
        self.defs = {}            # qualified or bare name -> body AST
        self.values = {}          # memoized evaluated bodies
        self.loaded = set()

    def lookup(self, name):
        if name in self.defs:
            return name
        if '.' not in name:                           # bare name: any namespace
            hits = [k for k in self.defs if k.endswith('.' + name)]
            if len(hits) == 1:
                return hits[0]
        raise Unknown(name)

    def value(self, name):
        key = self.lookup(name)
        if key not in self.values:
            self.values[key] = ev(self.defs[key], {}, self)
        return self.values[key]

    def load(self, path):
        path = os.path.realpath(path)
        if path in self.loaded or not os.path.exists(path):
            return
        self.loaded.add(path)
        src = open(path).read()
        cur_dir = os.path.dirname(path)
        ns = ''
        for form in parse_all(tokenize(src)):
            if not form or not isinstance(form[0], str):
                continue
            kw = form[0]
            if kw == 'load':                          # depth-first, like the engine
                rel = form[1].strip('"')
                self.load(self.resolve(rel, cur_dir))
            elif kw == 'namespace':
                ns = '' if form[1] in ('_', 'root') else form[1]
            elif kw in ('define', 'define!'):
                name = form[1]
                body = form[3] if len(form) >= 4 else form[2]
                key = f'{ns}.{name}' if ns and '.' not in name else name
                self.defs[key] = body
                self.defs.setdefault(name, body)      # bare alias (exports)

    def resolve(self, rel, cur_dir):
        if rel.startswith('std/'):
            return os.path.join(self.std_dir, rel[4:])
        p = os.path.join(cur_dir, rel)
        return p if os.path.exists(p) else os.path.join(self.std_dir, rel)


def ev(node, env, world):
    if isinstance(node, str):
        if node in ('true', 'tru'):
            return TRUE
        if node in ('false', 'fls'):
            return FALSE
        if node in env:
            return env[node]
        if node.isdigit():                    # Scott numeral, e.g. the `0` that
            return ('num', int(node))         # `ifl` passes to a branch thunk
        return world.value(node)
    if not node:
        raise Unknown('()')
    head = node[0]
    if isinstance(head, str) and head.startswith('\\'):        # (\x body)
        var, body = head[1:], node[1]
        return lambda a, var=var, body=body, env=env: ev(body, {**env, var: a}, world)
    f = ev(head, env, world)
    for a in node[1:]:
        if not callable(f):
            raise Unknown('apply non-function')
        f = f(ev(a, env, world))
    return f


# ------------------------------------------------------------------ engine output

def engine_lines(binary, std_dir, path):
    env = dict(os.environ, LIN_STD_DIR=std_dir,
               LIN_STD=os.path.join(std_dir, 'std.lin'))
    out = subprocess.run([binary, path], capture_output=True, text=True,
                         env=env, timeout=600).stdout
    lines = []
    for line in out.splitlines():
        line = line.strip()
        if line.startswith('=> '):
            lines.append(line[3:].strip())
        elif line.startswith('error'):
            lines.append(line)
    return lines


def as_bool(text):
    """Normalize either readback rendering of a Church boolean."""
    t = re.sub(r'\s+', '', text)
    if t in ('true', r'(\t(\ft))'):
        return True
    if t in ('false', r'(\t(\ff))'):
        return False
    return None


def check_file(binary, std_dir, path):
    world = World(std_dir)
    world.load(path)
    src = open(path).read()
    cur_dir = os.path.dirname(os.path.realpath(path))
    for form in parse_all(tokenize(src)):             # resolve this file's loads
        if form and form[0] == 'load':
            world.load(world.resolve(form[1].strip('"'), cur_dir))

    outputs, ns = [], ''
    for form in parse_all(tokenize(src)):
        if not form:
            continue
        # A directive is a *symbol* head; anything else (including a head that is
        # itself an application, like `((or x1) (not x1))`) is read back by the
        # engine and must be counted, or the lines go out of step.
        if isinstance(form[0], str):
            if form[0] == 'namespace':
                ns = '' if form[1] in ('_', 'root') else form[1]
                continue
            if form[0] in DIRECTIVES:
                continue
        outputs.append(form)

    got = engine_lines(binary, std_dir, path)
    checked = unevaluable = non_bool = bad = 0
    for i, form in enumerate(outputs):
        try:
            val = truth(ev(form, {}, world))
        except (Unknown, RecursionError):
            unevaluable += 1                      # lost coverage: reported and failed
            print(f'  {path}: expression {i + 1}: not modelled by the oracle: '
                  f'{" ".join(str(x) for x in form)[:48]}')
            continue
        if val is None:
            non_bool += 1                         # e.g. a model read back as a pair
            continue
        if i >= len(got):
            print(f'  {path}: expression {i + 1}: engine produced no output line')
            bad += 1
            continue
        eng = as_bool(got[i])
        if eng is None:
            non_bool += 1
            continue
        if eng != val:
            print(f'  {path}: expression {i + 1}: engine says {eng}, '
                  f'independent evaluation says {val}')
            bad += 1
        else:
            checked += 1
    print(f'  {os.path.basename(path)}: {checked} checked, {non_bool} non-boolean, '
          f'{unevaluable} unevaluable, {bad} mismatched')
    return checked, bad, unevaluable


def main():
    if len(sys.argv) < 4:
        print(__doc__)
        return 2
    binary, std_dir, files = sys.argv[1], sys.argv[2], sys.argv[3:]
    total_checked = total_bad = total_unevaluable = 0
    for path in files:
        c, b, u = check_file(binary, std_dir, path)
        total_checked += c
        total_bad += b
        total_unevaluable += u
    # A file whose vocabulary stops being modelled must not silently pass.
    if total_checked < 3 * len(files):
        print(f'soundness_enum: only {total_checked} expressions checked across '
              f'{len(files)} files; the oracle has lost coverage')
        return 1
    if total_bad:
        print(f'soundness_enum: {total_bad} mismatch(es) -- engine disagrees with '
              f'the independent evaluation')
        return 1
    if total_unevaluable:
        print(f'soundness_enum: {total_unevaluable} expression(s) the oracle can no '
              f'longer evaluate -- restore its vocabulary rather than dropping them')
        return 1
    print(f'soundness_enum: OK ({total_checked} independent evaluations agree)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
