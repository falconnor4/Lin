#!/usr/bin/env python3
r"""AOT/interpreter equivalence: a `.line` artifact must print what the interpreter prints.

`lin build` runs a different pipeline from `lin` -- expand -> e-graph optimize -> compile ->
build-time reduce -> compact -> serialize -- and the container tier only ever asserted one
hard-coded string for two programs, so a whole class of AOT-only miscompiles was invisible.

The class was real.  The e-graph pass's beta rule substituted the argument under binders
without checking for capture, so

    ((\y (((\x (\y x)) y) 5)) 99)

-- which the interpreter answers 99 -- was rewritten to `(\y y)` by the pass, extraction
preferred that form (cost 3 against 9), and the DEFAULT AOT candidate baked an artifact that
printed 5.  Nothing in the suite noticed: the interpreter path never calls the optimizer at
all, so only `lin build` could see it.

Every case below is checked twice, against the interpreter's own answer and against the artifact
the compiler ships -- both the default candidate and whatever `LIN_AOT_SEARCH` selects, because a
candidate can trade correctness for bytes (the table in src/main.c records one that made
`(fact 3)` return 0).  The expectations were derived by hand from lambda calculus rather than
copied from the engine.

Every case is SCALAR-valued on purpose.  Lin renders a variable occurrence by the name stored on
the binder it is wired to, so a shadowed binder prints as its own name and the text can denote a
different term than the value:

    (\y ((\x (\y x)) y))     value  \y.\y'.y  (constant)      prints  (\y (\y y))
    ((\y ((\x (\y x)) y)) 42 7)  =>  42          -- the value is right
    ((\y (\y y)) 42 7)           =>   7          -- but the printed text is not that term

That is a real round-trip limitation of the printer (finding 3 in the audit that produced this
file), and it is left alone here deliberately: a faithful fix has to rename a shadowing binder
only when the OUTER binder is actually referenced inside it, or it rewrites the 39 lambda-shaped
`; expect` strings across the corpus, all of which denote exactly what they print.  Pinning such
cases textually would assert the ambiguity instead of catching it, so the shadowing semantics are
pinned by APPLYING the result (cases 5-6): a captured argument changes a constant into the
identity, and the extra application is what makes the two distinguishable.

usage: aot_equiv.py <lin-binary> <std-dir>
"""

import os
import re
import subprocess
import sys
import tempfile

# (expression, expected readback).  Scalar-valued; derived by hand.  See the module docstring.
CASES = [
    # -- capture: the argument's free variable must not be captured by a binder in the body
    (r'((\y (((\x (\y x)) y) 5)) 99)', '=> 99'),
    (r'(let ((y 99)) (((\x (\y x)) y) 5))', '=> 99'),
    (r'((\y (((\x (\z x)) y) 5)) 99)', '=> 99'),          # renamed inner binder: same answer
    (r'((\y (((\x (\x x)) y) 5)) 99)', '=> 5'),           # inner \x shadows, so 5 is right
    # -- the shadowed-OUTER-reference shape, made observable by applying the result:
    #    a captured argument would turn each constant into the identity and yield 7 / 3.
    (r'(((\y ((\x (\y x)) y)) 42) 7)', '=> 42'),
    (r'((((\y ((\x (\y (\x y))) y)) 42) 7) 3)', '=> 7'),
    # -- beta / projection / shared function
    (r'((\x (\y x)) 10 20)', '=> 10'),
    (r'((\x 99) 123)', '=> 99'),
    (r'((\f (\x (f (f x)))) (\z (add z 1)) 0)', '=> 2'),
    (r'((\x (\y (\z x))) 1 2 3)', '=> 1'),
    (r'(let ((k (\x (\y x)))) ((k 7) 8))', '=> 7'),
    (r'(fst (pair 42 100))', '=> 42'),
    (r'((\y (((\y (\x y)) y) 5)) 99)', '=> 99'),          # inner \y shadows, arg is the outer one
    # -- float values.  A float box is a Scott numeral INDEXING a double table, and the container
    #    did not carry that table, so EVERY float-valued artifact was wrong: `2.0` and `144.0`
    #    built byte-identical files, readback fell back to printing the raw `_ffs` spine, and if
    #    the runtime had compiled a different float first the artifact printed THAT number.  These
    #    cases are the whole coverage this path ever had (the .line tier is integer-only, and
    #    `(float "...")` was the only spelling that happened to work, which is why it hid).
    (r'2.0', '=> 2'),
    (r'144.0', '=> 144'),                                  # the two that used to collide
    (r'(fmul 2.0 3.0)', '=> 6'),
    (r'(fadd 2.5 3.5)', '=> 6'),
    (r'(fsub 1.5 2.0)', '=> -0.5'),                        # sign distinguishes a stale table
    (r'(fsqrt 144.0)', '=> 12'),
    (r'(rad2deg pi)', '=> 180'),                           # pi is a precompiled float define: spliced
    (r'(let ((x 3.5)) (fmul x 2.0))', '=> 7'),
]


def run(argv, timeout, env):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, env=env)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -9, '', 'TIMEOUT'


def main():
    if len(sys.argv) < 3:
        print(__doc__.strip().splitlines()[-1])
        return 2
    lin, std_dir = sys.argv[1], sys.argv[2]
    env = dict(os.environ, LIN_STD=os.path.join(std_dir, 'std.lin'), LIN_STD_DIR=std_dir)
    lin_abs = os.path.abspath(lin)
    tmp = tempfile.mkdtemp()
    bad, fires, declines, chosen = 0, 0, 0, 0
    for i, (expr, want) in enumerate(CASES):
        src, art = os.path.join(tmp, 'c%d.lin' % i), os.path.join(tmp, 'c%d.line' % i)
        with open(src, 'w') as fh:
            fh.write(expr + '\n')
        rc, out, _ = run([lin_abs, src], 60, env)
        got = out.strip()
        if rc != 0 or got != want:
            print('FAIL %s\n  interpreter: want %r got %r (rc=%d)' % (expr, want, got, rc))
            bad += 1
            continue
        # LIN_PASSES reports what the optimizer did, so the run also proves the pass was
        # actually exercised rather than skipped (a vacuous pass would pass every case).
        brc, _, berr = run([lin_abs, 'build', src, '-o', art], 180, dict(env, LIN_PASSES='1'))
        if brc != 0 or not os.path.exists(art):
            print('FAIL %s\n  lin build failed (rc=%d)' % (expr, brc))
            bad += 1
            continue
        for m in re.finditer(r'beta=on/(\d+)(?:\(\+(\d+) capture-declined\))?', berr):
            fires += int(m.group(1))
            declines += int(m.group(2) or 0)
        rc, out, _ = run([art], 60, env)
        got = out.strip()
        if rc != 0 or got != want:
            print('FAIL %s\n  artifact:    want %r got %r (rc=%d)' % (expr, want, got, rc))
            bad += 1
            continue
        # LIN_AOT_SEARCH explores the candidate table in src/main.c and SHIPS the winner, and a
        # candidate can trade correctness for bytes -- the table's own comment records one that
        # made `(fact 3)` return 0.  Whatever the search picks has to be right too.
        src2, art2 = os.path.join(tmp, 'c%d.lin' % i), os.path.join(tmp, 'c%d.search.line' % i)
        with open(src2, 'w') as fh:
            fh.write(expr + '\n')
        brc, _, berr = run([lin_abs, 'build', src2, '-o', art2], 300,
                           dict(env, LIN_AOT_SEARCH='1', LIN_PASSES='1'))
        if brc != 0 or not os.path.exists(art2):
            print('FAIL %s\n  lin build (search) failed (rc=%d)' % (expr, brc))
            bad += 1
            continue
        if 'chosen' in berr:
            chosen += 1
        rc, out, _ = run([art2], 60, env)
        got = out.strip()
        if rc != 0 or got != want:
            print('FAIL %s\n  search artifact: want %r got %r (rc=%d)' % (expr, want, got, rc))
            bad += 1
    if bad:
        print('aot_equiv: %d case(s) where the artifact disagrees with the interpreter' % bad)
        return 1
    if fires < 1:
        print('aot_equiv: the e-graph pass fired no rule on any case -- it is no longer '
              'exercised, so these cases no longer test the AOT optimizer')
        return 1
    # The pass also has to PAY OFF, not merely run.  LIN_AOT_SEARCH=1 is the only way to turn it
    # off: aot_apply_cand calls unsetenv("LIN_NO_EGRAPH") for the default candidate, so setting
    # that variable in the environment measures nothing (both candidates come out byte-identical).
    root = os.path.dirname(os.path.abspath(std_dir))
    eg = os.path.join(root, 'test', 'egraph.lin')
    payoff = ''
    if os.path.exists(eg):
        rc, _, err = run([lin, 'build', eg, '-o', os.path.join(tmp, 'payoff.line')], 300,
                         dict(env, LIN_AOT_SEARCH='1', LIN_PASSES='1'))
        nodes = {}
        for m in re.finditer(r'candidate (\S+)\s+artifact=\d+ B.*?compile=(\d+) nodes', err):
            nodes[m.group(1)] = int(m.group(2))
        if 'default' not in nodes or 'no-egraph' not in nodes:
            print('FAIL could not read both candidates\' node counts from the build (%r)' % (nodes,))
            return 1
        if nodes['default'] >= nodes['no-egraph']:
            print('FAIL the e-graph pass no longer pays off on test/egraph.lin: %d compiled nodes '
                  'with the rules vs %d without them' % (nodes['default'], nodes['no-egraph']))
            return 1
        payoff = '; pays off %d -> %d nodes on test/egraph.lin' % (nodes['no-egraph'], nodes['default'])
    print('aot_equiv: OK (%d cases x {default, AOT-search}; e-graph fired %d time(s), declined %d '
          'capture-risk rewrite(s), %d searched builds%s)'
          % (len(CASES), fires, declines, chosen, payoff))
    return 0


if __name__ == '__main__':
    sys.exit(main())
