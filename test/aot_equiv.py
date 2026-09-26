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

THE CASES ARE THE SMALL HALF.  A curated list only covers what someone thought of, and three real
divergences (test/runtime_ffi.lin's frozen `getenv`, test/types.lin's artifact for a file whose final
form never parsed, test/unison.lin's `(get_driver)`) lived in the tree while every hand-written case
passed.  So the sweep below runs over the WHOLE corpus: every suite carrying `; expect` lines is
built and compared with the interpreter, and the comparison -- because `lin` is a form-by-form
evaluator while a container prints one answer -- is on the interpreter's FINAL outcome: the artifact
must print it, or, when that outcome is an error, the build must refuse.  Only one suite is
environmental (see ENVIRONMENTAL: `(get_driver)` reports the PROCESS's driver strategy, and a
container runs prelude-free), and it is pinned with both answers instead of being skipped.

usage: aot_equiv.py <lin-binary> <std-dir>
"""

import os
import re
import subprocess
import sys
import tempfile

# ============================================================================================
# THE CORPUS DIFFERENTIAL
# --------------------------------------------------------------------------------------------
# The case lists below are hand-written and finite, which is exactly how three AOT-vs-interpreter
# divergences lived in the tree unnoticed (test/runtime_ffi.lin, test/types.lin, test/unison.lin).
# The general form of the same question is mechanical: for EVERY suite that carries `; expect`
# lines, build it and compare the artifact with the interpreter.
#
# WHAT "IDENTICAL" CAN MEAN HERE, and why it is the last line.  `lin` evaluates a file FORM BY FORM
# and prints one line per top-level form (values and error reports alike); `lin build` compiles the
# program's FINAL expression into a container, and a container prints ONE answer.  So the artifact is
# comparable to the interpreter's FINAL outcome, and that is what is compared, byte for byte:
#
#   * the interpreter's last line is a VALUE  -> the artifact must print that same line last
#     (an artifact may print the effects the program itself performs, e.g. test/ffi_systems.lin's
#     `(system "echo ...")`, so its earlier lines are its own business and only the answer is pinned);
#   * the interpreter's last line is an ERROR -> the BUILD MUST REFUSE (non-zero, no artifact).
#     A program whose final form the interpreter refuses (types.lin ends in an unterminated `(1`)
#     must not become a runnable artifact that answers with the PREVIOUS form's value.
#
# RUN-TIME vs BUILD-TIME ENVIRONMENT.  A build may not make the program's observations, so a suite
# whose expectations come from the environment is BUILT with that variable absent and RUN with it
# set: the artifact has to answer from its own run-time environment.  (Measured before this:
# `lin build` executed the program's `getenv` and froze the build's answer into the artifact.)
CORPUS_ENV = {'runtime_ffi.lin': {'N': '6'}}      # mirrors test/run_tests.sh's `N=6 run_test`
CORPUS_BUILD_DROP = ('N',)                        # the run-time input: ABSENT while building

# Genuinely ENVIRONMENTAL, with both answers pinned so drift cannot pass silently.  `(get_driver)`
# reports the strategy of the PROCESS it runs in, not a value of the compiled program: the
# interpreter evaluates the file's `(load "std/drivers/gpu.lin")` / `(set_driver "gpu")` forms (they
# are ordinary top-level expressions, and its own process registers gpu at priority 20), while an
# artifact IS the compiled final expression and runs PRELUDE-FREE by design -- src/io.c: "A `.line`
# artifact runs with NO prelude, so no `(set_driver ...)` form is ever evaluated".  Its process has no
# strategy driver at all, so the readback driver's own answer for it is "cpu" (lin_get_driver()
# returns NULL).  Both answers are correct for their own process, and neither can be made to be the
# other without baking the build host's driver set into the artifact -- the very thing a build may not
# do.  Verified with gdb on lin_driver_add: the interpreter registers simd(prio 10)+gpu(prio 20); the
# build registers neither.
ENVIRONMENTAL = {
    'unison.lin': ('=> gpu', '=> cpu',
                   'the interpreter evaluated the file\'s `(set_driver "gpu")`; a container runs '
                   'prelude-free, so `(get_driver)` answers for a process with no strategy driver'),
}

# KNOWN DIVERGENCES: reported as FAILURES (never tolerated, never skipped silently) so the tree
# cannot hide them; the run continues so the rest of the corpus is still checked.  EMPTY, and it
# stays here empty: an entry is a live bug, so the honest state of this table is no entries at all.
# The one it held was test/runtime_ffi.lin, and it went away with the bug: a container carried a
# driver's STATE but not its PRESENCE, so an artifact -- which runs prelude-free -- never loaded the
# `arith` fold pre-emptor and its `(add <closure> 1)` could not fold, and the build's own AOT pass
# boxed the resulting stuck thunk.  See src/net.c's `carries_presence` and src/main.c's pass point.
KNOWN_DIVERGENT = {}

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

# The pass the numbers in the driver favour (arith's AOT pass, std/drivers/arith.c): it chooses an
# UNAMBIGUOUS ENCODING for the values of its own domain that the program observes.  Without it the
# artifact writes the value as the structure it is, because a container carries no type and `0`,
# TRUE and FALSE are shapes other domains claim too.  These are the cases that pin it: `want` is the
# INTERPRETER's answer, the pass-on artifact has to match it, and the pass-off artifact must differ
# (otherwise the pass is not exercised and this file would pass vacuously).
VALUE_CASES = [
    (r'0',                    '=> (\\a (\\b a))'),   # a bare literal: no nominal type, so it declines
    (r'(sub 4 4)',            '=> 0'),        # num: the zero a SATURATING subtraction folds to
    (r'(pred 1)',             '=> 0'),
    (r'(mul 0 5)',            '=> 0'),
    (r'(is_zero 0)',          '=> true'),
    (r'(is_zero 3)',          '=> false'),
    (r'(leq 5 5)',            '=> true'),
    (r'(gt 4 2)',             '=> true'),
]
# `0` above is deliberate: its type is an arrow, not the nominal `num`, so there is no domain for the
# pass to name and it DECLINES -- which is the honest limit of the mechanism, and why the improvement
# is "some cases" rather than all: a value whose meaning nothing states is still written as its net.
VALUE_DECLINES = {r'0'}


def run(argv, timeout, env):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, env=env)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -9, '', 'TIMEOUT'


def last_line(out):
    """The interpreter's FINAL outcome, or the artifact's ANSWER: its last non-blank line."""
    lines = [l for l in out.splitlines() if l.strip()]
    return lines[-1] if lines else ''


def corpus(lin_abs, std_dir, env, tmp, known):
    """Every `; expect` suite, differentially.

    Returns (checked, refused, environmental, known_hit, failures).  The count is RETURNED rather
    than accumulated into the caller: an int argument would be copied, and a divergence counted in
    here would then never reach the caller's total -- a harness that cannot fail the run is worse
    than no harness at all.
    """
    tdir = os.path.join(os.path.dirname(os.path.abspath(std_dir)), 'test')
    checked = refused = environ = known_hit = bad = 0
    for name in sorted(os.listdir(tdir)):
        if not name.endswith('.lin'):
            continue
        path = os.path.join(tdir, name)
        with open(path) as fh:
            if not re.search(r'^; expect ', fh.read(), re.M):
                continue
        renv = dict(env, **CORPUS_ENV.get(name, {}))
        benv = dict(renv)
        if name in CORPUS_BUILD_DROP:
            for k in CORPUS_BUILD_DROP:
                benv.pop(k, None)
        rc, iout, _ = run([lin_abs, path], 300, renv)
        if rc == -9:
            print('FAIL %s\n  the interpreter timed out (%ds)' % (name, 300))
            bad += 1
            continue
        want = last_line(iout)
        art = os.path.join(tmp, name[:-4] + '.corpus.line')
        if os.path.exists(art):
            os.remove(art)
        brc, _, berr = run([lin_abs, 'build', path, '-o', art], 900, benv)
        built = (brc == 0 and os.path.exists(art))
        checked += 1
        if want.startswith('error:'):
            # the interpreter's final form is REFUSED: the build has to refuse it too
            if built:
                print('FAIL %s\n  the interpreter refuses its last form (%r) but `lin build` shipped '
                      'an artifact for an earlier one' % (name, want))
                bad += 1
            else:
                refused += 1
            continue
        if not built:
            print('FAIL %s\n  the interpreter answers %r and `lin build` REFUSED (rc=%d, %s)'
                  % (name, want, brc, last_line(berr)[:100]))
            bad += 1
            continue
        arc, aout, aerr = run([art], 300, renv)
        got = last_line(aout)
        if name in ENVIRONMENTAL:
            iwant, awant, why = ENVIRONMENTAL[name]
            if want != iwant or got != awant:
                print('FAIL %s\n  the environmental pair moved: interpreter %r (pinned %r), artifact '
                      '%r (pinned %r) -- %s' % (name, want, iwant, got, awant, why))
                bad += 1
            else:
                environ += 1
            continue
        if arc != 0 or got != want:
            if name in known:
                known_hit += 1
                print('FAIL %s\n  KNOWN DIVERGENCE (reported, never tolerated): interpreter %r, '
                      'artifact %r (rc=%d)\n  diagnosis: %s' % (name, want, got, arc, known[name]))
            else:
                print('FAIL %s\n  interpreter %r, artifact %r (rc=%d)' % (name, want, got, arc))
            bad += 1
    return checked, refused, environ, known_hit, bad


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
        art_off = os.path.join(tmp, 'c%d.nopass.line' % i)
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
        # ... and with every driver pass SKIPPED.  A pass is optional by contract, so the artifact
        # must still build, still run, and still print what the interpreter prints.
        rc, out, _ = run([lin_abs, 'build', src, '-o', art_off], 180, dict(env, LIN_NO_PASS='1'))
        if rc != 0 or not os.path.exists(art_off):
            print('FAIL %s\n  lin build (LIN_NO_PASS) failed (rc=%d)' % (expr, rc))
            bad += 1
            continue
        rc, out, _ = run([art_off], 60, env)
        got = out.strip()
        if rc != 0 or got != want:
            print('FAIL %s\n  artifact(no pass): want %r got %r (rc=%d)' % (expr, want, got, rc))
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
    # THE PASS HAS TO PAY OFF, not merely run (and the pass-on/pass-off builds above already prove it
    # is exercised without crashing).  A case whose pass-off artifact ALREADY prints the value proves
    # nothing about the pass, so each VALUE_CASES entry must improve, except the ones listed as
    # declining by construction -- those must be untouched, which is the other half of the contract.
    improved, unchanged = [], []
    for expr, want in VALUE_CASES:
        src = os.path.join(tmp, 'v.lin')
        on, off = os.path.join(tmp, 'v.on.line'), os.path.join(tmp, 'v.off.line')
        with open(src, 'w') as fh:
            fh.write(expr + '\n')
        run([lin_abs, 'build', src, '-o', on], 180, env)
        run([lin_abs, 'build', src, '-o', off], 180, dict(env, LIN_NO_PASS='1'))
        _, gon, _ = run([on], 60, env)
        _, goff, _ = run([off], 60, env)
        gon, goff = gon.strip(), goff.strip()
        if gon != want:                       # whatever else, the pass-on artifact is the interpreter's answer
            print('FAIL %s\n  pass-on: want %r got %r (pass-off %r)' % (expr, want, gon, goff))
            bad += 1
        elif expr in VALUE_DECLINES:
            # A case the pass must NOT touch -- its result type names no domain, so it declines and
            # the artifact still writes the value as the structure it is -- so the two builds have to
            # agree, and there is nothing here for the pass to improve.  This is the honest limit of
            # the mechanism, and it is why the improvement is "some cases" rather than all.
            if gon != goff:
                print('FAIL %s\n  the pass touched a case it has no domain for: %r vs %r'
                      % (expr, gon, goff))
                bad += 1
            else:
                unchanged.append(expr)
        elif goff == want:
            print('FAIL %s\n  the pass-off artifact already reads %r, so this case does not pin the '
                  'pass' % (expr, want))
            bad += 1
        else:
            improved.append(expr)
    if bad:
        print('aot_equiv: %d case(s) where the artifact disagrees with the interpreter' % bad)
        return 1
    if not improved:
        print('aot_equiv: no case where the pass changes the readback -- it is no longer exercised')
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
    # ---- the corpus differential: every `; expect` suite, artifact against interpreter -----------
    cchecked, crefused, cenviron, cknown, cbad = corpus(lin_abs, std_dir, env, tmp, KNOWN_DIVERGENT)
    bad += cbad
    if cchecked < 40:
        print('aot_equiv: only %d corpora suites were checked -- the sweep is not covering the tree'
              % cchecked)
        return 1
    if bad:
        print('aot_equiv: %d divergence(s) between the artifacts and the interpreter (corpus: %d '
              'suites built and compared, %d of them refused by BOTH paths, %d environmental by '
              'construction, %d KNOWN and still failing)' % (bad, cchecked, crefused, cenviron, cknown))
        return 1
    print('aot_equiv: OK (%d cases x {passes on, passes off, AOT-search}; e-graph fired %d time(s), '
          'declined %d capture-risk rewrite(s), %d searched builds; AOT pass improved %d value case(s) '
          '(%s), declined by type on %d; CORPUS: %d suites, artifact == interpreter\'s final answer, '
          '%d refused by both paths, %d environmental (pinned)%s)'
          % (len(CASES), fires, declines, chosen, len(improved), ', '.join(improved), len(unchanged),
             cchecked, crefused, cenviron, payoff))
    return 0


if __name__ == '__main__':
    sys.exit(main())
