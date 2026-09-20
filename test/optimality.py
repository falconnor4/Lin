#!/usr/bin/env python3
r"""Lévy-optimality regression test: a fan-shared redex is reduced ONCE, whatever its cost.

The claim "shared subcomputations are evaluated at most once" is the whole point of the engine,
and nothing in the suite tested it.  What the suite tested was *values* -- and a value-based test
cannot see the difference: an engine that re-reduces a shared redex once per use still returns the
right answer, just slower.  This test measures the defect instead of the answer.

The instrument is a redex T with a LONG reduction and a SMALL value, used m times:

    shared   ((\x BODY_m) T)     -- T reaches its uses through the binder's fan
    copies   BODY_m[T]           -- m textual copies of T, so m independent reductions

`(czero? (cmul c5 c5))` and `(czero? (cmul c5 (cmul c5 c5)))` are two such redexes whose reduction
costs differ but whose values are both the 2-node boolean `false`, so the cost of *copying* the
value is the same for both and cancels out.  T_small/T_big being genuinely different costs is
confirmed first, by the m=1 row.

Two redexes let the test be robust to constant offsets: instead of asserting absolute step counts
(which move with any driver or scheduler change) it asserts that the COST DIFFERENCE between them
behaves correctly:

  * shared: for a fan-shared T the difference `steps(T_big) - steps(T_small)` must be the SAME at
    m=1, 2 and 4.  If T were re-reduced per use, the difference would be paid again for every use.
  * copies: with m textual copies the same difference must GROW with m -- that is the control that
    proves the test can detect re-reduction at all.

Measured (the numbers this test was written against):

    shared  m=1  56/81   m=2  66/91   m=4  86/111    difference 25, 25, 25   <- constant
    copies  m=2 111/161  m=4 223/323                 difference 50, 100      <- grows with m

The second half pins the scaling claim on a doubly-exponential value: `sq^k c2` reduces in
15/32/55/90 steps for values 4/16/256/65536 -- the reduction grows about 6x while the value grows
16384x.  Forcing the value with `count` is what makes the numbers exact; the readback of a shared
normal form prints `?` (a separate, known printer limitation), so those lines assert `count`.

usage: optimality.py <lin-binary> <std-dir>
"""

import os
import re
import subprocess
import sys
import tempfile

HEAD = r"""(define c5 (\f (\x (f (f (f (f (f x))))))))
(define c2 (\f (\x (f (f x)))))
(define cmul (\a (\b (\f (a (b f))))))
(define csq (\x (cmul x x)))
(define czero? (\n (n (\_ false) true)))
(define ts (czero? (cmul c5 c5)))
(define tb (czero? (cmul c5 (cmul c5 c5))))
(define body1 (\x (if x 1 0)))
(define body2 (\x (pair (if x 1 0) (if x 1 0))))
(define body4 (\x (pair (if x 1 0) (pair (if x 1 0) (pair (if x 1 0) (if x 1 0))))))
"""


def cases():
    """(label, kind, m, size, expression) in the order the assertions index them."""
    out, ts, tb, bodies = [], "(czero? (cmul c5 c5))", "(czero? (cmul c5 (cmul c5 c5)))", {1: "body1", 2: "body2", 4: "body4"}
    for m in (1, 2, 4):
        for name, t in (("small", ts), ("big", tb)):
            out.append(("shared", "shared", m, name, "((%s) %s)" % (bodies[m], t)))
    for m in (2, 4):
        for name, t in (("small", ts), ("big", tb)):
            body = " ".join("(if %s 1 0)" % t for _ in range(m))
            if m == 2:
                expr = "(pair %s %s)" % tuple(["(if %s 1 0)" % t] * 2)
            else:
                expr = ("(pair (if %s 1 0) (pair (if %s 1 0) (pair (if %s 1 0) (if %s 1 0))))"
                        % ((t,) * 4))
            out.append(("copies", "copies", m, name, expr))
    return out


def run(argv, timeout=300):
    p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                       stdin=subprocess.DEVNULL)
    return p.returncode, p.stdout, p.stderr


def main():
    if len(sys.argv) < 3:
        print(__doc__.strip().splitlines()[-1])
        return 2
    lin, std_dir = os.path.abspath(sys.argv[1]), sys.argv[2]
    env = dict(os.environ, LIN_STD=os.path.join(std_dir, "std.lin"), LIN_STD_DIR=std_dir)
    tmp = tempfile.mkdtemp()
    cs = cases()
    prog = os.path.join(tmp, "opt.lin")
    with open(prog, "w") as fh:
        fh.write(HEAD + "\n".join(c[4] for c in cs) + "\n")

    # Values come from a plain run (stdout) and step counts from a bench run -- where the counts go
    # to STDERR while the values still go to stdout.  Both are emitted in expression order, so they
    # pair by index rather than by line.
    rc, out, err = run([lin, prog])
    if rc != 0:
        print("optimality: the program failed to run: %s" % (err.strip() or rc))
        return 1
    vals = [l[3:] for l in out.split("\n") if l.startswith("=> ")]
    rc, bout, berr = run([lin, "-b", prog])
    steps = [int(m.group(1)) for m in re.finditer(r"(\d+) steps", berr)]
    if len(vals) != len(cs) or len(steps) != len(cs):
        print("optimality: expected %d results, got %d values / %d step counts" %
              (len(cs), len(vals), len(steps)))
        return 1

    ix = {(c[1], c[2], c[3]): i for i, c in enumerate(cs)}
    bad = []

    def diff(kind, m):
        return steps[ix[(kind, m, "big")]] - steps[ix[(kind, m, "small")]]

    # The premise: the two redexes really do have different costs, or the differences below are 0
    # and every later assertion is vacuous.
    if diff("shared", 1) <= 0:
        bad.append("the two redexes cost the same (%d); the cost-difference probe is vacuous"
                   % diff("shared", 1))

    # 1. a fan-shared redex is reduced once: its cost difference does not depend on the use count
    for m in (2, 4):
        if diff("shared", m) != diff("shared", 1):
            bad.append("shared T at m=%d pays its cost difference again (%d) instead of %d -- the "
                       "shared redex is being re-reduced" % (m, diff("shared", m), diff("shared", 1)))

    # 2. the control: textual copies DO pay it per copy, so the probe above can detect it
    if not diff("copies", 4) > diff("copies", 2) > diff("shared", 2):
        bad.append("textual copies do not re-reduce (diffs %d, %d for m=2,4) -- the control is "
                   "broken, so assertion 1 proves nothing" % (diff("copies", 2), diff("copies", 4)))

    # 3. sharing actually saves work
    for m in (2, 4):
        if not steps[ix[("shared", m, "big")]] < steps[ix[("copies", m, "big")]]:
            bad.append("sharing did not beat copying at m=%d (%d vs %d steps)" %
                       (m, steps[ix[("shared", m, "big")]], steps[ix[("copies", m, "big")]]))

    # 4. and it agrees with the copy: sharing must not change the answer
    for m in (2, 4):
        if vals[ix[("shared", m, "small")]] != vals[ix[("copies", m, "small")]] or \
           vals[ix[("shared", m, "big")]] != vals[ix[("copies", m, "big")]]:
            bad.append("shared and copied forms disagree at m=%d: %r vs %r" %
                       (m, vals[ix[("shared", m, "big")]], vals[ix[("copies", m, "big")]]))

    # 5. scaling: a doubly-exponential value reduces in a handful of times the steps of a small one
    sq = os.path.join(tmp, "sq.lin")
    with open(sq, "w") as fh:
        fh.write(HEAD + "\n".join(
            ["(csq c2)", "(csq (csq c2))", "(csq (csq (csq c2)))", "(csq (csq (csq (csq c2))))",
             "(count (csq c2))", "(count (csq (csq c2)))", "(count (csq (csq (csq c2))))",
             "(count (csq (csq (csq (csq c2)))))"]) + "\n")
    rc, sout, _ = run([lin, sq])
    svals = [l[3:] for l in sout.split("\n") if l.startswith("=> ")]
    rc, sbout, sberr = run([lin, "-b", sq])
    ssteps = [int(m.group(1)) for m in re.finditer(r"(\d+) steps", sberr)]
    if len(svals) != 8 or len(ssteps) != 8:
        bad.append("scaling program produced %d values / %d step counts, want 8 each" %
                   (len(svals), len(ssteps)))
    else:
        want = ["4", "16", "256", "65536"]
        if svals[4:] != want:
            bad.append("forced Church values are %r, want %r -- the shared normal forms do not "
                       "denote the numbers claimed" % (svals[4:], want))
        unfold, fold = ssteps[:4], ssteps[4:]
        if not unfold[3] <= 10 * unfold[0]:
            bad.append("reduction steps grew %dx for a 16384x value (%r) -- the reduction is "
                       "growing with the value, not with the term" % (unfold[3] // max(unfold[0], 1), unfold))
        if not fold[3] > unfold[3]:
            bad.append("forcing the value with `count` did not cost more than the bare normal form "
                       "(%r vs %r); the readback accounting is suspicious" % (fold[3], unfold[3]))

    # 6. readback must never mislead silently.
    #    A shared normal form cannot always be written as a tree, and a readback that ends on a
    #    discarded node is not a value at all.  The invariant below survives a future
    #    sharing-preserving readback, which would simply stop emitting the marks: IF stdout carries
    #    a mark, stderr must say what it means.  What must never happen -- and did, for both cases
    #    -- is a mark reaching stdout alone with exit status 0, looking like the answer.
    rb = os.path.join(tmp, "rb.lin")
    with open(rb, "w") as fh:
        fh.write(HEAD + "(cmul c2 c2)\n" + "((\\x (x x)) c2)\n" + "(count (cmul c2 c2))\n")
    rc, rvals, rerr = run([lin, rb])
    lines = [l for l in rvals.split("\n") if l.startswith("=> ")]
    if len(lines) != 3:
        bad.append("readback probe produced %d results, want 3" % len(lines))
    else:
        shared, lost, forced = lines[0], lines[1], lines[2]
        if "?" in shared and "shared normal form" not in rerr:
            bad.append("a '?'-bearing readback (%r) was printed without saying what the marker "
                       "means" % shared)
        if "?" not in shared and "shared normal form" in rerr:
            bad.append("stderr claims a shared-normal-form note for a clean readback (%r)" % shared)
        if "_" in lost and "not a value" not in rerr:
            bad.append("a discarded-node readback (%r) was printed without reporting that the "
                       "result is not a value" % lost)
        if forced != "=> 4":
            bad.append("forcing the shared product gave %r, want '=> 4'" % forced)

    if bad:
        for b in bad:
            print("FAIL " + b)
        print("optimality: %d problem(s)" % len(bad))
        return 1
    print("optimality: OK (shared cost difference %d at m=1/2/4; copies %d/%d; sq steps %s for "
          "values 4/16/256/65536)" % (diff("shared", 1), diff("copies", 2), diff("copies", 4),
                                      "/".join(str(s) for s in ssteps[:4])))
    return 0


if __name__ == "__main__":
    sys.exit(main())
