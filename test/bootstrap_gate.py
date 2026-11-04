#!/usr/bin/env python3
"""The bootstrap's engine gate, as an executable matrix.

Every case below is a shape the self-hosted front end needs.  A case PASSES when the C
engine answers what plain lambda calculus says it must.  Today most of the FFI cases fail,
which is why `test/parity.py` is still 0/53: a boot compiler written in Lin cannot classify
a character until these hold.

  python3 test/bootstrap_gate.py [--bin ./lin] [--verbose]

Exit 0 when every case passes.  This is NOT in run_tests.sh: it is the gate to WATCH until
it is green, not a suite that should fail the tree.

Why each family exists (all measured, see docs/NEXT-AGENT-BOOTSTRAP.md):

  fold/nonrec      control: an `_op` fold fires when the body is not recursive
  fold/rec         the `_op` fold DECLINES in a recursive body; the answer still comes out
                   right through num.lin's pure `_peq` fallback (so these pass, but at
                   ~1,100 firings per unfolding)
  ffi/value        an FFI call in a recursive body works when the call value is only a
                   THUNK (branch value, or compared outside the definition)
  ffi/operand      an FFI call feeding `_op` operands must fold inside the recursion: the
                   `_op` fold has a fallback, `_ffi` has none, so today these are garbage
  ffi/cond         an FFI BOOLEAN as a condition must fold: today the envelope is beta'd
                   against the branch thunk and the answer is 108

A fix is only done when the whole matrix is green AND `LIN_BIN=./lin test/run_tests.sh`
still reports 71/72 (line budget only) AND `python3 test/parity.py` improves.
"""

import argparse
import os
import subprocess
import sys
import tempfile

PRELUDE = '(load "std/text.lin")\n'

# (name, family, source, expected last stdout token)
CASES = [
    ("op fold, top level", "fold/nonrec",
     '(io_print (if (eq 1 1) 7 0) (io_print "\\n" 0))\n', "7"),
    ("op fold, non-recursive def", "fold/nonrec",
     '(define! e0 (list num -> num -> num) (\\s (\\i (if (eq i 1) 7 0))))\n'
     '(io_print (e0 (cons 1 nil) 1) (io_print "\\n" 0))\n', "7"),
    ("op fold, non-recursive def, param used twice", "fold/nonrec",
     '(define! h1 (num -> num) (\\x (if (eq x x) 7 0)))\n'
     '(io_print (h1 1) (io_print "\\n" 0))\n', "7"),
    ("op fallback, recursive body (must not regress)", "fold/rec",
     '(define! rc (num -> num) (\\n (if (eq n 0) 7 (rc (sub n 1)))))\n'
     '(io_print (rc 3) (io_print "\\n" 0))\n', "7"),
    ("list recursion, pure Lin", "fold/rec",
     '(define! q1 (list num -> num -> num) (\\s (\\i (if (is_empty s) 0 (if (eq i 1) 7 '
     '(q1 (list.tail s) (add i 1)))))))\n'
     '(io_print (q1 (cons 1 (cons 2 (cons 3 nil))) 0) (io_print "\\n" 0))\n', "7"),
    ("ffi value in a branch, recursive", "ffi/value",
     '(define! g4 (list num -> num -> num) (\\s (\\i (if (eq i 0) (tlen s) (g4 s (add i 1))))))\n'
     '(io_print (g4 "abcd" 0) (io_print "\\n" 0))\n', "4"),
    ("ffi value compared outside the def", "ffi/value",
     '(define! g7 (list num -> num -> num) (\\s (\\i (if (eq i 0) (tget s 0) (g7 s (add i 1))))))\n'
     '(io_print (if (eq (g7 "abcd" 0) 97) 7 0) (io_print "\\n" 0))\n', "7"),
    ("ffi number feeding eq, recursive", "ffi/operand",
     '(define! g5 (list num -> num -> num) (\\s (\\i (if (eq (tget s i) 97) 7 (g5 s (add i 1))))))\n'
     '(io_print (g5 "abcd" 0) (io_print "\\n" 0))\n', "7"),
    ("ffi number feeding eq via let, recursive", "ffi/operand",
     '(define! r2 (list num -> num -> num) (\\s (\\i (let ((c (tget s i))) '
     '(if (eq c 97) 7 (r2 s (add i 1)))))))\n'
     '(io_print (r2 "abcd" 0) (io_print "\\n" 0))\n', "7"),
    ("ffi number feeding eq, non-recursive (control)", "ffi/operand",
     '(define! r4 (list num -> num -> num) (\\s (\\i (if (eq (tget s i) 97) 7 0))))\n'
     '(io_print (r4 "abcd" 0) (io_print "\\n" 0))\n', "7"),
    ("ffi boolean as a condition, recursive", "ffi/cond",
     '(define! d1 (list num -> num -> num) (\\s (\\i (if (tbend s i) 9 (d1 s (add i 1))))))\n'
     '(io_print (d1 "abc" 0) (io_print "\\n" 0))\n', "9"),
    ("ffi boolean via let, recursive", "ffi/cond",
     '(define! r1 (list num -> num -> num) (\\s (\\i (let ((e (tbend s i))) '
     '(if e 7 (r1 s (add i 1)))))))\n'
     '(io_print (r1 "abc" 2) (io_print "\\n" 0))\n', "7"),
    ("ffi boolean as a condition, non-recursive (control)", "ffi/cond",
     '(define! d2 (list num -> num -> num) (\\s (\\i (if (tbend s i) 9 0))))\n'
     '(io_print (d2 "abc" 3) (io_print "\\n" 0))\n', "9"),
]


def last_number(text):
    toks = [t for t in text.replace("=>", " ").split() if t.strip()]
    return toks[-1] if toks else ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", default=os.environ.get("LIN_BIN", "./lin"))
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()
    if not os.path.exists(a.bin):
        print(f"error: no binary at {a.bin}", file=sys.stderr)
        return 2
    fam = {}
    failed = 0
    with tempfile.TemporaryDirectory() as td:
        for i, (name, family, src, want) in enumerate(CASES):
            path = os.path.join(td, f"case{i}.lin")
            with open(path, "w") as fh:
                fh.write(PRELUDE + src)
            try:
                p = subprocess.run([a.bin, path], capture_output=True, text=True,
                                   timeout=a.timeout)
                got, err, rc = last_number(p.stdout), p.stderr, p.returncode
            except subprocess.TimeoutExpired:
                got, err, rc = "<timeout>", "", -1
            ok = got == want
            fam.setdefault(family, [0, 0])[0 if ok else 1] += 1
            if not ok:
                failed += 1
            print(f"{'PASS' if ok else 'FAIL'}  {family:14s} {name:52s} "
                  f"want {want:>4s} got {got:>9s}")
            if a.verbose and not ok:
                print("      stderr:", (err or "").strip().splitlines()[-1:] or "(none)")
    print("-" * 78)
    for k in sorted(fam):
        p_, f_ = fam[k]
        print(f"  {k:14s} {p_}/{p_ + f_}")
    total = len(CASES)
    print(f"{total - failed}/{total} gate cases pass")
    return 0 if failed == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
