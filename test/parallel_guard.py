#!/usr/bin/env python3
r"""The driver ABI's failure modes must be diagnosed, not silently absorbed.

Two hooks can break the core's invariants, and both used to do so invisibly:

1. `arg_fold` runs inside a parallel wave, where `net_alloc` cannot grow the net (a `realloc` would
   move the tag/wire/scope/name arrays out from under every worker holding raw pointers into them).
   The wave reserves 4 nodes per parallel interaction -- exactly what the core rules use -- but a
   hook's footprint is its own business.  Measured before the guard: an ASan heap-buffer-overflow, a
   SIGSEGV, and `free(): invalid pointer`.

2. `drain` may re-enqueue work without making progress.  `net_reduce` bounds that with a livelock
   guard, but the guard used to drop the active list and `break` with no signal -- and because every
   caller decides "is this a value?" without a normal-form test, a truncated net could be printed as
   the answer and even baked into a `.line`.  Worse, `eval_form` consults the recursion-sentinel
   branch before anything else and `continue`s into another round, so a stall looked like a hang
   (measured: 20 s timeout, no output) instead of an error.

This test compiles deliberately misbehaving drivers from strings into a scratch std tree -- they are
NOT part of the shipped std -- and requires:

  * the over-allocating hook: inert serially (the control that proves the wiring triggers it), and
    DIAGNOSED with 8 threads rather than completing or crashing silently;
  * the non-progressing drain: the run TERMINATES and reports the stall, rather than hanging or
    printing a truncated net as its value.

A compiler is needed to build the probes; where none is found the test SKIPS loudly rather than
passing quietly, so a CI that loses its toolchain is visible.

usage: parallel_guard.py <lin-binary> <std-dir>
"""

import os
import shutil
import subprocess
import sys
import tempfile

PROLOGUE = r'''
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif
'''

# --- probe 1: allocate far past the wave's reservation, from inside the region -------------
DRIVER_ALLOC = PROLOGUE + r'''
static int probe_arg_fold(Net *n, Port arg, Port target) {
#ifdef _OPENMP
  if (!omp_in_parallel()) return 0;            /* control: never fires serially */
#else
  return 0;
#endif
  if (arg.node < 0 || arg.node >= n->nn || n->dead[arg.node]) return 0;
  Port res = net_alloc_scott(n, 200000);      /* 600,002 nodes against a 4-node reservation */
  net_link(n, res, target, 1);
  return 1;
}
static int probe_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 0; }
static int probe_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;
}
LinDriver lin_probe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "probe", .description = "arg_fold that over-allocates inside a parallel wave",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = probe_claim, .reduce = probe_reduce,
  .arg_fold = probe_arg_fold,
};
'''

# --- probe 2: claim everything, never progress, and re-enqueue from drain -------------------
DRIVER_STALL = PROLOGUE + r'''
static int stall_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 1; }
static int stall_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;   /* park: no step, no progress */
}
static int stall_drain(Net *n) {
  lin_enqueue(n, (Port){1, 0}, (Port){2, 0});   /* a pair that is not a redex: costs no step */
  return 1;
}
LinDriver lin_probe2_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "probe2", .description = "claim-all driver whose drain never progresses",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = stall_claim, .reduce = stall_reduce,
  .drain = stall_drain,
};
'''

# K = \h t. h discards its second argument, so the wave holds the arguments alive without forcing
# them; nesting it five deep makes the first wave wide enough to take the parallel path (>512 ports).
PROGRAM_ALLOC = r'''(load "std/drivers/driver.lin")
(set_driver "probe")
(define K (\h (\t h)))
((K ( (\x x) (mul 30 30))) ((K ( (\x x) (mul 30 30))) ((K ( (\x x) (mul 30 30))) ((K ( (\x x) (mul 30 30))) ((K ( (\x x) (mul 30 30))) 0)))))
'''

PROGRAM_STALL = r'''(load "std/drivers/driver.lin")
(set_driver "probe2")
((\x x) (mul 2 2))
'''

GUARD = "past the wave's reservation"
STALL = "reduction stalled"


def run(argv, timeout=180, env=None):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, env=env)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -9, "", "TIMEOUT"


def main():
    if len(sys.argv) < 3:
        print(__doc__.strip().splitlines()[-1])
        return 2
    lin, std_dir = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    cc = shutil.which("cc") or shutil.which("gcc")
    if not cc:
        print("parallel_guard: SKIPPED (no cc/gcc to build the probe drivers); the driver-failure "
              "paths are untested in this environment")
        return 0
    root = os.path.dirname(std_dir)
    tmp = tempfile.mkdtemp()
    # a scratch std tree: the probe drivers must not be part of the shipped std
    std = os.path.join(tmp, "std")
    shutil.copytree(std_dir, std, symlinks=True)
    inc = os.path.join(tmp, "inc")
    os.makedirs(inc)
    shutil.copy(os.path.join(root, "src", "lin.h"), inc)
    env = dict(os.environ, LIN_STD=os.path.join(std, "std.lin"), LIN_STD_DIR=std)
    bad = []

    def build(name, source):
        c = os.path.join(std, "drivers", name + ".c")
        so = os.path.join(std, "drivers", name + ".so")
        with open(c, "w") as fh:
            fh.write(source)
        rc, _, err = run([cc, "-O2", "-std=c99", "-fopenmp", "-fPIC", "-shared", "-I", inc,
                          "-o", so, c, "-ldl", "-lm"])
        return None if (rc == 0 and os.path.exists(so)) else err.strip().split("\n")[0][:160]

    # -- 1. an over-allocating arg_fold is diagnosed, not absorbed --------------------------
    why = build("probe", DRIVER_ALLOC)
    if why:
        print("parallel_guard: SKIPPED (probe driver did not compile: %s)" % why)
        return 0
    prog = os.path.join(tmp, "alloc.lin")
    with open(prog, "w") as fh:
        fh.write(PROGRAM_ALLOC)
    rc, out, serr = run([lin, "-t", "1", prog], env=env)
    if GUARD in serr:
        bad.append("the allocation guard fired in a SERIAL run, where nothing allocates in parallel")
    elif rc != 0 or "900" not in out:
        bad.append("the serial control did not produce its value (rc=%d, out=%r)" % (rc, out.strip()[-120:]))
    rc, out, perr = run([lin, "-t", "8", prog], env=env)
    if GUARD not in perr:
        bad.append("8 threads with an over-allocating arg_fold did not report the guard (rc=%d); "
                   "stderr tail: %r" % (rc, perr.strip()[-200:]))

    # -- 2. a drain that never progresses is reported, not printed as a value ---------------
    why = build("probe2", DRIVER_STALL)
    if why:
        print("parallel_guard: SKIPPED (stall probe did not compile: %s)" % why)
        return 0
    prog2 = os.path.join(tmp, "stall.lin")
    with open(prog2, "w") as fh:
        fh.write(PROGRAM_STALL)
    rc, out, _ = run([lin, "-t", "1", prog2], timeout=120, env=env)
    if rc == -9:
        bad.append("a driver that never progresses left the run HANGING (timeout) instead of "
                   "reporting the stall")
    elif STALL not in out:
        bad.append("the stall was not reported (rc=%d, stdout=%r) -- a truncated net can be "
                   "printed as the answer" % (rc, out.strip()[-200:]))

    if bad:
        for b in bad:
            print("FAIL " + b)
        print("parallel_guard: %d problem(s)" % len(bad))
        return 1
    print("parallel_guard: OK (over-allocating arg_fold diagnosed at the node/cap boundary and inert "
          "serially; non-progressing drain reported instead of hanging)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
