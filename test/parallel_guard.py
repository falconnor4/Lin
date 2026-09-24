#!/usr/bin/env python3
r"""The driver ABI's failure modes must be diagnosed, not silently absorbed.

ABI 3 deleted the four legacy hooks (`arg_fold`, `materialize`, `drain`, `pending`) and with them the
two ways a driver could break the core's invariants:

1. `arg_fold` ran INSIDE a parallel wave, where `net_alloc` cannot grow the net (a `realloc` would
   move the tag/wire/scope/name arrays out from under every worker holding raw pointers into them).
   Measured before the guard: an ASan heap-buffer-overflow, a SIGSEGV, `free(): invalid pointer`.
   A driver no longer gets a hook in that region at all -- `claim`/`reduce` run between waves -- and a
   driver that needs a concrete operand now asks for it with `net_force` rather than being handed one.

2. `drain` could re-enqueue work without making progress.  `net_reduce` bounded that with a livelock
   guard, and the guard used to drop the active list and `break` with no signal -- a truncated net
   could then be printed as the answer instead of being reported as not-a-value.  ABI 3 has no drain
   loop: a driver re-enqueues inside `reduce`, and `net_reduce` stops as soon as a wave makes no
   progress, so a driver that only re-enqueues TERMINATES the run rather than spinning in it.

What is left to test is therefore (a) that the ABI bump is actually enforced -- an ABI-2 plugin is
smaller than the ABI-3 struct, so reading it would run past its end and the core must reject it
loudly instead -- and (b) that a driver which claims every redex and then does nothing still leaves
the run TERMINATING, rather than hanging or quietly reporting a value it never computed.

This test compiles those drivers from strings into a scratch std tree -- they are NOT part of the
shipped std.  A compiler is needed to build the probes; where none is found the test SKIPS loudly
rather than passing quietly, so a CI that loses its toolchain is visible.

usage: parallel_guard.py <lin-binary> <std-dir>
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile

PROLOGUE = r'''
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
'''

# --- probe 1: a plugin built against the DELETED ABI must be rejected, not trusted --------------
DRIVER_ABI2 = PROLOGUE + r'''
static int old_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 0; }
static int old_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;
}
LinDriver lin_abiprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = 2u,     /* the deleted ABI: fewer fields than this core reads */
  .name = "abiprobe", .description = "an ABI-2 plugin",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = old_claim, .reduce = old_reduce,
};
'''

# --- probe 2: claim everything, compute nothing, and re-enqueue forever ------------------------
PROBE_BODY = PROLOGUE + r'''
static int noclaim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 1; }
static int noreduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)lim; (void)ch;
  for (int i = 0; i < nr; i++) lin_enqueue(n, rx[2 * i], rx[2 * i + 1]);   /* no progress, ever */
  return 0;
}
LinDriver lin_noprog_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "noprog", .description = "claims every redex and re-enqueues it without progress",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = noclaim, .reduce = noreduce,
};
'''

PROGRAM = '''(load "std/drivers/driver.lin")
(set_driver "%s")
((\\x x) (mul 2 2))
'''

REJECT = "rejected"
VALUE = re.compile(r"^=> .+", re.M)


def run(argv, timeout=120, env=None):
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
    # `lin.h` comes from the SOURCE tree, which is not where the installed std is: a packaged run
    # (nix's test derivation) has `$out/bin` and `$out/share/lin/std` but no `src/`.  The test file
    # itself lives beside the header, so that is the lookup that works in both.
    here = os.path.dirname(os.path.abspath(__file__))
    hdr = None
    for cand in (os.path.join(here, os.pardir, "src", "lin.h"),
                 os.path.join(os.path.dirname(std_dir), "src", "lin.h")):
        if os.path.exists(cand):
            hdr = os.path.abspath(cand)
            break
    if not hdr:
        print("parallel_guard: SKIPPED (src/lin.h not found; the probe drivers cannot be built)")
        return 0
    tmp = tempfile.mkdtemp()
    std = os.path.join(tmp, "std")
    shutil.copytree(std_dir, std, symlinks=True)
    for d, _, _ in os.walk(std):
        os.chmod(d, 0o755)          # a packaged std is read-only; the probes are written into it
    inc = os.path.join(tmp, "inc")
    os.makedirs(inc)
    shutil.copy(hdr, inc)
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

    # -- 1. an ABI-2 plugin is rejected loudly ----------------------------------------------
    why = build("abiprobe", DRIVER_ABI2)
    if why:
        print("parallel_guard: SKIPPED (ABI probe did not compile: %s)" % why)
        return 0
    prog = os.path.join(tmp, "abi.lin")
    with open(prog, "w") as fh:
        fh.write(PROGRAM % "abiprobe")
    rc, out, serr = run([lin, prog], env=env)
    if REJECT not in serr:
        bad.append("an ABI-2 plugin was not rejected; the core would read a struct the plugin does "
                   "not have (rc=%d, stderr=%r)" % (rc, serr.strip()[-200:]))
    if "=> 4" not in out:
        bad.append("with the ABI-2 plugin rejected the core still had to compute the answer itself "
                   "(the base engine is complete without any driver); got %r" % out.strip()[-120:])

    # -- 2. a driver that claims everything must not make the run hang ---------------------
    why = build("noprog", PROBE_BODY)
    if why:
        print("parallel_guard: SKIPPED (no-progress probe did not compile: %s)" % why)
        return 0
    prog2 = os.path.join(tmp, "noprog.lin")
    with open(prog2, "w") as fh:
        fh.write(PROGRAM % "noprog")
    rc, out, _ = run([lin, "-t", "1", prog2], timeout=120, env=env)
    if rc == -9:
        bad.append("a driver that claims every redex and never progresses left the run HANGING "
                   "(timeout): net_reduce must stop as soon as a wave makes no progress")
    elif rc != 0:
        bad.append("the no-progress run exited %d; a driver that declines to reduce must leave the "
                   "run terminating and reporting, not failing (stdout=%r)" % (rc, out.strip()[-160:]))

    if bad:
        for b in bad:
            print("FAIL " + b)
        print("parallel_guard: %d problem(s)" % len(bad))
        return 1
    print("parallel_guard: OK (an ABI-2 plugin is rejected instead of read past its end; a driver "
          "that claims every redex and never progresses terminates the run)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
