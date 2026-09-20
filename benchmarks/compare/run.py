#!/usr/bin/env python3
"""Head-to-head Lin vs C benchmark harness.

WHY THIS EXISTS.  DESIGN.md G4 makes the AOT artifact the deliverable, and every other
measurement in the tree is Lin-against-Lin: the flake's benchmark runner reports Lin's
step/node count with and without the e-graph pass, which says nothing about the claim
"faster than C".  So a comparison against a real C compiler is its own instrument and
lives here.

WHAT IS BEING COMPARED, HONESTLY.  Each workload is one program written twice -- the
natural Lin and the natural C for the same algorithm -- and both must print the same
value or the run is reported as MISMATCH and excluded from the timing summary.  Three
measurements are taken per side:

  src   the interpreted path (`lin file.lin`), which pays the front end: 73 ms of
        startup measured at 5a39e37, almost all of it compiling std.lin.
  aot   the `.line` artifact (`lin build`, then run the container): 1.1 ms of startup.
        This is the number that must be compared against C, because it is the artifact.
  c     `gcc -O2` on the C twin.

Ratios are Lin/C: below 1.00 means Lin is faster.  Wall clock is the whole process, so
startup is inside the number on both sides -- deliberately, since that is what a user
pays.  `--runs` takes the minimum, which is the standard choice for a lower bound on a
noisy shared machine; the median is printed too so a bimodal result cannot hide.

NOT COMPARABLE, and labelled so in the output: a workload whose C twin computes the same
value by a cheaper route than the Lin program does.  `church_exp` is the example -- Lin
normalises a Church exponentiation whose naive cost is exponential, and no C program
"does the same thing", because C cannot represent the sharing.  Those rows are reported
with the ratio but flagged, so the headline number is never built out of them.

usage: run.py [--runs N] [--filter SUBSTR] [--json PATH] [--interp-only]
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
WORKLOADS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "workloads")
LIN = os.environ.get("LIN_BIN", os.path.join(ROOT, "lin"))
CC = os.environ.get("CC", "gcc")


def run(cmd, cwd=None):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, stdin=subprocess.DEVNULL, text=True)


def timed(cmd, runs, cwd=None):
    """Best-of-`runs` and median wall clock in ms, plus the output of the last run."""
    ts, out, rc = [], "", None
    for _ in range(runs):
        t0 = time.perf_counter()
        r = run(cmd, cwd=cwd)
        ts.append((time.perf_counter() - t0) * 1000.0)
        out, rc = r.stdout, r.returncode
    ts.sort()
    return ts[0], ts[len(ts) // 2], out, rc


def normalise(s):
    """Lin prints `=> V`, C prints `V`.  Compare the value, ignore surrounding noise."""
    vals = []
    for line in s.splitlines():
        line = line.strip()
        if not line or line.startswith("warning") or line.startswith("[bench]"):
            continue
        vals.append(re.sub(r"^=>\s*", "", line))
    return vals


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--runs", type=int, default=7, help="timed repetitions, min is reported")
    ap.add_argument("--filter", default="", help="only workloads whose name contains this")
    ap.add_argument("--json", default="", help="also write the results to this path")
    ap.add_argument("--interp-only", action="store_true", help="skip the AOT build/run")
    args = ap.parse_args()

    if not os.path.isdir(WORKLOADS):
        sys.exit("no workloads directory: %s" % WORKLOADS)
    names = sorted(f[:-4] for f in os.listdir(WORKLOADS)
                   if f.endswith(".lin") and os.path.exists(os.path.join(WORKLOADS, f[:-4] + ".c")))
    names = [n for n in names if args.filter in n]
    if not names:
        sys.exit("no workloads matched")

    tmp = tempfile.mkdtemp(prefix="lincmp-")
    rows, mismatches = [], []
    hdr = "%-14s %9s %9s %9s %9s  %s" % ("workload", "c ms", "lin aot", "lin src", "aot/c", "note")
    print(hdr)
    print("-" * len(hdr))
    try:
        for name in names:
            lin_src = os.path.join(WORKLOADS, name + ".lin")
            c_src = os.path.join(WORKLOADS, name + ".c")
            c_bin = os.path.join(tmp, name + ".cbin")
            line_out = os.path.join(tmp, name + ".line")

            cc = run([CC, "-O2", "-o", c_bin, c_src])
            if cc.returncode != 0:
                print("%-14s  C build failed: %s" % (name, cc.stderr.strip().splitlines()[:1]))
                continue
            c_ms, c_med, c_out, _ = timed([c_bin], args.runs)

            src_ms, src_med, src_out, src_rc = timed([LIN, lin_src], args.runs, cwd=ROOT)

            aot_ms = aot_med = None
            aot_out, aot_rc = "", None
            note = ""
            if not args.interp_only:
                b = run([LIN, "build", lin_src, "-o", line_out], cwd=ROOT)
                if b.returncode != 0 or not os.path.exists(line_out):
                    note = "AOT BUILD FAILED"
                else:
                    aot_ms, aot_med, aot_out, aot_rc = timed([LIN, line_out], args.runs, cwd=ROOT)

            want = normalise(c_out)
            got_src = normalise(src_out)
            got_aot = normalise(aot_out) if aot_ms is not None else None
            ok = (want == got_src) and (got_aot is None or want == got_aot)
            if not ok:
                # A workload that disagrees is reported, never averaged in.
                note = "MISMATCH"
                mismatches.append((name, want, got_src, got_aot))

            ratio = (aot_ms / c_ms) if (aot_ms and c_ms) else float("nan")
            print("%-14s %9.2f %9s %9.2f %9s  %s" % (
                name, c_ms,
                ("%.2f" % aot_ms) if aot_ms is not None else "-",
                src_ms,
                ("%.2f" % ratio) if aot_ms is not None else "-", note))
            rows.append(dict(name=name, c_ms=c_ms, c_med=c_med, aot_ms=aot_ms, aot_med=aot_med,
                             src_ms=src_ms, src_med=src_med, ratio=ratio, ok=ok,
                             artifact_bytes=os.path.getsize(line_out) if os.path.exists(line_out) else None))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    good = [r for r in rows if r["ok"] and r["aot_ms"]]
    print()
    if good:
        wins = sum(1 for r in good if r["ratio"] < 1.0)
        geo = 1.0
        for r in good:
            geo *= r["ratio"]
        geo **= 1.0 / len(good)
        print("AOT vs gcc -O2 over %d correct workloads: %d faster, geometric mean Lin/C = %.2fx"
              % (len(good), wins, geo))
    if mismatches:
        print("\nMISMATCHES (excluded from the summary above):")
        for name, want, gs, ga in mismatches:
            print("  %s: C%s src%s aot%s" % (name, want, gs, ga))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump(rows, fh, indent=2)
    return 0


if __name__ == "__main__":
    sys.exit(main())
