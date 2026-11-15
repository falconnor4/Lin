#!/usr/bin/env python3
"""Where does a program's work happen: compiled, or left to the net?

The function compiler takes the shapes it recognises; everything else is reduced by the net, which is
exact but far slower.  This runs programs and reports, per top-level form, the reduction steps and time
the net still spent after the compiler had its turn, and why the compiler declined where it said so.
Ranked by net time, it is the list of what the compiler should learn next (or what the net must do
faster).  The slowest files are listed too, with their wall time split into net, compiling and the rest:
a front end that is slow (reading, checking, expanding) shows up there and nowhere else.

usage: coverage.py <lin-binary> [files or directories ...]     (default: test examples bench)
       --min-steps N    report a form only past N net steps (default 20000)
       --timeout S      per file (default 120)
"""
import collections
import os
import re
import subprocess
import sys
import time

FNTIME = re.compile(r"^fn: \[time: compile ([\d.]+) ms")
BENCH = re.compile(r"^\[bench\] (\d+) steps \| .*? \| ([\d.]+) ms")
DECLINE = re.compile(r"^fn: (?:declined: )?(.*?(?:declined|cannot|not|could not|lazy|missing|unknown|too ).*)$")


def files_of(args):
    out = []
    for a in args:
        if os.path.isdir(a):
            for root, _, fs in os.walk(a):
                out += [os.path.join(root, f) for f in sorted(fs) if f.endswith(".lin")]
        elif a.endswith(".lin"):
            out.append(a)
    return sorted(out)


def run(lin, path, timeout):
    env = dict(os.environ, LIN_FN_DEBUG="1", LIN_NO_CACHE="1")
    env.pop("LIN_FN_OFF", None)
    t0 = time.time()
    try:
        p = subprocess.run([lin, "--bench", path], capture_output=True, text=True, timeout=timeout,
                           env=env, stdin=subprocess.DEVNULL)
        return p.stderr.splitlines(), False, 1000 * (time.time() - t0)
    except subprocess.TimeoutExpired as e:
        err = e.stderr.decode() if isinstance(e.stderr, bytes) else (e.stderr or "")
        return err.splitlines(), True, 1000 * (time.time() - t0)


def forms(lines):
    """[(net steps, net ms, [compiler notes for that form])]: compiler lines precede their form's bench line"""
    out, notes = [], []
    for l in lines:
        m = BENCH.match(l)
        if m:
            out.append((int(m.group(1)), float(m.group(2)), notes))
            notes = []
        elif l.startswith("fn: "):
            notes.append(l[4:])
    return out


def main():
    argv = sys.argv[1:]
    if not argv:
        print(__doc__)
        return 2
    lin = argv.pop(0)
    min_steps, timeout = 20000, 120
    paths = []
    while argv:
        a = argv.pop(0)
        if a == "--min-steps":
            min_steps = int(argv.pop(0))
        elif a == "--timeout":
            timeout = int(argv.pop(0))
        else:
            paths.append(a)
    rows, reasons, timeouts, walls = [], collections.Counter(), [], []
    compiled = net_only = 0
    for f in files_of(paths or ["test", "examples", "bench"]):
        lines, to, wall = run(lin, f, timeout)
        if to:
            timeouts.append(f)
        net_ms = sum(ms for _, ms, _ in forms(lines))
        cc_ms = sum(float(m.group(1)) for m in map(FNTIME.match, lines) if m)
        walls.append((wall, net_ms, cc_ms, f))
        for i, (steps, ms, notes) in enumerate(forms(lines)):
            took = any("compiling" in n or "folded a call" in n for n in notes)
            declined = [n for n in notes if n.startswith("declined") or "the net computes" in n
                        or "is lazy and not yet" in n or "is not a number" in n]
            if steps < min_steps:
                compiled += took
                continue
            net_only += 1
            why = "; ".join(sorted(set(d.replace("declined: ", "") for d in declined))) or \
                ("compiled part, rest on the net" if took else "never offered to the compiler")
            reasons[why] += ms
            rows.append((ms, steps, f, i + 1, why))
    rows.sort(reverse=True)
    print(f"{'net ms':>10} {'net steps':>11}  form")
    for ms, steps, f, i, why in rows:
        print(f"{ms:10.1f} {steps:11d}  {f} #{i}: {why}")
    print("\nslowest files: wall time = net + compiling + the rest (reading, type checking, expanding, C compiler, readback)")
    print(f"{'wall ms':>10} {'net ms':>9} {'compile':>9} {'rest':>9}  file")
    for wall, net_ms, cc_ms, f in sorted(walls, reverse=True)[:15]:
        print(f"{wall:10.0f} {net_ms:9.0f} {cc_ms:9.0f} {max(0, wall - net_ms - cc_ms):9.0f}  {f}")
    print("\nnet time by reason:")
    total = sum(reasons.values()) or 1
    for why, ms in reasons.most_common():
        print(f"{ms:10.1f} ms {100 * ms / total:5.1f}%  {why}")
    if timeouts:
        print("\ntimed out (not counted past the timeout):", *timeouts, sep="\n  ")
    print(f"\ncoverage: {net_only} forms left over {min_steps} steps to the net; {compiled} below it were compiled")
    return 0


if __name__ == "__main__":
    sys.exit(main())
