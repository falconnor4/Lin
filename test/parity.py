#!/usr/bin/env python3
"""test/parity.py -- the same tests, run by two Lin implementations.

The corpus is READ FROM test/run_tests.sh, not restated here: every `run_test`
invocation in the tier loops and the standalone calls become one entry, with the
environment prefix the runner gives it (`N=6 run_test test/runtime_ffi.lin`).
That is the whole point of this file -- if a suite is added to the real runner it
is in the parity run by construction, and the two can never drift.

For each entry the two implementations are run on the SAME file, in the SAME
working directory, with the SAME environment, and their stdout is compared:

    ./lin <file>            (base: the C compiler)
    bin/lin-boot <file>     (boot: the self-hosted compiler)

A file counts as PARITY only when boot's stdout is line-for-line identical to
base's.  The `; expect` comments are still checked against BOTH, so agreement on
a wrong answer is not a pass.

Usage:
    test/parity.py                       # whole corpus
    test/parity.py --only maps,set       # substring filter
    test/parity.py --boot 'prog --x'     # alternate boot command
    test/parity.py --json out.json       # machine-readable report
    test/parity.py --timeout 120         # per-file timeout (default 60s)

Exit status: 0 all parity, 1 any mismatch/failure, 2 configuration error.
"""
import argparse
import json
import os
import re
import shlex
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RUNNER = os.path.join(ROOT, "test", "run_tests.sh")


def corpus():
    """Entries from test/run_tests.sh: [(file, env_dict)] in runner order."""
    src = open(RUNNER, encoding="utf-8").read().splitlines()
    out, env_loop, in_loop = [], {}, False
    for line in src:
        s = line.strip()
        if s.startswith("#"):
            continue
        m = re.match(r"for f in (.+?);\s*do\b", s)
        if m:
            in_loop, env_loop = True, {}
            for tok in m.group(1).split():
                if tok.startswith("test/"):
                    out.append((tok, dict(env_loop)))
            continue
        if s.startswith("done"):
            in_loop = False
            continue
        # `N=6 run_test test/runtime_ffi.lin` / `run_test "$f"` / `run_test "test/x.lin"`
        m = re.search(r"(?:^|\s)((?:[A-Za-z_][A-Za-z0-9_]*=\S+\s+)*)run_test\s+(.+)$", s)
        if not m:
            continue
        env = {}
        for kv in m.group(1).split():
            k, v = kv.split("=", 1)
            env[k] = v.strip('"\'')
        target = m.group(2).strip().strip('"\'')
        if target == "$f":
            continue                      # loop entries were already collected
        if target.startswith("test/") and target.endswith(".lin"):
            out.append((target, env))
    # de-duplicate, preserving order (a file may appear in a loop and again later)
    seen, uniq = set(), []
    for f, e in out:
        key = (f, tuple(sorted(e.items())))
        if key not in seen:
            seen.add(key)
            uniq.append((f, e))
    return uniq


def expects(path):
    got = []
    with open(path, encoding="utf-8", errors="replace") as fh:
        for line in fh:
            if line.startswith("; expect "):
                got.append(line[len("; expect "):].rstrip("\n"))
    return got


def matches(want, got_lines):
    if len(want) != len(got_lines):
        return False
    for w, g in zip(want, got_lines):
        if w.endswith("..."):
            if not g.startswith(w[:-3]):
                return False
        elif w != g:
            return False
    return True


def lines_match(want, b_lines, o_lines):
    if len(b_lines) != len(o_lines):
        return False
    if want and len(want) == len(b_lines):
        for w, b, o in zip(want, b_lines, o_lines):
            if w.endswith("..."):
                pfx = w[:-3]
                if not b.startswith(pfx) or not o.startswith(pfx):
                    return False
            elif b != o:
                return False
        return True
    return b_lines == o_lines


def run(cmd, path, env, timeout):
    e = dict(os.environ)
    e.update(env)
    try:
        p = subprocess.run(cmd + [path], cwd=ROOT, env=e, timeout=timeout,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return p.stdout.decode("utf-8", "replace"), p.stderr.decode("utf-8", "replace"), p.returncode, False
    except subprocess.TimeoutExpired:
        return "", "", None, True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--base", default="./lin")
    ap.add_argument("--boot", default=os.path.join(ROOT, "bin", "lin-boot"))
    ap.add_argument("--only", default="")
    ap.add_argument("--timeout", type=float, default=60.0)
    ap.add_argument("--json", default="")
    ap.add_argument("--verbose", action="store_true")
    a = ap.parse_args()

    base = shlex.split(a.base) if isinstance(a.base, str) else a.base
    boot = shlex.split(a.boot) if isinstance(a.boot, str) else a.boot
    base_bin = base[0] if len(base) == 1 else None
    boot_bin = boot[0] if len(boot) == 1 else None
    if base_bin and boot_bin:
        rb, rbo = os.path.realpath(os.path.join(ROOT, base_bin)), os.path.realpath(os.path.join(ROOT, boot_bin))
        if rb == rbo:
            print(f"parity: base and boot are the SAME executable ({rb}).\n"
                  f"        bin/lin-boot must be the self-hosted compiler, not a symlink to ./lin;\n"
                  f"        otherwise every suite 'passes' without the bootstrap doing anything.",
                  file=sys.stderr)
            return 2
    for name, cmd in (("base", base), ("boot", boot)):
        exe = os.path.join(ROOT, cmd[0])
        if not os.path.exists(exe) and not os.path.exists(cmd[0]):
            print(f"parity: {name} command not found: {' '.join(cmd)}", file=sys.stderr)
            return 2

    entries = corpus()
    if a.only:
        entries = [(f, e) for f, e in entries if a.only in f]
    if not entries:
        print("parity: empty corpus (nothing matched)", file=sys.stderr)
        return 2

    rows, counts = [], {"PARITY": 0, "BOOT-DIFF": 0, "BOOT-TIMEOUT": 0, "BASE-FAIL": 0, "EXPECT-FAIL": 0}
    for path, env in entries:
        want = expects(os.path.join(ROOT, path))
        b_out, b_err, b_rc, b_to = run(base, path, env, a.timeout)
        o_out, o_err, o_rc, o_to = run(boot, path, env, a.timeout)
        b_lines = [l for l in b_out.splitlines() if l != ""]
        o_lines = [l for l in o_out.splitlines() if l != ""]
        want_ok = matches(want, b_lines) if want else True
        if b_to or not want_ok:
            status = "BASE-FAIL" if not b_to else "BASE-FAIL"
        elif o_to:
            status = "BOOT-TIMEOUT"
        elif not lines_match(want, b_lines, o_lines):
            status = "BOOT-DIFF"
        elif want and not matches(want, o_lines):
            status = "EXPECT-FAIL"
        else:
            status = "PARITY"
        counts[status] += 1
        rows.append({"file": path, "env": env, "status": status,
                     "expect_checks": len(want),
                     "base_lines": len(b_lines), "boot_lines": len(o_lines),
                     "boot_stderr": o_err.strip()[:400]})

    width = max(len(r["file"]) for r in rows)
    for r in rows:
        extra = f"  {r['expect_checks']} checks" if r["expect_checks"] else ""
        print(f"{r['status']:<12} {r['file']:<{width}}{extra}")
        if a.verbose and r["status"] != "PARITY":
            for line in r["boot_stderr"].splitlines()[:3]:
                print(f"             boot: {line}")
    total = len(rows)
    print("-" * (width + 30))
    print(f"parity: {counts['PARITY']}/{total} identical, "
          f"{counts['BOOT-DIFF']} boot-diff, {counts['BOOT-TIMEOUT']} boot-timeout, "
          f"{counts['BASE-FAIL']} base-fail, {counts['EXPECT-FAIL']} expect-fail")
    if a.json:
        with open(a.json, "w", encoding="utf-8") as fh:
            json.dump({"rows": rows, "counts": counts, "total": total}, fh, indent=2)
    return 0 if counts["PARITY"] == total else 1


if __name__ == "__main__":
    sys.exit(main())
