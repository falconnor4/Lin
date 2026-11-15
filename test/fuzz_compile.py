#!/usr/bin/env python3
"""Random programs: the function compiler against the net.

The net is the definition of the language; the function compiler is an optimiser that must never change an
answer.  This generates random programs from the shapes the compiler handles -- numeric loops, tree recursion,
lists built, mapped, filtered and folded, a tree datatype built and taken apart, a record rebuilt in a loop,
higher-order folds, shared values, nested / literal / wildcard patterns in any order -- and requires each to print the same thing four ways:

  the net alone (LIN_FN_OFF=1), compiled, compiled on one thread, compiled with freed blocks poisoned.

Sizes are mostly small so the net can answer.  One time in six a size is past the compiler's parallel
threshold; the net alone is too slow there, so the compiled program on one thread (no parallel code at all)
is the reference, and the parallel and poisoned runs must match it.  A failing program is written out whole, with its seed.

usage: fuzz_compile.py <lin-binary> [count] [seed]       (default 40 programs, seed 1)
"""
import os
import random
import subprocess
import sys
import tempfile

OPS = ["add", "sub", "mul", "band", "bor", "bxor"]
CMPS = ["lt", "gt", "eq", "leq", "geq"]


class Gen:
    def __init__(self, rng):
        self.r = rng
        self.big = False    # a size past the parallel threshold: too slow for the net alone
        self.defs = []
        self.uses = []      # numeric expressions that call the definitions
        self.n = 0

    def size(self, small):
        """mostly small; one time in six past the compiler's parallel threshold (a few thousand), so the
        parallel paths run too -- still small enough for the net to answer"""
        if self.r.random() < 0.83:
            return self.r.randint(0, small)
        self.big = True
        return self.r.randint(4000, 6000)

    def name(self, base):
        self.n += 1
        return f"{base}{self.n}"

    def arith(self, vs, depth=2):
        r = self.r
        if depth == 0 or r.random() < 0.3:
            return r.choice(vs) if vs and r.random() < 0.7 else str(r.randint(-9, 30))
        op = r.choice(OPS + ["div", "mod"])
        a, b = self.arith(vs, depth - 1), self.arith(vs, depth - 1)
        if op in ("div", "mod"):
            b = str(r.randint(1, 9)) if r.random() < 0.8 else b   # (by zero is 0, in both)
        return f"({op} {a} {b})"

    def cond(self, vs):
        return f"({self.r.choice(CMPS)} {self.arith(vs, 1)} {self.arith(vs, 1)})"

    # ---- definitions: each adds a function and a use of it
    def loop(self):
        f = self.name("loop")
        self.defs.append(f"(define {f} (\\k (\\acc (if (eq k 0) acc ({f} (sub k 1) {self.arith(['acc', 'k'])})))))")
        self.uses.append(f"({f} {self.size(40)} {self.r.randint(-5, 5)})")

    def tree(self):
        f = self.name("tree")
        op = self.r.choice(["add", "sub", "bxor", "max"])
        comb = f"(if (gt ({f} (sub k 1)) ({f} (sub k 2))) ({f} (sub k 1)) ({f} (sub k 2)))" if op == "max" \
            else f"({op} ({f} (sub k 1)) ({f} (sub k 2)))"
        self.defs.append(f"(define {f} (\\k (if (lt k 2) {self.arith(['k'], 1)} {comb})))")
        self.uses.append(f"({f} {self.r.randint(0, 14)})")

    def lists(self):
        r = self.r
        b, m, fl, fo = self.name("build"), self.name("map"), self.name("filter"), self.name("fold")
        self.defs.append(f"(define {b} (\\k (if (eq k 0) snil (scons {self.arith(['k'])} ({b} (sub k 1))))))")
        self.defs.append(f"(define {m} (\\s (match s (snil snil) ((scons h t) (scons {self.arith(['h'])} ({m} t))))))")
        self.defs.append(f"(define {fl} (\\s (match s (snil snil) ((scons h t) (if {self.cond(['h'])} (scons h ({fl} t)) ({fl} t))))))")
        self.defs.append(f"(define {fo} (\\s (\\a (match s (snil a) ((scons h t) ({fo} t {self.arith(['h', 'a'])}))))))")
        src = f"({b} {self.size(25)})"
        for _ in range(r.randint(0, 3)):
            src = f"({r.choice([m, fl])} {src})"
        if r.random() < 0.4:   # (the list used twice: shared, so neither may consume it)
            self.uses.append(f"(let ((l {src})) (add ({fo} l 0) ({fo} l 1)))")
        else:
            self.uses.append(f"({fo} {src} {r.randint(0, 3)})")

    def trees(self):
        r = self.r
        mk, sm, mp = self.name("mkT"), self.name("sumT"), self.name("mapT")
        self.defs.append(f"(define {mk} (\\d (\\x (if (eq d 0) (leaf x) (node ({mk} (sub d 1) {self.arith(['x'], 1)}) ({mk} (sub d 1) {self.arith(['x'], 1)}) x)))))")
        arms = [f"((leaf v) {self.arith(['v'], 1)})", f"((node l q w) (add w ({r.choice(['add', 'bxor', 'sub'])} ({sm} l) ({sm} q))))"]
        r.shuffle(arms)
        self.defs.append(f"(define {sm} (\\t (match t {' '.join(arms)})))")
        self.defs.append(f"(define {mp} (\\t (match t ((leaf v) (leaf {self.arith(['v'], 1)})) ((node l q w) (node ({mp} l) ({mp} q) w)))))")
        d = r.randint(0, 6)
        if r.random() > 0.83:
            d, self.big = r.randint(11, 12), True
        t = f"({mk} {d} {r.randint(0, 9)})"
        if r.random() < 0.5:
            t = f"({mp} {t})"
        self.uses.append(f"({sm} {t})")

    def record(self):
        f = self.name("rec")
        self.defs.append(f"(define {f} (\\k (\\p (if (eq k 0) (match p ((pr a b) (add a b))) "
                         f"({f} (sub k 1) (match p ((pr a b) (pr {self.arith(['a', 'b', 'k'])} {self.arith(['a', 'b'])}))))))))")
        self.uses.append(f"({f} {self.r.randint(0, 30)} (pr {self.r.randint(0, 9)} {self.r.randint(0, 9)}))")

    def higher(self):
        r = self.r
        b = self.name("hb")
        self.defs.append(f"(define {b} (\\k (if (eq k 0) snil (scons k ({b} (sub k 1))))))")
        self.uses.append(f"(sfoldl (\\a (\\x {self.arith(['a', 'x'])})) {r.randint(0, 5)} (smap (\\x {self.arith(['x'])}) ({b} {self.size(20)})))")

    def patterns(self):
        """nested, literal and wildcard patterns, branches in a shuffled (still meaningful) order"""
        r = self.r
        b, c = self.name("pb"), self.name("cl")
        self.defs.append(f"(define {b} (\\k (if (eq k 0) lnil (lcons {self.arith(['k'], 1)} ({b} (sub k 1))))))")
        disjoint = [f"((lcons a (lcons q rest)) (add {self.arith(['a', 'q'], 1)} ({c} rest)))",
                    f"((lcons a lnil) {self.arith(['a'], 1)})"]
        wild = r.random() < 0.4
        if not wild:
            disjoint.append(f"(lnil {r.randint(-3, 9)})")
        r.shuffle(disjoint)
        if r.random() < 0.6:   # a literal row: before the general pair row it refines
            pair = next(i for i, x in enumerate(disjoint) if "rest" in x)
            disjoint.insert(r.randint(0, pair), f"((lcons {r.randint(-2, 5)} (lcons q rest)) (sub {self.arith(['q'], 1)} ({c} rest)))")
        if wild:
            disjoint.append(f"(_ {r.randint(-3, 9)})")
        self.defs.append(f"(define {c} (\\l (match l {' '.join(disjoint)})))")
        self.uses.append(f"({c} ({b} {self.size(30)}))")
        n = self.name("nm")
        lits = sorted(set(r.randint(0, 4) for _ in range(r.randint(1, 3))))
        rows = [f"({v} {self.arith([], 1)})" for v in lits]
        r.shuffle(rows)
        self.defs.append(f"(define {n} (\\k (match k {' '.join(rows)} (j (if (lt j 2) j (add ({n} (sub j 1)) ({n} (sub j 2))))))))")
        self.uses.append(f"({n} {r.randint(0, 15)})")

    def closures(self):
        """partial application, a closure capturing a value, a let-bound function used twice"""
        r = self.r
        mk, ap, b = self.name("mk"), self.name("ap"), self.name("cb")
        self.defs.append(f"(define {mk} (\\n (\\x {self.arith(['n', 'x'])})))")
        self.defs.append(f"(define {ap} (\\f (\\s (match s (snil snil) ((scons h t) (scons (f h) ({ap} f t)))))))")
        self.defs.append(f"(define {b} (\\k (if (eq k 0) snil (scons k ({b} (sub k 1))))))")
        k = r.randint(-5, 9)
        self.uses.append(f"(let ((g ({mk} {k}))) (sfoldl (\\a (\\x (add a x))) (g 1) ({ap} g ({b} {self.size(20)}))))")

    def shared(self):
        if not self.uses:
            self.loop()
        u = self.r.choice(self.uses)
        self.uses.append(f"(let ((x {u})) ({self.r.choice(OPS)} x x))")

    def program(self):
        for _ in range(self.r.randint(1, 4)):
            self.r.choice([self.loop, self.tree, self.lists, self.trees, self.record, self.higher, self.patterns, self.closures, self.shared])()
        e = self.uses[0]
        for u in self.uses[1:]:
            e = f"({self.r.choice(['add', 'bxor', 'sub'])} {e} {u})"
        return "\n".join(["(datatype T (leaf (v num)) (node (l T) (r T) (w num)))",
                          "(datatype P (pr (a num) (b num)))",
                          "(datatype L (lnil) (lcons (h num) (t L)))"] + self.defs + [e]) + "\n"


def run(lin, path, env_extra, args=()):
    env = dict(os.environ)
    env.update(env_extra)
    try:
        p = subprocess.run([lin, *args, path], capture_output=True, text=True, timeout=300, env=env)
        return p.stdout.strip() if p.returncode == 0 else f"<exit {p.returncode}> {p.stdout.strip()[-200:]}"
    except subprocess.TimeoutExpired:
        return "<timeout>"


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 2
    lin = sys.argv[1]
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 40
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    tmp = tempfile.mkdtemp()
    fails = big = 0
    for i in range(count):
        s = seed * 100003 + i
        g = Gen(random.Random(s))
        src = g.program()
        path = os.path.join(tmp, f"p{i}.lin")
        with open(path, "w") as f:
            f.write(src)
        # the reference: the net alone -- or, for a size past the parallel threshold (where the net alone is
        # too slow to wait for), the compiled program on one thread, which runs no parallel code at all
        if g.big:
            big += 1
            net = run(lin, path, {}, ("-t", "1"))
            runs = {"compiled": run(lin, path, {}),
                    "poisoned": run(lin, path, {"LIN_FN_POISON": "1"}),
                    "poisoned, one thread": run(lin, path, {"LIN_FN_POISON": "1"}, ("-t", "1"))}
        else:
            net = run(lin, path, {"LIN_FN_OFF": "1"})
            runs = {"compiled": run(lin, path, {}),
                    "one thread": run(lin, path, {}, ("-t", "1")),
                    "poisoned": run(lin, path, {"LIN_FN_POISON": "1"})}
        bad = {k: v for k, v in runs.items() if v != net}
        if bad or not net.startswith("=>"):
            fails += 1
            keep = os.path.join(tmp, f"fail_{s}.lin")
            with open(keep, "w") as f:
                f.write(src)
            ref = "one thread" if g.big else "net"
            print(f"FAIL program {i} (seed {s}, kept as {keep}): {ref} '{net}'", *(f"{k} '{v}'" for k, v in bad.items()))
    if fails:
        print(f"fuzz_compile: {fails} of {count} random programs disagreed")
        return 1
    print(f"fuzz_compile: OK ({count - big} random programs give the net's answer compiled, on one thread and poisoned; "
          f"{big} past the parallel threshold give one thread's answer in parallel and poisoned)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
