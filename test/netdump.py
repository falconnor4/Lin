#!/usr/bin/env python3
"""Read a `.line` net container and show its STRUCTURE -- the view the engine does not have.

A net carries no labels: `net_print` shows VALUES (and `?` where a value is not there), which
cannot say why a fold declined or which copy of a shared body a port belongs to.  Every failed
attempt at the `_ffi`-operand defect so far has ended at "the slot is wired to something that
looks like a binder"; this reads the same container the engine wrote and shows the wiring,
the node tags and the scope gauges, so the answer can be looked at instead of inferred.

Dump one with:

    LIN_DUMP_NET=/tmp/prog.line ./lin prog.lin     # dumped post-reduction, pre-print
    LIN_DUMP_NET=/tmp/prog.line ./lin prog.lin      # (same file, each observed form)

then:

    test/netdump.py /tmp/prog.line                  # node counts per tag
    test/netdump.py /tmp/prog.line --node 1225 2    # wiring around a node, 2 hops
    test/netdump.py /tmp/prog.line --ffi            # every `_ffi`-shaped closure, with its spine
    test/netdump.py /tmp/prog.line --chain 1225.1   # the fan/value chain from one port

The `--ffi` shape is the one std/drivers/arith.c's ffi_header accepts:
LAM -> body LAM -> body APP(port 1) -> fn APP(port 1) whose fn slot is the closure's own
binder, with the operand spine at the body APP's port 2.
"""
import argparse
import struct
import sys
from collections import Counter

TAG = ["LAM", "APP", "DUP", "ERA", "ROOT"]
NONE = (1 << 30) - 1


def load(path) -> dict:
    """The v3..v7 container: shebang, LINE, {ver,nn,nlv,names}, tags, dead, wires, scopes, trie, roots, sections."""
    b = open(path, "rb").read()
    i = b.index(b"LINE") + 4
    ver, nn, nlv, _ = struct.unpack_from("<4I", b, i)
    i += 16
    tag = list(b[i:i + nn]); i += nn
    dead = list(b[i:i + nn]); i += nn
    wire = []
    for _ in range(nn):
        a, c, d = struct.unpack_from("<3I", b, i)
        i += 12
        wire.append([(a & 0x3fffffff, a >> 30), (c & 0x3fffffff, c >> 30), (d & 0x3fffffff, d >> 30)])
    scope = list(struct.unpack_from("<%dI" % nn, b, i))
    return dict(ver=ver, nn=nn, nlv=nlv, tag=tag, dead=dead, wire=wire, scope=scope)


class Net:
    ver: int
    nn: int
    nlv: int
    tag: list
    dead: list
    wire: list
    scope: list

    def __init__(self, path):
        d = load(path)
        self.ver = d["ver"]; self.nn = d["nn"]; self.nlv = d["nlv"]
        self.tag = d["tag"]; self.dead = d["dead"]; self.wire = d["wire"]; self.scope = d["scope"]

    def live(self, p):
        return 0 <= p[0] < self.nn and not self.dead[p[0]]

    def tagof(self, p):
        return TAG[self.tag[p[0]]] if 0 <= p[0] < self.nn else "OUT"

    def wires(self, v):
        return "  ".join("%d->%d.%d(%s)" % (k, q[0], q[1], self.tagof(q)) for k, q in enumerate(self.wire[v]))

    def show(self, v, depth=2, seen=None, indent=0):
        if seen is None:
            seen = set()
        if not (0 <= v < self.nn) or v in seen:
            return
        seen.add(v)
        print("%s%d: %-4s%s scope=%d  |  %s" % ("  " * indent, v, TAG[self.tag[v]],
                                                " DEAD" if self.dead[v] else "", self.scope[v], self.wires(v)))
        if depth:
            for q in self.wire[v]:
                self.show(q[0], depth - 1, seen, indent + 1)

    def chain(self, node, port, steps=10):
        """skip_dup's walk (a fan reads through to the sharing point), then the port's own wire."""
        p = (node, port)
        seen = set()
        for k in range(steps):
            if not self.live(p):
                print("  %2d  %d.%d  dead/out" % (k, p[0], p[1]))
                return
            print("  %2d  %d.%d %-4s scope=%d  |  %s" % (k, p[0], p[1], self.tagof(p), self.scope[p[0]], self.wires(p[0])))
            if self.tag[p[0]] == 2 and p[0] not in seen:        # DUP: to the principal's wire
                seen.add(p[0]); p = self.wire[p[0]][0]
            elif self.tag[p[0]] == 1 and p[1] == 2:             # APP argument: from its wire
                p = self.wire[p[0]][2]
            else:
                p = self.wire[p[0]][p[1]]

    def check(self):
        """Structural invariants a live net must satisfy.  A wire from a live node to a DEAD one is
        the shape that makes a reader print `_` and a fold decline for ever; the engine has no test
        for it (the last count in the source is a comment), so it is checked here, per dump."""
        bad = []
        for v in range(self.nn):
            if self.dead[v]:
                continue
            for k, q in enumerate(self.wire[v]):
                if q[0] == NONE:
                    continue
                if not (0 <= q[0] < self.nn):
                    bad.append((v, k, q, "out of net"))
                elif self.dead[q[0]]:
                    bad.append((v, k, q, "points at a dead node"))
        return bad

    def ffi_closures(self):
        """Every closure std/drivers/arith.c's ffi_header accepts, with its operand spine."""
        def hop(p):
            for _ in range(self.nn):
                if not (self.live(p) and self.tag[p[0]] == 2):
                    return p
                p = self.wire[p[0]][1] if p[1] == 0 else self.wire[p[0]][0]
            return p
        out = []
        for lam in range(1, self.nn):
            if self.tag[lam] != 0 or self.dead[lam]:
                continue
            r = hop(self.wire[lam][2])
            if not (self.live(r) and self.tag[r[0]] == 0 and r[1] == 0):
                continue
            a2 = hop(self.wire[r[0]][2])
            if not (self.live(a2) and self.tag[a2[0]] == 1 and a2[1] == 1):
                continue
            fn = self.wire[a2[0]][0]
            if not (self.live(fn) and self.tag[fn[0]] == 1 and fn[1] == 1):
                continue
            a = hop(self.wire[lam][1])
            if not (a[0] == fn[0] and a[1] == 0):
                continue
            out.append((lam, r[0], a2[0], fn[0], self.wire[a2[0]][2]))
        return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--node", default="")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--chain", default="")
    ap.add_argument("--ffi", action="store_true", help="show every `_ffi`-shaped closure and its spine")
    ap.add_argument("--check", action="store_true", help="report live wires that point at dead nodes")
    a = ap.parse_args()
    net = Net(a.file)
    if a.check:
        bad = net.check()
        print("dangling wires: %d" % len(bad))
        for (v, k, q, why) in bad[:20]:
            print("  %d.%d -> %d.%d (%s)" % (v, k, q[0], q[1], why))
    elif a.node:
        net.show(int(a.node), a.depth)
    elif a.chain:
        n, p = a.chain.split(".")
        net.chain(int(n), int(p))
    elif a.ffi:
        for (lam, r, a2, fn, argp) in net.ffi_closures():
            print("closure LAM %d  ret LAM %d  body APP %d  fnapp %d  spine %d.%d" % (lam, r, a2, fn, argp[0], argp[1]))
            net.show(argp[0], 2, None, 1)
    else:
        print("ver %d  nodes %d  levels %d" % (net.ver, net.nn, net.nlv))
        print(Counter(TAG[t] for t, d in zip(net.tag, net.dead) if not d))
    return 0


if __name__ == "__main__":
    sys.exit(main())
