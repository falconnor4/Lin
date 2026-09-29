#!/usr/bin/env python3
"""No hardcoded limits.

Lin's rule is that a limit is DERIVED from the data (a net's node count, a spine's length, a graph's
class count) rather than chosen -- and that a chosen one, where it survives, is written down with a
reason instead of hiding in the tree.  This test is that writing-down: it audits the core and the
drivers for fixed-size scratch and numeric guards, and fails on anything that is neither structural
nor declared below.

It cannot know *semantically* whether an array is a cap (a node has 3 ports -- structure, not a limit),
so the classification is explicit.  What it guarantees is the property that matters: a new hardcoded
limit cannot land quietly.

Print `--list` for the whole inventory.
"""
import re, sys, glob, os

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# A fixed-size scratch array: `TYPE name[N]`, N a literal.  Under 16 it is the shape of the thing
# (a node's ports, a pair's ends, a format header), so it is structural by construction.
ARRAY = re.compile(r"\b(?:int|long|char|unsigned|size_t|double|Val|Port|void\s*\*)\s+\**(\w+)\s*\[\s*(\d+)\s*\]")
# A numeric guard: a two-digit-or-more literal compared against.  `ch < 256` is a byte, not a cap, but
# it is still a fact about the program worth stating.
GUARD = re.compile(r"(?:if|while|return|\?)[^;\n]*?(?<!<)([<>]=?\s*\d{2,})\b")
# A stated size: `#define X 256`.  The audit reads uses, so without this the definition itself is
# invisible -- and `[NAME]` downstream then looks like structure when it is that number, once removed.
DEFINE = re.compile(r"^\s*#define\s+(\w+)\s+(\d+)\b")
# An array whose size is a NAME rather than a literal: the same limit, one indirection further out.
SYMSIZE = re.compile(r"\b(?:int|long|char|unsigned|size_t|double|Val|Port|void\s*\*)\s+\**(\w+)\s*\[\s*([A-Z][A-Z0-9_]{2,})\s*\]")
# A shift, which is how a large round number gets written without digits: `1L << 24`.  Two-digit
# shift amounts only; `1 << 3` is a bit layout, not a budget.
SHIFT = re.compile(r"(?<![<\w])(\d+)[LU]*\s*<<\s*(\d{2,})\b")

# (file, finding) -> why it is allowed to be what it is.  Exact first, then the pattern table, so
# moving code does not churn this and one reason can cover a family.
DECLARED = {
    ("src/main.c", "< 30"): "rlimit request: the core asks for a 1 GB stack, capped at what the OS allows",
    ("src/net.c", "< 30"): "table growth guard: refuses to double past 1 << 30 entries (allocation)",
    ("src/net.c", ">= 16"): "driver cap list: driven by n->ndrv, bounded by the claim region",
    ("src/net.c", "< 16"): "the claim region: its slots are a fixed ABI array, and the count is n->ndrv",
    ("src/net.c", ">= 64"): "domain ids are a closed vocabulary (LIN_ENC_*), 64 leaves room",
    ("src/net.c", "slices[16]"): "claim-region scratch: one per claim slot",
    ("src/net.c", "scaps[16]"): "claim-region scratch: one per claim slot",
    ("src/net.c", "scnts[16]"): "claim-region scratch: one per claim slot",
    ("src/net.c", "have[16]"): "claim-region scratch: one per claim slot",
    ("src/type.c", "mid[256]"): "the same Scheme ABI array as f[256]",
    ("src/type.c", "dyn[256]"): "the same Scheme ABI array, for dynamic type variables",
    ("src/io.c", "< 256"): "byte range check: characters are bytes, not a program limit",
    ("src/lin.h", "sv[4096]"): "the Val ABI's string field: a driver-visible fixed buffer (known ABI limit)",
    ("src/type.c", "f[256]"): "free-variable set: bounded by the Scheme ABI array it is copied into",
    ("src/type.c", "f[64]"): "the same set, for a single type",
    ("src/type.c", "< 256"): "the same set, as a bound (known limit, see --list)",
    ("src/type.c", "< 26"): "renders a type variable a..z, then falls back to tN (display only)",
    ("std/drivers/readback.c", "< 255"): "byte range check on a terminal payload",
    ("std/drivers/readback.c", "> 255"): "the same byte range check, from the other side",
    ("std/drivers/readback.c", "< 26"): "renders a type variable as a letter, display only",
    ("std/drivers/native.c", "> 16"): "observation-cone depth for the native claim: a driver heuristic",
    ("std/drivers/gpu.c", "0x3fffffff"): "wire bit layout: node index in the low 30 bits",
    ("std/drivers/native.c", "expr[2048]"): "expression buffer for driver diagnostics",
    ("std/drivers/readback.c", "src[1024]"): "source slice for a readback diagnostic",
    ("src/lin.h", "#define LIN_MAX_CLAIM_PAIRS 32"): "the claim storage's OWN size: every bound in the core is N_OF(that array), so the region and its guard cannot drift apart, and lin_claim_check refuses a larger claim out loud",
    ("src/lin.h", "#define LIN_MAX_CLAIM_EXITS 16"): "the claim storage's own size, as above",
    ("src/lin.h", "#define LIN_CLAIM_NODES 128"): "the claim storage's own size, as above",
    ("src/lin.h", "#define LIN_DRV_SLOTS 8"): "driver state slots in the Net ABI; the core's own table derives from this array (N_OF(((Net *)0)->drv))",
    ("src/lin.h", "exits[LIN_MAX_CLAIM_EXITS]"): "the storage that LIN_MAX_CLAIM_EXITS sizes -- bounds derive from it, never from the macro",
    ("src/lin.h", "nodes[LIN_CLAIM_NODES]"): "the storage that LIN_CLAIM_NODES sizes -- bounds derive from it, never from the macro",
    ("src/main.c", "#define PATH_MAX 4096"): "POSIX path length, restated for hosts without limits.h",
    ("src/main.c", "<< 30"): "rlimit request: a 1 GB stack, capped at whatever the OS allows",
    ("src/main.c", "<< 22"): "AOT_STEP_LIMIT: the artifact build's own ceiling (known limit, next to remove)",
    ("src/net.c", "<< 30"): "table growth guard: refuses to double past 1 << 30 entries (allocation)",
    ("src/net.c", "<< 22"): "per-wave reduce quantum: work done before returning to the wave loop (scheduling, not a ceiling)",
    ("std/drivers/arith.c", "<< 22"): "the same per-wave reduce quantum, from the driver's own reducer",
    ("std/drivers/native.c", "#define FN_CACHE 256"): "driver-local symbol cache size (known limit)",
    ("std/drivers/simd.c", "#define SIMD_WIDTH 8"): "the machine's vector width, as this driver's own constant",
    ("std/runtime/pattern.h", "#define LIN_PAT_SLOTS 8"): "pattern matcher capacity per match (known limit)",
    ("std/runtime/pattern.h", "#define LIN_PAT_BINDS 8"): "pattern matcher capacity, as above",
    ("std/runtime/pattern.h", "#define LIN_PAT_CYCLES 4"): "pattern matcher capacity, as above",
    ("std/runtime/pattern.h", "#define LIN_PAT_NODES 64"): "pattern matcher capacity, as above",
    ("std/runtime/pattern.h", "#define LIN_PAT_DEPTH 48"): "pattern RECURSION DEPTH: a depth bound in the matcher (known limit, see --list)",
}
# A family reason: matched against (file, finding) in order.
PATTERNS = [
    (r"\.c$", r"^(fn|sfx)\[\d+\]$", "symbol name buffer: a longer FFI name is truncated before dlsym"),
    (r"\.c$", r"^sym\[\d+\]$", "symbol name buffer, as above"),
    (r"\.c$", r"^(path|tmp|dir|full|so|c|self_path)\[\d+\]$", "path buffer: a longer path is mishandled (known limit)"),
    (r"\.c$", r"^skip\[\d+\]$", "artifact-format skip buffer while scanning back from a wire (known limit)"),
    (r"\.(c|h)$", r"^\w*\[PATH_MAX\]$", "path buffer at the OS's own limit, not one of ours"),
    (r"\.(c|h)$", r"^<< 1[46]$", "initial net capacity: grows on demand, so not a ceiling"),
    (r"\.(c|h)$", r"^slots\[LIN_PAT_SLOTS\]$", "pattern matcher: its per-match slot array, at the matcher's own capacity"),
    (r"\.(c|h)$", r"^\w+\[EFF_N\]$", "enum-sized table: exactly one entry per kind, so structure, not a limit"),
    (r"pattern\.h$", r"^\w+\[LIN_PAT_\w+\]$", "pattern matcher: a per-match array at the matcher's own capacity"),
    (r"\.(c|h)$", r"^#define \w+ [0-2]$", "an enumeration tag (0..2), not a capacity: these are kinds, not sizes"),
    (r"\.c$", r"^in_buf\[\d+\]$", "stdin buffer for a driver readback: grows with the read, not a program limit"),
    (r"\.c$", r"^tmp\[\d+\]$", "scratch for a formatted diagnostic message"),
    (r"\.c$", r"^q\[\d+\]$", "quantified-variable set: the same Scheme ABI array"),
    (r"\.(c|h)$", r"^(why|msg|[A-Z]+MSG|err)\[\d+\]$", "diagnostic message buffer: truncates a message, never a value"),
    (r"\.c$", r"^dec\[\d+\]$", "lexer decode buffer for an escaped literal (known limit)"),
]

def in_comment(states, line):
    """Toggle a /* */ state, so prose about limits is not read as a limit."""
    i, n = 0, len(line)
    while i < n:
        if states["block"]:
            j = line.find("*/", i)
            if j < 0: return True
            states["block"] = False; i = j + 2
        else:
            j = line.find("/*", i)
            k = line.find("//", i)
            if k >= 0 and (j < 0 or k < j): return False      # code before any comment
            if j < 0: return False
            states["block"] = True; i = j + 2
    return states["block"]

def findings():
    out = []
    paths = sorted(glob.glob(f"{REPO}/src/*.c") + glob.glob(f"{REPO}/src/*.h") +
                   glob.glob(f"{REPO}/std/**/*.c", recursive=True) + glob.glob(f"{REPO}/std/**/*.h", recursive=True))
    for f in paths:
        rel = os.path.relpath(f, REPO)
        states = {"block": False}
        for i, line in enumerate(open(f), 1):
            if in_comment(states, line):
                continue
            code = line.split("//")[0]
            for m in ARRAY.finditer(code):
                if int(m.group(2)) >= 16:
                    out.append((rel, i, f"{m.group(1)}[{m.group(2)}]", code.strip()[:96]))
            for m in GUARD.finditer(code):
                if "<<" in code[:m.start(1)]:
                    continue                                       # a shift amount, not a guard
                out.append((rel, i, m.group(1).strip(), code.strip()[:96]))
            for m in DEFINE.finditer(line):
                out.append((rel, i, f"#define {m.group(1)} {m.group(2)}", line.strip()[:96]))
            for m in SYMSIZE.finditer(code):
                out.append((rel, i, f"{m.group(1)}[{m.group(2)}]", code.strip()[:96]))
            for m in SHIFT.finditer(code):
                out.append((rel, i, f"<< {m.group(2)}", code.strip()[:96]))
    return sorted(set(out), key=lambda f: (f[0], f[1], f[2]))

def reason(rel, what):
    if (rel, what) in DECLARED: return DECLARED[(rel, what)]
    for fre, wre, why in PATTERNS:
        if re.search(fre, rel) and re.search(wre, what): return why
    return None

def main():
    found = findings()
    undeclared = [f for f in found if reason(f[0], f[2]) is None]
    if "--list" in sys.argv:
        for rel, ln, what, text in found:
            print(f"{rel}:{ln}  {what:22} {reason(rel, what) or 'UNDECLARED'}")
    print(f"no_caps: {len(found)} findings, {len(found) - len(undeclared)} declared, {len(undeclared)} undeclared")
    if undeclared:
        for rel, ln, what, text in undeclared:
            print(f"  UNDECLARED {rel}:{ln}  {what}   {text}")
        print("  a new hardcoded limit: derive it from the data, or declare it above with a reason")
        return 1
    print("no_caps: OK (every fixed-size scratch and numeric guard is structural or has a stated reason)")
    return 0

if __name__ == "__main__":
    sys.exit(main())
