/* ============================================================================
 * native.c -- the C-EMITTING driver: one compiled call per arithmetic cone.
 *
 * Everything before this driver INTERPRETS.  The core's four rules rewrite the
 * graph, and arith's `_op` fold computes ONE op per redex: it forces each operand
 * through a reduction of its own and rebuilds every intermediate result as a
 * Scott numeral in the net (2(k+1) nodes per number).  For a cone -- a saturated
 * `_op` whose operands are themselves `_op` redexes or literals -- this driver
 * emits the whole tree as a single C expression, invokes cc once, caches the
 * shared object on disk by content hash, and folds every op in it with one call.
 * The intermediate results never become net structure at all.
 *
 * WHAT IS READ, AND WHAT IS DELIBERATELY NOT
 *
 * The operand LIST is itself a compiled application: `wire(app,2)` names a thunk
 * (measured: a nameless APP whose reduction builds the `_cl` cons chain), so the
 * spine has to be forced before it can be walked -- which is what
 * `net_spine_slots`, the core's operand-shape authority, does.  So the driver
 * forces the SPINE, exactly as the interpreted fold does, and then reads the
 * OPERANDS without forcing them: that is the difference that pays, because an
 * operand is where the boxing and the per-operand reduction entry live.  A cone
 * whose operands are not readable as structure is not compiled at all.
 *
 * WHY THIS IS SOUND RATHER THAN A SECOND IMPLEMENTATION THAT CAN DRIFT
 *
 *   - THE NET STAYS THE SOURCE OF TRUTH.  The driver computes a value the
 *     interpreter would also compute, from structure it reads out of the net, and
 *     rewrites the SAME redex the `_op` fold rewrites.  Nothing is baked: the C is
 *     compiled once, the VALUE is computed at run time.
 *
 *   - THE MATH IS NEVER RE-IMPLEMENTED.  The compiled expression is the shared
 *     table's own line (std/drivers/arith.c) copied verbatim -- including
 *     `lin_sub`'s saturating form `a >= b ? a-b : 0` and `lin_mod`'s zero guard --
 *     and the fallback calls that same table through `lin_arith_scalar`.  A driver
 *     that assumed `sub` meant `a-b` would be wrong for every operand pair, which
 *     is exactly why the whitelist carries the expression, not just the name.
 *
 *   - A CONE THAT DOES NOT DECOMPILE COSTS NOTHING.  It falls back to what arith
 *     would have done for that redex (force the operands, resolve through the
 *     table) and, if even that cannot fold, hands the pair to the core's own beta
 *     rather than stranding it.  The fallback is the OLD path, not a new one.
 *
 *   - THE REDUNDANT INNER FOLD DISAPPEARS BY CONSTRUCTION.  Folding the outside op
 *     kills the operand spine (`nat_kill(aa)`), and net_sever's cascade reclaims
 *     whatever loses its last live connection -- so the inner redexes go with it,
 *     and arith's per-pair `dead` guard skips its slice entries for them.  Without
 *     that, compiling the tree would save nothing: the inner ops would still be
 *     folded one at a time, boxed and read back.
 *
 * RECOGNITION IS PATTERNS, ACTION IS THE DRIVER'S
 *
 * What this driver RECOGNIZES -- the `_op` redex, its operand list, the numeral
 * normal form, the wrapper that stands between a slot and its operand -- is written
 * as patterns from the shared matcher (std/runtime/pattern.h), because that
 * recognition is the same walk every driver needs: range and `dead[]` checks, tag and
 * carrier tests, `_cl` spines, and a bound that keeps a cyclic net from spinning it.
 * What this driver DOES stays here, because doing is mutation: `fire_wrapper` fires
 * one interaction, `fold_cone` rewrites the redex, `compile_expr` builds and caches a
 * shared object.  The matcher is PURE -- it never forces and never rewrites -- so the
 * one place forcing is needed (the operand list is a compiled application until
 * something walks it) is the driver's, and that is exactly the retry in `emit_once`:
 * force with net_spine_slots, the interpreter's own operand-shape authority, then
 * re-match.  Nothing about patterns reaches the core: a pattern is a plugin's data.
 *
 * LIN_NATIVE_DEBUG traces the decision path (compiled / declined / no compiler).  A
 * driver that silently declines is otherwise indistinguishable from one that is not
 * loaded, which is the failure mode worth being able to see.
 * ==========================================================================*/
#include "../../src/lin.h"
#include "../runtime/pattern.h"
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <dlfcn.h>

static int dbg;
#define DBG(...) do { if (dbg) { fprintf(stderr, "native: " __VA_ARGS__); fflush(stderr); } } while (0)

#define NAT_IN(n, i) ((i) >= 0 && (i) < (n)->nn)
static inline Port wire_at(const Net *n, int node, int port) { return n->wire[node * 3 + port]; }
/* PURE: which head is this redex's LAM?  An `_ffi` closure's body is the `_ret` binder that applies
   the head to itself (the header SHAPE, std/runtime/pattern.h); an `_op` head's body is its pure
   fallback BODY.  A net carries no label, so this difference of shape is the whole of what a
   name-free net can say -- `ctor_tag(nmof(n, lam))` is what this used to read. */
static int head_is_ffi(const Net *n, int lam) {
  LinMatch m;
  return lin_pat_match((Net *)n, (Port){lam, 0}, lin_pat_enc_ffi, LIN_PAT_BUDGET_FOR(n), &m);
}

/* The scalar-table row an `_op` redex names: the OPERATOR INDEX is the FIRST SLOT of its operand list
   (std/num.lin writes it; LIN_OP_* in pattern.h is the enumeration), and the OPERANDS are that
   cell's tail.  FORCING -- reading the list demands it -- so this is `reduce`'s question, never
   `claim`'s. */
/* arity 2, integer result, PURE, and the C helper it compiles to.  Comparisons
   return bool (a different value kind, so they would need kind tracking through the
   cone) and every `lin_f*` float op stays with arith. */
static const char *op_helper(const char *fn) {
  if (!strncmp(fn, "lin_add", 8)) return "n_add";
  if (!strncmp(fn, "lin_sub", 8)) return "n_sub";
  if (!strncmp(fn, "lin_mul", 8)) return "n_mul";
  if (!strncmp(fn, "lin_div", 8)) return "n_div";
  if (!strncmp(fn, "lin_mod", 8)) return "n_mod";
  if (!strncmp(fn, "lin_pow", 8)) return "n_pow";
  return NULL;
}

/* The OPERATOR and its OPERANDS, read in ONE step: the index is the head of the operand list's first
   cell and the operands are that cell's tail, so reading the cell twice is not the same as reading it
   once -- the first read FORCES the list into being and a force re-aims the port it fired on (an
   `add` whose list was read twice folded with the OPERATOR INDEX as its first operand).  FORCING,
   which is why `claim` never calls this. */
static int op_head_of(Net *n, int app, const char **fn, Port *ops) {
  Port head, tail;
  *fn = NULL;
  *ops = (Port){-1, 0};
  if (!NAT_IN(n, app) || n->dead[app] || n->tag[app] != APP) return 0;
  if (!net_read_cell(n, wire_at(n, app, 2), &head, &tail)) return 0;
  *fn = lin_op_fn((int)net_read_int(n, head, LIN_ENC_NUM));
  *ops = tail;
  return *fn != NULL;
}

/* every scalar operand of an `_op`/`_ffi` is a NUMBER */
static const int DOMS_NUM[1] = { DT_NUM };

/* The helpers are the table's own lines from std/drivers/arith.c, verbatim, so the
   compiled cone and the interpreted fold cannot disagree: the only difference
   between the two paths is WHEN the arithmetic is done, not what it is. */
static const char *PRELUDE =
  "static long n_add(long a, long b) { return a + b; }\n"
  "static long n_sub(long a, long b) { return a >= b ? a - b : 0; }\n"
  "static long n_mul(long a, long b) { return a * b; }\n"
  "static long n_div(long a, long b) { return b ? a / b : 0; }\n"
  "static long n_mod(long a, long b) { return b ? a % b : 0; }\n"
  "static long n_pow(long b, long e) { long r = 1; while (e > 0) { if (e & 1) r *= b; b *= b; e >>= 1; } return r; }\n";

/* ---- emitting the cone ---------------------------------------------------- */

typedef struct { char *s; size_t cap; int len; } Buf;
static void put(Buf *b, const char *fmt, ...) {
  if (b->len < 0 || (size_t)b->len >= b->cap) { b->len = -1; return; }
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(b->s + b->len, b->cap - (size_t)b->len, fmt, ap);
  va_end(ap);
  if (n < 0 || (size_t)n >= b->cap - (size_t)b->len) { b->len = -1; return; }
  b->len += n;
}

/* ---- the shapes this driver recognizes, as DATA ---------------------------
 *
 * A pattern says what a recognition MEANS: mutual principal wiring is P_AT(0, ...)
 * after P_PORT(0, ...), "the same node" is P_REF, "the operand list" is P_SPINE,
 * "hop the fan" is P_FAN.  The matcher owns the parts that are easy to get wrong --
 * range and `dead[]` checks on every index taken from the net, a budget, termination
 * on a cyclic net -- and it is PURE, so a pattern can be run from `claim` (where
 * forcing would move the net out from under the wave) as well as from `reduce`.
 */

/* An `_op` redex: a live APP at a PRINCIPAL port (slot 1) whose port-0 wire arrives at
   the principal port of a live LAM (slot 0) that wires back to the APP -- mutual
   principal wiring, which is what a redex is.  No whitelist: this is the pair reduce
   must still see when the operator is one this driver does not compile, so that it can
   fall back to the interpreted table fold. */
static const LinPat *const P_OP_PAIR = P_AT(0, P_ALL(
  P_BIND(1),
  P_ALL(P_TAG(APP),
    P_PORT(0, P_AT(0, P_ALL(
      P_BIND(0),
      P_ALL(P_TAG(LAM), P_PORT(0, P_AT(0, P_REF(1))))))))));

/* A consumer's view of an unforced op redex: the value is observed at the APP's result
   port, so the root arrives at port 1.  Binds 0 = the LAM, 1 = the APP. */
static const LinPat *const P_CONE_RESULT = P_FAN(P_AT(1, P_ALL3(
  P_BIND(1), P_TAG(APP),
  P_PORT(0, P_AT(0, P_ALL3(P_BIND(0), P_TAG(LAM), P_OP_HEAD))))));

/* A closure whose principal is observed directly: an op LAM whose port 0 arrives at an
   APP's principal.  Binds 0 = the LAM, 1 = the APP. */
static const LinPat *const P_CONE_PRINCIPAL = P_FAN(P_AT(0, P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_ALL(P_OP_HEAD, P_PORT(0, P_AT(0, P_ALL(P_BIND(1), P_TAG(APP))))))));

/* fire_wrapper's three recognitions of an APP standing in the way.  Its port-0 wire
   either arrives at a LAM that is NOT this driver's operator (fire that β), at one that
   IS (stop: folding it is what compiling the cone replaces), or at another APP's port 1
   (one layer deeper into the application spine). */
static const LinPat *const P_IS_APP = P_TAG(APP);
static const LinPat *const P_WRAP_BETA = P_ALL(P_TAG(APP),
  P_PORT(0, P_AT(0, P_ALL(P_BIND(0),
    P_ALL(P_TAG(LAM), P_NOT(P_OP_HEAD))))));
static const LinPat *const P_WRAP_OP = P_ALL(P_TAG(APP),
  P_PORT(0, P_AT(0, P_ALL(P_TAG(LAM), P_OP_HEAD))));
static const LinPat *const P_SPINE_LINK = P_ALL(P_TAG(APP),
  P_PORT(0, P_AT(1, P_ALL(P_BIND(0), P_TAG(APP)))));

/* A port reached through a DUP chain: the value-level view fire_wrapper starts from. */
static const LinPat *const P_DHOP = P_FAN(P_BIND(0));

/* The operand list READ AS STRUCTURE: the slots of the `_cl` spine at `argp` and how
   many there are (-1: not a spine), collecting at most `max` slot ports.  A `_cl` spine
   is `\c.\n.((c h) t)` per cell (std/num.lin's `_cl_cons`), and the walk stops where the
   cell chain stops, exactly as the core's own spine walkers do.  The matcher never
   forces: a list that is still an unbuilt application is NOT a spine yet, so the caller
   forces it first (net_spine_slots) and calls this again. */
static int spine_slots(Net *n, Port argp, Port *out, int max) {
  LinMatch m;
  int cap = max < LIN_PAT_SLOTS ? max : LIN_PAT_SLOTS;
  if (!lin_pat_match(n, argp, P_SPINE(P_ANY), LIN_PAT_BUDGET_FOR(n), &m)) return -1;
  for (int i = 0; i < m.nslots && i < cap; i++) out[i] = m.slots[i];
  return m.nslots < cap ? m.nslots : cap;
}

static int emit_redex(Net *n, int app, Buf *b, int budget, int depth);
static int emit_once(Net *n, int app, Buf *b, int budget, int depth);

/* Fire ONE beta redex standing between a slot and the operand behind it.
 *
 * An operand is not reachable as structure in one step: the operand list is built by
 * a chain of applications (measured: a slot holds a nameless APP whose port 1 is a
 * DUP, i.e. a wrapper the spine's construction left behind), so the value the slot
 * names has to be produced before the operand's own redex is visible.  `net_force`
 * would produce it AND everything behind it, folding the operand into a numeral --
 * exactly the boxing this driver exists to avoid.  A single `net_interact` on the
 * wrapper is the surgical alternative: beta is lazy, so the operand comes out
 * unevaluated and still compilable, and firing it is a legal core interaction the
 * interpreter would take anyway (confluence makes that free).  Returns 1 if it fired.
 *
 * The RETRY LOOP is the driver's, because firing is mutation: the matcher can say
 * "this is an APP whose port-0 wire arrives at a non-operator LAM", but only the
 * driver may fire the pair.
 */
static int fire_wrapper(Net *n, int app) {
  Port slots[LIN_PAT_SLOTS];
  int ns = spine_slots(n, wire_at(n, app, 2), slots, LIN_PAT_SLOTS);
  for (int i = 0; i < ns; i++) {
    /* Descend the application spine the slot heads: the value is the result of a
       chain of applications, and the redex that produces the next layer is the one
       whose principal is a LAM.  An `_op` head is the operand itself, so it is never
       fired -- folding it is what the compile is here to replace. */
    LinMatch mv;
    if (!lin_pat_match(n, slots[i], P_DHOP, LIN_PAT_BUDGET_FOR(n), &mv)) continue;
    Port v = mv.bind[0];
    for (int step = 0; step < 8; step++) {
      if (!lin_pat_match(n, v, P_IS_APP, LIN_PAT_BUDGET_FOR(n), &mv)) break;
      if (lin_pat_match(n, v, P_WRAP_OP, LIN_PAT_BUDGET_FOR(n), &mv))
        break;                                           /* the operand's own redex: stop */
      if (lin_pat_match(n, v, P_WRAP_BETA, LIN_PAT_BUDGET_FOR(n), &mv)) {
        if (net_interact(n, mv.bind[0], (Port){v.node, 0})) {
          n->steps++;
          DBG("    fired spine beta %d x %d\n", mv.bind[0].node, v.node);
          return 1;
        }
        break;
      }
      if (!lin_pat_match(n, v, P_SPINE_LINK, LIN_PAT_BUDGET_FOR(n), &mv))
        break;                                           /* not a spine link */
      v = mv.bind[0];                                    /* one layer deeper */
    }
  }
  return 0;
}

/* Emit the redex, firing wrappers when they are what stands in the way -- AT EVERY
   LEVEL.  A cone is only compilable once each op in it can see its operands, and a
   child's operands are as wrapped as the outer's were (measured: the slot exposes the
   child's redex, and the child then reports its own list unreadable), so the retry
   belongs here rather than only at the top.  Each round fires one interaction the
   interpreter would have taken anyway, and the bound keeps a pathological cone from
   walking the net; failing after it costs nothing, because reduce falls back. */
static int emit_redex(Net *n, int app, Buf *b, int budget, int depth) {
  for (int round = 0; round < 6; round++) {
    int mark = b->len;
    if (emit_once(n, app, b, budget, depth)) {
      if (round) DBG("    exposed after %d fire(s)\n", round);
      return 1;
    }
    b->len = mark;                                   /* drop the partial expression */
    if (b->len < 0) return 0;
    if (!fire_wrapper(n, app)) return 0;
  }
  return 0;
}

/* Emit the C expression for the value observed at `p` (the convention every reader in
   src/io.c uses: `p.node` names the value node).

   Three shapes, three patterns: a numeral that is already a normal form (read
   STRUCTURALLY -- forcing it here would be the boxing this driver exists to avoid),
   an unevaluated op redex seen at its APP's result port, or an op closure whose
   principal is observed directly.  Both redex shapes hand the driver the LAM and the
   APP the pattern recognized, so nothing here re-reads the wires to find them. */
static int emit_cone(Net *n, Port p, Buf *b, int budget, int depth) {
  if (budget <= 0 || depth > 16) { DBG("    cone: budget/depth\n"); return 0; }
  long k;
  LinMatch m;
  if (lin_pat_num_nf(n, p, &k)) { put(b, "%ldL", k); return b->len >= 0; }
  if (lin_pat_match(n, p, P_CONE_RESULT, LIN_PAT_BUDGET_FOR(n), &m))
    return emit_redex(n, m.bind[1].node, b, budget - 1, depth + 1);
  if (lin_pat_match(n, p, P_CONE_PRINCIPAL, LIN_PAT_BUDGET_FOR(n), &m))
    return emit_redex(n, m.bind[1].node, b, budget - 1, depth + 1);
  DBG("    cone: no op redex at %d.%d\n", p.node, p.port);
  return 0;
}

/* One pass: recognize the redex and read its operand list as structure, then emit
   `<helper>(<operand>, <operand>)`.

   The redex itself is recognized FIRST, without touching the net: a pair this driver
   does not compile must cost nothing, exactly as it did when the check was inline.

   The operand LIST has to exist before it can be read, at EVERY level and not just at the
   one the wave handed us: a child's operands are as unbuilt as the outer's were, which is
   why a cone read only one op deep used to be all this driver could compile.  The matcher
   is pure and will not build it, so when the structural read declines the DRIVER forces
   the list with net_spine_slots -- the interpreter's own operand-shape authority, which
   forces the list and its cells and never the operands -- and matches again.  `argp` is
   captured ONCE and re-read after that force, which is the interpreter's own discipline:
   forcing can consume the node the port names (pair_boundary re-aims the consumer's end),
   so re-reading the wire instead would let a cone compile out of a net that has moved
   underneath the read.  Pure read, then force, then pure read, then emit. */
static int emit_once(Net *n, int app, Buf *b, int budget, int depth) {
  if (budget <= 0 || depth > 16) return 0;
  LinMatch m;
  if (!lin_pat_match(n, (Port){app, 0}, P_OP_PAIR, LIN_PAT_BUDGET_FOR(n), &m)) return 0;
  int lam = m.bind[0].node;
  const char *fnp;
  Port argp;
  if (!op_head_of(n, app, &fnp, &argp)) return 0;
  const char *h = op_helper(fnp);
  if (!h) return 0;
  Port slots[LIN_PAT_SLOTS];
  int ns = NAT_IN(n, argp.node) ? spine_slots(n, argp, slots, LIN_PAT_SLOTS) : -1;
  if (ns != 2 && NAT_IN(n, argp.node) && net_spine_slots(n, argp) == 2)
    ns = spine_slots(n, argp, slots, LIN_PAT_SLOTS);
  DBG("  redex lam %d app %d: spine slots %d\n", lam, app, ns);
  /* Exactly the arity the table reads: arith passes the whole spine and uses a[0],
     a[1], so anything else is a shape this driver does not model and declines. */
  if (ns != 2) return 0;
  put(b, "%s(", h);
  if (!emit_cone(n, slots[0], b, budget - 2, depth + 1)) return 0;
  put(b, ", ");
  if (!emit_cone(n, slots[1], b, budget - 2, depth + 1)) return 0;
  put(b, ")");
  return b->len >= 0;
}

/* ---- the JIT: content-hashed source, compiled once, cached on disk --------- */

#define FN_CACHE 256
static struct { unsigned long h, hp; long (*fn)(void); } fns[FN_CACHE];
static int nfns;

static unsigned long fnv1a(const char *s) {
  unsigned long h = 1469598103934665603UL;
  for (; *s; s++) { h ^= (unsigned char)*s; h *= 1099511628211UL; }
  return h;
}

static int mkdir_p(const char *path) {
  char tmp[4096];
  snprintf(tmp, sizeof tmp, "%s", path);
  for (char *p = tmp + 1; *p; p++)
    if (*p == '/') { *p = 0; mkdir(tmp, 0700); *p = '/'; }
  return mkdir(tmp, 0700) == 0 || access(path, F_OK) == 0;
}

static const char *cache_dir(char *out, size_t n) {
  const char *env = getenv("LIN_NATIVE_CACHE");
  if (env && env[0]) { snprintf(out, n, "%s", env); return out; }
  const char *xdg = getenv("XDG_CACHE_HOME");
  const char *home = getenv("HOME");
  if (xdg && xdg[0]) snprintf(out, n, "%s/lin/native", xdg);
  else if (home && home[0]) snprintf(out, n, "%s/.cache/lin/native", home);
  else snprintf(out, n, "/tmp/lin-native-%u", (unsigned)getuid());
  return out;
}

/* Run the compiler with no shell involved: the source text is generated, but the
   cache path may come from the environment, so it must never reach a shell. */
static int run_cc(const char *src, const char *so) {
  const char *cc = getenv("LIN_NATIVE_CC");
  if (!cc || !cc[0]) cc = "cc";
  pid_t pid = fork();
  if (pid < 0) return 0;
  if (pid == 0) {
    execlp(cc, cc, "-O2", "-w", "-fPIC", "-shared", "-o", so, src, (char *)NULL);
    _exit(127);
  }
  int st = 0;
  if (waitpid(pid, &st, 0) < 0) return 0;
  return WIFEXITED(st) && WEXITSTATUS(st) == 0;
}

/* Build (or find) the shared object for `expr` and return its function.  NULL means
   "cannot compile here" -- no compiler, no cache directory, a rejected build -- and
   the caller then takes the interpreted fallback, so a machine without cc runs
   exactly the old path instead of failing. */
static long (*compile_expr(const char *expr))(void) {
  /* The name comes from the EXPRESSION and the file name also from the PRELUDE, so
     editing the helpers above cannot resurrect an object compiled from the old ones.
     The symbol must have external linkage (dlsym cannot see a `static` function) and
     be unique per cone, which is what lets every object be loaded RTLD_LOCAL even
     though they all export a symbol of the same shape. */
  unsigned long he = fnv1a(expr), hp = fnv1a(PRELUDE);
  for (int i = 0; i < nfns; i++)
    if (fns[i].h == he && fns[i].hp == hp) return fns[i].fn;
  char sym[64];
  snprintf(sym, sizeof sym, "lin_cone_%016lx", he);
  char full[8192];
  int n = snprintf(full, sizeof full, "%s\nlong %s(void) { return %s; }\n", PRELUDE, sym, expr);
  if (n < 0 || (size_t)n >= sizeof full) return NULL;

  char dir[4096], so[4200], c[4200];
  cache_dir(dir, sizeof dir);
  snprintf(so, sizeof so, "%s/%016lx-%016lx.so", dir, he, hp);
  snprintf(c, sizeof c, "%s/%016lx-%016lx.c", dir, he, hp);
  void *hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
  if (!hnd) {
    if (!mkdir_p(dir)) { DBG("no cache directory %s\n", dir); return NULL; }
    char tmp[4300];
    snprintf(tmp, sizeof tmp, "%s.%d.tmp", c, (int)getpid());
    FILE *f = fopen(tmp, "wb");
    if (!f) return NULL;
    if (fwrite(full, 1, (size_t)n, f) != (size_t)n) { fclose(f); remove(tmp); return NULL; }
    fclose(f);
    if (rename(tmp, c) != 0) { remove(tmp); return NULL; }
    if (!run_cc(c, so)) {
      DBG("compiler '%s' rejected %s\n", getenv("LIN_NATIVE_CC") ? getenv("LIN_NATIVE_CC") : "cc", c);
      return NULL;
    }
    hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
    if (!hnd) { DBG("cannot dlopen %s\n", so); return NULL; }
  }
  long (*fn)(void) = (long (*)(void))(intptr_t)dlsym(hnd, sym);
  if (!fn) { DBG("no symbol %s in %s\n", sym, so); return NULL; }
  if (nfns < FN_CACHE) { fns[nfns].h = he; fns[nfns].hp = hp; fns[nfns].fn = fn; nfns++; }
  return fn;
}

/* ---- the fold (ports of arith's fold_op_head / val_to_port) ---------------- */

static Port val_port(Net *n, const Val *v) {
  if (v->kind == 3) return net_alloc_bool(n, (int)v->iv);
  if (v->kind == 4) { double d; memcpy(&d, &v->iv, 8); return net_alloc_float(n, d); }
  return net_alloc_scott(n, v->iv);
}

static void nat_kill(Net *n, int v) {
  if (!NAT_IN(n, v) || n->dead[v] || n->tag[v] == DUP) return;
  for (int p = 0; p < 3; p++) net_sever(n, (Port){v, p});
  n->dead[v] = 1;
}

/* Inject the value where the fold injects it: into `ar`, the APP's body-slot partner,
   and BEFORE anything is severed -- severing `app`'s result port removes `ar`'s
   connection, and with the cascade a consumer that just lost its last live connection
   would be reclaimed as garbage (measured in arith: linking afterwards handed the
   value to a freed consumer, and every FFI suite came back unreduced). */
static void fold_cone(Net *n, int lam, int app, const Val *v) {
  Port res = val_port(n, v);
  Port ar = wire_at(n, app, 1);
  if (NAT_IN(n, ar.node) && !n->dead[ar.node]) net_link(n, res, ar, 1);
  else net_link(n, res, (Port){app, 1}, 1);
  nat_kill(n, lam); nat_kill(n, app);
  /* The β-body and the operand spine are NOT this redex's to sever -- `(\x BODY)` copied by a fan
     still reads as a plain LAM, so cutting the body here reaches structure a sibling redex still
     reads.  `app`'s operand port already detaches the spine, and the reachability GC reclaims the
     rest.  arith's fold_op_head keeps the same rule; the differential with it is what enforces it. */
  lin_fold_bump();
}

/* IS THIS REDEX'S RESULT SHARED BY A COPY FAN?  β joins the closure's body port to the APP's result
   port, so a live fan on EITHER is the fan a DUPLICATION left at the body of a closure whose copies
   each carry their OWN argument -- and that body graph is OPEN, so the copies do not compute the same
   value.  Injecting one computed value through that port hands it to BOTH.  A VALUE fan (one feeding
   application slots) is not this case and still compiles.
   arith.c's result_shared is the authority -- this driver must agree with the interpreted fold
   EXACTLY, and test/native_cone.sh's differential is what says so. */
static int result_shared(const Net *n, int lam, int app) {
  const Port p[2] = { wire_at(n, lam, 2), wire_at(n, app, 1) };
  for (int i = 0; i < 2; i++) {
    int f = p[i].node;
    if (!NAT_IN(n, f) || n->dead[f] || n->tag[f] != DUP) continue;
    for (int a = 1; a <= 2; a++) {
      Port w = wire_at(n, f, a);
      if (!NAT_IN(n, w.node) || n->dead[w.node]) continue;
      if (n->tag[w.node] == DUP) return 1;                    /* the copy fans on to another copy */
      if (n->tag[w.node] == LAM && w.port == 2) return 1;     /* the fan feeds another copy's BODY */
    }
  }
  return 0;
}

/* ---- the interpreted fallback --------------------------------------------- */

/* The shared semantic table lives in arith.so, and it is reached THROUGH THE CORE'S REGISTRY
   (`lin_scalar_ops_run`), never by dlsym'ing the provider's symbol: the registry is where a provider
   states whether a call to it is a function of its operands alone, so routing every call through it is
   what makes that declaration authoritative -- a driver that resolved the symbol itself would perform
   calls the provider never vouched for as pure, which a build may not do. */

/* Exactly what the arith driver's op_eval does: force the operands (through the
   shared decoder, which demands each slot), then resolve the math through the one
   table.  Used whenever the cone could not be compiled, so a decline costs the
   interpreted path and nothing more.  `argp` is the OPERAND LIST the caller already
   read (past the operator index): re-reading the cell here would force it a second
   time and land on a different one. */
static int fold_via_table(Net *n, const char *fn, Val *v, Port argp) {
  int slots = net_spine_slots(n, argp);
  if (slots < 1 || slots > 8) return 0;
  Val fargs[8];
  memset(fargs, 0, sizeof fargs);
  int argc = net_spine_args(n, argp, DOMS_NUM, 1, fargs, 8);
  if (argc < slots) return 0;
  long c[8] = {0};
  for (int i = 0; i < slots; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return 0;
    c[i] = fargs[i].iv;
  }
  long out = 0; int okind = 0;
  if (!lin_scalar_ops_run(fn, slots, c, &out, &okind)) return 0;
  v->kind = okind == 4 ? 4 : (okind == 3 ? 3 : 1);
  v->iv = out;
  return 1;
}

/* ---- LinDriver hooks ------------------------------------------------------ */

/* claim: a `_op` closure redex whose op has a compiled form.  Deliberately CHEAP and
   not exact: whether the cone decompiles cannot be known here, because the operand
   list is a thunk that has to be forced before it can be read, and `claim` runs before
   any driver's reduce, building the wave's snapshot and every slice from the net as it
   stands -- so it must not touch it.  Disposing of a claimed pair is `reduce`'s job,
   and it always can: compile it, fold it through the table, or hand it to β.

   The recognition is a pattern, and it is the same one `reduce` starts from -- which is
   what keeps the two from drifting.  The matcher is PURE (this is the hook where that
   matters most: it never forces and never allocates, so calling it here cannot move the
   net out from under the wave). */
static int native_claim(const Net *ncn, Port p1, Port p2) {
  Net *n = (Net *)ncn;
  LinMatch m;
  /* The pair is recognized BY SHAPE and the WHICH is left to `reduce`: the whitelist lives in the
     operand list, which is an unbuilt application until something walks it, so gating the claim on
     it would either force the net out from under the wave (illegal here) or decline every freshly
     compiled redex -- the fold would never fire at all.  `reduce` disposes of everything claimed
     (compile it, fold it through the table, or hand it to β), which is what makes this safe. */
  if (!lin_pat_match_pair(n, p1, p2, P_OP_PAIR, LIN_PAT_BUDGET_FOR(n), &m)) return 0;
  int lam = m.bind[0].node;
  if (head_is_ffi(n, lam)) return 0;      /* an `_ffi` closure is the arith driver's fold */
  return lin_pat_op_head(n, (Port){lam, 0}, NULL);
}

/* reduce: fold every claimed pair, one way or another.  A claimed-but-unhandled pair
   would be dropped from the wave and stranded, so the three exits below are the whole
   contract: compiled, interpreted, or handed to the core's beta. */
static int native_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int done = 0;
  for (int i = 0; i < nred; i++) {
    if (limit > 0 && (long)n->steps >= limit) break;
    Port pa = redexes[2 * i], pb = redexes[2 * i + 1];
    /* Which of the two ports is the APP, whether both are live, whether the wiring is
       principal-to-principal and mutual: all of it is the pattern, so the pair that
       reaches the emit path below is the pair the pattern recognized -- and the
       operator name is derived from the LAM the pattern found, never guessed. */
    LinMatch m;
    if (!lin_pat_match_pair(n, pa, pb, P_OP_PAIR, LIN_PAT_BUDGET_FOR(n), &m))
      continue;                        /* an earlier fold in this wave took it, or not ours */
    int lam = m.bind[0].node, app = m.bind[1].node;
    const char *fnp;
    Port args;
    /* The operator's index is not readable YET (its list is an unbuilt application): this is the
       WAIT case, not a decline, so the pair goes back to the core's β rather than being dropped --
       a claimed pair that nothing disposes of is stranded, which is what the fold rule above warns
       about.  The next wave sees the list built. */
    if (!op_head_of(n, app, &fnp, &args)) {
      /* A def is precompiled with its operands still FREE, so its list cannot be a list yet and the
         operator is genuinely unreadable -- leave the redex alone, exactly as the un-foldable case
         below does, or the baked net would lose the fold it exists for. */
      if (lin_precompile_depth > 0) continue;
      if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
      continue;
    }
    /* A shared result is not this driver's to compute once: hand the pair to the core's β, the same
       exit the unreadable operator takes below.  (Precompile leaves the redex alone, as always.) */
    if (result_shared(n, lam, app)) {
      if (lin_precompile_depth > 0) continue;
      if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
      continue;
    }
    char fn[64];
    snprintf(fn, sizeof fn, "%s", fnp);

    /* Reading the operand LIST is what demands the spine -- it is a compiled
       application until something walks it -- and this is where the interpreted fold
       pays that cost too.  Only the spine is forced here; the operands are read as
       structure below, and forced only if that fails. */
    Port argp = args;
    int slots = NAT_IN(n, argp.node) ? net_spine_slots(n, argp) : -1;

    Val v;
    memset(&v, 0, sizeof v);
    int have = 0;
    const char *h = op_helper(fn);
    if (h && slots == 2) {
      char expr[2048];
      Buf b = { expr, sizeof expr, 0 };
      if (emit_redex(n, app, &b, 64, 0)) {
        long (*f)(void) = compile_expr(expr);
        if (f) { v.kind = 1; v.iv = f(); have = 1; DBG("compiled %s = %ld\n", expr, v.iv); }
      } else {
        DBG("declined lam %d ('%s'): operand cone not readable as structure\n", lam, fn);
      }
    }
    if (!have && fold_via_table(n, fn, &v, argp)) { have = 1; DBG("table fold %s = %ld\n", fn, v.iv); }
    if (have) {
      fold_cone(n, lam, app, &v);
      done++; (*changed)++; n->steps++;
      continue;
    }
    /* A def is precompiled with its operands still FREE, so a foldable redex can never
       be ready there; leaving it alone is what keeps the fold in the baked net (beta-ing
       it would replace the `_op` head with the pure-Lin body, and every later use of
       the def -- and the artifact itself -- would have lost the redex the fold exists
       for). */
    if (lin_precompile_depth > 0) continue;
    if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
  }
  return done;
}

/* ---- registration --------------------------------------------------------- */
LinDriver lin_native_driver;
static void __attribute__((constructor)) native_load(void) {
  dbg = getenv("LIN_NATIVE_DEBUG") != NULL;
  static int registered = 0;
  if (registered) return;
  registered = 1;
  DBG("registered (priority %d)\n", lin_native_driver.priority);
  lin_driver_add(&lin_native_driver);
}

LinDriver lin_native_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),   /* the ABI-5 extension contract: the core reads only these fields */
  .name = "native", .description = "C-emitting driver: compiles an arithmetic cone into one call",
  .caps = LIN_CAP_NATIVE_NUM | LIN_CAP_PREEMPT, .priority = 4,   /* ahead of arith(5): claim the cone */
  .claim = native_claim, .reduce = native_reduce,
};
