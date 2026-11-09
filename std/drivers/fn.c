/* ============================================================================
 * fn.c -- the FUNCTION COMPILER: a whole recursive function, compiled to C from its net.
 *
 * native.c compiles one arithmetic cone at a time; this driver compiles the FUNCTION.  It
 * watches for the one redex every recursive call starts with -- the fixpoint `Y` applied to
 * a functional `F = \self.\p1..\pk. body`, the result applied to k arguments -- and when it
 * can, it replaces the whole call by its value, computed by C.
 *
 * WHAT IT READS, AND HOW.  Nothing about the net is labelled, so F is read by EVALUATING it:
 * a call-by-need evaluator walks F's own net with the parameters as SYMBOLS and the self
 * binder as SELF, and what it gets back is the function's meaning as an expression:
 *   - an `_op` head applied to its operand list (std/num.lin) is that operation (the operator
 *     index is the list's first slot, exactly as every fold driver reads it);
 *   - a symbolic boolean applied to two values is a conditional -- both branches are compiled,
 *     only one runs, as in the net;
 *   - SELF applied to k arguments is a recursive call;
 *   - a constant numeral is decoded by applying it to markers (its cells and its sign terminal).
 * Anything else -- an FFI call, a self reference that escapes, a value that is not a number --
 * makes the evaluator DECLINE, and the redex goes to the core's beta unchanged.
 *
 * WHY THIS IS THE SAME FUNCTION.  The integer semantics are std/runtime/i64.h's, which the
 * net's own arithmetic computes too (test/int64.sh); a conditional evaluates one branch, as
 * needed order does; and a call is compiled only when the function is STRICT in every
 * parameter (each is evaluated on every path), so forcing the arguments first is exactly what
 * the program would have done.  The net stays the authority: the call's result is written back
 * as a numeral, and what the call consumed is erased.
 *
 * LIN_FN_DEBUG=1 traces every decision and prints the C it compiles.
 * ==========================================================================*/
#include "../../src/lin.h"
#include "../runtime/pattern.h"   /* the op vocabulary (LIN_OP_*) */
#include "../runtime/i64.h"
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <dlfcn.h>

static int dbg = -1;
#define DBG(...) do { if (dbg) { fprintf(stderr, "fn: " __VA_ARGS__); fflush(stderr); } } while (0)
#define IN(n, i) ((i) >= 0 && (i) < (n)->nn)
#define NONE ((Port){-1, 0})
static inline Port W(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }
static inline int live(const Net *n, Port p) { return IN(n, p.node) && !n->dead[p.node]; }
static inline int is(const Net *n, Port p, int tag, int port) { return live(n, p) && n->tag[p.node] == tag && (int)p.port == port; }
/* The value a port carries: arriving at a fan's copy port means the value comes from its principal side. */
static Port dhop(const Net *n, Port p) {
  for (int k = 0; k < n->nn && live(n, p) && n->tag[p.node] == DUP && p.port != 0; k++) p = W(n, (Port){p.node, 0});
  return p;
}

/* ---- recognising the call ------------------------------------------------------------------- */
/* Y = \h. ((\x. h (x x)) (\x. h (x x))): the shape, read through fans (h and x are each used twice). */
static int y_half(const Net *n, Port x, int h) {
  if (!is(n, x, LAM, 0)) return 0;
  Port c = dhop(n, W(n, (Port){x.node, 2}));
  if (!is(n, c, APP, 1)) return 0;
  Port hv = dhop(n, W(n, (Port){c.node, 0}));
  if (hv.node != h || hv.port != 1) return 0;
  Port d = dhop(n, W(n, (Port){c.node, 2}));
  if (!is(n, d, APP, 1)) return 0;
  Port a = dhop(n, W(n, (Port){d.node, 0})), b = dhop(n, W(n, (Port){d.node, 2}));
  return a.node == x.node && a.port == 1 && b.node == x.node && b.port == 1;
}
static int is_y(const Net *n, int h) {
  if (!IN(n, h) || n->dead[h] || n->tag[h] != LAM) return 0;
  Port b = dhop(n, W(n, (Port){h, 2}));
  if (!is(n, b, APP, 1)) return 0;
  return y_half(n, dhop(n, W(n, (Port){b.node, 0})), h) && y_half(n, dhop(n, W(n, (Port){b.node, 2})), h);
}
/* The pair (h, appY), with appY = (Y F) consumed as a FUNCTION: is this a recursive call? */
static int y_call(const Net *n, Port p1, Port p2, int *h, int *appy, int *F) {
  if (p1.port || p2.port || !live(n, p1) || !live(n, p2)) return 0;
  int a = n->tag[p1.node] == LAM ? p1.node : p2.node, b = a == p1.node ? p2.node : p1.node;
  if (n->tag[a] != LAM || n->tag[b] != APP) return 0;
  Port f = dhop(n, W(n, (Port){b, 2}));
  if (!is(n, f, LAM, 0)) return 0;
  if (!is(n, W(n, (Port){b, 1}), APP, 0)) return 0;          /* (Y F) is applied to something */
  if (!is_y(n, a)) return 0;
  *h = a; *appy = b; *F = f.node;
  return 1;
}

/* ---- the evaluator --------------------------------------------------------------------------- */
enum { E_CONST, E_PARAM, E_BIN, E_IF, E_CALL };
typedef struct Expr { int op; long k; struct Expr *a, *b, *c; struct Expr **args; int nargs, kind; } Expr;   /* kind 1 int, 3 bool */
enum { V_CLO, V_SYM, V_C1, V_COND, V_SELF, V_MCONS, V_MCONS1, V_MCELL, V_MNIL };
struct Lz;
typedef struct Env { int lam; struct Lz *t; struct Env *next; } Env;
typedef struct V { int k; int lam; Env *env; Expr *e; struct Lz *a, *b; struct Lz **args; int nargs; } V;
typedef struct Lz { int state; Port p; Env *env; struct Lz *f, *x; V *v; int busy; } Lz;   /* 0 port, 1 application, 2 value */

/* One compile attempt's memory: everything is freed together. */
static void **arena; static int narena, arcap;
static void *A(size_t sz) {
  void *p = calloc(1, sz);
  if (narena >= arcap) arena = realloc(arena, (size_t)(arcap = arcap ? arcap * 2 : 1024) * sizeof *arena);
  arena[narena++] = p; return p;
}
static void arena_free(void) { for (int i = 0; i < narena; i++) free(arena[i]); narena = 0; }

static Net *N; static long fuel; static int failed; static int F_lam, arity;
static void fail(const char *why) { if (!failed) DBG("declined: %s\n", why); failed = 1; }

static V *mkv(int k) { V *v = A(sizeof *v); v->k = k; return v; }
static Lz *ready(V *v) { Lz *l = A(sizeof *l); l->state = 2; l->v = v; return l; }
static Lz *lzp(Port p, Env *e) { Lz *l = A(sizeof *l); l->state = 0; l->p = p; l->env = e; return l; }
static Lz *lzapp(Lz *f, Lz *x) { Lz *l = A(sizeof *l); l->state = 1; l->f = f; l->x = x; return l; }
static Expr *mke(int op, int kind) { Expr *e = A(sizeof *e); e->op = op; e->kind = kind; return e; }

static V *eval(Port p, Env *env);
static V *apply(V *f, Lz *x);
static V *force(Lz *l) {
  if (failed) return NULL;
  if (l->state == 2) return l->v;
  if (l->busy) { fail("a value that needs itself"); return NULL; }
  l->busy = 1;
  V *v = l->state == 0 ? eval(l->p, l->env) : apply(force(l->f), l->x);
  l->busy = 0;
  if (!v) { failed = 1; return NULL; }
  l->state = 2; l->v = v; return v;
}

static Expr *to_expr(V *v);
/* An `_op` head: \x. ((\k. B) x) with k unused, applied to its operand list (code, a, b). */
static int op_head(int lam) {
  Port q = W(N, (Port){lam, 2});
  if (!is(N, q, APP, 1)) return 0;
  Port k = dhop(N, W(N, (Port){q.node, 0})), x = dhop(N, W(N, (Port){q.node, 2}));
  if (!is(N, k, LAM, 0) || x.node != lam || x.port != 1) return 0;
  Port kb = W(N, (Port){k.node, 1});
  return kb.node < 0 || (live(N, kb) && N->tag[kb.node] == ERA);
}
static long const_int(V *v, int *ok);
static V *op_value(Lz *list) {
  V *l = force(list); if (!l) return NULL;
  Expr *slot[4]; int ns = 0; long code = -1;
  for (int i = 0; i < 5 && !failed; i++) {
    V *r = apply(apply(l, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) return NULL;
    if (r->k == V_MNIL) break;
    if (r->k != V_MCELL || ns >= 3) { fail("an operand list that is not a list"); return NULL; }
    if (i == 0) { int ok; code = const_int(force(r->a), &ok); if (!ok) { fail("operator index not constant"); return NULL; } ns++; }
    else { Expr *e = to_expr(force(r->a)); if (!e) return NULL; slot[ns - 1] = e; ns++; }
    l = force(r->b); if (!l) return NULL;
  }
  if (ns != 3 || code < 0 || code >= LIN_OP_N) { fail("not a binary integer op"); return NULL; }
  V *v = mkv(V_SYM);
  v->e = mke(E_BIN, (code >= LIN_OP_EQ && code <= LIN_OP_GEQ) ? 3 : 1); v->e->k = code; v->e->a = slot[0]; v->e->b = slot[1];
  return v;
}

static V *apply(V *f, Lz *x) {
  if (failed || !f) return NULL;
  if (--fuel < 0) { fail("out of fuel"); return NULL; }
  switch (f->k) {
  case V_CLO: {
    if (op_head(f->lam)) return op_value(x);
    Env *e = A(sizeof *e); e->lam = f->lam; e->t = x; e->next = f->env;
    return eval(W(N, (Port){f->lam, 2}), e);
  }
  case V_SYM: {
    if (f->e->kind != 3) { fail("an integer applied as a function"); return NULL; }
    V *v = mkv(V_C1); v->e = f->e; v->a = x; return v;
  }
  case V_C1: { V *v = mkv(V_COND); v->e = f->e; v->a = f->a; v->b = x; return v; }
  case V_COND: { V *v = mkv(V_COND); v->e = f->e; v->a = lzapp(f->a, x); v->b = lzapp(f->b, x); return v; }
  case V_SELF: {
    V *v = mkv(V_SELF); v->nargs = f->nargs + 1; v->args = A(sizeof(Lz *) * (size_t)v->nargs);
    memcpy(v->args, f->args, sizeof(Lz *) * (size_t)f->nargs); v->args[f->nargs] = x;
    if (v->nargs < arity) return v;
    V *s = mkv(V_SYM); s->e = mke(E_CALL, 1); s->e->nargs = arity; s->e->args = A(sizeof(Expr *) * (size_t)arity);
    for (int i = 0; i < arity; i++) { s->e->args[i] = to_expr(force(v->args[i])); if (!s->e->args[i]) return NULL; }
    return s;
  }
  case V_MCONS: { V *v = mkv(V_MCONS1); v->a = x; return v; }
  case V_MCONS1: { V *v = mkv(V_MCELL); v->a = f->a; v->b = x; return v; }
  default: fail("a marker applied"); return NULL;
  }
}

static V *eval(Port p, Env *env) {
  if (failed) return NULL;
  if (--fuel < 0) { fail("out of fuel"); return NULL; }
  p = dhop(N, p);
  if (!live(N, p)) { fail("a dead or open wire"); return NULL; }
  int t = N->tag[p.node];
  if (t == LAM && p.port == 0) { V *v = mkv(V_CLO); v->lam = p.node; v->env = env; return v; }
  if (t == LAM && p.port == 1) {
    for (Env *e = env; e; e = e->next) if (e->lam == p.node) return force(e->t);
    fail("a variable bound outside the function"); return NULL;
  }
  if (t == APP && p.port == 1) return apply(eval(W(N, (Port){p.node, 0}), env), lzp(W(N, (Port){p.node, 2}), env));
  fail("a node the evaluator does not read"); return NULL;
}

/* Constants: a numeral answers the cell markers bit by bit, its terminal answers with its SIGN. */
static int const_bool(V *v, int *ok) {
  V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
  *ok = r && (r->k == V_MCONS || r->k == V_MNIL);
  return r && r->k == V_MCONS;
}
static long const_int(V *v, int *ok) {
  unsigned long a = 0; *ok = 0;
  for (int k = 0; k <= LIN_INT_BITS && v && !failed; k++) {
    if (v->k != V_CLO) return 0;
    V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) return 0;
    if (r->k == V_MCELL) {
      int bo; int b = const_bool(force(r->a), &bo); if (!bo) return 0;
      if (k < LIN_INT_BITS) a |= (unsigned long)b << k;
      v = force(r->b); continue;
    }
    if (r->k == V_CLO) {                           /* the terminal answered with its SIGN (a boolean) */
      int so; int nonneg = const_bool(r, &so); if (!so) return 0;
      if (!nonneg && k < LIN_INT_BITS) a |= ~0UL << k;
      *ok = k > 0; return (long)a;
    }
    return 0;
  }
  return 0;
}

static Expr *to_expr(V *v) {
  if (failed || !v) return NULL;
  if (v->k == V_SYM) return v->e;
  if (v->k == V_COND) {
    Expr *e = mke(E_IF, 1); e->a = v->e; e->b = to_expr(force(v->a)); e->c = to_expr(force(v->b));
    if (!e->b || !e->c) return NULL;
    e->kind = e->b->kind; return e;
  }
  if (v->k == V_CLO) {
    int ok; long k = const_int(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 1); e->k = k; return e; }
    int bk = const_bool(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 3); e->k = bk; return e; }
    fail("a closure where a number belongs"); return NULL;
  }
  fail("a value with no number"); return NULL;
}

/* Strictness: the parameters certainly evaluated, as a bit set (a call is assumed strict in its arguments). */
static unsigned strict(Expr *e) {
  switch (e->op) {
  case E_PARAM: return 1u << e->k;
  case E_BIN: return strict(e->a) | strict(e->b);
  case E_IF: return strict(e->a) | (strict(e->b) & strict(e->c));
  case E_CALL: { unsigned s = 0; for (int i = 0; i < e->nargs; i++) s |= strict(e->args[i]); return s; }
  default: return 0;
  }
}

/* ---- C ------------------------------------------------------------------------------------------ */
typedef struct { char *s; size_t len, cap; } Buf;
static Buf nbuf(size_t cap) { Buf b = { malloc(cap), 0, cap }; b.s[0] = 0; return b; }
static void put(Buf *b, const char *fmt, ...) {
  va_list ap; va_start(ap, fmt);
  for (;;) {
    va_list aq; va_copy(aq, ap);
    int k = vsnprintf(b->s + b->len, b->cap - b->len, fmt, aq); va_end(aq);
    if (k >= 0 && b->len + (size_t)k < b->cap) { b->len += (size_t)k; break; }
    b->cap = b->cap * 2 + (size_t)k + 64; b->s = realloc(b->s, b->cap);
  }
  va_end(ap);
}
/* THE PARALLEL SITES.  An operation whose two operands BOTH contain a recursive call evaluates them at the same
   time: one on a new thread, the other on this one.  That changes nothing about the value -- the operation
   evaluates both operands anyway, and compiled code is pure -- and it is where a tree recursion's work is.  The
   parallel version `fp` carries the recursion depth and spawns only while it is below `dmax` (derived from the
   thread count), so the leaves run the sequential `f` with no threading cost at all. */
static int has_call(const Expr *e) {
  switch (e->op) {
  case E_CALL: return 1;
  case E_BIN: return has_call(e->a) || has_call(e->b);
  case E_IF: return has_call(e->a) || has_call(e->b) || has_call(e->c);
  default: return 0;
  }
}
static int nsite;
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static void plist(Buf *b, int typed) { for (int i = 0; i < arity; i++) put(b, typed ? "%slong p%d" : "%sp%d", i ? ", " : "", i); }
static int emit_op(Buf *b, long k, const char *x, const char *y) {
  static const char *const fn[LIN_OP_N] = { [LIN_OP_ADD] = "lin_i64_add", [LIN_OP_MUL] = "lin_i64_mul",
    [LIN_OP_SUB] = "lin_i64_sub", [LIN_OP_EQ] = "==", [LIN_OP_LT] = "<", [LIN_OP_LEQ] = "<=", [LIN_OP_GT] = ">",
    [LIN_OP_GEQ] = ">=", [LIN_OP_DIV] = "lin_i64_div", [LIN_OP_MOD] = "lin_i64_mod", [LIN_OP_POW] = "lin_i64_pow" };
  if (k >= LIN_OP_EQ && k <= LIN_OP_GEQ) put(b, "(long)(%s %s %s)", x, fn[k], y);
  else put(b, "%s(%s, %s)", fn[k], x, y);
  return 1;
}
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  if (budget <= 0) return 0;
  switch (e->op) {
  case E_CONST: if (e->k == (long)(1UL << (LIN_INT_BITS - 1))) put(b, "(-%ldL-1)", -(e->k + 1)); else put(b, "(%ldL)", e->k); return 1;
  case E_PARAM: put(b, "p%ld", e->k); return 1;
  case E_BIN: {
    Buf x = nbuf(256), y = nbuf(256);
    int ok = 1;
    if (par && has_call(e->a) && has_call(e->b)) {
      int k = nsite++;
      Buf sb = nbuf(512);            /* the site: operand a as a function of the parameters */
      put(&sb, "static long site%d(", k); plist(&sb, 1); put(&sb, "%sint d) { return ", arity ? ", " : "");
      ok = emitx(&sb, pre, e->a, 1, budget - 1);
      put(&sb, "; }\ntypedef struct { long p[%d]; int d; long r; } S%d;\n", arity, k);
      put(&sb, "static void *run%d(void *v) { S%d *s = v; s->r = site%d(", k, k, k);
      for (int i = 0; i < arity; i++) put(&sb, "s->p[%d], ", i);
      put(&sb, "s->d); return 0; }\n");
      put(pre, "%s", sb.s); free(sb.s);
      ok = ok && emitx(&y, pre, e->b, 1, budget - 1);
      put(b, "({ S%d s%d_ = { {", k, k); plist(b, 0); put(b, "}, d, 0 }; pthread_t t%d_; ", k);
      put(b, "int sp%d_ = d < dmax && !pthread_create(&t%d_, &attr, run%d, &s%d_); long y%d_ = %s; ", k, k, k, k, k, y.s);
      put(b, "long x%d_ = sp%d_ ? (pthread_join(t%d_, 0), s%d_.r) : site%d(", k, k, k, k, k); plist(b, 0);
      put(b, "%sd); ", arity ? ", " : "");
      x.len = 0; put(&x, "x%d_", k); y.len = 0; put(&y, "y%d_", k);   /* the operands are now named locals */
      emit_op(b, e->k, x.s, y.s); put(b, "; })");
    } else {
      ok = emitx(&x, pre, e->a, par, budget - 1) && emitx(&y, pre, e->b, par, budget - 1);
      if (ok) emit_op(b, e->k, x.s, y.s);
    }
    free(x.s); free(y.s); return ok;
  }
  case E_IF:
    put(b, "("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    put(b, " ? "); if (!emitx(b, pre, e->b, par, budget - 1)) return 0;
    put(b, " : "); if (!emitx(b, pre, e->c, par, budget - 1)) return 0;
    put(b, ")"); return 1;
  case E_CALL:
    put(b, par ? "fp(" : "f(");
    for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; }
    put(b, par ? "%sd + 1)" : ")", e->nargs ? ", " : "");
    return 1;
  }
  return 0;
}

static unsigned long fnv1a(const char *s) { unsigned long h = 1469598103934665603UL; for (; *s; s++) { h ^= (unsigned char)*s; h *= 1099511628211UL; } return h; }
static const char *cache_dir(char *out, size_t n) {
  const char *env = getenv("LIN_NATIVE_CACHE"), *xdg = getenv("XDG_CACHE_HOME"), *home = getenv("HOME");
  if (env && env[0]) snprintf(out, n, "%s", env);
  else if (xdg && xdg[0]) snprintf(out, n, "%s/lin/native", xdg);
  else if (home && home[0]) snprintf(out, n, "%s/.cache/lin/native", home);
  else snprintf(out, n, "/tmp/lin-native-%u", (unsigned)getuid());
  return out;
}
static void mkdir_p(const char *path) {
  char tmp[4096]; snprintf(tmp, sizeof tmp, "%s", path);
  for (char *p = tmp + 1; *p; p++) if (*p == '/') { *p = 0; mkdir(tmp, 0700); *p = '/'; }
  mkdir(tmp, 0700);
}
static int run_cc(const char *src, const char *so) {
  const char *cc = getenv("LIN_NATIVE_CC"); if (!cc || !cc[0]) cc = "cc";
  pid_t pid = fork();
  if (pid < 0) return 0;
  if (pid == 0) { execlp(cc, cc, "-O2", "-w", "-fPIC", "-shared", "-pthread", "-o", so, src, (char *)NULL); _exit(127); }
  int st = 0;
  return waitpid(pid, &st, 0) >= 0 && WIFEXITED(st) && WEXITSTATUS(st) == 0;
}

typedef long (*Entry)(const long *, int threads);
typedef struct { unsigned long h; Entry fn; int arity, kind; unsigned strict; } Compiled;   /* strict: the parameters certainly evaluated */
static Compiled *done; static int ndone, donecap;
static Compiled *compile_src(const char *src, int ar, int kind) {
  unsigned long h = fnv1a(src);
  for (int i = 0; i < ndone; i++) if (done[i].h == h) return done[i].fn ? &done[i] : NULL;
  char dir[4096], c[4200], so[4200];
  cache_dir(dir, sizeof dir); mkdir_p(dir);
  snprintf(c, sizeof c, "%s/fn-%016lx.c", dir, h); snprintf(so, sizeof so, "%s/fn-%016lx.so", dir, h);
  void *hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
  if (!hnd) {
    char tmp[4300]; snprintf(tmp, sizeof tmp, "%s.%d.tmp", c, (int)getpid());
    FILE *f = fopen(tmp, "wb");
    if (f) { fputs(src, f); fclose(f); rename(tmp, c); if (run_cc(c, so)) hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL); }
  }
  Entry e = hnd ? (Entry)(intptr_t)dlsym(hnd, "lin_fn_entry") : NULL;   /* one per object, loaded RTLD_LOCAL */
  if (!e) DBG("no compiler or the build failed for %s\n", c);
  if (ndone >= donecap) done = realloc(done, (size_t)(donecap = donecap ? donecap * 2 : 32) * sizeof *done);
  done[ndone] = (Compiled){ h, e, ar, kind, 0 };
  return e ? &done[ndone++] : (ndone++, NULL);
}

/* Compile F = \self.\p1..\pk. body, or return NULL. */
static Compiled *compile_fn(Net *n, int F) {
  N = n; failed = 0; fuel = 200000; F_lam = F; arity = 0;
  int params[8]; Port body = W(n, (Port){F, 2});
  for (Port q = dhop(n, body); is(n, q, LAM, 0) && arity < 8; q = dhop(n, W(n, (Port){q.node, 2}))) {
    params[arity++] = q.node; body = W(n, (Port){q.node, 2});
  }
  if (arity == 0) { DBG("declined: no parameters\n"); return NULL; }
  DBG("compile F=%d arity %d (net %d nodes)\n", F, arity, n->nn);
  Env *env = A(sizeof *env); env->lam = F; env->t = ready(mkv(V_SELF));
  for (int i = 0; i < arity; i++) {
    Env *e = A(sizeof *e); e->lam = params[i]; V *s = mkv(V_SYM); s->e = mke(E_PARAM, 1); s->e->k = i;
    e->t = ready(s); e->next = env; env = e;
  }
  Expr *top = to_expr(eval(body, env));
  Compiled *r = NULL;
  if (!failed && top) {
    {
      Buf b = nbuf(4096), pre = nbuf(1024), pb = nbuf(1024);
      put(&b, "%s\n#include <pthread.h>\nstatic long f(", LIN_I64_SRC); plist(&b, 1); put(&b, ") { return ");
      nsite = 0;
      int ok = emitx(&b, &pre, top, 0, 4096) && emitx(&pb, &pre, top, 1, 4096);
      if (ok) {
        put(&b, "; }\nstatic int dmax; static pthread_attr_t attr;\nstatic long fp("); plist(&b, 1);
        put(&b, "%sint d);\n%sstatic long fp(", arity ? ", " : "", pre.s); plist(&b, 1);
        put(&b, "%sint d) { if (d >= dmax) return f(", arity ? ", " : ""); plist(&b, 0); put(&b, "); return %s; }\n", pb.s);
        put(&b, "long lin_fn_entry(const long *a, int threads) {\n");
        for (int i = 0; i < arity; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        /* the depth that keeps about four tasks per thread in flight */
        put(&b, "  if (%d && threads > 1) { int lg = 0; while ((1 << lg) < threads) lg++; dmax = lg + 2;\n", nsite);
        put(&b, "    pthread_attr_init(&attr); pthread_attr_setstacksize(&attr, (size_t)256 << 20); return fp(");
        plist(&b, 0); put(&b, "%s0); }\n  return f(", arity ? ", " : ""); plist(&b, 0); put(&b, ");\n}\n");
        DBG("compiling (arity %d, %d parallel site%s):\n%s\n", arity, nsite, nsite == 1 ? "" : "s", b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, arity, top->kind);
        if (r) r->strict = strict(top);
      } else DBG("declined: expression too large\n");
      free(pre.s); free(pb.s);
      free(b.s);
    }
  }
  arena_free();
  return r;
}

/* ---- the driver --------------------------------------------------------------------------------- */
static int fn_off = -1;   /* LIN_FN_OFF: refuse every call (the differential's control run) */
static int fn_claim(const Net *n, Port p1, Port p2) {
  if (fn_off < 0) fn_off = getenv("LIN_FN_OFF") != NULL;
  int h, a, F; return !fn_off && y_call(n, p1, p2, &h, &a, &F);
}

static int fn_reduce(Net *n, Port *rx, int nred, long limit, int *changed) {
  (void)limit;
  int folded = 0;
  for (int i = 0; i < nred; i++) {
    Port p1 = rx[2 * i], p2 = rx[2 * i + 1];
    int h, appy, F;
    if (!y_call(n, p1, p2, &h, &appy, &F)) {           /* an earlier fold in this wave took it */
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    Compiled *c = lin_precompile_depth ? NULL : compile_fn(n, F);
    long args[8]; int call = appy, ok = c != NULL;
    for (int k = 0; ok && k < c->arity; k++) {         /* the call chain: (Y F) a1 .. ak */
      Port nx = W(n, (Port){call, 1});
      if (!is(n, nx, APP, 0)) { ok = 0; break; }
      call = nx.node;
      /* A parameter the function certainly evaluates is FORCED: that is what the program does anyway.  One it
         may not evaluate is taken only if it already IS a value (a numeral's head is a lambda), because forcing
         it could run work -- or a divergence -- that needed order would never start. */
      Port a = W(n, (Port){call, 2});
      if (!((c->strict >> k) & 1u) && !is(n, dhop(n, a), LAM, 0)) { ok = 0; DBG("argument %d is lazy and not yet a value\n", k); break; }
      Port v = net_force_val(n, a);
      if (!net_read_i64(n, v, &args[k])) { ok = 0; DBG("argument %d is not a number\n", k); }
      if (!y_call(n, p1, p2, &h, &appy, &F)) { ok = 0; break; }   /* forcing rewrote the call itself */
    }
    if (!ok) {
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    extern int lin_threads;
    long r = c->fn(args, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
    Port val = c->kind == 3 ? net_alloc_bool(n, r != 0) : net_alloc_scott(n, r);
    Port out = W(n, (Port){call, 1});
    net_link(n, val, out, 1);
    net_drop(n, call);                                  /* erases the call chain, Y and F behind it */
    DBG("folded a call of arity %d -> %ld\n", c->arity, r);
    lin_fold_bump(); folded++; (*changed)++; n->steps++;
  }
  return folded;
}

LinDriver lin_fn_driver;
static void __attribute__((constructor)) fn_load(void) {
  if (dbg < 0) dbg = getenv("LIN_FN_DEBUG") ? atoi(getenv("LIN_FN_DEBUG")) : 0;
  static int registered;
  if (registered) return;
  registered = 1;
  lin_driver_add(&lin_fn_driver);
}
LinDriver lin_fn_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "fn", .description = "function compiler: a recursive integer function, compiled to C from its net",
  .caps = LIN_CAP_PREEMPT, .priority = 3,
  .claim = fn_claim, .reduce = fn_reduce,
};
