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
#define LIN_WANT_F64
#include <math.h>
#include "../runtime/i64.h"
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <dlfcn.h>
#include <limits.h>

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
enum { E_CONST, E_PARAM, E_BIN, E_IF, E_CALL, E_FOP };   /* E_FOP: a float row (FROW[k]) over args */
typedef struct Expr { int op; long k; struct Expr *a, *b, *c; struct Expr **args; int nargs, kind;   /* kind 1 int, 3 bool */
                      int id, var, vscope; } Expr;   /* id: a dense index; var: the local it is bound to while emitting */
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
struct Memo;
static struct Memo **memo; static int memocap;
static void arena_free(void) {
  for (int i = 0; i < narena; i++) free(arena[i]);
  narena = 0;
  if (memocap) memset(memo, 0, (size_t)memocap * sizeof *memo);   /* its entries lived in the arena */
}

static Net *N; static long fuel; static int failed;
/* THE UNIT: every function this compilation reaches.  funs[0] is the one being called; a call to another
   recursive function (a `Y G` met while evaluating) compiles G as funs[k], once per node. */
typedef struct { int lam, arity; Expr *body; unsigned strict, fmask; } Fun;   /* fmask: the FLOAT parameters */
static Fun *funs; static int nfun, funcap;
static int arity;   /* funs[0]'s, which the entry point and the parallel sites are written for */
static void fail(const char *why) { if (!failed) DBG("declined: %s\n", why); failed = 1; }

static V *mkv(int k) { V *v = A(sizeof *v); v->k = k; return v; }
static Lz *ready(V *v) { Lz *l = A(sizeof *l); l->state = 2; l->v = v; return l; }
static Lz *lzp(Port p, Env *e) { Lz *l = A(sizeof *l); l->state = 0; l->p = p; l->env = e; return l; }
static Lz *lzapp(Lz *f, Lz *x) { Lz *l = A(sizeof *l); l->state = 1; l->f = f; l->x = x; return l; }
static int eid;
static Expr *mke(int op, int kind) { Expr *e = A(sizeof *e); e->op = op; e->kind = kind; e->id = eid++; e->var = -1; return e; }

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
static Expr *ffi_expr(V *v);
/* An `_op` head: \x. ((\k. B) x) with k unused, applied to its operand list (code, a, b). */
static int compile_body(int G, Env *outer);
static int is_y(const Net *n, int h);
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
    /* A float operation USED (a comparison applied to two branches): its value is the operation's result, not
       a beta of the closure.  Never while decoding: the markers are applied to cells all the time. */
    if (!(x->state == 2 && x->v && x->v->k >= V_MCONS)) {
      Expr *fe = ffi_expr(f);
      if (failed) return NULL;
      if (fe) { V *s = mkv(V_SYM); s->e = fe; return apply(s, x); }
    }
    if (is_y(N, f->lam)) {                          /* another recursive function: compile it into the unit */
      V *g = force(x);
      if (!g || g->k != V_CLO) { fail("a fixpoint of something that is not a function"); return NULL; }
      int fid = compile_body(g->lam, g->env);   /* in its own closure: an enclosing function stays callable */
      if (fid < 0) return NULL;
      V *v = mkv(V_SELF); v->lam = fid; return v;
    }
    Env *e = A(sizeof *e); e->lam = f->lam; e->t = x; e->next = f->env;
    return eval(W(N, (Port){f->lam, 2}), e);
  }
  case V_SYM: {
    if (f->e->kind != 3) { fail("an integer applied as a function"); return NULL; }
    V *v = mkv(V_C1); v->e = f->e; v->a = x; return v;
  }
  case V_C1: { V *v = mkv(V_COND); v->e = f->e; v->a = f->a; v->b = x; return v; }
  case V_COND: { V *v = mkv(V_COND); v->e = f->e; v->a = lzapp(f->a, x); v->b = lzapp(f->b, x); return v; }
  case V_SELF: {                                    /* a function of the unit (v->lam is its index), being applied */
    int ar = funs[f->lam].arity;
    V *v = mkv(V_SELF); v->lam = f->lam; v->nargs = f->nargs + 1; v->args = A(sizeof(Lz *) * (size_t)v->nargs);
    memcpy(v->args, f->args, sizeof(Lz *) * (size_t)f->nargs); v->args[f->nargs] = x;
    if (v->nargs < ar) return v;
    V *s = mkv(V_SYM); s->e = mke(E_CALL, 1); s->e->k = f->lam; s->e->nargs = ar; s->e->args = A(sizeof(Expr *) * (size_t)ar);
    for (int i = 0; i < ar; i++) { s->e->args[i] = to_expr(force(v->args[i])); if (!s->e->args[i]) return NULL; }
    return s;
  }
  case V_MCONS: { V *v = mkv(V_MCONS1); v->a = x; return v; }
  case V_MCONS1: { V *v = mkv(V_MCELL); v->a = f->a; v->b = x; return v; }
  default: fail("a marker applied"); return NULL;
  }
}

/* A SHARED value is one value: reaching a producer through a fan (a `let`, a variable used twice) yields the
   same V every time in the same environment, so the expression it builds is one DAG node, kept shared in C. */
typedef struct Memo { Port p; Env *env; V *v; struct Memo *next; } Memo;
static V *eval_at(Port p, Env *env);
static V *eval(Port p, Env *env) {
  if (failed) return NULL;
  if (--fuel < 0) { fail("out of fuel"); return NULL; }
  Port q = dhop(N, p);
  if (q.node == p.node && q.port == p.port) return eval_at(q, env);   /* not shared: nothing to remember */
  if (!memocap) { memocap = 4096; memo = calloc((size_t)memocap, sizeof *memo); }
  unsigned h = ((unsigned)q.node * 2654435761u ^ (unsigned)(uintptr_t)env * 40503u ^ q.port) & (unsigned)(memocap - 1);
  for (Memo *m = memo[h]; m; m = m->next) if (m->p.node == q.node && m->p.port == q.port && m->env == env) return m->v;
  V *v = eval_at(q, env);
  if (v) { Memo *m = A(sizeof *m); m->p = q; m->env = env; m->v = v; m->next = memo[h]; memo[h] = m; }
  return v;
}
static V *eval_at(Port p, Env *env) {
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

/* FLOATS.  A float operation is an FFI closure \_ffi.\_ret.((_ffi name) args) (std/float.lin); its name and
   operand list are read by evaluating them, and a row the table below knows becomes E_FOP.  The rows are
   std/runtime/i64.h's, which arith's table uses too, so the compiled and the folded float are one function. */
static const struct { const char *name, *c; int arity, kind, in; } FROW[] = {
  { "lin_fadd", "lin_f64_add", 2, 4, 4 }, { "lin_fsub", "lin_f64_sub", 2, 4, 4 }, { "lin_fmul", "lin_f64_mul", 2, 4, 4 },
  { "lin_fdiv", "lin_f64_div", 2, 4, 4 }, { "lin_fpow", "lin_f64_pow", 2, 4, 4 }, { "lin_fatan2", "lin_f64_atan2", 2, 4, 4 },
  { "lin_fmin", "lin_f64_min", 2, 4, 4 }, { "lin_fmax", "lin_f64_max", 2, 4, 4 }, { "lin_fsqrt", "lin_f64_sqrt", 1, 4, 4 },
  { "lin_fsin", "lin_f64_sin", 1, 4, 4 }, { "lin_fcos", "lin_f64_cos", 1, 4, 4 }, { "lin_ftan", "lin_f64_tan", 1, 4, 4 },
  { "lin_fabs", "lin_f64_abs", 1, 4, 4 }, { "lin_fsign", "lin_f64_sign", 1, 4, 4 }, { "lin_ffract", "lin_f64_fract", 1, 4, 4 },
  { "lin_feq", "lin_f64_eq", 2, 3, 4 }, { "lin_flt", "lin_f64_lt", 2, 3, 4 }, { "lin_fleq", "lin_f64_leq", 2, 3, 4 },
  { "lin_ffloor", "lin_f64_floor", 1, 1, 4 }, { "lin_float", "lin_f64_of_int", 1, 4, 1 },
};
static int cur_fid;   /* the unit function being evaluated: a float operand that is one of ITS parameters marks it */
/* A string constant (a list of character codes) into `buf`; 0 if the value is not one. */
static int const_str(V *v, char *buf, int cap) {
  int n = 0;
  for (; v && !failed && n < cap - 1; ) {
    V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) return 0;
    if (r->k != V_MCELL) { buf[n] = 0; return n > 0; }       /* the terminal: \c.\n.true answers true */
    int ok; long ch = const_int(force(r->a), &ok);
    if (!ok || ch <= 0 || ch > UCHAR_MAX) return 0;
    buf[n++] = (char)ch; v = force(r->b);
  }
  return 0;
}
static Expr *ffi_expr(V *v) {
  int lam = v->lam;
  Port r = dhop(N, W(N, (Port){lam, 2}));
  if (!is(N, r, LAM, 0)) return NULL;
  Port a2 = dhop(N, W(N, (Port){r.node, 2}));
  if (!is(N, a2, APP, 1)) return NULL;
  Port fa = dhop(N, W(N, (Port){a2.node, 0}));
  if (!is(N, fa, APP, 1)) return NULL;
  Port self = dhop(N, W(N, (Port){fa.node, 0}));
  if (self.node != lam || self.port != 1) return NULL;
  /* A CONS CELL HAS THIS SHAPE TOO (\c.\n.((c h) t)) -- and so does every numeral, a chain of cells -- so the
     shape alone says nothing: only a head that reads as a NAME the table knows makes this an FFI call.  The
     read is speculative: a head that is not a string is "not mine", never a failure. */
  char name[64]; long sfuel = fuel; int sfail = failed;
  int named = const_str(eval(W(N, (Port){fa.node, 2}), v->env), name, (int)sizeof name);
  if (!named) { failed = sfail; fuel = sfuel; return NULL; }
  int known = !strcmp(name, "lin_parse_float");
  for (int k = 0; k < N_OF(FROW); k++) known |= !strcmp(name, FROW[k].name);
  if (!known) { failed = sfail; fuel = sfuel; if (!strncmp(name, "lin_", 4)) { fail("an FFI call the compiler does not know"); } return NULL; }
  V *l = eval(W(N, (Port){a2.node, 2}), v->env);
  V *argv[4]; int argc = 0;
  for (; l && !failed; ) {
    V *c = apply(apply(l, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!c) return NULL;
    if (c->k != V_MCELL) break;
    if (argc >= N_OF(argv)) { fail("an FFI call with too many operands"); return NULL; }
    argv[argc++] = force(c->a); l = force(c->b);
  }
  if (failed) return NULL;
  if (!strcmp(name, "lin_parse_float") && argc == 1) {        /* (float "2.5"): a constant, read now */
    char lit[64];
    if (!const_str(argv[0], lit, (int)sizeof lit)) { fail("a float literal that is not a constant"); return NULL; }
    Expr *e = mke(E_CONST, 4); e->k = lin_l(strtod(lit, NULL)); return e;
  }
  for (int k = 0; k < N_OF(FROW); k++) {
    if (strcmp(name, FROW[k].name) || argc != FROW[k].arity) continue;
    Expr *e = mke(E_FOP, FROW[k].kind); e->k = k; e->nargs = argc; e->args = A(sizeof(Expr *) * (size_t)argc);
    for (int i = 0; i < argc; i++) {
      if (!(e->args[i] = to_expr(argv[i]))) return NULL;
      if (e->args[i]->op == E_PARAM && e->args[i]->nargs == cur_fid && FROW[k].in == 4) funs[cur_fid].fmask |= 1u << e->args[i]->k;
    }
    return e;
  }
  fail("an FFI call the compiler does not know"); return NULL;
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
    Expr *f = ffi_expr(v);
    if (f || failed) return f;
    double d;
    if (net_read_float(N, (Port){v->lam, 0}, &d)) { Expr *e = mke(E_CONST, 4); e->k = lin_l(d); return e; }   /* a float box */
    int ok; long k = const_int(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 1); e->k = k; return e; }
    int bk = const_bool(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 3); e->k = bk; return e; }
    fail("a closure where a number belongs"); return NULL;
  }
  fail("a value with no number"); return NULL;
}

/* Strictness: the parameters certainly evaluated, as a bit set.  A call evaluates the arguments its callee is
   strict in, so the sets are a fixpoint over the unit (compile_unit iterates them down from "everything"). */
static unsigned strict(Expr *e) {
  switch (e->op) {
  case E_PARAM: return 1u << e->k;
  case E_BIN: return strict(e->a) | strict(e->b);
  case E_IF: return strict(e->a) | (strict(e->b) & strict(e->c));
  case E_CALL: { unsigned s = 0; for (int i = 0; i < e->nargs; i++) if ((funs[e->k].strict >> i) & 1u) s |= strict(e->args[i]); return s; }
  case E_FOP: { unsigned s = 0; for (int i = 0; i < e->nargs; i++) s |= strict(e->args[i]); return s; }
  default: return 0;
  }
}
static int has_call(const Expr *e);
/* C evaluates EVERY argument of a call, the net only the ones the callee uses.  An argument in a position the
   callee may ignore is therefore allowed only if it cannot diverge or cost: no call inside it. */
static int args_safe(const Expr *e) {
  switch (e->op) {
  case E_BIN: return args_safe(e->a) && args_safe(e->b);
  case E_IF: return args_safe(e->a) && args_safe(e->b) && args_safe(e->c);
  case E_CALL:
    for (int i = 0; i < e->nargs; i++) {
      if (!((funs[e->k].strict >> i) & 1u) && has_call(e->args[i])) return 0;
      if (!args_safe(e->args[i])) return 0;
    }
    return 1;
  case E_FOP: for (int i = 0; i < e->nargs; i++) if (!args_safe(e->args[i])) return 0; return 1;
  default: return 1;
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
  case E_FOP: for (int i = 0; i < e->nargs; i++) if (has_call(e->args[i])) return 1; return 0;
  default: return 0;
  }
}
static int nsite;
static int emitting;   /* the unit function being written: a parameter of another one cannot appear in it */
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget);

/* SHARING, KEPT IN THE C.  The evaluator builds a DAG -- a `let`-bound or shared value is ONE node -- and C
   would compute such a node once per use.  A region (a function body, or one branch of a conditional) binds
   every node it CERTAINLY evaluates (reachable without entering a branch) and uses twice or more, once, at its
   start.  Only certain nodes move: one evaluated in just one branch is bound inside that branch, so a hoisted
   value is never work -- or a divergent call -- the program would have skipped. */
static int fscope, nvar;
static unsigned *st_need, *st_vis, *st_uses; static int st_cap; static unsigned stamp;
static void st_grow(void) {
  if (eid <= st_cap) return;
  int c = eid * 2 + 64;
  st_need = realloc(st_need, (size_t)c * sizeof *st_need); st_vis = realloc(st_vis, (size_t)c * sizeof *st_vis);
  st_uses = realloc(st_uses, (size_t)c * sizeof *st_uses);
  memset(st_need + st_cap, 0, (size_t)(c - st_cap) * sizeof *st_need); memset(st_vis + st_cap, 0, (size_t)(c - st_cap) * sizeof *st_vis);
  memset(st_uses + st_cap, 0, (size_t)(c - st_cap) * sizeof *st_uses); st_cap = c;
}
static int bound(const Expr *e) { return e->var >= 0 && e->vscope == fscope; }
static void count_uses(const Expr *e) {           /* every reference inside the region, branches included */
  if (st_vis[e->id] == stamp) { st_uses[e->id]++; return; }
  st_vis[e->id] = stamp; st_uses[e->id] = 1;
  if (bound(e)) return;
  switch (e->op) {
  case E_BIN: count_uses(e->a); count_uses(e->b); break;
  case E_IF: count_uses(e->a); count_uses(e->b); count_uses(e->c); break;
  case E_CALL: case E_FOP: for (int i = 0; i < e->nargs; i++) count_uses(e->args[i]); break;
  }
}
static void certain(const Expr *e, const Expr ***out, int *n, int *cap) {   /* post-order: dependencies first */
  if (st_need[e->id] == stamp || bound(e)) return;
  st_need[e->id] = stamp;
  switch (e->op) {
  case E_BIN: certain(e->a, out, n, cap); certain(e->b, out, n, cap); break;
  case E_IF: certain(e->a, out, n, cap); break;                  /* only the condition: a branch may not run */
  case E_CALL: case E_FOP: for (int i = 0; i < e->nargs; i++) certain(e->args[i], out, n, cap); break;
  }
  if (*n >= *cap) *out = realloc(*out, (size_t)(*cap = *cap ? *cap * 2 : 16) * sizeof **out);
  (*out)[(*n)++] = e;
}
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  st_grow(); stamp += 2;
  count_uses(e);
  const Expr **cand = NULL; int nc = 0, cc = 0;
  certain(e, &cand, &nc, &cc);
  int nb = 0, ok = 1;
  for (int i = 0; i < nc && ok; i++) {
    Expr *x = (Expr *)cand[i];
    if (x == e || st_uses[x->id] < 2 || x->op == E_CONST || x->op == E_PARAM) continue;
    if (!nb++) put(b, "({ ");
    put(b, "long v%d = ", nvar);
    ok = emitx(b, pre, x, par, budget - 1);
    put(b, "; ");
    x->var = nvar++; x->vscope = fscope;
    cand[i] = x;                                   /* still listed, so it is unbound below */
  }
  ok = ok && emitx(b, pre, e, par, budget - 1);
  if (nb) put(b, "; })");
  for (int i = 0; i < nc; i++) if (cand[i]->var >= 0 && cand[i]->vscope == fscope) ((Expr *)cand[i])->var = -1;
  free(cand);
  return ok;
}
static void plistn(Buf *b, int typed, int n) { for (int i = 0; i < n; i++) put(b, typed ? "%slong p%d" : "%sp%d", i ? ", " : "", i); }
static void plist(Buf *b, int typed) { plistn(b, typed, arity); }
static int emit_op(Buf *b, long k, const char *x, const char *y) {
  static const char *const fn[LIN_OP_N] = { [LIN_OP_ADD] = "lin_i64_add", [LIN_OP_MUL] = "lin_i64_mul",
    [LIN_OP_SUB] = "lin_i64_sub", [LIN_OP_EQ] = "==", [LIN_OP_LT] = "<", [LIN_OP_LEQ] = "<=", [LIN_OP_GT] = ">",
    [LIN_OP_GEQ] = ">=", [LIN_OP_DIV] = "lin_i64_div", [LIN_OP_MOD] = "lin_i64_mod", [LIN_OP_POW] = "lin_i64_pow",
    [LIN_OP_BAND] = "lin_i64_band", [LIN_OP_BOR] = "lin_i64_bor", [LIN_OP_BXOR] = "lin_i64_bxor",
    [LIN_OP_SHL] = "lin_i64_shl", [LIN_OP_SHR] = "lin_i64_shr" };
  if (k >= LIN_OP_EQ && k <= LIN_OP_GEQ) put(b, "(long)(%s %s %s)", x, fn[k], y);
  else put(b, "%s(%s, %s)", fn[k], x, y);
  return 1;
}
/* A GROUP of operands evaluated at once: every one but the last that contains a call runs on a new thread
   (while `d < dmax`), the last runs here, and the rest are plain.  Writes "({ ...;" -- the caller writes the
   use of names[i] and closes it with "; })". */
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static int par_group(Buf *b, Buf *pre, const Expr **xs, int n, Buf *names, int budget) {
  int last = -1, ok = 1;
  for (int i = 0; i < n; i++) if (has_call(xs[i])) last = i;
  put(b, "({ ");
  int *site = calloc((size_t)n, sizeof *site);
  for (int i = 0; ok && i < n; i++) {
    site[i] = -1;
    if (!has_call(xs[i]) || i == last) continue;
    int k = site[i] = nsite++;
    Buf sb = nbuf(512);            /* the site: this operand as a function of the parameters */
    put(&sb, "static long site%d(", k); plist(&sb, 1); put(&sb, "%sint d) { return ", arity ? ", " : "");
    int save = fscope; fscope = ++nvar + (1 << 20);   /* a new C function: no enclosing local is in scope */
    ok = emit_region(&sb, pre, xs[i], 1, budget - 1);
    fscope = save;
    put(&sb, "; }\ntypedef struct { long p[%d]; int d; long r; } S%d;\n", arity, k);
    put(&sb, "static void *run%d(void *v) { S%d *s = v; s->r = site%d(", k, k, k);
    for (int j = 0; j < arity; j++) put(&sb, "s->p[%d], ", j);
    put(&sb, "s->d); return 0; }\n");
    put(pre, "%s", sb.s); free(sb.s);
    put(b, "S%d s%d_ = { {", k, k); plist(b, 0); put(b, "}, d, 0 }; pthread_t t%d_; ", k);
    put(b, "int sp%d_ = d < dmax && !pthread_create(&t%d_, &attr, run%d, &s%d_); ", k, k, k, k);
  }
  int self = nvar++;
  for (int i = 0; ok && i < n; i++) {             /* the last call-containing operand, on this thread */
    if (i != last) continue;
    put(b, "long y%d_ = ", self); ok = emitx(b, pre, xs[i], 1, budget - 1); put(b, "; ");
  }
  for (int i = 0; ok && i < n; i++) {
    names[i].len = 0; names[i].s[0] = 0;
    if (site[i] >= 0) {
      int k = site[i];
      put(b, "long x%d_ = sp%d_ ? (pthread_join(t%d_, 0), s%d_.r) : site%d(", k, k, k, k, k); plist(b, 0);
      put(b, "%sd); ", arity ? ", " : "");
      put(&names[i], "x%d_", k);
    } else if (i == last) put(&names[i], "y%d_", self);
    else ok = emitx(&names[i], pre, xs[i], 1, budget - 1);
  }
  free(site);
  return ok;
}
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  if (budget <= 0) return 0;
  if (bound(e)) { put(b, "v%d", e->var); return 1; }
  switch (e->op) {
  case E_CONST: if (e->k == (long)(1UL << (LIN_INT_BITS - 1))) put(b, "(-%ldL-1)", -(e->k + 1)); else put(b, "(%ldL)", e->k); return 1;
  case E_PARAM:   /* a parameter of an ENCLOSING function would need lambda lifting: decline instead */
    if (e->nargs != emitting) { DBG("declined: a nested function uses its parent's parameter\n"); return 0; }
    put(b, "p%ld", e->k); return 1;
  case E_BIN: {
    Buf x = nbuf(256), y = nbuf(256);
    int ok = 1;
    if (par && has_call(e->a) && has_call(e->b)) {
      const Expr *xs[2] = { e->a, e->b }; Buf nm[2] = { nbuf(32), nbuf(32) };
      ok = par_group(b, pre, xs, 2, nm, budget);
      if (ok) { emit_op(b, e->k, nm[0].s, nm[1].s); put(b, "; })"); }
      free(nm[0].s); free(nm[1].s);
    } else {
      ok = emitx(&x, pre, e->a, par, budget - 1) && emitx(&y, pre, e->b, par, budget - 1);
      if (ok) emit_op(b, e->k, x.s, y.s);
    }
    free(x.s); free(y.s); return ok;
  }
  case E_IF:
    put(b, "("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    put(b, " ? "); if (!emit_region(b, pre, e->b, par, budget - 1)) return 0;
    put(b, " : "); if (!emit_region(b, pre, e->c, par, budget - 1)) return 0;
    put(b, ")"); return 1;
  case E_FOP:
    put(b, "%s(", FROW[e->k].c);
    for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; }
    put(b, ")"); return 1;
  case E_CALL:
    par = par && e->k == 0;                        /* only the entry function has a parallel version */
    { int calls = 0; for (int i = 0; i < e->nargs; i++) calls += has_call(e->args[i]);
      if (par && calls >= 2) {                     /* independent calls among the arguments: at once */
        Buf *nm = calloc((size_t)e->nargs, sizeof *nm);
        for (int i = 0; i < e->nargs; i++) nm[i] = nbuf(32);
        int ok = par_group(b, pre, (const Expr **)e->args, e->nargs, nm, budget);
        if (ok) { put(b, "fp("); for (int i = 0; i < e->nargs; i++) put(b, "%s, ", nm[i].s); put(b, "d + 1); })"); }
        for (int i = 0; i < e->nargs; i++) free(nm[i].s);
        free(nm); return ok;
      } }
    if (par) put(b, "fp("); else put(b, "f%ld(", e->k);
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
  if (pid == 0) { execlp(cc, cc, "-O3", "-march=native", "-ffp-contract=off", "-w", "-fPIC", "-shared", "-pthread", "-o", so, src, "-lm", (char *)NULL); _exit(127); }
  int st = 0;
  return waitpid(pid, &st, 0) >= 0 && WIFEXITED(st) && WEXITSTATUS(st) == 0;
}

typedef long (*Entry)(const long *, int threads);
typedef struct { unsigned long h; Entry fn; int arity, kind; unsigned strict, fmask; } Compiled;   /* strict: the parameters certainly evaluated */
static Compiled *done; static int ndone, donecap;
/* -march=native code must never be loaded on a different CPU, so the cache key includes this one's identity. */
static unsigned long cpu_key(void) {
  static unsigned long k;
  if (k) return k;
  k = 1469598103934665603UL;
  FILE *f = fopen("/proc/cpuinfo", "r");
  if (f) {
    char *line = NULL; size_t cap = 0;
    while (getline(&line, &cap, f) > 0)
      if (!strncmp(line, "flags", 5) || !strncmp(line, "model name", 10)) { k ^= fnv1a(line); k *= 1099511628211UL; }
    free(line); fclose(f);
  }
  return k;
}
static Compiled *compile_src(const char *src, int ar, int kind) {
  unsigned long h = fnv1a(src) ^ cpu_key();
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
  done[ndone] = (Compiled){ h, e, ar, kind, 0, 0 };
  return e ? &done[ndone++] : (ndone++, NULL);
}

/* A PARALLEL REDUCTION.  f(.., i, .., acc, ..) = if i == c then acc else f(.., i - 1, .., acc (+) g, ..), with every
   other parameter passed unchanged, g independent of acc and (+) associative and commutative -- wrapping add or
   mul, band / bor / bxor, or max / min written as a conditional -- folds g over the range (c, i0] in ANY order
   to the same value.  So the range is split among the threads, each folds its blocks from (+)'s identity, and
   the partial results are combined with the initial acc.  Every g(i) is still evaluated exactly once. */
typedef struct { int iv, acc, op, ismax; long c; const Expr *g; } Red;
static int is_param(const Expr *e, int k) { return e && e->op == E_PARAM && e->k == k && e->nargs == 0; }
static int mentions(const Expr *e, int k) {
  switch (e->op) {
  case E_PARAM: return e->k == k && e->nargs == 0;
  case E_BIN: return mentions(e->a, k) || mentions(e->b, k);
  case E_IF: return mentions(e->a, k) || mentions(e->b, k) || mentions(e->c, k);
  case E_CALL: case E_FOP: for (int i = 0; i < e->nargs; i++) if (mentions(e->args[i], k)) return 1; return 0;
  default: return 0;
  }
}
static int find_reduction(Red *r) {
  const Expr *e = funs[0].body;
  if (e->op != E_IF || e->a->op != E_BIN || e->a->k != LIN_OP_EQ) return 0;
  const Expr *c = e->a, *base = e->b, *step = e->c;
  int iv; long cv;
  if (c->a->op == E_PARAM && c->a->nargs == 0 && c->b->op == E_CONST) { iv = (int)c->a->k; cv = c->b->k; }
  else if (c->b->op == E_PARAM && c->b->nargs == 0 && c->a->op == E_CONST) { iv = (int)c->b->k; cv = c->a->k; }
  else return 0;
  if (base->op != E_PARAM || base->nargs != 0 || base->k == iv) return 0;
  int acc = (int)base->k;
  if (step->op != E_CALL || step->k != 0 || step->nargs != arity) return 0;
  for (int j = 0; j < arity; j++) {
    const Expr *a = step->args[j];
    if (j == iv) { if (!(a->op == E_BIN && a->k == LIN_OP_SUB && is_param(a->a, iv) && a->b->op == E_CONST && a->b->k == 1)) return 0; }
    else if (j != acc && !is_param(a, j)) return 0;
  }
  const Expr *u = step->args[acc], *g = NULL; int op = -1, ismax = 0;
  if (u->op == E_BIN && (u->k == LIN_OP_ADD || u->k == LIN_OP_MUL || u->k == LIN_OP_BAND || u->k == LIN_OP_BOR || u->k == LIN_OP_BXOR)) {
    if (is_param(u->a, acc)) g = u->b; else if (is_param(u->b, acc)) g = u->a; else return 0;
    op = (int)u->k;
  } else if (u->op == E_IF && u->a->op == E_BIN && u->a->k >= LIN_OP_LT && u->a->k <= LIN_OP_GEQ) {
    /* (if (x > acc) x acc) is max, (if (x < acc) x acc) is min -- in either operand order */
    const Expr *x = NULL; int gt = u->a->k == LIN_OP_GT || u->a->k == LIN_OP_GEQ;
    if (is_param(u->a->b, acc)) x = u->a->a; else if (is_param(u->a->a, acc)) { x = u->a->b; gt = !gt; } else return 0;
    if (u->b == x && is_param(u->c, acc)) ismax = gt ? 1 : -1;
    else if (u->c == x && is_param(u->b, acc)) ismax = gt ? -1 : 1;
    else return 0;
    g = x; op = LIN_OP_ADD;                         /* unused when ismax */
  } else return 0;
  if (mentions(g, acc)) return 0;
  r->iv = iv; r->acc = acc; r->op = op; r->ismax = ismax; r->c = cv; r->g = g;
  return 1;
}
static void red_combine(Buf *b, const Red *r, const char *x, const char *y) {
  if (r->ismax) { put(b, "(%s %s %s ? %s : %s)", x, r->ismax > 0 ? ">" : "<", y, x, y); return; }
  emit_op(b, r->op, x, y);
}

/* Evaluate G = \self.\p1..\pk. body into the unit; its index, or -1. */
static int compile_body(int G, Env *outer) {
  for (int i = 0; i < nfun; i++) if (funs[i].lam == G) return i;
  if (nfun >= 1 + LIN_INT_BITS) { fail("too many functions in one unit"); return -1; }   /* mutual recursion re-copies: bound it */
  if (nfun >= funcap) funs = realloc(funs, (size_t)(funcap = funcap ? funcap * 2 : 8) * sizeof *funs);
  int fid = nfun++; funs[fid].lam = G; funs[fid].body = NULL; funs[fid].strict = ~0u; funs[fid].fmask = 0;
  /* a parameter is one bit of a strictness set, so a function has at most that many */
  int params[sizeof(unsigned) * 8], ar = 0; Port body = W(N, (Port){G, 2});
  for (Port q = dhop(N, body); is(N, q, LAM, 0) && ar < N_OF(params); q = dhop(N, W(N, (Port){q.node, 2}))) {
    params[ar++] = q.node; body = W(N, (Port){q.node, 2});
  }
  funs[fid].arity = ar;
  if (ar == 0) { fail("a function with no parameters"); return -1; }
  Env *env = A(sizeof *env); env->lam = G; V *self = mkv(V_SELF); self->lam = fid; env->t = ready(self); env->next = outer;
  for (int i = 0; i < ar; i++) {
    Env *e = A(sizeof *e); e->lam = params[i]; V *s = mkv(V_SYM); s->e = mke(E_PARAM, 1); s->e->k = i; s->e->nargs = fid;
    e->t = ready(s); e->next = env; env = e;
  }
  int save_fid = cur_fid; cur_fid = fid;
  Expr *top = to_expr(eval(body, env));
  cur_fid = save_fid;
  if (failed || !top) return -1;
  funs[fid].body = top;
  return fid;
}

/* Compile F and everything it calls, or return NULL. */
static Compiled *compile_fn(Net *n, int F) {
  N = n; failed = 0; fuel = 200000; nfun = 0; eid = 0; nvar = 0;
  DBG("compile F=%d (net %d nodes)\n", F, n->nn);
  Compiled *r = NULL;
  if (compile_body(F, NULL) == 0 && !failed) {
    arity = funs[0].arity;
    for (int it = 0, changed = 1; changed && it <= LIN_INT_BITS; it++) {   /* strictness: down to the fixpoint */
      changed = 0;
      for (int i = 0; i < nfun; i++) { unsigned st = strict(funs[i].body) & funs[i].strict; if (st != funs[i].strict) { funs[i].strict = st; changed = 1; } }
    }
    int safe = 1;
    for (int i = 0; i < nfun; i++) safe = safe && args_safe(funs[i].body);
    if (!safe) DBG("declined: a call passes a computation where its callee may not evaluate it\n");
    else {
      Buf b = nbuf(4096), pre = nbuf(1024), pb = nbuf(1024);
      put(&b, "%s%s\n#include <pthread.h>\n", LIN_I64_SRC, LIN_F64_SRC);
      for (int i = 0; i < nfun; i++) { put(&b, "static long f%d(", i); plistn(&b, 1, funs[i].arity); put(&b, ");\n"); }
      int ok = 1;
      for (int i = 0; ok && i < nfun; i++) {
        put(&b, "static long f%d(", i); plistn(&b, 1, funs[i].arity); put(&b, ") { return ");
        emitting = i; fscope++; ok = emit_region(&b, &pre, funs[i].body, 0, 4096); put(&b, "; }\n");
      }
      nsite = 0; emitting = 0; fscope++;
      ok = ok && emit_region(&pb, &pre, funs[0].body, 1, 4096);
      if (ok) {
        put(&b, "static int dmax; static pthread_attr_t attr;\nstatic long fp("); plist(&b, 1);
        put(&b, "%sint d);\n%sstatic long fp(", arity ? ", " : "", pre.s); plist(&b, 1);
        put(&b, "%sint d) { if (d >= dmax) return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); return %s; }\n", pb.s);
        Red red; int has_red = find_reduction(&red);
        if (has_red) {
          long id = red.ismax > 0 ? (long)(1UL << (LIN_INT_BITS - 1)) : red.ismax < 0 ? (long)~(1UL << (LIN_INT_BITS - 1))
                  : (red.op == LIN_OP_MUL) ? 1 : (red.op == LIN_OP_BAND) ? -1 : 0;   /* (+)'s identity */
          put(&b, "static long g("); plist(&b, 1); put(&b, ") { return ");
          emitting = 0; fscope++; ok = emit_region(&b, &pre, red.g, 0, 4096); put(&b, "; }\n");
          put(&b, "typedef struct { long p[%d]; long lo, block, r; long *next; } R;\n", arity);
          put(&b, "static void *rrun(void *v) { R *q = v; long acc = %ldL;\n", id);
          for (int i = 0; i < arity; i++) put(&b, "  long p%d = q->p[%d];\n", i, i);
          put(&b, "  for (;;) { long hi = __atomic_fetch_sub(q->next, q->block, __ATOMIC_RELAXED); if (hi <= q->lo) break;\n");
          put(&b, "    long lo = hi - q->block; if (lo < q->lo) lo = q->lo;\n    for (long i = hi; i > lo; i--) { p%d = i; long x = g(", red.iv);
          plist(&b, 0); put(&b, "); acc = "); red_combine(&b, &red, "x", "acc"); put(&b, "; } }\n");
          put(&b, "  q->r = acc; return 0; }\n");
          DBG("parallel reduction over p%d down to %ld, accumulator p%d\n", red.iv, red.c, red.acc);
        }
        put(&b, "long lin_fn_entry(const long *a, int threads) {\n");
        for (int i = 0; i < arity; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        if (has_red) {   /* a cheap step needs some thousands of iterations to pay for a thread; a step that CALLS
                            (a whole inner loop) pays from a few per thread */
          if (has_call(red.g)) put(&b, "  if (threads > 1 && p%d > %ldL && p%d - %ldL >= (long)threads * 4) {\n", red.iv, red.c, red.iv, red.c);
          else put(&b, "  if (threads > 1 && p%d > %ldL && p%d - %ldL >= 4096) {\n", red.iv, red.c, red.iv, red.c);
          put(&b, "    long next = p%d; pthread_t t[threads]; R q[threads];\n", red.iv);
          put(&b, "    for (int k = 0; k < threads; k++) { R r = { {"); plist(&b, 0);
          put(&b, "}, %ldL, (p%d - %ldL) / ((long)threads * 64) + 1, 0, &next }; q[k] = r; pthread_create(&t[k], 0, rrun, &q[k]); }\n", red.c, red.iv, red.c);
          put(&b, "    long acc = p%d;\n    for (int k = 0; k < threads; k++) { pthread_join(t[k], 0); acc = ", red.acc);
          red_combine(&b, &red, "q[k].r", "acc"); put(&b, "; }\n    return acc; }\n");
        }
        /* the depth that keeps about four tasks per thread in flight */
        put(&b, "  if (%d && threads > 1) { int lg = 0; while ((1 << lg) < threads) lg++; dmax = lg + 2;\n", nsite);
        put(&b, "    pthread_attr_init(&attr); pthread_attr_setstacksize(&attr, (size_t)256 << 20); return fp(");
        plist(&b, 0); put(&b, "%s0); }\n  return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, ");\n}\n");
        DBG("compiling (%d function%s, arity %d, %d parallel site%s):\n%s\n", nfun, nfun == 1 ? "" : "s", arity, nsite, nsite == 1 ? "" : "s", b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, arity, funs[0].body->kind);
        if (r) { r->strict = funs[0].strict; r->fmask = funs[0].fmask; }
      } else DBG("declined: expression too large\n");
      free(b.s); free(pre.s); free(pb.s);
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
      if ((c->fmask >> k) & 1u) {                     /* a float parameter: a box, or a float operation to dispatch */
        double d; Val fv; memset(&fv, 0, sizeof fv);
        if (net_read_float(n, v, &d)) args[k] = lin_l(d);
        else if (net_read_value(n, v, DT_FFI, &fv) && fv.kind == 4) args[k] = fv.iv;
        else { ok = 0; DBG("argument %d is not a float\n", k); }
      } else if (!net_read_i64(n, v, &args[k])) { ok = 0; DBG("argument %d is not a number\n", k); }
      if (!y_call(n, p1, p2, &h, &appy, &F)) { ok = 0; break; }   /* forcing rewrote the call itself */
    }
    if (!ok) {
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    extern int lin_threads;
    long r = c->fn(args, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
    Port val = c->kind == 3 ? net_alloc_bool(n, r != 0) : c->kind == 4 ? net_alloc_float(n, lin_d(r)) : net_alloc_scott(n, r);
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
