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
#include <pthread.h>
#include <limits.h>

#include <setjmp.h>
/* THE COMPILED UNITS' THREAD-LOCAL STATE, defined once HERE (this driver is loaded RTLD_GLOBAL) and shared by every
   unit: units run one call at a time on threads they create, so each starts from fresh values.  Initial-exec TLS
   is the fast kind, and it comes from a small fixed block per process -- one copy per unit ran out after a dozen
   units (dlopen: "cannot allocate memory in static TLS block"). */
__thread __attribute__((tls_model("initial-exec"))) jmp_buf lin_jb;
__thread __attribute__((tls_model("initial-exec"))) char *lin_stack_lo;
__thread __attribute__((tls_model("initial-exec"))) long *lin_hp, *lin_he;
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
enum { E_CONST, E_PARAM, E_BIN, E_IF, E_CALL, E_FOP,   /* E_FOP: a float row (FROW[k]) over args */
       E_CTOR, E_MATCH, E_FIELD };   /* data: constructor k (its index) of args; match on a over args (one result per
                                        constructor, in order); field k of a */
typedef struct Expr { int op; long k; struct Expr *a, *b, *c; struct Expr **args; int nargs, kind;   /* kind 1 int, 3 bool */
                      int id, var, vscope, rtag, untag, box; const LinCtor *ci; } Expr;   /* ci: the constructor (E_CTOR, E_FIELD) or one of the datatype's (E_MATCH) */   /* untag: the datatype's blocks carry no tag (box: its one boxed constructor) */   /* rtag: a reused block's constructor + 1 (ownership) */   /* id: a dense index; var: the local it is bound to while emitting */
enum { V_CLO, V_SYM, V_C1, V_COND, V_SELF, V_FIX, V_MCONS, V_MCONS1, V_MCELL, V_MNIL, V_MATCH };   /* V_FIX: a recursive function met, its arguments being collected */   /* V_MATCH: data applied to branches */
struct Lz;
typedef struct Env { int lam; struct Lz *t; struct Env *next; } Env;
typedef struct V { int k; int lam; Env *env; Expr *e; struct Lz *a, *b; struct Lz **args; int nargs; Expr *x; } V;   /* x: to_expr's answer */
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
typedef struct { int lam, arity; Expr *body; unsigned strict; Expr **pnode; struct V **known; struct Env *outer; } Fun;   /* pnode: each parameter's node */
/* known: a FUNCTION-VALUED parameter this copy is specialised to (NULL: a parameter like any other) -- see spec_call */
static Fun *funs; static int nfun, funcap;
static int arity;   /* funs[0]'s, which the entry point and the parallel sites are written for */
static int fail_quiet;   /* a speculative read (is_fun_value): its failures are answers, not declines */
static void fail(const char *why) { if (!failed && !fail_quiet) DBG("declined: %s\n", why); failed = 1; }

static V *mkv(int k) { V *v = A(sizeof *v); v->k = k; return v; }
static Lz *ready(V *v) { Lz *l = A(sizeof *l); l->state = 2; l->v = v; return l; }
static Lz *lzp(Port p, Env *e) { Lz *l = A(sizeof *l); l->state = 0; l->p = p; l->env = e; return l; }
static Lz *lzapp(Lz *f, Lz *x) { Lz *l = A(sizeof *l); l->state = 1; l->f = f; l->x = x; return l; }
static int eid;
static Expr *mke(int op, int kind) { Expr *e = A(sizeof *e); e->op = op; e->kind = kind; e->id = eid++; e->var = -1; return e; }
/* HASH-CONSING: a node equal to one already built (same operation, same children -- which are themselves
   canonical) IS that node, so a value the program computes twice along different paths is one DAG node, and
   the region binder computes it once.  Compiled code is pure, so equal expressions are equal values. */
static Expr **hct; static int hccap, hcn;
static unsigned long hc_hash(const Expr *e) {
  unsigned long h = (unsigned long)e->op * 1000003u ^ (unsigned long)e->k * 2654435761u ^ (unsigned long)e->kind * 97u
                  ^ (unsigned long)e->nargs * 131u;
  h = h * 31 + (uintptr_t)e->a; h = h * 31 + (uintptr_t)e->b; h = h * 31 + (uintptr_t)e->c; h = h * 31 + (uintptr_t)e->ci;
  for (int i = 0; i < e->nargs && e->args; i++) h = h * 31 + (uintptr_t)e->args[i];
  return h ^ (h >> 29);
}
static int hc_eq(const Expr *x, const Expr *y) {
  if (x->op != y->op || x->k != y->k || x->kind != y->kind || x->nargs != y->nargs || x->a != y->a || x->b != y->b || x->c != y->c || x->ci != y->ci) return 0;
  if (!x->args != !y->args) return 0;
  for (int i = 0; i < x->nargs && x->args; i++) if (x->args[i] != y->args[i]) return 0;
  return 1;
}
static Expr *hc(Expr *e) {
  if (!e) return e;
  if (e->op == E_IF && e->b == e->c) return e->b;   /* both branches one value: the condition decides nothing */
  if (hcn * 2 >= hccap) {
    int oc = hccap; Expr **ot = hct;
    hccap = hccap ? hccap * 2 : 1024; hct = calloc((size_t)hccap, sizeof *hct); hcn = 0;
    for (int i = 0; i < oc; i++) if (ot[i]) { unsigned long j = hc_hash(ot[i]) & (unsigned long)(hccap - 1); while (hct[j]) j = (j + 1) & (unsigned long)(hccap - 1); hct[j] = ot[i]; hcn++; }
    free(ot);
  }
  unsigned long j = hc_hash(e) & (unsigned long)(hccap - 1);
  for (; hct[j]; j = (j + 1) & (unsigned long)(hccap - 1)) if (hc_eq(hct[j], e)) return hct[j];
  hct[j] = e; hcn++; return e;
}
static void hc_reset(void) { if (hct) memset(hct, 0, (size_t)hccap * sizeof *hct); hcn = 0; }

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
static int compile_body_spec(int G, Env *outer, V **known);
static V *fix_call(int G, Env *genv, int target, Lz **args, int nargs);
static int fun_arity(int G);
static int is_y(const Net *n, int h);
static int op_head(int lam) {
  Port q = dhop(N, W(N, (Port){lam, 2}));            /* (read through a fan: a head being copied is still one) */
  if (!is(N, q, APP, 1)) return 0;
  Port k = dhop(N, W(N, (Port){q.node, 0})), x = dhop(N, W(N, (Port){q.node, 2}));
  if (!is(N, k, LAM, 0) || x.node != lam || x.port != 1) return 0;
  Port kb = W(N, (Port){k.node, 1});
  return kb.node < 0 || (live(N, kb) && N->tag[kb.node] == ERA);
}
static long const_int(V *v, int *ok);
static long fold_op(long code, long x, long y) {   /* an integer operation on known operands: the C's own rows */
  switch (code) {
  case LIN_OP_ADD: return lin_i64_add(x, y);   case LIN_OP_SUB: return lin_i64_sub(x, y);
  case LIN_OP_MUL: return lin_i64_mul(x, y);   case LIN_OP_DIV: return lin_i64_div(x, y);
  case LIN_OP_MOD: return lin_i64_mod(x, y);   case LIN_OP_POW: return lin_i64_pow(x, y);
  case LIN_OP_BAND: return lin_i64_band(x, y); case LIN_OP_BOR: return lin_i64_bor(x, y);
  case LIN_OP_BXOR: return lin_i64_bxor(x, y); case LIN_OP_SHL: return lin_i64_shl(x, y);
  case LIN_OP_SHR: return lin_i64_shr(x, y);
  case LIN_OP_EQ: return x == y; case LIN_OP_LT: return x < y; case LIN_OP_LEQ: return x <= y;
  case LIN_OP_GT: return x > y;  case LIN_OP_GEQ: return x >= y;
  case LIN_OP_FADD: return lin_f64_add(x, y);  case LIN_OP_FSUB: return lin_f64_sub(x, y);
  case LIN_OP_FMUL: return lin_f64_mul(x, y);  case LIN_OP_FDIV: return lin_f64_div(x, y);
  case LIN_OP_FEQ: return lin_f64_eq(x, y);    case LIN_OP_FLT: return lin_f64_lt(x, y);
  case LIN_OP_FLEQ: return lin_f64_leq(x, y);  case LIN_OP_FMIN: return lin_f64_min(x, y);
  case LIN_OP_FMAX: return lin_f64_max(x, y);  case LIN_OP_FSQRT: return lin_f64_sqrt(x);
  case LIN_OP_FFLOOR: return lin_f64_floorf(x); case LIN_OP_FTOI: return lin_f64_floor(x);
  case LIN_OP_ITOF: return lin_f64_of_int(x);  case LIN_OP_FABS: return lin_f64_abs(x);
  case LIN_OP_FSIGN: return lin_f64_sign(x);   case LIN_OP_FFRACT: return lin_f64_fract(x);
  }
  return 0;
}
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
  int cmp = LIN_OP_IS_CMP(code);
  if (slot[0]->op == E_CONST && slot[1]->op == E_CONST && slot[0]->kind == 1 && slot[1]->kind == 1) {
    /* both operands known: the operation is its value (the same rows the emitted C calls) */
    v->e = mke(E_CONST, cmp ? 3 : 1); v->e->k = fold_op(code, slot[0]->k, slot[1]->k); v->e = hc(v->e); return v;
  }
  v->e = mke(E_BIN, cmp ? 3 : 1); v->e->k = code; v->e->a = slot[0]; v->e->b = slot[1]; v->e = hc(v->e);
  return v;
}

/* DATA.  A constructor states which it is: its body is `((\_c (d_i f1..fk)) ID)` and a match branch for it is
   `((\_m BRANCH) ID)` (lin.h, the constructor registry), so a value's shape is never a guess -- a numeral and
   a cons cell are the same lambdas, the marker is what tells them apart.  A KNOWN constructor (a closure) needs
   nothing here: applying it to the branches is beta.  An UNKNOWN one (a parameter, a call's result, a field)
   applied to the branches collects them; when the datatype's m are all there it is a match: each branch applied
   to that constructor's fields, symbolically, one result per constructor. */
static int marker_app(Port p, Port *body, int *lam, Port *idp) {   /* `((\_x BODY) ID)`: its parts */
  Port q = dhop(N, p);
  if (!is(N, q, APP, 1)) return 0;
  Port fl = dhop(N, W(N, (Port){q.node, 0}));
  if (!is(N, fl, LAM, 0)) return 0;
  Port b = W(N, (Port){fl.node, 1});
  if (!(b.node >= 0 && live(N, b) && N->tag[b.node] == ERA)) return 0;   /* the marker's binder is unused */
  *lam = fl.node; *body = W(N, (Port){fl.node, 2}); *idp = W(N, (Port){q.node, 2});
  return 1;
}
static const LinCtor *marker_ctor(Port idp, Env *env, long *id) {
  int ok; *id = const_int(eval(idp, env), &ok);
  return ok ? lin_ctor_info(*id) : NULL;
}
/* LAYOUT: a datatype with exactly ONE constructor that has fields (a tree, a list, most ADTs) needs no tag in its
   blocks -- being a block at all says which constructor it is -- so a match tests only the low bit, as C tests a
   pointer for null, and a node is a word smaller.  (Measured: the tag load was half of a tree insert.) */
static int dt_boxed(const char *dt, int *box) {      /* how many constructors of dt have fields; *box: the last */
  int n = 0; const LinCtor *c;
  for (long k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->k > 0) { n++; *box = c->i; }
  return n;
}
static Expr *field_expr(Expr *scrut, int j, int untag, const LinCtor *ci) {
  Expr *e = mke(E_FIELD, 1); e->a = scrut; e->k = j; e->untag = untag; e->ci = ci; return hc(e);
}
static V *match_add(V *m, Lz *x) {
  if (x->state != 0) { fail("a match branch that is not net structure"); return NULL; }
  Port body, idp; int lam; long id;
  if (!marker_app(x->p, &body, &lam, &idp)) { fail("a parameter applied to something that is not a match branch (a function parameter?)"); return NULL; }
  const LinCtor *ci = marker_ctor(idp, x->env, &id);
  if (!ci || ci->i != m->nargs) { fail("a match branch out of its constructor's place"); return NULL; }
  V *v = mkv(V_MATCH); v->e = m->e; v->nargs = m->nargs + 1;
  v->args = A(sizeof(Lz *) * (size_t)v->nargs);
  if (m->nargs) memcpy(v->args, m->args, sizeof(Lz *) * (size_t)m->nargs);
  Env *e = A(sizeof *e); e->lam = lam; e->t = ready(mkv(V_MNIL)); e->next = x->env;   /* (the marker's binder: unused) */
  v->args[m->nargs] = lzp(body, e);
  v->lam = ci->m;
  if (v->nargs < ci->m) return v;
  /* every constructor has its branch: the match's value */
  Expr *r = mke(E_MATCH, 1); r->a = m->e; r->nargs = ci->m; r->args = A(sizeof(Expr *) * (size_t)ci->m);
  int box = 0, untag = dt_boxed(ci->dt, &box) == 1;
  r->untag = untag; r->box = box; r->ci = ci;
  int kind = -1;
  for (int i = 0; i < ci->m; i++) {
    const LinCtor *c2 = NULL;
    for (long k = 1; (c2 = lin_ctor_info(k)); k++) if (c2->dt == ci->dt && c2->i == i) break;
    if (!c2) { fail("a constructor missing from the registry"); return NULL; }
    V *b = force(v->args[i]);
    for (int j = 0; b && j < c2->k; j++) { V *fv = mkv(V_SYM); fv->e = field_expr(m->e, j, untag, c2); b = apply(b, ready(fv)); }
    if (!(r->args[i] = to_expr(b))) return NULL;
    if (r->args[i]->op == E_CALL) continue;          /* (a recursive call has the kind the other branches say) */
    int bk = r->args[i]->kind;
    kind = kind < 0 ? bk : (kind == bk ? kind : (kind == 5 || bk == 5 ? 5 : 1));
  }
  r->kind = kind < 0 ? 1 : kind;
  V *res = mkv(V_SYM); res->e = hc(r); return res;
}
/* A known constructor value, read as data: the closure's m dispatch binders, the marker, the fields. */
static Expr *ctor_expr(V *v) {
  int nl = 0, di = -1; Port q = (Port){v->lam, 0};
  for (int i = 0; i < N->nn && is(N, q, LAM, 0); i++) { nl++; q = dhop(N, W(N, (Port){q.node, 2})); }
  Port body, idp; int mlam; long id;
  if (!marker_app(q, &body, &mlam, &idp)) return NULL;
  const LinCtor *ci = marker_ctor(idp, v->env, &id);
  if (!ci || ci->m != nl) return NULL;              /* the registry sizes everything below */
  q = (Port){v->lam, 0};
  for (int i = 0; i < ci->i; i++) q = dhop(N, W(N, (Port){q.node, 2}));
  di = q.node;                                       /* the dispatch binder the body applies */
  Port *fields = A(sizeof *fields * (size_t)(ci->k ? ci->k : 1)); int nf = 0; Port x = dhop(N, body);
  while (is(N, x, APP, 1) && nf < ci->k) { fields[nf++] = W(N, (Port){x.node, 2}); x = dhop(N, W(N, (Port){x.node, 0})); }
  if (nf != ci->k || !(x.node == di && x.port == 1)) return NULL;
  Expr *e = mke(E_CTOR, 5); e->k = ci->i; e->nargs = nf; e->args = A(sizeof(Expr *) * (size_t)(nf ? nf : 1));
  { int box; e->untag = dt_boxed(ci->dt, &box) == 1; } e->ci = ci;
  for (int j = 0; j < nf; j++)                       /* (collected last field first) */
    if (!(e->args[nf - 1 - j] = to_expr(eval(fields[j], v->env)))) return NULL;
  return hc(e);
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
    if (is_y(N, f->lam)) {                          /* another recursive function: compiled into the unit when called */
      V *g = force(x);
      if (!g || g->k != V_CLO) { fail("a fixpoint of something that is not a function"); return NULL; }
      V *v = mkv(V_FIX); v->lam = g->lam; v->env = g->env; v->nargs = 0; return v;   /* (in its own closure) */
    }
    Env *e = A(sizeof *e); e->lam = f->lam; e->t = x; e->next = f->env;
    return eval(W(N, (Port){f->lam, 2}), e);
  }
  case V_SYM: {
    if (f->e->kind != 3) {                          /* DATA taken apart: a branch states its constructor */
      V *m = mkv(V_MATCH); m->e = f->e; m->nargs = 0; m->args = NULL;
      return match_add(m, x);
    }
    V *v = mkv(V_C1); v->e = f->e; v->a = x; return v;
  }
  case V_MATCH: return match_add(f, x);
  case V_C1:                                        /* a known condition is the branch it picks */
    if (f->e->op == E_CONST) return force(f->e->k ? f->a : x);
    { V *v = mkv(V_COND); v->e = f->e; v->a = f->a; v->b = x; return v; }
  case V_COND: { V *v = mkv(V_COND); v->e = f->e; v->a = lzapp(f->a, x); v->b = lzapp(f->b, x); return v; }
  case V_SELF: case V_FIX: {                        /* a function of the unit (V_SELF: its index), being applied */
    int ar = f->k == V_SELF ? funs[f->lam].arity : fun_arity(f->lam);
    if (ar <= 0) { fail("a function with no parameters"); return NULL; }
    V *v = mkv(f->k); v->lam = f->lam; v->env = f->env; v->nargs = f->nargs + 1; v->args = A(sizeof(Lz *) * (size_t)v->nargs);
    memcpy(v->args, f->args, sizeof(Lz *) * (size_t)f->nargs); v->args[f->nargs] = x;
    if (v->nargs < ar) return v;
    return f->k == V_SELF ? fix_call(funs[f->lam].lam, funs[f->lam].outer, f->lam, v->args, ar)
                          : fix_call(f->lam, f->env, -1, v->args, ar);
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
    Expr *e = mke(E_CONST, 4); e->k = lin_l(strtod(lit, NULL)); return hc(e);
  }
  for (int k = 0; k < N_OF(FROW); k++) {
    if (strcmp(name, FROW[k].name) || argc != FROW[k].arity) continue;
    Expr *e = mke(E_FOP, FROW[k].kind); e->k = k; e->nargs = argc; e->args = A(sizeof(Expr *) * (size_t)argc);
    for (int i = 0; i < argc; i++) if (!(e->args[i] = to_expr(argv[i]))) return NULL;
    return hc(e);
  }
  fail("an FFI call the compiler does not know"); return NULL;
}

static Expr *to_expr_v(V *v);
static Expr *to_expr(V *v) {                       /* one answer per value: a shared value is one node */
  if (failed || !v) return NULL;
  if (v->k == V_SYM) return v->e;
  if (!v->x) v->x = to_expr_v(v);
  return v->x;
}
static Expr *to_expr_v(V *v) {
  if (v->k == V_COND) {
    Expr *e = mke(E_IF, 1); e->a = v->e; e->b = to_expr(force(v->a)); e->c = to_expr(force(v->b));
    if (!e->b || !e->c) return NULL;
    e->kind = e->b->op == E_CALL ? e->c->kind : e->b->kind;   /* (a recursive call's kind is the other branch's) */
    return hc(e);
  }
  if (v->k == V_CLO) {
    Expr *d = ctor_expr(v);                          /* data first: its marker is unmistakable */
    if (d || failed) return d;
    Expr *f = ffi_expr(v);
    if (f || failed) return f;
    int ok; long k = const_int(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 1); e->k = k; return hc(e); }
    int bk = const_bool(v, &ok);
    if (ok) { Expr *e = mke(E_CONST, 3); e->k = bk; return hc(e); }
    fail("a closure where a number belongs"); return NULL;
  }
  if (v->k == V_MATCH) { fail("a match with branches missing"); return NULL; }
  fail("a value with no number"); return NULL;
}

/* The walks below run over the evaluator's DAG, where a shared node is reached along many paths: walked as a
   tree they are exponential (a soft-float function is a cascade of `let`s).  Each keeps one answer per node id
   for the current GENERATION: mm_new(w) starts one, a node's answer is kept until then. */
enum { MM_STRICT, MM_SAFE, MM_CALL, MM_SELF, MM_SITE, MM_SSTR, MM_NUM, MM_OCC, MM_UNIQ, MM_N };
static unsigned *mm_gen[MM_N], *mm_val[MM_N], mm_g[MM_N]; static int mm_cap[MM_N];
static void mm_new(int w) {
  if (mm_cap[w] < eid) {
    int c = eid * 2 + 64;
    mm_gen[w] = realloc(mm_gen[w], (size_t)c * sizeof **mm_gen); mm_val[w] = realloc(mm_val[w], (size_t)c * sizeof **mm_val);
    memset(mm_gen[w] + mm_cap[w], 0, (size_t)(c - mm_cap[w]) * sizeof **mm_gen); mm_cap[w] = c;
  }
  mm_g[w]++;
}
static int mm_has(int w, const Expr *e) { return e->id < mm_cap[w] && mm_gen[w][e->id] == mm_g[w]; }
static unsigned mm_put(int w, const Expr *e, unsigned v) {
  if (e->id < mm_cap[w]) { mm_gen[w][e->id] = mm_g[w]; mm_val[w][e->id] = v; }
  return v;
}
#define MEMO(w, e) do { if (mm_has(w, e)) return mm_val[w][(e)->id]; } while (0)

/* Strictness: the parameters certainly evaluated, as a bit set.  A call evaluates the arguments its callee is
   strict in, so the sets are a fixpoint over the unit (compile_unit iterates them down from "everything"). */
static int strict_fid = -2;   /* the function whose strictness is asked: an outer function's parameter is not its own */
static unsigned strict_r(Expr *e) {
  MEMO(MM_STRICT, e);
  unsigned s = 0;
  switch (e->op) {
  case E_PARAM: s = strict_fid == -2 || e->nargs == strict_fid ? 1u << e->k : 0; break;
  case E_BIN: s = strict_r(e->a) | strict_r(e->b); break;
  case E_IF: s = strict_r(e->a) | (strict_r(e->b) & strict_r(e->c)); break;
  case E_CALL: for (int i = 0; i < e->nargs; i++) if ((funs[e->k].strict >> i) & 1u) s |= strict_r(e->args[i]); break;
  case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) s |= strict_r(e->args[i]); break;
  case E_FIELD: s = strict_r(e->a); break;
  case E_MATCH: { unsigned all = ~0u; for (int i = 0; i < e->nargs; i++) all &= strict_r(e->args[i]); s = strict_r(e->a) | all; break; }
  default: break;
  }
  return mm_put(MM_STRICT, e, s);
}
static unsigned strict(Expr *e) { mm_new(MM_STRICT); return strict_r(e); }   /* funs[].strict changes between rounds */
static int has_call(const Expr *e);
/* C evaluates EVERY argument of a call, the net only the ones the callee uses.  An argument in a position the
   callee may ignore is therefore allowed only if it cannot diverge or cost: no call inside it. */
/* STRICTNESS AT A CALL SITE.  A parameter its function may skip can still be certainly read by THIS call: the
   arguments the call knows (constants) decide the callee's first conditionals.  `(sqrt_loop m 54 0 0)` reads `m`
   although the loop's last step does not, because 54 is not the last step.  So the callee's body is walked with
   the known arguments substituted and every condition they decide folded; its recursive calls count only what
   the fixpoint already proved.  (One step of partial evaluation: general, and never assumes more than the
   function does on those arguments.) */
static const Expr *const *site_args; static int site_fid;
static long *cv_val; static int cv_cap;
static int cval(const Expr *e, long *out) {           /* the node's value, when the known arguments decide it */
  if (e->op == E_CONST) { *out = e->k; return e->kind == 1 || e->kind == 3; }
  if (e->op == E_PARAM) {
    if (e->nargs != site_fid || !site_args) return 0;
    const Expr *a = site_args[e->k];
    if (a->op != E_CONST || (a->kind != 1 && a->kind != 3)) return 0;
    *out = a->k; return 1;
  }
  if (e->op != E_BIN && e->op != E_IF) return 0;
  if (cv_cap < mm_cap[MM_SITE]) { cv_cap = mm_cap[MM_SITE]; cv_val = realloc(cv_val, (size_t)cv_cap * sizeof *cv_val); }
  if (mm_has(MM_SITE, e)) { unsigned m = mm_val[MM_SITE][e->id]; if (m & 2u) *out = cv_val[e->id]; return (m & 2u) != 0; }
  long x, y, r = 0; int ok = 0;
  if (e->op == E_BIN) { if (cval(e->a, &x) && cval(e->b, &y)) { r = fold_op(e->k, x, y); ok = 1; } }
  else if (cval(e->a, &x)) ok = cval(x ? e->b : e->c, &r);
  if (ok && e->id < cv_cap) cv_val[e->id] = r;
  mm_put(MM_SITE, e, ok ? 2u : 0u);
  if (ok) *out = r;
  return ok;
}
static unsigned strict_site_r(const Expr *e) {
  MEMO(MM_SSTR, e);
  long c; unsigned s = 0;
  switch (e->op) {
  case E_PARAM: s = e->nargs == site_fid ? 1u << e->k : 0; break;
  case E_BIN: s = strict_site_r(e->a) | strict_site_r(e->b); break;
  case E_IF:
    s = strict_site_r(e->a);
    if (cval(e->a, &c)) s |= strict_site_r(c ? e->b : e->c);
    else s |= strict_site_r(e->b) & strict_site_r(e->c);
    break;
  case E_CALL: for (int i = 0; i < e->nargs; i++) if ((funs[e->k].strict >> i) & 1u) s |= strict_site_r(e->args[i]); break;
  case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) s |= strict_site_r(e->args[i]); break;
  case E_FIELD: s = strict_site_r(e->a); break;
  case E_MATCH: { unsigned all = ~0u; for (int i = 0; i < e->nargs; i++) all &= strict_site_r(e->args[i]); s = strict_site_r(e->a) | all; break; }
  default: break;
  }
  return mm_put(MM_SSTR, e, s);
}
static unsigned strict_site(const Expr *call) {       /* the parameters this call certainly makes its callee read */
  unsigned s = funs[call->k].strict;
  if (!funs[call->k].body) return s;
  int any = 0; for (int i = 0; i < call->nargs; i++) any |= call->args[i]->op == E_CONST;
  if (!any) return s;
  mm_new(MM_SITE); mm_new(MM_SSTR); site_args = (const Expr *const *)call->args; site_fid = (int)call->k;
  s |= strict_site_r(funs[call->k].body);
  site_args = NULL; site_fid = -1;
  return s;
}
static int args_safe_r(const Expr *e) {
  MEMO(MM_SAFE, e);
  int ok = 1;
  switch (e->op) {
  case E_BIN: ok = args_safe_r(e->a) && args_safe_r(e->b); break;
  case E_IF: ok = args_safe_r(e->a) && args_safe_r(e->b) && args_safe_r(e->c); break;
  case E_CALL: {
    unsigned st = funs[e->k].strict;
    for (int i = 0; i < e->nargs; i++) if (!((st >> i) & 1u) && has_call(e->args[i])) { st = strict_site(e); break; }
    for (int i = 0; i < e->nargs && ok; i++)
      ok = !(!((st >> i) & 1u) && has_call(e->args[i])) && args_safe_r(e->args[i]);
    break; }
  case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs && ok; i++) ok = args_safe_r(e->args[i]); break;
  case E_FIELD: ok = args_safe_r(e->a); break;
  case E_MATCH: ok = args_safe_r(e->a); for (int i = 0; i < e->nargs && ok; i++) ok = args_safe_r(e->args[i]); break;
  default: break;
  }
  return (int)mm_put(MM_SAFE, e, (unsigned)ok);
}
static int args_safe(const Expr *e) { mm_new(MM_SAFE); return args_safe_r(e); }

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
/* A recursive call of the ENTRY function: where a recursion's work is, so where splitting across threads pays.
   A call to a helper (a bit count, a small loop) is not worth a thread. */
/* (structure only, so remembered for the whole compile: compile_fn starts the generation) */
static int has_self(const Expr *e) {
  MEMO(MM_SELF, e);
  int r = 0;
  switch (e->op) {
  case E_CALL: r = e->k == 0; for (int i = 0; i < e->nargs && !r; i++) r = has_self(e->args[i]); break;
  case E_BIN: r = has_self(e->a) || has_self(e->b); break;
  case E_IF: r = has_self(e->a) || has_self(e->b) || has_self(e->c); break;
  case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs && !r; i++) r = has_self(e->args[i]); break;
  case E_FIELD: r = has_self(e->a); break;
  case E_MATCH: r = has_self(e->a); for (int i = 0; i < e->nargs && !r; i++) r = has_self(e->args[i]); break;
  default: break;
  }
  return (int)mm_put(MM_SELF, e, (unsigned)r);
}
static int has_call(const Expr *e) {
  MEMO(MM_CALL, e);
  int r = 0;
  switch (e->op) {
  case E_CALL: r = 1; break;
  case E_BIN: r = has_call(e->a) || has_call(e->b); break;
  case E_IF: r = has_call(e->a) || has_call(e->b) || has_call(e->c); break;
  case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs && !r; i++) r = has_call(e->args[i]); break;
  case E_FIELD: r = has_call(e->a); break;
  case E_MATCH: r = has_call(e->a); for (int i = 0; i < e->nargs && !r; i++) r = has_call(e->args[i]); break;
  default: break;
  }
  return (int)mm_put(MM_CALL, e, (unsigned)r);
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
static int uses_data;   /* the unit builds or reads data: it gets the arena and the guard (compile_fn) */
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
  case E_CALL: case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) count_uses(e->args[i]); break;
  case E_FIELD: count_uses(e->a); break;
  case E_MATCH: count_uses(e->a); for (int i = 0; i < e->nargs; i++) count_uses(e->args[i]); break;
  }
}
/* The nodes a region CERTAINLY evaluates: what its root reaches without entering a branch, plus what BOTH arms of
   a conditional certainly evaluate -- cert(if c a b) = cert(c) + (cert(a) & cert(b)).  The intersection is what
   keeps a value used in each arm of a cascade of conditionals from being written out once per arm (and, nested,
   exponentially often), without ever hoisting work only one arm does.  Sets are sorted id arrays, memoised per
   region by node. */
typedef struct { int *v, n; } ISet;
static ISet *st_cert; static unsigned *st_cstamp; static int st_ccap;
static ISet iset_union(ISet x, ISet y, int extra) {
  ISet r; r.v = malloc((size_t)(x.n + y.n + 1) * sizeof *r.v); r.n = 0;
  int i = 0, j = 0, put_extra = extra >= 0;
  while (i < x.n || j < y.n || put_extra) {
    int c = INT_MAX;
    if (i < x.n && x.v[i] < c) c = x.v[i];
    if (j < y.n && y.v[j] < c) c = y.v[j];
    if (put_extra && extra < c) c = extra;
    if (i < x.n && x.v[i] == c) i++;
    if (j < y.n && y.v[j] == c) j++;
    if (put_extra && extra == c) put_extra = 0;
    r.v[r.n++] = c;
  }
  return r;
}
static ISet iset_inter(ISet x, ISet y) {
  ISet r; r.v = malloc((size_t)(x.n < y.n ? x.n : y.n) * sizeof *r.v + sizeof *r.v); r.n = 0;
  for (int i = 0, j = 0; i < x.n && j < y.n;) {
    if (x.v[i] < y.v[j]) i++; else if (x.v[i] > y.v[j]) j++; else { r.v[r.n++] = x.v[i]; i++; j++; }
  }
  return r;
}
static ISet cert(const Expr *e) {
  if (st_ccap < eid) {
    int c = eid * 2 + 64;
    st_cert = realloc(st_cert, (size_t)c * sizeof *st_cert); st_cstamp = realloc(st_cstamp, (size_t)c * sizeof *st_cstamp);
    memset(st_cstamp + st_ccap, 0, (size_t)(c - st_ccap) * sizeof *st_cstamp); st_ccap = c;
  }
  if (st_cstamp[e->id] == stamp) return st_cert[e->id];
  ISet r = { NULL, 0 }, t;
  if (bound(e)) { r.v = malloc(sizeof *r.v); r.v[0] = e->id; r.n = 1; }
  else switch (e->op) {
  case E_BIN: r = iset_union(cert(e->a), cert(e->b), e->id); break;
  case E_IF: { ISet i = iset_inter(cert(e->b), cert(e->c)); r = iset_union(cert(e->a), i, e->id); free(i.v); break; }
  case E_FIELD: r = iset_union(cert(e->a), (ISet){ NULL, 0 }, e->id); break;
  case E_MATCH: {                                   /* the scrutinee, and what EVERY branch evaluates */
    ISet i = { NULL, 0 }; int first = 1;
    for (int k = 0; k < e->nargs; k++) {
      if (first) { ISet c0 = cert(e->args[k]); i.v = malloc((size_t)(c0.n + 1) * sizeof *i.v); memcpy(i.v, c0.v, (size_t)c0.n * sizeof *i.v); i.n = c0.n; first = 0; }
      else { ISet j = iset_inter(i, cert(e->args[k])); free(i.v); i = j; }
    }
    r = iset_union(cert(e->a), i, e->id); free(i.v); break;
  }
  case E_CALL: case E_FOP: case E_CTOR:
    r.v = malloc(sizeof *r.v); r.v[0] = e->id; r.n = 1;
    for (int k = 0; k < e->nargs; k++) { t = iset_union(r, cert(e->args[k]), -1); free(r.v); r = t; }
    break;
  default: r.v = malloc(sizeof *r.v); r.v[0] = e->id; r.n = 1;
  }
  if (st_cstamp[e->id]) free(st_cert[e->id].v);   /* the set of an earlier region: that region is done with it */
  st_cstamp[e->id] = stamp; st_cert[e->id] = r;
  return r;
}
static int in_set(ISet s, int id) {
  int lo = 0, hi = s.n - 1;
  while (lo <= hi) { int m = (lo + hi) / 2; if (s.v[m] == id) return 1; if (s.v[m] < id) lo = m + 1; else hi = m - 1; }
  return 0;
}
static void certain(const Expr *e, ISet c, const Expr ***out, int *n, int *cap) {   /* post-order: dependencies first */
  if (st_need[e->id] == stamp || bound(e)) return;
  st_need[e->id] = stamp;
  switch (e->op) {
  case E_BIN: certain(e->a, c, out, n, cap); certain(e->b, c, out, n, cap); break;
  case E_IF: certain(e->a, c, out, n, cap); certain(e->b, c, out, n, cap); certain(e->c, c, out, n, cap); break;
  case E_CALL: case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) certain(e->args[i], c, out, n, cap); break;
  case E_FIELD: certain(e->a, c, out, n, cap); break;
  case E_MATCH: certain(e->a, c, out, n, cap); for (int i = 0; i < e->nargs; i++) certain(e->args[i], c, out, n, cap); break;
  }
  if (!in_set(c, e->id)) return;
  if (*n >= *cap) *out = realloc(*out, (size_t)(*cap = *cap ? *cap * 2 : 16) * sizeof **out);
  (*out)[(*n)++] = e;
}
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  st_grow(); stamp += 2;
  count_uses(e);
  const Expr **cand = NULL; int nc = 0, cc = 0;
  certain(e, cert(e), &cand, &nc, &cc);
  int nb = 0, ok = 1, nk = 0;
  for (int i = 0; i < nc; i++) {                   /* choose first: emitting a binding runs nested regions' passes */
    const Expr *x = cand[i];
    if (x != e && st_uses[x->id] >= 2 && x->op != E_CONST && x->op != E_PARAM) cand[nk++] = x;
  }
  nc = nk;
  for (int i = 0; i < nc && ok; i++) {
    Expr *x = (Expr *)cand[i];
    if (!nb++) put(b, "({ ");
    int k = nvar++;                                /* reserved BEFORE the value is written: a binding nested in it takes later numbers */
    put(b, "long v%d = ", k);
    ok = emitx(b, pre, x, par, budget - 1);
    put(b, "; ");
    x->var = k; x->vscope = fscope;
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
    [LIN_OP_SHL] = "lin_i64_shl", [LIN_OP_SHR] = "lin_i64_shr",
    [LIN_OP_FADD] = "lin_f64_add", [LIN_OP_FSUB] = "lin_f64_sub", [LIN_OP_FMUL] = "lin_f64_mul",
    [LIN_OP_FDIV] = "lin_f64_div", [LIN_OP_FEQ] = "lin_f64_eq", [LIN_OP_FLT] = "lin_f64_lt", [LIN_OP_FLEQ] = "lin_f64_leq",
    [LIN_OP_FMIN] = "lin_f64_min", [LIN_OP_FMAX] = "lin_f64_max", [LIN_OP_FSQRT] = "lin_f64_sqrt",
    [LIN_OP_FFLOOR] = "lin_f64_floorf", [LIN_OP_FTOI] = "lin_f64_floor", [LIN_OP_ITOF] = "lin_f64_of_int",
    [LIN_OP_FABS] = "lin_f64_abs", [LIN_OP_FSIGN] = "lin_f64_sign", [LIN_OP_FFRACT] = "lin_f64_fract" };
  int unary = k >= LIN_OP_FSQRT && k <= LIN_OP_FFRACT;   /* (their second operand is the 0 the library writes) */
  if (k >= LIN_OP_EQ && k <= LIN_OP_GEQ) put(b, "(long)(%s %s %s)", x, fn[k], y);
  else if (unary) put(b, "%s(%s)", fn[k], x);
  else put(b, "%s(%s, %s)", fn[k], x, y);
  return 1;
}
/* A GROUP of operands evaluated at once: every one but the last that contains a call runs on a new thread
   (while `d < dmax`), the last runs here, and the rest are plain.  Writes "({ ...;" -- the caller writes the
   use of names[i] and closes it with "; })". */
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static int par_group(Buf *b, Buf *pre, const Expr **xs, int n, Buf *names, int budget) {
  int last = -1, ok = 1;
  for (int i = 0; i < n; i++) if (has_self(xs[i])) last = i;
  put(b, "({ ");
  int *site = calloc((size_t)n, sizeof *site);
  for (int i = 0; ok && i < n; i++) {
    site[i] = -1;
    if (!has_self(xs[i]) || i == last) continue;
    int k = site[i] = nsite++;
    Buf sb = nbuf(512);            /* the site: this operand as a function of the parameters */
    put(&sb, "static long site%d(", k); plist(&sb, 1); put(&sb, "%sint d) { return ", arity ? ", " : "");
    int save = fscope; fscope = ++nvar + (1 << 20);   /* a new C function: no enclosing local is in scope */
    ok = emit_region(&sb, pre, xs[i], 1, budget - 1);
    fscope = save;
    put(&sb, "; }\ntypedef struct { long p[%d]; int d; long r; } S%d;\n", arity, k);
    put(&sb, "static void *run%d(void *v) { S%d *s = v; LIN_TASK_START((size_t)256 << 20); s->r = site%d(", k, k, k);
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
      put(b, "long x%d_ = sp%d_ ? (pthread_join(t%d_, 0), LIN_JOINED, s%d_.r) : site%d(", k, k, k, k, k); plist(b, 0);
      put(b, "%sd); ", arity ? ", " : "");
      put(&names[i], "x%d_", k);
    } else if (i == last) put(&names[i], "y%d_", self);
    else ok = emitx(&names[i], pre, xs[i], 1, budget - 1);
  }
  free(site);
  return ok;
}
/* LAMBDA LIFTING.  A function the unit specialised to a closure reads what the closure captured -- often a parameter
   of the function that made it (`(smap (\x (mul x k)) s)` inside a loop over k).  Such a function takes those
   outer parameters as EXTRA C parameters, and every call passes them on: what a function reads from outside, its
   callers read too, unless it is their own.  (h, k): parameter k of function h, h = -1 the entry's. */
typedef struct { int h; long k; } FV;
static FV **fvs; static int *nfv, lifted;
static int fv_has(int f, int h, long k) { for (int i = 0; i < nfv[f]; i++) if (fvs[f][i].h == h && fvs[f][i].k == k) return 1; return 0; }
static int fv_add(int f, int h, long k) {
  if (h == f || fv_has(f, h, k)) return 0;
  fvs[f] = realloc(fvs[f], sizeof **fvs * (size_t)(nfv[f] + 1)); fvs[f][nfv[f]++] = (FV){ h, k }; return 1;
}
static int fv_changed;
static void fv_walk(int f, const Expr *e) {
  if (!e || mm_has(MM_SSTR, e)) return;
  mm_put(MM_SSTR, e, 1);
  if (e->op == E_PARAM && e->nargs != f) fv_changed |= fv_add(f, e->nargs, e->k);
  if (e->op == E_CALL) for (int i = 0; i < nfv[e->k]; i++) fv_changed |= fv_add(f, fvs[e->k][i].h, fvs[e->k][i].k);
  if (e->a) fv_walk(f, e->a);
  if (e->b) fv_walk(f, e->b);
  if (e->c) fv_walk(f, e->c);
  for (int i = 0; i < e->nargs && e->args; i++) fv_walk(f, e->args[i]);
}
static void lift(void) {
  if (fvs) { for (int i = 0; i < lifted; i++) free(fvs[i]); }
  free(fvs); free(nfv);
  fvs = calloc((size_t)(nfun ? nfun : 1), sizeof *fvs); nfv = calloc((size_t)(nfun ? nfun : 1), sizeof *nfv);
  for (int round = 0, ch = 1; ch && round <= nfun * 64 + 64; round++) {
    ch = 0;
    for (int f = 0; f < nfun; f++) { fv_changed = 0; mm_new(MM_SSTR); fv_walk(f, funs[f].body); ch |= fv_changed; }
  }
  lifted = nfun;
}
static void fv_params(Buf *b, int f, int typed, int lead) {   /* a function's extra parameters, after its own */
  for (int i = 0; i < nfv[f]; i++) put(b, typed ? "%slong l%d_%ld" : "%sl%d_%ld", (lead || i) ? ", " : "", fvs[f][i].h + 1, fvs[f][i].k);
}
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  if (budget <= 0) return 0;
  if (bound(e)) { put(b, "v%d", e->var); return 1; }
  switch (e->op) {
  case E_CONST: if (e->k == (long)(1UL << (LIN_INT_BITS - 1))) put(b, "(-%ldL-1)", -(e->k + 1)); else put(b, "(%ldL)", e->k); return 1;
  case E_PARAM:   /* an outer function's parameter: lifted into this one's extra parameters */
    if (e->nargs == emitting) { put(b, "p%ld", e->k); return 1; }
    if (emitting >= 0 && emitting < lifted && fv_has(emitting, e->nargs, e->k)) { put(b, "l%d_%ld", e->nargs + 1, e->k); return 1; }
    DBG("declined: a parameter read where it is not in scope\n"); return 0;
  case E_BIN: {
    Buf x = nbuf(256), y = nbuf(256);
    int ok = 1;
    if (par && has_self(e->a) && has_self(e->b)) {
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
  /* DATA in C: a constructor with fields is a block {index, fields...} from the unit's arena; one with none is
     the immediate 2*index+1 (a block is word-aligned, so the low bit tells them apart).  A match reads the index
     and picks the branch; a field is a word of the block. */
  case E_CTOR:
    uses_data = 1;
    if (!e->nargs) { put(b, "(%ldL)", e->k * 2 + 1); return 1; }
    if (e->c) {                                       /* REUSE: the block the enclosing match took apart (ownership) */
      /* only what changed is written: the same constructor keeps its tag, a field that IS the old one stays */
      put(b, "({ ");
      for (int i = 0; i < e->nargs; i++) {
        const Expr *a = e->args[i];
        if (a->op == E_FIELD && a->a == e->c && a->k == i) continue;
        put(b, "long _a%d = ", i); if (!emitx(b, pre, a, par, budget - 1)) return 0; put(b, "; ");
      }
      put(b, "long *_o = (long *)("); if (!emitx(b, pre, e->c, par, budget - 1)) return 0; put(b, "); ");
      if (!e->untag && e->rtag - 1 != e->k) put(b, "_o[0] = %ldL; ", e->k);
      for (int i = 0; i < e->nargs; i++) {
        const Expr *a = e->args[i];
        if (a->op == E_FIELD && a->a == e->c && a->k == i) continue;
        put(b, "_o[%d] = _a%d; ", i + !e->untag, i);
      }
      put(b, "(long)_o; })"); return 1;
    }
    if (e->untag) put(b, "({ long *_o = lin_alloc(%d); ", e->nargs);
    else put(b, "({ long *_o = lin_alloc(%d); _o[0] = %ldL; ", e->nargs + 1, e->k);
    for (int i = 0; i < e->nargs; i++) { put(b, "_o[%d] = ", i + !e->untag); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; put(b, "; "); }
    put(b, "(long)_o; })"); return 1;
  case E_FIELD:
    uses_data = 1;
    put(b, "(((long *)("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "))[%ld])", e->k + !e->untag); return 1;
  case E_MATCH:
    uses_data = 1;
    put(b, "({ long _s = "); if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    if (e->untag) put(b, "; long _t = (_s & 1) ? (_s >> 1) : %dL; (", e->box);
    else put(b, "; long _t = (_s & 1) ? (_s >> 1) : ((long *)_s)[0]; (");
    for (int i = 0; i < e->nargs; i++) {
      if (i < e->nargs - 1) put(b, "_t == %d ? ", i);
      if (!emit_region(b, pre, e->args[i], par, budget - 1)) return 0;
      if (i < e->nargs - 1) put(b, " : ");
    }
    put(b, "); })"); return 1;
  case E_FOP:
    put(b, "%s(", FROW[e->k].c);
    for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; }
    put(b, ")"); return 1;
  case E_CALL:
    par = par && e->k == 0;                        /* only the entry function has a parallel version */
    { int calls = 0; for (int i = 0; i < e->nargs; i++) calls += has_self(e->args[i]);
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
    for (int i = 0; !par && e->k < lifted && i < nfv[e->k]; i++) {   /* the callee's lifted parameters: ours, or passed on */
      const FV *v = &fvs[e->k][i];
      if (v->h == emitting) put(b, ", p%ld", v->k);
      else if (emitting >= 0 && emitting < lifted && fv_has(emitting, v->h, v->k)) put(b, ", l%d_%ld", v->h + 1, v->k);
      else { DBG("declined: a lifted parameter with no source\n"); return 0; }
    }
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
typedef struct { unsigned char k; const char *dt; } Shape;     /* (see SHAPES below) */
typedef struct { unsigned long h; Entry fn; int arity, kind; unsigned strict; int *aborted;
                 Shape res; Shape **fld; long nctor; void (*release)(void); } Compiled;   /* kind 5: a data result, read by res/fld */   /* aborted: a data unit's guard fired */   /* strict: the parameters certainly evaluated */
static Compiled **done; static int ndone, donecap;   /* (pointers: a call holds one while another compiles) */
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
static Shape **sh_fld; static long sh_nctor;
static Compiled *compile_src(const char *src, int ar, int kind, Shape res) {
  unsigned long h = fnv1a(src) ^ cpu_key();
  for (int i = 0; i < ndone; i++) if (done[i]->h == h) return done[i]->fn ? done[i] : NULL;
  char dir[4096], c[4200], so[4200];
  cache_dir(dir, sizeof dir); mkdir_p(dir);
  snprintf(c, sizeof c, "%s/fn-%016lx.c", dir, h); snprintf(so, sizeof so, "%s/fn-%016lx.so", dir, h);
  void *hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
  if (!hnd) {
    char tmp[4300]; snprintf(tmp, sizeof tmp, "%s.%d.tmp", c, (int)getpid());
    FILE *f = fopen(tmp, "wb");
    if (f) { fputs(src, f); fclose(f); rename(tmp, c); if (run_cc(c, so)) hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL); }
    if (!hnd) { const char *er = dlerror(); DBG("cannot load %s: %s\n", so, er ? er : "(no object)"); }
  }
  Entry e = hnd ? (Entry)(intptr_t)dlsym(hnd, "lin_fn_entry") : NULL;   /* one per object, loaded RTLD_LOCAL */
  int *ab = hnd ? (int *)dlsym(hnd, "lin_fn_aborted") : NULL;
  if (!e) DBG("no compiler or the build failed for %s\n", c);
  if (ndone >= donecap) done = realloc(done, (size_t)(donecap = donecap ? donecap * 2 : 32) * sizeof *done);
  Compiled *cp = calloc(1, sizeof *cp);
  *cp = (Compiled){ h, e, ar, kind, 0, ab, res, NULL, 0, NULL };
  if (kind == 5 && hnd) {                            /* the field shapes the result is read by, kept with the code */
    cp->release = (void (*)(void))(intptr_t)dlsym(hnd, "lin_fn_release");
    cp->nctor = sh_nctor; cp->fld = calloc((size_t)sh_nctor + 1, sizeof *cp->fld);
    for (long k = 1; k <= sh_nctor; k++) { int nk = lin_ctor_info(k)->k + 1; cp->fld[k] = malloc(sizeof **cp->fld * (size_t)nk); memcpy(cp->fld[k], sh_fld[k], sizeof **cp->fld * (size_t)nk); }
    if (!cp->release) e = NULL;
  }
  done[ndone++] = cp;
  return e ? cp : NULL;
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
  case E_CALL: case E_FOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) if (mentions(e->args[i], k)) return 1; return 0;
  case E_FIELD: return mentions(e->a, k);
  case E_MATCH: if (mentions(e->a, k)) return 1; for (int i = 0; i < e->nargs; i++) if (mentions(e->args[i], k)) return 1; return 0;
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

/* G = \self.\p1..\pk. body: its parameters (at most `cap`) and the body's port; the count, or -1. */
static int fun_params(int G, int *params, int cap, Port *bodyp) {
  int ar = 0; Port body = W(N, (Port){G, 2});
  for (Port q = dhop(N, body); is(N, q, LAM, 0) && ar < cap; q = dhop(N, W(N, (Port){q.node, 2}))) {
    params[ar++] = q.node; body = W(N, (Port){q.node, 2});
  }
  /* A function RETURNING a constructor value has that value's dispatch binders right under its own (shrinking
     inlines the constructor): `\n \d0 \d1 ((\_c ..) ID)`.  Those are the value's, not parameters -- the
     marker says how many. */
  { Port tip = dhop(N, body), mb, mid; int ml; long cid;
    if (marker_app(tip, &mb, &ml, &mid)) {
      Env *probe = NULL;
      int sf = failed; long sfu = fuel;
      const LinCtor *ci = marker_ctor(mid, probe, &cid);
      failed = sf; fuel = sfu;
      if (ci && ci->m <= ar) { ar -= ci->m; body = W(N, (Port){ar ? params[ar - 1] : G, 2}); }
    } }
  if (bodyp) *bodyp = body;
  return ar;
}
static int fun_arity(int G) { int params[sizeof(unsigned) * 8]; return fun_params(G, params, N_OF(params), NULL); }

static int numeral_shape(const Net *n, Port p);
/* HIGHER-ORDER CALLS.  A parameter that receives a FUNCTION -- `(smap (\x (mul x x)) s)`, the `f` a fold passes
   down unchanged -- has no C value.  The callee is compiled as a copy SPECIALISED to it: that parameter is bound to
   the function itself, so applying it is beta, inlined, and the recursion that passes it on calls the same copy.
   (Defunctionalisation by specialisation: every function value the unit meets is a known lambda.)  A copy is one
   per distinct function value; a recursion that builds a new one each step runs out of copies and declines. */
static int fun_eq(V *a, V *b) {
  if (a == b) return 1;
  if (!a || !b || a->k != b->k) return 0;
  if (a->k == V_CLO) return a->lam == b->lam && a->env == b->env;
  if (a->k == V_FIX) return a->lam == b->lam && a->env == b->env && !a->nargs && !b->nargs;
  return 0;
}
/* Is v a function (and not data, a number, a boolean or an FFI call -- all of which are lambdas too)?  Asked
   speculatively: reading it as a number applies it to markers, which must leave no trace in the unit. */
static int is_fun_value(V *v) {
  if (!v) return 0;
  if (v->k == V_FIX) return v->nargs == 0;
  if (v->k != V_CLO || op_head(v->lam) || is_y(N, v->lam)) return 0;
  if (numeral_shape(N, (Port){v->lam, 0})) return 0;   /* a cell or a terminal: a list, a string, a numeral -- data */
  { int nl = 0; Port q = (Port){v->lam, 0}, mb, mid; int ml;
    for (int i = 0; i < N->nn && is(N, q, LAM, 0); i++) { nl++; q = dhop(N, W(N, (Port){q.node, 2})); }
    if (nl && marker_app(q, &mb, &ml, &mid)) return 0; }            /* a constructor value: data */
  int sf = failed, snf = nfun, seid = eid; long sfu = fuel; int ok = 0, isf = 1; fail_quiet++;
  const_int(v, &ok); if (!failed && ok) isf = 0;
  failed = 0; if (isf) { const_bool(v, &ok); if (!failed && ok) isf = 0; }
  failed = 0; if (isf && ffi_expr(v)) isf = 0;
  failed = sf; fuel = sfu; nfun = snf; (void)seid; fail_quiet--;
  return isf;
}
static int known_eq(V **a, V **b, int ar) {
  for (int i = 0; i < ar; i++) {
    V *x = a ? a[i] : NULL, *y = b ? b[i] : NULL;
    if (!x != !y || (x && !fun_eq(x, y))) return 0;
  }
  return 1;
}
/* Evaluate G = \self.\p1..\pk. body into the unit (specialised to `known`); its index, or -1. */
static int compile_body_spec(int G, Env *outer, V **known) {
  int params[sizeof(unsigned) * 8]; Port body;
  int ar = fun_params(G, params, N_OF(params), &body);
  for (int i = 0; i < nfun; i++) if (funs[i].lam == G && known_eq(funs[i].known, known, ar)) return i;
  if (nfun >= 1 + LIN_INT_BITS) { fail("too many functions in one unit"); return -1; }   /* mutual recursion re-copies: bound it */
  if (nfun >= funcap) funs = realloc(funs, (size_t)(funcap = funcap ? funcap * 2 : 8) * sizeof *funs);
  int fid = nfun++; funs[fid].lam = G; funs[fid].body = NULL; funs[fid].strict = ~0u; funs[fid].pnode = NULL;
  funs[fid].outer = outer; funs[fid].known = NULL;
  if (known) { funs[fid].known = A(sizeof(V *) * (size_t)(ar ? ar : 1)); memcpy(funs[fid].known, known, sizeof(V *) * (size_t)ar); }
  funs[fid].arity = ar;
  if (ar == 0) { fail("a function with no parameters"); return -1; }
  Env *env = A(sizeof *env); env->lam = G; V *self = mkv(V_SELF); self->lam = fid; env->t = ready(self); env->next = outer;
  funs[fid].pnode = A(sizeof(Expr *) * (size_t)ar);
  for (int i = 0; i < ar; i++) {
    Env *e = A(sizeof *e); e->lam = params[i]; V *s = mkv(V_SYM); s->e = mke(E_PARAM, 1); s->e->k = i; s->e->nargs = fid;
    funs[fid].pnode[i] = s->e;
    e->t = ready(known && known[i] ? known[i] : s); e->next = env; env = e;   /* a known function: itself */
  }
  int save_fid = cur_fid; cur_fid = fid;
  Expr *top = to_expr(eval(body, env));
  cur_fid = save_fid;
  if (failed || !top) return -1;
  funs[fid].body = top;
  return fid;
}
static int compile_body(int G, Env *outer) { return compile_body_spec(G, outer, NULL); }
/* A full call of the recursive function G (closure genv): the copy its function arguments select (`target`, the
   copy making a self call, when they are its own), and the call over the rest. */
static V *fix_call(int G, Env *genv, int target, Lz **args, int ar) {
  V **known = NULL;
  for (int i = 0; i < ar; i++) {
    V *av = force(args[i]); if (!av) return NULL;
    if (is_fun_value(av)) { if (!known) known = A(sizeof(V *) * (size_t)ar); known[i] = av; }
  }
  int fid = target >= 0 && known_eq(funs[target].known, known, ar) ? target : compile_body_spec(G, genv, known);
  if (fid < 0) return NULL;
  V *s = mkv(V_SYM); s->e = mke(E_CALL, 1); s->e->k = fid; s->e->nargs = ar; s->e->args = A(sizeof(Expr *) * (size_t)ar);
  for (int i = 0; i < ar; i++) {
    if (known && known[i]) { Expr *z = mke(E_CONST, 1); z->k = 0; s->e->args[i] = hc(z); continue; }   /* (unused: bound in the copy) */
    s->e->args[i] = to_expr(force(args[i])); if (!s->e->args[i]) return NULL;
  }
  s->e = hc(s->e); return s;
}

/* WHAT KIND A VALUE IS, so a folded result is never a pointer.  Numbers and data are both words in the C, and the
   net's result has to be built as the right one; for now a unit is folded only when its result is PROVABLY a
   number or a boolean.  A parameter is numeric unless something takes it apart (a match, a field) or a call
   passes it something that is not provably numeric -- a fixpoint from "all numeric" down. */
static unsigned char **pnum, *fnum; static int num_changed;
static int is_num_r(const Expr *e);
static int is_num(const Expr *e) { return is_num_r(e); }
static int is_num_r(const Expr *e) {
  switch (e->op) {
  case E_CONST: case E_BIN: case E_FOP: return 1;
  case E_PARAM: return e->nargs >= 0 && e->nargs < nfun ? pnum[e->nargs][e->k] : 1;   /* (the entry's: numbers) */
  case E_IF: return is_num_r(e->b) && is_num_r(e->c);
  case E_MATCH: for (int i = 0; i < e->nargs; i++) if (!is_num_r(e->args[i])) return 0; return 1;
  case E_CALL: return fnum[e->k];
  default: return 0;                                 /* E_CTOR, E_FIELD */
  }
}
static void num_walk(const Expr *e) {                 /* demote what this expression shows is not a number */
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if ((e->op == E_MATCH || e->op == E_FIELD) && e->a->op == E_PARAM && e->a->nargs >= 0 && e->a->nargs < nfun &&
      pnum[e->a->nargs][e->a->k]) { pnum[e->a->nargs][e->a->k] = 0; num_changed = 1; }
  if (e->op == E_CALL)
    for (int i = 0; i < e->nargs; i++) if (pnum[e->k][i] && !is_num_r(e->args[i])) { pnum[e->k][i] = 0; num_changed = 1; }
  if (e->a) num_walk(e->a);
  if (e->b) num_walk(e->b);
  if (e->c) num_walk(e->c);
  for (int i = 0; i < e->nargs && e->args; i++) num_walk(e->args[i]);
}
/* OWNERSHIP, AND REUSE IN PLACE.  The unit's DAG shows sharing exactly (hash-consing: one value, one node -- the
   C image of the net's fans), so whether a block has ONE owner is a static question.  A value is FRESH if it
   was just built (a constructor, or a call returning fresh data); a data parameter is UNIQUE if every call
   passes it something fresh that nothing else on that path uses, and the function itself uses it at most once
   on any path (reading its fields does not count).  Then a match on a unique parameter can build the branch's
   constructor of the same size IN THE BLOCK IT JUST TOOK APART -- its fields are all computed before anything
   is written -- which is what a functional insert into a tree costs in C: the path is updated, not copied. */
static const Expr *occ_x;
static unsigned occ_r(const Expr *e) {               /* how often occ_x is MOVED on the worst path through e */
  if (e == occ_x) return 1;
  if (mm_has(MM_OCC, e)) return mm_val[MM_OCC][e->id];
  unsigned r = 0;
  switch (e->op) {
  case E_FIELD: r = e->a == occ_x ? 0 : occ_r(e->a); break;      /* reading a field consumes nothing */
  case E_IF: { unsigned b = occ_r(e->b), c = occ_r(e->c); r = occ_r(e->a) + (b > c ? b : c); break; }
  case E_MATCH: { unsigned m = 0; for (int i = 0; i < e->nargs; i++) { unsigned x = occ_r(e->args[i]); if (x > m) m = x; } r = occ_r(e->a) + m; break; }
  case E_BIN: r = occ_r(e->a) + occ_r(e->b); break;
  case E_CALL: case E_CTOR: case E_FOP: for (int i = 0; i < e->nargs; i++) r += occ_r(e->args[i]); break;
  default: break;
  }
  if (r > 2) r = 2;
  return mm_put(MM_OCC, e, r);
}
static unsigned occ(const Expr *in, const Expr *x) { occ_x = x; mm_new(MM_OCC); return occ_r(in); }
static unsigned char **uparam, *ufresh;
static int uniq_r(const Expr *e) {
  if (mm_has(MM_UNIQ, e)) return (int)mm_val[MM_UNIQ][e->id];
  int r = 0;
  switch (e->op) {
  case E_CTOR: case E_CONST: r = 1; break;
  case E_CALL: r = ufresh[e->k]; break;
  case E_PARAM: r = e->nargs >= 0 && e->nargs < nfun && uparam[e->nargs][e->k]; break;
  case E_IF: r = uniq_r(e->b) && uniq_r(e->c); break;
  case E_MATCH: r = 1; for (int i = 0; i < e->nargs; i++) r = r && uniq_r(e->args[i]); break;
  case E_FIELD: r = uniq_r(e->a); break;
  default: break;
  }
  return (int)mm_put(MM_UNIQ, e, (unsigned)r);
}
static int uniq(const Expr *e) { return uniq_r(e); }
static int uq_changed;
static void uniq_calls(const Expr *e, const Expr *body) {   /* demote a callee's parameter given something shared */
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_CALL)
    for (int i = 0; i < e->nargs; i++) {
      const Expr *a = e->args[i];
      int ok = uniq(a) && (a->op != E_FIELD || occ(body, a) <= 1) && (a->op != E_PARAM || occ(body, a) <= 1);
      if (!ok && uparam[e->k][i]) { uparam[e->k][i] = 0; uq_changed = 1; }
    }
  if (e->a) uniq_calls(e->a, body);
  if (e->b) uniq_calls(e->b, body);
  if (e->c) uniq_calls(e->c, body);
  for (int i = 0; i < e->nargs && e->args; i++) uniq_calls(e->args[i], body);
}
static int only_reads(const Expr *e, const Expr *x) { /* x appears in e only as the base of field reads */
  if (e == x) return 0;
  if (e->op == E_FIELD && e->a == x) return 1;
  if (e->a && !only_reads(e->a, x)) return 0;
  if (e->b && !only_reads(e->b, x)) return 0;
  if (e->c && !only_reads(e->c, x)) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!only_reads(e->args[i], x)) return 0;
  return 1;
}
static Expr **ctor_slot_tail(Expr **slot, Expr *s, int nf, int branch) {   /* mark the tail constructors of a branch */
  Expr *e = *slot;
  if (e->op == E_CTOR && e->nargs == nf && nf > 0 && !e->c) {
    Expr *c2 = A(sizeof *c2); *c2 = *e; c2->c = s; c2->rtag = branch + 1; c2->id = eid++; c2->var = -1; *slot = c2;   /* (a private copy: the mark is this place's) */
    return slot;
  }
  if (e->op == E_IF) {
    Expr *c2 = A(sizeof *c2); *c2 = *e; c2->id = eid++; c2->var = -1; *slot = c2;
    ctor_slot_tail(&c2->b, s, nf, branch); ctor_slot_tail(&c2->c, s, nf, branch);
  }
  return NULL;
}
static void mark_reuse(Expr *e, int f) {
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_MATCH && e->a->op == E_PARAM && e->a->nargs == f && uparam[f][e->a->k]) {
    for (int i = 0; i < e->nargs; i++) {
      const LinCtor *c2 = NULL; int nf = -1;
      for (long k = 1; (c2 = lin_ctor_info(k)); k++) if (c2->i == i && c2->m == e->nargs) { nf = c2->k; break; }
      if (nf > 0 && only_reads(e->args[i], e->a)) ctor_slot_tail(&e->args[i], e->a, nf, i);
    }
  }
  if (e->a) mark_reuse(e->a, f);
  if (e->b) mark_reuse(e->b, f);
  if (e->c && e->op != E_CTOR) mark_reuse(e->c, f);
  for (int i = 0; i < e->nargs && e->args; i++) mark_reuse(e->args[i], f);
}
static void ownership(Expr *entry) {
  uparam = A(sizeof *uparam * (size_t)nfun); ufresh = A((size_t)nfun);
  for (int i = 0; i < nfun; i++) { int a = funs[i].arity ? funs[i].arity : 1; uparam[i] = A((size_t)a); memset(uparam[i], 1, (size_t)a); ufresh[i] = 1; }
  for (int round = 0; round <= nfun * 64 + 64; round++) {
    uq_changed = 0;
    mm_new(MM_UNIQ);
    for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); uniq_calls(funs[i].body, funs[i].body); }
    mm_new(MM_NUM); uniq_calls(entry, entry);
    for (int i = 0; i < nfun; i++) for (int k = 0; k < funs[i].arity; k++)
      if (uparam[i][k] && funs[i].pnode && funs[i].pnode[k] && occ(funs[i].body, funs[i].pnode[k]) > 1) { uparam[i][k] = 0; uq_changed = 1; }
    mm_new(MM_UNIQ);
    for (int i = 0; i < nfun; i++) { int f = uniq(funs[i].body); if (ufresh[i] && !f) { ufresh[i] = 0; uq_changed = 1; } }
    if (!uq_changed) break;
  }
  for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); mark_reuse(funs[i].body, i); }
}

static int has_data(const Expr *e) {               /* (memoised in MM_NUM: call after mm_new(MM_NUM)) */
  if (!e || mm_has(MM_NUM, e)) return 0;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_CTOR || e->op == E_MATCH || e->op == E_FIELD) return 1;
  if ((e->a && has_data(e->a)) || (e->b && has_data(e->b)) || (e->c && has_data(e->c))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (has_data(e->args[i])) return 1;
  return 0;
}
static int result_numeric(const Expr *entry) {
  pnum = A(sizeof *pnum * (size_t)nfun); fnum = A((size_t)nfun);
  for (int i = 0; i < nfun; i++) { pnum[i] = A((size_t)(funs[i].arity ? funs[i].arity : 1)); memset(pnum[i], 1, (size_t)(funs[i].arity ? funs[i].arity : 1)); fnum[i] = 1; }
  for (int round = 0; round <= nfun * 64 + 64; round++) {
    num_changed = 0;
    mm_new(MM_NUM);
    for (int i = 0; i < nfun; i++) num_walk(funs[i].body);
    num_walk(entry);
    for (int i = 0; i < nfun; i++) { int f = is_num(funs[i].body); if (fnum[i] && !f) { fnum[i] = 0; num_changed = 1; } }
    if (!num_changed) break;
  }
  return is_num(entry);
}

/* SHAPES: what every value of the unit IS, data included, so a result that is a structure can be built back into
   the net.  A C word is a number, a boolean or a datatype's value (an immediate or a block); which, is a fixpoint
   over the unit: a constructor's field has the shape of what is put there, a parameter of what is passed, a call
   of what its body returns, a field read of what was stored in that field.  Floats are numerals of their bits,
   so they are numbers here.  Any disagreement (a field holding a number in one place and a tree in another) is
   TOP, and a unit whose result reaches a TOP is not folded -- the net computes it. */
/* Shape.k: 0 nothing yet, 1 number, 3 boolean, 5 data(dt), 9 top */
static Shape sh_join(Shape a, Shape b) {
  if (!a.k) return b;
  if (!b.k) return a;
  if (a.k == b.k && (a.k != 5 || a.dt == b.dt)) return a;
  return (Shape){ 9, NULL };
}
static int sh_eq(Shape a, Shape b) { return a.k == b.k && a.dt == b.dt; }
static Shape **sh_par, *sh_fun; static unsigned char *sh_built; static int sh_changed;
static Shape *sh_memo; static unsigned *sh_gen, sh_g; static int sh_cap;
static long ctor_id(const LinCtor *ci) { for (long k = 1; lin_ctor_info(k); k++) if (lin_ctor_info(k) == ci) return k; return 0; }
static void sh_upd(Shape *slot, Shape v) { Shape j = sh_join(*slot, v); if (!sh_eq(j, *slot)) { *slot = j; sh_changed = 1; } }
static Shape shape_of(const Expr *e) {
  if (e->id < sh_cap && sh_gen[e->id] == sh_g) return sh_memo[e->id];
  Shape r = { 0, NULL };
  switch (e->op) {
  case E_CONST: case E_BIN: case E_FOP: r.k = e->kind == 3 ? 3 : 1; break;
  case E_PARAM: r = e->nargs >= 0 && e->nargs < nfun ? sh_par[e->nargs][e->k] : (Shape){ 1, NULL }; break;
  case E_IF: shape_of(e->a); r = sh_join(shape_of(e->b), shape_of(e->c)); break;
  case E_MATCH: shape_of(e->a); for (int i = 0; i < e->nargs; i++) r = sh_join(r, shape_of(e->args[i])); break;
  case E_CALL:
    for (int i = 0; i < e->nargs; i++) { Shape a = shape_of(e->args[i]); if (!(funs[e->k].known && funs[e->k].known[i])) sh_upd(&sh_par[e->k][i], a); }
    r = sh_fun[e->k]; break;
  case E_CTOR: {
    long id = ctor_id(e->ci);
    if (id <= 0 || id > sh_nctor) { r.k = 9; break; }
    sh_built[id] = 1;
    for (int j = 0; j < e->nargs; j++) sh_upd(&sh_fld[id][j], shape_of(e->args[j]));
    r.k = 5; r.dt = e->ci->dt; break;
  }
  case E_FIELD: {
    shape_of(e->a);
    long id = ctor_id(e->ci);
    r = id > 0 && id <= sh_nctor && e->k < e->ci->k ? sh_fld[id][e->k] : (Shape){ 9, NULL }; break;
  }
  default: r.k = 9; break;
  }
  if (e->id < sh_cap) { sh_gen[e->id] = sh_g; sh_memo[e->id] = r; }
  return r;
}
/* The shapes of the unit, to a fixpoint; the entry's.  Tables stay for the result's reading (data_shapes). */
static Shape unit_shapes(const Expr *entry) {
  sh_nctor = 0; while (lin_ctor_info(sh_nctor + 1)) sh_nctor++;
  sh_par = A(sizeof *sh_par * (size_t)nfun); sh_fun = A(sizeof *sh_fun * (size_t)(nfun ? nfun : 1));
  for (int i = 0; i < nfun; i++) sh_par[i] = A(sizeof **sh_par * (size_t)(funs[i].arity ? funs[i].arity : 1));
  sh_fld = A(sizeof *sh_fld * (size_t)(sh_nctor + 1)); sh_built = A((size_t)(sh_nctor + 1));
  for (long k = 1; k <= sh_nctor; k++) sh_fld[k] = A(sizeof **sh_fld * (size_t)(lin_ctor_info(k)->k + 1));
  if (sh_cap < eid) { sh_cap = eid * 2 + 64; sh_memo = realloc(sh_memo, sizeof *sh_memo * (size_t)sh_cap); sh_gen = realloc(sh_gen, sizeof *sh_gen * (size_t)sh_cap); memset(sh_gen, 0, sizeof *sh_gen * (size_t)sh_cap); }
  Shape res = { 0, NULL };
  for (int round = 0; round < 1000; round++) {
    sh_changed = 0;
    sh_g++;
    for (int i = 0; i < nfun; i++) sh_upd(&sh_fun[i], shape_of(funs[i].body));
    res = shape_of(entry);
    if (!sh_changed) break;
  }
  return res;
}
/* Can a value of this shape be read back?  Every constructor of every datatype it reaches that the unit builds
   must have fields of a known shape. */
static int shape_closed(Shape s, int depth) {   /* depth: datatypes on the walk (each one checked once) */
  if (s.k == 1 || s.k == 3) return 1;
  if (s.k != 5 || depth > sh_nctor) return 0;
  for (long k = 1; k <= sh_nctor; k++) {
    const LinCtor *c = lin_ctor_info(k);
    if (c->dt != s.dt || !sh_built[k]) continue;
    for (int j = 0; j < c->k; j++) {
      Shape f = sh_fld[k][j];
      if (f.k == 5 ? (f.dt != s.dt && !shape_closed(f, depth + 1)) : !(f.k == 1 || f.k == 3)) return 0;
    }
  }
  return 1;
}

/* The data runtime a unit that builds or reads data gets: an arena (freed when the call returns -- nothing it
   built outlives a numeric result) and a GUARD.  Lin is lazy and the C is strict: a constructor's fields are
   computed when it is built, which a lazy program might never ask for -- an infinite structure, say.  So the
   unit runs on its own large stack with a memory and a stack bound, checked as it allocates, and a call that
   crosses either is ABANDONED (lin_fn_aborted) and handed back to the net, which computes it lazily.  Never a
   wrong answer: at worst the oracle's speed. */
static const char *DATA_RT =
  "#include <setjmp.h>\n#include <stdlib.h>\n"
  "#define LIN_TLS __thread __attribute__((tls_model(\"initial-exec\")))\n"
  "extern LIN_TLS jmp_buf lin_jb; extern LIN_TLS char *lin_stack_lo; int lin_fn_aborted;\n"
  "extern LIN_TLS long *lin_hp, *lin_he; static long lin_used; static void **lin_ch; static int lin_nch, lin_cch;\n"
  "static pthread_mutex_t lin_chm = PTHREAD_MUTEX_INITIALIZER;\n"
  "static __attribute__((noinline, cold)) void lin_refill(long n) {\n"
  "  long sz = n > 65536 ? n : 65536; long *c = malloc((size_t)sz * 8);\n"
  "  if (!c || lin_fn_aborted || lin_used > (1L << 28) || (char *)__builtin_frame_address(0) < lin_stack_lo) { free(c); lin_fn_aborted = 1; longjmp(lin_jb, 1); }\n"
  "  pthread_mutex_lock(&lin_chm);\n"
  "  if (lin_nch >= lin_cch) { lin_cch = lin_cch ? lin_cch * 2 : 64; lin_ch = realloc(lin_ch, (size_t)lin_cch * sizeof *lin_ch); }\n"
  "  lin_ch[lin_nch++] = c; lin_used += sz; pthread_mutex_unlock(&lin_chm); lin_hp = c; lin_he = c + sz; }\n"
  "static inline long *lin_alloc(long n) { if (__builtin_expect(lin_hp + n > lin_he, 0)) lin_refill(n); long *r = lin_hp; lin_hp += n; return r; }\n"
  "static void lin_free_all(void) { for (int i = 0; i < lin_nch; i++) free(lin_ch[i]); lin_nch = 0; lin_hp = lin_he = 0; lin_used = 0; }\n"
  /* The guard lives where an infinite STRUCTURE must go -- the arena's refill, once per chunk -- and checks memory and
     the stack there; a compiled function carries nothing (measured: a per-call check doubled a tree insert).  A call
     whose runaway recursion builds nothing is not caught -- the exposure numeric units have always had.  A task on
     another thread has its own buffer and bound; abandoning anywhere marks the call, and a join that finds it marked
     abandons the joiner too, so a half-computed value is never used. */
  "#define LIN_ENTER\n#define LIN_LEAVE\n"
  "#define LIN_TASK_START(ss) if (setjmp(lin_jb)) { lin_fn_aborted = 1; return 0; } lin_stack_lo = (char *)__builtin_frame_address(0) - (ss) + ((size_t)1 << 24)\n"
  "#define LIN_JOINED (lin_fn_aborted ? (longjmp(lin_jb, 1), 0) : 0)\n";

/* Compile F and everything it calls, or return NULL.  `aports`, when given, are the call's arguments: a NUMBER
   one (anum[k]) is passed to the entry, any other is compiled into it as an expression -- `(check (make 7))`
   compiles `make` too, instead of asking the net to build the tree first. */
static Compiled *compile_fn_ex(Net *n, int F, const Port *aports, const int *anum);
static Compiled *compile_fn(Net *n, int F) { return compile_fn_ex(n, F, NULL, NULL); }
static Compiled *compile_fn_ex(Net *n, int F, const Port *aports, const int *anum) {
  N = n; failed = 0; fuel = 20000000; nfun = 0; eid = 0; nvar = 0; hc_reset(); uses_data = 0;   /* a one-time compile: the budget only stops an evaluation that does not end */
  DBG("compile F=%d (net %d nodes)%s\n", F, n->nn, aports ? " with its arguments" : "");
  Compiled *r = NULL;
  V **known = NULL;                                  /* an argument that is a FUNCTION: the entry's copy is specialised to it */
  if (aports) {
    int ar = fun_arity(F);
    for (int k = 0; k < ar && !failed; k++)
      if (!anum[k] && is(n, dhop(n, aports[k]), LAM, 0)) {
        V *av = eval(aports[k], NULL);
        if (av && is_fun_value(av)) { if (!known) known = A(sizeof(V *) * (size_t)ar); known[k] = av; DBG("argument %d is a function: the callee is specialised to it\n", k); }
      }
    failed = 0; nfun = 0;
  }
  if (compile_body_spec(F, NULL, known) == 0 && !failed) {
    arity = funs[0].arity;
    /* THE ENTRY: f0 applied to the call's arguments -- the entry's own parameters, or expressions */
    int nnum = 0;
    Expr *entry = mke(E_CALL, funs[0].body->kind); entry->k = 0; entry->nargs = arity; entry->args = A(sizeof(Expr *) * (size_t)(arity ? arity : 1));
    for (int k = 0; k < arity && !failed; k++) {
      if (known && known[k]) { Expr *z = mke(E_CONST, 1); z->k = 0; entry->args[k] = hc(z); }   /* (bound in the copy) */
      else if (!aports || anum[k]) { Expr *pe = mke(E_PARAM, 1); pe->k = nnum++; pe->nargs = -1; entry->args[k] = hc(pe); }
      else { cur_fid = -1; entry->args[k] = to_expr(eval(aports[k], NULL)); if (!entry->args[k]) failed = 1; }
    }
    if (failed) { arena_free(); return NULL; }        /* (a function the entry reached may be half-built) */
    entry = hc(entry);
    mm_new(MM_CALL); mm_new(MM_SELF);              /* the DAG is complete: its structure answers stay valid */
    for (int it = 0, changed = 1; changed && it <= LIN_INT_BITS; it++) {   /* strictness: down to the fixpoint */
      changed = 0;
      for (int i = 0; i < nfun; i++) { strict_fid = i; unsigned st = strict(funs[i].body) & funs[i].strict; if (st != funs[i].strict) { funs[i].strict = st; changed = 1; } }
      strict_fid = -2;
    }
    int safe = !failed;
    for (int i = 0; safe && i < nfun; i++) safe = args_safe(funs[i].body);
    if (safe && aports) safe = args_safe(entry);
    /* A DATA unit runs under its guard (DATA_RT): a structure the lazy program would only have used a part of --
       an infinite one -- is abandoned when it outgrows memory or the stack, and the net computes the call.  So for
       data the rule above is relaxed: work may be wasted on a value nobody reads, but the answer is the net's. */
    if (!safe) { mm_new(MM_NUM); int d = has_data(entry); for (int i = 0; !d && i < nfun; i++) d = has_data(funs[i].body); if (d) safe = 1; }
    if (!safe) DBG("declined: a call passes a computation where its callee may not evaluate it\n");
    int numeric = safe && result_numeric(entry);
    Shape rshape = { 1, NULL };
    if (safe && !numeric) {                            /* a STRUCTURE: folded if its shape is known to the leaves */
      rshape = unit_shapes(entry);
      if (!shape_closed(rshape, 0) || rshape.k != 5) { safe = 0; DBG("declined: the result's shape is not known (a field holding different kinds of value)\n"); }
    }
    if (!safe) {}
    else {
      { mm_new(MM_NUM); int d = has_data(entry); for (int i = 0; !d && i < nfun; i++) d = has_data(funs[i].body); if (d) ownership(entry); }
      Buf b = nbuf(4096), fb = nbuf(4096), pre = nbuf(1024), pb = nbuf(1024);
      lift();
      for (int i = 0; i < nfun; i++) { put(&fb, "static long f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0); put(&fb, ");\n"); }
      int ok = 1;
      for (int i = 0; ok && i < nfun; i++) {
        put(&fb, "static long f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0); put(&fb, ") { LIN_ENTER; return ");
        emitting = i; fscope++; ok = emit_region(&fb, &pre, funs[i].body, 0, 4096); put(&fb, "; }\n");
      }
      Buf eb = nbuf(1024);                             /* the entry's call, as an expression of its parameters */
      emitting = -1; fscope++; ok = ok && emit_region(&eb, &pre, entry, 0, 4096);
      int data = uses_data;
      put(&b, "%s%s\n#include <pthread.h>\n", LIN_I64_SRC, LIN_F64_SRC);
      if (data) put(&b, "%s", DATA_RT); else put(&b, "#define LIN_ENTER\n#define LIN_LEAVE\n#define LIN_TASK_START(ss)\n#define LIN_JOINED 0\nint lin_fn_aborted;\n");
      put(&b, "%s", fb.s);
      if (ok && data) {                                /* data: on its own large stack, the tree recursions forked */
        Buf ebp = nbuf(1024);
        nsite = 0; emitting = 0; fscope++;
        int pok = !nfv[0] && emit_region(&pb, &pre, funs[0].body, 1, 4096);   /* (the parallel copy is of f0's own parameters) */
        emitting = -1; fscope++;
        pok = pok && emit_region(&ebp, &pre, entry, 1, 4096);
        put(&b, "static int dmax; static pthread_attr_t attr;\nstatic long fp("); plist(&b, 1);
        put(&b, "%sint d);\n%s", arity ? ", " : "", pre.s);
        if (pok) { put(&b, "static long fp("); plist(&b, 1); put(&b, "%sint d) { if (d >= dmax) return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); return %s; }\n", pb.s); }
        else { put(&b, "static long fp("); plist(&b, 1); put(&b, "%sint d) { (void)d; return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); }\n"); }
        put(&b, "static const long *lin_args; static long lin_res; static int lin_threads_;\n");
        put(&b, "static void *lin_run(void *u) { (void)u; const long *a = lin_args; LIN_TASK_START((size_t)1 << 30);\n");
        for (int i = 0; i < nnum; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        if (pok && nsite) {
          put(&b, "  if (lin_threads_ > 1) { int lg = 0; while ((1 << lg) < lin_threads_) lg++; dmax = lg + 2;\n");
          put(&b, "    pthread_attr_init(&attr); pthread_attr_setstacksize(&attr, (size_t)256 << 20); int d = -1; lin_res = %s; return 0; }\n", ebp.s);
        }
        put(&b, "  lin_res = %s; return 0; }\n", eb.s);
        free(ebp.s);
        put(&b, "long lin_fn_entry(const long *a, int threads) { lin_threads_ = threads; lin_args = a; lin_fn_aborted = 0;\n");
        put(&b, "  pthread_t t; pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);\n");
        /* a structure result stays in the arena until the driver has built it into the net (lin_fn_release) */
        put(&b, "  if (pthread_create(&t, &at, lin_run, 0)) { lin_fn_aborted = 1; return 0; } pthread_join(t, 0);%s return lin_res; }\n",
            numeric ? " lin_free_all();" : "");
        put(&b, "void lin_fn_release(void) { lin_free_all(); }\n");
        DBG("compiling a data unit (%d function%s, %d numeric argument%s, %d parallel site%s%s):\n%s\n", nfun, nfun == 1 ? "" : "s", nnum, nnum == 1 ? "" : "s", nsite, nsite == 1 ? "" : "s", numeric ? "" : ", a structure result", b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, nnum, numeric ? (entry->kind == 3 ? 3 : 1) : 5, rshape);
        if (r) r->strict = funs[0].strict;
      } else if (ok && aports) {                       /* numbers only, with expression arguments: the plain entry */
        put(&b, "%slong lin_fn_entry(const long *a, int threads) { (void)threads;\n", pre.s);
        for (int i = 0; i < nnum; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        put(&b, "  return %s; }\n", eb.s);
        DBG("compiling (%d functions, entry with expression arguments):\n%s\n", nfun, b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, nnum, entry->kind == 3 ? 3 : 1, (Shape){ 1, NULL });
        if (r) r->strict = funs[0].strict;
      }
      nsite = 0; emitting = 0; fscope++;
      if (!ok || data || aports || nfv[0]) goto done;
      ok = emit_region(&pb, &pre, funs[0].body, 1, 4096);
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
        r = compile_src(b.s, arity, funs[0].body->kind, (Shape){ 1, NULL });
        if (r) r->strict = funs[0].strict;
      } else DBG("declined: expression too large\n");
    done:
      free(b.s); free(fb.s); free(pre.s); free(pb.s); free(eb.s);
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

/* A STRUCTURE RESULT, BUILT INTO THE NET.  The unit's answer is a word: a number, a boolean, or a datatype's value
   in its arena -- an immediate for a constructor with no fields, else a block (the layout the unit's own matches
   read).  The shapes the compiler proved say which, field by field, so the value is rebuilt as the constructors
   the source would have built -- each `\d0..\d(m-1). ((\_c (d_i f1..fk)) ID)`, marker and all, so everything that
   reads a constructor reads these -- and a block the result reaches more than once is built ONCE and shared by a
   fan with a label of its own, as the program's own sharing would be: the net gets the DAG, not a tree. */
typedef struct { long ptr; int refs; int used; Port *outs; } RBlk;
typedef struct { Net *n; const Compiled *c; RBlk *tab; long cap, cnt; long budget; int bad; unsigned long lbl; } Reif;
static RBlk *rb_get(Reif *R, long ptr, int make) {
  if (make && (R->cnt + 1) * 2 > R->cap) {
    RBlk *o = R->tab; long oc = R->cap; R->cap = R->cap ? R->cap * 2 : 1024; R->tab = calloc((size_t)R->cap, sizeof *R->tab); R->cnt = 0;
    for (long i = 0; i < oc; i++) if (o[i].ptr) { RBlk *b = rb_get(R, o[i].ptr, 1); *b = o[i]; }
    free(o);
  }
  if (!R->cap) return NULL;
  for (unsigned long h = ((unsigned long)ptr * 0x9E3779B97F4A7C15UL >> 7) & (unsigned long)(R->cap - 1);; h = (h + 1) & (unsigned long)(R->cap - 1)) {
    if (R->tab[h].ptr == ptr) return &R->tab[h];
    if (!R->tab[h].ptr) { if (!make) return NULL; R->tab[h].ptr = ptr; R->cnt++; return &R->tab[h]; }
  }
}
static const LinCtor *dt_ctor(const char *dt, int i) {
  const LinCtor *c; for (long k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->i == i) return c; return NULL;
}
/* the constructor of a word of datatype dt, and its fields' words */
static const LinCtor *rd_word(const char *dt, long w, const long **fields) {
  int box = 0, untag = dt_boxed(dt, &box) == 1;
  if (w & 1) { *fields = NULL; return dt_ctor(dt, (int)(w >> 1)); }
  const long *blk = (const long *)w;
  if (!blk) return NULL;
  if (untag) { *fields = blk; return dt_ctor(dt, box); }
  *fields = blk + 1; return dt_ctor(dt, (int)blk[0]);
}
static long cid_of(const LinCtor *ci) { return ctor_id(ci); }
/* pass 1: how often each block is reached (a block's fields are walked once) -- iteratively: results are deep */
typedef struct { long w; const char *dt; } RTodo;
static void rf_count(Reif *R, long w0, const char *dt0) {
  RTodo *st = malloc(sizeof *st * 64); long sp = 0, sc = 64;
  st[sp++] = (RTodo){ w0, dt0 };
  while (sp && !R->bad) {
    RTodo t = st[--sp];
    const long *f; const LinCtor *ci = rd_word(t.dt, t.w, &f);
    if (!ci) { R->bad = 1; break; }
    if (!(t.w & 1)) { RBlk *b = rb_get(R, t.w, 1); if (b->refs++) continue; }
    long id = cid_of(ci);
    for (int j = 0; j < ci->k; j++) {
      Shape fs = R->c->fld[id][j];
      if (fs.k != 5) continue;
      if (sp >= sc) st = realloc(st, sizeof *st * (size_t)(sc *= 2));
      st[sp++] = (RTodo){ f[j], fs.dt };
    }
  }
  free(st);
}
static Scope fresh_label(Reif *R) {                   /* a sharing point no other fan in the net has */
  Scope s = scope_nil();
  unsigned long v = 0x5Au << 24 | (R->lbl++ & 0xFFFFFFu);
  for (int b = 31; b >= 0; b--) s = scope_app(R->n, s, (int)((v >> b) & 1));
  return s;
}
static Port rf_ctor(Reif *R, const LinCtor *ci, const Port *fields) {
  Net *n = R->n; Scope sc = scope_nil();
  Port *lam = malloc(sizeof *lam * (size_t)ci->m);
  for (int j = 0; j < ci->m; j++) lam[j] = net_alloc(n, LAM, sc);
  for (int j = 0; j + 1 < ci->m; j++) net_link(n, (Port){lam[j].node, 2}, (Port){lam[j + 1].node, 0}, 1);
  Port ma = net_alloc(n, APP, sc), lc = net_alloc(n, LAM, sc);
  net_link(n, (Port){lam[ci->m - 1].node, 2}, (Port){ma.node, 1}, 1);
  net_link(n, (Port){ma.node, 0}, (Port){lc.node, 0}, 1);              /* the marker: a redex, as the source's is */
  net_link(n, (Port){lc.node, 1}, net_alloc(n, ERA, sc), 1);
  net_link(n, (Port){ma.node, 2}, net_alloc_scott(n, cid_of(ci)), 1);
  Port f = (Port){lam[ci->i].node, 1};
  for (int j = 0; j < ci->k; j++) {
    Port ap = net_alloc(n, APP, sc);
    net_link(n, (Port){ap.node, 0}, f, 1);
    net_link(n, (Port){ap.node, 2}, fields[j], 1);
    f = (Port){ap.node, 1};
  }
  net_link(n, (Port){lc.node, 2}, f, 1);
  for (int j = 0; j < ci->m; j++) if (j != ci->i) net_link(n, (Port){lam[j].node, 1}, net_alloc(n, ERA, sc), 1);
  Port v = (Port){lam[0].node, 0};
  free(lam);
  return v;
}
/* pass 2: build (recursively, on the large stack rf_thread gives it) */
static Port rf_build(Reif *R, long w, Shape s) {
  if (R->bad) return NONE;
  if (s.k == 1) return net_alloc_scott(R->n, w);
  if (s.k == 3) return net_alloc_bool(R->n, w != 0);
  const long *f; const LinCtor *ci = rd_word(s.dt, w, &f);
  if (!ci) { R->bad = 1; return NONE; }
  RBlk *b = (w & 1) ? NULL : rb_get(R, w, 0);
  if (b && b->outs) return b->outs[b->used++];
  long id = cid_of(ci);
  Port *fp = malloc(sizeof *fp * (size_t)(ci->k + 1));
  for (int j = 0; j < ci->k && !R->bad; j++) fp[j] = rf_build(R, f[j], R->c->fld[id][j]);
  Port v = R->bad ? NONE : rf_ctor(R, ci, fp);
  free(fp);
  if (R->bad || !b || b->refs < 2) return v;
  b->outs = malloc(sizeof *b->outs * (size_t)b->refs); b->used = 0;
  Scope lb = fresh_label(R); Port cur = v;
  for (int r = 0; r < b->refs - 1; r++) {
    Port d = net_alloc(R->n, DUP, lb);
    net_link(R->n, (Port){d.node, 0}, cur, 1);
    b->outs[r] = (Port){d.node, 1}; cur = (Port){d.node, 2};
  }
  b->outs[b->refs - 1] = cur;
  return b->outs[b->used++];
}
typedef struct { Reif *R; long w; Port out; } RfArg;
static void *rf_thread(void *u) { RfArg *a = u; a->out = rf_build(a->R, a->w, a->R->c->res); return NULL; }
/* The value of a compiled call's result word, as net structure; NONE if it cannot be read back. */
static Port result_port(Net *n, const Compiled *c, long r) {
  if (c->kind == 3) return net_alloc_bool(n, r != 0);
  if (c->kind != 5) return net_alloc_scott(n, r);   /* (a float is the numeral of its bits) */
  static unsigned long lbl;
  Reif R = { n, c, NULL, 0, 0, 0, 0, lbl };   /* (each block is walked once: the arena bounds the walk) */
  rf_count(&R, r, c->res.dt);
  Port v = NONE;
  if (!R.bad) {
    RfArg a = { &R, r, NONE };
    pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);
    pthread_t t;
    if (!pthread_create(&t, &at, rf_thread, &a)) { pthread_join(t, NULL); v = a.out; }
    pthread_attr_destroy(&at);
  }
  lbl = R.lbl;
  for (long i = 0; i < R.cap; i++) free(R.tab[i].outs);
  free(R.tab);
  if (c->release) c->release();
  if (R.bad) DBG("the structure result could not be read back: the net computes it\n");
  return R.bad ? NONE : v;
}

/* Could this argument be a numeral already -- `\c.\n.` over a cell or a terminal -- WITHOUT forcing anything?
   Reading a number forces its layers, and a FUNCTION argument forced so would have its body reduced (an `_op`
   head under its binder taken apart) before the compiler reads it. */
static int numeral_shape(const Net *n, Port p) {
  Port c = dhop(n, p);
  if (!is(n, c, LAM, 0)) return 0;
  Port nn = dhop(n, W(n, (Port){c.node, 2}));
  if (!is(n, nn, LAM, 0)) return 0;
  Port b = dhop(n, W(n, (Port){nn.node, 2}));
  if (is(n, b, LAM, 0)) return 1;                    /* a terminal: \c.\n.<sign> */
  if (!is(n, b, APP, 1)) return 0;
  Port ia = dhop(n, W(n, (Port){b.node, 0}));
  if (!is(n, ia, APP, 1)) return 0;
  Port hd = dhop(n, W(n, (Port){ia.node, 0}));
  return hd.node == c.node && hd.port == 1;          /* a cell applies its own first binder */
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
    int car = c ? c->arity : (lin_precompile_depth ? 0 : (N = n, fun_arity(F)));   /* (a function that needs its arguments: see below) */
    /* ARGUMENTS THAT ARE NOT VALUES YET -- `(check (make 7))` -- are compiled into the unit as expressions, rather
       than built by the net first (which is the slow part); a number already there is passed as one.  A function
       taking a FUNCTION compiles only with its arguments (it is specialised to them). */
    if (car > 0 && car <= 8) {
      Port ap[8]; int an[8], cl = appy, nexpr = 0, shape = 1;
      for (int k = 0; k < car; k++) {
        Port nx = W(n, (Port){cl, 1});
        if (!is(n, nx, APP, 0)) { shape = 0; break; }
        cl = nx.node; ap[k] = W(n, (Port){cl, 2});
        long dummy; an[k] = numeral_shape(n, ap[k]) && net_read_i64(n, ap[k], &dummy);
        nexpr += !an[k];
      }
      if (shape && nexpr) {
        Compiled *c2 = compile_fn_ex(n, F, ap, an);
        if (c2) {
          int nn = 0;
          for (int k = 0; k < car; k++) if (an[k]) net_read_i64(n, ap[k], &args[nn++]);
          extern int lin_threads;
          long r = c2->fn(args, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
          if (c2->aborted && *c2->aborted) { DBG("the data unit's guard fired: the net computes it\n"); }
          else {
            Port val = result_port(n, c2, r);
            if (val.node < 0) goto decline_ex;
            Port out = W(n, (Port){cl, 1});
            net_link(n, val, out, 1);
            net_drop(n, cl);
            DBG("folded a call with %d expression argument%s -> %s\n", nexpr, nexpr == 1 ? "" : "s", c2->kind == 5 ? "a structure" : "a word");
            lin_fold_bump(); folded++; (*changed)++; n->steps++;
            continue;
          }
          decline_ex:;
        }
      }
    }
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
      /* a number -- an integer or a float, both numerals -- or an FFI call still to dispatch */
      if (!net_read_i64(n, v, &args[k])) {
        Val fv; memset(&fv, 0, sizeof fv);
        if (net_read_value(n, v, DT_FFI, &fv) && (fv.kind == 1 || fv.kind == 4)) args[k] = fv.iv;
        else { ok = 0; DBG("argument %d is not a number\n", k); }
      }
      if (!y_call(n, p1, p2, &h, &appy, &F)) { ok = 0; break; }   /* forcing rewrote the call itself */
    }
    if (!ok) {
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    extern int lin_threads;
    long r = c->fn(args, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
    if (c->aborted && *c->aborted) {                 /* a data unit's guard fired: the net computes it, lazily */
      DBG("the data unit's guard fired: the net computes it\n");
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    Port val = result_port(n, c, r);
    if (val.node < 0) {
      if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
      continue;
    }
    Port out = W(n, (Port){call, 1});
    net_link(n, val, out, 1);
    net_drop(n, call);                                  /* erases the call chain, Y and F behind it */
    DBG("folded a call of arity %d -> %s\n", c->arity, c->kind == 5 ? "a structure" : "a word");
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
