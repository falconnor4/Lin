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
__thread __attribute__((tls_model("initial-exec"))) int64_t *lin_hp, *lin_he;
__thread __attribute__((tls_model("initial-exec"))) int64_t *lin_fl[8 + 8 * sizeof(int64_t)];   /* freed blocks by size class, for reuse: see lin_cls */
static int dbg = -1;
#include <time.h>
static double now_ms(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec * 1e3 + t.tv_nsec / 1e6; }
#define DBG(...) do { if (dbg) { fprintf(stderr, "fn: " __VA_ARGS__); fflush(stderr); } } while (0)
#define IN(n, i) ((i) >= 0 && (i) < (n)->nn)
#define NONE ((Port){-1, 0})
static inline Port W(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }
static inline int live(const Net *n, Port p) { return IN(n, p.node) && !n->dead[p.node]; }
static inline int is(const Net *n, Port p, int tag, int port) { return live(n, p) && n->tag[p.node] == tag && (int)p.port == port; }
/* The value a port carries: arriving at a fan's copy port means the value comes from its principal side. */
/* WHICH COPY A READ STANDS FOR.  A recursive call the unit declined is rewritten with ONE fan on the function, labelled
   with a label of its own (y_expand: net_fresh_label), and every fan the copying makes carries that label.  So while
   a unit is read (xing_on), each FRESH-labelled fan crossed at a copy port is remembered, and a fan-in met later with
   that label -- the function's body still shared between this call's copy and the copy kept for the next call -- is
   read at the copy the path in crossed: the pairing the two fans' annihilation will give.  Only fresh labels: an
   ordinary label is a level, which two unrelated fans can share (measured: reading by level gave a wrong answer).
   A label crossed at both copy ports is not decided, and the read declines as it always did. */
typedef struct { Scope l; int port; } Xing;
static Xing *xing; static int nxing, cxing, xing_on;
static int xing_fresh(const Net *n, Scope l) { return l > 0 && (int)l <= n->nlv && n->lv_parent[l] == 0 && n->lv_bit[l] == 3; }
static void xing_note(const Net *n, Port p) {
  Scope l = n->scope[p.node];
  if (!xing_fresh(n, l)) return;
  for (int i = 0; i < nxing; i++) if (xing[i].l == l) { if (xing[i].port != (int)p.port) xing[i].port = -1; return; }
  if (nxing >= cxing) xing = realloc(xing, sizeof *xing * (size_t)(cxing = cxing ? cxing * 2 : 64));
  xing[nxing++] = (Xing){ l, (int)p.port };
}
static int xing_port(const Net *n, int fan) {
  Scope l = n->scope[fan];
  if (!xing_fresh(n, l)) return -1;
  for (int i = 0; i < nxing; i++) if (xing[i].l == l) return xing[i].port;
  return -1;
}
static Port dhop(const Net *n, Port p) {
  for (int k = 0; k < n->nn && live(n, p) && n->tag[p.node] == DUP && p.port != 0; k++) {
    if (xing_on) xing_note(n, p);
    p = W(n, (Port){p.node, 0});
  }
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
/* (Y v) however it is consumed -- applied, shared by a fan, passed on -- and whatever v is */
static int y_fix(const Net *n, Port p1, Port p2, int *h, int *appy) {
  if (p1.port || p2.port || !live(n, p1) || !live(n, p2)) return 0;
  int a = n->tag[p1.node] == LAM ? p1.node : p2.node, b = a == p1.node ? p2.node : p1.node;
  if (n->tag[a] != LAM || n->tag[b] != APP || !is_y(n, a)) return 0;
  *h = a; *appy = b;
  return 1;
}

/* ---- the evaluator --------------------------------------------------------------------------- */
enum { E_CONST, E_PARAM, E_BIN, E_IF, E_CALL, E_FOP,   /* E_FOP: a float row (FROW[k]) over args */
       E_CTOR, E_MATCH, E_FIELD, E_VOP,
       E_LET, E_VAR,
       E_DUP, E_DROP, E_AFTER, E_SPEC };   /* E_SPEC: a (a block of constructor ci) taken apart, then b -- see MATCH ON A DYING VALUE */   /* (MEMORY) E_DUP: a, with a reference of its own; E_DROP: the drops, then b; E_AFTER: a, then the drops */   /* E_LET: a (the value) bound for b (the body); E_VAR: that value, by name (bind: its E_LET) -- see EXPLICIT BINDING */   /* E_VOP: a vector operation (LIN_VOP_*, k) over args: OWNED VECTORS */   /* data: constructor k (its index) of args; match on a over args (one result per
                                        constructor, in order); field k of a */
struct Drop { const struct Expr *p; int fn; struct Drop *next; };   /* a name released (E_DROP, E_AFTER: see MEMORY); fn <= -2 frees reuse token -2 - fn */
typedef struct Expr { int op; int64_t k; struct Expr *a, *b, *c; struct Expr **args; int nargs, kind;   /* kind 1 int, 3 bool */
                      int id, var, vscope, untag, box; const LinCtor *ci; struct Drop *drops; struct Expr *bind; unsigned char **mspec; int tok; } Expr;
   /* id: a dense index; var: the local it is bound to while emitting.  ci: the constructor (E_CTOR, E_FIELD) or one of
      the datatype's (E_MATCH, E_SPEC); untag: the datatype's blocks carry no tag (box: its one boxed constructor).
      (MEMORY) drops: what E_DROP / E_AFTER release; bind: an E_LET's name, a name's E_LET; mspec[0]: the fields an
      E_SPEC loads; tok: a constructor built in reuse token tok-1 when it is there */
enum { V_CLO, V_SYM, V_C1, V_COND, V_SELF, V_FIX, V_MCONS, V_MCONS1, V_MCELL, V_MNIL, V_MATCH };   /* V_FIX: a recursive function met, its arguments being collected */   /* V_MATCH: data applied to branches */
struct Lz;
typedef struct ShArgs ShArgs;
typedef struct { unsigned char k; const char *dt; const ShArgs *a; } Shape;     /* (see SHAPES below) */   /* a: the datatype's parameters' shapes (interned), NULL: not known */
struct ShArgs { int n; Shape s[]; };
typedef struct Env { int lam; struct Lz *t; struct Env *next; } Env;
typedef struct V { int k; int lam; Env *env; Expr *e; struct Lz *a, *b; struct Lz **args; int nargs; Expr *x; int cells; } V;   /* cells: a match on the cell encoding */   /* x: to_expr's answer */
typedef struct Lz { int state; Port p; Env *env; struct Lz *f, *x; V *v; int busy; int port; } Lz;   /* 0 port, 1 application, 2 value */   /* port: it was a port (p, env), forced or not */

/* One compile attempt's memory: everything is freed together, so it is carved from chunks rather than asked of
   malloc one object at a time (measured: 8.7M callocs, a fifth of examples/games/tictactoe.lin).  A chunk is
   as large as the attempt has needed so far, doubled; an object larger than a quarter of one gets its own. */
static void **arena; static int narena, arcap;
static char *ar_at; static size_t ar_left, ar_chunk;
static void *ar_keep(void *p) {
  if (narena >= arcap) arena = realloc(arena, (size_t)(arcap = arcap ? arcap * 2 : 1024) * sizeof *arena);
  arena[narena++] = p; return p;
}
static void *A(size_t sz) {
  sz = (sz + 15) & ~(size_t)15;
  if (sz > ar_left) {
    if (!ar_chunk) ar_chunk = 4096 * 16;
    if (sz > ar_chunk / 4) return ar_keep(calloc(1, sz));
    ar_at = ar_keep(calloc(1, ar_chunk)); ar_left = ar_chunk; ar_chunk *= 2;
  }
  void *p = ar_at; ar_at += sz; ar_left -= sz; return p;
}
struct Memo;
static struct Memo **memo; static int memocap;
static void arena_free(void) {
  for (int i = 0; i < narena; i++) free(arena[i]);
  narena = 0; ar_left = 0; ar_at = NULL; ar_chunk = 0;
  if (memocap) memset(memo, 0, (size_t)memocap * sizeof *memo);   /* its entries lived in the arena */
}

static Net *N; static int64_t fuel; static int failed;
/* THE UNIT: every function this compilation reaches.  funs[0] is the one being called; a call to another
   recursive function (a `Y G` met while evaluating) compiles G as funs[k], once per node. */
typedef struct { int lam, arity; Expr *body; unsigned strict; Expr **pnode; struct V **known; struct Env *outer; } Fun;   /* pnode: each parameter's node */
/* known: a FUNCTION-VALUED parameter this copy is specialised to (NULL: a parameter like any other) -- see spec_call */
static Fun *funs; static int nfun, funcap;
/* A SPECULATIVE read that fails leaves the functions it began half-built.  They are not handed their numbers
   back: a value computed (and remembered) during the read may name a function that DID complete, and giving its
   number to another function made two different closures one -- `(av n (av n u))`, nested, called itself.
   The half-built ones are closed off instead: no call can find them, and each is a constant. */
static Expr *hc(Expr *e); static Expr *mke(int op, int kind);
static void fun_rollback(int from) {
  for (int i = from; i < nfun; i++) if (!funs[i].body) { funs[i].lam = -1; funs[i].known = NULL; Expr *z = mke(E_CONST, 1); z->k = 0; funs[i].body = hc(z); }
}
static int arity;   /* funs[0]'s, which the entry point and the parallel sites are written for */
static int fail_quiet;   /* a speculative read (is_fun_value): its failures are answers, not declines */
static void fail(const char *why) { if (!failed && !fail_quiet) DBG("declined: %s\n", why); failed = 1; }

static V *mkv(int k) { V *v = A(sizeof *v); v->k = k; return v; }
static Lz *ready(V *v) { Lz *l = A(sizeof *l); l->state = 2; l->v = v; return l; }
static Lz *lzp(Port p, Env *e) { Lz *l = A(sizeof *l); l->state = 0; l->p = p; l->env = e; l->port = 1; return l; }
static Lz *lzapp(Lz *f, Lz *x) { Lz *l = A(sizeof *l); l->state = 1; l->f = f; l->x = x; return l; }
static int eid;
static Expr *mke(int op, int kind) { Expr *e = A(sizeof *e); e->op = op; e->kind = kind; e->id = eid++; e->var = -1; return e; }
/* HASH-CONSING: a node equal to one already built (same operation, same children -- which are themselves
   canonical) IS that node, so a value the program computes twice along different paths is one DAG node, and
   the region binder computes it once.  Compiled code is pure, so equal expressions are equal values. */
static Expr **hct; static int hccap, hcn;
static uint64_t hc_hash(const Expr *e) {
  uint64_t h = (uint64_t)e->op * 1000003u ^ (uint64_t)e->k * 2654435761u ^ (uint64_t)e->kind * 97u
                  ^ (uint64_t)e->nargs * 131u;
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
    for (int i = 0; i < oc; i++) if (ot[i]) { uint64_t j = hc_hash(ot[i]) & (uint64_t)(hccap - 1); while (hct[j]) j = (j + 1) & (uint64_t)(hccap - 1); hct[j] = ot[i]; hcn++; }
    free(ot);
  }
  uint64_t j = hc_hash(e) & (uint64_t)(hccap - 1);
  for (; hct[j]; j = (j + 1) & (uint64_t)(hccap - 1)) if (hc_eq(hct[j], e)) return hct[j];
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
static int64_t const_int(V *v, int *ok);
static int64_t fold_op(int64_t code, int64_t x, int64_t y) {   /* an integer operation on known operands: the C's own rows */
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
/* (the operator index of an `_op` application, read without judging the operands; -1 if it states none) */
static int64_t op_peek(Lz *list) {
  V *l = force(list); if (!l) return -1;
  V *r = apply(apply(l, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
  if (!r || r->k != V_MCELL) return -1;
  int ok; int64_t code = const_int(force(r->a), &ok);
  return ok ? code : -1;
}
/* OWNED VECTORS.  A vector the unit makes and uses is one block -- {length, capacity, elements} -- read and
   written by index, rebuilt in place when its count says it is the only reference and copied when it is not
   (which is what the trie's persistence costs, paid only when it is used); `apush` doubles the capacity.  Only
   counted code knows a block's count, so only counted units keep vectors flat; and a vector the unit is given by
   the net, or gives back, is the net's trie: such a unit is compiled again with the operations as their meaning. */
static int vop_off, vop_used;
static int vop_ok(void) { return !vop_off; }
static int vt_find(void);   /* (the trie a vector is on the net: A VECTOR AT THE EDGE) */
static const char VEC_DT[] = "vec";                  /* (a vector's shape: a datatype of one parameter, its elements) */
static int vop_read(const Expr *a); static int vop_takes(const Expr *e, int i);
static int sh_has_vec(Shape s) {                     /* a vector anywhere in what a value of shape s holds */
  if (s.k == 5 && s.dt == VEC_DT) return 1;
  for (int i = 0; s.a && i < s.a->n; i++) if (sh_has_vec(s.a->s[i])) return 1;
  return 0;
}
static V *vop_value(int64_t code, Lz *list) {
  V *l = force(list); if (!l) return NULL;
  Expr *slot[3]; int ns = 0, want = code == LIN_VOP_NEW || code == LIN_VOP_GET || code == LIN_VOP_PUSH ? 2 : code == LIN_VOP_SET ? 3 : 1;
  for (int i = 0; i < 5 && !failed; i++) {
    V *r = apply(apply(l, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) return NULL;
    if (r->k == V_MNIL) break;
    if (r->k != V_MCELL || ns > want) { fail("a vector operation's operands are not a list"); return NULL; }
    if (i > 0) { Expr *e = to_expr(force(r->a)); if (!e) return NULL; slot[ns++] = e; }
    l = force(r->b); if (!l) return NULL;
  }
  if (ns != want) { fail("a vector operation with the wrong operands"); return NULL; }
  V *v = mkv(V_SYM);
  Expr *e = mke(E_VOP, code == LIN_VOP_LEN ? 1 : code == LIN_VOP_GET ? 1 : 5); e->k = code; e->nargs = ns;
  e->args = A(sizeof(Expr *) * (size_t)ns); for (int i = 0; i < ns; i++) e->args[i] = slot[i];
  vop_used = 1; v->e = hc(e); return v;
}
static V *op_value(Lz *list) {
  { int64_t c = op_peek(list); if (failed) return NULL; if (c >= LIN_VOP_FIRST && c <= LIN_VOP_LAST) return vop_value(c, list); }
  V *l = force(list); if (!l) return NULL;
  Expr *slot[4]; int ns = 0; int64_t code = -1;
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
static const LinCtor *marker_ctor(Port idp, Env *env, int64_t *id) {
  int ok; *id = const_int(eval(idp, env), &ok);
  return ok ? lin_ctor_info(*id) : NULL;
}
/* LAYOUT: a datatype with exactly ONE constructor that has fields (a tree, a list, most ADTs) needs no tag in its
   blocks -- being a block at all says which constructor it is -- so a match tests only the low bit, as C tests a
   pointer for null, and a node is a word smaller.  (Measured: the tag load was half of a tree insert.) */
static int dt_boxed(const char *dt, int *box) {      /* how many constructors of dt have fields; *box: the last */
  int n = 0; const LinCtor *c;
  for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->k > 0) { n++; *box = c->i; }
  return n;
}
/* A field's declared type, from the constructor's descriptor (src/type.c desc_rec: N B F ? a letter each,
   L<elem>, P<i>;, D<name>(<args>)): a field declared `bool` is read as a condition, not as data. */
static const char *fd_skip(const char *d) {
  if (!d || !*d) return d;
  switch (*d) {
  case 'L': return fd_skip(d + 1);
  case 'P': { const char *e = strchr(d, ';'); return e ? e + 1 : d + strlen(d); }
  case 'D': { const char *p = strchr(d, '('); if (!p) return d + strlen(d); p++;
              while (*p && *p != ')') { const char *q = fd_skip(p); if (q == p) break; p = q; }
              return *p == ')' ? p + 1 : p; }
  default: return d + 1;
  }
}
static int field_is_bool(const LinCtor *ci, int j) {
  const char *d = ci ? ci->fdesc : NULL;
  for (int i = 0; d && *d && i < j; i++) d = fd_skip(d);
  return d && *d == 'B';
}
static int field_is_param(const LinCtor *ci, int j) {
  const char *d = ci ? ci->fdesc : NULL;
  for (int i = 0; d && *d && i < j; i++) d = fd_skip(d);
  return d && *d == 'P';
}
/* A branch that is a constructor with no fields -- an immediate word -- takes the kind the other branches say.  In a
   typed program the branches agree anyway; the one place they do not is the library's `head`, whose empty case
   answers `nil` (an immediate: a number where a number is read, the empty list where a list is), as the list
   encoding's end always answered one word whatever was asked of it. */
static int neutral_branch(const Expr *x) { return x && ((x->op == E_CTOR && x->nargs == 0) || (x->op == E_CONST && x->box)); }
static Expr *field_expr(Expr *scrut, int j, int untag, const LinCtor *ci) {
  Expr *e = mke(E_FIELD, field_is_bool(ci, j) ? 3 : 1); e->a = scrut; e->k = j; e->untag = untag; e->ci = ci; return hc(e);
}
/* THE LIST DATATYPE.  A list is the core's own datatype (src/main.c, builtin_list): `(cons h t)`, a block {h, t},
   or `nil`, an immediate.  A value built by its constructors carries their marker, and a `match` on it is the
   datatype's own; a list may also be APPLIED to two branches with no marker (`(l (\h (\t ..)) z)`, the way the
   encoding was used before it was declared), and that is taken apart as the same datatype: the cell branch gets
   the fields, the end the second branch.  Whether a value applied that way really is a list is the SHAPE
   analysis' question (a numeral is cells too, of bits, ended by a sign -- one used both ways is not compiled). */
static const LinCtor *cell_cons, *cell_nil;
static const char *cells_dt;
static void cells_init(void) {                       /* (re-read each time: the registry may have moved) */
  cell_cons = lin_ctor_info(lin_list_cons_id); cell_nil = lin_ctor_info(lin_list_nil_id);
  cells_dt = cell_cons ? cell_cons->dt : NULL;
}
static Expr *field_expr(Expr *scrut, int j, int untag, const LinCtor *ci);
static V *cells_add(V *m, Lz *x) {
  if (m->nargs == 0) {                               /* the cell branch is a FUNCTION of the cell's two parts */
    V *bv = force(x); if (!bv) return NULL;
    if (bv->k != V_CLO && bv->k != V_FIX && bv->k != V_SELF) { fail("a value applied to something that is not a branch"); return NULL; } V *v = mkv(V_MATCH); v->e = m->e; v->cells = 1; v->nargs = 1; v->args = A(sizeof(Lz *)); v->args[0] = x; v->lam = 2; return v; }
  cells_init();
  if (!cell_cons || !cell_nil) { fail("no cell datatype"); return NULL; }
  Expr *r = mke(E_MATCH, 1); r->a = m->e; r->nargs = 2; r->args = A(sizeof(Expr *) * 2);
  int box = 0; r->untag = dt_boxed(cell_cons->dt, &box) == 1; r->box = box; r->ci = cell_cons;
  V *b = force(m->args[0]);
  for (int j = 0; b && j < 2; j++) { V *fv = mkv(V_SYM); fv->e = field_expr(m->e, j, r->untag, cell_cons); b = apply(b, ready(fv)); }
  if (!(r->args[0] = to_expr(b))) return NULL;
  if (!(r->args[1] = to_expr(force(x)))) return NULL;   /* the end: the second branch */
  int k0 = r->args[0]->kind, k1 = r->args[1]->kind;
  r->kind = r->args[0]->op == E_CALL || neutral_branch(r->args[0]) ? k1 : r->args[1]->op == E_CALL || neutral_branch(r->args[1]) ? k0
          : k0 == k1 ? k0 : (k0 == 5 || k1 == 5 ? 5 : 1);
  V *res = mkv(V_SYM); res->e = hc(r); return res;
}
static V *match_add(V *m, Lz *x) {
  /* (a branch is net structure: a port, perhaps forced already -- one arm of a conditional applies it to its
     constructor's fields before the other arm takes it apart) */
  if (m->cells || (m->nargs == 0 && !(x->port && ({ Port b_, i_; int l_; marker_app(x->p, &b_, &l_, &i_); }))))
    return cells_add(m, x);
  if (!x->port) { fail("a match branch that is not net structure"); return NULL; }
  Port body, idp; int lam; int64_t id;
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
    for (int64_t k = 1; (c2 = lin_ctor_info(k)); k++) if (c2->dt == ci->dt && c2->i == i) break;
    if (!c2) { fail("a constructor missing from the registry"); return NULL; }
    V *b = force(v->args[i]);
    for (int j = 0; b && j < c2->k; j++) { V *fv = mkv(V_SYM); fv->e = field_expr(m->e, j, untag, c2); b = apply(b, ready(fv)); }
    if (!(r->args[i] = to_expr(b))) return NULL;
    if (r->args[i]->op == E_CALL) continue;          /* (a recursive call has the kind the other branches say) */
    if (neutral_branch(r->args[i])) { if (kind < 0 && i == ci->m - 1) kind = r->args[i]->kind; continue; }
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
  Port body, idp; int mlam; int64_t id;
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
    if (op_head(f->lam)) {
      int64_t c = op_peek(x);
      if (failed) return NULL;
      if (c < LIN_VOP_FIRST || c > LIN_VOP_LAST || vop_ok()) return op_value(x);
      /* (a vector operation the unit does not keep flat: its meaning, the trie, is compiled like any code) */
    }
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
  /* A VARIABLE OF A COPY.  A function the net is still copying (the step of a loop that runs through effects,
     whose turns each get a copy) has its body shared between the copies, so a read inside it can meet a fan-in:
     its two inputs are the two copies'.  Which copy this evaluation stands for is the copy it entered the body
     by: the fresh-labelled fans the walk to the callee crossed (WHICH COPY A READ STANDS FOR, above). */
  if (t == DUP && p.port == 0) {
    int k = xing_port(N, p.node);
    if (k == 1 || k == 2) return eval(W(N, (Port){p.node, k}), env);
  }
  { static const char *const tn[] = {"lambda", "application", "fan", "eraser", "root"};   /* (which, so the coverage report can say) */
    static char why[96]; snprintf(why, sizeof why, "a node the evaluator does not read (%s, port %d)", t >= 0 && t < 5 ? tn[t] : "?", p.port);
    fail(why); }
  return NULL;
}

/* Constants: a numeral answers the cell markers bit by bit, its terminal answers with its SIGN. */
static int const_bool(V *v, int *ok) {
  V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
  *ok = r && (r->k == V_MCONS || r->k == V_MNIL);
  return r && r->k == V_MCONS;
}
static int64_t const_int(V *v, int *ok) {
  uint64_t a = 0; *ok = 0;
  for (int k = 0; k <= LIN_INT_BITS && v && !failed; k++) {
    if (v->k != V_CLO) return 0;
    V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) return 0;
    if (r->k == V_MCELL) {
      int bo; int b = const_bool(force(r->a), &bo); if (!bo) return 0;
      if (k < LIN_INT_BITS) a |= (uint64_t)b << k;
      v = force(r->b); continue;
    }
    if (r->k == V_CLO) {                           /* the terminal answered with its SIGN (a boolean) */
      int so; int nonneg = const_bool(r, &so); if (!so) return 0;
      if (!nonneg && k < LIN_INT_BITS) a |= ~(uint64_t)0 << k;
      *ok = k > 0; return (int64_t)a;
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
    if (r->k != V_MCELL) { buf[n] = 0; return n > 0 && r->k == V_MNIL; }   /* the end answers with the second branch */
    int ok; int64_t ch = const_int(force(r->a), &ok);
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
  char name[64]; int64_t sfuel = fuel; int sfail = failed;
  fail_quiet++;
  int named = const_str(eval(W(N, (Port){fa.node, 2}), v->env), name, (int)sizeof name);
  fail_quiet--;
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
static Expr *to_expr(V *v);
static int numeral_shape(const Net *n, Port p);
static int inp_on;
static int input_of(Port p);
/* the END of a list, by itself: an immediate, so a constant of the unit (never a runtime input -- an input is
   not known to be unshared, and an empty accumulator must not cost the list built on it its ownership) */
static int list_end(const Net *n, Port p) {
  Port c = dhop(n, p); if (!is(n, c, LAM, 0)) return 0;
  Port nn = dhop(n, W(n, (Port){c.node, 2})); if (!is(n, nn, LAM, 0)) return 0;
  Port b = dhop(n, W(n, (Port){nn.node, 2}));
  Port ma, mi; int ml;                               /* (`\c.\n.((\_c n) NIL)`: the marker, then the second binder) */
  if (marker_app(b, &ma, &ml, &mi)) b = dhop(n, ma);
  return b.node == nn.node && b.port == 1;
}
/* A constant list: the cells answer the markers one by one, the end answers with a boolean.  Speculative: a value
   that is not a list leaves no trace. */
static Expr *const_cells(V *v) {
  cells_init(); if (!cell_cons || !cell_nil) return NULL;
  int sf = failed, snf = nfun; int64_t sfu = fuel;
  Expr **hs = NULL, *tailx = NULL; int nh = 0, cap = 0, ok = 0;
  fail_quiet++;
  for (int k = 0; k <= N->nn && v && !failed; k++) {
    if (v->k != V_CLO) {                           /* a cell built on a list computed elsewhere: its tail */
      if (nh && (tailx = to_expr(v))) ok = 1;
      break;
    }
    V *r = apply(apply(v, ready(mkv(V_MCONS))), ready(mkv(V_MNIL)));
    if (!r) break;
    if (r->k == V_MCELL) {
      Expr *h = to_expr(force(r->a)); if (!h) break;
      if (nh == cap) { Expr **o = hs; hs = A(sizeof *hs * (size_t)(cap = cap ? cap * 2 : 16)); if (nh) memcpy(hs, o, sizeof *hs * (size_t)nh); }
      hs[nh++] = h; v = force(r->b); continue;
    }
    ok = r->k == V_MNIL;                             /* the end: it answered with the second branch */
    break;
  }
  fail_quiet--;
  if (!ok) { failed = sf; fuel = sfu; fun_rollback(snf); return NULL; }
  int box = 0, untag = dt_boxed(cell_cons->dt, &box) == 1;
  Expr *l = tailx;
  if (!l) { l = mke(E_CTOR, 5); l->k = cell_nil->i; l->nargs = 0; l->untag = untag; l->ci = cell_nil; l = hc(l); }
  for (int i = nh - 1; i >= 0; i--) {
    Expr *c = mke(E_CTOR, 5); c->k = cell_cons->i; c->nargs = 2; c->args = A(sizeof(Expr *) * 2);
    c->args[0] = hs[i]; c->args[1] = l; c->untag = untag; c->ci = cell_cons; l = hc(c);
  }
  return l;
}
static Expr *to_expr(V *v) {                       /* one answer per value: a shared value is one node */
  if (failed || !v) return NULL;
  if (v->k == V_SYM) return v->e;
  if (!v->x) v->x = to_expr_v(v);
  return v->x;
}
#define SMALL_CONST_NODES 65536
static int small_data(const Net *n, Port p, int limit); static int const_tree(const Expr *e, int depth); static Expr *const_cells(V *v);
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
    /* (speculative: applying a cell to the markers takes its symbolic parts apart, which is no failure) */
    int ok, sf = failed, snf = nfun; int64_t sfu = fuel;
    fail_quiet++; int64_t k = const_int(v, &ok); if (failed) ok = 0; fail_quiet--;
    if (!ok) { failed = sf; fuel = sfu; fun_rollback(snf); }
    if (ok) { Expr *e = mke(E_CONST, 1); e->k = k; return hc(e); }
    fail_quiet++; int bk = const_bool(v, &ok); if (failed) ok = 0; fail_quiet--;
    if (!ok) { failed = sf; fuel = sfu; fun_rollback(snf); }
    if (ok) { Expr *e = mke(E_CONST, 3); e->k = bk; return hc(e); }
    if (inp_on && !v->env && numeral_shape(N, (Port){v->lam, 0}) && !list_end(N, (Port){v->lam, 0})) {   /* a list already built: read in at call time */
      if (!lin_io_looping && small_data(N, (Port){v->lam, 0}, SMALL_CONST_NODES)) {   /* (a short one of pure data is a constant of the unit; not a loop's state: lin.h) */
        int sf = failed, snf = nfun; int64_t sfu = fuel;
        fail_quiet++; Expr *cl = const_cells(v); if (failed) cl = NULL; fail_quiet--;
        if (cl && const_tree(cl, 0)) return cl;
        failed = sf; fuel = sfu; fun_rollback(snf);
      }
      Expr *pe = mke(E_PARAM, 1); pe->k = input_of((Port){v->lam, 0}); pe->nargs = -1; return hc(pe);
    }
    Expr *cl = const_cells(v);                       /* a list (a string): its cells, as constructors */
    if (cl || failed) return cl;
    fail("a closure where a number belongs"); return NULL;
  }
  if (v->k == V_MATCH) { fail("a match with branches missing"); return NULL; }
  if (dbg > 1) DBG("[no number: V kind %d]\n", v->k);
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
  case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) s |= strict_r(e->args[i]); break;
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
static int64_t *cv_val; static int cv_cap;
static int cval(const Expr *e, int64_t *out) {           /* the node's value, when the known arguments decide it */
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
  int64_t x, y, r = 0; int ok = 0;
  if (e->op == E_BIN) { if (cval(e->a, &x) && cval(e->b, &y)) { r = fold_op(e->k, x, y); ok = 1; } }
  else if (cval(e->a, &x)) ok = cval(x ? e->b : e->c, &r);
  if (ok && e->id < cv_cap) cv_val[e->id] = r;
  mm_put(MM_SITE, e, ok ? 2u : 0u);
  if (ok) *out = r;
  return ok;
}
static unsigned strict_site_r(const Expr *e) {
  MEMO(MM_SSTR, e);
  int64_t c; unsigned s = 0;
  switch (e->op) {
  case E_PARAM: s = e->nargs == site_fid ? 1u << e->k : 0; break;
  case E_BIN: s = strict_site_r(e->a) | strict_site_r(e->b); break;
  case E_IF:
    s = strict_site_r(e->a);
    if (cval(e->a, &c)) s |= strict_site_r(c ? e->b : e->c);
    else s |= strict_site_r(e->b) & strict_site_r(e->c);
    break;
  case E_CALL: for (int i = 0; i < e->nargs; i++) if ((funs[e->k].strict >> i) & 1u) s |= strict_site_r(e->args[i]); break;
  case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) s |= strict_site_r(e->args[i]); break;
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
  case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs && ok; i++) ok = args_safe_r(e->args[i]); break;
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
  case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs && !r; i++) r = has_self(e->args[i]); break;
  case E_FIELD: r = has_self(e->a); break;
  case E_MATCH: r = has_self(e->a); for (int i = 0; i < e->nargs && !r; i++) r = has_self(e->args[i]); break;
  case E_LET: r = has_self(e->a) || has_self(e->b); break;
  case E_DUP: case E_AFTER: r = has_self(e->a); break;
  case E_DROP: r = has_self(e->b); break;
  case E_SPEC: r = has_self(e->b); break;
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
  case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs && !r; i++) r = has_call(e->args[i]); break;
  case E_FIELD: r = has_call(e->a); break;
  case E_MATCH: r = has_call(e->a); for (int i = 0; i < e->nargs && !r; i++) r = has_call(e->args[i]); break;
  case E_LET: r = has_call(e->a) || has_call(e->b); break;
  case E_DUP: case E_AFTER: r = has_call(e->a); break;
  case E_DROP: r = has_call(e->b); break;
  case E_SPEC: r = has_call(e->b); break;
  default: break;
  }
  return (int)mm_put(MM_CALL, e, (unsigned)r);
}
static int nsite;
static int emitting;   /* the unit function being written: a parameter of another one cannot appear in it */
/* DESTINATION PASSING.  `(scons (f h) (smap f t))` is not a tail call -- the cell is built after the call returns
   -- so a list a million long was a million frames.  A function with such a tail gets a second form, `fN_d(dst,
   ...)`, that writes its result through `dst` instead of returning it: the cell is built FIRST, with a hole where
   the call's result goes, and the call becomes a tail call given the hole's address.  cc turns that into a loop.
   `hasd[f]`: f has the form; `tailpos`: the expression about to be written is in tail position of one. */
static unsigned char *hasd; static int tailpos; static const struct Expr *dp_hole;
static int emitting;
static int dp_self;   /* how the function being written names ITSELF: 0 `_d`, 1 `_ds` (its loop), 2 `_dp` (a stretch of its loop) */
static const char *dp_name(int64_t k) { return k != emitting || !dp_self ? "_d" : dp_self == 1 ? "_ds" : "_dp"; }
static const char *dp_stop(int64_t k) { return k == emitting && dp_self == 2 ? ", stop" : ""; }
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
  case E_CALL: case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) count_uses(e->args[i]); break;
  case E_FIELD: count_uses(e->a); break;
  case E_MATCH: count_uses(e->a); for (int i = 0; i < e->nargs; i++) count_uses(e->args[i]); break;
  case E_LET: count_uses(e->a); count_uses(e->b); break;
  case E_DUP: case E_AFTER: count_uses(e->a); break;
  case E_DROP: count_uses(e->b); break;
  case E_SPEC: count_uses(e->a); count_uses(e->b); break;
  }
  /* (a local a path's end drops is used there too: so the region binds it, and the drop names what was computed --
     computed again, it would be another reference, and the first never released) */
  for (const struct Drop *d = e->drops; d; d = d->next) if (d->p && d->p->op != E_PARAM) count_uses(d->p);
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
  case E_LET: r = iset_union(cert(e->a), cert(e->b), e->id); break;
  case E_DUP: case E_AFTER: r = iset_union(cert(e->a), (ISet){ NULL, 0 }, e->id); break;
  case E_DROP: r = iset_union(cert(e->b), (ISet){ NULL, 0 }, e->id); break;
  case E_SPEC: r = iset_union(cert(e->a), cert(e->b), e->id); break;
  case E_MATCH: {                                   /* the scrutinee, and what EVERY branch evaluates */
    ISet i = { NULL, 0 }; int first = 1;
    for (int k = 0; k < e->nargs; k++) {
      if (first) { ISet c0 = cert(e->args[k]); i.v = malloc((size_t)(c0.n + 1) * sizeof *i.v); memcpy(i.v, c0.v, (size_t)c0.n * sizeof *i.v); i.n = c0.n; first = 0; }
      else { ISet j = iset_inter(i, cert(e->args[k])); free(i.v); i = j; }
    }
    r = iset_union(cert(e->a), i, e->id); free(i.v); break;
  }
  case E_CALL: case E_FOP: case E_VOP: case E_CTOR:
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
  case E_CALL: case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) certain(e->args[i], c, out, n, cap); break;
  case E_FIELD: certain(e->a, c, out, n, cap); break;
  case E_MATCH: certain(e->a, c, out, n, cap); for (int i = 0; i < e->nargs; i++) certain(e->args[i], c, out, n, cap); break;
  case E_LET: certain(e->a, c, out, n, cap); certain(e->b, c, out, n, cap); break;
  case E_DUP: case E_AFTER: certain(e->a, c, out, n, cap); break;
  case E_DROP: certain(e->b, c, out, n, cap); break;
  case E_SPEC: certain(e->a, c, out, n, cap); certain(e->b, c, out, n, cap); break;
  }
  if (!in_set(c, e->id)) return;
  if (*n >= *cap) *out = realloc(*out, (size_t)(*cap = *cap ? *cap * 2 : 16) * sizeof **out);
  (*out)[(*n)++] = e;
}
static int has_call(const Expr *e);
static int fork_open(Buf *b, Buf *pre, const Expr *x, int budget, Buf *call, int *ok);
static int rf_dep(const Expr *x, const int *ci, unsigned char *seen) {   /* the last binding x reads (-1: none) */
  if (!x || x->op == E_PARAM || x->op == E_CONST || seen[x->id]) return -1;
  seen[x->id] = 1;
  if (ci[x->id] >= 0) return ci[x->id];
  if (bound(x)) return -1;
  int m = rf_dep(x->a, ci, seen), t;
  if ((t = rf_dep(x->b, ci, seen)) > m) m = t;
  if (x->op != E_CTOR && (t = rf_dep(x->c, ci, seen)) > m) m = t;
  for (int i = 0; i < x->nargs && x->args; i++) if ((t = rf_dep(x->args[i], ci, seen)) > m) m = t;
  return m;
}
static void rf_pick(const Expr *y, ISet c, const int *ci, unsigned char *seen, const Expr ***fx, int *nf) {
  if (!y || y->op == E_PARAM || y->op == E_CONST || seen[y->id] || ci[y->id] >= 0 || bound(y) || !in_set(c, y->id)) return;
  seen[y->id] = 1;
  if (y->op == E_CALL && st_uses[y->id] == 1 && !y->drops) { *fx = realloc(*fx, sizeof **fx * (size_t)(*nf + 1)); (*fx)[(*nf)++] = y; return; }
  rf_pick(y->a, c, ci, seen, fx, nf);
  if (y->op == E_IF || y->op == E_MATCH) return;     /* (only what is certainly evaluated) */
  if (y->op == E_LET) return;                        /* (its body reads a name not yet bound where a fork starts) */
  rf_pick(y->b, c, ci, seen, fx, nf); if (y->op != E_CTOR) rf_pick(y->c, c, ci, seen, fx, nf);
  for (int i = 0; i < y->nargs && y->args; i++) rf_pick(y->args[i], c, ci, seen, fx, nf);
}
static void region_forks(const Expr *e, const Expr **cand, int nc, const Expr ***fx, int **fpos, int *nf) {
  int *ci = malloc(sizeof *ci * (size_t)(eid + 1)); for (int i = 0; i <= eid; i++) ci[i] = -1;
  for (int i = 0; i < nc; i++) ci[cand[i]->id] = i;
  int lastheavy = -1; for (int i = 0; i < nc; i++) if (has_call(cand[i])) lastheavy = i;
  unsigned char *seen = calloc((size_t)eid + 1, 1);
  const Expr **all = NULL; int na = 0;
  rf_pick(e, cert(e), ci, seen, &all, &na);
  *fpos = malloc(sizeof **fpos * (size_t)(na + 1));
  for (int i = 0; i < na; i++) {
    memset(seen, 0, (size_t)eid + 1);
    int at = rf_dep(all[i], ci, seen) + 1;           /* started right after the last binding it reads */
    if (at <= lastheavy)                             /* (worth it only with a loop still to come beside it) */ { all[*nf] = all[i]; (*fpos)[(*nf)++] = at; }
  }
  *fx = all;
  free(ci); free(seen);
}
static void tail_uses(const Expr *e, unsigned *n) {   /* how often each node is reached where a region ends */
  if (!e) return;
  if (e->op == E_LET || e->op == E_DROP || e->op == E_SPEC) { tail_uses(e->b, n); return; }
  if (e->op == E_IF) { tail_uses(e->b, n); tail_uses(e->c, n); return; }
  if (e->op == E_MATCH) { for (int i = 0; i < e->nargs; i++) tail_uses(e->args[i], n); return; }
  if (e->op == E_CTOR) {                             /* (a call in two fields of one cell is two uses on one path) */
    for (int i = 0; i < e->nargs; i++) {
      if (e->args[i]->op != E_CALL) continue;
      int same = 0; for (int j = 0; j < e->nargs; j++) same += e->args[j] == e->args[i];
      if (same == 1) n[e->args[i]->id]++;
    }
    return;
  }
  if (e->op == E_CALL) n[e->id]++;
}
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  int tp = tailpos; tailpos = 0;
  st_grow(); stamp += 2;
  count_uses(e);
  const Expr **cand = NULL; int nc = 0, cc = 0;
  certain(e, cert(e), &cand, &nc, &cc);
  int nb = 0, ok = 1, nk = 0;
  /* (a call used only where the region ENDS -- each arm's tail, or the rest of a cell an arm builds -- is used
     once on any path: the arms are exclusive.  Bound first, it would no longer be a tail call: a filter whose
     two arms both step to the same next call became a recursion a million frames deep.) */
  unsigned *tails = NULL;
  if (tp || emitting >= 0) { tails = calloc((size_t)eid + 1, sizeof *tails); tail_uses(e, tails); }
  for (int i = 0; i < nc; i++) {                   /* choose first: emitting a binding runs nested regions' passes */
    const Expr *x = cand[i];
    if (tails && x->op == E_CALL && tails[x->id] >= st_uses[x->id]) continue;
    if (x != e && st_uses[x->id] >= 2 && x->op != E_CONST && x->op != E_PARAM && x->op != E_FIELD && x->op != E_VAR) cand[nk++] = x;   /* (a field read is one load: not worth a local; a name is one already) */
  }
  free(tails);
  nc = nk;
  /* THE ENTRY'S LOOPS, STARTED EARLY: a loop the expression certainly runs is started on a thread as soon as
     the bindings it reads exist -- so it runs alongside the loops bound after it (fasta's repeated sequence beside its two random ones, which follow each
     other) -- and joined where the expression begins. */
  const Expr **fx = NULL; int *fpos = NULL, nf = 0;
  if (par && emitting == -1 && nc) region_forks(e, cand, nc, &fx, &fpos, &nf);
  int *fsite = nf ? calloc((size_t)nf, sizeof *fsite) : NULL; Buf *fcall = nf ? calloc((size_t)nf, sizeof *fcall) : NULL;
  for (int i = 0; i <= nc && ok; i++) {
    for (int f = 0; f < nf && ok; f++) if (fpos[f] == i) {
      if (!nb++) put(b, "({ ");
      fcall[f] = nbuf(64); fsite[f] = fork_open(b, pre, fx[f], budget, &fcall[f], &ok);
    }
    if (i == nc) break;
    Expr *x = (Expr *)cand[i];
    if (!nb++) put(b, "({ ");
    int k = nvar++;                                /* reserved BEFORE the value is written: a binding nested in it takes later numbers */
    put(b, "int64_t v%d = ", k);
    ok = emitx(b, pre, x, par, budget - 1);
    put(b, "; ");
    x->var = k; x->vscope = fscope;
    cand[i] = x;                                   /* still listed, so it is unbound below */
  }
  for (int f = 0; f < nf && ok; f++) {             /* (joined before the expression: it is where they are used) */
    int k = fsite[f], v = nvar++;
    put(b, "int64_t v%d = sp%d_ ? (pthread_join(t%d_, 0), LIN_JOINED, s%d_.r) : %s; ", v, k, k, k, fcall[f].s);
    ((Expr *)fx[f])->var = v; ((Expr *)fx[f])->vscope = fscope;
  }
  tailpos = tp;
  ok = ok && emitx(b, pre, e, par, budget - 1);
  tailpos = 0;
  if (nb) put(b, "; })");
  for (int i = 0; i < nc; i++) if (cand[i]->var >= 0 && cand[i]->vscope == fscope) ((Expr *)cand[i])->var = -1;
  for (int f = 0; f < nf; f++) { if (fx[f]->var >= 0 && fx[f]->vscope == fscope) ((Expr *)fx[f])->var = -1; free(fcall[f].s); }
  free(fx); free(fpos); free(fsite); free(fcall);
  free(cand);
  return ok;
}
/* EXPLICIT BINDING.  The memory pass needs every value to have ONE name: a node of the DAG reached from two
   places is one value, and whether a use moves it or takes a count depends on what else uses it, on that path.
   So before it runs, each body is made a TREE whose shared values are bound by E_LET and named by E_VAR -- bound
   exactly where emit_region would bind them (a region binds what it certainly evaluates and uses twice or more:
   see above), so the tree's evaluation is the emitter's.  A match's scrutinee is always a name (its fields are
   read from it), and every other node is a copy of its own: a node the DAG shares between two exclusive arms is
   two nodes, one per arm, each with the decisions of its own path. */
static int indexed_pick(const Expr *e, const Expr **K, const Expr **S, int64_t *off);
static int anf_n;                                    /* the unit's names: w0, w1, ... */
static Expr *anf_tree(const Expr *e);
static Expr *anf_copy(const Expr *e) { Expr *c = A(sizeof *c); *c = *e; c->id = eid++; c->var = -1; c->bind = NULL; c->drops = NULL; return c; }
/* (a let's name is ONE node, shared by its uses: emitting the let binds it -- var, vscope -- so every use, and
   everything that asks bound(), sees the value in hand.  let->bind is the name, the name's bind its let) */
static Expr *anf_var(const Expr *let) { return let->bind; }
static Expr *anf_let(const Expr *x) {                /* a name for x's value (its body is set by the caller) */
  Expr *l = mke(E_LET, x->kind); l->k = anf_n++;
  Expr *v = mke(E_VAR, x->kind); v->k = l->k; v->bind = l; l->bind = v; return l;
}
static Expr *anf_region(const Expr *e, int tails_ok) {
  st_grow(); stamp += 2;
  count_uses(e);
  const Expr **cand = NULL; int nc = 0, cc = 0, nk = 0;
  certain(e, cert(e), &cand, &nc, &cc);
  unsigned *tails = NULL;
  if (tails_ok) { tails = calloc((size_t)eid + 1, sizeof *tails); tail_uses(e, tails); }
  for (int i = 0; i < nc; i++) {
    const Expr *x = cand[i];
    if (tails && x->op == E_CALL && tails[x->id] >= st_uses[x->id]) continue;
    if (x != e && st_uses[x->id] >= 2 && x->op != E_CONST && x->op != E_PARAM && x->op != E_FIELD) cand[nk++] = x;
  }
  free(tails);
  Expr **lets = nk ? A(sizeof *lets * (size_t)nk) : NULL;
  for (int i = 0; i < nk; i++) {                     /* each value, then its name (the next ones may read it) */
    Expr *x = (Expr *)cand[i];
    lets[i] = anf_let(x); lets[i]->a = anf_tree(x);
    x->var = i; x->vscope = fscope; x->bind = lets[i];   /* (bound: bound() sees it, and bind names its let) */
  }
  Expr *body = anf_tree(e);
  for (int i = nk - 1; i >= 0; i--) { lets[i]->b = body; body = lets[i]; }
  for (int i = 0; i < nk; i++) { Expr *x = (Expr *)cand[i]; x->var = -1; x->bind = NULL; }
  free(cand);
  return body;
}
static Expr *anf_tree(const Expr *e) {
  if (!e) return NULL;
  if (bound(e) && e->bind && e->bind->op == E_LET) return anf_var(e->bind);
  Expr *c;
  switch (e->op) {
  case E_IF:
    c = anf_copy(e); c->a = anf_tree(e->a);
    { const Expr *K, *S; int64_t off; if (indexed_pick(e, &K, &S, &off)) { c->b = anf_tree(e->b); c->c = anf_tree(e->c); return c; } }
    c->b = anf_region(e->b, 1); c->c = anf_region(e->c, 1); return c;
  case E_MATCH: {
    Expr *sc = (Expr *)e->a, *l = NULL;
    c = anf_copy(e);
    if (sc->op == E_PARAM || sc->op == E_CONST || bound(sc) || (sc->op == E_FIELD && (sc->a->op == E_PARAM || bound(sc->a))))
      c->a = anf_tree(sc);                           /* (a field read is a name already: borrowed, or the arm's own) */
    else {                                           /* (the scrutinee named, for the arms' fields) */
      l = anf_let(sc); l->a = anf_tree(sc);
      sc->var = 0; sc->vscope = fscope; sc->bind = l;
      c->a = anf_var(l);
    }
    c->args = A(sizeof(Expr *) * (size_t)(e->nargs ? e->nargs : 1));
    for (int i = 0; i < e->nargs; i++) c->args[i] = anf_region(e->args[i], 1);
    if (l) { sc->var = -1; sc->bind = NULL; l->b = c; return l; }
    return c; }
  default:
    c = anf_copy(e);
    c->a = anf_tree(e->a); c->b = anf_tree(e->b);
    if (e->op != E_CTOR) c->c = anf_tree(e->c); else c->c = NULL;
    if (e->nargs && e->args) { c->args = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) c->args[i] = anf_tree(e->args[i]); }
    return c;
  }
}
static void ex_dump(const Expr *e, int d) {         /* (LIN_FN_DEBUG=4: a tree, for reading) */
  static const char *nm[] = { "CONST","PARAM","BIN","IF","CALL","FOP","CTOR","MATCH","FIELD","VOP","LET","VAR","DUP","DROP","AFTER","SPEC" };
  if (!e) { fprintf(stderr, "%*s-\n", d * 2, ""); return; }
  fprintf(stderr, "%*s%s k%" PRId64 "", d * 2, "", e->op >= 0 && e->op <= E_SPEC ? nm[e->op] : "?", e->k);
  if (e->op == E_PARAM) fprintf(stderr, " f%d", e->nargs);
  if (e->op == E_CTOR && e->ci) fprintf(stderr, " %s", e->ci->name);
  if (e->op == E_DROP || e->op == E_AFTER) { fprintf(stderr, " ["); for (const struct Drop *q = e->drops; q; q = q->next) { if (!q->p) fprintf(stderr, " tok%d", -2 - q->fn); else fprintf(stderr, " %s%" PRId64 "", q->p->op == E_PARAM ? "p" : q->p->op == E_VAR ? "w" : "fld", q->p->k); } fprintf(stderr, " ]"); }
  if (e->op == E_SPEC && e->k >= 0) fprintf(stderr, " tok%" PRId64 "", e->k);
  if (e->op == E_CTOR && e->tok) fprintf(stderr, " in tok%d", e->tok - 1);
  fprintf(stderr, "\n");
  if (e->op == E_VAR) return;
  if (e->a) ex_dump(e->a, d + 1);
  if (e->b) ex_dump(e->b, d + 1);
  if (e->c && e->op != E_CTOR) ex_dump(e->c, d + 1);
  for (int i = 0; i < e->nargs && e->args; i++) ex_dump(e->args[i], d + 1);
}
static void plistn(Buf *b, int typed, int n) { for (int i = 0; i < n; i++) put(b, typed ? "%slong p%d" : "%sp%d", i ? ", " : "", i); }
static void plist(Buf *b, int typed) { plistn(b, typed, arity); }
static int emit_op(Buf *b, int64_t k, const char *x, const char *y) {
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
  if (k >= LIN_OP_EQ && k <= LIN_OP_GEQ) put(b, "(int64_t)(%s %s %s)", x, fn[k], y);
  else if (unary) put(b, "%s(%s)", fn[k], x);
  else put(b, "%s(%s, %s)", fn[k], x, y);
  return 1;
}
/* A GROUP of operands evaluated at once: every one but the last that contains a call runs on a new thread
   (while `d < dmax`), the last runs here, and the rest are plain.  Writes "({ ...;" -- the caller writes the
   use of names[i] and closes it with "; })". */
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget);
/* Operands run side by side are each written as a function of the PARAMETERS: a value they share -- a node
   both reach, or one the enclosing code already holds in a local -- would be computed again inside each.  That
   is the opposite of what sharing is for (`(fdiv (dot u v) (dot v v))` built `v` on both threads), so such
   operands are evaluated in turn, the shared value once. */
/* (A value the enclosing code already holds in a local is no conflict: it is computed, and each operand's task
   is handed it -- see par_group.) */
static int ps_walk(const Expr *e, unsigned char *mark, int who) {
  if (!e || e->op == E_PARAM || e->op == E_CONST) return 0;
  if (mark[e->id] == who) return 0;
  if (mark[e->id] && !bound(e) && has_call(e)) return 1;
  mark[e->id] = (unsigned char)who;
  if (bound(e)) return 0;
  if (ps_walk(e->a, mark, who) || ps_walk(e->b, mark, who) || (e->op != E_CTOR && ps_walk(e->c, mark, who))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (ps_walk(e->args[i], mark, who)) return 1;
  return 0;
}
static int par_shares(const Expr **xs, int n) {
  unsigned char *mark = calloc((size_t)eid + 1, 1); int r = 0;
  for (int i = 0; i < n && !r; i++) r = ps_walk(xs[i], mark, i + 1);
  free(mark); return r;
}
/* WORTH A THREAD: inside a function's parallel copy, an operand that calls the function again (the tree of
   calls is what spreads); in the ENTRY -- the expression the program observes, run once -- any operand that runs
   a loop, a call of one of the unit's recursive functions.  Independent loops in one expression (seven maps
   built from one sequence, or two sums) run side by side. */
static int entry_np;   /* the entry's parameters: its numeric arguments */
static int runs_loop(const Expr *e, unsigned char *seen) {   /* a call not yet made: one a local already holds is done */
  if (!e || e->op == E_PARAM || e->op == E_CONST || bound(e) || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_CALL) return 1;
  if (runs_loop(e->a, seen) || runs_loop(e->b, seen) || (e->op != E_CTOR && runs_loop(e->c, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (runs_loop(e->args[i], seen)) return 1;
  return 0;
}
static int heavy(const Expr *e) {
  if (emitting != -1) return has_self(e);
  if (!has_call(e)) return 0;
  unsigned char *seen = calloc((size_t)eid + 1, 1); int r = runs_loop(e, seen); free(seen); return r;
}
static int site_np(void) { return emitting == -1 ? entry_np : arity; }
/* The locals an operand reads: what the enclosing code holds that the operand's task is handed. */
static void captures(const Expr *e, unsigned char *seen, const Expr ***out, int *n) {
  if (!e || e->op == E_PARAM || e->op == E_CONST || seen[e->id]) return;
  seen[e->id] = 1;
  if (bound(e)) { *out = realloc(*out, sizeof **out * (size_t)(*n + 1)); (*out)[(*n)++] = e; return; }
  captures(e->a, seen, out, n); captures(e->b, seen, out, n); if (e->op != E_CTOR) captures(e->c, seen, out, n);
  for (int i = 0; i < e->nargs && e->args; i++) captures(e->args[i], seen, out, n);
}
/* (counted) WHAT A THREAD IS HANDED is marked shared first (see gen_data_fns): the function that marks a value of
   shape s, or -1 -- a number needs none, and a value whose shape is not known cannot be marked, so its unit counts
   atomically instead (rc_mt) */
static int rc_mt; static int rc_is_pure(int g, int k);
/* (how a value handed to threads is marked: FROZEN -- what tasks all read, freed with the unit -- or, for a list a
   parallel map splits among them, SHARED: counted atomically, and freed as it is consumed) */
static const char *rc_mark = "freeze";
static int drop_fn(Shape sh); static Shape shape_of(const Expr *e);
static int rc_share_fn(Shape s) {
  if (s.k == 0 || s.k == 1 || s.k == 3) return -1;   /* (k 0: nothing is known of it -- no count is taken of it anywhere) */
  if (s.k == 5 && s.dt) return drop_fn(s);
  rc_mt = 1; return -1;
}
static int reads_p_r(const Expr *e, int f, int64_t k, unsigned char *seen) {
  if (!e) return 0;
  if (e->op == E_PARAM) return e->nargs == f && e->k == k;
  if (seen[e->id]) return 0;
  seen[e->id] = 1;
  if (reads_p_r(e->a, f, k, seen) || reads_p_r(e->b, f, k, seen) || reads_p_r(e->c, f, k, seen)) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (reads_p_r(e->args[i], f, k, seen)) return 1;
  return 0;
}
static int reads_p(const Expr *e, int f, int64_t k) { unsigned char *seen = calloc((size_t)eid + 1, 1); int r = reads_p_r(e, f, k, seen); free(seen); return r; }
/* the shares of f's data parameters (named p<k>, or `<pre>[<k>]`) that x reads -- all of them when x is NULL */
static void rc_share_params(Buf *b, int f, const Expr *x, const char *arr, const char *idx) {
  if (f < 0 || f >= nfun || !funs[f].pnode) return;
  for (int k = 0; k < funs[f].arity; k++) {
    if (!funs[f].pnode[k] || (x && !reads_p(x, f, k)) || rc_is_pure(f, k)) continue;   /* (no count of it is ever taken) */
    int sf = rc_share_fn(shape_of(funs[f].pnode[k])); if (sf < 0) continue;
    if (arr) put(b, "lin_%s%d(%s[%s%d]); ", rc_mark, sf, arr, idx, k); else put(b, "lin_%s%d(p%d); ", rc_mark, sf, k);
  }
}
/* A TASK: x on a new thread (while `d < dmax`), as a function of the parameters and the locals it reads.
   Writes the start to b; `call` gets the same computation made here, for when no thread was started.
   Returns the site's number: the join is `sp<k>_ ? (pthread_join(t<k>_, 0), LIN_JOINED, s<k>_.r) : <call>`. */
static int fork_open(Buf *b, Buf *pre, const Expr *x, int budget, Buf *call, int *ok) {
  int np = site_np(), k = nsite++;
  const Expr **cap = NULL; int nc = 0;
  { unsigned char *seen = calloc((size_t)eid + 1, 1); captures(x, seen, &cap, &nc); free(seen); }
  Buf sb = nbuf(512);
  put(&sb, "static int64_t site%d(", k); plistn(&sb, 1, np);
  for (int c = 0; c < nc; c++) put(&sb, "%slong v%d", np || c ? ", " : "", cap[c]->var);
  put(&sb, "%sint d) { return ", np || nc ? ", " : "");
  *ok = emit_region(&sb, pre, x, 1, budget - 1);   /* (the same scope: the locals it reads are its parameters) */
  put(&sb, "; }\ntypedef struct { int64_t p[%d]; int64_t v[%d]; int d; int64_t r; } S%d;\n", np + 1, nc + 1, k);
  put(&sb, "static void *run%d(void *v) { S%d *s = v; LIN_TASK_START((size_t)256 << 20); s->r = site%d(", k, k, k);
  for (int j = 0; j < np; j++) put(&sb, "s->p[%d], ", j);
  for (int c = 0; c < nc; c++) put(&sb, "s->v[%d], ", c);
  put(&sb, "s->d); return 0; }\n");
  put(pre, "%s", sb.s); free(sb.s);
  put(b, "S%d s%d_ = { {", k, k); plistn(b, 0, np); put(b, "%s}, {", np ? "" : "0");
  for (int c = 0; c < nc; c++) put(b, "%sv%d", c ? ", " : "", cap[c]->var);
  put(b, "%s}, d, 0 }; pthread_t t%d_; ", nc ? "" : "0", k);
  {                                     /* (counted: what both threads will read is marked shared first) */
    Buf sh = nbuf(64);
    if (emitting >= 0) rc_share_params(&sh, emitting, x, NULL, NULL);
    for (int c = 0; c < nc; c++) { int sf = rc_share_fn(shape_of(cap[c])); if (sf >= 0) put(&sh, "lin_freeze%d(v%d); ", sf, cap[c]->var); }
    if (sh.len) put(b, "if (d < dmax) { %s} ", sh.s);
    free(sh.s);
  }
  put(b, "int sp%d_ = d < dmax && !pthread_create(&t%d_, &attr, run%d, &s%d_); ", k, k, k, k);
  put(call, "site%d(", k); plistn(call, 0, np);
  for (int c = 0; c < nc; c++) put(call, "%sv%d", np || c ? ", " : "", cap[c]->var);
  put(call, "%sd)", np || nc ? ", " : "");
  free(cap);
  return k;
}
static int par_group(Buf *b, Buf *pre, const Expr **xs, int n, Buf *names, int budget) {
  int last = -1, ok = 1;
  for (int i = 0; i < n; i++) if (heavy(xs[i])) last = i;
  put(b, "({ ");
  int *site = calloc((size_t)n, sizeof *site);
  for (int i = 0; ok && i < n; i++) {
    site[i] = -1;
    if (!heavy(xs[i]) || i == last) continue;
    site[i] = fork_open(b, pre, xs[i], budget, &names[i], &ok);   /* (names[i]: the call, until the join is written) */
  }
  int self = nvar++;
  for (int i = 0; ok && i < n; i++) {             /* the last call-containing operand, on this thread */
    if (i != last) continue;
    put(b, "int64_t y%d_ = ", self); ok = emitx(b, pre, xs[i], 1, budget - 1); put(b, "; ");
  }
  for (int i = 0; ok && i < n; i++) {
    if (site[i] >= 0) {
      int k = site[i];
      put(b, "int64_t x%d_ = sp%d_ ? (pthread_join(t%d_, 0), LIN_JOINED, s%d_.r) : %s; ", k, k, k, k, names[i].s);
      names[i].len = 0; names[i].s[0] = 0;
      put(&names[i], "x%d_", k);
    } else {
      names[i].len = 0; names[i].s[0] = 0;
      if (i == last) put(&names[i], "y%d_", self);
      else ok = emitx(&names[i], pre, xs[i], 1, budget - 1);
    }
  }
  free(site);
  return ok;
}
/* LAMBDA LIFTING.  A function the unit specialised to a closure reads what the closure captured -- often a parameter
   of the function that made it (`(smap (\x (mul x k)) s)` inside a loop over k).  Such a function takes those
   outer parameters as EXTRA C parameters, and every call passes them on: what a function reads from outside, its
   callers read too, unless it is their own.  (h, k): parameter k of function h, h = -1 the entry's. */
typedef struct { int h; int64_t k; } FV;
static FV **fvs; static int *nfv, lifted;
static int fv_has(int f, int h, int64_t k) { for (int i = 0; i < nfv[f]; i++) if (fvs[f][i].h == h && fvs[f][i].k == k) return 1; return 0; }
static int fv_add(int f, int h, int64_t k) {
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
  for (int i = 0; i < nfv[f]; i++) put(b, typed ? "%slong l%d_%" PRId64 "" : "%sl%d_%" PRId64 "", (lead || i) ? ", " : "", fvs[f][i].h + 1, fvs[f][i].k);
}
/* INDEXED FIELDS.  A datatype with many fields of one kind is how a program says "an array of k slots" in pure Lin
   (std/array.lin's trie nodes): choosing slot k is a decision tree of comparisons, and replacing it is one
   conditional per field.  When the tree provably picks field k+off for every value k can take (k is masked,
   so its range is known), that is ONE indexed load; and a constructor whose every field j is
   `k == j+off ? f(field j) : field j`, with f the same for all j, is ONE indexed read-modify-write. */
static int key_hi(const Expr *k, int64_t *hi) {
  while (k->op == E_VAR && k->bind && k->bind->a) k = k->bind->a;   /* (a named key: its value) */
  if (k->op != E_BIN || k->k != LIN_OP_BAND) return 0;
  const Expr *m = k->b->op == E_CONST ? k->b : k->a->op == E_CONST ? k->a : NULL;
  int64_t most = 0; const LinCtor *c;                  /* (no constructor has more slots than the widest declared) */
  for (int64_t id = 1; (c = lin_ctor_info(id)); id++) if (c->k > most) most = c->k;
  if (!m || m->k <= 0 || m->k >= most || (m->k & (m->k + 1))) return 0;
  *hi = m->k; return 1;
}
static int cmp_int(int64_t code, int64_t x, int64_t y) {
  switch (code) { case LIN_OP_EQ: return x == y; case LIN_OP_LT: return x < y; case LIN_OP_LEQ: return x <= y;
                  case LIN_OP_GT: return x > y; case LIN_OP_GEQ: return x >= y; }
  return -1;
}
static const Expr *dt_key(const Expr *e) {           /* the compared expression at the root of a decision tree */
  if (e->op != E_IF || e->a->op != E_BIN || cmp_int(e->a->k, 0, 0) < 0) return NULL;
  return e->a->b->op == E_CONST ? e->a->a : e->a->a->op == E_CONST ? e->a->b : NULL;
}
static const Expr *dt_leaf(const Expr *e, const Expr *K, int64_t v) {
  while (e->op == E_IF) {
    const Expr *c = e->a; int r;
    if (c->op != E_BIN) return NULL;
    if (c->a == K && c->b->op == E_CONST) r = cmp_int(c->k, v, c->b->k);
    else if (c->b == K && c->a->op == E_CONST) r = cmp_int(c->k, c->a->k, v);
    else return NULL;
    if (r < 0) return NULL;
    e = r ? e->b : e->c;
  }
  return e;
}
/* Is e the selection of field K+off of one block?  Writes the block and off. */
static int indexed_pick(const Expr *e, const Expr **K, const Expr **S, int64_t *off) {
  int64_t hi; const Expr *k = dt_key(e);
  if (!k || !key_hi(k, &hi)) return 0;
  const Expr *base = NULL; const LinCtor *ci = NULL; int64_t o = 0; int untag = 0;
  for (int64_t v = 0; v <= hi; v++) {
    const Expr *l = dt_leaf(e, k, v);
    if (!l || l->op != E_FIELD) return 0;
    if (!v) { base = l->a; ci = l->ci; o = l->k; untag = l->untag; }
    else if (l->a != base || l->ci != ci || l->untag != untag || l->k != v + o) return 0;
  }
  if (!ci || hi + o >= ci->k) return 0;
  *K = k; *S = base; *off = o + !untag; return 1;
}
static int mr_same_base(const Expr *x, const Expr *y); static const Expr **mr_tokb;
/* a[field 0 of base] == b[field j of base]: the same expression of a different slot */
static int eq_ix(const Expr *a, const Expr *b, const Expr *base, int64_t j, int depth) {
  if (a->op == E_FIELD && a->k == 0 && mr_same_base(a->a, base)) return b->op == E_FIELD && b->k == j && mr_same_base(b->a, base);
  if (b->op == E_FIELD && b->k == j && mr_same_base(b->a, base)) return 0;
  if (a->op == E_VAR || b->op == E_VAR) return a->op == b->op && a->bind == b->bind;
  if (depth > eid || a->op != b->op || a->k != b->k || a->kind != b->kind || a->nargs != b->nargs || a->ci != b->ci || a->untag != b->untag || a->tok != b->tok) return 0;
  if (a->op == E_LET || a->op == E_SPEC || a->op == E_DROP || a->op == E_AFTER || a->drops || b->drops) return 0;   /* (names and counts of their own: not one shape) */
  if (!a->a != !b->a || !a->b != !b->b || !a->c != !b->c || !a->args != !b->args) return 0;
  if (a->a && !eq_ix(a->a, b->a, base, j, depth + 1)) return 0;
  if (a->b && !eq_ix(a->b, b->b, base, j, depth + 1)) return 0;
  if (a->c && a->op != E_CTOR && !eq_ix(a->c, b->c, base, j, depth + 1)) return 0;
  for (int i = 0; a->args && i < a->nargs; i++) if (!eq_ix(a->args[i], b->args[i], base, j, depth + 1)) return 0;
  return 1;
}
/* A block rebuilt in the block an arm took apart (REUSE), every field j `k == j ? f(field j) : field j` with one
   f: the update of ONE slot.  Writes k and f's instance at slot 0 (whose field 0 stands for slot k). */
static int ix_update(const Expr *e, const Expr **K, const Expr **x0) {
  if (e->op != E_CTOR || !e->tok || e->nargs < 2 || !e->args) return 0;
  const Expr *base = mr_tokb[e->tok - 1], *k = NULL;
  for (int j = 0; j < e->nargs; j++) {
    const Expr *a = e->args[j];
    if (a->op != E_IF || a->a->op != E_BIN || a->a->k != LIN_OP_EQ) return 0;
    const Expr *kk = a->a->b->op == E_CONST ? a->a->a : a->a->a->op == E_CONST ? a->a->b : NULL;
    int64_t cv = a->a->b->op == E_CONST ? a->a->b->k : a->a->a->k;
    if (!kk || cv != j || (j && kk != k)) return 0;
    k = kk;
    if (a->c->op != E_FIELD || a->c->k != j || !mr_same_base(a->c->a, base)) return 0;
    if (j && !eq_ix(e->args[0]->b, a->b, base, j, 0)) return 0;
  }
  int64_t hi; if (!key_hi(k, &hi) || hi != e->nargs - 1) return 0;
  *K = k; *x0 = e->args[0]->b; return 1;
}
static int refs_field(const Expr *e, const Expr *base, int but0) {   /* reads a field of base (but0: other than 0)? */
  if (!e) return 0;
  if (e->op == E_FIELD && mr_same_base(e->a, base) && !(but0 && e->k == 0)) return 1;
  if (refs_field(e->a, base, but0) || refs_field(e->b, base, but0) || (e->op != E_CTOR && refs_field(e->c, base, but0))) return 1;
  for (int i = 0; e->args && i < e->nargs; i++) if (refs_field(e->args[i], base, but0)) return 1;
  for (const struct Drop *d = e->drops; d; d = d->next) if (d->fn > -2 && refs_field(d->p, base, but0)) return 1;
  return 0;
}
/* An arm whose whole work is ONE slot update of the block it takes apart (ix_update): it needs no field but that
   slot, so the block is kept -- or, shared, copied -- and only the slot is read. */
static int spec_ix_only(const Expr *sp) {
  const Expr *x = sp->b, *K, *x0, *base = sp->a;
  for (; x->op == E_LET || x->op == E_DROP; x = x->b) {   /* (names and drops before it that need no field) */
    if (x->op == E_LET && refs_field(x->a, base, 0)) return 0;
    for (const struct Drop *d = x->op == E_DROP ? x->drops : NULL; d; d = d->next) if (d->fn <= -2 || refs_field(d->p, base, 0)) return 0;
  }
  return ix_update(x, &K, &x0) && x->tok - 1 == sp->k && !refs_field(x0, base, 1) && !refs_field(K, base, 0);
}
static unsigned *ct_gen, ct_g; static unsigned char *ct_val; static int ct_cap;   /* one answer per node per question */
static int contains_r(const Expr *e, const Expr *x) {
  if (e == x) return 1;
  if (e->id < ct_cap && ct_gen[e->id] == ct_g) return ct_val[e->id];
  int r = (e->a && contains_r(e->a, x)) || (e->b && contains_r(e->b, x)) || (e->c && contains_r(e->c, x));
  for (int i = 0; !r && i < e->nargs && e->args; i++) r = contains_r(e->args[i], x);
  if (e->id < ct_cap) { ct_gen[e->id] = ct_g; ct_val[e->id] = (unsigned char)r; }
  return r;
}
static int contains(const Expr *e, const Expr *x, int depth) {
  (void)depth;
  if (ct_cap < eid) { int c = eid * 2 + 64; ct_gen = realloc(ct_gen, sizeof *ct_gen * (size_t)c); ct_val = realloc(ct_val, (size_t)c); memset(ct_gen + ct_cap, 0, sizeof *ct_gen * (size_t)(c - ct_cap)); ct_cap = c; }
  ct_g++;
  return contains_r(e, x);
}
static int field_live(const LinCtor *ci, int j);
static int indexed_pick(const Expr *e, const Expr **K, const Expr **S, int64_t *off);
static int call_fv(Buf *b, int64_t k) {                 /* the callee's lifted parameters: ours, or passed on */
  for (int i = 0; k < lifted && i < nfv[k]; i++) {
    const FV *v = &fvs[k][i];
    if (v->h == emitting) put(b, ", p%" PRId64 "", v->k);
    else if (emitting >= 0 && emitting < lifted && fv_has(emitting, v->h, v->k)) put(b, ", l%d_%" PRId64 "", v->h + 1, v->k);
    else { DBG("declined: a lifted parameter with no source (f%d calls f%" PRId64 ", which reads f%d's parameter %" PRId64 ")\n", emitting, k, v->h, v->k); return 0; }
  }
  return 1;
}
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static int drop_fn(Shape sh);
static int rc_fdrop(const LinCtor *ci, int j, Shape vs);
/* occurrences in e's TREE (capped at 2) of: x itself (tc_mode 0), the field tc_k of tc_base (1), or tc_base other
   than as the block a field is read from (2) */
/* (counted) a slot rebuilt by a call told to write it: the old value must be handed to that call -- moved, once, to
   a parameter it owns -- for nothing else will release it: the call writes over it */
static int rc_borrowed(int g, int k);
static int emit_arg(Buf *b, Buf *pre, const Expr *call, int i, int par, int budget) { return emitx(b, pre, call->args[i], par, budget); }
/* A LOOP WHOSE STEPS ARE INDEPENDENT.  f(.., acc) = if c then acc else f(next.., A(acc, G)), where neither the
   condition nor the next state reads acc, and G -- a call of another loop -- reads only the state: every step's
   G can be computed before any is folded in.  fannkuch's `each` is one (G: the permutations under one
   rotation, A: joining their counts), and its G's are most of the program.  The parallel form, fN_pl, walks
   the states first (the loop's own cheap part), computes every G on worker threads, and folds them into acc
   IN ORDER -- the same fold the loop makes, so the answer is the loop's whatever A is.  It is used where the
   caller is itself running in parallel (the entry, a parallel copy), with the depth `d` bounding the nesting. */
typedef struct { int acc, base_then; const Expr *cond, *step, *G, *Gname, *base; const Expr **chain; int nchain; } PL;   /* Gname: G's name, when a let binds it (EXPLICIT BINDING) */
static PL *plinfo; static unsigned char *pl_done; static int plpar, pl_unit;   /* pl_unit: writing a data unit (its runtime has the threads) */
static int pl_ment(const Expr *e, int f, int k, unsigned char *seen) {   /* does e read parameter k of f? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_PARAM) return e->nargs == f && e->k == k;
  if (e->op == E_CALL && e->k >= 0 && e->k < lifted && fv_has((int)e->k, f, k)) return 1;   /* (read by the callee, lifted) */
  if (pl_ment(e->a, f, k, seen) || pl_ment(e->b, f, k, seen) || (e->op != E_CTOR && pl_ment(e->c, f, k, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (pl_ment(e->args[i], f, k, seen)) return 1;
  return 0;
}
static int pl_m(const Expr *e, int f, int k) { unsigned char *seen = calloc((size_t)eid + 1, 1); int r = pl_ment(e, f, k, seen); free(seen); return r; }
static int pl_params(const Expr *e, int f, unsigned char *seen) {   /* does e read any parameter of f? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_PARAM) return e->nargs == f;
  if (e->op == E_CALL && e->k >= 0 && e->k < lifted) for (int i = 0; i < nfv[e->k]; i++) if (fvs[e->k][i].h == f) return 1;
  if (pl_params(e->a, f, seen) || pl_params(e->b, f, seen) || (e->op != E_CTOR && pl_params(e->c, f, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (pl_params(e->args[i], f, seen)) return 1;
  return 0;
}
/* A's parts that do not read acc: one call G, or values that read no parameter at all */
static int pl_split(const Expr *e, int f, int acc, const Expr **G, unsigned char *seen) {
  if (!e || seen[e->id]) return 1;
  seen[e->id] = 1;
  if (!pl_m(e, f, acc)) {
    if (e->op == E_CALL && e->k != f) { if (*G && *G != e) return 0; *G = e; return 1; }
    unsigned char *s2 = calloc((size_t)eid + 1, 1); int r = !pl_params(e, f, s2); free(s2);
    if (r) return 1;                                 /* (a constant) */
    if (e->op == E_PARAM || e->op == E_CALL) return 0;   /* (the state, read outside G) */
  }
  if (!pl_split(e->a, f, acc, G, seen) || !pl_split(e->b, f, acc, G, seen) || (e->op != E_CTOR && !pl_split(e->c, f, acc, G, seen))) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!pl_split(e->args[i], f, acc, G, seen)) return 0;
  return 1;
}
static int pl_has(const Expr *e, const Expr *x, unsigned char *seen) {   /* is x in e (a name, a node)? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e == x || (e->op == E_VAR && x->op == E_VAR && e->bind == x->bind)) return 1;
  if (pl_has(e->a, x, seen) || pl_has(e->b, x, seen) || (e->op != E_CTOR && pl_has(e->c, x, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (pl_has(e->args[i], x, seen)) return 1;
  for (const struct Drop *d = e->drops; d; d = d->next) if (d->fn > -2 && pl_has(d->p, x, seen)) return 1;
  return 0;
}
static int pl_in(const Expr *e, const Expr *x, const Expr *skip) {
  unsigned char *seen = calloc((size_t)eid + 1, 1); if (skip) seen[skip->id] = 1;
  int r = pl_has(e, x, seen); free(seen); return r;
}
static int pl_mskip(const Expr *e, int f, int k, const Expr *skip) {   /* pl_m, not looking inside skip */
  unsigned char *seen = calloc((size_t)eid + 1, 1); if (skip) seen[skip->id] = 1;
  int r = pl_ment(e, f, k, seen); free(seen); return r;
}
/* (with names and counts made explicit: the recursive side is a chain of lets and drops ending in the step; G is
   one let's call, or the one call in A; the base is acc after the drops of the rest of the state.  The loop that
   walks the states evaluates the chain IN ORDER and keeps G's ARGUMENTS -- with whatever counts they took --
   so what the threads run is exactly the calls the loop would have made) */
static int pl_ok(int f) {
  if (!plinfo || f < 0 || f >= nfun || (hasd && hasd[f]) || nfv[f] || !funs[f].body) return 0;
  if (plinfo[f].acc >= 0) return plinfo[f].acc > 0 || plinfo[f].G;   /* (decided: acc 0 with G set is acc 0) */
  plinfo[f].acc = 0; plinfo[f].G = NULL;
  const Expr *B = funs[f].body;
  if (B->op != E_IF) return 0;
  for (int side = 0; side < 2; side++) {
    const Expr *base = side ? B->c : B->b, *rec = side ? B->b : B->c, *bp = base;
    int bad = 0;
    for (; bp->op == E_DROP; bp = bp->b) for (const struct Drop *d = bp->drops; d; d = d->next) if (d->fn <= -2) bad = 1;
    if (bad || bp->op != E_PARAM || bp->nargs != f) continue;
    int acc = (int)bp->k, nc = 0;
    const Expr **chain = malloc(sizeof *chain * 8); int cap = 8;
    const Expr *x = rec;
    for (; x->op == E_LET || x->op == E_DROP; x = x->b) {
      if (x->op == E_DROP) for (const struct Drop *d = x->drops; d; d = d->next) if (d->fn <= -2) bad = 1;
      if (nc == cap) chain = realloc(chain, sizeof *chain * (size_t)(cap *= 2));
      chain[nc++] = x;
    }
    const Expr *step = x;
    if (bad || step->op != E_CALL || step->k != f || step->nargs != funs[f].arity || pl_m(B->a, f, acc)) { free(chain); continue; }
    for (const struct Drop *d = base->op == E_DROP ? base->drops : NULL; d; d = d->next) if (pl_m(d->p, f, acc)) bad = 1;
    const Expr *A = step->args[acc], *G = NULL, *Gname = NULL;
    for (int i = 0; i < nc && !G; i++)                /* G named by a let, read by A */
      if (chain[i]->op == E_LET && chain[i]->a->op == E_CALL && chain[i]->a->k != f && pl_in(A, chain[i]->bind, NULL)) { G = chain[i]->a; Gname = chain[i]->bind; }
    if (!G) { unsigned char *seen = calloc((size_t)eid + 1, 1); if (!pl_split(A, f, acc, &G, seen)) G = NULL; free(seen); }
    if (!G || G->op != E_CALL || G->k < 0 || G->k >= nfun || G->k == f || (G->k < lifted && nfv[G->k]) || pl_m(G, f, acc) || (Gname && pl_in(G, Gname, NULL))) bad = 1;
    int after = 0;
    for (int i = 0; i < nc && !bad; i++) {           /* the chain: no acc; after G, not G's value */
      const Expr *c = chain[i];
      if (c->op == E_LET && c->bind == Gname) { after = 1; continue; }
      for (const struct Drop *d = c->op == E_DROP ? c->drops : NULL; d; d = d->next) if (pl_m(d->p, f, acc)) bad = 1;
      if (c->op == E_LET && pl_m(c->a, f, acc)) bad = 1;
      if (after && Gname && c->op == E_LET && pl_in(c->a, Gname, NULL)) bad = 1;
      if (c->op == E_LET && pl_in(A, c->bind, G)) bad = 1;   /* (A, folded later, reads only acc and G) */
    }
    for (int k = 0; k < step->nargs && !bad; k++) {
      if (k == acc) continue;
      if (pl_m(step->args[k], f, acc) || (Gname && pl_in(step->args[k], Gname, NULL)) || pl_in(step->args[k], G, NULL)) bad = 1;
      if (pl_mskip(A, f, k, G)) bad = 1;
    }
    if (bad) { free(chain); continue; }
    PL *L = &plinfo[f];
    L->acc = acc; L->base_then = !side; L->cond = B->a; L->step = step; L->G = G; L->Gname = Gname; L->base = base; L->chain = chain; L->nchain = nc;
    if (dbg) DBG("f%d folds independent steps: its calls of f%" PRId64 " run in parallel\n", f, G->k);
    return 1;
  }
  return 0;
}
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static int pl_emit(Buf *pre, int f, int budget) {    /* fN_pl, written once per unit into `pre` */
  if (pl_done[f]) return 1;
  pl_done[f] = 1;
  const PL *L = &plinfo[f]; int ar = funs[f].arity, ok = 1, se = emitting; emitting = f;
  const Expr *G = L->G; int na = G->nargs;
  Buf g = nbuf(1024), w = nbuf(2048);
  /* G, as a function of its arguments (their nodes stand for them while it is written) */
  put(&g, "static int64_t f%d_g(", f); for (int i = 0; i < na; i++) put(&g, "int64_t a%d, ", i); put(&g, "int d) { return ");
  fscope++;
  { int a0 = nvar; nvar += na; int *sv = malloc(sizeof *sv * (size_t)(2 * na + 1));
    for (int i = 0; i < na; i++) { Expr *a = (Expr *)G->args[i]; sv[2 * i] = a->var; sv[2 * i + 1] = a->vscope; a->var = a0 + i; a->vscope = fscope; }
    put(&g, "({ "); for (int i = 0; i < na; i++) put(&g, "int64_t v%d = a%d; ", a0 + i, i);
    ok = emitx(&g, pre, G, 1, budget - 1); put(&g, "; })");
    for (int i = 0; i < na; i++) { Expr *a = (Expr *)G->args[i]; a->var = sv[2 * i]; a->vscope = sv[2 * i + 1]; }
    free(sv); }
  put(&g, "; }\n");
  put(&g, "typedef struct { const int64_t *st; int64_t *g; int64_t n, next; int d; } PL%d;\n", f);
  put(&g, "static void *plrun%d(void *v) { PL%d *s = v; LIN_TASK_START((size_t)256 << 20);\n", f, f);
  put(&g, "  for (int64_t i; (i = __sync_fetch_and_add(&s->next, 1)) < s->n; ) s->g[i] = f%d_g(", f);
  for (int k = 0; k < na; k++) put(&g, "s->st[i * %d + %d], ", na ? na : 1, k);
  put(&g, "s->d + 1);\n  return 0; }\n");
  put(pre, "%s", g.s); free(g.s);
  int NA = na ? na : 1;
  put(&w, "static int lin_threads_; static int lin_live;\n");
  put(&w, "static int64_t f%d_pl(", f); plistn(&w, 1, ar); put(&w, ", int d) {\n");
  put(&w, "  if (d >= dmax) return f%d(", f); plistn(&w, 0, ar); put(&w, ");\n");
  put(&w, "  int64_t cap = 16, n = 0; int64_t *st = malloc(sizeof(int64_t) * (size_t)cap * %d);\n", NA);
  put(&w, "  { int64_t "); for (int k = 0; k < ar; k++) put(&w, "%sq%d = p%d", k ? ", " : "", k, k); put(&w, ";\n    for (;;) {\n      int64_t ");
  for (int k = 0; k < ar; k++) put(&w, "%sp%d = q%d", k ? ", " : "", k, k); put(&w, ";\n      if (%s(", L->base_then ? "" : "!");
  fscope++; ok = ok && emit_region(&w, pre, L->cond, 0, budget - 1); put(&w, ")) { ");
  for (const Expr *x = L->base; ok && x->op == E_DROP; x = x->b)   /* (the end: the rest of the state goes) */
    for (const struct Drop *d = x->drops; ok && d; d = d->next) { put(&w, "lin_drop%d(", d->fn); ok = emitx(&w, pre, d->p, 0, budget - 1); put(&w, "); "); }
  put(&w, "break; }\n");
  put(&w, "      if (n == cap) st = realloc(st, sizeof(int64_t) * (size_t)(cap *= 2) * %d);\n", NA);
  int *bound_v = malloc(sizeof *bound_v * (size_t)(L->nchain + 1)), gdone = 0;
  #define PL_GARGS() do { for (int i = 0; ok && i < na; i++) { put(&w, "      st[n * %d + %d] = ", NA, i); ok = emit_region(&w, pre, G->args[i], 0, budget - 1); put(&w, ";\n"); } gdone = 1; } while (0)
  for (int i = 0; ok && i < L->nchain; i++) {
    const Expr *c = L->chain[i];
    if (c->op == E_DROP) {
      for (const struct Drop *d = c->drops; ok && d; d = d->next) { put(&w, "      lin_drop%d(", d->fn); ok = emitx(&w, pre, d->p, 0, budget - 1); put(&w, ");\n"); }
      continue;
    }
    if (c->bind == L->Gname) { PL_GARGS(); continue; }
    int v = nvar++; put(&w, "      int64_t v%d = ", v); ok = ok && emitx(&w, pre, c->a, 0, budget - 1); put(&w, ";\n");
    c->bind->var = v; c->bind->vscope = fscope;
  }
  if (!gdone) PL_GARGS();
  #undef PL_GARGS
  put(&w, "      n++;\n");
  for (int k = 0; k < ar && ok; k++) {
    if (k == L->acc) continue;
    put(&w, "      int64_t n%d = ", k); ok = emitx(&w, pre, L->step->args[k], 0, budget - 1); put(&w, ";\n");
  }
  for (int i = 0; i < L->nchain; i++) if (L->chain[i]->op == E_LET) L->chain[i]->bind->var = -1;
  free(bound_v);
  put(&w, "      "); for (int k = 0; k < ar; k++) if (k != L->acc) put(&w, "q%d = n%d; ", k, k);
  put(&w, "\n    } }\n");
  /* every G at once: the threads and this one take states in turn */
  put(&w, "  int64_t *g = malloc(sizeof(int64_t) * (size_t)(n + 1));\n");
  put(&w, "  PL%d s = { st, g, n, 0, d }; int T = lin_threads_ > 0 ? lin_threads_ : 1; pthread_t t[T]; int nt = 0;\n", f);
  {                                     /* (counted: what the threads are given, frozen -- they may share blocks, and no count of them is taken again) */
    Buf sh = nbuf(64);
    for (int i = 0; i < na; i++) { const Expr *ga = G->args[i]; while (ga->op == E_DUP || ga->op == E_AFTER) ga = ga->a; int sf = rc_share_fn(shape_of(ga)); if (sf >= 0) { put(&sh, "lin_%s%d(st[i * %d + %d]); ", rc_mark, sf, NA, i); } }
    if (sh.len) put(&w, "  if (T > 1 && n > 1) for (int64_t i = 0; i < n; i++) { %s}\n", sh.s);
    free(sh.s);
  }
  put(&w, "  for (int k = 1; k < T && k < n; k++) { if (__sync_add_and_fetch(&lin_live, 1) > 2 * T) { __sync_sub_and_fetch(&lin_live, 1); break; }\n");
  put(&w, "    if (pthread_create(&t[nt], &attr, plrun%d, &s)) { __sync_sub_and_fetch(&lin_live, 1); break; } nt++; }\n", f);
  put(&w, "  for (int64_t i; (i = __sync_fetch_and_add(&s.next, 1)) < n; ) g[i] = f%d_g(", f);
  for (int k = 0; k < na; k++) put(&w, "st[i * %d + %d], ", NA, k);
  put(&w, "d + 1);\n  for (int k = 0; k < nt; k++) { pthread_join(t[k], 0); __sync_sub_and_fetch(&lin_live, 1); }\n  (void)LIN_JOINED;\n");
  /* the fold, in order (A reads only acc and G) */
  int gv = nvar++;
  put(&w, "  int64_t acc = p%d;\n  for (int64_t i = 0; i < n; i++) {\n    int64_t p%d = acc; int64_t v%d = g[i];\n    acc = ", L->acc, L->acc, gv);
  fscope++; Expr *Gx = (Expr *)G; int sv = Gx->var, ss = Gx->vscope; Gx->var = gv; Gx->vscope = fscope;
  if (L->Gname) { ((Expr *)L->Gname)->var = gv; ((Expr *)L->Gname)->vscope = fscope; }
  ok = ok && emit_region(&w, pre, L->step->args[L->acc], 0, budget - 1);
  Gx->var = sv; Gx->vscope = ss; if (L->Gname) ((Expr *)L->Gname)->var = -1;
  put(&w, ";\n  }\n  free(st); free(g);\n  return acc;\n}\n");
  put(pre, "%s", w.s); free(w.s);
  emitting = se;
  return ok;
}
static Shape shape_of(const Expr *e);
static Shape **sh_fld; static int64_t sh_nctor;
static Shape field_shape(Shape **fld, int64_t nctor, const LinCtor *c, int64_t id, int j, Shape v);
static int64_t ctor_id(const LinCtor *c);
/* the drop function of field j of a block built by constructor ci, of value shape vs (-1: not data) */
static int rc_fdrop(const LinCtor *ci, int j, Shape vs) {
  if (!ci || !field_live(ci, j)) return -1;
  int64_t k = ctor_id(ci); if (k <= 0 || k > sh_nctor) return -1;
  Shape fs = field_shape(sh_fld, sh_nctor, ci, k, j, vs);
  return fs.k == 5 && fs.dt ? drop_fn(fs) : -1;
}
static const LinCtor *rc_arm_ci(const Expr *m, int i) {   /* the constructor of a match's arm i */
  if (!m->ci) return NULL;
  const LinCtor *c; for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == m->ci->dt && c->i == i) return c;
  return NULL;
}
static int rc_borrowed(int g, int k);
static int let_chain;   /* (the entry's let chain being written: its inner lets are plain) */
static void rf_pick(const Expr *y, ISet c, const int *ci, unsigned char *seen, const Expr ***fx, int *nf); static int rf_dep(const Expr *x, const int *ci, unsigned char *seen);
typedef struct { const Expr *base; int64_t k; int v; } EmFB;   /* (MEMORY) the fields an arm took apart, by local */
static int *mr_tokw; static const Expr **mr_tokb; static const Expr *dp_hole;
static EmFB *em_fb; static int em_nfb, em_cfb; static int ixu_always = -1;   /* (a token that is always there: spec_ix_only) */
static int mr_same_base(const Expr *x, const Expr *y);
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget);
/* (see ix_update) slot k of the reused block, given f(slot k): the rest stays where it is.  In tail position with
   f a call that takes a destination, the call writes the slot itself -- the loop of a trie update. */
static int emit_ixu(Buf *b, Buf *pre, const Expr *e, const Expr *K, const Expr *x0, int par, int budget, int tp) {
  int t = e->tok - 1, W = e->nargs + !e->untag, kv = nvar++, ov = nvar++, off = !e->untag;
  put(b, "({ int64_t v%d = ", kv); if (!emitx(b, pre, K, par, budget - 1)) return 0;
  if (t == ixu_always) put(b, "; int64_t *_o = t%d; int _r = 1; t%d = 0; ", t, t);   /* (see spec_ix_only) */
  else {
    put(b, "; int64_t *_o; int _r = t%d != 0; if (_r) { _o = t%d; t%d = 0; } else { _o = lin_alloc(%d); ", t, t, t, W);
    if (!e->untag) put(b, "_o[0] = %" PRId64 "L; ", e->k);
    for (int i = 0; i < e->nargs; i++) { put(b, "_o[%d] = ", i + off); if (!emitx(b, pre, e->args[i]->c, par, budget - 1)) return 0; put(b, "; "); }
    put(b, "} ");
  }
  put(b, "int64_t v%d = _o[v%d + %d]; ", ov, kv, off);
  if (em_nfb == em_cfb) em_fb = realloc(em_fb, sizeof *em_fb * (size_t)(em_cfb = em_cfb ? em_cfb * 2 : 16));
  em_fb[em_nfb++] = (EmFB){ e->args[0]->c->a, 0, ov };   /* (field 0 stands for slot k) */
  int ok = 1;
  if (tp && x0->op == E_CALL && hasd[x0->k] && !bound(x0)) {
    int a0 = nvar; nvar += x0->nargs;
    for (int i = 0; ok && i < x0->nargs; i++) { put(b, "int64_t v%d = ", a0 + i); ok = emit_arg(b, pre, x0, i, par, budget - 1); put(b, "; "); }
    em_nfb--;
    if (!ok) return 0;
    put(b, "LIN_PUT(dst, (int64_t)_o); f%" PRId64 "%s(&_o[v%d + %d]", x0->k, dp_name(x0->k), kv, off);
    for (int i = 0; i < x0->nargs; i++) put(b, ", v%d", a0 + i);
    if (!call_fv(b, x0->k)) return 0;
    put(b, "%s); })", dp_stop(x0->k)); return 1;
  }
  put(b, "int64_t _n = "); ok = emitx(b, pre, x0, par, budget - 1); em_nfb--;
  if (!ok) return 0;
  put(b, "; if (!_r || _n != v%d) _o[v%d + %d] = _n; %s(int64_t)_o%s; })", ov, kv, off, tp ? "LIN_PUT(dst, " : "", tp ? ")" : ""); return 1;
}
static int emit_fn_body(Buf *fb, Buf *pre, const Expr *body) { put(fb, "return "); return emit_region(fb, pre, body, 0, 4096); }
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  int tp = tailpos; tailpos = 0;
  if (budget <= 0) return 0;
  if ((e->op == E_DUP || e->op == E_AFTER || e->op == E_DROP) && bound(e)) { put(b, tp ? "LIN_SET(dst, v%d)" : "v%d", e->var); return 1; }   /* (a value standing for itself: pl_emit) */
  if (e->op == E_LET && par && emitting == -1 && !let_chain) {   /* (the entry's bindings: THE ENTRY'S LOOPS, STARTED EARLY) */
    int n = 0; const Expr *body = e;
    int cap = 8; const Expr **lets = malloc(sizeof *lets * (size_t)cap);
    while (body->op == E_LET) { if (n == cap) lets = realloc(lets, sizeof *lets * (size_t)(cap *= 2)); lets[n++] = body; body = body->b; }
    st_grow(); stamp += 2; count_uses(body);
    int *ci = malloc(sizeof *ci * (size_t)(eid + 1)); for (int i = 0; i <= eid; i++) ci[i] = -1;
    for (int i = 0; i < n; i++) ci[lets[i]->bind->id] = i;
    int lastheavy = -1; for (int i = 0; i < n; i++) if (has_call(lets[i]->a)) lastheavy = i;
    unsigned char *seen = calloc((size_t)eid + 1, 1); const Expr **fx = NULL; int na = 0;
    rf_pick(body, cert(body), ci, seen, &fx, &na);
    int *fpos = malloc(sizeof *fpos * (size_t)(na + 1)), nf = 0;
    for (int i = 0; i < na; i++) { memset(seen, 0, (size_t)eid + 1); int at = rf_dep(fx[i], ci, seen) + 1; if (at <= lastheavy) { fx[nf] = fx[i]; fpos[nf++] = at; } }
    free(seen); free(ci);
    int *fsite = calloc((size_t)(nf ? nf : 1), sizeof *fsite), ok = 1; Buf *fcall = calloc((size_t)(nf ? nf : 1), sizeof *fcall);
    put(b, "({ ");
    for (int i = 0; i <= n && ok; i++) {
      for (int f = 0; f < nf && ok; f++) if (fpos[f] == i) { fcall[f] = nbuf(64); fsite[f] = fork_open(b, pre, fx[f], budget, &fcall[f], &ok); }
      if (i == n) break;
      int k = nvar++; put(b, "int64_t v%d = ", k); ok = ok && emitx(b, pre, lets[i]->a, par, budget - 1); put(b, "; ");
      lets[i]->bind->var = k; lets[i]->bind->vscope = fscope;
    }
    for (int f = 0; f < nf && ok; f++) {
      int k = fsite[f], v = nvar++;
      put(b, "int64_t v%d = sp%d_ ? (pthread_join(t%d_, 0), LIN_JOINED, s%d_.r) : %s; ", v, k, k, k, fcall[f].s);
      ((Expr *)fx[f])->var = v; ((Expr *)fx[f])->vscope = fscope;
    }
    let_chain = 1; tailpos = tp; ok = ok && emitx(b, pre, body, par, budget - 1); tailpos = 0; let_chain = 0;
    put(b, "; })");
    for (int i = 0; i < n; i++) lets[i]->bind->var = -1;
    for (int f = 0; f < nf; f++) { ((Expr *)fx[f])->var = -1; free(fcall[f].s); }
    free(lets); free(fx); free(fpos); free(fsite); free(fcall);
    return ok;
  }
  if (e->op == E_LET) {                              /* (see EXPLICIT BINDING) the value, its name, the body */
    int k = nvar++; Expr *v = e->bind;
    put(b, "({ int64_t v%d = ", k); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "; ");
    v->var = k; v->vscope = fscope;
    tailpos = tp; int ok = emitx(b, pre, e->b, par, budget - 1); tailpos = 0;
    v->var = -1; put(b, "; })"); return ok;
  }
  if (e->op == E_VAR && !bound(e)) { DBG("declined: a name (w%" PRId64 ") out of its let's scope (writing f%d%s)\n", e->k, emitting, par ? ", in parallel" : ""); return 0; }   /* (never written: see EXPLICIT BINDING) */
  if (e->op == E_DUP) {                              /* (see MEMORY) */
    uses_data = 1; put(b, tp ? "LIN_SET(dst, lin_dup(" : "lin_dup("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, tp ? "))" : ")"); return 1;
  }
  if (e->op == E_DROP || e->op == E_AFTER) {
    uses_data = 1; put(b, "({ ");
    if (e->op == E_AFTER) { put(b, "int64_t r_ = "); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "; "); }
    for (const struct Drop *d = e->drops; d; d = d->next) {
      if (d->fn <= -2) { int t = -2 - d->fn; put(b, "if (t%d) lin_free(t%d, %d); ", t, t, mr_tokw[t]); continue; }   /* (see REUSE) */
      put(b, "lin_drop%d(", d->fn); if (!emitx(b, pre, d->p, par, budget - 1)) return 0; put(b, "); "); }
    if (e->op == E_AFTER) { put(b, tp ? "LIN_SET(dst, r_); })" : "r_; })"); return 1; }
    tailpos = tp; int ok = emitx(b, pre, e->b, par, budget - 1); tailpos = 0; put(b, "; })"); return ok;
  }
  if (e->op == E_SPEC) {                             /* (see MATCH ON A DYING VALUE, and REUSE) */
    const LinCtor *ac = e->ci; Shape ss = shape_of(e->a); int nk = ac->k, fb0 = em_nfb, tk = (int)e->k, q = nvar++;
    uses_data = 1; put(b, "({ int64_t *_q%d = (int64_t *)(", q); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "); ");
    if (tk >= 0 && spec_ix_only(e)) {                /* (one slot updated: the block itself, or a copy of it if shared) */
      int W = nk + !e->untag;
      put(b, "int64_t *t%d = _q%d; if (!lin_uniq(_q%d)) { t%d = lin_alloc(%d); __builtin_memcpy(t%d, _q%d, %d * 8); ", tk, q, q, tk, W, tk, q, W);
      for (int j = 0; j < nk; j++) { int fd = rc_fdrop(ac, j, ss); if (fd >= 0) put(b, "lin_dup(t%d[%d]); ", tk, j + !e->untag); }
      put(b, "lin_drop%d((int64_t)_q%d); } ", drop_fn(ss), q);
      int sa = ixu_always; ixu_always = tk;
      tailpos = tp; int ok = emitx(b, pre, e->b, par, budget - 1); tailpos = 0; ixu_always = sa;
      put(b, "; })"); return ok;
    }
    for (int j = 0; j < nk; j++) if (e->mspec[0][j]) {
      int k = nvar++;
      if (em_nfb == em_cfb) em_fb = realloc(em_fb, sizeof *em_fb * (size_t)(em_cfb = em_cfb ? em_cfb * 2 : 16));
      em_fb[em_nfb++] = (EmFB){ e->a, j, k };
    }
    /* (shared: the fields it keeps get counts first; then they are read; then the block is let go.  The reads come
       after the test, in one place: read before it, or in each branch, a walk down a tree measured 1.5x slower) */
    put(b, "int _u%d = lin_uniq(_q%d); ", q, q);
    if (tk >= 0) put(b, "int64_t *t%d = _u%d ? _q%d : 0; ", tk, q, q);
    { Buf d = nbuf(64);
      for (int i = fb0; i < em_nfb; i++) { int fd = rc_fdrop(ac, (int)em_fb[i].k, ss); if (fd >= 0) put(&d, "lin_dup(_q%d[%" PRId64 "]); ", q, em_fb[i].k + !e->untag); }
      if (d.len) put(b, "if (!_u%d) { %s} ", q, d.s);
      free(d.s); }
    for (int i = fb0; i < em_nfb; i++) put(b, "int64_t v%d = _q%d[%" PRId64 "]; ", em_fb[i].v, q, em_fb[i].k + !e->untag);
    put(b, "if (_u%d) { ", q);
    for (int j = 0; j < nk; j++) if (!e->mspec[0][j]) { int fd = rc_fdrop(ac, j, ss); if (fd >= 0) put(b, "lin_drop%d(_q%d[%d]); ", fd, q, j + !e->untag); }
    if (tk < 0) put(b, "lin_free(_q%d, %d); ", q, nk + !e->untag);
    put(b, "} else lin_drop%d((int64_t)_q%d); ", drop_fn(ss), q);
    tailpos = tp; int ok = emitx(b, pre, e->b, par, budget - 1); tailpos = 0;
    put(b, "; })"); em_nfb = fb0; return ok;
  }
  if (e->op == E_FIELD && em_nfb) for (int i = em_nfb - 1; i >= 0; i--)   /* (a field an arm took: its local) */
    if (em_fb[i].k == e->k && mr_same_base(em_fb[i].base, e->a)) { put(b, tp ? "LIN_SET(dst, v%d)" : "v%d", em_fb[i].v); return 1; }
  if (bound(e)) { put(b, tp ? "LIN_SET(dst, v%d)" : "v%d", e->var); return 1; }
  if (tp) {
    const Expr *K, *S; int64_t off;
    if (e->op == E_CALL && hasd[e->k]) {              /* a tail call: the destination goes with it */
      put(b, "f%" PRId64 "%s(dst", e->k, dp_name(e->k));
      for (int i = 0; i < e->nargs; i++) { put(b, ", "); if (!emit_arg(b, pre, e, i, par, budget - 1)) return 0; }
      if (!call_fv(b, e->k)) return 0;
      put(b, "%s)", dp_stop(e->k)); return 1;
    }
    { const Expr *K2, *x0; if (ix_update(e, &K2, &x0)) return emit_ixu(b, pre, e, K2, x0, par, budget, 1); }
    int hole = -1;
    if (e->op == E_CTOR && e->nargs)
      for (int i = 0; i < e->nargs && hole < 0; i++)
        if (e->args[i]->op == E_CALL && hasd[e->args[i]->k] && !bound(e->args[i]) && (!e->ci || field_live(e->ci, i))) hole = i;
    if (hole >= 0) {
      /* the call's arguments first (they may read the block this cell is rebuilt in), then the cell with a hole,
         then the call, told where its result goes */
      Expr *c = (Expr *)e->args[hole]; int hv = nvar++, ov = nvar++, a0 = nvar; nvar += c->nargs;
      put(b, "({ int64_t v%d = 0; ", hv);
      for (int i = 0; i < c->nargs; i++) { put(b, "int64_t v%d = ", a0 + i); if (!emit_arg(b, pre, c, i, par, budget - 1)) return 0; put(b, "; "); }
      int sv = c->var, ss = c->vscope; c->var = hv; c->vscope = fscope;
      const Expr *sh = dp_hole; dp_hole = c;
      put(b, "int64_t *v%d = (int64_t *)(", ov); int ok = emitx(b, pre, e, par, budget - 1);
      dp_hole = sh;
      c->var = sv; c->vscope = ss;
      if (!ok) return 0;
      put(b, "); ");
      put(b, "LIN_SET(dst, (int64_t)v%d); f%" PRId64 "%s(&v%d[%d]", ov, c->k, dp_name(c->k), ov, hole + !e->untag);
      for (int i = 0; i < c->nargs; i++) put(b, ", v%d", a0 + i);
      if (!call_fv(b, c->k)) return 0;
      put(b, "%s); })", dp_stop(c->k)); return 1;
    }
    if (!(e->op == E_MATCH || (e->op == E_IF && !indexed_pick(e, &K, &S, &off)))) {   /* a leaf: the result itself */
      /* (a block rebuilt in place is usually where it was: LIN_PUT; anything else is new: LIN_SET) */
      put(b, e->op == E_CTOR && e->tok ? "LIN_PUT(dst, " : "LIN_SET(dst, "); if (!emitx(b, pre, e, par, budget - 1)) return 0; put(b, ")"); return 1;
    }
  }
  switch (e->op) {
  case E_CONST: if (e->k == INT64_MIN) put(b, "(-%" PRId64 "L-1)", -(e->k + 1)); else put(b, "(%" PRId64 "L)", e->k); return 1;
  case E_PARAM:   /* an outer function's parameter: lifted into this one's extra parameters */
    if (e->nargs == emitting) { put(b, "p%" PRId64 "", e->k); return 1; }
    if (emitting >= 0 && emitting < lifted && fv_has(emitting, e->nargs, e->k)) { put(b, "l%d_%" PRId64 "", e->nargs + 1, e->k); return 1; }
    DBG("declined: a parameter read where it is not in scope\n"); return 0;
  case E_BIN: {
    Buf x = nbuf(256), y = nbuf(256);
    int ok = 1;
    const Expr *xs2[2] = { e->a, e->b };
    if (par && heavy(e->a) && heavy(e->b) && !par_shares(xs2, 2)) {
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
  case E_IF: {
    const Expr *K, *S; int64_t off;
    if (indexed_pick(e, &K, &S, &off)) {
      put(b, "(((int64_t *)("); if (!emitx(b, pre, S, par, budget - 1)) return 0;
      put(b, "))[("); if (!emitx(b, pre, K, par, budget - 1)) return 0; put(b, ") + %" PRId64 "])", off); return 1;
    } }
    put(b, "("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    put(b, " ? "); tailpos = tp; if (!emit_region(b, pre, e->b, par, budget - 1)) return 0;
    put(b, " : "); tailpos = tp; if (!emit_region(b, pre, e->c, par, budget - 1)) return 0;
    put(b, ")"); return 1;
  /* DATA in C: a constructor with fields is a block {index, fields...} from the unit's arena; one with none is
     the immediate 2*index+1 (a block is word-aligned, so the low bit tells them apart).  A match reads the index
     and picks the branch; a field is a word of the block. */
  case E_CTOR:
    uses_data = 1;
    if (!e->nargs) { put(b, "(%" PRId64 "L)", e->k * 2 + 1); return 1; }
    { const Expr *K2, *x0; if (ix_update(e, &K2, &x0)) return emit_ixu(b, pre, e, K2, x0, par, budget, 0); }
    if (e->tok) {                                    /* (see REUSE) built in the block an arm took apart, when it was unique */
      int t = e->tok - 1, W = e->nargs + !e->untag;
      put(b, "({ int64_t *_o; int _r = t%d != 0; if (_r) { _o = t%d; t%d = 0; } else _o = lin_alloc(%d); ", t, t, t, W);
      if (!e->untag) put(b, "_o[0] = %" PRId64 "L; ", e->k);
      for (int i = 0; i < e->nargs; i++) {
        if (e->ci && !field_live(e->ci, i)) continue;
        const Expr *a = e->args[i];
        if (a == dp_hole) continue;                   /* (the hole of a destination-passing cell: its call writes it) */
        int same = a->op == E_FIELD && a->k == i && mr_same_base(a->a, mr_tokb[t]);   /* (moved back to its own slot) */
        if (same) put(b, "if (!_r) ");
        put(b, "_o[%d] = (", i + !e->untag); if (!emitx(b, pre, a, par, budget - 1)) return 0; put(b, "); ");
      }
      put(b, "(int64_t)_o; })"); return 1;
    }
    if (e->untag) put(b, "({ int64_t *_o = lin_alloc(%d); ", e->nargs);
    else put(b, "({ int64_t *_o = lin_alloc(%d); _o[0] = %" PRId64 "L; ", e->nargs + 1, e->k);
    for (int i = 0; i < e->nargs; i++) {
      if (e->ci && !field_live(e->ci, i)) continue;   /* (a field nobody reads is not computed) */
      put(b, "_o[%d] = (", i + !e->untag); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; put(b, "); ");
    }
    put(b, "(int64_t)_o; })"); return 1;
  case E_FIELD:
    uses_data = 1;
    put(b, "(((int64_t *)("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "))[%" PRId64 "])", e->k + !e->untag); return 1;
  case E_MATCH: {
    uses_data = 1;
    /* the scrutinee once, in a local the branches read it by (a reused block is named by it, never recomputed) */
    int sv = nvar++;
    put(b, "({ int64_t v%d = ", sv);
    if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    put(b, "; int64_t _s = v%d", sv);
    Expr *sx = (Expr *)e->a; int sx_var = sx->var, sx_scope = sx->vscope;
    if (sx->op != E_PARAM && sx->op != E_CONST) { sx->var = sv; sx->vscope = fscope; }
    if (e->untag) put(b, "; int64_t _t = (_s & 1) ? (_s >> 1) : %dL; (", e->box);
    else put(b, "; int64_t _t = (_s & 1) ? (_s >> 1) : ((int64_t *)_s)[0]; (");
    for (int i = 0; i < e->nargs; i++) {
      if (i < e->nargs - 1) put(b, "_t == %d ? ", i);
      if ((tailpos = tp, !emit_region(b, pre, e->args[i], par, budget - 1))) return 0;   /* (an arm that takes its block apart: E_SPEC) */
      if (i < e->nargs - 1) put(b, " : ");
    }
    put(b, "); })");
    sx->var = sx_var; sx->vscope = sx_scope;
    return 1;
  }
  case E_VOP: {                                     /* (see OWNED VECTORS) */
    uses_data = 1;
    Shape vs = shape_of(e->k == LIN_VOP_NEW || e->k == LIN_VOP_SET || e->k == LIN_VOP_PUSH ? e : e->args[0]);
    Shape es = vs.k == 5 && vs.dt == VEC_DT && vs.a && vs.a->n ? vs.a->s[0] : (Shape){ 0, NULL, NULL };
    int ed = es.k == 5 && es.dt ? drop_fn(es) : -1;   /* (elements that are counted) */
    int vd = vs.k == 5 && vs.dt == VEC_DT ? drop_fn(vs) : -1;
#define ARG(i) do { if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; } while (0)
    switch (e->k) {
    case LIN_VOP_NEW:
      put(b, "({ int64_t _n = ("); ARG(0); put(b, "), _x = ("); ARG(1);
      put(b, "); if (_n < 0) _n = 0; int64_t _c = _n < 4 ? 4 : _n, *_o = lin_alloc(_c + 2); _o[0] = _n; _o[1] = _c; for (int64_t _i = 0; _i < _n; _i++) _o[_i + 2] = _x; ");
      if (ed >= 0) put(b, "if (_n) lin_dupn(_x, _n - 1); else lin_drop%d(_x); ", ed);   /* (the one reference it was given, n times over) */
      put(b, "(int64_t)_o; })"); return 1;
    case LIN_VOP_LEN: put(b, "(((int64_t *)("); ARG(0); put(b, "))[0])"); return 1;
    case LIN_VOP_GET:
      put(b, "({ int64_t *_v = (int64_t *)("); ARG(0); put(b, "); uint64_t _i = (uint64_t)("); ARG(1);
      put(b, "); _i < (uint64_t)_v[0] ? _v[_i + 2] : 0L; })"); return 1;
    case LIN_VOP_SET:
      put(b, "({ int64_t *_v = (int64_t *)("); ARG(0); put(b, "); uint64_t _i = (uint64_t)("); ARG(1); put(b, "); int64_t _x = ("); ARG(2); put(b, "); ");
      put(b, "if (_i < (uint64_t)_v[0]) { if (!lin_uniq(_v)) { int64_t *_n = (int64_t *)lin_copy%d((int64_t)_v); lin_drop%d((int64_t)_v); _v = _n; } ", vd, vd);
      if (ed >= 0) put(b, "int64_t _old = _v[_i + 2]; _v[_i + 2] = _x; lin_drop%d(_old); } else lin_drop%d(_x); ", ed, ed);
      else put(b, "_v[_i + 2] = _x; } ");
      put(b, "(int64_t)_v; })"); return 1;
    case LIN_VOP_PUSH:
      put(b, "({ int64_t *_v = (int64_t *)("); ARG(0); put(b, "); int64_t _x = ("); ARG(1); put(b, "); int64_t _n = _v[0]; ");
      put(b, "if (!lin_uniq(_v) || _n == _v[1]) { int64_t _c = _n == _v[1] ? _v[1] * 2 : _v[1], *_w = lin_alloc(_c + 2); __builtin_memcpy(_w, _v, (size_t)(_n + 2) * 8); _w[1] = _c; ");
      put(b, "if (lin_uniq(_v)) lin_free(_v, _v[1] + 2); else { ");
      if (ed >= 0) put(b, "for (int64_t _j = 0; _j < _n; _j++) lin_dup(_w[_j + 2]); ");
      put(b, "lin_drop%d((int64_t)_v); } _v = _w; } _v[_n + 2] = _x; _v[0] = _n + 1; (int64_t)_v; })", vd); return 1;
    }
#undef ARG
    return 0; }
  case E_FOP:
    put(b, "%s(", FROW[e->k].c);
    for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; }
    put(b, ")"); return 1;
  case E_CALL:
    { int calls = 0, entry = par && emitting == -1 && e->k != 0;   /* (the entry: any call's independent loops) */
      plpar = par && (e->k != 0 || emitting == -1);   /* (f0 has its own parallel copy, but the entry may fold it) */
      par = par && e->k == 0;                      /* only the entry function has a parallel version */
      for (int i = 0; i < e->nargs; i++) calls += heavy(e->args[i]);
      if ((par || entry) && calls >= 2 && !par_shares((const Expr **)e->args, e->nargs)) {   /* independent calls among the arguments: at once */
        Buf *nm = calloc((size_t)e->nargs, sizeof *nm);
        for (int i = 0; i < e->nargs; i++) nm[i] = nbuf(32);
        int ok = par_group(b, pre, (const Expr **)e->args, e->nargs, nm, budget);
        if (ok && par) { put(b, "fp("); for (int i = 0; i < e->nargs; i++) put(b, "%s, ", nm[i].s); put(b, "d + 1); })"); }
        else if (ok) { put(b, "f%" PRId64 "(", e->k); for (int i = 0; i < e->nargs; i++) put(b, "%s%s", i ? ", " : "", nm[i].s); ok = call_fv(b, e->k); put(b, "); })"); }
        for (int i = 0; i < e->nargs; i++) free(nm[i].s);
        free(nm); return ok;
      } }
    if (plpar && pl_unit && pl_ok((int)e->k) && !e->drops) {   /* (see A LOOP WHOSE STEPS ARE INDEPENDENT) */
      int se = emitting, sfs = fscope; if (!pl_emit(pre, (int)e->k, budget)) return 0; emitting = se; fscope = sfs;   /* (its own scope while it is written: then ours again, our names with it) */
      put(b, "f%" PRId64 "_pl(", e->k);
      for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emit_arg(b, pre, e, i, 0, budget - 1)) return 0; }
      put(b, ", %s)", emitting == -1 ? "d" : "d + 1"); nsite++; return 1;
    }
    {
      if (par) put(b, "fp("); else put(b, "f%" PRId64 "(", e->k);
      for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emit_arg(b, pre, e, i, par, budget - 1)) return 0; }
      if (!par && !call_fv(b, e->k)) return 0;
      put(b, par ? "%sd + 1)" : ")", e->nargs ? ", " : "");
    }
    return 1;
  }
  return 0;
}

/* the tails of f's body: a cell holding f's own call in a field makes f a destination-passing function, and so is
   whatever one of those tail-calls (the destination goes along, so their mutual loops stay loops) */
/* A MAP IN PARALLEL.  A destination-passing loop that walks ONE list -- each call of itself takes the rest of
   that list and every other parameter unchanged -- computes each cell from the cell alone, so stretches of the
   list can be done at once: each thread builds its stretch through a destination of its own and reports the
   hole it stopped at, and the stretches are joined end to end.  Worth it when a cell's value takes a call to
   compute.  `pm_k`: the list parameter; `pm_tf`: the field holding the rest. */
static int ho_f; static unsigned ho_info(const Expr *e); static unsigned char *fr_memo;
static int pm_k, pm_tf, pm_heavy, pm_holes;
static int pm_self(const Expr *c, int f) {           /* is this call of f the next step of the walk? */
  int K = -1;
  for (int j = 0; j < c->nargs; j++) {
    const Expr *a = c->args[j];
    if (a->op == E_PARAM && a->nargs == f && a->k == j) continue;
    if (a->op == E_CONST && funs[f].known && j < funs[f].arity && funs[f].known[j]) continue;   /* (a function bound in this copy) */
    if (a->op == E_FIELD && a->untag && a->a && a->a->op == E_PARAM && a->a->nargs == f && a->a->k == j && K < 0) { K = j; if (pm_tf >= 0 && pm_tf != (int)a->k) return 0; pm_tf = (int)a->k; continue; }
    return 0;
  }
  if (K < 0 || (pm_k >= 0 && pm_k != K)) return 0;
  pm_k = K; return 1;
}
static int pm_tail(const Expr *e, int f) {
  const Expr *K, *S; int64_t off;
  ho_f = f;
  switch (e->op) {
  case E_IF: if (indexed_pick(e, &K, &S, &off)) return !(ho_info(e) & 4u);
    return !(ho_info(e->a) & 4u) && pm_tail(e->b, f) && pm_tail(e->c, f);
  case E_MATCH: if (ho_info(e->a) & 4u) return 0;
    for (int i = 0; i < e->nargs; i++) if (!pm_tail(e->args[i], f)) return 0;
    return 1;
  case E_LET: return !(ho_info(e->a) & 4u) && pm_tail(e->b, f);
  case E_DROP: case E_SPEC: return pm_tail(e->b, f);
  case E_CALL: if (e->k == f) return pm_self(e, f);
    return !(ho_info(e) & 4u);
  case E_CTOR: {
    int hole = -1;
    for (int i = 0; i < e->nargs; i++) if (e->args[i]->op == E_CALL && e->args[i]->k == f && (!e->ci || field_live(e->ci, i))) { if (hole >= 0) return 0; hole = i; }
    if (hole < 0) return !(ho_info(e) & 4u);
    if (!pm_self(e->args[hole], f)) return 0;
    for (int i = 0; i < e->nargs; i++) if (i != hole) { if (ho_info(e->args[i]) & 4u) return 0; if (has_call(e->args[i])) pm_heavy = 1; }
    pm_holes++; return 1; }
  default: return !(ho_info(e) & 4u);
  }
}
static int pm_cand(int f) {
  const Expr *mb = funs[f].body; while (mb && (mb->op == E_LET || mb->op == E_DROP || mb->op == E_SPEC)) mb = mb->b;   /* (values bound before it: see EXPLICIT BINDING) */
  if (!mb || mb->op != E_MATCH || !mb->untag) return 0;
  const Expr *sc = mb->a;
  if (sc->op != E_PARAM || sc->nargs != f) return 0;
  pm_k = pm_tf = -1; pm_heavy = pm_holes = 0; ho_f = f; mm_new(MM_SSTR);
  free(fr_memo); fr_memo = calloc((size_t)nfun + 1, 1);
  return pm_tail(funs[f].body, f) && pm_holes > 0 && pm_heavy && pm_k == (int)sc->k && pm_tf >= 0;
}
static int dp_scan(const Expr *e, int f, unsigned char *hd) {
  const Expr *K, *S; int64_t off;
  switch (e->op) {
  case E_IF: if (indexed_pick(e, &K, &S, &off)) return 0; return dp_scan(e->b, f, hd) | dp_scan(e->c, f, hd);
  case E_MATCH: { int r = 0; for (int i = 0; i < e->nargs; i++) r |= dp_scan(e->args[i], f, hd); return r; }
  case E_LET: case E_DROP: case E_SPEC: return dp_scan(e->b, f, hd);
  case E_CTOR:
    { const Expr *K2, *x0; if (ix_update(e, &K2, &x0)) { if (x0->op == E_CALL && x0->k == f && !hd[f]) { hd[f] = 1; return 1; } return 0; } }
    for (int i = 0; i < e->nargs; i++)
      if (e->args[i]->op == E_CALL && e->args[i]->k == f && (!e->ci || field_live(e->ci, i)) && !hd[f]) { hd[f] = 1; return 1; }
    return 0;
  case E_CALL: if (hd[f] && e->k >= 0 && e->k < nfun && !hd[e->k]) { hd[e->k] = 1; return 1; } return 0;
  default: return 0;
  }
}
static uint64_t fnv1a(const char *s) { uint64_t h = 1469598103934665603UL; for (; *s; s++) { h ^= (unsigned char)*s; h *= 1099511628211UL; } return h; }
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

typedef int64_t (*Entry)(const int64_t *, int threads);
#ifdef LIN_STATIC
/* the units a static build was given (web/units.c, written by the build; ended by h == 0) */
typedef struct { uint64_t h; Entry entry; int *aborted; void (*release)(void); } LinFnUnit;
extern const LinFnUnit lin_fn_units[];
#endif
typedef struct { uint64_t h; Entry fn; int arity, kind; unsigned strict; int *aborted;
                 Shape res; Shape **fld; int64_t nctor; void (*release)(void); Shape *psh; int npsh; } Compiled;   /* psh: each runtime argument's shape */   /* kind 5: a data result, read by res/fld */   /* aborted: a data unit's guard fired */   /* strict: the parameters certainly evaluated */
static Compiled **done; static int ndone, donecap;   /* (pointers: a call holds one while another compiles) */
/* -march=native code must never be loaded on a different CPU, so the cache key includes this one's identity. */
static uint64_t cpu_key(void) {
  static uint64_t k;
  if (k) return k;
#ifdef LIN_STATIC
  return k = fnv1a("wasm32");                         /* (one target, whatever the machine: the units were compiled for it) */
#endif
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
static Shape **sh_fld; static int64_t sh_nctor;
static Shape *esh; static int nesh, esh_data, esh_cap;
/* RUNTIME INPUTS: a closed list met while compiling (a string the program read, nested in an argument
   expression) is not expanded as a constant -- it is an extra runtime argument, read in at call time. */
static Port *inp_port; static int n_inp, inp_cap;
static int input_of(Port p) {                       /* its runtime index (a new one the first time) */
  for (int i = 0; i < n_inp; i++) if (inp_port[i].node == p.node) return nesh - n_inp + i;
  if (n_inp >= inp_cap) inp_port = realloc(inp_port, sizeof *inp_port * (size_t)(inp_cap = inp_cap ? inp_cap * 2 : 8));
  if (nesh >= esh_cap) esh = realloc(esh, sizeof *esh * (size_t)(esh_cap = esh_cap ? esh_cap * 2 : 16));
  inp_port[n_inp++] = p; esh[nesh] = (Shape){ 0, NULL }; esh_data = 1;
  return nesh++;
}   /* the entry's runtime arguments' shapes (data ones: passed in) */
static Compiled *compile_src(const char *src, int ar, int kind, Shape res) {
  /* LIN_FN_LEAKS=1 (a debugging aid): every allocation site is numbered, every block remembers its own, and the
     unit reports at its end the sites whose blocks are still held -- the code around each is printed here */
  char *lsrc = NULL;
  if (getenv("LIN_FN_LEAKS") && strstr(src, "lin_alloc(")) {
    Buf lb = nbuf(strlen(src) * 2 + 64); put(&lb, "#define LIN_LEAKS 1\n"); int site = 0;
    for (const char *q = src, *m; ; q = m + 10) {
      m = strstr(q, "lin_alloc("); if (!m) { put(&lb, "%s", q); break; }
      put(&lb, "%.*s", (int)(m - q), q);
      if (m > src && (m[-1] == '*' || m[-1] == '_')) { put(&lb, "lin_alloc("); continue; }   /* (its definition, and others' names) */
      put(&lb, "lin_alloc_at(%d, ", site);
      const char *ctx = m - 160 > src ? m - 160 : src;
      fprintf(stderr, "fn: [allocation site %d: ...%.*s]\n", site, (int)(m - ctx), ctx);
      site++;
    }
    lsrc = lb.s; src = lsrc;
  }
  uint64_t h = fnv1a(src) ^ cpu_key();
#ifndef LIN_STATIC
  {                                                  /* AHEAD FOR ANOTHER TARGET: the unit's source, kept for a static build */
    const char *ed = getenv("LIN_FN_EMIT_DIR");      /* (web/build.sh: its key is the one that build will look for) */
    if (ed && ed[0]) {
      size_t en = strlen(ed) + 32; char ep[en]; snprintf(ep, en, "%s/fn-%016" PRIx64 ".c", ed, fnv1a(src) ^ fnv1a("wasm32"));   /* (sized from the directory's name) */
      FILE *ef = fopen(ep, "wb"); if (ef) { fputs(src, ef); fclose(ef); }
    }
  }
#endif
  for (int i = 0; i < ndone; i++) if (done[i]->h == h) return done[i]->fn ? done[i] : NULL;
#ifdef LIN_STATIC
  /* (no C compiler where this runs: a unit is one compiled AHEAD, by the build, and linked in -- found by the
     same key, the hash of the source written here; see web/README.md) */
  Entry e = NULL; int *ab = NULL; void (*rel)(void) = NULL;
  for (const LinFnUnit *u = lin_fn_units; u->h; u++) if (u->h == h) { e = u->entry; ab = u->aborted; rel = u->release; break; }
  void *hnd = e ? (void *)lin_fn_units : NULL;
  if (!e) DBG("unit %016" PRIx64 " was not compiled into this build\n", h);
#else
  char dir[4096], c[4200], so[4200];
  cache_dir(dir, sizeof dir); mkdir_p(dir);
  snprintf(c, sizeof c, "%s/fn-%016" PRIx64 ".c", dir, h); snprintf(so, sizeof so, "%s/fn-%016" PRIx64 ".so", dir, h);
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
#endif
  if (ndone >= donecap) done = realloc(done, (size_t)(donecap = donecap ? donecap * 2 : 32) * sizeof *done);
  Compiled *cp = calloc(1, sizeof *cp);
  *cp = (Compiled){ h, e, ar, kind, 0, ab, res, NULL, 0, NULL };
  if (esh_data && nesh) { cp->npsh = nesh; cp->psh = malloc(sizeof *cp->psh * (size_t)nesh); memcpy(cp->psh, esh, sizeof *esh * (size_t)nesh); }
  if ((kind == 5 || esh_data) && hnd) {             /* the field shapes the result (and the arguments) are read by */
#ifdef LIN_STATIC
    cp->release = rel;
#else
    cp->release = (void (*)(void))(intptr_t)dlsym(hnd, "lin_fn_release");
#endif
    cp->nctor = sh_nctor; cp->fld = calloc((size_t)sh_nctor + 1, sizeof *cp->fld);
    for (int64_t k = 1; k <= sh_nctor; k++) { int nk = lin_ctor_info(k)->k + 1; cp->fld[k] = malloc(sizeof **cp->fld * (size_t)nk); memcpy(cp->fld[k], sh_fld[k], sizeof **cp->fld * (size_t)nk); }
    if (kind == 5 && !cp->release) e = NULL;
  }
  done[ndone++] = cp;
  return e ? cp : NULL;
}

/* A PARALLEL REDUCTION.  f(.., i, .., acc, ..) = if i == c then acc else f(.., i - 1, .., acc (+) g, ..), with every
   other parameter passed unchanged, g independent of acc and (+) associative and commutative -- wrapping add or
   mul, band / bor / bxor, or max / min written as a conditional -- folds g over the range (c, i0] in ANY order
   to the same value.  So the range is split among the threads, each folds its blocks from (+)'s identity, and
   the partial results are combined with the initial acc.  Every g(i) is still evaluated exactly once. */
typedef struct { int iv, acc, op, ismax; int64_t c; const Expr *g; int up, bnd; } Red;   /* up: counts up to parameter bnd (or to c) */
static int is_param(const Expr *e, int k) { return e && e->op == E_PARAM && e->k == k && e->nargs == 0; }
static int mentions(const Expr *e, int k) {
  switch (e->op) {
  case E_PARAM: return e->k == k && e->nargs == 0;
  case E_BIN: return mentions(e->a, k) || mentions(e->b, k);
  case E_IF: return mentions(e->a, k) || mentions(e->b, k) || mentions(e->c, k);
  case E_CALL: case E_FOP: case E_VOP: case E_CTOR: for (int i = 0; i < e->nargs; i++) if (mentions(e->args[i], k)) return 1; return 0;
  case E_FIELD: return mentions(e->a, k);
  case E_MATCH: if (mentions(e->a, k)) return 1; for (int i = 0; i < e->nargs; i++) if (mentions(e->args[i], k)) return 1; return 0;
  default: return 0;
  }
}
static int find_reduction(Red *r) {
  const Expr *e = funs[0].body;
  if (e->op != E_IF || e->a->op != E_BIN || e->a->k != LIN_OP_EQ) return 0;
  const Expr *c = e->a, *base = e->b, *step = e->c;
  int iv; int64_t cv;
  int bnd = -1, up = 0; cv = 0;
  if (c->a->op == E_PARAM && c->a->nargs == 0 && c->b->op == E_CONST) { iv = (int)c->a->k; cv = c->b->k; }
  else if (c->b->op == E_PARAM && c->b->nargs == 0 && c->a->op == E_CONST) { iv = (int)c->b->k; cv = c->a->k; }
  else if (c->a->op == E_PARAM && c->a->nargs == 0 && c->b->op == E_PARAM && c->b->nargs == 0 && c->a != c->b) { iv = (int)c->a->k; bnd = (int)c->b->k; }
  else return 0;
  if (base->op != E_PARAM || base->nargs != 0 || base->k == iv) return 0;
  int acc = (int)base->k;
  if (step->op != E_CALL || step->k != 0 || step->nargs != arity) return 0;
  if (bnd >= 0) {                                    /* which of the two compared parameters moves: the other is the bound */
    const Expr *a = step->args[iv];
    if (is_param(a, iv)) { int t = iv; iv = bnd; bnd = t; }
    if (bnd == acc || iv == acc) return 0;
  }
  for (int j = 0; j < arity; j++) {
    const Expr *a = step->args[j];
    if (j == iv) {
      if (!(a->op == E_BIN && (a->k == LIN_OP_SUB || a->k == LIN_OP_ADD) && is_param(a->a, iv) && a->b->op == E_CONST && a->b->k == 1)) return 0;
      up = a->k == LIN_OP_ADD;
    }
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
  r->iv = iv; r->acc = acc; r->op = op; r->ismax = ismax; r->c = cv; r->g = g; r->up = up; r->bnd = bnd;
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
  { Port tip = dhop(N, body), mb, mid; int ml; int64_t cid;
    if (marker_app(tip, &mb, &ml, &mid)) {
      Env *probe = NULL;
      int sf = failed; int64_t sfu = fuel;
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
  int sf = failed, snf = nfun, seid = eid; int64_t sfu = fuel; int ok = 0, isf = 1; fail_quiet++;
  const_int(v, &ok); if (!failed && ok) isf = 0;
  failed = 0; if (isf) { const_bool(v, &ok); if (!failed && ok) isf = 0; }
  failed = 0; if (isf && ffi_expr(v)) isf = 0;
  failed = sf; fuel = sfu; fun_rollback(snf); (void)seid; fail_quiet--;
  return isf;
}
static int known_eq(V **a, V **b, int ar) {
  for (int i = 0; i < ar; i++) {
    V *x = a ? a[i] : NULL, *y = b ? b[i] : NULL;
    if (!x != !y || (x && !fun_eq(x, y))) return 0;
  }
  return 1;
}
/* FIELDS NOBODY READS.  Lin is lazy: a constructor's field that no match ever looks at is never computed.  The C
   is strict, so the same economy is made statically: a field of a constructor is LIVE if some read of it is
   reachable from a result (through live fields only -- a fixpoint from "none"), and a dead field's value is not
   computed at all: `(slength (str_words s))` builds no words.  A structure that leaves the unit is read by
   whoever gets it, so then every field is live. */
static unsigned char **fld_live; static int64_t fl_n; static int fl_changed;
static int64_t ctor_id(const LinCtor *ci);
static int field_live(const LinCtor *ci, int j) {
  if (!fld_live) return 1;
  int64_t id = ctor_id(ci);
  return !(id > 0 && id <= fl_n && j < ci->k) || fld_live[id][j];
}
static void live_walk(const Expr *e) {
  if (!e || mm_has(MM_SITE, e)) return;
  mm_put(MM_SITE, e, 1);
  if (e->op == E_FIELD && e->ci) { int64_t id = ctor_id(e->ci); if (id > 0 && id <= fl_n && e->k < e->ci->k && !fld_live[id][e->k]) { fld_live[id][e->k] = 1; fl_changed = 1; } }
  if (e->op == E_CTOR && e->ci) {
    for (int i = 0; i < e->nargs; i++) if (field_live(e->ci, i)) live_walk(e->args[i]);
    return;
  }
  if (e->a) live_walk(e->a);
  if (e->b) live_walk(e->b);
  if (e->c) live_walk(e->c);
  for (int i = 0; i < e->nargs && e->args; i++) live_walk(e->args[i]);
}
static void fields_live(const Expr *entry, int all) {
  fl_n = 0; while (lin_ctor_info(fl_n + 1)) fl_n++;
  fld_live = A(sizeof *fld_live * (size_t)(fl_n + 1));
  for (int64_t k = 1; k <= fl_n; k++) { int nk = lin_ctor_info(k)->k + 1; fld_live[k] = A((size_t)nk); memset(fld_live[k], all ? 1 : 0, (size_t)nk); }
  if (all) return;
  for (int round = 0; round <= fl_n * 64 + 64; round++) {
    fl_changed = 0; mm_new(MM_SITE);
    for (int i = 0; i < nfun; i++) live_walk(funs[i].body);
    live_walk(entry);
    if (!fl_changed) break;
  }
}

/* The reduction's code: g (one step's value), the worker, and the statement that runs it over the range.
   The range is (lo, hi] of j, the induction variable being j (counting down to lo) or j - 1 (counting up to hi);
   an empty or backwards range is not ours (the caller's sequential code decides what that means). */
static int emit_region(Buf *b, Buf *pre, const Expr *e, int par, int budget);
static int red_defs(Buf *b, Buf *pre, const Red *red, int data) {
  int64_t id = red->ismax > 0 ? INT64_MIN : red->ismax < 0 ? INT64_MAX
          : (red->op == LIN_OP_MUL) ? 1 : (red->op == LIN_OP_BAND) ? -1 : 0;   /* (+)'s identity */
  put(b, "static int64_t g("); plist(b, 1); put(b, ") { return ");
  emitting = 0; fscope++; int ok = emit_region(b, pre, red->g, 0, 4096); put(b, "; }\n");
  put(b, "typedef struct { int64_t p[%d]; int64_t lo, block, r; int64_t *next; } R;\n", arity);
  put(b, "static void *rrun(void *v) { R *q = v; int64_t acc = %" PRId64 "L;%s\n", id, data ? " LIN_TASK_START((size_t)256 << 20);" : "");
  for (int i = 0; i < arity; i++) put(b, "  int64_t p%d = q->p[%d];\n", i, i);
  put(b, "  for (;;) { int64_t hi = __atomic_fetch_sub(q->next, q->block, __ATOMIC_RELAXED); if (hi <= q->lo) break;\n");
  put(b, "    int64_t lo = hi - q->block; if (lo < q->lo) lo = q->lo;\n    for (int64_t i = hi; i > lo; i--) { p%d = i%s; int64_t x = g(", red->iv, red->up ? " - 1" : "");
  plist(b, 0); put(b, "); acc = "); red_combine(b, red, "x", "acc"); put(b, "; } }\n");
  put(b, "  q->r = acc; return 0; }\n");
  return ok;
}
static void red_run(Buf *b, const Red *red, int data, const char *threads, const char *done) {
  Buf lob = nbuf(32), hib = nbuf(32);
  Buf *mv = red->up ? &lob : &hib, *bd = red->up ? &hib : &lob;   /* the moving end, and the bound */
  put(mv, "p%d", red->iv);
  if (red->bnd >= 0) put(bd, "p%d", red->bnd); else put(bd, "%" PRId64 "L", red->c);
  const char *lo = lob.s, *hi = hib.s;
  /* a cheap step needs some thousands of iterations to pay for a thread; a step that CALLS (a whole inner loop)
     pays from a few per thread */
  if (has_call(red->g)) put(b, "  if (%s > 1 && %s > %s && %s - %s >= (int64_t)%s * 4) {\n", threads, hi, lo, hi, lo, threads);
  else put(b, "  if (%s > 1 && %s > %s && %s - %s >= 4096) {\n", threads, hi, lo, hi, lo);
  put(b, "    int64_t next = %s; pthread_t t[%s]; R q[%s];%s\n", hi, threads, threads,
      data ? " pthread_attr_t ra; pthread_attr_init(&ra); pthread_attr_setstacksize(&ra, (size_t)256 << 20);" : "");
  if (data) { Buf sh = nbuf(64); rc_share_params(&sh, 0, red->g, NULL, NULL); if (sh.len) put(b, "    %s\n", sh.s); free(sh.s); }   /* (counted: read by every thread) */
  put(b, "    for (int k = 0; k < %s; k++) { R r = { {", threads); plist(b, 0);
  put(b, "}, %s, (%s - %s) / ((int64_t)%s * 64) + 1, 0, &next }; q[k] = r; pthread_create(&t[k], %s, rrun, &q[k]); }\n", lo, hi, lo, threads, data ? "&ra" : "0");
  put(b, "    int64_t acc = p%d;\n    for (int k = 0; k < %s; k++) { pthread_join(t[k], 0); acc = ", red->acc, threads);
  red_combine(b, red, "q[k].r", "acc"); put(b, "; }\n    %s }\n", done);
  free(lob.s); free(hib.s);
}

/* Evaluate G = \self.\p1..\pk. body into the unit (specialised to `known`); its index, or -1. */
static int compile_body_spec(int G, Env *outer, V **known) {
  int params[sizeof(unsigned) * 8]; Port body;
  int ar = fun_params(G, params, N_OF(params), &body);
  for (int i = 0; i < nfun; i++) if (funs[i].lam == G && known_eq(funs[i].known, known, ar)) return i;
  /* (the net holds one copy of a definition per use, so a program applying a library function in five places
     reaches five copies of everything under it; the bound is against mutual recursion re-copying for ever) */
  if (nfun >= 4 * LIN_INT_BITS) { fail("too many functions in one unit"); return -1; }
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
  /* (the call's kind is its function's: a recursive predicate's result is a condition, and `if` on it picks a
     branch rather than taking data apart -- known once the body is, which it is unless this is a call of
     itself from inside) */
  V *s = mkv(V_SYM); s->e = mke(E_CALL, funs[fid].body && funs[fid].body->kind == 3 ? 3 : 1); s->e->k = fid; s->e->nargs = ar; s->e->args = A(sizeof(Expr *) * (size_t)ar);
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
static Shape shape_of(const Expr *e);
static int contains(const Expr *e, const Expr *x, int depth);
static int64_t ctor_id(const LinCtor *ci);
static Shape shape_of(const Expr *e);
static Shape *sh_memo; static unsigned *sh_gen, sh_g; static int sh_cap;
/* One drop (and copy) function per SHAPE of data dropped -- a list of numbers frees its cells; a list of lists
   frees its cells and the lists in them -- not per datatype. */
static Shape *drop_sh; static int ndrop, drop_cap;
static int drop_fn(Shape sh) {
  sh.k = 5;
  for (int i = 0; i < ndrop; i++) if (drop_sh[i].dt == sh.dt && drop_sh[i].a == sh.a) return i;
  if (ndrop >= drop_cap) drop_sh = realloc(drop_sh, sizeof *drop_sh * (size_t)(drop_cap = drop_cap ? drop_cap * 2 : 8));
  drop_sh[ndrop] = sh; return ndrop++;
}
static void tail_uses(const Expr *e, unsigned *n);
static int fun_reads(int h);
static int rc_borrowed(int g, int k); static unsigned char **rc_bor; static int rc_held(const Expr *a, int f);
static int contains(const Expr *e, const Expr *x, int depth);
static int ho_f;
/* REFERENCE COUNTING.  Every block carries a count (see lin_alloc); who takes, moves and releases references is
   decided by ONE pass over explicit names (MEMORY), and uniqueness, tested as the program runs, alone licenses
   rebuilding in place (REUSE).  What follows decides which parameters are only lent (BORROWED PARAMETERS). */
static int rc_imm(const Expr *a) { return a->op == E_CONST || (a->op == E_CTOR && !a->nargs); }
/* (vectors) an element read from a vector is held by it, as a field is by its block; the operations that make a
   vector hand back a reference of their own; and which operands an operation consumes (the rest it reads) */
static int vop_read(const Expr *a) { return a && a->op == E_VOP && (a->k == LIN_VOP_GET || a->k == LIN_VOP_LEN); }
static int vop_takes(const Expr *e, int i) {
  if (e->op != E_VOP) return 0;
  switch (e->k) { case LIN_VOP_NEW: return i == 1; case LIN_VOP_SET: return i == 0 || i == 2; case LIN_VOP_PUSH: return 1; }
  return 0;
}
static int rc_seen_cap;                              /* (the nodes the walk's `seen` covers) */
static int indexed_pick(const Expr *e, const Expr **K, const Expr **S, int64_t *off);
/* BORROWED PARAMETERS.  A function that only READS a parameter -- takes it apart without rebuilding in it, reads
   its fields, lends it on to a parameter that is itself borrowed -- need not own it: its caller lends it, with no
   reference taken for the call and none released in the callee.  A loop over a structure it does not change
   (`(sum a i n s)`, a lookup down a tree) then touches no count at all, and threads reading one structure write
   nothing to it.  A parameter is borrowed until some use needs it owned: handed on whole (a path's value, a
   field stored, a parameter that owns), rebuilt in, or captured by another function.  And a TAIL call stays one:
   a call a path ends with that hands an owned value to a parameter makes that parameter owned -- or the caller
   would have to release the value after the call returns, and a loop would become a recursion. */
static int rc_borrowed(int g, int k) { return rc_bor && g >= 0 && g < nfun && k >= 0 && k < funs[g].arity && rc_bor[g][k]; }
static int rc_held(const Expr *a, int f) {           /* a value f holds without owning it: what it was lent, or a part of that */
  if (!a) return 0;
  if (a->op == E_PARAM) return a->nargs != f || rc_borrowed(f, (int)a->k);
  if (a->op == E_FIELD) return rc_held(a->a, f);
  { const Expr *K, *S; int64_t off; if (a->op == E_IF && indexed_pick(a, &K, &S, &off)) return rc_held(S, f); }
  return 0;
}
static int rcb_changed;
/* A TRAVERSED PARAMETER -- one the function recurses on through its parts, `(_addc xs ys 0)` passing a field of b to
   b -- stays borrowed though some path hands it on whole to an owner: owned, every step of the traversal would take a
   count of the rest and release the cell whenever the caller still holds it; borrowed, the path that hands it on
   takes one count, once. */
static int trav_base(const Expr *e, int f, int64_t k) {
  if (!e || e->op != E_FIELD) return 0;
  while (e && e->op == E_FIELD) e = e->a;
  return e && e->op == E_PARAM && e->nargs == f && e->k == k;
}
static int trav_r(const Expr *e, int f, int64_t k, unsigned char *seen) {
  if (!e || (e->id < rc_seen_cap && seen[e->id])) return 0;
  if (e->id < rc_seen_cap) seen[e->id] = 1;
  if (e->op == E_CALL && e->k == f && k < e->nargs && trav_base(e->args[k], f, k)) return 1;
  if (trav_r(e->a, f, k, seen) || trav_r(e->b, f, k, seen) || (e->op != E_CTOR && trav_r(e->c, f, k, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (trav_r(e->args[i], f, k, seen)) return 1;
  return 0;
}
static int traversed(int f, int64_t k) {
  if (f < 0 || f >= nfun || !funs[f].body) return 0;
  unsigned char *seen = calloc((size_t)rc_seen_cap + 1, 1); int r = trav_r(funs[f].body, f, k, seen); free(seen); return r;
}
static const char *rcb_why; static int rcb_in;
static int mr_tok_can(const Expr *e, int words); static const LinCtor *rc_arm_ci(const Expr *m, int i);
static void rcb_own(int g, int k) { if (rc_borrowed(g, k)) { if (dbg > 2) DBG("[counted: f%d's parameter %d is owned: %s in f%d]\n", g, k, rcb_why, rcb_in); rc_bor[g][k] = 0; rcb_changed = 1; } }
/* the uses of f's parameters in e that need them owned (parent: how e is used -- 1: read, 0: handed on) */
static void rcb_walk(const Expr *e, int f, int read, unsigned char *seen) {
  if (!e) return;
  if (e->op == E_PARAM) { if (!read && e->nargs >= 0 && e->nargs < nfun) { rcb_why = "handed on whole"; rcb_in = f; rcb_own(e->nargs, (int)e->k); } return; }
  if (e->op == E_CONST) return;
  if (e->id < rc_seen_cap) { int bit = read ? 1 : 2; if (seen[e->id] & bit) return; seen[e->id] |= bit; }
  switch (e->op) {
  case E_FIELD: rcb_walk(e->a, f, 1, seen); return;
  case E_MATCH:
    /* (a parameter taken apart where an arm can build its tail in the block is OWNED: borrowed, the block is the
       caller's, and every rebuild would copy it -- see REUSE) */
    if (e->a->op == E_PARAM && e->a->nargs == f && f >= 0)
      for (int i = 0; i < e->nargs; i++) { const LinCtor *ac = rc_arm_ci(e, i);
        if (ac && ac->k > 0 && mr_tok_can(e->args[i], ac->k + !e->untag)) { rcb_why = "rebuilt in"; rcb_in = f; rcb_own(f, (int)e->a->k); break; } }
    rcb_walk(e->a, f, 1, seen); for (int i = 0; i < e->nargs; i++) rcb_walk(e->args[i], f, read, seen); return;
  case E_IF: {
    const Expr *K, *S; int64_t off;
    if (indexed_pick(e, &K, &S, &off)) { rcb_walk(K, f, 1, seen); rcb_walk(S, f, 1, seen); return; }   /* (a field read) */
    rcb_walk(e->a, f, 1, seen); rcb_walk(e->b, f, read, seen); rcb_walk(e->c, f, read, seen); return; }
  case E_BIN: rcb_walk(e->a, f, 1, seen); rcb_walk(e->b, f, 1, seen); return;
  case E_VOP: for (int i = 0; i < e->nargs; i++) rcb_walk(e->args[i], f, !vop_takes(e, i), seen); return;
  case E_CALL:
    for (int i = 0; i < e->nargs; i++) {
      const Expr *a = e->args[i];
      int rd = e->k >= 0 && e->k < nfun && rc_borrowed((int)e->k, i);
      if (!rd && a->op == E_PARAM && a->nargs == f && traversed(f, a->k)) rd = 1;   /* (see A TRAVERSED PARAMETER) */
      rcb_walk(a, f, rd, seen);
    }
    return;
  case E_CTOR: if (e->c) rcb_walk(e->c, f, 0, seen); for (int i = 0; i < e->nargs; i++) rcb_walk(e->args[i], f, 0, seen); return;
  default:
    rcb_walk(e->a, f, 0, seen); rcb_walk(e->b, f, 0, seen); rcb_walk(e->c, f, 0, seen);
    for (int i = 0; i < e->nargs && e->args; i++) rcb_walk(e->args[i], f, 0, seen);
  }
}
static void rcb_tails(const Expr *e, int f) {        /* the calls f's paths end with: an owned value handed there is owned there */
  if (!e) return;
  { const Expr *K, *S; int64_t off; if (e->op == E_IF && indexed_pick(e, &K, &S, &off)) return; }
  if (e->op == E_IF) { rcb_tails(e->b, f); rcb_tails(e->c, f); return; }
  if (e->op == E_MATCH) { for (int i = 0; i < e->nargs; i++) rcb_tails(e->args[i], f); return; }
  if (e->op == E_CALL && e->k >= 0 && e->k < nfun)
    for (int i = 0; i < e->nargs && i < funs[e->k].arity; i++)
      if (rc_borrowed((int)e->k, i) && !rc_held(e->args[i], f) && !rc_imm(e->args[i])
          && !traversed((int)e->k, i))   /* (one handed a fresh value on a path stays borrowed: that call is not a tail call, its traversal's are) */
        { rcb_why = "given a fresh value by a tail call"; rcb_in = f; rcb_own((int)e->k, i); }
}
/* READ ALL THE WAY DOWN: a borrowed parameter of which nothing -- neither it nor any part of it -- is ever given a
   count: only taken apart, its fields read, and lent on to a parameter read the same way.  A thread handed such a
   value touches no count of it, so it need not be marked shared (rc_share_params). */
static unsigned char **rc_pure;
static int rc_is_pure(int g, int k) { return rc_pure && g >= 0 && g < nfun && k >= 0 && k < funs[g].arity && rc_pure[g][k]; }
static int rcp_root(const Expr *e) {                 /* the parameter (index) a data value is a part of, or -1 */
  for (;;) {
    if (!e) return -1;
    if (e->op == E_PARAM) return (int)e->k + 1;     /* (+1: 0 is "none") */
    if (e->op == E_FIELD) { e = e->a; continue; }
    if (vop_read(e) && e->k == LIN_VOP_GET) { e = e->args[0]; continue; }
    const Expr *K, *S; int64_t off;
    if (e->op == E_IF && indexed_pick(e, &K, &S, &off)) { e = S; continue; }
    return 0;
  }
}
static void rcp_walk(const Expr *e, int f, int ok_here, unsigned char *seen) {   /* ok_here: e is used where a read is all */
  if (!e) return;
  int r = rcp_root(e);
  if (r > 0 && e->op == E_PARAM && e->nargs != f) r = 0;   /* (a captured value: its own function's) */
  if (r > 0 && !ok_here && shape_of(e).k != 1 && shape_of(e).k != 3 && rc_is_pure(f, r - 1)) { rc_pure[f][r - 1] = 0; rcb_changed = 1; }
  if (e->op == E_PARAM || e->op == E_CONST) return;
  if (e->id < rc_seen_cap) { int bit = ok_here ? 1 : 2; if (seen[e->id] & bit) return; seen[e->id] |= bit; }
  if (e->op == E_FIELD) { rcp_walk(e->a, f, 1, seen); return; }
  { const Expr *K, *S; int64_t off; if (e->op == E_IF && indexed_pick(e, &K, &S, &off)) { rcp_walk(K, f, 1, seen); rcp_walk(S, f, 1, seen); return; } }
  switch (e->op) {
  case E_MATCH: rcp_walk(e->a, f, 1, seen); for (int i = 0; i < e->nargs; i++) rcp_walk(e->args[i], f, ok_here, seen); return;
  case E_IF: rcp_walk(e->a, f, 1, seen); rcp_walk(e->b, f, ok_here, seen); rcp_walk(e->c, f, ok_here, seen); return;
  case E_BIN: rcp_walk(e->a, f, 1, seen); rcp_walk(e->b, f, 1, seen); return;
  case E_VOP: for (int i = 0; i < e->nargs; i++) rcp_walk(e->args[i], f, !vop_takes(e, i), seen); return;
  case E_CALL: for (int i = 0; i < e->nargs; i++) rcp_walk(e->args[i], f, e->k >= 0 && e->k < nfun && rc_is_pure((int)e->k, i), seen); return;
  default:
    if (e->op == E_CTOR && e->c) rcp_walk(e->c, f, 0, seen);
    rcp_walk(e->a, f, 0, seen); rcp_walk(e->b, f, 0, seen); if (e->op != E_CTOR) rcp_walk(e->c, f, 0, seen);
    for (int i = 0; i < e->nargs && e->args; i++) rcp_walk(e->args[i], f, 0, seen);
  }
}
static void rc_borrow(Expr *entry) {
  rc_bor = A(sizeof *rc_bor * (size_t)(nfun ? nfun : 1));
  for (int g = 0; g < nfun; g++) {
    int a = funs[g].arity ? funs[g].arity : 1; rc_bor[g] = A((size_t)a); memset(rc_bor[g], 0, (size_t)a);
    for (int k = 0; k < funs[g].arity; k++) {
      const Expr *p = funs[g].pnode ? funs[g].pnode[k] : NULL;
      if (p && funs[g].body) { Shape ps = shape_of(p); rc_bor[g][k] = ps.k == 5 && ps.dt; }
    }
  }
  rc_seen_cap = eid;
  do {
    rcb_changed = 0;
    for (int g = -1; g < nfun; g++) {
      const Expr *b = g < 0 ? entry : funs[g].body; if (!b) continue;
      unsigned char *seen = calloc((size_t)eid + 1, 1);
      rcb_walk(b, g, 0, seen); free(seen);
      if (g >= 0) rcb_tails(b, g);
    }
  } while (rcb_changed);
  rc_pure = A(sizeof *rc_pure * (size_t)(nfun ? nfun : 1));
  for (int g = 0; g < nfun; g++) { int a = funs[g].arity ? funs[g].arity : 1; rc_pure[g] = A((size_t)a); memcpy(rc_pure[g], rc_bor[g], (size_t)a); }
  do {
    rcb_changed = 0;
    for (int g = 0; g < nfun; g++) {
      if (!funs[g].body) continue;
      unsigned char *seen = calloc((size_t)eid + 1, 1); rcp_walk(funs[g].body, g, 0, seen); free(seen);
    }
  } while (rcb_changed);
  for (int g = 0; g < nfun; g++) for (int k = 0; k < funs[g].arity; k++)
    if (rc_pure[g][k] && dbg > 1) DBG("[counted: f%d's parameter %d is read all the way down]\n", g, k);
  /* (a parameter another function captured is that function's to read as long as it runs: owned here) */
  for (int g = 0; g < nfun; g++) for (int k = 0; k < funs[g].arity; k++)
    if (rc_bor[g][k] && dbg > 1) DBG("[counted: f%d's parameter %d is borrowed]\n", g, k);
}
static Expr *fu_clone(const Expr *e);
static Expr *vcopy(const Expr *e, int from, int to, Expr **memo, int memo_n) {   /* the body, its parameters to's */
  if (!e) return NULL;
  if (e->op == E_PARAM && e->nargs == from) return funs[to].pnode[e->k];
  if (e->id < memo_n && memo[e->id]) return memo[e->id];
  Expr *x = fu_clone(e);
  x->a = vcopy(e->a, from, to, memo, memo_n); x->b = vcopy(e->b, from, to, memo, memo_n);
  x->c = e->op == E_CTOR ? e->c : vcopy(e->c, from, to, memo, memo_n);
  if (e->nargs && e->args) { x->args = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) x->args[i] = vcopy(e->args[i], from, to, memo, memo_n); }
  x = hc(x);
  if (e->id < memo_n) memo[e->id] = x;
  return x;
}
static int reads_param_of(const Expr *e, int f, unsigned char *seen) {   /* a parameter of f read here? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_PARAM) return e->nargs == f;
  if (reads_param_of(e->a, f, seen) || reads_param_of(e->b, f, seen) || (e->op != E_CTOR && reads_param_of(e->c, f, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (reads_param_of(e->args[i], f, seen)) return 1;
  return 0;
}
static int reads_outer_r(const Expr *e, int f, unsigned char *seen) {   /* a parameter of another function read here? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_PARAM) return e->nargs != f;
  if (reads_outer_r(e->a, f, seen) || reads_outer_r(e->b, f, seen) || (e->op != E_CTOR && reads_outer_r(e->c, f, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (reads_outer_r(e->args[i], f, seen)) return 1;
  return 0;
}
static int reads_outer(int f) {                    /* f reads another's parameters, or another reads f's */
  unsigned char *seen = calloc((size_t)eid + 1, 1); int r = reads_outer_r(funs[f].body, f, seen);
  for (int g = 0; !r && g < nfun; g++) { if (g == f || !funs[g].body) continue; memset(seen, 0, (size_t)eid + 1); r = reads_param_of(funs[g].body, f, seen); }
  free(seen); return r;
}
static Shape unit_shapes(const Expr *entry);
static Shape unit_shapes(const Expr *entry);
/* MEMORY.  One rule set, over the tree EXPLICIT BINDING makes (Perceus: Reinking, Xie, de Moura, Leijen 2021).
   Every value a block word holds is a reference, and every reference has one owner.
   - A NAME is a parameter, a let, or (in an arm that takes its scrutinee apart: below) a field.  A borrowed
     parameter (rc_borrowed) is the caller's; every other name is owned by the code that binds it.
   - Every expression that is not a name yields a reference of its own.  Where its value is only read -- a
     borrowed parameter, a vector read, a match -- it is named first (a let around the reader), so that what
     is read is always a name.
   - Liveness is computed backwards.  A name used where its value is taken over (a let, a constructor's field,
     an owned parameter, a vector operation that consumes it, the function's result) MOVES there if nothing
     after uses it, and is DUPLICATED there otherwise.  Operands are evaluated in no fixed order, so a name
     used by two operands of one operation is live across each -- except a name handed WHOLE to a call or a
     constructor, which takes it only once every operand is computed, while the others only read numbers
     from it (`(_mulc m k 0 (alen m) 0)`).
   - A name an operation only reads, and nothing after it uses, is DROPPED when the operation is done
     (E_AFTER).  A name a branch does not use, though the conditional's other branches do, is dropped where
     that branch begins (E_DROP); a let nothing uses, where its body begins; an owned parameter nothing uses,
     where the function begins.
   - MATCH ON A DYING VALUE: an arm of a match on an owned name that the arm does not use whole, and nothing
     after uses, tests the block: shared, it takes a count of each field it uses; it loads those fields; then,
     unique, it frees the block (or keeps it: REUSE) and drops the fields it does not use, and shared, it
     releases the block.  In that arm the fields are owned names -- and a field read is itself a name, so a
     match on a field of such an arm (a nested pattern) takes that block apart the same way.  A name for a field
     of a block nobody in the arm owns is an ALIAS: no reference of its own, its block kept while it is used. */
static int mr_f, mr_par, mr_nv, mr_cap;
static unsigned char *mr_own; static int *mr_dfn, *mr_alias; static Expr **mr_atom; static int *mr_letv, mr_letcap;   /* mr_alias: a borrowed name's block (-1: none) */
typedef struct { const Expr *base; int64_t k; int id; } MrFB;
static MrFB *mr_fb; static int mr_nfb, mr_cfb;
static int mr_newvar(int own, int dfn, Expr *atom) {
  if (mr_nv >= mr_cap) { int c = mr_cap ? mr_cap * 2 : 64;
    mr_own = realloc(mr_own, (size_t)c); mr_dfn = realloc(mr_dfn, sizeof *mr_dfn * (size_t)c); mr_alias = realloc(mr_alias, sizeof *mr_alias * (size_t)c); mr_atom = realloc(mr_atom, sizeof *mr_atom * (size_t)c); mr_cap = c; }
  mr_own[mr_nv] = (unsigned char)(own && dfn >= 0); mr_dfn[mr_nv] = dfn; mr_alias[mr_nv] = -1; mr_atom[mr_nv] = atom; return mr_nv++;
}
static int mr_same_base(const Expr *x, const Expr *y) {   /* one name: the same let's name, or the same parameter */
  if (x == y) return 1;
  if (x && y && x->op == E_FIELD && y->op == E_FIELD) return x->k == y->k && mr_same_base(x->a, y->a);   /* (a field of one block: a name too) */
  return x && y && x->op == E_PARAM && y->op == E_PARAM && x->nargs == y->nargs && x->k == y->k;
}
static int mr_letid(const Expr *let) { return let && let->k >= 0 && let->k < mr_letcap ? mr_letv[let->k] : -1; }
static int mr_fid(const Expr *e) {                   /* a field of an arm's own: its name */
  for (int i = mr_nfb - 1; i >= 0; i--) if (mr_fb[i].k == e->k && mr_same_base(mr_fb[i].base, e->a)) return mr_fb[i].id;
  return -1;
}
static int mr_id(const Expr *e) {
  if (!e) return -1;
  if (e->op == E_PARAM) return e->nargs == mr_f && e->k < mr_par ? (int)e->k : -1;
  if (e->op == E_VAR) return mr_letid(e->bind);
  if (e->op == E_FIELD) return mr_fid(e);
  return -1;
}
static int mr_atomic(const Expr *e) { return e->op == E_PARAM || e->op == E_VAR || e->op == E_CONST || e->op == E_FIELD; }
static int mr_data(const Expr *e);
/* (a vector's element read is what a field read is: a reference the VECTOR holds, not one of its own) */
static int mr_elemread(const Expr *e) {           /* (of a NAMED vector: one computed for the read dies at it, and its element is taken first) */
  return e->op == E_VOP && e->k == LIN_VOP_GET && mr_data(e) && e->nargs && mr_atomic(e->args[0]);
}
static int mr_dfn_of(const Expr *e) { Shape s = shape_of(e); return s.k == 5 && s.dt ? drop_fn(s) : -1; }
static int mr_data(const Expr *e) { return mr_dfn_of(e) >= 0; }
static unsigned char *mr_set(void) { return calloc((size_t)mr_cap + 1, 1); }
static unsigned char *mr_grow(unsigned char *x, int had) { unsigned char *y = calloc((size_t)mr_cap + 1, 1); memcpy(y, x, (size_t)had); free(x); return y; }
static void mr_uses(const Expr *e, unsigned char *u) {   /* the names e reads (its tree) */
  if (!e) return;
  int id = mr_id(e);
  if (id >= 0) { u[id] = 1; if (mr_alias[id] >= 0) u[mr_alias[id]] = 1; return; }
  if (e->op == E_FIELD) { mr_uses(e->a, u); return; }
  if (e->op == E_CALL && e->k >= 0 && e->k < lifted) for (int i = 0; i < nfv[e->k]; i++) if (fvs[e->k][i].h == mr_f && fvs[e->k][i].k < mr_par) u[fvs[e->k][i].k] = 1;
  if (e->op == E_DROP) for (const struct Drop *d = e->drops; d; d = d->next) mr_uses(d->p, u);
  mr_uses(e->a, u); mr_uses(e->b, u); if (e->op != E_CTOR) mr_uses(e->c, u);
  for (int i = 0; i < e->nargs && e->args; i++) mr_uses(e->args[i], u);
}
static Expr *mr_wrap(int op, Expr *inner, const unsigned char *ids, int n) {   /* E_DROP (ids; inner) or E_AFTER (inner; ids) */
  struct Drop *dl = NULL;
  for (int x = 0; x < n; x++) if (ids[x]) { struct Drop *d = A(sizeof *d); d->p = mr_atom[x]; d->fn = mr_dfn[x]; d->next = dl; dl = d; }
  if (!dl) return inner;
  Expr *w = mke(op, inner->kind); w->drops = dl;
  if (op == E_DROP) w->b = inner; else w->a = inner;
  return w;
}
static int mr_whole(const Expr *e, const Expr *s) {  /* s used other than as the block its fields are read from */
  if (!e) return 0;
  if (mr_same_base(e, s)) return 1;                  /* (s itself, a name -- or a field read, when s is one) */
  if (e->op == E_FIELD) return e->a != s && !mr_same_base(e->a, s) ? mr_whole(e->a, s) : 0;
  if (e->op == E_CALL && s->op == E_PARAM && e->k >= 0 && e->k < lifted && fv_has((int)e->k, s->nargs, s->k)) return 1;
  if (e->op == E_DROP) for (const struct Drop *d = e->drops; d; d = d->next) if (mr_whole(d->p, s)) return 1;
  if (mr_whole(e->a, s) || mr_whole(e->b, s) || (e->op != E_CTOR && mr_whole(e->c, s))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (mr_whole(e->args[i], s)) return 1;
  return 0;
}
static void mr_fields(const Expr *e, const Expr *s, unsigned char *ks, int nk) {   /* the fields of s an arm reads */
  if (!e) return;
  if (e->op == E_FIELD && mr_same_base(e->a, s) && e->k >= 0 && e->k < nk) ks[e->k] = 1;
  mr_fields(e->a, s, ks, nk); mr_fields(e->b, s, ks, nk); if (e->op != E_CTOR) mr_fields(e->c, s, ks, nk);
  for (int i = 0; i < e->nargs && e->args; i++) mr_fields(e->args[i], s, ks, nk);
}
static int mr_reads_only(const Expr *e, int x, const Expr *parent) {   /* every use of x in e reads a number from it */
  if (!e) return 1;
  if (mr_id(e) == x) return parent && ((vop_read(parent) && parent->args[0] == e) || (parent->op == E_FIELD && parent->a == e)) && !mr_data(parent);
  if (e->op == E_FIELD && mr_id(e->a) == x) return !mr_data(e);
  if (e->op == E_CALL && e->k >= 0 && e->k < lifted && x < mr_par) for (int i = 0; i < nfv[e->k]; i++) if (fvs[e->k][i].h == mr_f && fvs[e->k][i].k == x) return 0;
  if (!mr_reads_only(e->a, x, e) || !mr_reads_only(e->b, x, e) || (e->op != E_CTOR && !mr_reads_only(e->c, x, e))) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!mr_reads_only(e->args[i], x, e)) return 0;
  return 1;
}
static int mr_argown(const Expr *e, int i) {        /* does this operand's value go to e (else e only reads it) */
  if (e->op == E_CALL) return !(e->k >= 0 && e->k < nfun && rc_borrowed((int)e->k, i));
  if (e->op == E_CTOR) return 1;
  if (e->op == E_VOP) return vop_takes(e, i);
  return 0;
}
static Expr *mr(Expr *e, int octx, const unsigned char *A, unsigned char *B);
static int mr_ntok, mr_ctok; static int mr_tok_can(const Expr *e, int words); static int mr_tok_mark(Expr **slot, int t, int words, int *used);   /* (see REUSE) */
static Expr *mr_ops(Expr *e, int octx, const unsigned char *A, unsigned char *B) {   /* an operation over operands */
  /* operands: (slot, owned?) -- BIN: a, b; others: args (a constructor's dead fields are never computed) */
  int no = e->op == E_BIN ? 2 : e->nargs;
  Expr **slot[no ? no : 1]; int own[no ? no : 1], n = 0;
  if (e->op == E_BIN) { slot[n] = &e->a; own[n++] = 0; slot[n] = &e->b; own[n++] = 0; }
  else for (int i = 0; i < e->nargs; i++) { if (e->op == E_CTOR && e->ci && !field_live(e->ci, i)) continue; slot[n] = &e->args[i]; own[n++] = mr_argown(e, i); }
  /* a value only read that is not a name: named first (see MEMORY) */
  for (int i = 0; i < n; i++) {
    Expr *a = *slot[i];
    if (own[i] || mr_atomic(a) || mr_elemread(a) || !mr_data(a)) continue;
    Expr *l = anf_let(a); l->a = a; *slot[i] = anf_var(l); l->b = e;
    if (l->k >= mr_letcap) { int c = l->k * 2 + 64; mr_letv = realloc(mr_letv, sizeof *mr_letv * (size_t)c); for (int j = mr_letcap; j < c; j++) mr_letv[j] = -1; mr_letcap = c; }
    return mr(l, octx, A, B);
  }
  unsigned char **U = malloc(sizeof *U * (size_t)(n + 1));
  for (int i = 0; i <= n; i++) U[i] = mr_set();
  for (int i = 0; i < n; i++) mr_uses(*slot[i], U[i]);
  if (e->op == E_CALL && e->k >= 0 && e->k < lifted)   /* (a callee reading a parameter lifted: read for the call) */
    for (int q = 0; q < nfv[e->k]; q++) if (fvs[e->k][q].h == mr_f && fvs[e->k][q].k < mr_par) U[n][fvs[e->k][q].k] = 1;
  int nv0 = mr_nv;
  int *mvbr = calloc((size_t)mr_cap + 1, sizeof *mvbr);   /* (the operand a name handed whole moves into, + 1) */
  for (int x = 0; x < nv0; x++) {                    /* (see MEMORY: handed whole, read beside) */
    int c = 0, whole = -1; for (int i = 0; i <= n; i++) if (U[i][x]) c++;
    if (c < 2 || !mr_own[x] || A[x] || !(e->op == E_CALL || e->op == E_CTOR) || U[n][x]) continue;
    for (int i = 0; i < n; i++) if (own[i] && mr_id(*slot[i]) == x) whole = i;   /* (the last: the others take counts) */
    if (whole < 0) continue;
    int ok = 1; for (int i = 0; i < n && ok; i++) if (i != whole && U[i][x]) ok = (own[i] && mr_id(*slot[i]) == x) || mr_reads_only(*slot[i], x, NULL);
    if (ok) mvbr[x] = whole + 1;
  }
  unsigned char *Bacc = mr_set(); memcpy(Bacc, A, (size_t)nv0);
  for (int i = 0; i < n; i++) {
    unsigned char *Ai = mr_set(); memcpy(Ai, A, (size_t)nv0);
    for (int j = 0; j <= n; j++) if (j != i) for (int x = 0; x < nv0; x++) if (U[j][x]) Ai[x] = 1;
    if (mr_id(*slot[i]) >= 0 && mvbr[mr_id(*slot[i])] == i + 1) Ai[mr_id(*slot[i])] = 0;   /* (it moves here) */
    unsigned char *Bi = mr_set();
    *slot[i] = mr(*slot[i], own[i], Ai, Bi);
    if (mr_nv > nv0) { Bacc = mr_grow(Bacc, nv0 + 0); }
    for (int x = 0; x < mr_nv && x < mr_cap; x++) if (Bi[x]) Bacc[x] = 1;
    free(Ai); free(Bi);
  }
  for (int x = 0; x < nv0; x++) if (U[n][x]) Bacc[x] = 1;
  /* the names that die HERE: read by this operation (or by two operands), and not used after it */
  unsigned char *D = mr_set();
  for (int x = 0; x < nv0; x++) {
    if (!mr_own[x] || A[x] || mvbr[x]) continue;
    int c = 0, at = -1; for (int i = 0; i <= n; i++) if (U[i][x]) { c++; at = i; }
    if (!c) continue;
    if (c >= 2) { D[x] = 1; continue; }
    if (at == n) { D[x] = 1; continue; }         /* (read by the callee, lifted) */
    const Expr *a = *slot[at];
    while (a->op == E_DUP) a = a->a;
    if (mr_id(a) == x && !own[at]) D[x] = 1;       /* (read here) */
    else if (a->op == E_FIELD && mr_id(a) != x && mr_id(a->a) == x) D[x] = 1;   /* (a field of it read here) */
  }
  memcpy(B, Bacc, (size_t)mr_cap);
  Expr *r = mr_wrap(E_AFTER, e, D, nv0);
  for (int i = 0; i <= n; i++) free(U[i]); free(U); free(mvbr); free(Bacc); free(D);
  return r;
}
/* (a block of an enclosing arm, owned and dying there, but used whole in it: taken apart in the first branch
   where it is not -- the path of `pull` that builds a new body, beside the one that returns the old) */
typedef struct { const Expr *sc; int sid; const LinCtor *ac; int untag; } MrPend;
static MrPend *mr_pend; static int mr_npend, mr_cpend;
static Expr *mr_spec(Expr *body, const Expr *sc, int sid, const LinCtor *ac, int untag, int octx, const unsigned char *A, unsigned char *B) {
  int nk = ac->k, fb0 = mr_nfb;
  unsigned char *ks = calloc((size_t)nk + 1, 1); mr_fields(body, sc, ks, nk);
  int *fid = malloc(sizeof *fid * (size_t)(nk + 1));
  Shape ss = shape_of(sc);
  for (int k = 0; k < nk; k++) {
    fid[k] = -1; if (!ks[k]) continue;
    Expr *fa = mke(E_FIELD, 1); fa->a = (Expr *)sc; fa->k = k; fa->ci = ac; fa->untag = untag;
    fid[k] = mr_newvar(1, rc_fdrop(ac, k, ss), fa);
    if (mr_nfb == mr_cfb) mr_fb = realloc(mr_fb, sizeof *mr_fb * (size_t)(mr_cfb = mr_cfb ? mr_cfb * 2 : 16));
    mr_fb[mr_nfb++] = (MrFB){ sc, k, fid[k] };
  }
  for (int q = 0; q < mr_npend; q++) if (mr_pend[q].sid == sid) mr_pend[q].sid = -1 - sid;   /* (taken apart here: not again inside) */
  body = mr(body, octx, A, B);
  for (int q = 0; q < mr_npend; q++) if (mr_pend[q].sid == -1 - sid) mr_pend[q].sid = sid;
  Expr *sp = mke(E_SPEC, body->kind); sp->a = (Expr *)sc; sp->b = body; sp->ci = ac; sp->untag = untag; sp->k = -1;
  sp->mspec = calloc(1, sizeof *sp->mspec); sp->mspec[0] = calloc((size_t)nk + 1, 1);
  for (int k = 0; k < nk; k++) if (fid[k] >= 0) { if (B[fid[k]]) sp->mspec[0][k] = 1; B[fid[k]] = 0; }
  B[sid] = 1;                                        /* (the block is used here: it is taken apart) */
  if (mr_tok_can(body, nk + !untag)) {             /* (see REUSE) its token */
    int t = mr_ntok, used = 0;
    if (mr_ntok == mr_ctok) { mr_ctok = mr_ctok ? mr_ctok * 2 : 16; mr_tokw = realloc(mr_tokw, sizeof *mr_tokw * (size_t)mr_ctok); mr_tokb = realloc(mr_tokb, sizeof *mr_tokb * (size_t)mr_ctok); }
    mr_tokb[mr_ntok] = sc; mr_tokw[mr_ntok++] = nk + !untag;
    mr_tok_mark(&sp->b, t, nk + !untag, &used);
    sp->k = t;
  }
  mr_nfb = fb0; free(ks); free(fid);
  return sp;
}
static Expr *mr_branch(Expr *br, int octx, const unsigned char *A, unsigned char *B, int *spec_sid) {
  *spec_sid = -1;
  for (int q = mr_npend - 1; q >= 0; q--) {
    MrPend p = mr_pend[q];
    if (p.sid < 0 || A[p.sid] || mr_whole(br, p.sc)) continue;
    *spec_sid = p.sid;
    return mr_spec(br, p.sc, p.sid, p.ac, p.untag, octx, A, B);
  }
  return mr(br, octx, A, B);
}
static Expr *mr(Expr *e, int octx, const unsigned char *A, unsigned char *B) {
  if (!e) { memcpy(B, A, (size_t)mr_cap); return e; }
  switch (e->op) {
  case E_PARAM: case E_VAR: case E_CONST: case E_FIELD: {
    memcpy(B, A, (size_t)mr_cap);
    int id = mr_id(e);
    if (id >= 0) { B[id] = 1; if (mr_alias[id] >= 0) B[mr_alias[id]] = 1; }
    else if (e->op == E_FIELD) { int bid = mr_id(e->a); if (bid >= 0) B[bid] = 1; }
    if (octx && mr_data(e) && !(id >= 0 && mr_own[id] && !A[id])) { Expr *d = mke(E_DUP, e->kind); d->a = e; return d; }
    return e; }
  case E_LET: {
    /* (a name for a value only borrowed -- a field of a block someone else owns -- is an ALIAS: no reference of
       its own, and its block lives while it is used) */
    int vid = mr_atomic(e->a) ? mr_id(e->a) : -1, alias = 0, ablock = -1;
    int fbase = e->a->op == E_FIELD && vid < 0 ? mr_id(e->a->a) : -1;
    if (mr_atomic(e->a) && e->a->op != E_CONST && !(vid >= 0 && mr_own[vid]) && !(fbase >= 0 && mr_own[fbase])) {   /* (not of an owned block: it may be taken apart) */
      alias = 1;
      if (vid >= 0) ablock = mr_alias[vid] >= 0 ? mr_alias[vid] : vid;
      else if (e->a->op == E_FIELD) ablock = mr_id(e->a->a);
    } else if (mr_elemread(e->a) && mr_atomic(e->a->args[0]) && mr_id(e->a->args[0]) >= 0) {   /* (an element: an alias of its vector) */
      int vv = mr_id(e->a->args[0]); alias = 1; ablock = mr_alias[vv] >= 0 ? mr_alias[vv] : vv;
    }
    int x = mr_newvar(!alias, mr_dfn_of(e->a), e->bind);
    if (alias) mr_alias[x] = ablock;
    if (e->k >= mr_letcap) { int c = (int)e->k * 2 + 64; mr_letv = realloc(mr_letv, sizeof *mr_letv * (size_t)c); for (int j = mr_letcap; j < c; j++) mr_letv[j] = -1; mr_letcap = c; }
    mr_letv[e->k] = x;
    unsigned char *Bb = mr_set();
    Expr *body = mr(e->b, octx, A, Bb);
    if (mr_own[x] && !Bb[x]) { unsigned char *one = mr_set(); one[x] = 1; body = mr_wrap(E_DROP, body, one, mr_nv); free(one); }
    Bb[x] = 0;
    unsigned char *Bv = mr_set();
    e->a = mr(e->a, !alias, Bb, Bv); e->b = body;
    for (int i = 0; i < mr_cap; i++) B[i] = Bv[i] | Bb[i];
    free(Bb); free(Bv);
    return e; }
  case E_IF: {
    unsigned char *Bb = mr_set(), *Bc = mr_set(); int sb = -1, sc2 = -1;
    Expr *tb = mr_branch(e->b, octx, A, Bb, &sb), *tc = mr_branch(e->c, octx, A, Bc, &sc2);
    unsigned char *Lin = mr_set(), *db = mr_set(), *dc = mr_set();
    for (int x = 0; x < mr_nv; x++) { Lin[x] = Bb[x] | Bc[x]; db[x] = mr_own[x] && Lin[x] && !Bb[x] && x != sb; dc[x] = mr_own[x] && Lin[x] && !Bc[x] && x != sc2; }
    e->b = mr_wrap(E_DROP, tb, db, mr_nv); e->c = mr_wrap(E_DROP, tc, dc, mr_nv);
    e->a = mr(e->a, 0, Lin, B);
    free(Bb); free(Bc); free(Lin); free(db); free(dc);
    return e; }
  case E_MATCH: {
    const Expr *sc = e->a; int sid = mr_id(sc), na = e->nargs;
    unsigned char **Bi = malloc(sizeof *Bi * (size_t)(na + 1)); int *spec = malloc(sizeof *spec * (size_t)(na + 1));
    for (int i = 0; i < na; i++) {
      const LinCtor *ac = rc_arm_ci(e, i);
      int nk = ac ? ac->k : 0;
      Bi[i] = mr_set(); spec[i] = -1;
      if (sid >= 0 && mr_own[sid] && !A[sid] && nk > 0 && !mr_whole(e->args[i], sc)) {   /* taken apart where the arm begins */
        e->args[i] = mr_spec(e->args[i], sc, sid, ac, e->untag, octx, A, Bi[i]); spec[i] = sid; continue;
      }
      int pushed = 0;                               /* (used whole in the arm: taken apart further in, where it is not) */
      if (sid >= 0 && mr_own[sid] && !A[sid] && nk > 0) {
        if (mr_npend == mr_cpend) mr_pend = realloc(mr_pend, sizeof *mr_pend * (size_t)(mr_cpend = mr_cpend ? mr_cpend * 2 : 8));
        mr_pend[mr_npend++] = (MrPend){ sc, sid, ac, e->untag }; pushed = 1;
      }
      e->args[i] = mr_branch(e->args[i], octx, A, Bi[i], &spec[i]);
      if (pushed) mr_npend--;
    }
    unsigned char *Lin = mr_set();
    for (int i = 0; i < na; i++) for (int x = 0; x < mr_nv; x++) Lin[x] |= Bi[i][x];
    for (int i = 0; i < na; i++) {
      unsigned char *d = mr_set();
      for (int x = 0; x < mr_nv; x++) d[x] = mr_own[x] && Lin[x] && !Bi[i][x] && x != spec[i];
      e->args[i] = mr_wrap(E_DROP, e->args[i], d, mr_nv); free(d);
    }
    memcpy(B, Lin, (size_t)mr_cap);
    if (sid >= 0) B[sid] = 1;
    else if (sc->op == E_FIELD) { int bid = mr_id(sc->a); if (bid >= 0) B[bid] = 1; }
    for (int i = 0; i < na; i++) free(Bi[i]); free(Bi); free(spec); free(Lin);
    return e; }
  case E_CALL: case E_CTOR: case E_VOP: case E_BIN: case E_FOP:
    if (e->op == E_CTOR && !e->nargs) { memcpy(B, A, (size_t)mr_cap); return e; }
    if (mr_elemread(e)) {                            /* (taken over: a count of its own; read: the vector's) */
      Expr *r = mr_ops(e, 0, A, B);
      if (octx) {                                    /* (the count taken before the vector, dying here, goes) */
        Expr **at = r->op == E_AFTER ? &r->a : &r; Expr *d = mke(E_DUP, e->kind); d->a = *at; *at = d;
      }
      return r;
    }
    return mr_ops(e, octx, A, B);
  default: memcpy(B, A, (size_t)mr_cap); return e;
  }
}
/* REUSE.  An arm that takes apart a dying block (MATCH ON A DYING VALUE) keeps the block, when it was unique,
   as a TOKEN rather than freeing it: a constructor of the same size the arm ends with -- on every path its tails
   reach, at most one -- is built in it, and a path that ends otherwise frees it where it begins.  So a match that
   rebuilds what it took apart (an insertion, a map, an update) allocates nothing.  (A constructor an inner arm
   already builds in its own token is that arm's: the inner block is the nearer.) */
static int *mr_tokw, mr_ntok, mr_ctok;               /* each token's block size, in words */
static const Expr **mr_tokb;                         /* and the name of the block it was */
static int mr_tok_can(const Expr *e, int words) {   /* does some tail build a block of this size (in no token yet) */
  switch (e->op) {
  case E_LET: case E_DROP: case E_SPEC: return mr_tok_can(e->b, words);
  case E_IF: { const Expr *K, *S; int64_t off; if (!indexed_pick(e, &K, &S, &off)) return mr_tok_can(e->b, words) || mr_tok_can(e->c, words); break; }
  case E_MATCH: for (int i = 0; i < e->nargs; i++) if (mr_tok_can(e->args[i], words)) return 1; return 0;
  default: break;
  }
  const Expr *c = e->op == E_AFTER ? e->a : e;
  return c->op == E_CTOR && c->nargs && !c->tok && c->nargs + !c->untag == words;
}
static int mr_tok_mark(Expr **slot, int t, int words, int *used) {   /* (returns: some path consumes it) */
  Expr *e = *slot;
  switch (e->op) {
  case E_LET: case E_DROP: case E_SPEC: return mr_tok_mark(&e->b, t, words, used);
  case E_IF: { const Expr *K, *S; int64_t off; if (!indexed_pick(e, &K, &S, &off)) { int a = mr_tok_mark(&e->b, t, words, used); return mr_tok_mark(&e->c, t, words, used) | a; } break; }
  case E_MATCH: { int r = 0; for (int i = 0; i < e->nargs; i++) r |= mr_tok_mark(&e->args[i], t, words, used); return r; }
  default: break;
  }
  Expr *c = e->op == E_AFTER ? e->a : e;
  if (c->op == E_CTOR && c->nargs && !c->tok && c->nargs + !c->untag == words) { c->tok = t + 1; *used = 1; return 1; }
  struct Drop *d = A(sizeof *d); d->p = NULL; d->fn = -2 - t; d->next = NULL;   /* (this path frees it) */
  Expr *w = mke(E_DROP, e->kind); w->drops = d; w->b = e; *slot = w;
  return 0;
}
static int mr_count(const Expr *e) { if (!e) return 0; int n = 1 + mr_count(e->a) + mr_count(e->b) + (e->op != E_CTOR ? mr_count(e->c) : 0); for (int i = 0; i < e->nargs && e->args; i++) n += mr_count(e->args[i]); return n; }
static Expr *mem_rc_body(Expr *body, int f, int arity) {   /* one function's body (f -1: the entry) */
  mr_f = f; mr_par = arity; mr_nv = 0; mr_nfb = 0;
  int want = arity + anf_n + 2 * mr_count(body) + 64;
  if (want > mr_cap) { mr_own = realloc(mr_own, (size_t)want); mr_dfn = realloc(mr_dfn, sizeof *mr_dfn * (size_t)want); mr_alias = realloc(mr_alias, sizeof *mr_alias * (size_t)want); mr_atom = realloc(mr_atom, sizeof *mr_atom * (size_t)want); mr_cap = want; }
  if (anf_n + 64 > mr_letcap) { int c = anf_n * 2 + 64; mr_letv = realloc(mr_letv, sizeof *mr_letv * (size_t)c); mr_letcap = c; }
  for (int j = 0; j < mr_letcap; j++) mr_letv[j] = -1;
  for (int k = 0; k < arity; k++) {
    Expr *pa = mke(E_PARAM, 1); pa->nargs = f; pa->k = k;
    const Expr *pn = f >= 0 && funs[f].pnode ? funs[f].pnode[k] : NULL;
    int dfn = pn ? mr_dfn_of(pn) : -1;
    mr_newvar(f >= 0 && !rc_borrowed(f, k), dfn, pa);
  }
  unsigned char *A0 = mr_set(), *B0 = mr_set();
  body = mr(body, 1, A0, B0);
  unsigned char *d = mr_set(); for (int k = 0; k < arity; k++) d[k] = mr_own[k] && !B0[k];
  body = mr_wrap(E_DROP, body, d, arity);
  free(A0); free(B0); free(d);
  return body;
}
static int pm_cand(int f); static int pm_k;
static void mem_rc(Expr **entry) {
  rc_borrow(*entry);
  /* (a list a parallel map walks is split among threads, each walking a stretch: it is the caller's, never
     consumed along the way -- the cell that ends one stretch holds the head of the next.  Borrowing is always
     safe: a borrowed name used where its value is taken over takes a count) */
  for (int i = 0; i < nfun; i++) if (funs[i].body && pm_cand(i) && pm_k >= 0 && pm_k < funs[i].arity && rc_bor && rc_bor[i]) rc_bor[i][pm_k] = 1;
  for (int i = 0; i < nfun; i++) if (funs[i].body) funs[i].body = mem_rc_body(funs[i].body, i, funs[i].arity);
  *entry = mem_rc_body(*entry, -1, 0);
}

static int has_data(const Expr *e) {               /* (memoised in MM_NUM: call after mm_new(MM_NUM)) */
  if (!e || mm_has(MM_NUM, e)) return 0;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_CTOR || e->op == E_MATCH || e->op == E_FIELD || e->op == E_VOP) return 1;
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
static const ShArgs *sha_intern(int n, const Shape *v);
static Shape sh_mk(const char *dt, int n, const Shape *v);
static void sh_print(Shape s);
static int sh_top(Shape s);
static Shape sh_join(Shape a, Shape b) {
  if (!a.k) return b;
  if (!b.k) return a;
  if (a.k == 5 && b.k == 5 && a.dt == b.dt && a.dt && a.a != b.a) {   /* one datatype: its parameters, joined */
    if (!a.a) return b;
    if (!b.a) return a;
    int n = a.a->n < b.a->n ? a.a->n : b.a->n; Shape *v = calloc((size_t)(n ? n : 1), sizeof *v);
    for (int i = 0; i < n; i++) v[i] = sh_join(a.a->s[i], b.a->s[i]);
    Shape r = sh_mk(a.dt, n, v); free(v); return r;
  }
  if (a.k == b.k && (a.k != 5 || a.dt == b.dt)) return a;
  /* two datatypes in one field: a polymorphic constructor (a Seq of pieces and a Seq of ranges) used at two
     types.  Still a block of SOME datatype, which is all a match needs -- it reads the layout its own
     constructors state; only reading such a value in or out needs to know which */
  if (a.k == 5 && b.k == 5) return (Shape){ 5, NULL };
  return (Shape){ 9, NULL };
}
static int sh_eq(Shape a, Shape b) { return a.k == b.k && a.dt == b.dt && a.a == b.a; }
/* A SHAPE WITH PARAMETERS.  A polymorphic datatype's value says what its parameters hold -- a list of lists of numbers
   is `list(list(num))` -- because a constructor's field whose declared type is a parameter holds a number in one
   value and a list in another (the inner lists' cells and the outer's), and only the value can say which.  The
   parameters are interned (one ShArgs per distinct list), so shapes still compare by pointer; they live for the
   run, since a compiled unit reads its results back by them.  Nesting deeper than SHAPE_DEPTH forgets the
   parameters (a function that wraps its argument once per call would otherwise grow a shape for ever). */
#define SHAPE_DEPTH 6
static ShArgs **sha_tab; static int sha_n, sha_cap;
static int sh_depth(Shape s) {
  int d = 0;
  if (s.a) for (int i = 0; i < s.a->n; i++) { int x = sh_depth(s.a->s[i]); if (x > d) d = x; }
  return s.a ? d + 1 : 0;
}
static const ShArgs *sha_intern(int n, const Shape *v) {
  int any = 0; for (int i = 0; i < n; i++) any |= v[i].k != 0;
  if (!any) return NULL;
  for (int t = 0; t < sha_n; t++) {
    const ShArgs *x = sha_tab[t]; if (x->n != n) continue;
    int eq = 1; for (int i = 0; i < n && eq; i++) eq = sh_eq(x->s[i], v[i]);
    if (eq) return x;
  }
  ShArgs *x = malloc(sizeof *x + sizeof *v * (size_t)n); x->n = n; memcpy(x->s, v, sizeof *v * (size_t)n);
  if (sha_n == sha_cap) sha_tab = realloc(sha_tab, sizeof *sha_tab * (size_t)(sha_cap = sha_cap ? sha_cap * 2 : 64));
  sha_tab[sha_n++] = x; return x;
}
static Shape sh_mk(const char *dt, int n, const Shape *v) {
  Shape r = { 5, dt, n > 0 ? sha_intern(n, v) : NULL };
  if (sh_depth(r) > SHAPE_DEPTH) r.a = NULL;
  return r;
}
static const char *list_dt(void) { const LinCtor *c = lin_ctor_info(lin_list_cons_id); return c ? c->dt : NULL; }
static const char *dt_named(const char *name, size_t len) {   /* the registry's (interned) name of a datatype */
  const LinCtor *c;
  for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt && strlen(c->dt) == len && !strncmp(c->dt, name, len)) return c->dt;
  return NULL;
}
static int dt_nparams(const char *dt) {              /* how many type parameters its constructors' fields name */
  int n = 0; const LinCtor *c;
  if (dt == VEC_DT) return 1;                        /* (its elements) */
  for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->fdesc)
    for (const char *d = c->fdesc; (d = strchr(d, 'P')); d++) { int i = atoi(d + 1); if (i + 1 > n) n = i + 1; }
  return n;
}
/* A field's declared type (a descriptor: lin.h) read against the parameters' shapes: what that field holds. */
static Shape desc_shape(const char **d, const Shape *pa, int np) {
  const char *p = *d;
  if (!p || !*p) return (Shape){ 0, NULL, NULL };
  switch (*p) {
  case 'N': case 'F': *d = p + 1; return (Shape){ 1, NULL, NULL };
  case 'B': *d = p + 1; return (Shape){ 3, NULL, NULL };
  case 'P': { int i = atoi(p + 1); *d = fd_skip(p); return pa && i < np ? pa[i] : (Shape){ 0, NULL, NULL }; }
  case 'L': { *d = p + 1; Shape e = desc_shape(d, pa, np); const char *ldt = list_dt(); return ldt ? sh_mk(ldt, 1, &e) : (Shape){ 5, NULL, NULL }; }
  case 'D': {
    const char *q = strchr(p, '('); if (!q) { *d = p + strlen(p); return (Shape){ 0, NULL, NULL }; }
    const char *dt = dt_named(p + 1, (size_t)(q - p - 1)); int n = dt ? dt_nparams(dt) : 0;
    Shape *v = n ? calloc((size_t)n, sizeof *v) : NULL; int i = 0; q++;
    while (*q && *q != ')') { Shape a = desc_shape(&q, pa, np); if (i < n) v[i] = a; i++; }
    *d = *q == ')' ? q + 1 : q;
    Shape r = dt ? sh_mk(dt, n, v) : (Shape){ 0, NULL, NULL }; free(v); return r;
  }
  default: *d = p + 1; return (Shape){ 0, NULL, NULL };
  }
}
/* ...and the other way: a value of shape v put in a field of that declared type says what the parameters hold. */
static void desc_bind(const char **d, Shape v, Shape *pa, int np, Shape (*join)(Shape, Shape)) {
  const char *p = *d;
  if (!p || !*p) return;
  switch (*p) {
  case 'P': { int i = atoi(p + 1); *d = fd_skip(p); if (i < np) pa[i] = join(pa[i], v); return; }
  case 'L': *d = p + 1; if (v.k == 5 && v.a && v.a->n >= 1) desc_bind(d, v.a->s[0], pa, np, join); else *d = fd_skip(*d); return;
  case 'D': {
    const char *q = strchr(p, '('); if (!q) { *d = p + strlen(p); return; }
    int i = 0; q++;
    while (*q && *q != ')') { if (v.k == 5 && v.a && i < v.a->n) desc_bind(&q, v.a->s[i], pa, np, join); else q = fd_skip(q); i++; }
    *d = *q == ')' ? q + 1 : q; return;
  }
  default: *d = fd_skip(p); return;
  }
}
/* What field j of constructor c holds in a value of shape v: its declared type read against v's parameters, or --
   when v says nothing of them -- what the unit stored in that field anywhere (fld, the per-constructor table). */
static Shape field_shape(Shape **fld, int64_t nctor, const LinCtor *c, int64_t id, int j, Shape v) {
  Shape g = fld && id > 0 && id <= nctor && fld[id] ? fld[id][j] : (Shape){ 0, NULL, NULL };
  if (v.k == 5 && v.a && c && v.dt == c->dt && c->fdesc) {
    const char *d = c->fdesc; for (int i = 0; i < j && *d; i++) d = fd_skip(d);
    Shape s = desc_shape(&d, v.a->s, v.a->n);
    if (s.k) return s;
  }
  return g;
}
static Shape **sh_par, *sh_fun; static unsigned char *sh_built; static int sh_changed, sh_bad, sh_optimistic, sh_guessed, sh_no_fallback;
static int64_t ctor_id(const LinCtor *ci) { for (int64_t k = 1; lin_ctor_info(k); k++) if (lin_ctor_info(k) == ci) return k; return 0; }
static void sh_upd(Shape *slot, Shape v) { Shape j = sh_join(*slot, v); if (!sh_eq(j, *slot)) { *slot = j; sh_changed = 1; } }
/* WHAT A USE SAYS, BACK UP TO WHERE THE VALUE CAME FROM.  A value taken apart as a datatype, or computed with as a
   number, says so of what it was read from: a parameter is that, and a field of the datatype's parameter says what
   that parameter holds in the value it was read from -- an inner list's head added as a number makes the outer
   list's elements lists of numbers.  (What a unit is given from the net is known only by how it is used.) */
static void sh_use(const Expr *x, Shape X) {
  if (!x || !X.k || X.k == 9) return;
  if (x->op == E_PARAM) {
    if (x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], X);
    else if (x->nargs >= 0 && x->nargs < nfun && x->k < funs[x->nargs].arity) sh_upd(&sh_par[x->nargs][x->k], X);
    return;
  }
  if (x->op == E_FIELD && x->ci && field_is_param(x->ci, (int)x->k)) {
    const char *d = x->ci->fdesc; for (int64_t i = 0; i < x->k && *d; i++) d = fd_skip(d);
    int pi = atoi(d + 1), np = dt_nparams(x->ci->dt);
    if (pi < 0 || pi >= np) return;
    Shape *pa = calloc((size_t)np, sizeof *pa); pa[pi] = X;
    sh_use(x->a, sh_mk(x->ci->dt, np, pa)); free(pa);
  }
}
static unsigned char *sh_fneed;                     /* a function whose result is needed as a number (once each) */
static void sh_need_num(const Expr *x) {
  if (x->op == E_IF) { sh_need_num(x->b); sh_need_num(x->c); return; }   /* (what the value may be, everywhere) */
  if (x->op == E_CALL && sh_fneed && x->k >= 0 && x->k < nfun) {       /* ...and what a call returns */
    if (!sh_fneed[x->k]) { sh_fneed[x->k] = 1; sh_changed = 1; sh_need_num(funs[x->k].body); }
    return;
  }
  if (x->op == E_MATCH) { for (int i = 0; i < x->nargs; i++) if (!neutral_branch(x->args[i])) sh_need_num(x->args[i]); return; }
  if (x->op == E_FIELD && x->ci) { int64_t id = ctor_id(x->ci); if (id > 0 && id <= sh_nctor && x->k < x->ci->k) sh_upd(&sh_fld[id][x->k], (Shape){ 1, NULL }); sh_use(x, (Shape){ 1, NULL, NULL }); }
  else if (x->op == E_PARAM && x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], (Shape){ 1, NULL });
  else if (x->op == E_PARAM && x->nargs >= 0 && x->nargs < nfun) sh_upd(&sh_par[x->nargs][x->k], (Shape){ 1, NULL });
}
static Shape shape_of(const Expr *e) {
  if (e->id < sh_cap && sh_gen[e->id] == sh_g) return sh_memo[e->id];
  Shape r = { 0, NULL };
  switch (e->op) {
  case E_LET: shape_of(e->a); r = shape_of(e->b); break;
  case E_VAR: r = shape_of(e->bind->a); break;     /* (a name has its value's shape) */
  case E_DUP: case E_AFTER: r = shape_of(e->a); break;
  case E_DROP: case E_SPEC: r = shape_of(e->b); break;
  case E_CONST: if (e->box) break;                 /* the cells' end answering true: every shape takes it */
    r.k = e->kind == 3 ? 3 : 1; break;
  case E_BIN: case E_FOP:                            /* an operation's operands are numbers: what they were read from too */
    for (int i = 0; i < (e->op == E_BIN ? 2 : e->nargs); i++) {
      const Expr *x = e->op == E_BIN ? (i ? e->b : e->a) : e->args[i];
      shape_of(x); sh_need_num(x);
    }
    r.k = e->kind == 3 ? 3 : 1; break;
  case E_PARAM: r = e->nargs >= 0 && e->nargs < nfun ? sh_par[e->nargs][e->k] : e->k < nesh ? esh[e->k] : (Shape){ 1, NULL }; break;
  case E_IF: shape_of(e->a); r = sh_join(shape_of(e->b), shape_of(e->c)); break;
  case E_MATCH: {
    if (e->ci) sh_use(e->a, (Shape){ 5, e->ci->dt, NULL });   /* (what is taken apart: its use says what it is, back to where it was read) */
    Shape sc = shape_of(e->a);                       /* what is taken apart must be that datatype's */
    /* a field whose declared type is the datatype's PARAMETER holds whatever this use of the datatype holds:
       taken apart as another datatype than the unit built in it elsewhere (a Seq of pieces, a Seq of ranges),
       it is a block of SOME datatype -- the field's shape says so from now on */
    if (sc.k == 5 && e->ci && sc.dt && sc.dt != e->ci->dt && e->a->op == E_FIELD && field_is_param(e->a->ci, (int)e->a->k)) {
      int64_t fid = ctor_id(e->a->ci);
      if (fid > 0 && fid <= sh_nctor) sh_upd(&sh_fld[fid][e->a->k], (Shape){ 5, e->ci->dt });
    } else
    if (sc.k && !(sc.k == 5 && e->ci && (!sc.dt || sc.dt == e->ci->dt))) { if (dbg > 2) DBG("[shape: match on op %d (f%d.%" PRId64 " k%" PRId64 ") shape %d %s, wanted %s]\n", e->a->op, e->a->nargs, e->a->k, e->a->k, sc.k, sc.dt ? sc.dt : "-", e->ci ? e->ci->dt : "?"); sh_bad = 1; }
    { int any = 0; for (int i = 0; i < e->nargs; i++) any |= !neutral_branch(e->args[i]);
      for (int i = 0; i < e->nargs; i++) { Shape b = shape_of(e->args[i]); if (!any || !neutral_branch(e->args[i])) r = sh_join(r, b); } }
    break;
  }
  case E_CALL:
    for (int i = 0; i < e->nargs; i++) {
      Shape a = shape_of(e->args[i]);
      if (funs[e->k].known && funs[e->k].known[i]) continue;
      sh_upd(&sh_par[e->k][i], a);
      const Expr *x = e->args[i];                    /* an argument passed in takes the parameter's shape */
      if (x->op == E_PARAM && x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], sh_par[e->k][i]);
      /* (and a function's own parameter handed to one that is taken apart is that datatype too: `src` in
         `(repeat src src ...)` is only ever passed along, to the parameter that walks it) */
      else if (x->op == E_PARAM && x->nargs >= 0 && x->nargs < nfun && sh_par[e->k][i].k == 5) sh_upd(&sh_par[x->nargs][x->k], sh_par[e->k][i]);
    }
    r = sh_fun[e->k]; break;
  case E_CTOR: {
    int64_t id = ctor_id(e->ci);
    if (id <= 0 || id > sh_nctor) { r.k = 9; break; }
    sh_built[id] = 1;
    int np = dt_nparams(e->ci->dt); Shape *pa = np ? A(sizeof *pa * (size_t)np) : NULL;
    const char *d = e->ci->fdesc;
    for (int j = 0; j < e->nargs; j++) {
      Shape aj = shape_of(e->args[j]);
      { Shape g = aj; g.a = NULL; sh_upd(&sh_fld[id][j], g); }   /* (the per-constructor table: what ANY value holds there -- no parameters, which differ by value) */
      const Expr *x = e->args[j];
      if (x->op == E_PARAM && x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], sh_fld[id][j]);
      if (np && d && *d) desc_bind(&d, aj, pa, np, sh_join);   /* (what this value's parameters hold) */
    }
    r = np ? sh_mk(e->ci->dt, np, pa) : (Shape){ 5, e->ci->dt, NULL }; break;
  }
  case E_FIELD: {
    { Shape sc = shape_of(e->a); if (sc.k && !(sc.k == 5 && e->ci && (!sc.dt || sc.dt == e->ci->dt))) sh_bad = 1; }
    int64_t id = ctor_id(e->ci);
    Shape sv = shape_of(e->a);
    r = id > 0 && id <= sh_nctor && e->k < e->ci->k ? field_shape(sh_fld, sh_nctor, e->ci, id, (int)e->k, sv) : (Shape){ 9, NULL };
    /* OPTIMISM: a field of the datatype's parameter, read from a value whose parameters are not known YET, is
       nothing yet -- the per-constructor table would say what any value holds there (a number in an inner list's
       cell, a list in the outer's: TOP), and a join never comes back down from TOP.  If such a guess survives to
       the last round, the unit's shapes are worked out again without it (unit_shapes). */
    if (sh_optimistic && (sv.k == 0 || (sv.k == 5 && !sv.a && sv.dt == e->ci->dt)) && field_is_param(e->ci, (int)e->k)) { r = (Shape){ 0, NULL, NULL }; sh_guessed = 1; }
    break;
  }
  case E_VOP: {                                     /* (see OWNED VECTORS) */
    Shape v = shape_of(e->args[0]);
    switch (e->k) {
    case LIN_VOP_NEW: { sh_need_num(e->args[0]); Shape x = shape_of(e->args[1]); r = sh_mk(VEC_DT, 1, &x); break; }
    case LIN_VOP_LEN: sh_use(e->args[0], (Shape){ 5, VEC_DT, NULL }); r.k = 1; break;
    case LIN_VOP_GET:
      sh_use(e->args[0], (Shape){ 5, VEC_DT, NULL }); shape_of(e->args[1]); sh_need_num(e->args[1]);
      if (v.k && !(v.k == 5 && v.dt == VEC_DT)) sh_bad = 1;
      r = v.k == 5 && v.dt == VEC_DT && v.a ? v.a->s[0] : (Shape){ 0, NULL, NULL }; break;
    default: {                                       /* SET, PUSH: the vector, with what is stored in it */
      Shape x = shape_of(e->args[e->nargs - 1]);
      if (e->k == LIN_VOP_SET) { shape_of(e->args[1]); sh_need_num(e->args[1]); }
      if (v.k && !(v.k == 5 && v.dt == VEC_DT)) sh_bad = 1;
      r = sh_join(v.k == 5 && v.dt == VEC_DT ? v : (Shape){ 0, NULL, NULL }, sh_mk(VEC_DT, 1, &x));
      sh_use(e->args[0], r);
      break; }
    }
    break; }
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
  sh_fld = A(sizeof *sh_fld * (size_t)(sh_nctor + 1)); sh_built = A((size_t)(sh_nctor + 1)); sh_fneed = A((size_t)(nfun ? nfun : 1));
  for (int64_t k = 1; k <= sh_nctor; k++) sh_fld[k] = A(sizeof **sh_fld * (size_t)(lin_ctor_info(k)->k + 1));
  /* a field's DECLARED type is its shape to start from: a field the unit only passes along is never taken
     apart, so nothing else would say what it holds -- and data read in needs its shape */
  for (int64_t k = 1; k <= sh_nctor; k++) {
    const LinCtor *c = lin_ctor_info(k); const char *d = c->fdesc;
    for (int j = 0; d && *d && j < c->k; j++, d = fd_skip(d)) {
      if (*d == 'N' || *d == 'F') sh_fld[k][j] = (Shape){ 1, NULL };
      else if (*d == 'B') sh_fld[k][j] = (Shape){ 3, NULL };
      else if (*d == 'D') {
        const char *p = strchr(d, '('); size_t nl = p ? (size_t)(p - d - 1) : 0; const LinCtor *c2;
        for (int64_t k2 = 1; nl && (c2 = lin_ctor_info(k2)); k2++)
          if (c2->dt && strlen(c2->dt) == nl && !strncmp(c2->dt, d + 1, nl)) { sh_fld[k][j] = (Shape){ 5, c2->dt }; break; }
      }
    }
  }
  if (sh_cap < eid) { sh_cap = eid * 2 + 64; sh_memo = realloc(sh_memo, sizeof *sh_memo * (size_t)sh_cap); sh_gen = realloc(sh_gen, sizeof *sh_gen * (size_t)sh_cap); memset(sh_gen, 0, sizeof *sh_gen * (size_t)sh_cap); }
  Shape res = { 0, NULL };
  Shape **fld0 = A(sizeof *fld0 * (size_t)(sh_nctor + 1));   /* (the declared start, for a second attempt) */
  for (int64_t k = 1; k <= sh_nctor; k++) { int nk = lin_ctor_info(k)->k + 1; fld0[k] = A(sizeof **fld0 * (size_t)nk); memcpy(fld0[k], sh_fld[k], sizeof **fld0 * (size_t)nk); }
  Shape *esh0 = nesh ? A(sizeof *esh0 * (size_t)nesh) : NULL; if (nesh) memcpy(esh0, esh, sizeof *esh * (size_t)nesh);
  int okeep = 0, obad = 0; Shape ores = { 0, NULL, NULL }, **opar = NULL, *ofun = NULL, **ofld = NULL, *oesh = NULL; unsigned char *obuilt = NULL;
  for (sh_optimistic = 1; sh_optimistic >= 0; sh_optimistic--) {
    if (sh_optimistic == 0) {                        /* a guess outlived the fixpoint: again, without guessing */
      for (int i = 0; i < nfun; i++) { memset(sh_par[i], 0, sizeof **sh_par * (size_t)(funs[i].arity ? funs[i].arity : 1)); sh_fun[i] = (Shape){ 0, NULL, NULL }; }
      for (int64_t k = 1; k <= sh_nctor; k++) memcpy(sh_fld[k], fld0[k], sizeof **sh_fld * (size_t)(lin_ctor_info(k)->k + 1));
      memset(sh_built, 0, (size_t)(sh_nctor + 1)); memset(sh_fneed, 0, (size_t)(nfun ? nfun : 1));
      if (nesh) memcpy(esh, esh0, sizeof *esh * (size_t)nesh);
    }
    for (int round = 0; round < 1000; round++) {
      sh_changed = 0; sh_bad = 0; sh_guessed = 0;
      sh_g++;
      for (int i = 0; i < nfun; i++) sh_upd(&sh_fun[i], shape_of(funs[i].body));
      res = shape_of(entry);
      if (!sh_changed) break;
    }
    if (!sh_guessed || sh_no_fallback) break;
    if (sh_optimistic == 1) {                        /* (kept: if the old analysis does worse, this is the answer) */
      okeep = 1; ores = res; obad = sh_bad;
      opar = A(sizeof *opar * (size_t)(nfun ? nfun : 1)); for (int i = 0; i < nfun; i++) { int a = funs[i].arity ? funs[i].arity : 1; opar[i] = A(sizeof **opar * (size_t)a); memcpy(opar[i], sh_par[i], sizeof **opar * (size_t)a); }
      ofun = A(sizeof *ofun * (size_t)(nfun ? nfun : 1)); memcpy(ofun, sh_fun, sizeof *ofun * (size_t)nfun);
      ofld = A(sizeof *ofld * (size_t)(sh_nctor + 1)); for (int64_t k = 1; k <= sh_nctor; k++) { int nk = lin_ctor_info(k)->k + 1; ofld[k] = A(sizeof **ofld * (size_t)nk); memcpy(ofld[k], sh_fld[k], sizeof **ofld * (size_t)nk); }
      oesh = nesh ? A(sizeof *oesh * (size_t)nesh) : NULL; if (nesh) memcpy(oesh, esh, sizeof *esh * (size_t)nesh);
      obuilt = A((size_t)(sh_nctor + 1)); memcpy(obuilt, sh_built, (size_t)(sh_nctor + 1));
    }
    if (dbg > 2) DBG("[shapes: a parameter's field was still guessed at the end; again, without guessing]\n");
  }
  /* A guess that survives is a value whose parameters nothing says -- a word of unknown kind, which the unit never
     frees, copies or reads back as data (a field of it reaching the result or the arguments is refused as before).
     So the optimistic shapes stand when they are clean and the old analysis's are not. */
  if (okeep) {
    int top_new = sh_bad || sh_top(res), top_old = obad || sh_top(ores);
    for (int i = 0; i < nfun; i++) for (int k = 0; k < funs[i].arity; k++) { top_new |= sh_top(sh_par[i][k]); top_old |= sh_top(opar[i][k]); }
    if (top_new && !top_old) {
      for (int i = 0; i < nfun; i++) memcpy(sh_par[i], opar[i], sizeof **opar * (size_t)(funs[i].arity ? funs[i].arity : 1));
      memcpy(sh_fun, ofun, sizeof *ofun * (size_t)nfun);
      for (int64_t k = 1; k <= sh_nctor; k++) memcpy(sh_fld[k], ofld[k], sizeof **ofld * (size_t)(lin_ctor_info(k)->k + 1));
      if (nesh) memcpy(esh, oesh, sizeof *esh * (size_t)nesh);
      memcpy(sh_built, obuilt, (size_t)(sh_nctor + 1));
      res = ores; sh_bad = obad; sh_g++;
      if (dbg > 2) DBG("[shapes: the optimistic ones stand]\n");
    }
  }
  sh_optimistic = 0;
  if (dbg > 2) {
    for (int i = 0; i < nfun; i++) { fprintf(stderr, "fn: [shapes f%d:", i); for (int j = 0; j < funs[i].arity; j++) { fprintf(stderr, " "); sh_print(sh_par[i][j]); } fprintf(stderr, " -> "); sh_print(sh_fun[i]); fprintf(stderr, "]\n"); }
    fprintf(stderr, "fn: [shape of the entry: "); sh_print(res); fprintf(stderr, "]\n");
  }
  return res;
}
static void sh_print(Shape s) {                     /* (LIN_FN_DEBUG=3) */
  if (s.k == 5) { fprintf(stderr, "%s", s.dt ? s.dt : "data"); if (s.a) { fprintf(stderr, "("); for (int i = 0; i < s.a->n; i++) { if (i) fprintf(stderr, ","); sh_print(s.a->s[i]); } fprintf(stderr, ")"); } }
  else fprintf(stderr, "%s", s.k == 1 ? "num" : s.k == 3 ? "bool" : s.k == 9 ? "TOP" : "?");
}
/* A FUNCTION USED AT TWO SHAPES.  One function's parameter has one shape, so a library function called on a list of
   lists in one place and on a list of numbers in another (`nth`) joins them to TOP and the unit is handed back.
   Such a function is given one version per shape its callers give it -- the same body, its own calls to itself
   kept in the version -- and the shapes are worked out again: monomorphised by need, not by a pass that copies
   every function.  (Not one a closure ties to another: as for the ownership versions, below.) */
static int sh_top(Shape s) { if (s.k == 9) return 1; if (s.a) for (int i = 0; i < s.a->n; i++) if (sh_top(s.a->s[i])) return 1; return 0; }
static int *sv_orig; static Shape **sv_sig; static int sv_n, sv_cap, sv_changed, sv_limit;
static int sv_version(int g, Shape *sig) {
  int o = sv_orig[g], ar = funs[o].arity;
  for (int i = 0; i < nfun; i++) if (i < sv_n && sv_orig[i] == o && sv_sig[i]) {
    int eq = 1; for (int k = 0; k < ar && eq; k++) eq = sh_eq(sv_sig[i][k], sig[k]);
    if (eq) return i;
  }
  /* (every shape a caller gives gets a version, and the original keeps the callers whose own arguments are still TOP --
      a call fed by another call of the same function: once that one has its version, its result is no longer the
      join of both, and the next round sees this caller's shape too) */
  if (nfun >= sv_limit) return -1;
  if (nfun >= funcap) funs = realloc(funs, (size_t)(funcap = funcap ? funcap * 2 : 8) * sizeof *funs);
  if (nfun >= sv_cap) { sv_cap = nfun * 2 + 8; sv_orig = realloc(sv_orig, sizeof *sv_orig * (size_t)sv_cap); sv_sig = realloc(sv_sig, sizeof *sv_sig * (size_t)sv_cap); }
  int v = nfun++;
  funs[v] = funs[o]; funs[v].lam = -1;
  funs[v].pnode = A(sizeof(Expr *) * (size_t)(ar ? ar : 1));
  for (int k = 0; k < ar; k++) { Expr *q = mke(E_PARAM, funs[o].pnode && funs[o].pnode[k] ? funs[o].pnode[k]->kind : 1); q->k = k; q->nargs = v; funs[v].pnode[k] = q; }
  int mn = eid; Expr **memo = calloc((size_t)mn + 1, sizeof *memo);
  funs[v].body = vcopy(funs[o].body, o, v, memo, mn); free(memo);
  sv_orig[v] = o; sv_sig[v] = A(sizeof *sig * (size_t)(ar ? ar : 1)); memcpy(sv_sig[v], sig, sizeof *sig * (size_t)ar); sv_n = nfun;
  if (dbg > 1) DBG("[f%d: f%d at another shape]\n", v, o);
  return v;
}
static Expr **sv_map; static int sv_mapn, sv_self;
static Expr *sv_redirect(Expr *e) {
  if (!e) return NULL;
  if (e->op == E_PARAM || e->op == E_CONST) return e;
  if (e->id < sv_mapn && sv_map[e->id]) return sv_map[e->id];
  Expr *a = sv_redirect(e->a), *b = sv_redirect(e->b), *c = e->op == E_CTOR ? e->c : sv_redirect(e->c);
  int ch = a != e->a || b != e->b || c != e->c; Expr **na = NULL;
  if (e->nargs && e->args) { na = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) { na[i] = sv_redirect(e->args[i]); ch |= na[i] != e->args[i]; } }
  int64_t k = e->k;
  /* a version's own recursive calls are to itself (vcopy gives it its parameters; its calls are still the original's) */
  if (e->op == E_CALL && sv_self >= 0 && sv_self < sv_n && sv_orig[sv_self] != sv_self && e->k == sv_orig[sv_self]) { k = sv_self; ch = 1; sv_changed = 1; }
  else if (e->op == E_CALL && e->k >= 0 && e->k < nfun && e->k < sv_n && funs[e->k].body && !funs[sv_orig[e->k]].known
      && sv_orig[e->k] != (sv_self >= 0 ? sv_orig[sv_self] : -1) && !reads_outer(sv_orig[e->k])) {
    int g = (int)e->k, ar = funs[g].arity, top = 0;
    for (int i = 0; i < ar; i++) top |= sh_top(sh_par[g][i]);
    if (top) {
      Shape *sig = A(sizeof *sig * (size_t)(ar ? ar : 1));
      int ok = 1;
      for (int i = 0; i < ar; i++) { sig[i] = i < e->nargs ? shape_of(e->args[i]) : (Shape){ 0, NULL, NULL }; ok &= !sh_top(sig[i]); }
      int t = ok ? sv_version(g, sig) : -1;
      if (t >= 0 && t != g) { k = t; ch = 1; sv_changed = 1; }
    }
  }
  Expr *x = e;
  if (ch) { x = fu_clone(e); x->a = a; x->b = b; x->c = c; if (na) x->args = na; x->k = k; x = hc(x); }
  if (e->id < sv_mapn) sv_map[e->id] = x;
  return x;
}
static Shape shape_versions(Expr **entry, Shape res) {
  int n0 = nfun; sv_limit = 2 * n0 + 2;
  { int any = 0; for (int i = 0; i < nfun && !any; i++) for (int k = 0; k < funs[i].arity; k++) any |= sh_top(sh_par[i][k]);
    if (!any) return res; }
  sh_no_fallback = 1; res = unit_shapes(*entry);   /* (the versions are chosen by the optimistic shapes: the old analysis's TOP says nothing of which) */
  sv_cap = nfun * 2 + 8; sv_orig = malloc(sizeof *sv_orig * (size_t)sv_cap); sv_sig = calloc((size_t)sv_cap, sizeof *sv_sig);
  for (int i = 0; i < nfun; i++) sv_orig[i] = i;
  sv_n = nfun;
  for (int round = 0; round <= n0 + 1; round++) {
    int any = 0; for (int i = 0; i < nfun && !any; i++) for (int k = 0; k < funs[i].arity; k++) any |= sh_top(sh_par[i][k]);
    if (!any) break;
    sv_changed = 0; int nb = nfun;
    for (int g = -1; g < nb; g++) {
      if (g >= 0 && !funs[g].body) continue;
      sv_self = g; sv_mapn = eid; sv_map = calloc((size_t)sv_mapn + 1, sizeof *sv_map);
      sh_g++;                                        /* (shape_of's memo: the shapes stay those just worked out) */
      Expr *nb2 = sv_redirect(g < 0 ? *entry : funs[g].body);
      free(sv_map);
      if (g < 0) *entry = nb2; else funs[g].body = nb2;
    }
    if (!sv_changed) break;
    res = unit_shapes(*entry);
  }
  sh_no_fallback = 0;
  res = unit_shapes(*entry);                         /* (and once more as the unit will be: guessing only if nothing is left to guess) */
  if (nfun > n0 && dbg) DBG("%d version%s of the unit's functions for the shapes they are called at\n", nfun - n0, nfun - n0 == 1 ? "" : "s");
  free(sv_orig); free(sv_sig); sv_orig = NULL; sv_sig = NULL;
  return res;
}
/* Can a value of this shape be read back?  Every constructor of every datatype it reaches that the unit builds
   must have fields of a known shape. */
static int shape_closed(Shape s, int depth) {   /* depth: datatypes on the walk (each one checked once) */
  if (s.k == 1 || s.k == 3) return 1;
  if (s.k != 5 || !s.dt || depth > sh_nctor) return 0;
  if (s.dt == VEC_DT) return s.a && s.a->n == 1 && shape_closed(s.a->s[0], depth + 1);   /* (a vector: its elements) */
  for (int64_t k = 1; k <= sh_nctor; k++) {
    const LinCtor *c = lin_ctor_info(k);
    if (c->dt != s.dt || !sh_built[k]) continue;
    for (int j = 0; j < c->k; j++) {
      Shape f = field_shape(sh_fld, sh_nctor, c, k, j, s);
      if (f.k == 5 ? (!(f.dt == s.dt && f.a == s.a) && !shape_closed(f, depth + 1)) : !(f.k == 1 || f.k == 3)) return 0;
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
  "#include <setjmp.h>\n#include <stdlib.h>\n#include <stdio.h>\n"
  "#define LIN_TLS __thread __attribute__((tls_model(\"initial-exec\")))\n"
  "extern LIN_TLS jmp_buf lin_jb; extern LIN_TLS char *lin_stack_lo; int lin_fn_aborted;\n"
  "extern LIN_TLS int64_t *lin_hp, *lin_he; static int64_t lin_used; static void **lin_ch; static int lin_nch, lin_cch; \n"
  "static pthread_mutex_t lin_chm = PTHREAD_MUTEX_INITIALIZER;\n"
  /* A CHUNK POOL.  A task's thread ends with most of its chunk unused; the rest is put here for the next thread, so
     tasks started over and over (a parallel map in a loop) take the same memory again instead of new chunks */
  "typedef struct { int64_t *p, *e; } LinRest; static LinRest *lin_pool; static int lin_npool, lin_cpool;\n"
  "static void lin_task_end(void) { if (lin_he - lin_hp >= 4096) { pthread_mutex_lock(&lin_chm);\n"
  "  if (lin_npool == lin_cpool) lin_pool = realloc(lin_pool, sizeof *lin_pool * (size_t)(lin_cpool = lin_cpool ? lin_cpool * 2 : 16));\n"
  "  lin_pool[lin_npool++] = (LinRest){ lin_hp, lin_he }; pthread_mutex_unlock(&lin_chm); } lin_hp = lin_he = 0; }\n"
  "#ifdef __linux__\nextern int madvise(void *, size_t, int);\n#define LIN_HUGE(p, n) madvise((p), (n), 14)\n#else\n#define LIN_HUGE(p, n) ((void)0)\n#endif\n"
  "static __attribute__((noinline, cold)) void lin_refill(int64_t n) {\n"
  "  /* (the arena grows by doubling chunks; a large one is asked for in huge pages, where the OS has them: a fresh\n"
  "     page is the dearest thing a list costs, and a 2 MB page is one fault where 4 KB pages are 512) */\n"
  "  pthread_mutex_lock(&lin_chm);\n"   /* (first what a finished thread left: see lin_task_end) */
  "  for (int i = lin_npool - 1; i >= 0; i--) if (lin_pool[i].e - lin_pool[i].p >= n) { lin_hp = lin_pool[i].p; lin_he = lin_pool[i].e; lin_pool[i] = lin_pool[--lin_npool]; pthread_mutex_unlock(&lin_chm); return; }\n"
  "  pthread_mutex_unlock(&lin_chm);\n"
  "  int64_t g = lin_nch < 6 ? lin_nch : 6, sz = 65536L << g; if (sz < n) sz = n; int64_t *c;\n"
  "  if (sz >= (1L << 18) && !(sz & ((1L << 18) - 1))) { c = aligned_alloc((size_t)1 << 21, (size_t)sz * 8); if (c) LIN_HUGE(c, (size_t)sz * 8); }\n"
  "  else c = malloc((size_t)sz * 8);\n"
  "  if (!c || lin_fn_aborted || lin_used > (1L << 28) || (char *)__builtin_frame_address(0) < lin_stack_lo) { free(c); lin_fn_aborted = 1; longjmp(lin_jb, 1); }\n"
  "  pthread_mutex_lock(&lin_chm);\n"
  "  if (lin_nch >= lin_cch) { lin_cch = lin_cch ? lin_cch * 2 : 64; lin_ch = realloc(lin_ch, (size_t)lin_cch * sizeof *lin_ch); }\n"
  "  lin_ch[lin_nch++] = c; lin_used += sz; pthread_mutex_unlock(&lin_chm); lin_hp = c; lin_he = c + sz; }\n"
  "extern LIN_TLS int64_t *lin_fl[8 + 8 * sizeof(int64_t)];\n"
  /* (SIZE CLASSES: a block under 8 words has a list of its own size; a larger one is rounded up to a power of two,
     one list per power -- so the block a freed vector leaves serves the next of its class, and memory stays the
     live data however large the blocks are) */
  "static inline int lin_cls(int64_t n) { return n < 8 ? (int)n : 8 + (int)(8 * sizeof(int64_t)) - __builtin_clzl((uint64_t)(n - 1)); }\n"
  /* EVERY BLOCK CARRIES A COUNT, in the word before it (so a field's offset is the same with or without it): how
     many references hold it.  A new block has one. */
  "#ifdef LIN_STATS\nstatic int64_t lin_na[9], lin_nf[9];\n#define LIN_NA(n) lin_na[(n) < 8 ? (n) : 8]++\n#define LIN_NF(n) lin_nf[(n) < 8 ? (n) : 8]++\n#else\n#define LIN_NA(n)\n#define LIN_NF(n)\n#endif\n"
  "#ifdef LIN_LEAKS\nstatic int64_t *lk_p; static int *lk_s; static int64_t lk_n, lk_c;\n"
  "static void lin_leak_note(int64_t *p, int site) { if (lk_n * 2 >= lk_c) { int64_t oc = lk_c, *op = lk_p; int *os = lk_s; lk_c = lk_c ? lk_c * 2 : 1 << 16;\n"
  "  lk_p = calloc((size_t)lk_c, sizeof *lk_p); lk_s = calloc((size_t)lk_c, sizeof *lk_s); lk_n = 0;\n"
  "  for (int64_t i = 0; i < oc; i++) if (op[i] > 1) { int64_t j = ((uint64_t)op[i] >> 3) & (lk_c - 1); while (lk_p[j]) j = (j + 1) & (lk_c - 1); lk_p[j] = op[i]; lk_s[j] = os[i]; lk_n++; } free(op); free(os); }\n"
  "  int64_t j = ((uint64_t)p >> 3) & (lk_c - 1); while (lk_p[j] > 1 && lk_p[j] != (int64_t)p) j = (j + 1) & (lk_c - 1); if (lk_p[j] != (int64_t)p) lk_n++; lk_p[j] = (int64_t)p; lk_s[j] = site; }\n"
  "static void lin_leak_forget(int64_t *p) { if (!lk_c) return; int64_t j = ((uint64_t)p >> 3) & (lk_c - 1); while (lk_p[j]) { if (lk_p[j] == (int64_t)p) { lk_p[j] = 1; return; } j = (j + 1) & (lk_c - 1); } }\n"
  "static void lin_leak_report(void) { int mx = 0; for (int64_t i = 0; i < lk_c; i++) if (lk_p[i] > 1 && lk_s[i] > mx) mx = lk_s[i];\n"
  "  int64_t *cnt = calloc((size_t)mx + 1, sizeof *cnt); for (int64_t i = 0; i < lk_c; i++) if (lk_p[i] > 1) cnt[lk_s[i]]++;\n"
  "  for (int s = 0; s <= mx; s++) if (cnt[s]) fprintf(stderr, \"lin: site %d holds %\" PRId64 \" blocks\\n\", s, cnt[s]); free(cnt); }\n"
  "#define LIN_LF(p) lin_leak_forget(p)\n#else\n#define LIN_LF(p)\n#define lin_leak_report()\n#endif\n"
  "static inline int64_t *lin_alloc(int64_t n) { LIN_NA(n); int c = lin_cls(n); int64_t *f = lin_fl[c]; if (f) { lin_fl[c] = (int64_t *)f[0]; f[-1] = 1; return f; }\n"
  "  if (n >= 8) n = 1L << (c - 8);\n"
  "  if (__builtin_expect(lin_hp + n + 1 > lin_he, 0)) lin_refill(n + 1); int64_t *r = lin_hp + 1; r[-1] = 1; lin_hp += n + 1; return r; }\n"
  /* (a count is positive while one thread alone can see the block, and is then plain arithmetic; what is handed to
     another thread is first marked SHARED -- its count negated, see gen_data_fns -- and a shared count is atomic.
     A shared block held by one reference is that holder's alone: made local again, and rebuilt in.  Only a unit
     that hands a thread something it cannot mark counts everything atomically: lin_mt) */
  "static int lin_mt;\n"
  "static inline int64_t lin_dup(int64_t v) { if (!(v & 1)) { int64_t *p = (int64_t *)v; int64_t c = __atomic_load_n(&p[-1], __ATOMIC_RELAXED);\n"
  "  if (c > 0 && !lin_mt) p[-1] = c + 1; else if (c > 0) __atomic_fetch_add(&p[-1], 1, __ATOMIC_RELAXED); else if (c) __atomic_fetch_sub(&p[-1], 1, __ATOMIC_RELAXED); } return v; }\n"
  "static inline void lin_dupn(int64_t v, int64_t k) { if (!(v & 1) && k > 0) { int64_t *p = (int64_t *)v; int64_t c = __atomic_load_n(&p[-1], __ATOMIC_RELAXED);\n"
  "  if (c > 0 && !lin_mt) p[-1] = c + k; else if (c > 0) __atomic_fetch_add(&p[-1], k, __ATOMIC_RELAXED); else if (c) __atomic_fetch_sub(&p[-1], k, __ATOMIC_RELAXED); } }\n"
  "static inline int lin_uniq(int64_t *p) { int64_t c = __atomic_load_n(&p[-1], __ATOMIC_ACQUIRE); if (c == 1) return 1; if (c == -1) { p[-1] = 1; return 1; } return 0; }\n"
  "static inline int lin_dec(int64_t *p) { int64_t c = __atomic_load_n(&p[-1], __ATOMIC_RELAXED);\n"
  "  if (c > 0 && !lin_mt) { p[-1] = c - 1; return c == 1; } if (c > 0) return __atomic_sub_fetch(&p[-1], 1, __ATOMIC_ACQ_REL) == 0;\n"
  "  return c && __atomic_add_fetch(&p[-1], 1, __ATOMIC_ACQ_REL) == 0; }\n"
  /* a block a match consumed and nothing else holds: back on its size's list (memory is the live data, as in C) */
  "#ifdef LIN_POISON\n"   /* (LIN_FN_POISON: a freed block's words become an address nothing is at -- read after its free, it faults) */
  "static inline void lin_free(int64_t *p, int64_t n) { LIN_LF(p); LIN_NF(n); if (p[-1] > 1) { fprintf(stderr, \"lin: a block freed while %\" PRId64 \" references hold it\\n\", p[-1]); abort(); } for (int64_t i = 1; i < n; i++) p[i] = 0x5eadbeefde00L; int c = lin_cls(n); p[0] = (int64_t)lin_fl[c]; lin_fl[c] = p; }\n"
  "#else\n"
  "static inline void lin_free(int64_t *p, int64_t n) { LIN_LF(p); LIN_NF(n); int c = lin_cls(n); p[0] = (int64_t)lin_fl[c]; lin_fl[c] = p; }\n"
  "#ifdef LIN_LEAKS\n#define LIN_ALLOC_RAW lin_alloc\nstatic inline int64_t *lin_alloc_at(int site, int64_t n) { int64_t *p = LIN_ALLOC_RAW(n); lin_leak_note(p, site); return p; }\n#endif\n"
  "#endif\n"
  "#ifdef LIN_STATS\nstatic void lin_stats(void) { for (int i = 0; i < 9; i++) if (lin_na[i]) fprintf(stderr, \"lin: blocks of %d words: %\" PRId64 \" built, %\" PRId64 \" freed\\n\", i, lin_na[i], lin_nf[i]); }\n#else\n#define lin_stats()\n#endif\n"
  "static void lin_free_all(void) { lin_stats(); lin_leak_report(); for (int i = 0; i < lin_nch; i++) free(lin_ch[i]); lin_nch = 0; lin_npool = 0; lin_hp = lin_he = 0; lin_used = 0; for (size_t i = 0; i < sizeof lin_fl / sizeof *lin_fl; i++) lin_fl[i] = 0; }\n"
  /* The guard lives where an infinite STRUCTURE must go -- the arena's refill, once per chunk -- and checks memory and
     the stack there; a compiled function carries nothing (measured: a per-call check doubled a tree insert).  A call
     whose runaway recursion builds nothing is not caught -- the exposure numeric units have always had.  A task on
     another thread has its own buffer and bound; abandoning anywhere marks the call, and a join that finds it marked
     abandons the joiner too, so a half-computed value is never used. */
  "#define LIN_ENTER\n#define LIN_LEAVE\n"
  "static pthread_key_t lin_tkey; static pthread_once_t lin_tonce = PTHREAD_ONCE_INIT;\n"   /* (a task's end, however it returns: lin_task_end) */
  "static void lin_tend(void *u) { (void)u; lin_task_end(); }\nstatic void lin_tkinit(void) { pthread_key_create(&lin_tkey, lin_tend); }\n"
  /* (the guard's stack: what a task asked for -- or, where there are no threads and a task runs on the caller's
     stack (WebAssembly), that stack's own end) */
  "#ifdef __EMSCRIPTEN__\n#include <emscripten/stack.h>\n#define LIN_STACK_LO(ss) ((char *)emscripten_stack_get_end() + 65536)\n#define LIN_NO_THREAD lin_run(0)\n"
  "#else\n#define LIN_STACK_LO(ss) ((char *)__builtin_frame_address(0) - (ss) + ((size_t)1 << 24))\n#define LIN_NO_THREAD lin_fn_aborted = 1; return 0\n#endif\n"
  "#define LIN_TASK_START(ss) pthread_once(&lin_tonce, lin_tkinit); pthread_setspecific(lin_tkey, (void *)1); if (setjmp(lin_jb)) { lin_fn_aborted = 1; return 0; } lin_stack_lo = LIN_STACK_LO(ss)\n"
  "#define LIN_JOINED (lin_fn_aborted ? (longjmp(lin_jb, 1), 0) : 0)\n"
  /* a result through its destination: LIN_PUT stores it only if it is not there already (a block rebuilt in place
     is, and storing it again would hold up the next load of that slot); LIN_SET is for a value that is new */
  "#define LIN_PUT(d, x) ({ int64_t x_ = (x); if (*(d) != x_) *(d) = x_; 0L; })\n"
  "#define LIN_SET(d, x) (*(d) = (x), 0L)\n";

/* A CAPTURED VALUE IS COMPUTED ONCE.  A function specialised to a closure has the closure's variables in its
   body; one that is an EXPRESSION of the enclosing function's parameters -- `(av n u)` in
   `(smap (\i (col i 0 (av n u) 0.0)) (srange 0 n))` -- would be evaluated again at every step of the loop, where
   the net shares it and evaluates it once.  Such an expression (a call, of other functions' parameters only) is
   made a PARAMETER of the function: whoever calls it computes the value and hands it over, and the function's own
   recursive calls pass it on. */
static int ho_f;
/* does function h read a parameter of ho_f -- itself, or through what it calls?  (An inner function reads its
   enclosing function's parameters without being handed them: a call of it is not free of them.) */
static int fr_body(const Expr *e, unsigned char *seen);
static int fun_reads(int h) {
  if (h < 0 || h >= nfun || h == ho_f) return 0;
  if (fr_memo[h]) return fr_memo[h] == 2;
  fr_memo[h] = 1;                                    /* (in progress: a cycle adds nothing) */
  unsigned char *seen = calloc((size_t)eid + 1, 1);
  int r = funs[h].body ? fr_body(funs[h].body, seen) : 0;
  free(seen);
  fr_memo[h] = r ? 2 : 1; return r;
}
static int fr_body(const Expr *e, unsigned char *seen) {
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_PARAM) return e->nargs == ho_f;
  if (e->op == E_CONST) return 0;
  if (e->op == E_CALL && fun_reads((int)e->k)) return 1;
  if (fr_body(e->a, seen) || fr_body(e->b, seen) || (e->op != E_CTOR && fr_body(e->c, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fr_body(e->args[i], seen)) return 1;
  return 0;
}
static unsigned ho_info(const Expr *e) {             /* 1: reads ho_f's own parameter (or an input); 2: has a call; 4: calls ho_f */
  if (!e) return 0;
  if (mm_has(MM_SSTR, e)) return mm_val[MM_SSTR][e->id];
  unsigned r = 0;
  if (e->op == E_PARAM) r = (e->nargs == ho_f || e->nargs < 0) ? 1u : 0u;
  else {
    if (e->op == E_CALL) r |= e->k == ho_f ? 6u : fun_reads((int)e->k) ? 3u : 2u;
    r |= ho_info(e->a) | ho_info(e->b); if (e->op != E_CTOR) r |= ho_info(e->c);
    for (int i = 0; i < e->nargs && e->args; i++) r |= ho_info(e->args[i]);
  }
  return mm_put(MM_SSTR, e, r);
}
static const Expr *ho_find(const Expr *e) {          /* the first, largest, such expression in e */
  if (!e || mm_has(MM_NUM, e)) return NULL;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_PARAM || e->op == E_CONST) return NULL;
  if (ho_info(e) == 2u) return e;
  const Expr *r = ho_find(e->a); if (!r) r = ho_find(e->b); if (!r && e->op != E_CTOR) r = ho_find(e->c);
  for (int i = 0; !r && i < e->nargs && e->args; i++) r = ho_find(e->args[i]);
  return r;
}
static Expr **ho_map; static int ho_cap; static const Expr *ho_x; static Expr *ho_p, *ho_extra;
static Expr *ho_rep(Expr *e) {                       /* x -> p (when p), and every call of ho_f given `extra` */
  if (!e) return NULL;
  if (e == ho_x && ho_p) return ho_p;
  if (e->op == E_PARAM || e->op == E_CONST) return e;   /* (a parameter's `nargs` is its function, not a count) */
  if (e->id < ho_cap && ho_map[e->id]) return ho_map[e->id];
  Expr *a = ho_rep(e->a), *b = ho_rep(e->b), *c = e->op != E_CTOR ? ho_rep(e->c) : e->c;
  int grow = e->op == E_CALL && e->k == ho_f, ch = grow || a != e->a || b != e->b || c != e->c;
  Expr **args = e->args;
  if ((e->nargs > 0 && e->args) || grow) {
    Expr **na = A(sizeof *na * (size_t)(e->nargs + 1));
    for (int i = 0; i < e->nargs && e->args; i++) { na[i] = ho_rep(e->args[i]); ch |= na[i] != e->args[i]; }
    if (grow) na[e->nargs] = ho_extra;
    if (ch) args = na;
  }
  Expr *r = e;
  if (ch) { Expr *n = A(sizeof *n); *n = *e; n->id = eid++; n->var = -1; n->a = a; n->b = b; n->c = c; n->args = args; n->nargs = e->nargs + grow; r = hc(n); }
  if (e->id < ho_cap) ho_map[e->id] = r;
  return r;
}
static Expr *ho_apply(Expr *body, const Expr *x, Expr *p, Expr *extra) {
  ho_cap = eid; ho_map = A(sizeof *ho_map * (size_t)(ho_cap ? ho_cap : 1));
  ho_x = x; ho_p = p; ho_extra = extra;
  return ho_rep(body);
}
static Expr *hoist_captured(Expr *entry) {
  for (int round = 0; round <= nfun * 4 + 16; round++) {
    int f = -1; const Expr *x = NULL;
    for (int i = 0; i < nfun && !x; i++) {
      if (funs[i].arity + 1 >= (int)(sizeof(unsigned) * 8) || !funs[i].body) continue;
      ho_f = i; mm_new(MM_SSTR); mm_new(MM_NUM);
      free(fr_memo); fr_memo = calloc((size_t)nfun + 1, 1);
      if ((x = ho_find(funs[i].body))) f = i;
    }
    if (!x) break;
    ho_f = f;
    Expr *p = mke(E_PARAM, x->kind); p->k = funs[f].arity; p->nargs = f; p = hc(p);
    Expr **pn = A(sizeof *pn * (size_t)(funs[f].arity + 1));
    for (int k = 0; k < funs[f].arity; k++) pn[k] = funs[f].pnode ? funs[f].pnode[k] : NULL;
    pn[funs[f].arity] = p; funs[f].pnode = pn;
    if (dbg) DBG("a captured value of f%d is computed once: its parameter %d\n", f, funs[f].arity);
    funs[f].arity++;
    for (int g = 0; g < nfun; g++) if (funs[g].body) funs[g].body = g == f ? ho_apply(funs[g].body, x, p, p) : ho_apply(funs[g].body, NULL, NULL, (Expr *)x);
    entry = ho_apply(entry, NULL, NULL, (Expr *)x);
  }
  return entry;
}

/* Compile F and everything it calls, or return NULL.  `aports`, when given, are the call's arguments: a NUMBER
   one (anum[k]) is passed to the entry, any other is compiled into it as an expression -- `(check (make 7))`
   compiles `make` too, instead of asking the net to build the tree first. */
static Compiled *compile_fn_ex(Net *n, int F, const Port *aports, const int *anum);
static Compiled *compile_fn(Net *n, int F) { return compile_fn_ex(n, F, NULL, NULL); }
/* ONE MATCH PER VALUE.  Code written with tests and selectors -- `(if (is_empty s) a (f (head s) (tail s)))` --
   takes one value apart three times: a test whose answer is a constant per constructor, then a match per field.
   Inside each answer the constructor is KNOWN, so the conditional moves inside the test's match and every
   further match on that value becomes its known branch: one match per path, its fields read from it.  That is
   the shape ownership understands -- the value is consumed once, so its block is reused or freed -- and it is
   what `match` would have written.  (Case-of-known-constructor; nothing is evaluated that was not before.) */
typedef struct { const Expr *s; int i; } Known;
static Known *kn; static int nkn, ckn;
static Expr **r0_memo; static unsigned *r0_gen, r0_g; static int r0_cap;
static int contains(const Expr *e, const Expr *x, int depth);
static Expr *rw(Expr *e);
static Expr *rw_kids(Expr *e) {                      /* e with its children rewritten (itself when none changed) */
  Expr *a = e->a ? rw(e->a) : NULL, *b = e->b ? rw(e->b) : NULL, *c = e->c && e->op != E_CTOR ? rw(e->c) : e->c;
  Expr **args = NULL; int ch = a != e->a || b != e->b || c != e->c;
  if (e->nargs && e->args) {
    args = A(sizeof *args * (size_t)e->nargs);
    for (int i = 0; i < e->nargs; i++) { args[i] = rw(e->args[i]); ch |= args[i] != e->args[i]; }
  }
  if (!ch) return e;
  Expr *n = A(sizeof *n); *n = *e; n->id = eid++; n->var = -1; n->a = a; n->b = b; n->c = c; n->args = args ? args : e->args;
  return hc(n);
}
static Expr *rw(Expr *e) {
  if (!e) return e;
  if (nkn) {                                         /* under a known constructor: only what mentions that value changes */
    int any = 0;
    for (int k = 0; k < nkn && !any; k++) any = contains(e, kn[k].s, 0);
    if (!any) { int sv = nkn; nkn = 0; Expr *r = rw(e); nkn = sv; return r; }
  } else if (e->id < r0_cap && r0_gen[e->id] == r0_g) return r0_memo[e->id];
  Expr *r = NULL;
  if (e->op == E_MATCH)
    for (int k = nkn - 1; k >= 0 && !r; k--) if (kn[k].s == e->a && kn[k].i < e->nargs) r = rw(e->args[kn[k].i]);
  if (!r && e->op == E_IF && e->a->op == E_MATCH && e->a->ci) {
    Expr *m = e->a; int consts = 1, known = 0;
    for (int i = 0; i < m->nargs && consts; i++) consts = m->args[i]->op == E_CONST;
    for (int k = 0; k < nkn; k++) known |= kn[k].s == m->a;
    if (consts && !known && m->a->op != E_CALL) {    /* (a call's value is one evaluation: left to its own match) */
      Expr *n = A(sizeof *n); *n = *m; n->id = eid++; n->var = -1; n->kind = e->kind;
      n->args = A(sizeof(Expr *) * (size_t)m->nargs);
      n->a = rw(m->a);
      for (int i = 0; i < m->nargs; i++) {
        if (nkn >= ckn) kn = realloc(kn, sizeof *kn * (size_t)(ckn = ckn ? ckn * 2 : 8));
        kn[nkn].s = m->a; kn[nkn].i = i; nkn++;
        n->args[i] = rw(m->args[i]->k ? e->b : e->c);
        nkn--;
      }
      r = hc(n);
    }
  }
  if (!r) r = rw_kids(e);
  if (!nkn && e->id < r0_cap) { r0_gen[e->id] = r0_g; r0_memo[e->id] = r; }
  return r;
}
static Expr *one_match(Expr *e) {
  if (r0_cap < eid + 1) { int c = eid * 2 + 64; r0_memo = realloc(r0_memo, sizeof *r0_memo * (size_t)c); r0_gen = realloc(r0_gen, sizeof *r0_gen * (size_t)c); memset(r0_gen + r0_cap, 0, sizeof *r0_gen * (size_t)(c - r0_cap)); r0_cap = c; }
  nkn = 0;
  return rw(e);
}

/* THE CALL'S CONTEXT.  A recursive call is where the driver notices a unit, but the call's value is often taken
   apart at once -- `(alen (fill a 0 n))` is fill's result applied to a match branch -- and folding a structure back
   into the net only for the net to read one field of it is the slow way round.  So the applications around the
   call join the unit: the result applied to arguments (kind 0: a match, a function result applied), or passed to a
   function whose value is known (kind 1).  fn_reduce collects them, outermost last; the unit's value is theirs. */
static Port *cx_port; static int *cx_kind, cx_n, cx_cap;
static int root_mode;   /* fn_match: the unit is the whole expression the program observes, or nothing */
static void cx_push(int kind, Port p) {
  if (cx_n >= cx_cap) { cx_cap = cx_cap ? cx_cap * 2 : 8; cx_port = realloc(cx_port, sizeof *cx_port * (size_t)cx_cap); cx_kind = realloc(cx_kind, sizeof *cx_kind * (size_t)cx_cap); }
  cx_port[cx_n] = p; cx_kind[cx_n] = kind; cx_n++;
}
/* FUSION.  `(check (revcomp (draw n seed) snil) 0 0)`: draw builds a million-cell list, revcomp takes it apart
   cell by cell and nothing else ever sees it.  When a call's argument is the only use of another call's result,
   the consumer takes that argument apart one cell per step (a match at the top of its body, the rest of the
   list handed to itself and to nothing else) and the producer builds it one cell per step (each cell's rest
   is its own next call), the two are one loop: the producer's body, where each cell it would build is the
   consumer's step on that cell -- and the list is never built.  What the consumer does not read of a cell is
   not computed at all.  The fused function is a new function of the unit, so everything after (strictness,
   ownership, destination passing, the parallel forms) sees an ordinary loop. */
typedef struct { int c, j, p, tf, nilb, consb, F, ap, ac; const LinCtor *ncons, *nnil; const Expr *ctail; Expr *tailcall; Expr **hs; } Fuse;
static Expr **fu_mp, **fu_mr, **fu_mc; static int fu_n;   /* copies: of the producer's nodes, its result positions, the consumer's */
static int *fu_occ;
static void fu_count(const Expr *e, unsigned char *seen) {
  if (!e) return;
  fu_occ[e->id]++;
  if (seen[e->id]) return;
  seen[e->id] = 1;
  fu_count(e->a, seen); fu_count(e->b, seen); if (e->op != E_CTOR) fu_count(e->c, seen);
  for (int i = 0; i < e->nargs && e->args; i++) fu_count(e->args[i], seen);
}
static int fu_pj(const Expr *e, int f, int j) { return e && e->op == E_PARAM && e->nargs == f && e->k == j; }
/* the consumer: c's body is a match on parameter j; its rest field reaches only c's own calls, as argument j */
static int fu_cuses(const Expr *e, const Fuse *u, int *tf, unsigned char *seen, int top) {
  if (!e || seen[e->id]) return 1;
  seen[e->id] = 1;
  if (fu_pj(e, u->c, u->j)) return top;             /* (only as the top match's scrutinee) */
  if (e->op == E_FIELD && fu_pj(e->a, u->c, u->j)) return 1;   /* (a head read: checked at the calls) */
  if (e->op == E_CALL && e->k == u->c) {
    const Expr *a = e->args[u->j];
    if (!(a->op == E_FIELD && fu_pj(a->a, u->c, u->j))) return 0;
    if (*tf >= 0 && *tf != a->k) return 0;
    *tf = (int)a->k;
    for (int i = 0; i < e->nargs; i++) if (i != u->j && !fu_cuses(e->args[i], u, tf, seen, 0)) return 0;
    return 1;
  }
  if (!fu_cuses(e->a, u, tf, seen, 0) || !fu_cuses(e->b, u, tf, seen, 0) || (e->op != E_CTOR && !fu_cuses(e->c, u, tf, seen, 0))) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!fu_cuses(e->args[i], u, tf, seen, 0)) return 0;
  return 1;
}
static int fu_tailreads(const Expr *e, const Fuse *u, unsigned char *seen) {   /* the rest field outside a call of c? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_CALL && e->k == u->c) { for (int i = 0; i < e->nargs; i++) if (i != u->j && fu_tailreads(e->args[i], u, seen)) return 1; return 0; }
  if (e->op == E_FIELD && fu_pj(e->a, u->c, u->j) && e->k == u->tf) return 1;
  if (fu_tailreads(e->a, u, seen) || fu_tailreads(e->b, u, seen) || (e->op != E_CTOR && fu_tailreads(e->c, u, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fu_tailreads(e->args[i], u, seen)) return 1;
  return 0;
}
static int fu_mentions_list(const Expr *e, const Fuse *u, unsigned char *seen) {
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (fu_pj(e, u->c, u->j)) return 1;
  if (fu_mentions_list(e->a, u, seen) || fu_mentions_list(e->b, u, seen) || (e->op != E_CTOR && fu_mentions_list(e->c, u, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fu_mentions_list(e->args[i], u, seen)) return 1;
  return 0;
}
static int fu_otherloop(const Expr *e, int c, unsigned char *seen) {
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_CALL && e->k != c) return 1;
  if (fu_otherloop(e->a, c, seen) || fu_otherloop(e->b, c, seen) || (e->op != E_CTOR && fu_otherloop(e->c, c, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fu_otherloop(e->args[i], c, seen)) return 1;
  return 0;
}
static int fu_consumer(Fuse *u) {
  const Expr *B = funs[u->c].body;
  if (!B || B->op != E_MATCH || !fu_pj(B->a, u->c, u->j) || B->nargs != 2 || !B->ci) return 0;
  const LinCtor *k0 = NULL, *k1 = NULL;
  for (int64_t k = 1; lin_ctor_info(k); k++) { const LinCtor *ci = lin_ctor_info(k); if (ci->dt == B->ci->dt) { if (ci->i == 0) k0 = ci; else if (ci->i == 1) k1 = ci; } }
  if (!k0 || !k1) return 0;
  if (k0->k == 0 && k1->k == 2) { u->nilb = 0; u->consb = 1; u->nnil = k0; u->ncons = k1; }
  else if (k1->k == 0 && k0->k == 2) { u->nilb = 1; u->consb = 0; u->nnil = k1; u->ncons = k0; }
  else return 0;
  unsigned char *seen = calloc((size_t)eid + 1, 1);
  int ok = !fu_mentions_list(B->args[u->nilb], u, seen);   /* (the end branch cannot read the list: it is the end) */
  int tf = -1;
  if (ok) { memset(seen, 0, (size_t)eid + 1); ok = fu_cuses(B->args[u->consb], u, &tf, seen, 0) && tf >= 0; }   /* (it must walk the list) */
  u->tf = tf;
  if (ok) { memset(seen, 0, (size_t)eid + 1); ok = !fu_tailreads(B->args[u->consb], u, seen); }
  /* (a step that runs a loop of its own -- a matrix row per cell -- is worth a list: its cells are mapped in
     parallel stretches, and the list costs little beside the work) */
  if (ok) { memset(seen, 0, (size_t)eid + 1); ok = !fu_otherloop(B->args[u->consb], u->c, seen); }
  free(seen);
  return ok;
}
/* the producer: every result is the end, a cell whose rest is a call of itself (at least one is), a call of
   itself, or any other value; it calls itself nowhere else */
static int fu_res(const Expr *e, const Fuse *u, int *guarded, unsigned char *ok) {
  if (!e) return 0;
  if (e->op == E_IF) return fu_res(e->b, u, guarded, ok) && fu_res(e->c, u, guarded, ok);
  if (e->op == E_MATCH) { for (int i = 0; i < e->nargs; i++) if (!fu_res(e->args[i], u, guarded, ok)) return 0; return 1; }
  if (e->op == E_CTOR && e->ci == u->ncons && e->nargs == 2) {
    const Expr *t = e->args[u->tf];
    if (t->op == E_CALL && t->k == u->p) { (*guarded)++; ok[t->id] = 1; }
    return 1;
  }
  if (e->op == E_CALL && e->k == u->p) ok[e->id] = 1;
  return 1;
}
static int fu_stray(const Expr *e, int p, const unsigned char *ok, unsigned char *seen) {   /* a call of itself elsewhere? */
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_CALL && e->k == p && !ok[e->id]) return 1;
  if (fu_stray(e->a, p, ok, seen) || fu_stray(e->b, p, ok, seen) || (e->op != E_CTOR && fu_stray(e->c, p, ok, seen))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fu_stray(e->args[i], p, ok, seen)) return 1;
  return 0;
}
static int fu_producer(Fuse *u) {
  const Expr *B = funs[u->p].body; int g = 0;
  unsigned char *okc = calloc((size_t)eid + 1, 1), *seen = calloc((size_t)eid + 1, 1);
  int r = B && fu_res(B, u, &g, okc) && g > 0 && !fu_stray(B, u->p, okc, seen);
  free(okc); free(seen);
  return r;
}
/* copies, with the parameters renumbered into F's */
static Expr *fu_param(const Fuse *u, int k) { return funs[u->F].pnode[k]; }
static Expr *fu_clone(const Expr *e) { Expr *x = mke(e->op, e->kind); int id = x->id; *x = *e; x->id = id; x->var = -1; x->vscope = 0; return x; }
static Expr *fu_copyP(const Fuse *u, const Expr *e) {   /* a node of the producer's body (not a result position) */
  if (!e) return NULL;
  if (e->op == E_PARAM && e->nargs == u->p) return fu_param(u, (int)e->k);
  if (e->id < fu_n && fu_mp[e->id]) return fu_mp[e->id];
  Expr *x = fu_clone(e);
  x->a = fu_copyP(u, e->a); x->b = fu_copyP(u, e->b); x->c = e->op == E_CTOR ? e->c : fu_copyP(u, e->c);
  if (e->nargs && e->args) { x->args = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) x->args[i] = fu_copyP(u, e->args[i]); }
  x = hc(x);
  if (e->id < fu_n) fu_mp[e->id] = x;
  return x;
}
static int fu_cparam(const Fuse *u, int k) { return u->ap + (k < u->j ? k : k - 1); }
static Expr *fu_copyC(const Fuse *u, const Expr *e) {   /* a node of the consumer's branch, on the cell (hs, tailcall) */
  if (!e) return NULL;
  if (e->op == E_PARAM && e->nargs == u->c) return fu_param(u, fu_cparam(u, (int)e->k));
  if (e->op == E_FIELD && fu_pj(e->a, u->c, u->j)) return u->hs[e->k];   /* (a field of the cell: its value) */
  if (e->id < fu_n && fu_mc[e->id]) return fu_mc[e->id];
  Expr *x;
  if (e->op == E_CALL && e->k == u->c && e->args[u->j]->op == E_FIELD && fu_pj(e->args[u->j]->a, u->c, u->j)) {
    /* the step to the rest of the list: the producer's next step, or the consumer on a rest that is not one */
    const Expr *t = u->ctail;
    if (t->op == E_CALL && t->k == u->p) {
      x = mke(E_CALL, e->kind); x->k = u->F; x->nargs = u->ap + u->ac - 1; x->args = A(sizeof(Expr *) * (size_t)x->nargs);
      for (int i = 0; i < u->ap; i++) x->args[i] = fu_copyP(u, t->args[i]);
      for (int i = 0; i < u->ac; i++) if (i != u->j) x->args[fu_cparam(u, i)] = fu_copyC(u, e->args[i]);
    } else {
      x = fu_clone(e); x->args = A(sizeof(Expr *) * (size_t)e->nargs);
      for (int i = 0; i < e->nargs; i++) x->args[i] = i == u->j ? fu_copyP(u, t) : fu_copyC(u, e->args[i]);
    }
  } else {
    x = fu_clone(e);
    x->a = fu_copyC(u, e->a); x->b = fu_copyC(u, e->b); x->c = e->op == E_CTOR ? e->c : fu_copyC(u, e->c);
    if (e->nargs && e->args) { x->args = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) x->args[i] = fu_copyC(u, e->args[i]); }
  }
  x = hc(x);
  if (e->id < fu_n) fu_mc[e->id] = x;
  return x;
}
static Expr *fu_consumer_on(Fuse *u, const Expr *list) {   /* c applied to a list that is not a cell of the producer's */
  Expr *x = mke(E_CALL, funs[u->c].body->kind); x->k = u->c; x->nargs = u->ac; x->args = A(sizeof(Expr *) * (size_t)u->ac);
  for (int i = 0; i < u->ac; i++) x->args[i] = i == u->j ? (Expr *)list : fu_param(u, fu_cparam(u, i));
  return hc(x);
}
static Expr *fu_res_copy(Fuse *u, const Expr *e) {   /* a result position of the producer */
  if (e->id < fu_n && fu_mr[e->id]) return fu_mr[e->id];
  const Expr *B = funs[u->c].body; Expr *x;
  if (e->op == E_IF) { x = fu_clone(e); x->a = fu_copyP(u, e->a); x->b = fu_res_copy(u, e->b); x->c = fu_res_copy(u, e->c); }
  else if (e->op == E_MATCH) {
    x = fu_clone(e); x->a = fu_copyP(u, e->a); x->args = A(sizeof(Expr *) * (size_t)e->nargs);
    for (int i = 0; i < e->nargs; i++) x->args[i] = fu_res_copy(u, e->args[i]);
  } else if (e->op == E_CTOR && e->ci == u->nnil) {
    memset(fu_mc, 0, sizeof *fu_mc * (size_t)fu_n);
    x = fu_copyC(u, B->args[u->nilb]);
  } else if (e->op == E_CTOR && e->ci == u->ncons && e->nargs == 2) {
    Expr *hs[2]; for (int i = 0; i < 2; i++) hs[i] = i == u->tf ? NULL : fu_copyP(u, e->args[i]);
    u->hs = hs; u->ctail = e->args[u->tf];
    memset(fu_mc, 0, sizeof *fu_mc * (size_t)fu_n);   /* (each cell is its own instance of the step) */
    x = fu_copyC(u, B->args[u->consb]);
  } else if (e->op == E_CALL && e->k == u->p) {
    x = mke(E_CALL, funs[u->c].body->kind); x->k = u->F; x->nargs = u->ap + u->ac - 1; x->args = A(sizeof(Expr *) * (size_t)x->nargs);
    for (int i = 0; i < u->ap; i++) x->args[i] = fu_copyP(u, e->args[i]);
    for (int i = u->ap; i < x->nargs; i++) x->args[i] = fu_param(u, i);
  } else x = fu_consumer_on(u, fu_copyP(u, e));
  x = hc(x);
  if (e->id < fu_n) fu_mr[e->id] = x;
  return x;
}
/* the call site: replaced through every body and the entry */
static Expr *fu_from, *fu_to; static Expr **fu_mrep;
static Expr *fu_replace(Expr *e) {
  if (!e) return NULL;
  if (e == fu_from) return fu_to;
  if (e->id < fu_n && fu_mrep[e->id]) return fu_mrep[e->id];
  Expr *a = fu_replace(e->a), *b = fu_replace(e->b), *c = e->op == E_CTOR ? e->c : fu_replace(e->c);
  int ch = a != e->a || b != e->b || c != e->c; Expr **na = NULL;
  if (e->nargs && e->args) {
    na = A(sizeof(Expr *) * (size_t)e->nargs);
    for (int i = 0; i < e->nargs; i++) { na[i] = fu_replace(e->args[i]); ch |= na[i] != e->args[i]; }
  }
  Expr *x = e;
  if (ch) { x = fu_clone(e); x->a = a; x->b = b; x->c = c; if (na) x->args = na; x = hc(x); }
  if (e->id < fu_n) fu_mrep[e->id] = x;
  return x;
}
static int fu_find(const Expr *e, unsigned char *seen, Fuse *u) {
  if (!e || seen[e->id]) return 0;
  seen[e->id] = 1;
  if (e->op == E_CALL && e->k >= 0 && e->k < nfun && funs[e->k].body && !e->drops)
    for (int j = 0; j < e->nargs; j++) {
      const Expr *P = e->args[j];
      if (P->op != E_CALL || P->k == e->k || P->k < 0 || P->k >= nfun || !funs[P->k].body || fu_occ[P->id] != 1) continue;
      memset(u, 0, sizeof *u); u->c = (int)e->k; u->j = j; u->p = (int)P->k; u->ap = funs[u->p].arity; u->ac = funs[u->c].arity;
      if (u->ap + u->ac - 1 > (int)(sizeof(unsigned) * 8)) continue;   /* (a function's parameters are a bit set: see strict) */
      int okc = fu_consumer(u), okp = okc && fu_producer(u);
      if (dbg > 1) DBG("[fuse? f%d arg %d <- f%d: consumer %d producer %d]\n", u->c, j, u->p, okc, okp);
      if (okp) { fu_from = (Expr *)e; return 1; }
    }
  if (fu_find(e->a, seen, u) || fu_find(e->b, seen, u) || (e->op != E_CTOR && fu_find(e->c, seen, u))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (fu_find(e->args[i], seen, u)) return 1;
  return 0;
}
/* ONE FUNCTION, ONE COPY.  The net holds one copy of a definition per use, so a unit that uses `seq` eight times
   meets eight copies of `draw` -- and eight equal calls of eight functions are eight computations, where the
   program has one.  Functions of the unit that are the same function (the same body, with their calls of
   each other the same too: a partition refined to a fixpoint) are merged into one, after which equal calls
   are one node and the region binder computes them once. */
typedef struct { char *s; size_t n, cap; } Sig;
static void sig_put(Sig *g, const char *fmt, ...) {
  va_list ap; char tmp[96]; va_start(ap, fmt); int k = vsnprintf(tmp, sizeof tmp, fmt, ap); va_end(ap);
  if (k < 0) return;
  if (g->n + (size_t)k + 1 > g->cap) { g->cap = (g->n + (size_t)k + 1) * 2; g->s = realloc(g->s, g->cap); }
  memcpy(g->s + g->n, tmp, (size_t)k + 1); g->n += (size_t)k;
}
static int *dd_cls, *dd_num, dd_next;
static void dd_sig(const Expr *e, int f, Sig *g) {   /* the body as a DAG: each node once, its children by number */
  if (!e) { sig_put(g, "_"); return; }
  if (dd_num[e->id]) { sig_put(g, "#%d", dd_num[e->id]); return; }
  dd_num[e->id] = ++dd_next;
  if (e->op == E_PARAM) { if (e->nargs == f) sig_put(g, "P%" PRId64 "", e->k); else sig_put(g, "Q%d.%" PRId64 "", e->nargs, e->k); return; }
  sig_put(g, "(%d %" PRId64 " %d %d %p %d %d", e->op, e->op == E_CALL ? (int64_t)dd_cls[e->k] : e->k, e->kind, e->nargs, (const void *)e->ci, e->untag, e->box);
  if (e->op == E_CALL && e->k == f) sig_put(g, "S");
  dd_sig(e->a, f, g); dd_sig(e->b, f, g); if (e->op != E_CTOR) dd_sig(e->c, f, g); else sig_put(g, "c");
  for (int i = 0; i < e->nargs && e->args; i++) dd_sig(e->args[i], f, g);
  sig_put(g, ")");
}
static Expr **dd_map; static int dd_n; static int *dd_rep;
static Expr *dd_rewrite(Expr *e, int f) {   /* calls of a merged function become calls of its representative */
  if (!e) return NULL;
  if (e->id < dd_n && dd_map[e->id]) return dd_map[e->id];
  Expr *x = e;
  if (e->op == E_PARAM) { if (e->nargs >= 0 && e->nargs < nfun && dd_rep[e->nargs] != e->nargs) x = funs[dd_rep[e->nargs]].pnode[e->k]; }
  else {
    Expr *a = dd_rewrite(e->a, f), *b = dd_rewrite(e->b, f), *c = e->op == E_CTOR ? e->c : dd_rewrite(e->c, f);
    int ch = a != e->a || b != e->b || c != e->c || (e->op == E_CALL && dd_rep[e->k] != e->k); Expr **na = NULL;
    if (e->nargs && e->args) { na = A(sizeof(Expr *) * (size_t)e->nargs); for (int i = 0; i < e->nargs; i++) { na[i] = dd_rewrite(e->args[i], f); ch |= na[i] != e->args[i]; } }
    if (ch) { x = fu_clone(e); x->a = a; x->b = b; x->c = c; if (na) x->args = na; if (e->op == E_CALL) x->k = dd_rep[e->k]; x = hc(x); }
  }
  if (e->id < dd_n) dd_map[e->id] = x;
  return x;
}
static void dedup_funs(Expr **entry) {
  if (nfun < 2) return;
  dd_cls = calloc((size_t)nfun, sizeof *dd_cls);
  for (int i = 0; i < nfun; i++) dd_cls[i] = funs[i].body && funs[i].pnode && !funs[i].known && !funs[i].outer ? funs[i].arity : -1 - i;
  char **sg = calloc((size_t)nfun, sizeof *sg);
  for (int round = 0; round < nfun + 1; round++) {   /* refine: same class and same signature under the classes */
    for (int i = 0; i < nfun; i++) {
      free(sg[i]); sg[i] = NULL;
      if (dd_cls[i] < 0) continue;
      Sig g = { NULL, 0, 0 }; dd_num = calloc((size_t)eid + 1, sizeof *dd_num); dd_next = 0;
      sig_put(&g, "%d|", dd_cls[i]); dd_sig(funs[i].body, i, &g); free(dd_num); sg[i] = g.s;
    }
    int *nc = malloc(sizeof *nc * (size_t)nfun), changed = 0;
    for (int i = 0; i < nfun; i++) {
      nc[i] = dd_cls[i] < 0 ? dd_cls[i] : i;
      if (dd_cls[i] >= 0) for (int j = 0; j < i; j++) if (dd_cls[j] >= 0 && !strcmp(sg[i], sg[j])) { nc[i] = nc[j]; break; }
    }
    /* (renumber to the first member, so the classes are comparable across rounds) */
    for (int i = 0; i < nfun; i++) if (dd_cls[i] >= 0 && nc[i] != dd_cls[i]) changed = 1;
    for (int i = 0; i < nfun; i++) dd_cls[i] = nc[i];
    free(nc);
    if (!changed) break;
  }
  for (int i = 0; i < nfun; i++) free(sg[i]);
  free(sg);
  dd_rep = malloc(sizeof *dd_rep * (size_t)nfun); int merged = 0;
  for (int i = 0; i < nfun; i++) { dd_rep[i] = i; if (dd_cls[i] >= 0) for (int j = 0; j < i; j++) if (dd_cls[j] == dd_cls[i]) { dd_rep[i] = j; merged++; if (dbg > 1) DBG("[f%d is f%d]\n", i, j); break; } }
  if (merged) {
    dd_n = eid; dd_map = calloc((size_t)dd_n + 1, sizeof *dd_map);
    *entry = dd_rewrite(*entry, -1);
    for (int i = 0; i < nfun; i++) if (dd_rep[i] == i) funs[i].body = dd_rewrite(funs[i].body, i);
    free(dd_map);
    if (dbg) DBG("merged %d copies of the unit's functions into the ones they copy\n", merged);
  }
  free(dd_rep); free(dd_cls); dd_cls = NULL;
}
static void fuse_lists(Expr **entry) {
  for (int round = 0; round < nfun + 1; round++) {
    fu_n = eid;
    fu_occ = calloc((size_t)fu_n + 1, sizeof *fu_occ);
    unsigned char *seen = calloc((size_t)fu_n + 1, 1);
    fu_count(*entry, seen); for (int i = 0; i < nfun; i++) fu_count(funs[i].body, seen);
    memset(seen, 0, (size_t)fu_n + 1);
    Fuse u; int found = fu_find(*entry, seen, &u);
    for (int i = 0; !found && i < nfun; i++) found = fu_find(funs[i].body, seen, &u);
    free(seen); free(fu_occ); fu_occ = NULL;
    if (!found) return;
    /* the fused function */
    if (nfun >= funcap) funs = realloc(funs, (size_t)(funcap = funcap ? funcap * 2 : 8) * sizeof *funs);
    int F = u.F = nfun++, ar = u.ap + u.ac - 1;
    funs[F].lam = -1; funs[F].arity = ar; funs[F].strict = ~0u; funs[F].known = NULL; funs[F].outer = NULL; funs[F].body = NULL;
    funs[F].pnode = A(sizeof(Expr *) * (size_t)(ar ? ar : 1));
    for (int i = 0; i < ar; i++) { Expr *q = mke(E_PARAM, 1); q->k = i; q->nargs = F; funs[F].pnode[i] = q; }
    fu_mp = calloc((size_t)fu_n + 1, sizeof *fu_mp); fu_mr = calloc((size_t)fu_n + 1, sizeof *fu_mr); fu_mc = calloc((size_t)fu_n + 1, sizeof *fu_mc);
    funs[F].body = fu_res_copy(&u, funs[u.p].body);
    free(fu_mp); free(fu_mr); free(fu_mc);
    /* the call site: F on the producer's arguments and the consumer's others */
    const Expr *P = fu_from->args[u.j];
    Expr *call = mke(E_CALL, fu_from->kind); call->k = F; call->nargs = ar; call->args = A(sizeof(Expr *) * (size_t)(ar ? ar : 1));
    for (int i = 0; i < u.ap; i++) call->args[i] = P->args[i];
    for (int i = 0; i < u.ac; i++) if (i != u.j) call->args[fu_cparam(&u, i)] = fu_from->args[i];
    fu_to = hc(call);
    fu_mrep = calloc((size_t)fu_n + 1, sizeof *fu_mrep);
    *entry = fu_replace(*entry);
    for (int i = 0; i < nfun; i++) if (i != F) funs[i].body = fu_replace(funs[i].body);
    free(fu_mrep);
    if (dbg) DBG("fused f%d's list into f%d: f%d\n", u.p, u.c, F);
  }
}
/* A DATATYPE SHAPE's functions: its drop, its copy, and (counted) its SHARE -- a structure handed to another thread
   is marked as visible to more than one (its counts negated, and from then on atomic), all the way down to what is
   already shared -- so a positive count is only ever touched by the one thread that can see the block. */
static void gen_data_fns(Buf *dbp, int d) {
  if (drop_sh[d].dt == VEC_DT) {                     /* a vector: {length, capacity, elements} (OWNED VECTORS) */
    Shape es = drop_sh[d].a && drop_sh[d].a->n ? drop_sh[d].a->s[0] : (Shape){ 0, NULL, NULL };
    int ed = es.k == 5 && es.dt ? drop_fn(es) : -1;
    put(dbp, "static void lin_drop%d_(int64_t v) { int64_t *o = (int64_t *)v; if (!lin_dec(o)) return;", d);
    if (ed >= 0) put(dbp, " for (int64_t i = 0; i < o[0]; i++) lin_drop%d(o[i + 2]);", ed);
    put(dbp, " lin_free(o, o[1] + 2); }\n");
    put(dbp, "static int64_t lin_copy%d(int64_t v) { if (v & 1) return v; int64_t *o = (int64_t *)v, *n = lin_alloc(o[1] + 2); __builtin_memcpy(n, o, (size_t)(o[0] + 2) * 8);", d);
    if (ed >= 0) put(dbp, " for (int64_t i = 0; i < o[0]; i++) lin_dup(n[i + 2]);");
    put(dbp, " return (int64_t)n; }\n");
    {
      put(dbp, "static void lin_share%d(int64_t v) { if (lin_mt || (v & 1)) return; int64_t *o = (int64_t *)v; if (o[-1] < 0) return; o[-1] = -o[-1];", d);
      if (ed >= 0) put(dbp, " for (int64_t i = 0; i < o[0]; i++) lin_share%d(o[i + 2]);", ed);
      put(dbp, " }\n");
      put(dbp, "static void lin_freeze%d(int64_t v) { if (lin_mt || (v & 1)) return; int64_t *o = (int64_t *)v; if (o[-1] <= 0) return; o[-1] = 0;", d);
      if (ed >= 0) put(dbp, " for (int64_t i = 0; i < o[0]; i++) lin_freeze%d(o[i + 2]);", ed);
      put(dbp, " }\n");
    }
    return;
  }
#define db (*dbp)
        Shape ds = drop_sh[d]; const char *dt = ds.dt; int box = -1, untag = dt_boxed(dt, &box) == 1; const LinCtor *c;
#define FS(k, j) field_shape(sh_fld, sh_nctor, c, k, j, ds)
#define FDROP(k, j) (field_live(c, j) && k <= sh_nctor && FS(k, j).k == 5 && FS(k, j).dt)
        put(dbp, "static void lin_drop%d_(int64_t v) { while (!(v & 1)) { int64_t *o = (int64_t *)v; int64_t nx = 1;%s%s", d, " if (!lin_dec(o)) return;", untag ? " {" : " switch (o[0]) {");
        for (int64_t k = 1; (c = lin_ctor_info(k)); k++) {
          if (c->dt != dt || c->k == 0) continue;
          if (!untag) put(dbp, " case %d: {", c->i);
          int last = -1;
          for (int j = 0; j < c->k; j++) if (FDROP(k, j)) last = j;
          for (int j = 0; j < c->k; j++) {
            if (!FDROP(k, j)) continue;
            Shape fs = FS(k, j);
            if (j == last && fs.dt == dt && fs.a == ds.a) put(dbp, " nx = o[%d];", j + !untag);     /* (the rest of a list: the loop, not a call) */
            else put(dbp, " lin_drop%d(o[%d]);", drop_fn(fs), j + !untag);
          }
          put(dbp, " lin_free(o, %d);", c->k + !untag);
          if (!untag) put(dbp, " break; }");
        }
        put(dbp, " } v = nx; } }\n");
      /* a COPY of what a drop would free -- the owned structure, down the same fields -- sharing the rest */
      {
        put(dbp, "static int64_t lin_copy%d(int64_t v) { int64_t r = v, *dst = &r; while (!(v & 1)) { int64_t *o = (int64_t *)v, *t = 0; int64_t nx = 1;%s", d, untag ? " {" : " switch (o[0]) {");
        for (int64_t k = 1; (c = lin_ctor_info(k)); k++) {
          if (c->dt != dt || c->k == 0) continue;
          if (!untag) put(dbp, " case %d: {", c->i);
          put(dbp, " int64_t *n = lin_alloc(%d); __builtin_memcpy(n, o, %d * 8); *dst = (int64_t)n;", c->k + !untag, c->k + !untag);
          int last = -1;
          for (int j = 0; j < c->k; j++) if (FDROP(k, j)) last = j;
          for (int j = 0; j < c->k; j++) {
            if (!FDROP(k, j)) continue;
            Shape fs = FS(k, j);
            if (j == last && fs.dt == dt && fs.a == ds.a) put(dbp, " nx = o[%d]; t = &n[%d];", j + !untag, j + !untag);
            else put(dbp, " n[%d] = lin_copy%d(o[%d]);", j + !untag, drop_fn(fs), j + !untag);
          }
          if (!untag) put(dbp, " break; }");
        }
        put(dbp, " } if (!t) return r; dst = t; v = nx; } *dst = v; return r; }\n");
      }
      {
        put(dbp, "static void lin_share%d(int64_t v) { if (lin_mt) return; while (!(v & 1)) { int64_t *o = (int64_t *)v; int64_t nx = 1; if (o[-1] < 0) return; o[-1] = -o[-1];%s", d, untag ? " {" : " switch (o[0]) {");
        for (int64_t k = 1; (c = lin_ctor_info(k)); k++) {
          if (c->dt != dt || c->k == 0) continue;
          if (!untag) put(dbp, " case %d: {", c->i);
          int last = -1;
          for (int j = 0; j < c->k; j++) if (FDROP(k, j)) last = j;
          for (int j = 0; j < c->k; j++) {
            if (!FDROP(k, j)) continue;
            Shape fs = FS(k, j);
            if (j == last && fs.dt == dt && fs.a == ds.a) put(dbp, " nx = o[%d];", j + !untag);
            else put(dbp, " lin_share%d(o[%d]);", drop_fn(fs), j + !untag);
          }
          if (!untag) put(dbp, " break; }");
        }
        put(dbp, " } v = nx; } }\n");
        /* ...and FROZEN: never counted again, freed with the unit (what concurrent tasks all read: no count of it
           is ever written, so no core waits on another's) */
        put(dbp, "static void lin_freeze%d(int64_t v) { if (lin_mt) return; while (!(v & 1)) { int64_t *o = (int64_t *)v; int64_t nx = 1; if (o[-1] <= 0) return; o[-1] = 0;%s", d, untag ? " {" : " switch (o[0]) {");
        for (int64_t k = 1; (c = lin_ctor_info(k)); k++) {
          if (c->dt != dt || c->k == 0) continue;
          if (!untag) put(dbp, " case %d: {", c->i);
          int last = -1;
          for (int j = 0; j < c->k; j++) if (FDROP(k, j)) last = j;
          for (int j = 0; j < c->k; j++) {
            if (!FDROP(k, j)) continue;
            Shape fs = FS(k, j);
            if (j == last && fs.dt == dt && fs.a == ds.a) put(dbp, " nx = o[%d];", j + !untag);
            else put(dbp, " lin_freeze%d(o[%d]);", drop_fn(fs), j + !untag);
          }
          if (!untag) put(dbp, " break; }");
        }
        put(dbp, " } v = nx; } }\n");
      }
#undef FS
#undef FDROP
#undef db
}
static Compiled *compile_fn_ex1(Net *n, int F, const Port *aports, const int *anum);
static Compiled *compile_fn_ex(Net *n, int F, const Port *aports, const int *anum) {
  vop_used = 0;
  Compiled *r = compile_fn_ex1(n, F, aports, anum);
  if (!r && vop_used && !vop_off) { vop_off = 1; r = compile_fn_ex1(n, F, aports, anum); vop_off = 0; }   /* (see OWNED VECTORS) */
  return r;
}
static Compiled *compile_fn_ex1(Net *n, int F, const Port *aports, const int *anum) {
  N = n; failed = 0; fuel = 20000000; nfun = 0; eid = 0; nvar = 0; mr_ntok = 0; hc_reset(); uses_data = 0; rc_bor = NULL; rc_pure = NULL; rc_mt = 0;
  /* a one-time compile: the budget only stops an evaluation that does not end */
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
  nesh = 0; esh_data = 0; n_inp = 0; inp_on = aports != NULL;
  int *rt_of = NULL;
  if (aports) {                                      /* the runtime arguments: numbers, and data passed in (anum 2) */
    int ar = fun_arity(F);
    if (esh_cap < ar + 1) esh = realloc(esh, sizeof *esh * (size_t)(esh_cap = ar + 16));
    rt_of = A(sizeof *rt_of * (size_t)(ar + 1));
    for (int k = 0; k < ar; k++) {
      rt_of[k] = -1;
      if (anum[k] && !(known && known[k])) { rt_of[k] = nesh; esh[nesh++] = anum[k] == 2 ? (Shape){ 0, NULL } : (Shape){ 1, NULL }; esh_data |= anum[k] == 2; }
    }
  }
  /* (the copy choices are the CALLEE's: its body is what the unit replaces nothing of.  The arguments and the context
     are the call site's, which may itself be shared between copies -- a value read there for one copy and folded
     into the shared call would be every copy's -- so they are read without them.) */
  xing_on = 1;
  int body_ok = compile_body_spec(F, NULL, known) == 0;
  xing_on = 0;
  if (body_ok && !failed) {
    arity = funs[0].arity;
    /* THE ENTRY: f0 applied to the call's arguments -- the entry's own parameters, or expressions */
    int nnum = 0;
    Expr *entry = mke(E_CALL, funs[0].body->kind); entry->k = 0; entry->nargs = arity; entry->args = A(sizeof(Expr *) * (size_t)(arity ? arity : 1));
    for (int k = 0; k < arity && !failed; k++) {
      if (known && known[k]) { Expr *z = mke(E_CONST, 1); z->k = 0; entry->args[k] = hc(z); }   /* (bound in the copy) */
      else if (!aports || anum[k]) { Expr *pe = mke(E_PARAM, 1); pe->k = aports ? rt_of[k] : nnum; nnum++; pe->nargs = -1; entry->args[k] = hc(pe); }
      else { cur_fid = -1; entry->args[k] = to_expr(eval(aports[k], NULL)); if (!entry->args[k]) failed = 1; }
    }
    if (failed) { arena_free(); return NULL; }        /* (a function the entry reached may be half-built) */
    if (aports) nnum = nesh;                         /* (the inputs met in the arguments come after them) */
    entry = hc(entry);
    if (aports && cx_n) {                              /* the context, applied to the call's value */
      V *v = mkv(V_SYM); v->e = entry; cur_fid = -1;
      for (int i = 0; i < cx_n && v && !failed; i++)
        v = cx_kind[i] == 2 ? eval(cx_port[i], NULL)   /* (the whole expression: the call is met again inside it) */
          : cx_kind[i] == 0 ? apply(v, lzp(cx_port[i], NULL)) : apply(eval(cx_port[i], NULL), ready(v));
      Expr *x = v && !failed ? to_expr(v) : NULL;
      if (!x || failed) { arena_free(); return NULL; }
      entry = x; nnum = nesh;
    }
    entry = hoist_captured(entry); arity = funs[0].arity;   /* (the unit's own function may have gained a parameter) */
    r0_g++;
    for (int i = 0; i < nfun; i++) funs[i].body = one_match(funs[i].body);
    entry = one_match(entry);
    dedup_funs(&entry);
    if (!getenv("LIN_FN_NOFUSE")) fuse_lists(&entry);
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
    Shape rshape = safe ? unit_shapes(entry) : (Shape){ 1, NULL };
    if (safe) rshape = shape_versions(&entry, rshape);
    if (safe && sh_bad) { safe = 0; DBG("declined: a value taken apart as something it is not (a number read as cells?)\n"); }
    for (int k = 0; safe && k < nesh; k++)            /* a data argument is read in by its shape: it must be known */
      if (esh[k].k && !shape_closed(esh[k], 0)) {
        safe = 0; DBG("declined: argument %d's shape is not known (%d %s)\n", k, esh[k].k, esh[k].dt ? esh[k].dt : "");
        if (dbg > 1) for (int64_t c = 1; c <= sh_nctor; c++) { const LinCtor *ci = lin_ctor_info(c); if (!sh_built[c]) continue; DBG("  %s built:", ci->name); for (int jj = 0; jj < ci->k; jj++) fprintf(stderr, " %d", sh_fld[c][jj].k); fprintf(stderr, "\n"); }
      }
    int numeric = safe && (result_numeric(entry) || rshape.k == 1 || rshape.k == 3);   /* (a field read the shapes prove a number) */
    int rbool = rshape.k == 3 || (rshape.k != 1 && entry->kind == 3);
    if (safe && vop_used) {                            /* (a vector the net gives or is given is its trie: see OWNED VECTORS) */
      int cross = sh_has_vec(rshape);
      for (int k = 0; k < nesh; k++) cross |= sh_has_vec(esh[k]);
      if (!cross && (!numeric || esh_data))
        for (int64_t c = 1; c <= sh_nctor && !cross; c++) { const LinCtor *ci = lin_ctor_info(c); for (int j = 0; ci && j < ci->k; j++) cross |= sh_has_vec(sh_fld[c][j]); }
      if (cross && !vt_find()) { safe = 0; DBG("declined: a vector crosses the unit's edge, and the trie it is on the net is not loaded\n"); }
    }
    fld_live = NULL;
    if (safe) fields_live(entry, !numeric);
    if (safe && !numeric) {                            /* a STRUCTURE: folded if its shape is known to the leaves */
      if (!shape_closed(rshape, 0) || rshape.k != 5) { safe = 0; DBG("declined: the result's shape is not known (a field holding different kinds of value)\n"); }
    }
    if (!safe) {}
    else {
      int unit_data; { mm_new(MM_NUM); unit_data = has_data(entry); for (int i = 0; !unit_data && i < nfun; i++) unit_data = has_data(funs[i].body); }
      if (unit_data) {                                 /* (see EXPLICIT BINDING, and MEMORY: numbers alone need neither) */
        anf_n = 0;
        for (int i = 0; i < nfun; i++) if (funs[i].body) { fscope++; emitting = i; funs[i].body = anf_region(funs[i].body, 1); }
        fscope++; emitting = -1; entry = anf_region(entry, 0);
        fscope++;
        lift(); mem_rc(&entry);
        if (dbg > 3) { for (int i = 0; i < nfun; i++) { DBG("[f%d:]\n", i); ex_dump(funs[i].body, 1); } DBG("[entry:]\n"); ex_dump(entry, 1); }
      }
      Buf b = nbuf(4096), fb = nbuf(4096), pre = nbuf(1024), pb = nbuf(1024);
      lift();
      for (int i = 0; i < nfun; i++) { put(&fb, "static int64_t f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0); put(&fb, ");\n"); }
      int ok = 1;
      unsigned char *hd = A((size_t)nfun + 1);         /* which functions get a destination-passing form */
      for (int i = 0; i < nfun; i++) dp_scan(funs[i].body, i, hd);
      for (int ch = 1; ch; ) { ch = 0; for (int i = 0; i < nfun; i++) if (hd[i]) ch |= dp_scan(funs[i].body, i, hd); }
      for (int i = 0; i < nfun; i++) if (hd[i]) { put(&fb, "static int64_t f%d_d(int64_t *dst", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", int64_t p%d", j); fv_params(&fb, i, 1, 1); put(&fb, ");\n"); }
      hasd = hd;
      plinfo = A(sizeof *plinfo * (size_t)(nfun + 1)); pl_done = A((size_t)nfun + 1);
      for (int i = 0; i < nfun; i++) plinfo[i].acc = -1;
      for (int i = 0; ok && i < nfun; i++) {
        put(&fb, "static int64_t f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0);
        emitting = i; fscope++;
        if (hd[i]) {                                   /* the plain form: the other, given a local to write */
          put(&fb, ") { int64_t r = 0; f%d_d(&r", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", p%d", j); fv_params(&fb, i, 0, 1); put(&fb, "); return r; }\n");
          if (pm_cand(i)) {                             /* (see pm_cand) its loop, a stretch of its loop, and who decides */
            int K = pm_k, tf = pm_tf, np = funs[i].arity + nfv[i];
            Buf pt = nbuf(256), pu = nbuf(256);          /* the parameters, typed and not */
            for (int j = 0; j < funs[i].arity; j++) { put(&pt, ", int64_t p%d", j); put(&pu, ", p%d", j); }
            fv_params(&pt, i, 1, 1); fv_params(&pu, i, 0, 1);
            put(&fb, "static int64_t f%d_ds(int64_t *dst%s);\nstatic int64_t f%d_dp(int64_t *dst%s, int64_t stop);\n", i, pt.s, i, pt.s);
            put(&fb, "static int64_t f%d_ds(int64_t *dst%s) { LIN_ENTER; ", i, pt.s);
            dp_self = 1; tailpos = 1; ok = emit_fn_body(&fb, &pre, funs[i].body); tailpos = 0; put(&fb, "; }\n");
            fscope++;
            put(&fb, "static int64_t f%d_dp(int64_t *dst%s, int64_t stop) { LIN_ENTER; if (p%d == stop) return (int64_t)dst; ", i, pt.s, K);
            dp_self = 2; tailpos = 1; ok = ok && emit_fn_body(&fb, &pre, funs[i].body); tailpos = 0; put(&fb, "; }\n");
            dp_self = 0;
            put(&fb, "typedef struct { int64_t *dst; int64_t p[%d]; int64_t stop, r; } PM%d;\n", np ? np : 1, i);
            put(&fb, "static void *pmrun%d(void *v) { PM%d *s = v; LIN_TASK_START((size_t)256 << 20); s->r = f%d_dp(s->dst", i, i, i);
            for (int j = 0; j < np; j++) put(&fb, ", s->p[%d]", j);
            put(&fb, ", s->stop); return 0; }\n");
            put(&fb, "static int lin_threads_; static int lin_pm_busy;\n");
            put(&fb, "static int64_t f%d_d(int64_t *dst%s) {\n  int T = lin_threads_; int64_t n = 0;\n", i, pt.s);
            put(&fb, "  if (T < 2 || lin_pm_busy) return f%d_ds(dst%s);\n", i, pu.s);
            put(&fb, "  for (int64_t q = p%d; !(q & 1) && n < (int64_t)T * 4; q = ((int64_t *)q)[%d]) n++;\n", K, tf);
            put(&fb, "  if (n < (int64_t)T * 4 || !__sync_bool_compare_and_swap(&lin_pm_busy, 0, 1)) return f%d_ds(dst%s);\n", i, pu.s);
            put(&fb, "  for (int64_t q = p%d; !(q & 1); q = ((int64_t *)q)[%d]) n++;\n  n -= (int64_t)T * 4;\n", K, tf);
            put(&fb, "  pthread_t t[T]; PM%d s[T]; int64_t head[T]; int64_t q = p%d; int started = 0;\n", i, K);
            put(&fb, "  pthread_attr_t ra; pthread_attr_init(&ra); pthread_attr_setstacksize(&ra, (size_t)256 << 20);\n");
            put(&fb, "  for (int k = 0; k < T; k++) {\n    PM%d x = { k ? &head[k] : dst, {", i);
            { int c = 0; for (int j = 0; j < funs[i].arity; j++) put(&fb, j == K ? "%sq" : "%sp%d", c++ ? ", " : "", j);
              Buf fu = nbuf(64); fv_params(&fu, i, 0, 0); if (nfv[i]) put(&fb, "%s%s", c ? ", " : "", fu.s); free(fu.s); if (!np) put(&fb, "0"); }
            put(&fb, "}, 0, 0 };\n    if (k < T - 1) { for (int64_t j = n / T; j > 0; j--) q = ((int64_t *)q)[%d]; x.stop = q; }\n    s[k] = x;\n  }\n", tf);
            {                             /* (counted: the list split among the threads, and what they all read, marked shared) */
              Buf sh = nbuf(64); rc_mark = "share"; rc_share_params(&sh, i, NULL, NULL, NULL); rc_mark = "freeze";
              for (int q = 0; q < nfv[i]; q++) { const FV *v = &fvs[i][q];
                int sf = v->h >= 0 && v->h < nfun && funs[v->h].pnode && funs[v->h].pnode[v->k] ? rc_share_fn(shape_of(funs[v->h].pnode[v->k])) : (rc_mt = 1, -1);
                if (sf >= 0) put(&sh, "lin_share%d(l%d_%" PRId64 "); ", sf, v->h + 1, v->k); }
              if (sh.len) put(&fb, "  %s\n", sh.s);
              free(sh.s);
            }
            put(&fb, "  for (int k = 0; k < T; k++) { if (pthread_create(&t[k], &ra, pmrun%d, &s[k])) break; started++; }\n", i);
            put(&fb, "  for (int k = 0; k < started; k++) pthread_join(t[k], 0);\n  pthread_attr_destroy(&ra);\n");
            put(&fb, "  if (started < T) lin_fn_aborted = 1;\n  lin_pm_busy = 0;\n  (void)LIN_JOINED;\n");
            put(&fb, "  for (int k = 0; k < T - 1; k++) *(int64_t *)s[k].r = head[k + 1];\n  return 0;\n}\n");
            free(pt.s); free(pu.s);
            if (dbg) DBG("f%d maps its list in parallel\n", i);
          } else {
          put(&fb, "static int64_t f%d_d(int64_t *dst", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", int64_t p%d", j); fv_params(&fb, i, 1, 1); put(&fb, ") { LIN_ENTER; ");
          tailpos = 1; ok = emit_fn_body(&fb, &pre, funs[i].body); tailpos = 0; put(&fb, "; }\n");
          }
        } else { put(&fb, ") { LIN_ENTER; "); ok = emit_fn_body(&fb, &pre, funs[i].body); put(&fb, "; }\n"); }
      }
      Buf eb = nbuf(1024);                             /* the entry's call, as an expression of its parameters */
      emitting = -1; fscope++; ok = ok && emit_region(&eb, &pre, entry, 0, 4096);
      int data = uses_data;
      put(&b, "%s%s\n#include <pthread.h>\n", LIN_I64_SRC, LIN_F64_SRC);
      if (data && getenv("LIN_FN_POISON")) put(&b, "#define LIN_POISON 1\n");
      if (data && getenv("LIN_FN_STATS")) put(&b, "#define LIN_STATS 1\n");   /* (blocks built and freed, per size: is memory the live data?) */
      if (data) put(&b, "%s", DATA_RT); else put(&b, "#define LIN_ENTER\n#define LIN_LEAVE\n#define LIN_TASK_START(ss)\n#define LIN_JOINED 0\nint lin_fn_aborted;\n");
      size_t proto_at = b.len; int ngen = 0;          /* (the prototypes go here once every shape is known: see gen_data_fns) */
      { Buf db = nbuf(256);                            /* (written first: a drop function may call for another datatype's) */
      for (; data && ngen < ndrop; ngen++) gen_data_fns(&db, ngen);   /* (drop_fn may add datatypes while these are written; a unit without data has no allocator to free into) */
        put(&b, "%s", db.s); free(db.s); }
      put(&b, "%s", fb.s);
      if (ok && data) {                                /* data: on its own large stack, the tree recursions forked */
        Buf ebp = nbuf(1024);
        nsite = 0; emitting = 0; fscope++; pl_unit = 1;
        int pok = !nfv[0] && emit_region(&pb, &pre, funs[0].body, 1, 4096);   /* (the parallel copy is of f0's own parameters) */
        emitting = -1; fscope++; entry_np = nnum;
        pok = pok && emit_region(&ebp, &pre, entry, 1, 4096);
        pl_unit = 0;
        put(&b, "static int dmax; static pthread_attr_t attr;\nstatic int64_t fp("); plist(&b, 1);
        put(&b, "%sint d);\n%s", arity ? ", " : "", pre.s);
        if (pok) { put(&b, "static int64_t fp("); plist(&b, 1); put(&b, "%sint d) { if (d >= dmax) return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); return %s; }\n", pb.s); }
        else { put(&b, "static int64_t fp("); plist(&b, 1); put(&b, "%sint d) { (void)d; return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); }\n"); }
        put(&b, "static const int64_t *lin_args; static int64_t lin_res; static int lin_threads_;\n");
        /* a loop folding an associative operation over a range, its other parameters only READ: split among the
           threads, as for numbers -- what a step builds is its thread's own, what the loop shares nobody writes */
        /* (the entry may name what it computes first, and drop it after: `let m = (build ..) in (f0 .. m ..)`) */
        const Expr *ec = entry, *eaft = NULL; while (ec->op == E_LET) ec = ec->b;
        if (ec->op == E_AFTER) { eaft = ec; ec = ec->a; }
        Red red; int has_red = numeric && !nfv[0] && ec->op == E_CALL && ec->k == 0 && find_reduction(&red);
        Buf rq = nbuf(256), rd = nbuf(64);
        if (has_red) {
          emitting = 0; fscope++;
          has_red = red_defs(&b, &pre, &red, 1);
          emitting = -1; fscope++;
          for (const Expr *x = entry; has_red && x->op == E_LET; x = x->b) {
            int v = nvar++; put(&rq, "  int64_t v%d = ", v); has_red = emitx(&rq, &pre, x->a, 0, 4096); put(&rq, ";\n");
            x->bind->var = v; x->bind->vscope = fscope;
          }
          for (int i = 0; has_red && i < arity; i++) { put(&rq, "  int64_t q%d = ", i); has_red = emit_region(&rq, &pre, ec->args[i], 0, 4096); put(&rq, ";\n"); }
          for (const struct Drop *d = eaft ? eaft->drops : NULL; has_red && d; d = d->next) {
            if (d->fn <= -2) { has_red = 0; break; }
            put(&rd, "lin_drop%d(", d->fn); has_red = emitx(&rd, &pre, d->p, 0, 4096); put(&rd, "); ");
          }
          for (const Expr *x = entry; x->op == E_LET; x = x->b) x->bind->var = -1;
          if (has_red) DBG("parallel reduction over p%d (%s), accumulator p%d, in a data unit\n", red.iv, red.up ? "up" : "down", red.acc);
        }
        put(&b, "static void *lin_run(void *u) { (void)u; const int64_t *a = lin_args; LIN_TASK_START((size_t)1 << 30);\n");
        for (int i = 0; i < nnum; i++) put(&b, "  int64_t p%d = a[%d];\n", i, i);
        if (has_red) {
          put(&b, "  if (lin_threads_ > 1) {\n%s  {\n", rq.s);
          for (int i = 0; i < arity; i++) put(&b, "  int64_t p%d = q%d;\n", i, i);
          Buf rr = nbuf(128); put(&rr, "lin_res = acc; (void)LIN_JOINED; %sreturn 0;", rd.s);
          red_run(&b, &red, 1, "lin_threads_", rr.s); free(rr.s);
          put(&b, "  lin_res = f0("); plist(&b, 0); put(&b, "); %sreturn 0; } }\n", rd.s);
        }
        free(rq.s); free(rd.s);
        if (pok && nsite) {
          put(&b, "  if (lin_threads_ > 1) { int lg = 0; while ((1 << lg) < lin_threads_) lg++; dmax = lg + 2;\n");
          put(&b, "    pthread_attr_init(&attr); pthread_attr_setstacksize(&attr, (size_t)256 << 20); int d = -1; lin_res = %s; return 0; }\n", ebp.s);
        }
        put(&b, "  lin_res = %s; return 0; }\n", eb.s);
        free(ebp.s);
        put(&b, "int64_t lin_fn_entry(const int64_t *a, int threads) { lin_threads_ = threads; lin_args = a; lin_fn_aborted = 0;%s\n", data ? (rc_mt ? " lin_mt = threads > 1;" : " lin_mt = 0;") : "");
        put(&b, "  pthread_t t; pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);\n");
        /* a structure result stays in the arena until the driver has built it into the net (lin_fn_release) */
        put(&b, "  if (pthread_create(&t, &at, lin_run, 0)) { LIN_NO_THREAD; } else pthread_join(t, 0);%s return lin_res; }\n",
            numeric ? " lin_free_all();" : "");
        put(&b, "void lin_fn_release(void) { lin_free_all(); }\n");
        {                                              /* the shapes the parallel code and the entry met, then every prototype */
          Buf db = nbuf(256);
          for (; ngen < ndrop; ngen++) gen_data_fns(&db, ngen);
          put(&b, "%s", db.s); free(db.s);
          Buf pr = nbuf(256);
          for (int d = 0; d < ndrop; d++)   /* (an immediate is no block: tested where it is dropped, not in a call) */
            put(&pr, "static void lin_drop%d_(int64_t v);\nstatic inline void lin_drop%d(int64_t v) { if (!(v & 1)) lin_drop%d_(v); }\nstatic int64_t lin_copy%d(int64_t v);\n", d, d, d, d);
          for (int d = 0; d < ndrop; d++) put(&pr, "static void lin_share%d(int64_t v);\nstatic void lin_freeze%d(int64_t v);\n", d, d);
          Buf nb = nbuf(b.len + pr.len + 1);
          put(&nb, "%.*s%s%s", (int)proto_at, b.s, pr.s, b.s + proto_at);
          free(b.s); free(pr.s); b = nb;
        }
        DBG("compiling a data unit (%d function%s, %d numeric argument%s, %d parallel site%s%s):\n%s\n", nfun, nfun == 1 ? "" : "s", nnum, nnum == 1 ? "" : "s", nsite, nsite == 1 ? "" : "s", numeric ? "" : ", a structure result", b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, nnum, numeric ? (rbool ? 3 : 1) : 5, rshape);
        if (r) r->strict = funs[0].strict;
      } else if (ok && aports) {                       /* numbers only, with expression arguments: the plain entry */
        put(&b, "%slong lin_fn_entry(const int64_t *a, int threads) { (void)threads;\n", pre.s);
        for (int i = 0; i < nnum; i++) put(&b, "  int64_t p%d = a[%d];\n", i, i);
        put(&b, "  return %s; }\n", eb.s);
        DBG("compiling (%d functions, entry with expression arguments):\n%s\n", nfun, b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, nnum, rbool ? 3 : 1, (Shape){ 1, NULL });
        if (r) r->strict = funs[0].strict;
      }
      nsite = 0; emitting = 0; fscope++;
      if (!ok || data || aports || nfv[0]) goto done;
      ok = emit_region(&pb, &pre, funs[0].body, 1, 4096);
      if (ok) {
        put(&b, "static int dmax; static pthread_attr_t attr;\nstatic int64_t fp("); plist(&b, 1);
        put(&b, "%sint d);\n%sstatic int64_t fp(", arity ? ", " : "", pre.s); plist(&b, 1);
        put(&b, "%sint d) { if (d >= dmax) return f0(", arity ? ", " : ""); plist(&b, 0); put(&b, "); return %s; }\n", pb.s);
        Red red; int has_red = find_reduction(&red);
        if (has_red) {
          ok = red_defs(&b, &pre, &red, 0);
          DBG("parallel reduction over p%d (%s), accumulator p%d\n", red.iv, red.up ? "up" : "down", red.acc);
        }
        put(&b, "int64_t lin_fn_entry(const int64_t *a, int threads) {\n");
        for (int i = 0; i < arity; i++) put(&b, "  int64_t p%d = a[%d];\n", i, i);
        if (has_red) red_run(&b, &red, 0, "threads", "return acc;");
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
/* THE PROGRAM CACHE (src/lin.h): which unit, on which constants, answered an expression -- so the next run of an
   unchanged program runs the units and nothing else.  A record is one line per expression; a file of them is
   committed only when every expression of the program has one. */
static FILE *fr_f; static uint64_t fr_key; static int fr_n;
static void form_path(char *out, size_t sz, uint64_t key, const char *ext) { char dir[4096]; cache_dir(dir, sizeof dir); snprintf(out, sz, "%s/form-%016llx.%s", dir, (unsigned long long)key, ext); }
static void form_note(const Net *n, const Compiled *c, const int64_t *a, int na) {
  if (!lin_form_key || lin_form_idx < 0 || (const void *)n != lin_form_net || c->kind == 5 || c->npsh) return;
  if (fr_key != lin_form_key) {
    if (fr_f) fclose(fr_f);
    char path[4300]; form_path(path, sizeof path, lin_form_key, "tmp"); mkdir_p(path); rmdir(path);
    fr_f = fopen(path, "w"); fr_key = lin_form_key; fr_n = 0;
  }
  if (!fr_f || lin_form_idx != fr_n) return;        /* (one record per expression, in order: anything else never commits) */
  fprintf(fr_f, "%016" PRIx64 " %d %d %d", c->h, c->kind, lin_form_domain, na);
  for (int i = 0; i < na; i++) fprintf(fr_f, " %" PRId64 "", a[i]);
  fputc('\n', fr_f); fr_n++;
  lin_form_idx = -1;
}
static void form_commit(uint64_t key, int count) {
  if (!fr_f || fr_key != key) return;
  fclose(fr_f); fr_f = NULL; fr_key = 0;
  char tmp[4300], full[4300]; form_path(tmp, sizeof tmp, key, "tmp"); form_path(full, sizeof full, key, "txt");
  if (fr_n == count) rename(tmp, full); else unlink(tmp);
}
static char *fc_text; static uint64_t fc_key; static char *fc_pos;
static int form_recall(uint64_t key, int idx, int threads, int64_t *word, int *kind, int *domain) {
  if (getenv("LIN_FN_OFF")) return -1;
  if (idx == 0 || fc_key != key) {
    free(fc_text); fc_text = NULL; fc_key = key;
    char path[4300]; form_path(path, sizeof path, key, "txt");
    FILE *fp = fopen(path, "r"); if (!fp) return -1;
    fseek(fp, 0, SEEK_END); int64_t sz = ftell(fp); fseek(fp, 0, SEEK_SET);
    fc_text = malloc((size_t)sz + 1); if (fread(fc_text, 1, (size_t)sz, fp) != (size_t)sz) sz = 0; fc_text[sz] = 0; fclose(fp);
    fc_pos = fc_text;
  }
  if (!fc_text) return -1;
  if (!*fc_pos) return 0;
  char *e; uint64_t h = strtoull(fc_pos, &e, 16); int k = (int)strtoll(e, &e, 10), d = (int)strtoll(e, &e, 10), na = (int)strtoll(e, &e, 10);
  if (na < 0) return -1;
  int64_t *a = malloc(sizeof *a * (size_t)(na + 1));
  for (int i = 0; i < na; i++) a[i] = strtoll(e, &e, 10);
  if (*e != '\n') { free(a); return -1; }
  fc_pos = e + 1;
  char dir[4096], so[4300]; cache_dir(dir, sizeof dir); snprintf(so, sizeof so, "%s/fn-%016" PRIx64 ".so", dir, h);
  void *hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
  Entry en = hnd ? (Entry)(intptr_t)dlsym(hnd, "lin_fn_entry") : NULL;
  int *ab = hnd ? (int *)dlsym(hnd, "lin_fn_aborted") : NULL;
  if (!en) { free(a); return -1; }
  int64_t r = en(a, threads > 0 ? threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
  free(a);
  if (ab && *ab) return -1;                          /* (its guard fired: the net computes the program) */
  *word = r; *kind = k; *domain = d;
  return 1;
}
static int fn_off = -1;   /* LIN_FN_OFF: refuse every call (the differential's control run) */
static int fn_claim(const Net *n, Port p1, Port p2) {
  if (fn_off < 0) fn_off = getenv("LIN_FN_OFF") != NULL;
  int h, a, F; return y_call(n, p1, p2, &h, &a, &F) || y_fix(n, p1, p2, &h, &a);   /* (LIN_FN_OFF: claimed, and declined -- the cheap rewrite or the beta) */
}

/* A STRUCTURE RESULT, BUILT INTO THE NET.  The unit's answer is a word: a number, a boolean, or a datatype's value
   in its arena -- an immediate for a constructor with no fields, else a block (the layout the unit's own matches
   read).  The shapes the compiler proved say which, field by field, so the value is rebuilt as the constructors
   the source would have built -- each `\d0..\d(m-1). ((\_c (d_i f1..fk)) ID)`, marker and all, so everything that
   reads a constructor reads these -- and a block the result reaches more than once is built ONCE and shared by a
   fan with a label of its own, as the program's own sharing would be: the net gets the DAG, not a tree. */
typedef struct { int64_t ptr; int refs; int used; Port *outs; } RBlk;
typedef struct { Net *n; const Compiled *c; RBlk *tab; int64_t cap, cnt; int64_t budget; int bad; uint64_t lbl; } Reif;
static RBlk *rb_get(Reif *R, int64_t ptr, int make) {
  if (make && (R->cnt + 1) * 2 > R->cap) {
    RBlk *o = R->tab; int64_t oc = R->cap; R->cap = R->cap ? R->cap * 2 : 1024; R->tab = calloc((size_t)R->cap, sizeof *R->tab); R->cnt = 0;
    for (int64_t i = 0; i < oc; i++) if (o[i].ptr) { RBlk *b = rb_get(R, o[i].ptr, 1); *b = o[i]; }
    free(o);
  }
  if (!R->cap) return NULL;
  for (uint64_t h = ((uint64_t)ptr * 0x9E3779B97F4A7C15UL >> 7) & (uint64_t)(R->cap - 1);; h = (h + 1) & (uint64_t)(R->cap - 1)) {
    if (R->tab[h].ptr == ptr) return &R->tab[h];
    if (!R->tab[h].ptr) { if (!make) return NULL; R->tab[h].ptr = ptr; R->cnt++; return &R->tab[h]; }
  }
}
/* A VECTOR AT THE EDGE.  On the net a vector is its meaning, std/array.lin's `(arr len depth root)` over a 32-way
   trie whose bottom nodes hold 32 elements; compiled it is one block {length, capacity, elements}.  A vector a unit
   is given is read in by walking the trie into the block, and one it returns is built back as the trie: the
   operations need not fall back to their meaning for the whole unit because a vector crosses. */
static const LinCtor *vt_arr, *vt_empty, *vt_vals, *vt_node;
static int vt_find(void) {                          /* the trie's constructors, by their shape (one each) */
  if (vt_arr && vt_vals) return 1;
  const LinCtor *c;
  for (int64_t k = 1; (c = lin_ctor_info(k)); k++) {
    const char *nm = c->name, *dot = nm ? strrchr(nm, '.') : NULL; if (dot) nm = dot + 1;
    if (!nm) continue;
    if (!strcmp(nm, "arr") && c->k == 3 && c->m == 1) vt_arr = c;
    else if (!strcmp(nm, "tempty") && c->k == 0) vt_empty = c;
    else if (!strcmp(nm, "tvals")) vt_vals = c;
    else if (!strcmp(nm, "tnode")) vt_node = c;
  }
  return vt_arr && vt_empty && vt_vals && vt_node && vt_vals->k == vt_node->k && vt_vals->dt == vt_node->dt;
}
static const LinCtor *dt_ctor(const char *dt, int i) {
  const LinCtor *c; for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->i == i) return c; return NULL;
}
/* the constructor of a word of datatype dt, and its fields' words */
static const LinCtor *rd_word(const char *dt, int64_t w, const int64_t **fields) {
  int box = 0, untag = dt_boxed(dt, &box) == 1;
  if (w & 1) { *fields = NULL; return dt_ctor(dt, (int)(w >> 1)); }
  const int64_t *blk = (const int64_t *)w;
  if (!blk) return NULL;
  if (untag) { *fields = blk; return dt_ctor(dt, box); }
  *fields = blk + 1; return dt_ctor(dt, (int)blk[0]);
}
static int64_t cid_of(const LinCtor *ci) { return ctor_id(ci); }
/* pass 1: how often each block is reached (a block's fields are walked once) -- iteratively: results are deep */
typedef struct { int64_t w; Shape s; } RTodo;
static void rf_count(Reif *R, int64_t w0, Shape s0) {
  RTodo *st = malloc(sizeof *st * 64); int64_t sp = 0, sc = 64;
  st[sp++] = (RTodo){ w0, s0 };
  while (sp && !R->bad) {
    RTodo t = st[--sp];
    if (t.s.dt == VEC_DT) {                          /* (a vector: its block once, then its data elements) */
      if (t.w & 1) { R->bad = 1; break; }
      RBlk *b = rb_get(R, t.w, 1); if (b->refs++) continue;
      Shape es = t.s.a && t.s.a->n ? t.s.a->s[0] : (Shape){ 0, NULL, NULL };
      if (!vt_find() || es.k == 0) { R->bad = 1; break; }
      const int64_t *v = (const int64_t *)t.w;
      if (es.k == 5) for (int64_t i = 0; i < v[0]; i++) {
        if (sp >= sc) st = realloc(st, sizeof *st * (size_t)(sc *= 2));
        st[sp++] = (RTodo){ v[i + 2], es };
      }
      continue;
    }
    const int64_t *f; const LinCtor *ci = rd_word(t.s.dt, t.w, &f);
    if (!ci) { R->bad = 1; break; }
    if (!(t.w & 1)) { RBlk *b = rb_get(R, t.w, 1); if (b->refs++) continue; }
    int64_t id = cid_of(ci);
    for (int j = 0; j < ci->k; j++) {
      Shape fs = field_shape(R->c->fld, R->c->nctor, ci, id, j, t.s);
      if (fs.k != 5) continue;
      if (sp >= sc) st = realloc(st, sizeof *st * (size_t)(sc *= 2));
      st[sp++] = (RTodo){ f[j], fs };
    }
  }
  free(st);
}
static Scope fresh_label(Reif *R) {                   /* a sharing point no other fan in the net has */
  Scope s = scope_nil();
  uint64_t v = 0x5Au << 24 | (R->lbl++ & 0xFFFFFFu);
  for (int b = 31; b >= 0; b--) s = scope_app(R->n, s, (int)((v >> b) & 1));
  return s;
}
static Port rf_ctor(Reif *R, const LinCtor *ci, const Port *fields) {
  Net *n = R->n; Scope sc = scope_nil();
  if (cells_dt && ci->dt == cells_dt && ci->k == 2) {   /* a cell `\c.\n.((c h) t)`: its marker reduced (a list end keeps
                                                     its marker below: `\c.\n.n` alone would read as the boolean false) */
    Port c = net_alloc(n, LAM, sc), nn = net_alloc(n, LAM, sc);
    net_link(n, (Port){c.node, 2}, (Port){nn.node, 0}, 1);
    net_link(n, (Port){nn.node, 1}, net_alloc(n, ERA, sc), 1);
    Port a1 = net_alloc(n, APP, sc), a2 = net_alloc(n, APP, sc);
    net_link(n, (Port){a1.node, 0}, (Port){c.node, 1}, 1); net_link(n, (Port){a1.node, 2}, fields[0], 1);
    net_link(n, (Port){a2.node, 0}, (Port){a1.node, 1}, 1); net_link(n, (Port){a2.node, 2}, fields[1], 1);
    net_link(n, (Port){nn.node, 2}, (Port){a2.node, 1}, 1);
    return (Port){c.node, 0};
  }
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
static Port rf_build(Reif *R, int64_t w, Shape s);
static Port rf_share(Reif *R, RBlk *b, Port v);
/* a vector's elements lo.. as a trie node of depth d (std/array.lin's _tfill: past the length, nothing) */
static Port rf_trie(Reif *R, const int64_t *v, Shape es, int64_t lo, int64_t d) {
  int k = vt_vals->k; int64_t len = v[0];
  Port *fp = malloc(sizeof *fp * (size_t)k);
  const LinCtor *ci;
  if (lo >= len) ci = vt_empty;
  else if (d == 0) {
    ci = vt_vals;
    for (int j = 0; j < k && !R->bad; j++) fp[j] = lo + j < len ? rf_build(R, v[lo + j + 2], es) : net_alloc_scott(R->n, 0);   /* (a slot past the length is never read) */
  } else {
    ci = vt_node; int64_t w = 1; for (int64_t q = 0; q < d; q++) w *= k;
    for (int j = 0; j < k && !R->bad; j++) fp[j] = rf_trie(R, v, es, lo + j * w, d - 1);
  }
  Port r = R->bad ? NONE : rf_ctor(R, ci, fp);
  free(fp); return r;
}
static Port rf_vec(Reif *R, int64_t w, Shape s) {
  const int64_t *v = (const int64_t *)w; Shape es = s.a->s[0];
  int64_t d = 0, span = vt_vals->k; while (v[0] > span) { span *= vt_vals->k; d++; }   /* (_depth_for) */
  Port t = rf_trie(R, v, es, 0, d);
  if (R->bad) return NONE;
  Port fp[3] = { net_alloc_scott(R->n, v[0]), net_alloc_scott(R->n, d), t };
  return rf_ctor(R, vt_arr, fp);
}
/* pass 2: build (recursively, on the large stack rf_thread gives it) */
static Port rf_build(Reif *R, int64_t w, Shape s) {
  if (R->bad) return NONE;
  if (s.k == 1) return net_alloc_scott(R->n, w);
  if (s.k == 3) return net_alloc_bool(R->n, w != 0);
  RBlk *b = (w & 1) ? NULL : rb_get(R, w, 0);
  if (b && b->outs) return b->outs[b->used++];
  if (s.dt == VEC_DT) { Port v = rf_vec(R, w, s); return R->bad ? NONE : rf_share(R, b, v); }
  const int64_t *f; const LinCtor *ci = rd_word(s.dt, w, &f);
  if (!ci) { R->bad = 1; return NONE; }
  int64_t id = cid_of(ci);
  Port *fp = malloc(sizeof *fp * (size_t)(ci->k + 1));
  for (int j = 0; j < ci->k && !R->bad; j++) fp[j] = rf_build(R, f[j], field_shape(R->c->fld, R->c->nctor, ci, id, j, s));
  Port v = R->bad ? NONE : rf_ctor(R, ci, fp);
  free(fp);
  return R->bad ? NONE : rf_share(R, b, v);
}
static Port rf_share(Reif *R, RBlk *b, Port v) {     /* a block reached more than once: one value, fanned out */
  if (!b || b->refs < 2) return v;
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
typedef struct { Reif *R; int64_t w; Port out; } RfArg;
static void *rf_thread(void *u) { RfArg *a = u; a->out = rf_build(a->R, a->w, a->R->c->res); return NULL; }
/* The value of a compiled call's result word, as net structure; NONE if it cannot be read back. */
static Port result_port(Net *n, const Compiled *c, int64_t r) {
  if (c->kind == 3) return net_alloc_bool(n, r != 0);
  if (c->kind != 5) return net_alloc_scott(n, r);   /* (a float is the numeral of its bits) */
  static uint64_t lbl;
  Reif R = { n, c, NULL, 0, 0, 0, 0, lbl };   /* (each block is walked once: the arena bounds the walk) */
  rf_count(&R, r, c->res);
  Port v = NONE;
  if (!R.bad) {
    RfArg a = { &R, r, NONE };
    pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);
    pthread_t t;
    if (!pthread_create(&t, &at, rf_thread, &a)) { pthread_join(t, NULL); v = a.out; }
    pthread_attr_destroy(&at);
  }
  lbl = R.lbl;
  for (int64_t i = 0; i < R.cap; i++) free(R.tab[i].outs);
  free(R.tab);
  if (c->release) c->release();
  if (R.bad) DBG("the structure result could not be read back: the net computes it\n");
  return R.bad ? NONE : v;
}

static int numeral_shape(const Net *n, Port p);
/* DATA PASSED IN.  An argument that is already a value in the net -- a string the program read, a structure an
   earlier call built -- is not compiled as a constant (a megabyte of input is not a C literal): the driver reads it
   at call time into blocks of the layout the unit uses, by the shape the compiler inferred from how the unit uses
   it.  The blocks live in a driver arena freed after the call (and after the result is read back, which may hold
   them: a block the unit owned may have been rebuilt in place). */
typedef struct { Net *n; const Compiled *c; void **ch; int nch, cch; int64_t *hp, *he; int64_t *mk; Port *mp; int64_t mcap, mcnt; int bad; int64_t steps0; } Marsh;
static int64_t *ms_alloc(Marsh *M, int64_t words) {
  if (M->hp + words + 1 > M->he) {
    int64_t sz = words + 1 > 65536 ? words + 1 : 65536; int64_t *c = malloc((size_t)sz * sizeof *c);
    if (!c) { M->bad = 1; return NULL; }
    if (M->nch >= M->cch) M->ch = realloc(M->ch, sizeof *M->ch * (size_t)(M->cch = M->cch ? M->cch * 2 : 16));
    M->ch[M->nch++] = c; M->hp = c; M->he = c + sz;
  }
  int64_t *r = M->hp + 1; r[-1] = 1; M->hp += words + 1; return r;   /* (a count word before each block: see lin_alloc) */
}
static void ms_free(Marsh *M) { for (int i = 0; i < M->nch; i++) free(M->ch[i]); free(M->ch); free(M->mk); free(M->mp); }
static int64_t ms_value(Marsh *M, Port p, Shape s, int depth);
/* THE VALUE'S DECLARED TYPE, carried down while reading it in: a field whose type is the datatype's parameter
   (a Seq's element) is told what it is by the type it was declared at -- `(alts Seq (Seq Piece))` says the
   elements of the inner Seqs are Pieces, which no shape of `scons` can say for every use of it.
   Descriptors are src/type.c's: N B F ?, L<elem>, P<i>;, D<name>(<args>). */
static const char *td_dt(const char *d) {            /* the datatype a D-descriptor names (the registry's own string) */
  if (!d || *d != 'D') return NULL;
  const char *e = strchr(d, '('); if (!e) return NULL;
  size_t nl = (size_t)(e - d - 1); const LinCtor *c;
  for (int64_t k = 1; (c = lin_ctor_info(k)); k++) if (c->dt && strlen(c->dt) == nl && !strncmp(c->dt, d + 1, nl)) return c->dt;
  return NULL;
}
static int td_args(const char *d, const char **out, int max) {   /* a D-descriptor's type arguments, each a pointer into it */
  const char *p = d ? strchr(d, '(') : NULL; int n = 0;
  if (!p) return 0;
  for (p++; *p && *p != ')'; p = fd_skip(p)) { if (out && n < max) out[n] = p; n++; }   /* (out NULL: just count them) */
  return n;
}
static char *td_subst(const char *f, const char **args, int na) {   /* a field's descriptor, the parent's arguments put in */
  size_t cap = 64, len = 0; char *o = malloc(cap);
  for (const char *p = f; p && *p; ) {
    const char *piece = p, *end; char tmp[2] = { 0, 0 };
    if (*p == 'P') { int i = atoi(p + 1); const char *q = strchr(p, ';'); end = q ? q + 1 : p + strlen(p);
      if (i < na && args[i]) { piece = args[i]; size_t l = (size_t)(fd_skip(args[i]) - args[i]);
        while (len + l + 1 > cap) o = realloc(o, cap *= 2); memcpy(o + len, piece, l); len += l; p = end; continue; } }
    else end = p + 1;
    (void)tmp; size_t l = (size_t)(end - p);
    while (len + l + 1 > cap) o = realloc(o, cap *= 2); memcpy(o + len, p, l); len += l; p = end;
  }
  o[len] = 0; return o;
}
static Shape td_shape(const char *d, Shape dflt) {   /* what a descriptor says the value is, or the analysis's shape */
  if (!d || !*d) return dflt;
  if (*d == 'N' || *d == 'F') return (Shape){ 1, NULL };
  if (*d == 'B') return (Shape){ 3, NULL };
  if (*d == 'D' && !strncmp(d + 1, VEC_DT, strlen(VEC_DT)) && d[1 + strlen(VEC_DT)] == '(') {   /* (a vector: of what its argument says) */
    const char *ta[1]; Shape es = { 0, NULL, NULL };
    if (td_args(d, ta, 1) == 1) { Shape ed = (dflt.k == 5 && dflt.dt == VEC_DT && dflt.a && dflt.a->n) ? dflt.a->s[0] : es; es = td_shape(ta[0], ed); }
    return es.k ? sh_mk(VEC_DT, 1, &es) : dflt;
  }
  if (*d == 'D') { const char *dt = td_dt(d); if (dt) return (Shape){ 5, dt }; }
  return dflt;
}
static const char *ms_desc;                          /* the declared type of the value ms_value is about to read */
static int64_t *ms_seen(Marsh *M, int node, int make) {   /* a value reached twice is one block (the net's sharing kept) */
  if (make && (M->mcnt + 1) * 2 > M->mcap) {
    int64_t *ok = M->mk; Port *op = M->mp; int64_t oc = M->mcap; M->mcap = M->mcap ? M->mcap * 2 : 1024;
    M->mk = calloc((size_t)M->mcap, sizeof *M->mk); M->mp = calloc((size_t)M->mcap, sizeof *M->mp); M->mcnt = 0;
    for (int64_t i = 0; i < oc; i++) if (op[i].node > 0) { int64_t *w = ms_seen(M, op[i].node, 1); *w = ok[i]; }
    free(ok); free(op);
  }
  if (!M->mcap) return NULL;
  for (uint64_t h = ((uint64_t)node * 0x9E3779B97F4A7C15UL >> 7) & (uint64_t)(M->mcap - 1);; h = (h + 1) & (uint64_t)(M->mcap - 1)) {
    if (M->mp[h].node == node) return &M->mk[h];
    if (M->mp[h].node <= 0) { if (!make) return NULL; M->mp[h].node = node; M->mk[h] = 0; M->mcnt++; return &M->mk[h]; }
  }
}
/* a trie node of depth d covering elements lo.. read into the vector's block (see A VECTOR AT THE EDGE) */
static void ms_trie(Marsh *M, Port p, int64_t *v, Shape es, int64_t lo, int64_t d, int depth) {
  int k = vt_vals->k, i = -1; int64_t len = v[0];
  if (M->bad || lo >= len) return;
  Port *fp = malloc(sizeof *fp * (size_t)k);
  int got = net_read_scott(M->n, p, vt_vals->m, &i, fp, k);
  if (got == 0 && i == vt_empty->i) {}                /* (nothing stored there) */
  else if (got == k && i == vt_vals->i && d == 0) { for (int j = 0; j < k && lo + j < len && !M->bad; j++) v[lo + j + 2] = ms_value(M, fp[j], es, depth + 1); }
  else if (got == k && i == vt_node->i && d > 0) {
    int64_t w = 1; for (int64_t q = 0; q < d; q++) w *= k;
    for (int j = 0; j < k && !M->bad; j++) ms_trie(M, fp[j], v, es, lo + j * w, d - 1, depth + 1);
  } else { if (dbg > 1) DBG("[a vector's trie not read in: %d fields, constructor %d, depth %" PRId64 "]\n", got, i, d); M->bad = 1; }
  free(fp);
}
static int64_t ms_vec(Marsh *M, Port p, Shape s, int depth) {
  if (!vt_find() || !s.a || s.a->n != 1) { if (dbg > 1) DBG("[a vector not read in: its element's shape is not known]\n"); M->bad = 1; return 0; }
  Port v0 = net_dhop(M->n, net_force_val(M->n, p));
  int64_t *seen = v0.node > 0 ? ms_seen(M, v0.node, 0) : NULL;
  if (seen && *seen) return *seen;
  Port fp[3]; int i = -1; int64_t len = 0, d = 0;
  int got = net_read_scott(M->n, p, vt_arr->m, &i, fp, 3);
  if (got != 3 || i != vt_arr->i || !net_read_i64(M->n, fp[0], &len) || !net_read_i64(M->n, fp[1], &d) || len < 0 || d < 0) { if (dbg > 1) DBG("[a vector not read in: %d fields, constructor %d]\n", got, i); M->bad = 1; return 0; }
  int64_t cap = len < 4 ? 4 : len;
  int64_t *v = ms_alloc(M, cap + 2); if (!v) return 0;
  v[0] = len; v[1] = cap; for (int64_t j = 0; j < cap; j++) v[j + 2] = 1;   /* (an immediate until read: a drop of it is nothing) */
  ms_trie(M, fp[2], v, s.a->s[0], 0, d, depth + 1);
  if (!M->bad && v0.node > 0) { int64_t *slot = ms_seen(M, v0.node, 1); if (slot) *slot = (int64_t)v; }
  return (int64_t)v;
}
static int64_t ms_value(Marsh *M, Port p, Shape s, int depth) {
  Net *n = M->n;
  const char *desc = ms_desc; ms_desc = NULL;
  s = td_shape(desc, s);
  if (M->bad || depth > n->nn) { M->bad = 1; return 0; }
  if (n->steps - M->steps0 > (int64_t)n->nn) { M->bad = 1; return 0; }   /* (a value in hand needs no reduction to read) */
  if (s.k == 0) {                                    /* a field the analysis saw no use of: what the value IS decides */
    int64_t x; if (net_read_i64(n, p, &x)) return x;
    int64_t b = net_read_int(n, p, LIN_ENC_BOOL); if (b >= 0) return b;
    if (dbg > 1) DBG("[not read in: a value of no known shape that is not a number (declared %s)]\n", desc ? desc : "-");
    M->bad = 1; return 0;
  }
  if (s.k == 1) { int64_t x; if (!net_read_i64(n, p, &x)) M->bad = 1; return x; }
  if (s.k == 3) { int64_t b = net_read_int(n, p, LIN_ENC_BOOL); if (b < 0) M->bad = 1; return b; }
  if (s.k != 5 || !s.dt) { if (dbg > 1) DBG("[not read in: a block of a datatype not known (shape %d, declared %s)]\n", s.k, desc ? desc : "-"); M->bad = 1; return 0; }   /* (a block of some datatype, not known which: not read in) */
  if (s.dt == VEC_DT) return ms_vec(M, p, s, depth);
  int box = 0, untag = dt_boxed(s.dt, &box) == 1;
  if (cells_dt && s.dt == cells_dt) {               /* a list: its spine read in a loop */
    int64_t first = 0, *link = &first;
    Shape hs = field_shape(M->c->fld, M->c->nctor, cell_cons, ctor_id(cell_cons), 0, s);
    for (int64_t k = 0; !M->bad; k++) {
      Port h, t;
      if (k > n->nn) { M->bad = 1; break; }
      if (!net_read_cell(n, p, &h, &t)) {
        if (net_read_int(n, p, LIN_ENC_STR) != 0) { M->bad = 1; break; }
        *link = ((int64_t)cell_nil->i << 1) | 1; break;
      }
      int64_t *blk = ms_alloc(M, 2); if (!blk) break;
      ms_desc = desc && *desc == 'L' ? desc + 1 : NULL;
      blk[0] = ms_value(M, h, hs, depth + 1); *link = (int64_t)blk; link = &blk[1]; p = t;
    }
    return first;
  }
  int m = 0, kmax = 0; const LinCtor *c;
  for (int64_t id = 1; (c = lin_ctor_info(id)); id++) if (c->dt == s.dt) { m = c->m; if (c->k > kmax) kmax = c->k; }
  Port v = net_dhop(n, net_force_val(n, p));
  int64_t *seen = v.node > 0 ? ms_seen(M, v.node, 0) : NULL;
  if (seen && *seen) return *seen;
  Port *fp = malloc(sizeof *fp * (size_t)(kmax + 1)); int i = -1;
  int k = m ? net_read_scott(n, p, m, &i, fp, kmax) : -1;
  const LinCtor *ci = k >= 0 ? dt_ctor(s.dt, i) : NULL;
  int64_t w = 0;
  if (!ci || ci->k != k) M->bad = 1;
  else if (!k) w = ((int64_t)ci->i << 1) | 1;
  else {
    int64_t *blk = ms_alloc(M, k + !untag);
    if (blk) {
      if (!untag) blk[0] = ci->i;
      int64_t id = ctor_id(ci);
      int na = desc ? td_args(desc, NULL, 0) : 0; const char **ta = malloc(sizeof *ta * (size_t)(na + 1)); if (desc) td_args(desc, ta, na); const char *fd = ci->fdesc;
      for (int j = 0; j < k && !M->bad; j++, fd = fd_skip(fd)) {
        char *f = desc && fd && *fd ? td_subst(fd, ta, na) : NULL;
        ms_desc = f;
        blk[j + !untag] = ms_value(M, fp[j], field_shape(M->c->fld, M->c->nctor, ci, id, j, s), depth + 1);
        ms_desc = NULL; free(f);
      }
      free(ta);
      w = (int64_t)blk;
    }
  }
  free(fp);
  if (!M->bad && v.node > 0 && !(w & 1)) { int64_t *slot = ms_seen(M, v.node, 1); if (slot) *slot = w; }
  return w;
}
typedef struct { Marsh *M; Port p; Shape s; int64_t w; } MsArg;
static void *ms_thread(void *u) {
  MsArg *a = u;
  /* (a datatype with no parameters is its own declared type: its fields' descriptors say the rest) */
  char *top = a->s.k == 5 && a->s.dt ? malloc(strlen(a->s.dt) + 4) : NULL; if (top) { sprintf(top, "D%s()", a->s.dt); ms_desc = top; }
  a->w = ms_value(a->M, a->p, a->s, 0); ms_desc = NULL; free(top); return NULL;
}
static int64_t marshal(Marsh *M, Port p, Shape s) {   /* (on a large stack: data is deep) */
  MsArg a = { M, p, s, 0 };
  pthread_attr_t at; pthread_attr_init(&at); pthread_attr_setstacksize(&at, (size_t)1 << 30);
  pthread_t t;
  if (pthread_create(&t, &at, ms_thread, &a)) M->bad = 1; else pthread_join(t, NULL);
  pthread_attr_destroy(&at);
  return a.w;
}
/* Is this argument a DATA value already -- a list or a constructor -- rather than a number or a function? */
static int data_value(const Net *n, Port p) {
  Port q = dhop(n, p);
  if (!is(n, q, LAM, 0)) return 0;
  if (numeral_shape(n, q)) return 1;                 /* (a cell or an end: a list, a string) */
  int nl = 0;
  for (int i = 0; i < n->nn && is(n, q, LAM, 0); i++) { nl++; q = dhop(n, W(n, (Port){q.node, 2})); }
  Port mb, mid; int ml; Net *sn = N; N = (Net *)n;
  int r = nl > 0 && marker_app(q, &mb, &ml, &mid);
  N = sn; return r;
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
  if (is(n, b, LAM, 0)) {                            /* a terminal: \c.\n.<sign>, the sign a boolean \t.\f.t or \t.\f.f */
    /* (exactly that: `\i.7` -- a function whose body is a literal -- is three lambdas deep too, and read as data
       it was passed in as a list and then applied) */
    Port f = dhop(n, W(n, (Port){b.node, 2}));
    if (!is(n, f, LAM, 0)) return 0;
    Port v = dhop(n, W(n, (Port){f.node, 2}));
    return v.port == 1 && (v.node == b.node || v.node == f.node);
  }
  if (!is(n, b, APP, 1)) return 0;
  Port ia = dhop(n, W(n, (Port){b.node, 0}));
  if (!is(n, ia, APP, 1)) return 0;
  Port hd = dhop(n, W(n, (Port){ia.node, 0}));
  return hd.node == c.node && hd.port == 1;          /* a cell applies its own first binder */
}
/* A SMALL CONSTANT already in the net -- n-body's five bodies, fasta's alphabets -- is compiled into the unit
   rather than read in at call time: the unit then has no inputs, and the program cache can answer for the
   whole program on the next run (a unit that reads data in is computed afresh every time).  How small: the
   value's own structure (below its root, through sharing) within a bound, so a long list built at run time is
   still read in. */
/* (`seen` is a stamp per node, kept between calls: the walk visits at most `limit` nodes, and clearing a table the
   net's size for each one made the call cost the whole net -- measured, a game whose net had grown to a million
   slots spent a tenth of every frame in memset here.) */
static unsigned *sd_seen; static size_t sd_cap; static unsigned sd_gen;
static int small_data(const Net *n, Port p, int limit) {
  int *stk = malloc(sizeof *stk * (size_t)(limit + 8)), sp = 0, cnt = 0;
  if (sd_cap < (size_t)n->nn || ++sd_gen == 0) {
    size_t c = (size_t)n->nn * 2 + 64; free(sd_seen); sd_seen = calloc(c, sizeof *sd_seen); sd_cap = c; sd_gen = 1;
  }
  unsigned *seen = sd_seen; const unsigned g = sd_gen;
  Port q = dhop(n, p); stk[sp++] = q.node; seen[q.node] = g;
  while (sp > 0 && cnt <= limit) {
    int a = stk[--sp]; cnt++;
    int t = n->tag[a], ks[2], nk = 0;
    if (t == LAM) ks[nk++] = 2;
    else if (t == APP) { ks[nk++] = 0; ks[nk++] = 2; }
    else if (t == DUP) ks[nk++] = 0;
    for (int i = 0; i < nk; i++) {
      Port w = W(n, (Port){a, ks[i]});
      if (!live(n, w) || seen[w.node] == g) continue;
      int tw = n->tag[w.node];
      if (tw == ROOT) { cnt = limit + 1; break; }
      seen[w.node] = g; if (sp < limit + 4) stk[sp++] = w.node;
    }
  }
  free(stk);
  return cnt <= limit;
}
static Compiled *compile_fn_ex(Net *n, int F, const Port *aports, const int *anum);
/* (A list cell whose head is a non-empty list is also the SHAPE of a foreign call -- `\_ffi.\_ret.((_ffi name)
   args)`, its head the symbol's name -- and a call is no constant: such a value is never taken for one.) */
static int const_tree(const Expr *e, int depth) {   /* constructors and numbers only: data, not a computation */
  if (!e) return 0;
  if (e->op == E_CONST) return 1;
  if (e->op != E_CTOR) return 0;
  if (cell_cons && e->ci == cell_cons && e->nargs > 0 && e->args[0]->op == E_CTOR && e->args[0]->ci == cell_cons) return 0;
  for (int i = 0; i < e->nargs; i++) if (!const_tree(e->args[i], depth + 1)) return 0;
  return 1;
}
static int const_data(Net *n, Port p) {             /* does this value read as pure data? (a speculative read) */
  N = n; failed = 0; fuel = 1000000; nfun = 0; eid = 0; hc_reset(); inp_on = 0;
  fail_quiet++; V *v = eval(p, NULL); Expr *x = v && !failed ? to_expr(v) : NULL; fail_quiet--;
  int ok = x && !failed && const_tree(x, 0);
  failed = 0; nfun = 0; arena_free(); hc_reset();
  return ok;
}
/* The unit with its small constants compiled in (small_data), else as it was asked for.  `an` is updated to
   the arguments the unit that compiled takes. */
static Compiled *compile_pref(Net *n, int F, const Port *ap, int *an, int car) {
  int an2[8], diff = 0;
  for (int k = 0; k < car; k++) { an2[k] = an[k]; if (an[k] == 2 && !lin_io_looping && small_data(n, ap[k], SMALL_CONST_NODES) && const_data(n, ap[k])) { an2[k] = 0; diff = 1; } }
  if (diff) {
    int sc = cx_n; Port *sp = NULL; int *sk = NULL;
    if (sc) { sp = malloc(sizeof *sp * (size_t)sc); sk = malloc(sizeof *sk * (size_t)sc); memcpy(sp, cx_port, sizeof *sp * (size_t)sc); memcpy(sk, cx_kind, sizeof *sk * (size_t)sc); }
    Compiled *c = compile_fn_ex(n, F, ap, an2);
    if (c) { for (int k = 0; k < car; k++) an[k] = an2[k]; free(sp); free(sk); DBG("(small constants compiled in)\n"); return c; }
    if (sc) { memcpy(cx_port, sp, sizeof *sp * (size_t)sc); memcpy(cx_kind, sk, sizeof *sk * (size_t)sc); } cx_n = sc; free(sp); free(sk);
  }
  return compile_fn_ex(n, F, ap, an);
}
/* A RECURSIVE CALL THE UNIT DOES NOT TAKE, MADE CHEAP.  `(Y v) args` reduced as it stands goes through the
   combinator's own machinery every call: `(\x. h (x x))` duplicated by its fans, the self-application unfolded,
   and v copied through layers of those fans (measured: ~300 fan interactions per iteration of a counting loop,
   2 of them betas, and a time that grows faster than the loop).  What the combinator computes is one equation,
   `Y v = v (Y v)`, and that is the rewrite:

       (Y v) args   ->   (v1 (Y' v2)) args,      v1 and v2 the two sides of ONE new fan on v.

   Nothing of v is copied here: the fan copies it as each call reaches it, so a call pays for what it uses (an
   untaken branch is never copied), and what is reduced in front of the fan -- a redex of v that does not depend on
   the argument -- is reduced once and shared by every call: the sharing is the net's own.  There is no walk over
   v, so no size of v matters, and v need not be closed or private.  Y' is a copy of the combinator (a fixed dozen
   nodes) on a new application; the old pair is dropped -- an eraser takes the old combinator -- so whatever named
   it (a demand root) goes with it, and a reference fires only when its own value is demanded.

   THE FAN'S LABEL is the call's own (net_fresh_label): no other fan carries it, so the core can retire the
   duplication as soon as the call's copy can no longer be observed -- the call returned, or what it left is
   garbage -- and its fans become wires to the definition's side.  Without that, every call would leave its fans
   waiting in the definition (an eraser at one copy port waits), and later calls would walk through all of
   them: the net would grow with the number of calls and the time with its square. */
/* a copy of the combinator: everything hanging off `h` but its port 0, or -1 when that is not closed */
static int y_copy(Net *n, int h) {
  int *list = NULL; int64_t nl = 0, cl = 32; int ok = 1, res = -1;
  list = malloc(sizeof *list * (size_t)cl); list[nl++] = h;
  for (int64_t i = 0; i < nl && ok; i++) {
    int u = list[i]; int np = n->tag[u] == ERA ? 1 : 3;
    for (int k = 0; k < np; k++) {
      if (u == h && k == 0) continue;
      Port w = W(n, (Port){u, k});
      if (w.node <= 0 || !live(n, w) || n->tag[w.node] == ROOT) { ok = 0; break; }
      int64_t j; for (j = 0; j < nl && list[j] != w.node; j++) ;
      if (j < nl) continue;
      if (nl == cl) list = realloc(list, sizeof *list * (size_t)(cl *= 2));
      list[nl++] = w.node;
    }
  }
  if (ok) {
    int *cp = malloc(sizeof *cp * (size_t)nl);
    for (int64_t i = 0; i < nl; i++) cp[i] = net_alloc(n, n->tag[list[i]], n->scope[list[i]]).node;
    for (int64_t i = 0; i < nl; i++) {
      int u = list[i], np = n->tag[u] == ERA ? 1 : 3;
      for (int k = 0; k < np; k++) {
        if (u == h && k == 0) continue;
        Port w = W(n, (Port){u, k}); int64_t j; for (j = 0; j < nl && list[j] != w.node; j++) ;
        if (j < i || (j == i && (int)w.port < k)) continue;   /* (each wire once) */
        net_link(n, (Port){cp[i], k}, (Port){cp[j], w.port}, 1);
      }
    }
    res = cp[0]; free(cp);
  }
  free(list);
  return res;
}
static int y_off = -1;
static int y_expand(Net *n, int h, int appy) {
  if (y_off < 0) y_off = getenv("LIN_Y_OFF") != NULL;
  if (y_off) return 0;
  int Yc = y_copy(n, h);
  if (Yc < 0) return 0;
  Port out = W(n, (Port){appy, 1}), v = W(n, (Port){appy, 2});
  Port d = net_alloc(n, DUP, net_fresh_label(n));
  Port b = net_alloc(n, APP, n->scope[appy]), a2 = net_alloc(n, APP, n->scope[appy]);
  net_link(n, (Port){d.node, 0}, v, 1);            /* the one fan on v */
  net_link(n, (Port){b.node, 0}, (Port){d.node, 1}, 1);
  net_link(n, (Port){b.node, 1}, out, 1);
  net_link(n, (Port){a2.node, 2}, (Port){d.node, 2}, 1);
  net_link(n, (Port){b.node, 2}, (Port){a2.node, 1}, 1);
  net_drop(n, appy);                                /* (its function, the old combinator, gets the eraser; v has moved) */
  net_link(n, (Port){a2.node, 0}, (Port){Yc, 0}, 1);   /* a redex, queued: fired when the self argument is demanded */
  return 1;
}
/* A CALL SHARED BY TWO COPIES, SPLIT.  A function the net is still copying (y_expand's one fan, with its own label L)
   shares its body between the copy being run and the copy kept for the next call, and a call in that body then
   has an argument that is a SUPERPOSITION -- {a1 a2}_L, the two copies' values -- which no unit can be given: the
   call stands for two calls.  So it is made two, by the rule an application to a superposition has,

       (Y F) .. {a1 a2}_L ..   ->   { ((Y1 F1) .. a1 ..)  ((Y2 F2) .. a2 ..) }_L      F, and every other argument, shared by fans labelled L

   -- the result a superposition with the same label, so the consumer's copying fan (label L) meets it and each copy
   receives its own call.  Each is an ordinary call (a fresh combinator applied to F through the L fan), which the
   unit takes like any other; the copy it reached F by is the one it reads F's body at (WHICH COPY). */
static int y_split(Net *n, int h, int appy, int F, int car) {
  (void)F;
  int c[car], ks = -1;   /* (the spine's own length: one slot per argument) */
  int cl = appy;
  for (int k = 0; k < car; k++) {
    Port nx = W(n, (Port){cl, 1});
    if (!is(n, nx, APP, 0)) return 0;
    cl = c[k] = nx.node;
    Port a = W(n, (Port){cl, 2});
    if (ks < 0 && is(n, a, DUP, 0) && xing_fresh(n, n->scope[a.node])) ks = k;
  }
  if (ks < 0) return 0;
  int S = W(n, (Port){c[ks], 2}).node;
  Scope L = n->scope[S];
  int Y1 = y_copy(n, h); if (Y1 < 0) return 0;
  int Y2 = y_copy(n, h); if (Y2 < 0) { net_drop(n, Y1); return 0; }
  Port out = W(n, (Port){c[car - 1], 1}), fv = W(n, (Port){appy, 2});
  Port Df = net_alloc(n, DUP, L), A1 = net_alloc(n, APP, n->scope[appy]), A2 = net_alloc(n, APP, n->scope[appy]);
  net_link(n, (Port){Df.node, 0}, fv, 1);
  net_link(n, (Port){A1.node, 2}, (Port){Df.node, 1}, 0);
  net_link(n, (Port){A2.node, 2}, (Port){Df.node, 2}, 0);
  Port f1 = (Port){A1.node, 1}, f2 = (Port){A2.node, 1};
  for (int k = 0; k < car; k++) {
    Port B1 = net_alloc(n, APP, n->scope[c[k]]), B2 = net_alloc(n, APP, n->scope[c[k]]);
    net_link(n, (Port){B1.node, 0}, f1, 1); net_link(n, (Port){B2.node, 0}, f2, 1);
    if (k == ks) {
      net_link(n, (Port){B1.node, 2}, W(n, (Port){S, 1}), 1);
      net_link(n, (Port){B2.node, 2}, W(n, (Port){S, 2}), 1);
    } else {
      Port D = net_alloc(n, DUP, L);
      net_link(n, (Port){D.node, 0}, W(n, (Port){c[k], 2}), 1);
      net_link(n, (Port){B1.node, 2}, (Port){D.node, 1}, 0);
      net_link(n, (Port){B2.node, 2}, (Port){D.node, 2}, 0);
    }
    f1 = (Port){B1.node, 1}; f2 = (Port){B2.node, 1};
  }
  Port R = net_alloc(n, DUP, L);
  net_link(n, (Port){R.node, 0}, out, 1);
  net_link(n, (Port){R.node, 1}, f1, 0);
  net_link(n, (Port){R.node, 2}, f2, 0);
  for (int k = 0; k < 3; k++) n->wire[S * 3 + k] = NONE;   /* (its copies have moved to the two calls) */
  net_drop(n, S);
  for (int k = car - 1; k >= 0; k--) net_drop(n, c[k]);   /* (wires all moved: nothing is erased) */
  net_drop(n, appy);                                 /* (its function, the old combinator, gets the eraser; F has moved) */
  net_link(n, (Port){A1.node, 0}, (Port){Y1, 0}, 1);   /* the two calls: redexes, queued */
  net_link(n, (Port){A2.node, 0}, (Port){Y2, 0}, 1);
  DBG("split a call shared by two copies (argument %d)\n", ks);
  return 1;
}
/* a call the unit declines: the cheap rewrite above, else the net's own beta */
static void y_decline(Net *n, Port p1, Port p2, int *changed) {
  int h, appy;
  if (y_fix(n, p1, p2, &h, &appy) && y_expand(n, h, appy)) { (*changed)++; n->steps++; return; }
  if (live(n, p1) && live(n, p2) && W(n, p1).node == p2.node && net_interact(n, p1, p2)) { (*changed)++; n->steps++; }
}
static int fn_reduce_body(Net *n, Port *rx, int nred, int64_t limit, int *changed);
static int fn_reduce(Net *n, Port *rx, int nred, int64_t limit, int *changed) {
  int r = fn_reduce_body(n, rx, nred, limit, changed);
  xing_on = 0; nxing = 0;
  return r;
}
static int fn_reduce_body(Net *n, Port *rx, int nred, int64_t limit, int *changed) {
  (void)limit;
  int folded = 0;
  for (int i = 0; i < nred; i++) {
    Port p1 = rx[2 * i], p2 = rx[2 * i + 1];
    if (fn_off) { y_decline(n, p1, p2, changed); continue; }
    int h, appy, F;
    xing_on = 0; nxing = 0;
    if (!y_call(n, p1, p2, &h, &appy, &F)) {           /* an earlier fold in this wave took it */
      y_decline(n, p1, p2, changed);
      continue;
    }
    xing_on = 1; (void)dhop(n, W(n, (Port){appy, 2})); xing_on = 0;   /* (the copy of F this call reached: WHICH COPY) */
    /* (the call WITH its arguments first, when some are not numbers yet: that unit is the one that runs, and a
       function of data or of functions compiles no other way -- the function alone is the fallback) */
    Compiled *c = NULL;
    int64_t args[8]; int call = appy, ok;
    int car = lin_precompile_depth ? 0 : (N = n, fun_arity(F));
    /* ARGUMENTS THAT ARE NOT VALUES YET -- `(check (make 7))` -- are compiled into the unit as expressions, rather
       than built by the net first (which is the slow part); a number already there is passed as one.  A function
       taking a FUNCTION compiles only with its arguments (it is specialised to them). */
    if (car > 0 && !root_mode && y_split(n, h, appy, F, car)) { (*changed)++; n->steps++; continue; }
    if (car > 0 && car <= 8) {
      Port ap[8]; int an[8], cl = appy, nexpr = 0, shape = 1;
      for (int k = 0; k < car; k++) {
        Port nx = W(n, (Port){cl, 1});
        if (!is(n, nx, APP, 0)) { shape = 0; break; }
        cl = nx.node; ap[k] = W(n, (Port){cl, 2});
        int64_t dummy; an[k] = numeral_shape(n, ap[k]) && net_read_i64(n, ap[k], &dummy);
        if (!an[k] && data_value(n, ap[k]) && !list_end(n, ap[k])) an[k] = 2;   /* data already in the net: passed in at call time */
        if (dbg > 1) { int64_t x = 0; int ns = numeral_shape(n, ap[k]); int ok = ns && net_read_i64(n, ap[k], &x); DBG("[arg %d: shape %d read %d (%" PRId64 ") -> %d]\n", k, ns, ok, x, an[k]); }
        nexpr += an[k] != 1;
      }
      if (root_mode && (!shape || W(n, (Port){0, 0}).node == cl)) return folded;   /* (the call IS the expression: the ordinary way) */
      if (shape && (nexpr || root_mode)) {
        /* the context first (see cx_push): the widest that compiles, else the call alone */
        int top = cl; cx_n = 0;
        for (int k = 0; k < n->nn; k++) {
          Port o = W(n, (Port){top, 1});
          if (is(n, o, APP, 0)) { cx_push(0, W(n, (Port){o.node, 2})); top = o.node; }
          else if (is(n, o, APP, 2)) { cx_push(1, W(n, (Port){o.node, 0})); top = o.node; }
          else break;
        }
        double t_c0 = now_ms();
        Compiled *c2 = NULL;
        int *tops = malloc(sizeof *tops * (size_t)(cx_n + 1)), all = cx_n;   /* each context's node, to cut back to */
        { int t = cl; tops[0] = cl;
          for (int i = 0; i < all; i++) { Port o = W(n, (Port){t, 1}); t = o.node; tops[i + 1] = t; } }
        if (root_mode) {                              /* (see fn_match) */
          Port rp = W(n, (Port){0, 0});
          cx_n = 0; cx_push(2, rp);
          c2 = compile_pref(n, F, ap, an, car);
          cx_n = 0; all = 0;
          if (!c2) { free(tops); return folded; }
          cl = rp.node; DBG("(the whole expression is the unit)\n");
        }
        for (; cx_n > 0 && !c2; cx_n--) {             /* the widest context that compiles */
          c2 = compile_pref(n, F, ap, an, car);
          if (c2) cl = tops[cx_n];
        }
        if (all && !c2) DBG("(no context of the call compiles: the call alone)\n");
        free(tops); cx_n = 0;
        if (!c2 && !root_mode) c2 = compile_pref(n, F, ap, an, car);
        double t_c1 = now_ms();
        if (c2) {
          int nn = 0, pi = 0;
          int64_t *xa = malloc(sizeof *xa * (size_t)(car + n_inp + c2->npsh + 1));   /* (the arguments, inputs included) */
          Marsh M; memset(&M, 0, sizeof M); M.n = n; M.c = c2; M.steps0 = n->steps;
          for (int k = 0; k < car && !M.bad; k++) {
            if (an[k] == 1) { net_read_i64(n, ap[k], &xa[nn++]); pi++; }
            else if (an[k] == 2) {
/* (a data argument the unit has NO shape for is one it never looks at -- passed along from call to
                 call, or met by a whole-expression unit where the program names it: nothing is read in for it) */
              if (!c2->npsh || (pi < c2->npsh && c2->psh[pi].k == 0)) { xa[nn++] = 0; pi++; continue; }
              if (pi >= c2->npsh) { M.bad = 1; break; }
              xa[nn++] = marshal(&M, ap[k], c2->psh[pi]); pi++;
              if (dbg > 1) DBG("[argument %d passed in as %d %s: %" PRIx64 "]\n", k, c2->psh[pi - 1].k, c2->psh[pi - 1].dt ? c2->psh[pi - 1].dt : "", (uint64_t)xa[nn - 1]);
            }
          }
          for (int i = 0; i < n_inp && !M.bad; i++, pi++) {   /* the inputs met inside the arguments */
            if (pi >= c2->npsh) { M.bad = 1; break; }
            xa[nn++] = marshal(&M, inp_port[i], c2->psh[pi]);
          }
          if (M.bad) { DBG("an argument could not be read in: the net computes the call\n"); ms_free(&M); free(xa); goto decline_ex; }
          extern int lin_threads;
          double t_m = now_ms();
          int64_t r = c2->fn(xa, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
          double t_r = now_ms();
          if (dbg) DBG("[time: compile %.2f ms, read in %.2f ms, run %.2f ms]\n", t_c1 - t_c0, t_m - t_c1, t_r - t_m);
          free(xa);
          if (c2->aborted && *c2->aborted) { DBG("the data unit's guard fired: the net computes it\n"); ms_free(&M); }
          else {
            Port val = result_port(n, c2, r);
            ms_free(&M);                                 /* (after the result is read: it may hold blocks passed in) */
            if (val.node < 0) goto decline_ex;
            Port out = W(n, (Port){cl, 1});
            { int plain = n_inp == 0; for (int k = 0; plain && k < car; k++) plain = an[k] != 2;   /* (nothing read in at run time) */
              if (plain && n->tag[out.node] == ROOT) { int64_t *ka = malloc(sizeof *ka * (size_t)(car + 1)); int kn = 0;
                for (int k = 0; k < car; k++) if (an[k] == 1) net_read_i64(n, ap[k], &ka[kn++]);
                form_note(n, c2, ka, kn); free(ka); } }
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
    if (root_mode) return folded;
    c = lin_precompile_depth ? NULL : compile_fn(n, F);
    ok = c != NULL;
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
      y_decline(n, p1, p2, changed);
      continue;
    }
    extern int lin_threads;
    int64_t r = c->fn(args, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
    if (c->aborted && *c->aborted) {                 /* a data unit's guard fired: the net computes it, lazily */
      DBG("the data unit's guard fired: the net computes it\n");
      y_decline(n, p1, p2, changed);
      continue;
    }
    Port val = result_port(n, c, r);
    if (val.node < 0) {
      y_decline(n, p1, p2, changed);
      continue;
    }
    Port out = W(n, (Port){call, 1});
    if (n->tag[out.node] == ROOT) form_note(n, c, args, c->arity);
    net_link(n, val, out, 1);
    net_drop(n, call);                                  /* erases the call chain, Y and F behind it */
    DBG("folded a call of arity %d -> %s\n", c->arity, c->kind == 5 ? "a structure" : "a word");
    lin_fold_bump(); folded++; (*changed)++; n->steps++;
  }
  return folded;
}

/* THE WHOLE EXPRESSION, BEFORE ANYTHING ELSE TOUCHES IT.  A call's context is a chain, and a chain ends at a
   fan -- every operand of an arithmetic operation is shared with the operation's own definition.  So each call
   under an operation was a unit of its own, and a value two of them used (`v` in `(fdiv (dot u v) (dot v v))`)
   was computed by both, where the net computes it once.  The expression the program observes is the widest
   context there is: compiled as one unit, what it shares is one node of the unit.

   It can only be replaced while nobody holds a port inside it -- not from within a force, which is how an
   operation reaches its operands -- so this runs from `match`, on a net no rule has fired in yet: find a
   recursive call in the expression, and try the expression as that call's unit.  Declined, nothing changed. */
static int fn_reduce(Net *n, Port *rx, int nred, int64_t limit, int *changed);
static int fn_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)st; (void)view; (void)out;
  if (fn_off < 0) fn_off = getenv("LIN_FN_OFF") != NULL;
  if (fn_off || n->steps != 0 || lin_reduce_nested() || lin_precompile_depth || n->tag[0] != ROOT) return 0;
  Port rp = W(n, (Port){0, 0});
  if (!is(n, rp, APP, 1)) return 0;
  unsigned char *seen = calloc((size_t)n->nn, 1); int *stk = malloc(sizeof *stk * (size_t)n->nn), sp = 0, found = 0;
  Port rx[2];
  stk[sp++] = rp.node; seen[rp.node] = 1;
  while (sp > 0 && !found) {                         /* the applications and fans of the expression, outermost first */
    int a = stk[--sp];
    if (n->tag[a] == APP) {
      Port f = W(n, (Port){a, 0});
      if (live(n, f) && f.port == 0 && n->tag[f.node] == LAM && (fn_claim(n, (Port){a, 0}, f) || fn_claim(n, f, (Port){a, 0}))) {
        int h, ay, F; rx[0] = (Port){a, 0}; rx[1] = f;
        if (!y_call(n, rx[0], rx[1], &h, &ay, &F)) { rx[0] = f; rx[1] = (Port){a, 0}; }
        found = 1; break;
      }
    }
    for (int k = 2; k >= 0; k -= 2) {                /* (an application's argument, then its function -- looked at first, so
                                                         the call found is the outermost: a fan has only its source) */
      if (n->tag[a] == DUP && k == 2) continue;
      Port w = W(n, (Port){a, k});
      if (!live(n, w) || seen[w.node]) continue;
      int t = n->tag[w.node];
      if ((t == APP && w.port == 1) || (t == DUP && w.port != 0)) { seen[w.node] = 1; stk[sp++] = w.node; }
    }
  }
  free(seen); free(stk);
  if (!found) return 0;
  int ch = 0;
  root_mode = 1; fn_reduce(n, rx, 1, 0, &ch); root_mode = 0;
  return 0;
}
LinDriver lin_fn_driver;
LIN_PLUGIN_INIT(fn) {
  if (dbg < 0) dbg = getenv("LIN_FN_DEBUG") ? atoi(getenv("LIN_FN_DEBUG")) : 0;
  static int registered;
  if (registered) return;
  registered = 1;
  lin_driver_add(&lin_fn_driver);
  lin_form_register(form_recall, form_commit);
  cells_init();                                      /* (the cell datatype, registered once) */
}
LinDriver lin_fn_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "fn", .description = "function compiler: a recursive integer function, compiled to C from its net",
  .caps = LIN_CAP_PREEMPT, .priority = 3,
  .claim = fn_claim, .reduce = fn_reduce, .match = fn_match,
};
