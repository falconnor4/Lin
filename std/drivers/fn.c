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
__thread __attribute__((tls_model("initial-exec"))) long *lin_fl[8];   /* freed blocks by size (words), for reuse */
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
struct Drop { const struct Expr *p; int fn; struct Drop *next; };   /* a parameter dropped at a path's end (drop_paths) */
typedef struct Expr { int op; long k; struct Expr *a, *b, *c; struct Expr **args; int nargs, kind;   /* kind 1 int, 3 bool */
                      int id, var, vscope, rtag, untag, box; const LinCtor *ci; unsigned char *freeb; struct Expr *fre; int fren; unsigned clone; const struct Expr *dropx; int dropfn; struct Drop *drops; } Expr;   /* dropx: a parameter this call only borrowed and nothing needs after it -- freed (by drop function dropfn) once the call returns */   /* clone: the arguments (a call's) handed over as a copy of their one block */   /* fre: a consumed block (fren words) this tail frees */   /* ci: the constructor (E_CTOR, E_FIELD) or one of the datatype's (E_MATCH) */   /* untag: the datatype's blocks carry no tag (box: its one boxed constructor) */   /* rtag: a reused block's constructor + 1 (ownership) */   /* id: a dense index; var: the local it is bound to while emitting */
enum { V_CLO, V_SYM, V_C1, V_COND, V_SELF, V_FIX, V_MCONS, V_MCONS1, V_MCELL, V_MNIL, V_MATCH };   /* V_FIX: a recursive function met, its arguments being collected */   /* V_MATCH: data applied to branches */
struct Lz;
typedef struct Env { int lam; struct Lz *t; struct Env *next; } Env;
typedef struct V { int k; int lam; Env *env; Expr *e; struct Lz *a, *b; struct Lz **args; int nargs; Expr *x; int cells; } V;   /* cells: a match on the cell encoding */   /* x: to_expr's answer */
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
static Expr *field_expr(Expr *scrut, int j, int untag, const LinCtor *ci) {
  Expr *e = mke(E_FIELD, field_is_bool(ci, j) ? 3 : 1); e->a = scrut; e->k = j; e->untag = untag; e->ci = ci; return hc(e);
}
/* THE CELL ENCODING AS A DATATYPE.  Lists, strings and the std's sequences are cells `\c.\n.((c h) t)` ended by
   `\c.\n.true` -- no constructor marker, but two constructors all the same, and the compiler gives them the
   datatype treatment under a name no source can write: a cell is a block {h, t}, the end an immediate.  A value
   applied to branches with no marker is taken apart as cells; whether it really is a list is the SHAPE analysis'
   question (a numeral is cells too, of bits -- one used both ways is not compiled).  The end answers `true` to
   whatever it is given, which a program reads only as a boolean: here it is a constant every shape accepts. */
static const LinCtor *cell_cons, *cell_nil;
static const char *cells_dt;
static void cells_init(void) {
  if (cell_cons && lin_ctor_info(1)) {               /* (re-read: the registry may have moved) */
    cell_cons = lin_ctor_info(lin_ctor_lookup(" cons")); cell_nil = lin_ctor_info(lin_ctor_lookup(" nil"));
    return;
  }
  lin_ctor_register(" cells", " cons", 2, 0, 2); lin_ctor_register(" cells", " nil", 2, 1, 0);
  cell_cons = lin_ctor_info(lin_ctor_lookup(" cons")); cell_nil = lin_ctor_info(lin_ctor_lookup(" nil"));
  cells_dt = cell_cons ? cell_cons->dt : NULL;
}
static Expr *end_true(void) { Expr *e = mke(E_CONST, 3); e->k = 3; e->box = 1; return hc(e); }   /* (3: true, and the end) */
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
  r->args[1] = end_true();                           /* the end answers true, whatever the second branch was */
  r->kind = r->args[0]->kind;
  V *res = mkv(V_SYM); res->e = hc(r); return res;
}
static V *match_add(V *m, Lz *x) {
  if (m->cells || (m->nargs == 0 && !(x->state == 0 && ({ Port b_, i_; int l_; marker_app(x->p, &b_, &l_, &i_); }))))
    return cells_add(m, x);
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
  return is(n, dhop(n, W(n, (Port){nn.node, 2})), LAM, 0);
}
/* A constant list: the cells answer the markers one by one, the end answers with a boolean.  Speculative: a value
   that is not a list leaves no trace. */
static Expr *const_cells(V *v) {
  cells_init(); if (!cell_cons || !cell_nil) return NULL;
  int sf = failed, snf = nfun; long sfu = fuel;
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
    if (r->k == V_CLO) { int bo; const_bool(r, &bo); ok = bo && !failed; }
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
    int ok, sf = failed, snf = nfun; long sfu = fuel;
    fail_quiet++; long k = const_int(v, &ok); if (failed) ok = 0; fail_quiet--;
    if (!ok) { failed = sf; fuel = sfu; fun_rollback(snf); }
    if (ok) { Expr *e = mke(E_CONST, 1); e->k = k; return hc(e); }
    fail_quiet++; int bk = const_bool(v, &ok); if (failed) ok = 0; fail_quiet--;
    if (!ok) { failed = sf; fuel = sfu; fun_rollback(snf); }
    if (ok) { Expr *e = mke(E_CONST, 3); e->k = bk; return hc(e); }
    if (inp_on && !v->env && numeral_shape(N, (Port){v->lam, 0}) && !list_end(N, (Port){v->lam, 0})) {   /* a list already built: read in at call time */
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
/* DESTINATION PASSING.  `(scons (f h) (smap f t))` is not a tail call -- the cell is built after the call returns
   -- so a list a million long was a million frames.  A function with such a tail gets a second form, `fN_d(dst,
   ...)`, that writes its result through `dst` instead of returning it: the cell is built FIRST, with a hole where
   the call's result goes, and the call becomes a tail call given the hole's address.  cc turns that into a loop.
   `hasd[f]`: f has the form; `tailpos`: the expression about to be written is in tail position of one. */
static unsigned char *hasd; static int tailpos; static const struct Expr *dp_hole;
static int emitting;
static int dp_self;   /* how the function being written names ITSELF: 0 `_d`, 1 `_ds` (its loop), 2 `_dp` (a stretch of its loop) */
static const char *dp_name(long k) { return k != emitting || !dp_self ? "_d" : dp_self == 1 ? "_ds" : "_dp"; }
static const char *dp_stop(long k) { return k == emitting && dp_self == 2 ? ", stop" : ""; }
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
  int tp = tailpos; tailpos = 0;
  st_grow(); stamp += 2;
  count_uses(e);
  const Expr **cand = NULL; int nc = 0, cc = 0;
  certain(e, cert(e), &cand, &nc, &cc);
  int nb = 0, ok = 1, nk = 0;
  for (int i = 0; i < nc; i++) {                   /* choose first: emitting a binding runs nested regions' passes */
    const Expr *x = cand[i];
    if (x != e && st_uses[x->id] >= 2 && x->op != E_CONST && x->op != E_PARAM && x->op != E_FIELD) cand[nk++] = x;   /* (a field read is one load: not worth a local) */
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
  tailpos = tp;
  ok = ok && emitx(b, pre, e, par, budget - 1);
  tailpos = 0;
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
/* Operands run side by side are each written as a function of the PARAMETERS: a value they share -- a node
   both reach, or one the enclosing code already holds in a local -- would be computed again inside each.  That
   is the opposite of what sharing is for (`(fdiv (dot u v) (dot v v))` built `v` on both threads), so such
   operands are evaluated in turn, the shared value once. */
static int ps_walk(const Expr *e, unsigned char *mark, int who) {
  if (!e || e->op == E_PARAM || e->op == E_CONST) return 0;
  if (mark[e->id] == who) return 0;
  if ((mark[e->id] || bound(e)) && has_call(e)) return 1;
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
/* INDEXED FIELDS.  A datatype with many fields of one kind is how a program says "an array of k slots" in pure Lin
   (std/array.lin's trie nodes): choosing slot k is a decision tree of comparisons, and replacing it is one
   conditional per field.  When the tree provably picks field k+off for every value k can take (k is masked,
   so its range is known), that is ONE indexed load; and a constructor whose every field j is
   `k == j+off ? f(field j) : field j`, with f the same for all j, is ONE indexed read-modify-write. */
static int key_hi(const Expr *k, long *hi) {
  if (k->op != E_BIN || k->k != LIN_OP_BAND) return 0;
  const Expr *m = k->b->op == E_CONST ? k->b : k->a->op == E_CONST ? k->a : NULL;
  long most = 0; const LinCtor *c;                  /* (no constructor has more slots than the widest declared) */
  for (long id = 1; (c = lin_ctor_info(id)); id++) if (c->k > most) most = c->k;
  if (!m || m->k <= 0 || m->k >= most || (m->k & (m->k + 1))) return 0;
  *hi = m->k; return 1;
}
static int cmp_int(long code, long x, long y) {
  switch (code) { case LIN_OP_EQ: return x == y; case LIN_OP_LT: return x < y; case LIN_OP_LEQ: return x <= y;
                  case LIN_OP_GT: return x > y; case LIN_OP_GEQ: return x >= y; }
  return -1;
}
static const Expr *dt_key(const Expr *e) {           /* the compared expression at the root of a decision tree */
  if (e->op != E_IF || e->a->op != E_BIN || cmp_int(e->a->k, 0, 0) < 0) return NULL;
  return e->a->b->op == E_CONST ? e->a->a : e->a->a->op == E_CONST ? e->a->b : NULL;
}
static const Expr *dt_leaf(const Expr *e, const Expr *K, long v) {
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
static int indexed_pick(const Expr *e, const Expr **K, const Expr **S, long *off) {
  long hi; const Expr *k = dt_key(e);
  if (!k || !key_hi(k, &hi)) return 0;
  const Expr *base = NULL; const LinCtor *ci = NULL; long o = 0; int untag = 0;
  for (long v = 0; v <= hi; v++) {
    const Expr *l = dt_leaf(e, k, v);
    if (!l || l->op != E_FIELD) return 0;
    if (!v) { base = l->a; ci = l->ci; o = l->k; untag = l->untag; }
    else if (l->a != base || l->ci != ci || l->untag != untag || l->k != v + o) return 0;
  }
  if (!ci || hi + o >= ci->k) return 0;
  *K = k; *S = base; *off = o + !untag; return 1;
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
static int eq_mod(const Expr *a, const Expr *b, const Expr *f0, const Expr *fj, int depth) {   /* a[f0] == b[fj] */
  if (a == f0) return b == fj;
  if (a == b) return !contains(a, f0, 0);
  if (depth > eid || a->op != b->op || a->k != b->k || a->kind != b->kind || a->nargs != b->nargs || a->ci != b->ci || a->untag != b->untag) return 0;
  if (!a->a != !b->a || !a->b != !b->b || !a->c != !b->c) return 0;
  if (a->a && !eq_mod(a->a, b->a, f0, fj, depth + 1)) return 0;
  if (a->b && !eq_mod(a->b, b->b, f0, fj, depth + 1)) return 0;
  if (a->c && !eq_mod(a->c, b->c, f0, fj, depth + 1)) return 0;
  for (int i = 0; i < a->nargs; i++) if (!eq_mod(a->args[i], b->args[i], f0, fj, depth + 1)) return 0;
  return 1;
}
/* A reused constructor that rewrites exactly field K+off as f(that field)?  Writes K, off and f's field-0 instance. */
static int indexed_update(const Expr *e, const Expr **K, long *off, const Expr **f0, const Expr **x0) {
  if (!e->c || e->nargs < 2) return 0;
  const Expr *k = NULL; long o = 0;
  for (int j = 0; j < e->nargs; j++) {
    const Expr *a = e->args[j];
    if (a->op != E_IF || a->a->op != E_BIN || a->a->k != LIN_OP_EQ) return 0;
    const Expr *kk = a->a->b->op == E_CONST ? a->a->a : a->a->a->op == E_CONST ? a->a->b : NULL;
    long cv = a->a->b->op == E_CONST ? a->a->b->k : a->a->a->k;
    const Expr *old = a->c;
    if (!kk || old->op != E_FIELD || old->a != e->c || old->k != j) return 0;
    if (!j) { k = kk; o = cv; } else if (kk != k || cv != j + o) return 0;
    if (j && !eq_mod(e->args[0]->b, a->b, e->args[0]->c, old, 0)) return 0;
  }
  long hi; if (!key_hi(k, &hi) || hi != e->nargs - 1 || o != 0) return 0;
  *K = k; *off = !e->untag; *f0 = e->args[0]->c; *x0 = e->args[0]->b; return 1;
}
static int field_live(const LinCtor *ci, int j);
static void fre_fields(const Expr *e, const Expr *s, Expr ***out, int *n, int *cap) {   /* the reads of s's fields in e */
  if (!e) return;
  if (e->id < mm_cap[MM_SITE]) { if (mm_has(MM_SITE, e)) return; mm_put(MM_SITE, e, 1); }
  if (e->op == E_FIELD && e->a == s) { if (*n >= *cap) *out = realloc(*out, sizeof **out * (size_t)(*cap = *cap ? *cap * 2 : 8)); (*out)[(*n)++] = (Expr *)e; return; }
  if (e->a) fre_fields(e->a, s, out, n, cap);
  if (e->b) fre_fields(e->b, s, out, n, cap);
  if (e->c && e->op != E_CTOR) fre_fields(e->c, s, out, n, cap);
  for (int i = 0; i < e->nargs && e->args; i++) fre_fields(e->args[i], s, out, n, cap);
}
static int call_fv(Buf *b, long k) {                 /* the callee's lifted parameters: ours, or passed on */
  for (int i = 0; k < lifted && i < nfv[k]; i++) {
    const FV *v = &fvs[k][i];
    if (v->h == emitting) put(b, ", p%ld", v->k);
    else if (emitting >= 0 && emitting < lifted && fv_has(emitting, v->h, v->k)) put(b, ", l%d_%ld", v->h + 1, v->k);
    else { DBG("declined: a lifted parameter with no source (f%d calls f%ld, which reads f%d's parameter %ld)\n", emitting, k, v->h, v->k); return 0; }
  }
  return 1;
}
/* An argument of a call.  One marked to be handed over as a COPY (ownership: uniq_calls) is its block copied --
   a flat value, a few words -- so that the callee owns what it is given and can rebuild in it. */
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget);
#define CLONE_BITS ((int)(sizeof(((Expr *)0)->clone) * 8))   /* (one bit of the mask per argument) */
static int clone_words(const Expr *a);
static int emit_arg(Buf *b, Buf *pre, const Expr *call, int i, int par, int budget) {
  const Expr *a = call->args[i];
  if (i < CLONE_BITS && ((call->clone >> i) & 1u)) {
    int w = clone_words(a);
    if (w > 0) { uses_data = 1; put(b, "lin_clone("); if (!emitx(b, pre, a, par, budget)) return 0; put(b, ", %d)", w); return 1; }
  }
  return emitx(b, pre, a, par, budget);
}
static int emitx(Buf *b, Buf *pre, const Expr *e, int par, int budget) {
  int tp = tailpos; tailpos = 0;
  if (budget <= 0) return 0;
  if (bound(e)) { put(b, tp ? "LIN_SET(dst, v%d)" : "v%d", e->var); return 1; }
  if (e->drops && !par) {                            /* (see drop_paths) */
    struct Drop *mine = NULL; for (struct Drop *d = e->drops; d; d = d->next) if (d->p->nargs == emitting) mine = d;
    if (mine) {
      Expr t = *e; t.drops = NULL; uses_data = 1;
      if (e->op == E_CALL) {                         /* the arguments, then the drops, then the call (a tail call stays one) */
        int a0 = nvar; nvar += e->nargs;
        int *sv = A(sizeof(int) * (size_t)(e->nargs + 1)), *ss = A(sizeof(int) * (size_t)(e->nargs + 1));
        put(b, "({ ");
        for (int i = 0; i < e->nargs; i++) { put(b, "long v%d = ", a0 + i); if (!emit_arg(b, pre, e, i, par, budget - 1)) return 0; put(b, "; "); }
        for (struct Drop *d = e->drops; d; d = d->next) if (d->p->nargs == emitting) put(b, "lin_drop%d(p%ld); ", d->fn, d->p->k);
        Expr **na = A(sizeof(Expr *) * (size_t)(e->nargs + 1)); t.args = na; t.clone = 0;
        for (int i = 0; i < e->nargs; i++) { Expr *v = mke(E_PARAM, e->args[i]->kind); v->var = a0 + i; v->vscope = fscope; na[i] = v; }
        (void)sv; (void)ss;
        tailpos = tp; int ok = emitx(b, pre, &t, par, budget - 1); put(b, "; })"); return ok;
      }
      put(b, "({ long r_ = "); int ok = emitx(b, pre, &t, par, budget - 1);   /* the value, then the drops */
      put(b, "; ");
      for (struct Drop *d = e->drops; d; d = d->next) if (d->p->nargs == emitting) put(b, "lin_drop%d(p%ld); ", d->fn, d->p->k);
      put(b, tp ? "LIN_SET(dst, r_); })" : "r_; })"); return ok;
    }
  }
  if (e->fre && !par) {                              /* a tail that frees the block its match consumed */
    Expr t = *e; t.fre = NULL;
    /* the fields of the block this tail still reads go into locals first; then the block is released, so what
       the tail allocates can be it */
    Expr **fl = NULL; int nfl = 0, cfl = 0;
    mm_new(MM_SITE); fre_fields(&t, e->fre, &fl, &nfl, &cfl);
    put(b, "({ ");
    for (int j = 0; j < nfl; j++) {
      if (bound(fl[j])) { fl[j] = NULL; continue; }
      int k = nvar++; put(b, "long v%d = ", k); if (!emitx(b, pre, fl[j], par, budget - 1)) { free(fl); return 0; } put(b, "; ");
      fl[j]->var = k; fl[j]->vscope = fscope;
    }
    put(b, "lin_free((long *)("); int ok = emitx(b, pre, e->fre, par, budget - 1);
    put(b, "), %d); ", e->fren);
    tailpos = tp;
    ok = ok && emitx(b, pre, &t, par, budget - 1); put(b, "; })");
    tailpos = 0;
    for (int j = 0; j < nfl; j++) if (fl[j]) fl[j]->var = -1;
    free(fl);
    return ok;
  }
  if (tp) {
    const Expr *K, *S; long off;
    if (e->op == E_CALL && hasd[e->k]) {              /* a tail call: the destination goes with it */
      put(b, "f%ld%s(dst", e->k, dp_name(e->k));
      for (int i = 0; i < e->nargs; i++) { put(b, ", "); if (!emit_arg(b, pre, e, i, par, budget - 1)) return 0; }
      if (!call_fv(b, e->k)) return 0;
      put(b, "%s)", dp_stop(e->k)); return 1;
    }
    { const Expr *K2, *f0, *x0; long off2;          /* slot K of a block rebuilt in place, given to a call: the loop of a trie update */
      if (e->op == E_CTOR && e->nargs && e->c && (e->untag || e->rtag - 1 == e->k) && indexed_update(e, &K2, &off2, &f0, &x0) &&
          x0->op == E_CALL && hasd[x0->k] && !bound(x0)) {
        int kv = nvar++, pv = nvar++, ov = nvar++, a0 = nvar; nvar += x0->nargs;
        put(b, "({ long v%d = ", kv); if (!emitx(b, pre, K2, par, budget - 1)) return 0;
        put(b, "; long *v%d = (long *)(", pv); if (!emitx(b, pre, e->c, par, budget - 1)) return 0;
        put(b, "); long v%d = v%d[v%d + %ld]; ", ov, pv, kv, off2);
        Expr *fx = (Expr *)f0; int sv = fx->var, ss = fx->vscope; fx->var = ov; fx->vscope = fscope;
        Expr *kx = (Expr *)K2; int skv = kx->var, sks = kx->vscope; kx->var = kv; kx->vscope = fscope;
        int ok = 1;
        for (int i = 0; ok && i < x0->nargs; i++) { put(b, "long v%d = ", a0 + i); ok = emit_arg(b, pre, x0, i, par, budget - 1); put(b, "; "); }
        fx->var = sv; fx->vscope = ss; kx->var = skv; kx->vscope = sks;
        if (!ok) return 0;
        put(b, "LIN_PUT(dst, (long)v%d); f%ld%s(&v%d[v%d + %ld]", pv, x0->k, dp_name(x0->k), pv, kv, off2);
        for (int i = 0; i < x0->nargs; i++) put(b, ", v%d", a0 + i);
        if (!call_fv(b, x0->k)) return 0;
        put(b, "%s); })", dp_stop(x0->k)); return 1;
      } }
    int hole = -1;
    if (e->op == E_CTOR && e->nargs)
      for (int i = 0; i < e->nargs && hole < 0; i++)
        if (e->args[i]->op == E_CALL && hasd[e->args[i]->k] && !bound(e->args[i]) && (!e->ci || field_live(e->ci, i))) hole = i;
    if (hole >= 0) {
      /* the call's arguments first (they may read the block this cell is rebuilt in), then the cell with a hole,
         then the call, told where its result goes */
      Expr *c = (Expr *)e->args[hole]; int hv = nvar++, ov = nvar++, a0 = nvar; nvar += c->nargs;
      put(b, "({ long v%d = 0; ", hv);
      for (int i = 0; i < c->nargs; i++) { put(b, "long v%d = ", a0 + i); if (!emit_arg(b, pre, c, i, par, budget - 1)) return 0; put(b, "; "); }
      int sv = c->var, ss = c->vscope; c->var = hv; c->vscope = fscope;
      const Expr *sh = dp_hole; dp_hole = c;
      put(b, "long *v%d = (long *)(", ov); int ok = emitx(b, pre, e, par, budget - 1);
      dp_hole = sh;
      c->var = sv; c->vscope = ss;
      if (!ok) return 0;
      put(b, "); LIN_SET(dst, (long)v%d); f%ld%s(&v%d[%d]", ov, c->k, dp_name(c->k), ov, hole + !e->untag);
      for (int i = 0; i < c->nargs; i++) put(b, ", v%d", a0 + i);
      if (!call_fv(b, c->k)) return 0;
      put(b, "%s); })", dp_stop(c->k)); return 1;
    }
    if (!(e->op == E_MATCH || (e->op == E_IF && !indexed_pick(e, &K, &S, &off)))) {   /* a leaf: the result itself */
      /* (a block rebuilt in place is usually where it was: LIN_PUT; anything else is new: LIN_SET) */
      put(b, e->op == E_CTOR && e->c ? "LIN_PUT(dst, " : "LIN_SET(dst, "); if (!emitx(b, pre, e, par, budget - 1)) return 0; put(b, ")"); return 1;
    }
  }
  switch (e->op) {
  case E_CONST: if (e->k == (long)(1UL << (LIN_INT_BITS - 1))) put(b, "(-%ldL-1)", -(e->k + 1)); else put(b, "(%ldL)", e->k); return 1;
  case E_PARAM:   /* an outer function's parameter: lifted into this one's extra parameters */
    if (e->nargs == emitting) { put(b, "p%ld", e->k); return 1; }
    if (emitting >= 0 && emitting < lifted && fv_has(emitting, e->nargs, e->k)) { put(b, "l%d_%ld", e->nargs + 1, e->k); return 1; }
    DBG("declined: a parameter read where it is not in scope\n"); return 0;
  case E_BIN: {
    Buf x = nbuf(256), y = nbuf(256);
    int ok = 1;
    const Expr *xs2[2] = { e->a, e->b };
    if (par && has_self(e->a) && has_self(e->b) && !par_shares(xs2, 2)) {
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
    const Expr *K, *S; long off;
    if (indexed_pick(e, &K, &S, &off)) {
      put(b, "(((long *)("); if (!emitx(b, pre, S, par, budget - 1)) return 0;
      put(b, "))[("); if (!emitx(b, pre, K, par, budget - 1)) return 0; put(b, ") + %ld])", off); return 1;
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
    if (!e->nargs) { put(b, "(%ldL)", e->k * 2 + 1); return 1; }
    { const Expr *K, *f0, *x0; long off;
      if (e->c && !(par && e->c->op != E_PARAM) && (e->untag || e->rtag - 1 == e->k) && indexed_update(e, &K, &off, &f0, &x0)) {
        int kv = nvar++, ov = nvar++;
        put(b, "({ long v%d = ", kv); if (!emitx(b, pre, K, par, budget - 1)) return 0;
        put(b, "; long *_o = (long *)("); if (!emitx(b, pre, e->c, par, budget - 1)) return 0;
        put(b, "); long v%d = _o[v%d + %ld]; ", ov, kv, off);
        Expr *fx = (Expr *)f0; int sv = fx->var, ss = fx->vscope; fx->var = ov; fx->vscope = fscope;   /* field 0 stands for field K */
        Expr *kx = (Expr *)K; int skv = kx->var, sks = kx->vscope; kx->var = kv; kx->vscope = fscope;
        /* written only if it CHANGED: an update in place hands back the block it was given, and storing that
           pointer again would make the next operation's load of it wait on this store -- every step of a loop
           over the structure in series, where they could overlap */
        put(b, "long _n = ");
        int ok = emit_region(b, pre, x0, par, budget - 1);
        fx->var = sv; fx->vscope = ss; kx->var = skv; kx->vscope = sks;
        if (!ok) return 0;
        if (x0->op == E_CALL || x0->op == E_MATCH || x0->op == E_IF) put(b, "; if (_n != v%d) _o[v%d + %ld] = _n; (long)_o; })", ov, kv, off);
        else put(b, "; _o[v%d + %ld] = _n; (long)_o; })", kv, off);   /* (a plain value: stored without reading the old one) */
        return 1;
      } }
    if (e->c && !(par && e->c->op != E_PARAM)) {      /* REUSE: the block the enclosing match took apart (ownership) */
      /* only what changed is written: the same constructor keeps its tag, a field that IS the old one stays */
      put(b, "({ ");
#define SAMEF(x) (((x)->op == E_FIELD && (x)->a == e->c && (x)->k == i) || (e->ci && !field_live(e->ci, i)))
      for (int i = 0; i < e->nargs; i++) {
        const Expr *a = e->args[i];
        if (SAMEF(a) || a == dp_hole) continue;   /* (the hole of a destination-passing cell: its call writes it) */
        /* `cond ? new : old` (or `cond ? old : new`): the field is written only when it changes */
        if (a->op == E_IF && (SAMEF(a->c) || SAMEF(a->b))) {
          int keep_else = SAMEF(a->c);
          put(b, "long _c%d = ", i); if (!emitx(b, pre, a->a, par, budget - 1)) return 0;
          put(b, "; long _a%d = %s_c%d ? ", i, keep_else ? "" : "!", i);
          if (!emitx(b, pre, keep_else ? a->b : a->c, par, budget - 1)) return 0; put(b, " : 0; ");
          continue;
        }
        put(b, "long _a%d = ", i); if (!emitx(b, pre, a, par, budget - 1)) return 0; put(b, "; ");
      }
      put(b, "long *_o = (long *)("); if (!emitx(b, pre, e->c, par, budget - 1)) return 0; put(b, "); ");
      if (!e->untag && e->rtag - 1 != e->k) put(b, "_o[0] = %ldL; ", e->k);
      for (int i = 0; i < e->nargs; i++) {
        const Expr *a = e->args[i];
        if (SAMEF(a) || a == dp_hole) continue;   /* (the hole of a destination-passing cell: its call writes it) */
        if (a->op == E_IF && (SAMEF(a->c) || SAMEF(a->b))) { put(b, "if (%s_c%d) _o[%d] = _a%d; ", SAMEF(a->c) ? "" : "!", i, i + !e->untag, i); continue; }
        /* (a field a call computed is often the very block it was given, rebuilt in place: see above) */
        if ((e->untag || e->rtag - 1 == e->k) && !bound(a) && (a->op == E_CALL || a->op == E_MATCH || a->op == E_IF))
          put(b, "if (_o[%d] != _a%d) ", i + !e->untag, i);
        put(b, "_o[%d] = _a%d; ", i + !e->untag, i);
      }
#undef SAMEF
      put(b, "(long)_o; })"); return 1;
    }
    if (e->untag) put(b, "({ long *_o = lin_alloc(%d); ", e->nargs);
    else put(b, "({ long *_o = lin_alloc(%d); _o[0] = %ldL; ", e->nargs + 1, e->k);
    for (int i = 0; i < e->nargs; i++) {
      if (e->ci && !field_live(e->ci, i)) continue;   /* (a field nobody reads is not computed) */
      put(b, "_o[%d] = ", i + !e->untag); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; put(b, "; ");
    }
    put(b, "(long)_o; })"); return 1;
  case E_FIELD:
    uses_data = 1;
    put(b, "(((long *)("); if (!emitx(b, pre, e->a, par, budget - 1)) return 0; put(b, "))[%ld])", e->k + !e->untag); return 1;
  case E_MATCH: {
    uses_data = 1;
    /* the scrutinee once, in a local the branches read it by (a reused block is named by it, never recomputed) */
    int sv = nvar++;
    put(b, "({ long v%d = ", sv); if (!emitx(b, pre, e->a, par, budget - 1)) return 0;
    put(b, "; long _s = v%d", sv);
    Expr *sx = (Expr *)e->a; int sx_var = sx->var, sx_scope = sx->vscope;
    if (sx->op != E_PARAM && sx->op != E_CONST) { sx->var = sv; sx->vscope = fscope; }
    if (e->untag) put(b, "; long _t = (_s & 1) ? (_s >> 1) : %dL; (", e->box);
    else put(b, "; long _t = (_s & 1) ? (_s >> 1) : ((long *)_s)[0]; (");
    for (int i = 0; i < e->nargs; i++) {
      if (i < e->nargs - 1) put(b, "_t == %d ? ", i);
      const LinCtor *bc = NULL;
      if (0 && e->freeb && e->freeb[i] && !par && e->ci)   /* (fields are bound where a tail frees: emitx, e->fre) */
        for (long k = 1; (bc = lin_ctor_info(k)); k++) if (bc->dt == e->ci->dt && bc->i == i) break;
      if (bc && bc->k > 0) {
        /* the fields first, then the block back to the allocator, then the branch over the copies */
        int nfx = bc->k; Expr **fx = A(sizeof *fx * (size_t)nfx);
        put(b, "({ ");
        for (int j = 0; j < nfx; j++) {
          Expr *t = mke(E_FIELD, 1); t->a = e->a; t->k = j; t->untag = e->untag; t->ci = bc; fx[j] = hc(t);
          int k = nvar++; put(b, "long v%d = ((long *)_s)[%d]; ", k, j + !e->untag);
          fx[j]->var = k; fx[j]->vscope = fscope;
        }
        tailpos = tp;
        int ok = emit_region(b, pre, e->args[i], par, budget - 1);
        put(b, "; })");
        for (int j = 0; j < nfx; j++) fx[j]->var = -1;
        if (!ok) return 0;
      } else if ((tailpos = tp, !emit_region(b, pre, e->args[i], par, budget - 1))) return 0;
      if (i < e->nargs - 1) put(b, " : ");
    }
    put(b, "); })");
    sx->var = sx_var; sx->vscope = sx_scope;
    return 1;
  }
  case E_FOP:
    put(b, "%s(", FROW[e->k].c);
    for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emitx(b, pre, e->args[i], par, budget - 1)) return 0; }
    put(b, ")"); return 1;
  case E_CALL:
    par = par && e->k == 0;                        /* only the entry function has a parallel version */
    { int calls = 0; for (int i = 0; i < e->nargs; i++) calls += has_self(e->args[i]);
      if (par && calls >= 2 && !e->clone && !par_shares((const Expr **)e->args, e->nargs)) {   /* independent calls among the arguments: at once */
        Buf *nm = calloc((size_t)e->nargs, sizeof *nm);
        for (int i = 0; i < e->nargs; i++) nm[i] = nbuf(32);
        int ok = par_group(b, pre, (const Expr **)e->args, e->nargs, nm, budget);
        if (ok) { put(b, "fp("); for (int i = 0; i < e->nargs; i++) put(b, "%s, ", nm[i].s); put(b, "d + 1); })"); }
        for (int i = 0; i < e->nargs; i++) free(nm[i].s);
        free(nm); return ok;
      } }
    { int dr = !par && e->dropx && e->dropx->nargs == emitting;   /* (see `drops`) */
      if (dr) put(b, "({ long r_ = ");
      if (par) put(b, "fp("); else put(b, "f%ld(", e->k);
      for (int i = 0; i < e->nargs; i++) { if (i) put(b, ", "); if (!emit_arg(b, pre, e, i, par, budget - 1)) return 0; }
      if (!par && !call_fv(b, e->k)) return 0;
      put(b, par ? "%sd + 1)" : ")", e->nargs ? ", " : "");
      if (dr) { uses_data = 1; put(b, "; lin_drop%d(p%ld); r_; })", e->dropfn, e->dropx->k); } }
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
  const Expr *K, *S; long off;
  ho_f = f;
  switch (e->op) {
  case E_IF: if (indexed_pick(e, &K, &S, &off)) return !(ho_info(e) & 4u);
    return !(ho_info(e->a) & 4u) && pm_tail(e->b, f) && pm_tail(e->c, f);
  case E_MATCH: if (ho_info(e->a) & 4u) return 0;
    for (int i = 0; i < e->nargs; i++) if (!pm_tail(e->args[i], f)) return 0;
    return 1;
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
  if (!funs[f].body || funs[f].body->op != E_MATCH || !funs[f].body->untag) return 0;
  const Expr *sc = funs[f].body->a;
  if (sc->op != E_PARAM || sc->nargs != f) return 0;
  pm_k = pm_tf = -1; pm_heavy = pm_holes = 0; ho_f = f; mm_new(MM_SSTR);
  free(fr_memo); fr_memo = calloc((size_t)nfun + 1, 1);
  return pm_tail(funs[f].body, f) && pm_holes > 0 && pm_heavy && pm_k == (int)sc->k && pm_tf >= 0;
}
static int dp_scan(const Expr *e, int f, unsigned char *hd) {
  const Expr *K, *S; long off;
  switch (e->op) {
  case E_IF: if (indexed_pick(e, &K, &S, &off)) return 0; return dp_scan(e->b, f, hd) | dp_scan(e->c, f, hd);
  case E_MATCH: { int r = 0; for (int i = 0; i < e->nargs; i++) r |= dp_scan(e->args[i], f, hd); return r; }
  case E_CTOR:
    { const Expr *K2, *f0, *x0; long off2;
      if (e->nargs && e->c && (e->untag || e->rtag - 1 == e->k) && indexed_update(e, &K2, &off2, &f0, &x0) && x0->op == E_CALL && x0->k == f && !hd[f]) { hd[f] = 1; return 1; } }
    for (int i = 0; i < e->nargs; i++)
      if (e->args[i]->op == E_CALL && e->args[i]->k == f && (!e->ci || field_live(e->ci, i)) && !hd[f]) { hd[f] = 1; return 1; }
    return 0;
  case E_CALL: if (hd[f] && e->k >= 0 && e->k < nfun && !hd[e->k]) { hd[e->k] = 1; return 1; } return 0;
  default: return 0;
  }
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
                 Shape res; Shape **fld; long nctor; void (*release)(void); Shape *psh; int npsh; } Compiled;   /* psh: each runtime argument's shape */   /* kind 5: a data result, read by res/fld */   /* aborted: a data unit's guard fired */   /* strict: the parameters certainly evaluated */
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
  if (esh_data && nesh) { cp->npsh = nesh; cp->psh = malloc(sizeof *cp->psh * (size_t)nesh); memcpy(cp->psh, esh, sizeof *esh * (size_t)nesh); }
  if ((kind == 5 || esh_data) && hnd) {             /* the field shapes the result (and the arguments) are read by */
    cp->release = (void (*)(void))(intptr_t)dlsym(hnd, "lin_fn_release");
    cp->nctor = sh_nctor; cp->fld = calloc((size_t)sh_nctor + 1, sizeof *cp->fld);
    for (long k = 1; k <= sh_nctor; k++) { int nk = lin_ctor_info(k)->k + 1; cp->fld[k] = malloc(sizeof **cp->fld * (size_t)nk); memcpy(cp->fld[k], sh_fld[k], sizeof **cp->fld * (size_t)nk); }
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
typedef struct { int iv, acc, op, ismax; long c; const Expr *g; int up, bnd; } Red;   /* up: counts up to parameter bnd (or to c) */
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
static unsigned char **fld_live; static long fl_n; static int fl_changed;
static long ctor_id(const LinCtor *ci);
static int field_live(const LinCtor *ci, int j) {
  if (!fld_live) return 1;
  long id = ctor_id(ci);
  return !(id > 0 && id <= fl_n && j < ci->k) || fld_live[id][j];
}
static void live_walk(const Expr *e) {
  if (!e || mm_has(MM_SITE, e)) return;
  mm_put(MM_SITE, e, 1);
  if (e->op == E_FIELD && e->ci) { long id = ctor_id(e->ci); if (id > 0 && id <= fl_n && e->k < e->ci->k && !fld_live[id][e->k]) { fld_live[id][e->k] = 1; fl_changed = 1; } }
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
  for (long k = 1; k <= fl_n; k++) { int nk = lin_ctor_info(k)->k + 1; fld_live[k] = A((size_t)nk); memset(fld_live[k], all ? 1 : 0, (size_t)nk); }
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
  long id = red->ismax > 0 ? (long)(1UL << (LIN_INT_BITS - 1)) : red->ismax < 0 ? (long)~(1UL << (LIN_INT_BITS - 1))
          : (red->op == LIN_OP_MUL) ? 1 : (red->op == LIN_OP_BAND) ? -1 : 0;   /* (+)'s identity */
  put(b, "static long g("); plist(b, 1); put(b, ") { return ");
  emitting = 0; fscope++; int ok = emit_region(b, pre, red->g, 0, 4096); put(b, "; }\n");
  put(b, "typedef struct { long p[%d]; long lo, block, r; long *next; } R;\n", arity);
  put(b, "static void *rrun(void *v) { R *q = v; long acc = %ldL;%s\n", id, data ? " LIN_TASK_START((size_t)256 << 20);" : "");
  for (int i = 0; i < arity; i++) put(b, "  long p%d = q->p[%d];\n", i, i);
  put(b, "  for (;;) { long hi = __atomic_fetch_sub(q->next, q->block, __ATOMIC_RELAXED); if (hi <= q->lo) break;\n");
  put(b, "    long lo = hi - q->block; if (lo < q->lo) lo = q->lo;\n    for (long i = hi; i > lo; i--) { p%d = i%s; long x = g(", red->iv, red->up ? " - 1" : "");
  plist(b, 0); put(b, "); acc = "); red_combine(b, red, "x", "acc"); put(b, "; } }\n");
  put(b, "  q->r = acc; return 0; }\n");
  return ok;
}
static void red_run(Buf *b, const Red *red, int data, const char *threads, const char *done) {
  Buf lob = nbuf(32), hib = nbuf(32);
  Buf *mv = red->up ? &lob : &hib, *bd = red->up ? &hib : &lob;   /* the moving end, and the bound */
  put(mv, "p%d", red->iv);
  if (red->bnd >= 0) put(bd, "p%d", red->bnd); else put(bd, "%ldL", red->c);
  const char *lo = lob.s, *hi = hib.s;
  /* a cheap step needs some thousands of iterations to pay for a thread; a step that CALLS (a whole inner loop)
     pays from a few per thread */
  if (has_call(red->g)) put(b, "  if (%s > 1 && %s > %s && %s - %s >= (long)%s * 4) {\n", threads, hi, lo, hi, lo, threads);
  else put(b, "  if (%s > 1 && %s > %s && %s - %s >= 4096) {\n", threads, hi, lo, hi, lo);
  put(b, "    long next = %s; pthread_t t[%s]; R q[%s];%s\n", hi, threads, threads,
      data ? " pthread_attr_t ra; pthread_attr_init(&ra); pthread_attr_setstacksize(&ra, (size_t)256 << 20);" : "");
  put(b, "    for (int k = 0; k < %s; k++) { R r = { {", threads); plist(b, 0);
  put(b, "}, %s, (%s - %s) / ((long)%s * 64) + 1, 0, &next }; q[k] = r; pthread_create(&t[k], %s, rrun, &q[k]); }\n", lo, hi, lo, threads, data ? "&ra" : "0");
  put(b, "    long acc = p%d;\n    for (int k = 0; k < %s; k++) { pthread_join(t[k], 0); acc = ", red->acc, threads);
  red_combine(b, red, "q[k].r", "acc"); put(b, "; }\n    %s }\n", done);
  free(lob.s); free(hib.s);
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
/* OWNERSHIP, AND REUSE IN PLACE.  The unit's DAG shows sharing exactly (hash-consing: one value, one node -- the
   C image of the net's fans), so whether a block has ONE owner is a static question.  A value is FRESH if it
   was just built (a constructor, or a call returning fresh data); a data parameter is UNIQUE if every call
   passes it something fresh that nothing else on that path uses, and the function itself uses it at most once
   on any path (reading its fields does not count).  Then a match on a unique parameter can build the branch's
   constructor of the same size IN THE BLOCK IT JUST TOOK APART -- its fields are all computed before anything
   is written -- which is what a functional insert into a tree costs in C: the path is updated, not copied. */
static const Expr *occ_x; static int occ_reads;   /* occ_reads: a match taking occ_x apart only reads it */
static unsigned occ_r(const Expr *e);
static unsigned occ_tail(const Expr *e) {            /* e as the VALUE of a match on occ_x: occ_x itself there is no further move */
  if (e == occ_x) return 0;
  if (e->op == E_IF) { unsigned b = occ_tail(e->b), c = occ_tail(e->c); return occ_r(e->a) + (b > c ? b : c); }
  if (e->op == E_MATCH && e->a != occ_x) { unsigned m = 0; for (int i = 0; i < e->nargs; i++) { unsigned x = occ_tail(e->args[i]); if (x > m) m = x; } return occ_r(e->a) + m; }
  return occ_r(e);
}
static unsigned occ_r(const Expr *e) {               /* how often occ_x is MOVED on the worst path through e */
  if (e == occ_x) return 1;
  /* a DAG node is ONE evaluation (the emitter binds a value used twice): what moves inside it, moves once --
     the second reference to it moves nothing more */
  if (mm_has(MM_OCC, e)) return 0;
  unsigned r = 0;
  switch (e->op) {
  case E_FIELD: r = 0; break;   /* reading a field consumes nothing -- and its base is an enclosing match's scrutinee,
                                    evaluated (and counted) once, there */
  case E_IF: { unsigned b = occ_r(e->b), c = occ_r(e->c); r = occ_r(e->a) + (b > c ? b : c); break; }
  case E_MATCH: {
    /* (a match that takes x apart and, on some path, hands x on whole as its value moved it ONCE on that path:
       the block was not rebuilt there, it went on) */
    int own = !occ_reads && e->a == occ_x; unsigned m = 0;
    for (int i = 0; i < e->nargs; i++) { unsigned x = own ? occ_tail(e->args[i]) : occ_r(e->args[i]); if (x > m) m = x; }
    r = (occ_reads && e->a == occ_x ? 0 : occ_r(e->a)) + m; break; }
  case E_BIN: r = occ_r(e->a) + occ_r(e->b); break;
  case E_CTOR: for (int i = 0; i < e->nargs; i++) if (!e->ci || field_live(e->ci, i)) r += occ_r(e->args[i]); break;   /* (a field nobody reads is not computed: nothing moves into it) */
  case E_CALL: case E_FOP: for (int i = 0; i < e->nargs; i++) r += occ_r(e->args[i]); break;
  default: break;
  }
  if (r > 2) r = 2;
  return mm_put(MM_OCC, e, r);
}
/* PATH-SENSITIVE: the most moves of occ_x on a path that evaluates node `through` (-1: no path does). */
static const Expr *ot_node;
static const Expr **ot_ev; static int ot_nev, ot_cev;   /* values already evaluated on this path (scrutinees) */
static void ot_fresh(void) { mm_new(MM_OCC); for (int i = 0; i < ot_nev; i++) mm_put(MM_OCC, ot_ev[i], 0); }
static int ot_r_dbg(const Expr *e);
static int ot_r(const Expr *e) {
  for (int i = 0; i < ot_nev; i++) if (ot_ev[i] == e) return -1;   /* (evaluated already on this path) */
  if (e == ot_node) {                                /* the node itself: what it moves */
    int r = 0; occ_reads = 0;
    for (int i = 0; i < e->nargs && e->args; i++) { ot_fresh(); r += (int)occ_r(e->args[i]); }
    if (e->a) { ot_fresh(); r += (int)occ_r(e->a); }
    return r;
  }
  if (e->op == E_FIELD) return -1;                   /* (its base was evaluated at its match: a field read evaluates nothing) */
  for (int i = 0; i < ot_nev; i++) if (ot_ev[i] == e) return -1;   /* (evaluated already: a second reference is the same value) */
  if (!contains(e, ot_node, 0)) return -1;
  ot_fresh();
  switch (e->op) {
  case E_IF: case E_MATCH: {
    const Expr *sc = e->a; int best = -1;
    int ts = ot_r_dbg(sc);
    ot_fresh(); int sa = (int)occ_r(sc);
    if (ot_nev >= ot_cev) ot_ev = realloc(ot_ev, sizeof *ot_ev * (size_t)(ot_cev = ot_cev ? ot_cev * 2 : 16));
    ot_ev[ot_nev++] = sc;                            /* in the branches, the scrutinee is a value in hand */
    unsigned bmax = 0;
    int nb = e->op == E_IF ? 2 : e->nargs;
    for (int i = 0; i < nb; i++) { const Expr *br = e->op == E_IF ? (i ? e->c : e->b) : e->args[i]; ot_fresh(); unsigned u = occ_r(br); if (u > bmax) bmax = u; }
    if (ts >= 0) best = ts + (int)bmax;
    for (int i = 0; i < nb; i++) { const Expr *br = e->op == E_IF ? (i ? e->c : e->b) : e->args[i]; int t = ot_r_dbg(br); if (t >= 0 && sa + t > best) best = sa + t; }
    ot_nev--;
    return best;
  }
  default: {
    int cap = 2 + e->nargs, nk = 0;
    const Expr **kid = A(sizeof *kid * (size_t)cap); int *any = A(sizeof *any * (size_t)cap);
    if (e->a) kid[nk++] = e->a;
    if (e->b) kid[nk++] = e->b;
    for (int i = 0; i < e->nargs && e->args; i++) kid[nk++] = e->args[i];
    int best = -1;
    for (int i = 0; i < nk; i++) { ot_fresh(); any[i] = (int)occ_r(kid[i]); }
    for (int i = 0; i < nk; i++) {
      int t = ot_r_dbg(kid[i]); if (t < 0) continue;
      int sum = t; for (int j = 0; j < nk; j++) if (j != i) sum += any[j];
      if (sum > best) best = sum;
    }
    return best;
  }
  }
}
static int contains(const Expr *e, const Expr *x, int depth);
static int ot_depth;
static int ot_r_dbg(const Expr *e) {
  ot_depth++; int r = ot_r(e); ot_depth--;
  if (dbg > 3) { static const char *nm[] = { "CONST","PARAM","BIN","IF","CALL","FOP","CTOR","MATCH","FIELD" }; DBG("%*s[ot %s k%ld id %d -> %d]\n", ot_depth, "", nm[e->op], e->k, e->id, r); }
  return r;
}
static unsigned occ_through(const Expr *in, const Expr *x, const Expr *node) {
  occ_x = x; occ_reads = 0; ot_node = node; ot_nev = 0;
  int r = ot_r_dbg(in);
  return r < 0 ? 0 : (unsigned)r;
}
static unsigned occ(const Expr *in, const Expr *x) { occ_x = x; occ_reads = 0; mm_new(MM_OCC); return occ_r(in); }
/* the moves of x other than being taken apart: whether a STORED value is shared (a match that consumes it is
   decided separately, counting itself: mark_reuse) */
static unsigned occ_stored(const Expr *in, const Expr *x) { occ_x = x; occ_reads = 1; mm_new(MM_OCC); unsigned r = occ_r(in); occ_reads = 0; return r; }
static unsigned char **uparam, *ufresh;
/* A FIELD IS OWNED only if every constructor that writes it is given something fresh that nothing else holds:
   `(node t t)` stores ONE block in two fields, and taking either apart in place would corrupt the other. */
static unsigned char **fown; static long fown_n;
static long ctor_id(const LinCtor *ci);
static int field_owned(const Expr *e) {
  long id = e->ci ? ctor_id(e->ci) : 0;
  return id > 0 && id <= fown_n && e->k < e->ci->k && fown[id][e->k];
}
static int uniq_r(const Expr *e) {
  if (mm_has(MM_UNIQ, e)) return (int)mm_val[MM_UNIQ][e->id];
  int r = 0;
  switch (e->op) {
  case E_CTOR: case E_CONST: r = 1; break;
  case E_CALL: r = ufresh[e->k]; break;
  case E_PARAM: r = e->nargs >= 0 && e->nargs < nfun && uparam[e->nargs][e->k]; break;
  case E_IF: r = uniq_r(e->b) && uniq_r(e->c); break;
  case E_MATCH: r = 1; for (int i = 0; i < e->nargs; i++) r = r && uniq_r(e->args[i]); break;
  case E_FIELD: r = uniq_r(e->a) && field_owned(e); break;
  default: break;
  }
  return (int)mm_put(MM_UNIQ, e, (unsigned)r);
}
static int uniq(const Expr *e) { return uniq_r(e); }
static int uq_changed;
/* A FLAT datatype: one constructor with fields, every field a number or a boolean.  Its value is one block that
   points at nothing, so a copy of the block is a value nothing else holds.  Its size in words, or 0. */
static int flat_words(const char *dt) {
  if (!dt) return 0;
  int box = -1; if (dt_boxed(dt, &box) != 1) return 0;
  const LinCtor *c; long id = 0;
  for (long k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt && c->i == box) { id = k; break; }
  if (!id || id > sh_nctor || !sh_fld || !sh_fld[id]) return 0;
  for (int j = 0; j < c->k; j++) if (sh_fld[id][j].k != 1 && sh_fld[id][j].k != 3) return 0;
  return c->k;
}
static Shape shape_of(const Expr *e);
static int clone_words(const Expr *a) { return flat_words(shape_of(a).dt); }
/* does f, calling itself, give parameter i a value it BUILT (an accumulator), rather than pass it along? */
static int accumulates(const Expr *e, int f, int i) {
  if (!e || mm_has(MM_SITE, e)) return 0;
  mm_put(MM_SITE, e, 1);
  if (e->op == E_PARAM || e->op == E_CONST) return 0;
  if (e->op == E_CALL && e->k == f && i < e->nargs && e->args[i]->op != E_PARAM && e->args[i]->op != E_FIELD) return 1;
  if (accumulates(e->a, f, i) || accumulates(e->b, f, i) || (e->op != E_CTOR && accumulates(e->c, f, i))) return 1;
  for (int j = 0; j < e->nargs && e->args; j++) if (accumulates(e->args[j], f, i)) return 1;
  return 0;
}
/* how many places name each value (over the whole unit): one named once is given to its one call once, on every
   path -- no need to walk the paths for it */
static unsigned *nrefs; static int nrefs_cap;
static void count_refs(const Expr *e) {
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
#define REF(x) do { const Expr *x_ = (x); if (x_) { if (x_->id >= nrefs_cap) { int o = nrefs_cap; nrefs_cap = x_->id * 2 + 64; nrefs = realloc(nrefs, sizeof *nrefs * (size_t)nrefs_cap); memset(nrefs + o, 0, sizeof *nrefs * (size_t)(nrefs_cap - o)); } nrefs[x_->id]++; count_refs(x_); } } while (0)
  REF(e->a); REF(e->b); if (e->op != E_CTOR) REF(e->c);
  for (int i = 0; i < e->nargs && e->args; i++) REF(e->args[i]);
#undef REF
}
static int cur_own = -1;   /* the function whose body uniq_calls is in */
static void uniq_calls(const Expr *e, const Expr *body) {   /* demote a callee's parameter given something shared */
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_CALL)
    for (int i = 0; i < e->nargs; i++) {
      const Expr *a = e->args[i];
      if (!uparam[e->k][i]) continue;
      if (a->id < nrefs_cap && nrefs[a->id] <= 1 && uniq(a)) continue;   /* (named once: moved once) */
      int imm = a->op == E_CONST || (a->op == E_CTOR && !a->nargs);   /* (an immediate is no block) */
      int ok = uniq(a) && (imm || occ_through(body, a, e) <= 1);   /* (on the paths through this call: one value given twice -- a field, a parameter, or a block the expression shares -- is not unique) */
      /* A flat value given to an ACCUMULATOR is given as a copy: `(sfoldl step b xs)` starts from a `b` someone
         else holds, and every step after it builds a new one -- with a copy to start from, each step rebuilds
         in the block of the one before. */
      if (!ok && uparam[e->k][i] && i < CLONE_BITS && (a->op == E_FIELD || a->op == E_PARAM) && cur_own != e->k) {
        Shape sa = shape_of(a);
        if (sa.k == 5 && flat_words(sa.dt) > 0 && (mm_new(MM_SITE), accumulates(funs[e->k].body, (int)e->k, i))) {
          if (!((e->clone >> i) & 1u) && dbg > 1) DBG("[f%ld's parameter %d is given a copy]\n", e->k, i);
          ((Expr *)e)->clone |= 1u << i; continue;
        }
      }
      if (!ok && uparam[e->k][i]) { if (dbg > 1) DBG("[not unique: f%ld's parameter %d: arg op %d uniq %d through %u]\n", e->k, i, a->op, uniq(a), imm ? 0 : occ_through(body, a, e)); uparam[e->k][i] = 0; uq_changed = 1; }
    }
  if (e->a) uniq_calls(e->a, body);
  if (e->b) uniq_calls(e->b, body);
  if (e->c) uniq_calls(e->c, body);
  for (int i = 0; i < e->nargs && e->args; i++) uniq_calls(e->args[i], body);
}
static Shape *sh_memo; static unsigned *sh_gen, sh_g; static int sh_cap;
static void own_ctors(const Expr *e, const Expr *body) {   /* demote a field some constructor writes shared */
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_CTOR && e->ci) {
    long id = ctor_id(e->ci);
    for (int j = 0; id > 0 && id <= fown_n && j < e->nargs && j < e->ci->k; j++) {
      const Expr *a = e->args[j];
      if (!fown[id][j] || a->op == E_CONST || (a->op == E_CTOR && !a->nargs)) continue;   /* (an immediate is no block) */
      if (sh_cap > a->id && sh_gen[a->id] == sh_g && sh_memo[a->id].k != 5) continue;   /* (nor a number: only data is owned) */
      if (!uniq(a) || occ_stored(body, a) > 1) { if (dbg > 1) DBG("[disown %s.%d: arg op %d k %ld uniq %d occ %u body id %d]\n", e->ci->name, j, a->op, a->k, uniq(a), occ(body, a), body->id); fown[id][j] = 0; uq_changed = 1; }
    }
  }
  if (e->a) own_ctors(e->a, body);
  if (e->b) own_ctors(e->b, body);
  if (e->c) own_ctors(e->c, body);
  for (int i = 0; i < e->nargs && e->args; i++) own_ctors(e->args[i], body);
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
/* EVERY PATH of a branch that consumes a block settles it: a tail constructor of its size is built IN it; any
   other tail (through conditionals and matches, whose own tails are tails) FREES it first, so what that tail
   allocates can be the block just released.  Each marked node is a private copy: the mark is this place's. */
/* ...or as the VALUE of a tail: a path that hands the block on whole neither rebuilds in it nor frees it */
static int tail_reads(const Expr *e, const Expr *x) {
  if (e == x) return 1;
  if (e->op == E_IF) return only_reads(e->a, x) && tail_reads(e->b, x) && tail_reads(e->c, x);
  if (e->op == E_MATCH && e->a != x) {
    if (!only_reads(e->a, x)) return 0;
    for (int i = 0; i < e->nargs; i++) if (!tail_reads(e->args[i], x)) return 0;
    return 1;
  }
  return only_reads(e, x);
}
static void ctor_slot_tail(Expr **slot, Expr *s, int nf, int branch, int words) {
  Expr *e = *slot;
  if (e == s) return;                                /* (the block itself, handed on) */
  Expr *c2 = A(sizeof *c2); *c2 = *e; c2->id = eid++; c2->var = -1; *slot = c2;
  if (e->op == E_CTOR && e->nargs == nf && nf > 0 && !e->c) { c2->c = s; c2->rtag = branch + 1; return; }
  if (e->op == E_IF) { ctor_slot_tail(&c2->b, s, nf, branch, words); ctor_slot_tail(&c2->c, s, nf, branch, words); return; }
  if (e->op == E_MATCH) {
    c2->args = A(sizeof(Expr *) * (size_t)(e->nargs ? e->nargs : 1)); memcpy(c2->args, e->args, sizeof(Expr *) * (size_t)e->nargs);
    if (e->freeb) { c2->freeb = A((size_t)e->nargs); memcpy(c2->freeb, e->freeb, (size_t)e->nargs); }
    for (int i = 0; i < e->nargs; i++) ctor_slot_tail(&c2->args[i], s, nf, branch, words);
    return;
  }
  c2->fre = s; c2->fren = words;
}
/* A FIELD's block may be consumed only where its parent's is: the parent still points at it.  So every match on
   the parent that has this match in a branch must, in that branch, only READ the parent (never pass it on or store
   it whole) -- then nothing that survives the branch reaches the field's block but the field itself. */
static int fc_ok;
static void fc_walk(const Expr *e, const Expr *X, const Expr *M) {
  if (!e || !fc_ok || mm_has(MM_SITE, e)) return;
  mm_put(MM_SITE, e, 1);
  if (e->op == E_MATCH && e->a == X)
    for (int i = 0; i < e->nargs && fc_ok; i++) if (contains(e->args[i], M, 0) && !only_reads(e->args[i], X)) fc_ok = 0;
  if (e->a) fc_walk(e->a, X, M);
  if (e->b) fc_walk(e->b, X, M);
  if (e->c && e->op != E_CTOR) fc_walk(e->c, X, M);
  for (int i = 0; i < e->nargs && e->args; i++) fc_walk(e->args[i], X, M);
}
static int field_consumable(const Expr *body, const Expr *M) {
  for (const Expr *x = M->a; x->op == E_FIELD; x = x->a) {   /* each ancestor up to the value the chain reads from */
    fc_ok = 1; mm_new(MM_SITE); fc_walk(body, x->a, M);
    if (!fc_ok) return 0;
  }
  return 1;
}
static int reuses(const Expr *e, const Expr *s) {   /* does a constructor in e rebuild in s's block? */
  if (!e) return 0;
  if (e->op == E_CTOR && e->c == s) return 1;
  if (e->op == E_IF) return reuses(e->b, s) || reuses(e->c, s);
  return 0;
}
static void mark_reuse(Expr *e, int f) {
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  /* a match on a value it CONSUMES: unique (a unique parameter, an owned field of one, a fresh call's result), and
     moved nowhere else on any path of the function */
  int owned_scrut = e->op == E_MATCH && e->ci &&
    (e->a->op == E_PARAM ? (e->a->nargs == f && uparam[f][e->a->k])
                         : ((e->a->op == E_FIELD || e->a->op == E_CALL) && (mm_new(MM_UNIQ), uniq(e->a)) && occ(funs[f].body, e->a) <= 1
                            && (e->a->op != E_FIELD || field_consumable(funs[f].body, e))));
  if (owned_scrut) {
    for (int i = 0; i < e->nargs; i++) {
      const LinCtor *c2 = NULL; int nf = -1;
      for (long k = 1; (c2 = lin_ctor_info(k)); k++) if (c2->i == i && e->ci && c2->dt == e->ci->dt) { nf = c2->k; break; }
      if (nf > 0 && tail_reads(e->args[i], e->a)) {
        ctor_slot_tail(&e->args[i], e->a, nf, i, nf + !e->untag);
        if (!e->freeb) e->freeb = A((size_t)e->nargs);
        e->freeb[i] = 1;                               /* (its fields are read into locals first: emitx, E_MATCH) */
      }
    }
  }
  if (e->a) mark_reuse(e->a, f);
  if (e->b) mark_reuse(e->b, f);
  if (e->c && e->op != E_CTOR) mark_reuse(e->c, f);
  for (int i = 0; i < e->nargs && e->args; i++) mark_reuse(e->args[i], f);
}
static void captured(const Expr *e, int f) {
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_PARAM) { if (e->nargs >= 0 && e->nargs < nfun && e->nargs != f && e->k >= 0 && e->k < funs[e->nargs].arity) uparam[e->nargs][e->k] = 0; return; }
  captured(e->a, f); captured(e->b, f); if (e->op != E_CTOR) captured(e->c, f);
  for (int i = 0; i < e->nargs && e->args; i++) captured(e->args[i], f);
}
/* THE ERASER, IN COMPILED CODE.  In the net a value nothing uses is erased where it stops being used.  A unit
   had two ways to give a block back -- rebuild in it, or free it where a match took it apart -- and so a value
   that was only READ and then abandoned stayed until the unit returned: `(run (sub n 1) (step bs))` kept every
   `bs` it had ever stepped from.  A parameter is now DROPPED after the call that last uses it, when
     - the function owns it (every caller hands over something fresh),
     - on the path through that call it appears nowhere but as the call's arguments,
     - the callee does not take it apart itself (then it would already be gone), and
     - the call's result holds none of it: fresh, and every field of its datatypes owned.
   Dropping walks what the value owns and frees each block. */
static const char **drop_dt; static int ndrop, drop_cap;
static int drop_fn(const char *dt) {
  for (int i = 0; i < ndrop; i++) if (drop_dt[i] == dt) return i;
  if (ndrop >= drop_cap) drop_dt = realloc(drop_dt, sizeof *drop_dt * (size_t)(drop_cap = drop_cap ? drop_cap * 2 : 8));
  drop_dt[ndrop] = dt; return ndrop++;
}
static int deep_owned(const char *dt, int depth) {   /* every data field of dt's values, all the way down, is owned */
  if (depth > 8 || !dt) return 0;
  const LinCtor *c;
  for (long k = 1; (c = lin_ctor_info(k)); k++) if (c->dt == dt)
    for (int j = 0; j < c->k; j++) {
      if (!field_live(c, j) || k > sh_nctor) continue;
      Shape f = sh_fld[k][j];
      if (f.k == 1 || f.k == 3) continue;
      if (f.k != 5 || k > fown_n || !fown[k][j]) return 0;
      if (f.dt != dt && !deep_owned(f.dt, depth + 1)) return 0;
    }
  return 1;
}
static unsigned char **uown;
static void own_sites(const Expr *e) {               /* a parameter is OWNED if every call hands it a fresh value */
  if (!e || mm_has(MM_NUM, e)) return;
  mm_put(MM_NUM, e, 1);
  if (e->op == E_PARAM || e->op == E_CONST) return;
  if (e->op == E_CALL && e->k >= 0 && e->k < nfun)
    for (int i = 0; i < e->nargs && i < funs[e->k].arity; i++) {
      const Expr *a = e->args[i];
      /* fresh: something built, or computed by what builds (a conditional of such); or the function's own
         parameter handed back to itself, in its place -- what it owned, it still owns */
      int self = a->op == E_PARAM && a->nargs == (int)e->k && a->k == i;
      if (!self && !(a->op != E_PARAM && a->op != E_FIELD && a->op != E_CONST && uniq(a))) uown[e->k][i] = 0;
    }
  own_sites(e->a); own_sites(e->b); if (e->op != E_CTOR) own_sites(e->c);
  for (int i = 0; i < e->nargs && e->args; i++) own_sites(e->args[i]);
}
/* in e, is p named only as a direct argument of ONE call (returned in *call)? 1 yes, 0 no; *call stays NULL if p is not named */
static int drop_only(const Expr *e, const Expr *p, const Expr **call) {
  if (!e || e == p) return 0;
  if (!contains(e, p, 0)) return 1;
  if (e->op == E_CALL) {
    int direct = 0;
    for (int i = 0; i < e->nargs; i++) { if (e->args[i] == p) direct = 1; else if (contains(e->args[i], p, 0)) { direct = -1; break; } }
    if (direct == 1) { if (*call && *call != e) return 0; *call = e; return 1; }
    if (direct == 0) return 1;
  }
  if (e->a && !drop_only(e->a, p, call)) return 0;
  if (e->b && !drop_only(e->b, p, call)) return 0;
  if (e->c && e->op != E_CTOR && !drop_only(e->c, p, call)) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!drop_only(e->args[i], p, call)) return 0;
  return 1;
}
static int contains_dropx(const Expr *e, const Expr *p) {
  if (!e || e->op == E_PARAM || e->op == E_CONST) return 0;
  if (e->dropx == p) return 1;
  if (contains_dropx(e->a, p) || contains_dropx(e->b, p) || (e->op != E_CTOR && contains_dropx(e->c, p))) return 1;
  for (int i = 0; i < e->nargs && e->args; i++) if (contains_dropx(e->args[i], p)) return 1;
  return 0;
}
static void drop_tails(Expr *e, int g, int k) {      /* each path of g's body: p handed on whole, unnamed, or lent to one call */
  const Expr *p = funs[g].pnode[k];
  if (e == p || !contains(e, p, 0)) return;
  if (e->op == E_IF && !contains(e->a, p, 0)) { drop_tails(e->b, g, k); drop_tails(e->c, g, k); return; }
  const Expr *call = NULL;
  if (!drop_only(e, p, &call) || !call || call->dropx) return;
  int h = (int)call->k;
  for (int i = 0; i < call->nargs; i++) if (call->args[i] == p && (i >= funs[h].arity || uparam[h][i])) return;   /* (the callee takes it apart) */
  if (!ufresh[h]) return;
  Shape rs = shape_of(call), ps = shape_of(p);
  if (ps.k != 5 || !ps.dt) return;
  if (!(rs.k == 1 || rs.k == 3 || (rs.k == 5 && rs.dt && deep_owned(rs.dt, 0)))) return;
  ((Expr *)call)->dropx = p; ((Expr *)call)->dropfn = drop_fn(ps.dt);
  if (dbg > 1) DBG("[f%d's parameter %d is dropped after its call of f%d]\n", g, k, h);
}
/* ...and a parameter only LENT on the way to a path's end -- to calls that read it and hand back nothing of it
   (`(digits ... (big_mul_small nu k) ...)` lends `nu` twice, and keeps neither) -- is dropped at that end: before
   the tail call, its arguments evaluated, or after the value a path ends with. */
static int fun_reads(int h);
static int borrows(const Expr *call, int i) {        /* does this call only read its argument i, and keep none of it? */
  int h = (int)call->k;
  if (h < 0 || h >= nfun || (i < funs[h].arity && uparam[h][i]) || !ufresh[h]) return 0;
  if (i < funs[h].arity && uown[h][i]) return 0;     /* (a callee that owns the parameter may free it: handed over, not lent) */
  if (fun_reads(h)) return 0;                        /* (it reads the parameters of the function the drop is in) */
  Shape rs = shape_of(call);
  return rs.k == 1 || rs.k == 3 || (rs.k == 5 && rs.dt && deep_owned(rs.dt, 0));
}
static int lent_only(const Expr *e, const Expr *p, unsigned char *seen) {   /* p in e only as a lent argument */
  if (!e || e == p) return e != p;
  if (e->op == E_PARAM || e->op == E_CONST || seen[e->id]) return 1;
  seen[e->id] = 1;
  if (!contains(e, p, 0)) return 1;
  if (e->op == E_CALL) {
    if (fun_reads((int)e->k)) return 0;
    for (int i = 0; i < e->nargs; i++) {
      if (e->args[i] == p) { if (!borrows(e, i)) return 0; }
      else if (!lent_only(e->args[i], p, seen)) return 0;
    }
    return 1;
  }
  if (!lent_only(e->a, p, seen) || !lent_only(e->b, p, seen) || (e->op != E_CTOR && !lent_only(e->c, p, seen))) return 0;
  for (int i = 0; i < e->nargs && e->args; i++) if (!lent_only(e->args[i], p, seen)) return 0;
  return 1;
}
static int lent(const Expr *e, const Expr *p) { unsigned char *seen = calloc((size_t)eid + 1, 1); int r = lent_only(e, p, seen); free(seen); return r; }
static void drop_at(Expr **slot, const Expr *p, int fn) {   /* this path's end, as a node of its own, drops p */
  Expr *c = A(sizeof *c); *c = **slot; c->id = eid++; c->var = -1;
  struct Drop *d = A(sizeof *d); d->p = p; d->fn = fn; d->next = c->drops; c->drops = d;
  *slot = c;
}
static void drop_paths(Expr **slot, const Expr *p, int fn, int seen) {
  Expr *e = *slot;
  if (e == p) return;                                /* (handed on whole) */
  if ((e->op == E_IF && !indexed_pick(e, &(const Expr *){0}, &(const Expr *){0}, &(long){0})) || (e->op == E_MATCH && e->a != p)) {
    const Expr *c = e->a;
    if (!lent(c, p)) return;
    Expr *c2 = A(sizeof *c2); *c2 = *e; c2->id = eid++; c2->var = -1; *slot = c2;
    int s2 = seen || contains(c, p, 0);
    if (e->op == E_IF) { drop_paths(&c2->b, p, fn, s2); drop_paths(&c2->c, p, fn, s2); return; }
    c2->args = A(sizeof(Expr *) * (size_t)(e->nargs ? e->nargs : 1)); memcpy(c2->args, e->args, sizeof(Expr *) * (size_t)e->nargs);
    for (int i = 0; i < e->nargs; i++) drop_paths(&c2->args[i], p, fn, s2);
    return;
  }
  if (e->op == E_MATCH) return;                      /* (p taken apart: what becomes of it is the match's business) */
  if (e->op == E_CALL) { if (fun_reads((int)e->k)) return; for (int i = 0; i < e->nargs; i++) if (e->args[i] == p) return; }
  if (!lent(e, p)) return;
  if (seen || contains(e, p, 0)) drop_at(slot, p, fn);
}
static void drops(Expr *entry) {
  ndrop = 0;
  uown = A(sizeof *uown * (size_t)(nfun ? nfun : 1));
  for (int i = 0; i < nfun; i++) { int a = funs[i].arity ? funs[i].arity : 1; uown[i] = A((size_t)a); memset(uown[i], 1, (size_t)a); }
  mm_new(MM_UNIQ); mm_new(MM_NUM);
  for (int i = 0; i < nfun; i++) own_sites(funs[i].body);
  own_sites(entry);
  for (int g = 0; g < nfun; g++) for (int k = 0; k < funs[g].arity; k++)
    if (uown[g][k] && funs[g].pnode && funs[g].pnode[k] && funs[g].body) drop_tails(funs[g].body, g, k);
  for (int g = 0; g < nfun; g++) {
    ho_f = g; free(fr_memo); fr_memo = calloc((size_t)nfun + 1, 1);   /* (fun_reads: of g's parameters) */
    for (int k = 0; k < funs[g].arity; k++) {
      const Expr *p = funs[g].pnode ? funs[g].pnode[k] : NULL;
      if (dbg > 2 && p) DBG("[drop? f%d.%d own %d shape %d]\n", g, k, uown[g][k], shape_of(p).k);
      if (!p || !uown[g][k] || !funs[g].body) continue;
      Shape ps = shape_of(p); if (ps.k != 5 || !ps.dt) continue;
      if (contains_dropx(funs[g].body, p)) continue;   /* (the single-call drop above already has it) */
      drop_paths(&funs[g].body, p, drop_fn(ps.dt), 0);
      if (dbg > 1) DBG("[f%d's parameter %d is dropped where its paths end]\n", g, k);
    }
  }
}
static void ownership(Expr *entry) {
  uparam = A(sizeof *uparam * (size_t)nfun); ufresh = A((size_t)nfun);
  for (int i = 0; i < nfun; i++) { int a = funs[i].arity ? funs[i].arity : 1; uparam[i] = A((size_t)a); memset(uparam[i], 1, (size_t)a); ufresh[i] = 1; }
  fown_n = 0; while (lin_ctor_info(fown_n + 1)) fown_n++;
  fown = A(sizeof *fown * (size_t)(fown_n + 1));
  for (long k = 1; k <= fown_n; k++) { int nk = lin_ctor_info(k)->k + 1; fown[k] = A((size_t)nk); memset(fown[k], 1, (size_t)nk); }
  /* a parameter an INNER function reads (a captured variable) is held by that function for as long as it runs --
     through every step of its loop -- so neither the function it belongs to nor the one reading it may take it
     apart or rebuild in it */
  for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); captured(funs[i].body, i); }
  if (nrefs_cap) memset(nrefs, 0, sizeof *nrefs * (size_t)nrefs_cap);
  mm_new(MM_NUM); for (int i = 0; i < nfun; i++) count_refs(funs[i].body);
  count_refs(entry);
  for (int round = 0; round <= nfun * 64 + 64 + fown_n; round++) {
    uq_changed = 0;
    mm_new(MM_UNIQ);
    for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); own_ctors(funs[i].body, funs[i].body); }
    mm_new(MM_NUM); own_ctors(entry, entry);
    mm_new(MM_UNIQ);
    for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); cur_own = i; uniq_calls(funs[i].body, funs[i].body); }
    mm_new(MM_NUM); cur_own = -1; uniq_calls(entry, entry);
    for (int i = 0; i < nfun; i++) for (int k = 0; k < funs[i].arity; k++)
      if (uparam[i][k] && funs[i].pnode && funs[i].pnode[k] && occ(funs[i].body, funs[i].pnode[k]) > 1) { uparam[i][k] = 0; uq_changed = 1; }
    mm_new(MM_UNIQ);
    for (int i = 0; i < nfun; i++) { int f = uniq(funs[i].body); if (ufresh[i] && !f) { ufresh[i] = 0; uq_changed = 1; } }
    if (!uq_changed) break;
  }
  drops(entry);
  for (int i = 0; i < nfun; i++) { mm_new(MM_NUM); mark_reuse(funs[i].body, i); }
  if (dbg > 1) {
    for (int i = 0; i < nfun; i++) { DBG("[own f%d fresh %d:", i, ufresh[i]); for (int k = 0; k < funs[i].arity; k++) fprintf(stderr, " %d", uparam[i][k]); fprintf(stderr, "]\n"); }
    for (long k = 1; k <= fown_n; k++) { const LinCtor *c = lin_ctor_info(k); if (c->k == 0) continue; DBG("[own %s:", c->name); for (int j = 0; j < c->k; j++) fprintf(stderr, " %d", fown[k][j]); fprintf(stderr, "]\n"); }
  }
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
  /* two datatypes in one field: a polymorphic constructor (a Seq of pieces and a Seq of ranges) used at two
     types.  Still a block of SOME datatype, which is all a match needs -- it reads the layout its own
     constructors state; only reading such a value in or out needs to know which */
  if (a.k == 5 && b.k == 5) return (Shape){ 5, NULL };
  return (Shape){ 9, NULL };
}
static int sh_eq(Shape a, Shape b) { return a.k == b.k && a.dt == b.dt; }
static Shape **sh_par, *sh_fun; static unsigned char *sh_built; static int sh_changed, sh_bad;
static long ctor_id(const LinCtor *ci) { for (long k = 1; lin_ctor_info(k); k++) if (lin_ctor_info(k) == ci) return k; return 0; }
static void sh_upd(Shape *slot, Shape v) { Shape j = sh_join(*slot, v); if (!sh_eq(j, *slot)) { *slot = j; sh_changed = 1; } }
static unsigned char *sh_fneed;                     /* a function whose result is needed as a number (once each) */
static void sh_need_num(const Expr *x) {
  if (x->op == E_IF) { sh_need_num(x->b); sh_need_num(x->c); return; }   /* (what the value may be, everywhere) */
  if (x->op == E_CALL && sh_fneed && x->k >= 0 && x->k < nfun) {       /* ...and what a call returns */
    if (!sh_fneed[x->k]) { sh_fneed[x->k] = 1; sh_changed = 1; sh_need_num(funs[x->k].body); }
    return;
  }
  if (x->op == E_MATCH) { for (int i = 0; i < x->nargs; i++) if (!(x->args[i]->op == E_CONST && x->args[i]->box)) sh_need_num(x->args[i]); return; }
  if (x->op == E_FIELD && x->ci) { long id = ctor_id(x->ci); if (id > 0 && id <= sh_nctor && x->k < x->ci->k) sh_upd(&sh_fld[id][x->k], (Shape){ 1, NULL }); }
  else if (x->op == E_PARAM && x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], (Shape){ 1, NULL });
  else if (x->op == E_PARAM && x->nargs >= 0 && x->nargs < nfun) sh_upd(&sh_par[x->nargs][x->k], (Shape){ 1, NULL });
}
static Shape shape_of(const Expr *e) {
  if (e->id < sh_cap && sh_gen[e->id] == sh_g) return sh_memo[e->id];
  Shape r = { 0, NULL };
  switch (e->op) {
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
    if (e->a->op == E_PARAM && e->ci) {             /* (a parameter taken apart: its use says what it is) */
      if (e->a->nargs < 0 && e->a->k < nesh) sh_upd(&esh[e->a->k], (Shape){ 5, e->ci->dt });
      else if (e->a->nargs >= 0 && e->a->nargs < nfun) sh_upd(&sh_par[e->a->nargs][e->a->k], (Shape){ 5, e->ci->dt });
    }
    Shape sc = shape_of(e->a);                       /* what is taken apart must be that datatype's */
    /* a field whose declared type is the datatype's PARAMETER holds whatever this use of the datatype holds:
       taken apart as another datatype than the unit built in it elsewhere (a Seq of pieces, a Seq of ranges),
       it is a block of SOME datatype -- the field's shape says so from now on */
    if (sc.k == 5 && e->ci && sc.dt && sc.dt != e->ci->dt && e->a->op == E_FIELD && field_is_param(e->a->ci, (int)e->a->k)) {
      long fid = ctor_id(e->a->ci);
      if (fid > 0 && fid <= sh_nctor) sh_upd(&sh_fld[fid][e->a->k], (Shape){ 5, e->ci->dt });
    } else
    if (sc.k && !(sc.k == 5 && e->ci && (!sc.dt || sc.dt == e->ci->dt))) { if (dbg > 2) DBG("[shape: match on op %d (f%d.%ld k%ld) shape %d %s, wanted %s]\n", e->a->op, e->a->nargs, e->a->k, e->a->k, sc.k, sc.dt ? sc.dt : "-", e->ci ? e->ci->dt : "?"); sh_bad = 1; }
    for (int i = 0; i < e->nargs; i++) r = sh_join(r, shape_of(e->args[i]));
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
    long id = ctor_id(e->ci);
    if (id <= 0 || id > sh_nctor) { r.k = 9; break; }
    sh_built[id] = 1;
    for (int j = 0; j < e->nargs; j++) {
      sh_upd(&sh_fld[id][j], shape_of(e->args[j]));
      const Expr *x = e->args[j];
      if (x->op == E_PARAM && x->nargs < 0 && x->k < nesh) sh_upd(&esh[x->k], sh_fld[id][j]);
    }
    r.k = 5; r.dt = e->ci->dt; break;
  }
  case E_FIELD: {
    { Shape sc = shape_of(e->a); if (sc.k && !(sc.k == 5 && e->ci && (!sc.dt || sc.dt == e->ci->dt))) sh_bad = 1; }
    long id = ctor_id(e->ci);
    r = id > 0 && id <= sh_nctor && e->k < e->ci->k ? sh_fld[id][e->k] : (Shape){ 9, NULL };
    break;
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
  sh_fld = A(sizeof *sh_fld * (size_t)(sh_nctor + 1)); sh_built = A((size_t)(sh_nctor + 1)); sh_fneed = A((size_t)(nfun ? nfun : 1));
  for (long k = 1; k <= sh_nctor; k++) sh_fld[k] = A(sizeof **sh_fld * (size_t)(lin_ctor_info(k)->k + 1));
  /* a field's DECLARED type is its shape to start from: a field the unit only passes along is never taken
     apart, so nothing else would say what it holds -- and data read in needs its shape */
  for (long k = 1; k <= sh_nctor; k++) {
    const LinCtor *c = lin_ctor_info(k); const char *d = c->fdesc;
    for (int j = 0; d && *d && j < c->k; j++, d = fd_skip(d)) {
      if (*d == 'N' || *d == 'F') sh_fld[k][j] = (Shape){ 1, NULL };
      else if (*d == 'B') sh_fld[k][j] = (Shape){ 3, NULL };
      else if (*d == 'D') {
        const char *p = strchr(d, '('); size_t nl = p ? (size_t)(p - d - 1) : 0; const LinCtor *c2;
        for (long k2 = 1; nl && (c2 = lin_ctor_info(k2)); k2++)
          if (c2->dt && strlen(c2->dt) == nl && !strncmp(c2->dt, d + 1, nl)) { sh_fld[k][j] = (Shape){ 5, c2->dt }; break; }
      }
    }
  }
  if (sh_cap < eid) { sh_cap = eid * 2 + 64; sh_memo = realloc(sh_memo, sizeof *sh_memo * (size_t)sh_cap); sh_gen = realloc(sh_gen, sizeof *sh_gen * (size_t)sh_cap); memset(sh_gen, 0, sizeof *sh_gen * (size_t)sh_cap); }
  Shape res = { 0, NULL };
  for (int round = 0; round < 1000; round++) {
    sh_changed = 0; sh_bad = 0;
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
  if (s.k != 5 || !s.dt || depth > sh_nctor) return 0;
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
  "#ifdef __linux__\nextern int madvise(void *, unsigned long, int);\n#define LIN_HUGE(p, n) madvise((p), (n), 14)\n#else\n#define LIN_HUGE(p, n) ((void)0)\n#endif\n"
  "static __attribute__((noinline, cold)) void lin_refill(long n) {\n"
  "  /* (the arena grows by doubling chunks; a large one is asked for in huge pages, where the OS has them: a fresh\n"
  "     page is the dearest thing a list costs, and a 2 MB page is one fault where 4 KB pages are 512) */\n"
  "  long g = lin_nch < 6 ? lin_nch : 6, sz = 65536L << g; if (sz < n) sz = n; long *c;\n"
  "  if (sz >= (1L << 18) && !(sz & ((1L << 18) - 1))) { c = aligned_alloc((size_t)1 << 21, (size_t)sz * 8); if (c) LIN_HUGE(c, (size_t)sz * 8); }\n"
  "  else c = malloc((size_t)sz * 8);\n"
  "  if (!c || lin_fn_aborted || lin_used > (1L << 28) || (char *)__builtin_frame_address(0) < lin_stack_lo) { free(c); lin_fn_aborted = 1; longjmp(lin_jb, 1); }\n"
  "  pthread_mutex_lock(&lin_chm);\n"
  "  if (lin_nch >= lin_cch) { lin_cch = lin_cch ? lin_cch * 2 : 64; lin_ch = realloc(lin_ch, (size_t)lin_cch * sizeof *lin_ch); }\n"
  "  lin_ch[lin_nch++] = c; lin_used += sz; pthread_mutex_unlock(&lin_chm); lin_hp = c; lin_he = c + sz; }\n"
  "extern LIN_TLS long *lin_fl[8];\n"
  "static inline long *lin_alloc(long n) { long *f = lin_fl[n & 7]; if (n < 8 && f) { lin_fl[n] = (long *)f[0]; return f; }\n"
  "  if (__builtin_expect(lin_hp + n > lin_he, 0)) lin_refill(n); long *r = lin_hp; lin_hp += n; return r; }\n"
  /* a block a match consumed and nothing else holds: back on its size's list (memory is the live data, as in C) */
  "static inline void lin_free(long *p, long n) { if (n < 8) { p[0] = (long)lin_fl[n]; lin_fl[n] = p; } }\n"
  "static inline long lin_clone(long v, int n) { if (v & 1) return v; long *o = lin_alloc(n); __builtin_memcpy(o, (long *)v, (size_t)n * 8); return (long)o; }\n"
  "static void lin_free_all(void) { for (int i = 0; i < lin_nch; i++) free(lin_ch[i]); lin_nch = 0; lin_hp = lin_he = 0; lin_used = 0; for (int i = 0; i < 8; i++) lin_fl[i] = 0; }\n"
  /* The guard lives where an infinite STRUCTURE must go -- the arena's refill, once per chunk -- and checks memory and
     the stack there; a compiled function carries nothing (measured: a per-call check doubled a tree insert).  A call
     whose runaway recursion builds nothing is not caught -- the exposure numeric units have always had.  A task on
     another thread has its own buffer and bound; abandoning anywhere marks the call, and a join that finds it marked
     abandons the joiner too, so a half-computed value is never used. */
  "#define LIN_ENTER\n#define LIN_LEAVE\n"
  "#define LIN_TASK_START(ss) if (setjmp(lin_jb)) { lin_fn_aborted = 1; return 0; } lin_stack_lo = (char *)__builtin_frame_address(0) - (ss) + ((size_t)1 << 24)\n"
  "#define LIN_JOINED (lin_fn_aborted ? (longjmp(lin_jb, 1), 0) : 0)\n"
  /* a result through its destination: LIN_PUT stores it only if it is not there already (a block rebuilt in place
     is, and storing it again would hold up the next load of that slot); LIN_SET is for a value that is new */
  "#define LIN_PUT(d, x) ({ long x_ = (x); if (*(d) != x_) *(d) = x_; 0L; })\n"
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
  if (compile_body_spec(F, NULL, known) == 0 && !failed) {
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
    if (safe && sh_bad) { safe = 0; DBG("declined: a value taken apart as something it is not (a number read as cells?)\n"); }
    for (int k = 0; safe && k < nesh; k++)            /* a data argument is read in by its shape: it must be known */
      if (esh[k].k && !shape_closed(esh[k], 0)) {
        safe = 0; DBG("declined: argument %d's shape is not known (%d %s)\n", k, esh[k].k, esh[k].dt ? esh[k].dt : "");
        if (dbg > 1) for (long c = 1; c <= sh_nctor; c++) { const LinCtor *ci = lin_ctor_info(c); if (!sh_built[c]) continue; DBG("  %s built:", ci->name); for (int jj = 0; jj < ci->k; jj++) fprintf(stderr, " %d", sh_fld[c][jj].k); fprintf(stderr, "\n"); }
      }
    int numeric = safe && (result_numeric(entry) || rshape.k == 1 || rshape.k == 3);   /* (a field read the shapes prove a number) */
    int rbool = rshape.k == 3 || (rshape.k != 1 && entry->kind == 3);
    fld_live = NULL;
    if (safe) fields_live(entry, !numeric);
    if (safe && !numeric) {                            /* a STRUCTURE: folded if its shape is known to the leaves */
      if (!shape_closed(rshape, 0) || rshape.k != 5) { safe = 0; DBG("declined: the result's shape is not known (a field holding different kinds of value)\n"); }
    }
    if (!safe) {}
    else {
      { mm_new(MM_NUM); int d = has_data(entry); for (int i = 0; !d && i < nfun; i++) d = has_data(funs[i].body); if (d) ownership(entry); }
      Buf b = nbuf(4096), fb = nbuf(4096), pre = nbuf(1024), pb = nbuf(1024);
      lift();
      for (int i = 0; i < nfun; i++) { put(&fb, "static long f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0); put(&fb, ");\n"); }
      int ok = 1;
      unsigned char *hd = A((size_t)nfun + 1);         /* which functions get a destination-passing form */
      for (int i = 0; i < nfun; i++) dp_scan(funs[i].body, i, hd);
      for (int ch = 1; ch; ) { ch = 0; for (int i = 0; i < nfun; i++) if (hd[i]) ch |= dp_scan(funs[i].body, i, hd); }
      for (int i = 0; i < nfun; i++) if (hd[i]) { put(&fb, "static long f%d_d(long *dst", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", long p%d", j); fv_params(&fb, i, 1, 1); put(&fb, ");\n"); }
      hasd = hd;
      for (int i = 0; ok && i < nfun; i++) {
        put(&fb, "static long f%d(", i); plistn(&fb, 1, funs[i].arity); fv_params(&fb, i, 1, funs[i].arity > 0);
        emitting = i; fscope++;
        if (hd[i]) {                                   /* the plain form: the other, given a local to write */
          put(&fb, ") { long r = 0; f%d_d(&r", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", p%d", j); fv_params(&fb, i, 0, 1); put(&fb, "); return r; }\n");
          if (pm_cand(i)) {                             /* (see pm_cand) its loop, a stretch of its loop, and who decides */
            int K = pm_k, tf = pm_tf, np = funs[i].arity + nfv[i];
            Buf pt = nbuf(256), pu = nbuf(256);          /* the parameters, typed and not */
            for (int j = 0; j < funs[i].arity; j++) { put(&pt, ", long p%d", j); put(&pu, ", p%d", j); }
            fv_params(&pt, i, 1, 1); fv_params(&pu, i, 0, 1);
            put(&fb, "static long f%d_ds(long *dst%s);\nstatic long f%d_dp(long *dst%s, long stop);\n", i, pt.s, i, pt.s);
            put(&fb, "static long f%d_ds(long *dst%s) { LIN_ENTER; return ", i, pt.s);
            dp_self = 1; tailpos = 1; ok = emit_region(&fb, &pre, funs[i].body, 0, 4096); tailpos = 0; put(&fb, "; }\n");
            fscope++;
            put(&fb, "static long f%d_dp(long *dst%s, long stop) { LIN_ENTER; if (p%d == stop) return (long)dst; return ", i, pt.s, K);
            dp_self = 2; tailpos = 1; ok = ok && emit_region(&fb, &pre, funs[i].body, 0, 4096); tailpos = 0; put(&fb, "; }\n");
            dp_self = 0;
            put(&fb, "typedef struct { long *dst; long p[%d]; long stop, r; } PM%d;\n", np ? np : 1, i);
            put(&fb, "static void *pmrun%d(void *v) { PM%d *s = v; LIN_TASK_START((size_t)256 << 20); s->r = f%d_dp(s->dst", i, i, i);
            for (int j = 0; j < np; j++) put(&fb, ", s->p[%d]", j);
            put(&fb, ", s->stop); return 0; }\n");
            put(&fb, "static int lin_threads_; static int lin_pm_busy;\n");
            put(&fb, "static long f%d_d(long *dst%s) {\n  int T = lin_threads_; long n = 0;\n", i, pt.s);
            put(&fb, "  if (T < 2 || lin_pm_busy) return f%d_ds(dst%s);\n", i, pu.s);
            put(&fb, "  for (long q = p%d; !(q & 1) && n < (long)T * 4; q = ((long *)q)[%d]) n++;\n", K, tf);
            put(&fb, "  if (n < (long)T * 4 || !__sync_bool_compare_and_swap(&lin_pm_busy, 0, 1)) return f%d_ds(dst%s);\n", i, pu.s);
            put(&fb, "  for (long q = p%d; !(q & 1); q = ((long *)q)[%d]) n++;\n  n -= (long)T * 4;\n", K, tf);
            put(&fb, "  pthread_t t[T]; PM%d s[T]; long head[T]; long q = p%d; int started = 0;\n", i, K);
            put(&fb, "  pthread_attr_t ra; pthread_attr_init(&ra); pthread_attr_setstacksize(&ra, (size_t)256 << 20);\n");
            put(&fb, "  for (int k = 0; k < T; k++) {\n    PM%d x = { k ? &head[k] : dst, {", i);
            { int c = 0; for (int j = 0; j < funs[i].arity; j++) put(&fb, j == K ? "%sq" : "%sp%d", c++ ? ", " : "", j);
              Buf fu = nbuf(64); fv_params(&fu, i, 0, 0); if (nfv[i]) put(&fb, "%s%s", c ? ", " : "", fu.s); free(fu.s); if (!np) put(&fb, "0"); }
            put(&fb, "}, 0, 0 };\n    if (k < T - 1) { for (long j = n / T; j > 0; j--) q = ((long *)q)[%d]; x.stop = q; }\n    s[k] = x;\n  }\n", tf);
            put(&fb, "  for (int k = 0; k < T; k++) { if (pthread_create(&t[k], &ra, pmrun%d, &s[k])) break; started++; }\n", i);
            put(&fb, "  for (int k = 0; k < started; k++) pthread_join(t[k], 0);\n  pthread_attr_destroy(&ra);\n");
            put(&fb, "  if (started < T) lin_fn_aborted = 1;\n  lin_pm_busy = 0;\n  (void)LIN_JOINED;\n");
            put(&fb, "  for (int k = 0; k < T - 1; k++) *(long *)s[k].r = head[k + 1];\n  return 0;\n}\n");
            free(pt.s); free(pu.s);
            if (dbg) DBG("f%d maps its list in parallel\n", i);
          } else {
          put(&fb, "static long f%d_d(long *dst", i); for (int j = 0; j < funs[i].arity; j++) put(&fb, ", long p%d", j); fv_params(&fb, i, 1, 1); put(&fb, ") { LIN_ENTER; return ");
          tailpos = 1; ok = emit_region(&fb, &pre, funs[i].body, 0, 4096); tailpos = 0; put(&fb, "; }\n");
          }
        } else { put(&fb, ") { LIN_ENTER; return "); ok = emit_region(&fb, &pre, funs[i].body, 0, 4096); put(&fb, "; }\n"); }
      }
      Buf eb = nbuf(1024);                             /* the entry's call, as an expression of its parameters */
      emitting = -1; fscope++; ok = ok && emit_region(&eb, &pre, entry, 0, 4096);
      int data = uses_data;
      put(&b, "%s%s\n#include <pthread.h>\n", LIN_I64_SRC, LIN_F64_SRC);
      if (data) put(&b, "%s", DATA_RT); else put(&b, "#define LIN_ENTER\n#define LIN_LEAVE\n#define LIN_TASK_START(ss)\n#define LIN_JOINED 0\nint lin_fn_aborted;\n");
      { Buf db = nbuf(256);                            /* (written first: a drop function may call for another datatype's) */
      for (int d = 0; d < ndrop; d++) {                /* (drop_fn may add datatypes while these are written) */
        const char *dt = drop_dt[d]; int box = -1, untag = dt_boxed(dt, &box) == 1; const LinCtor *c;
        put(&db, "static void lin_drop%d(long v) { while (!(v & 1)) { long *o = (long *)v; long nx = 1;%s", d, untag ? " {" : " switch (o[0]) {");
        for (long k = 1; (c = lin_ctor_info(k)); k++) {
          if (c->dt != dt || c->k == 0) continue;
          if (!untag) put(&db, " case %d: {", c->i);
          int last = -1;
          for (int j = 0; j < c->k; j++) if (field_live(c, j) && k <= sh_nctor && sh_fld[k][j].k == 5 && sh_fld[k][j].dt && k <= fown_n && fown[k][j]) last = j;
          for (int j = 0; j < c->k; j++) {
            if (!(field_live(c, j) && k <= sh_nctor && sh_fld[k][j].k == 5 && sh_fld[k][j].dt && k <= fown_n && fown[k][j])) continue;
            if (j == last && sh_fld[k][j].dt == dt) put(&db, " nx = o[%d];", j + !untag);     /* (the rest of a list: the loop, not a call) */
            else put(&db, " lin_drop%d(o[%d]);", drop_fn(sh_fld[k][j].dt), j + !untag);
          }
          put(&db, " lin_free(o, %d);", c->k + !untag);
          if (!untag) put(&db, " break; }");
        }
        put(&db, " } v = nx; } }\n");
      }
        for (int d = 0; d < ndrop; d++) put(&b, "static void lin_drop%d(long v);\n", d);
        put(&b, "%s", db.s); free(db.s); }
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
        /* a loop folding an associative operation over a range, its other parameters only READ: split among the
           threads, as for numbers -- what a step builds is its thread's own, what the loop shares nobody writes */
        Red red; int has_red = numeric && !nfv[0] && entry->op == E_CALL && entry->k == 0 && !entry->fre && find_reduction(&red);
        Buf rq = nbuf(256);
        if (has_red) {
          emitting = 0; fscope++;
          has_red = red_defs(&b, &pre, &red, 1);
          emitting = -1; fscope++;
          for (int i = 0; has_red && i < arity; i++) { put(&rq, "  long q%d = ", i); has_red = emit_region(&rq, &pre, entry->args[i], 0, 4096); put(&rq, ";\n"); }
          if (has_red) DBG("parallel reduction over p%d (%s), accumulator p%d, in a data unit\n", red.iv, red.up ? "up" : "down", red.acc);
        }
        put(&b, "static void *lin_run(void *u) { (void)u; const long *a = lin_args; LIN_TASK_START((size_t)1 << 30);\n");
        for (int i = 0; i < nnum; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        if (has_red) {
          put(&b, "  if (lin_threads_ > 1) {\n%s  {\n", rq.s);
          for (int i = 0; i < arity; i++) put(&b, "  long p%d = q%d;\n", i, i);
          red_run(&b, &red, 1, "lin_threads_", "lin_res = acc; (void)LIN_JOINED; return 0;");
          put(&b, "  lin_res = f0("); plist(&b, 0); put(&b, "); return 0; } }\n");
        }
        free(rq.s);
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
        r = compile_src(b.s, nnum, numeric ? (rbool ? 3 : 1) : 5, rshape);
        if (r) r->strict = funs[0].strict;
      } else if (ok && aports) {                       /* numbers only, with expression arguments: the plain entry */
        put(&b, "%slong lin_fn_entry(const long *a, int threads) { (void)threads;\n", pre.s);
        for (int i = 0; i < nnum; i++) put(&b, "  long p%d = a[%d];\n", i, i);
        put(&b, "  return %s; }\n", eb.s);
        DBG("compiling (%d functions, entry with expression arguments):\n%s\n", nfun, b.s + strlen(LIN_I64_SRC));
        r = compile_src(b.s, nnum, rbool ? 3 : 1, (Shape){ 1, NULL });
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
          ok = red_defs(&b, &pre, &red, 0);
          DBG("parallel reduction over p%d (%s), accumulator p%d\n", red.iv, red.up ? "up" : "down", red.acc);
        }
        put(&b, "long lin_fn_entry(const long *a, int threads) {\n");
        for (int i = 0; i < arity; i++) put(&b, "  long p%d = a[%d];\n", i, i);
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
static void form_note(const Net *n, const Compiled *c, const long *a, int na) {
  if (!lin_form_key || lin_form_idx < 0 || (const void *)n != lin_form_net || c->kind == 5 || c->npsh) return;
  if (fr_key != lin_form_key) {
    if (fr_f) fclose(fr_f);
    char path[4300]; form_path(path, sizeof path, lin_form_key, "tmp"); mkdir_p(path); rmdir(path);
    fr_f = fopen(path, "w"); fr_key = lin_form_key; fr_n = 0;
  }
  if (!fr_f || lin_form_idx != fr_n) return;        /* (one record per expression, in order: anything else never commits) */
  fprintf(fr_f, "%016lx %d %d %d", c->h, c->kind, lin_form_domain, na);
  for (int i = 0; i < na; i++) fprintf(fr_f, " %ld", a[i]);
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
static int form_recall(uint64_t key, int idx, int threads, long *word, int *kind, int *domain) {
  if (getenv("LIN_FN_OFF")) return -1;
  if (idx == 0 || fc_key != key) {
    free(fc_text); fc_text = NULL; fc_key = key;
    char path[4300]; form_path(path, sizeof path, key, "txt");
    FILE *fp = fopen(path, "r"); if (!fp) return -1;
    fseek(fp, 0, SEEK_END); long sz = ftell(fp); fseek(fp, 0, SEEK_SET);
    fc_text = malloc((size_t)sz + 1); if (fread(fc_text, 1, (size_t)sz, fp) != (size_t)sz) sz = 0; fc_text[sz] = 0; fclose(fp);
    fc_pos = fc_text;
  }
  if (!fc_text) return -1;
  if (!*fc_pos) return 0;
  char *e; unsigned long h = strtoul(fc_pos, &e, 16); int k = (int)strtol(e, &e, 10), d = (int)strtol(e, &e, 10), na = (int)strtol(e, &e, 10);
  if (na < 0) return -1;
  long *a = malloc(sizeof *a * (size_t)(na + 1));
  for (int i = 0; i < na; i++) a[i] = strtol(e, &e, 10);
  if (*e != '\n') { free(a); return -1; }
  fc_pos = e + 1;
  char dir[4096], so[4300]; cache_dir(dir, sizeof dir); snprintf(so, sizeof so, "%s/fn-%016lx.so", dir, h);
  void *hnd = dlopen(so, RTLD_NOW | RTLD_LOCAL);
  Entry en = hnd ? (Entry)(intptr_t)dlsym(hnd, "lin_fn_entry") : NULL;
  int *ab = hnd ? (int *)dlsym(hnd, "lin_fn_aborted") : NULL;
  if (!en) { free(a); return -1; }
  long r = en(a, threads > 0 ? threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
  free(a);
  if (ab && *ab) return -1;                          /* (its guard fired: the net computes the program) */
  *word = r; *kind = k; *domain = d;
  return 1;
}
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
  if (cells_dt && ci->dt == cells_dt) {             /* a cell `\c.\n.((c h) t)`, or the end `\c.\n.true`: no marker */
    Port c = net_alloc(n, LAM, sc), nn = net_alloc(n, LAM, sc);
    net_link(n, (Port){c.node, 2}, (Port){nn.node, 0}, 1);
    net_link(n, (Port){nn.node, 1}, net_alloc(n, ERA, sc), 1);
    if (ci->k == 2) {
      Port a1 = net_alloc(n, APP, sc), a2 = net_alloc(n, APP, sc);
      net_link(n, (Port){a1.node, 0}, (Port){c.node, 1}, 1); net_link(n, (Port){a1.node, 2}, fields[0], 1);
      net_link(n, (Port){a2.node, 0}, (Port){a1.node, 1}, 1); net_link(n, (Port){a2.node, 2}, fields[1], 1);
      net_link(n, (Port){nn.node, 2}, (Port){a2.node, 1}, 1);
    } else {
      net_link(n, (Port){c.node, 1}, net_alloc(n, ERA, sc), 1);
      net_link(n, (Port){nn.node, 2}, net_alloc_bool(n, 1), 1);
    }
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

static int numeral_shape(const Net *n, Port p);
/* DATA PASSED IN.  An argument that is already a value in the net -- a string the program read, a structure an
   earlier call built -- is not compiled as a constant (a megabyte of input is not a C literal): the driver reads it
   at call time into blocks of the layout the unit uses, by the shape the compiler inferred from how the unit uses
   it.  The blocks live in a driver arena freed after the call (and after the result is read back, which may hold
   them: a block the unit owned may have been rebuilt in place). */
typedef struct { Net *n; const Compiled *c; void **ch; int nch, cch; long *hp, *he; long *mk; Port *mp; long mcap, mcnt; int bad; long steps0; } Marsh;
static long *ms_alloc(Marsh *M, long words) {
  if (M->hp + words > M->he) {
    long sz = words > 65536 ? words : 65536; long *c = malloc((size_t)sz * sizeof *c);
    if (!c) { M->bad = 1; return NULL; }
    if (M->nch >= M->cch) M->ch = realloc(M->ch, sizeof *M->ch * (size_t)(M->cch = M->cch ? M->cch * 2 : 16));
    M->ch[M->nch++] = c; M->hp = c; M->he = c + sz;
  }
  long *r = M->hp; M->hp += words; return r;
}
static void ms_free(Marsh *M) { for (int i = 0; i < M->nch; i++) free(M->ch[i]); free(M->ch); free(M->mk); free(M->mp); }
static long ms_value(Marsh *M, Port p, Shape s, int depth);
/* THE VALUE'S DECLARED TYPE, carried down while reading it in: a field whose type is the datatype's parameter
   (a Seq's element) is told what it is by the type it was declared at -- `(alts Seq (Seq Piece))` says the
   elements of the inner Seqs are Pieces, which no shape of `scons` can say for every use of it.
   Descriptors are src/type.c's: N B F ?, L<elem>, P<i>;, D<name>(<args>). */
static const char *td_dt(const char *d) {            /* the datatype a D-descriptor names (the registry's own string) */
  if (!d || *d != 'D') return NULL;
  const char *e = strchr(d, '('); if (!e) return NULL;
  size_t nl = (size_t)(e - d - 1); const LinCtor *c;
  for (long k = 1; (c = lin_ctor_info(k)); k++) if (c->dt && strlen(c->dt) == nl && !strncmp(c->dt, d + 1, nl)) return c->dt;
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
  if (*d == 'D') { const char *dt = td_dt(d); if (dt) return (Shape){ 5, dt }; }
  return dflt;
}
static const char *ms_desc;                          /* the declared type of the value ms_value is about to read */
static long *ms_seen(Marsh *M, int node, int make) {   /* a value reached twice is one block (the net's sharing kept) */
  if (make && (M->mcnt + 1) * 2 > M->mcap) {
    long *ok = M->mk; Port *op = M->mp; long oc = M->mcap; M->mcap = M->mcap ? M->mcap * 2 : 1024;
    M->mk = calloc((size_t)M->mcap, sizeof *M->mk); M->mp = calloc((size_t)M->mcap, sizeof *M->mp); M->mcnt = 0;
    for (long i = 0; i < oc; i++) if (op[i].node > 0) { long *w = ms_seen(M, op[i].node, 1); *w = ok[i]; }
    free(ok); free(op);
  }
  if (!M->mcap) return NULL;
  for (unsigned long h = ((unsigned long)node * 0x9E3779B97F4A7C15UL >> 7) & (unsigned long)(M->mcap - 1);; h = (h + 1) & (unsigned long)(M->mcap - 1)) {
    if (M->mp[h].node == node) return &M->mk[h];
    if (M->mp[h].node <= 0) { if (!make) return NULL; M->mp[h].node = node; M->mk[h] = 0; M->mcnt++; return &M->mk[h]; }
  }
}
static long ms_value(Marsh *M, Port p, Shape s, int depth) {
  Net *n = M->n;
  const char *desc = ms_desc; ms_desc = NULL;
  s = td_shape(desc, s);
  if (M->bad || depth > n->nn) { M->bad = 1; return 0; }
  if (n->steps - M->steps0 > (long)n->nn) { M->bad = 1; return 0; }   /* (a value in hand needs no reduction to read) */
  if (s.k == 0) {                                    /* a field the analysis saw no use of: what the value IS decides */
    long x; if (net_read_i64(n, p, &x)) return x;
    long b = net_read_int(n, p, LIN_ENC_BOOL); if (b >= 0) return b;
    M->bad = 1; return 0;
  }
  if (s.k == 1) { long x; if (!net_read_i64(n, p, &x)) M->bad = 1; return x; }
  if (s.k == 3) { long b = net_read_int(n, p, LIN_ENC_BOOL); if (b < 0) M->bad = 1; return b; }
  if (s.k != 5 || !s.dt) { M->bad = 1; return 0; }   /* (a block of some datatype, not known which: not read in) */
  int box = 0, untag = dt_boxed(s.dt, &box) == 1;
  if (cells_dt && s.dt == cells_dt) {               /* a list: its spine read in a loop */
    long first = 0, *link = &first;
    Shape hs = M->c->fld[ctor_id(cell_cons)][0];
    for (long k = 0; !M->bad; k++) {
      Port h, t;
      if (k > n->nn) { M->bad = 1; break; }
      if (!net_read_cell(n, p, &h, &t)) {
        if (net_read_int(n, p, LIN_ENC_STR) != 0) { M->bad = 1; break; }
        *link = ((long)cell_nil->i << 1) | 1; break;
      }
      long *blk = ms_alloc(M, 2); if (!blk) break;
      ms_desc = desc && *desc == 'L' ? desc + 1 : NULL;
      blk[0] = ms_value(M, h, hs, depth + 1); *link = (long)blk; link = &blk[1]; p = t;
    }
    return first;
  }
  int m = 0, kmax = 0; const LinCtor *c;
  for (long id = 1; (c = lin_ctor_info(id)); id++) if (c->dt == s.dt) { m = c->m; if (c->k > kmax) kmax = c->k; }
  Port v = net_dhop(n, net_force_val(n, p));
  long *seen = v.node > 0 ? ms_seen(M, v.node, 0) : NULL;
  if (seen && *seen) return *seen;
  Port *fp = malloc(sizeof *fp * (size_t)(kmax + 1)); int i = -1;
  int k = m ? net_read_scott(n, p, m, &i, fp, kmax) : -1;
  const LinCtor *ci = k >= 0 ? dt_ctor(s.dt, i) : NULL;
  long w = 0;
  if (!ci || ci->k != k) M->bad = 1;
  else if (!k) w = ((long)ci->i << 1) | 1;
  else {
    long *blk = ms_alloc(M, k + !untag);
    if (blk) {
      if (!untag) blk[0] = ci->i;
      long id = ctor_id(ci);
      int na = desc ? td_args(desc, NULL, 0) : 0; const char **ta = malloc(sizeof *ta * (size_t)(na + 1)); if (desc) td_args(desc, ta, na); const char *fd = ci->fdesc;
      for (int j = 0; j < k && !M->bad; j++, fd = fd_skip(fd)) {
        char *f = desc && fd && *fd ? td_subst(fd, ta, na) : NULL;
        ms_desc = f;
        blk[j + !untag] = ms_value(M, fp[j], M->c->fld[id][j], depth + 1);
        ms_desc = NULL; free(f);
      }
      free(ta);
      w = (long)blk;
    }
  }
  free(fp);
  if (!M->bad && v.node > 0 && !(w & 1)) { long *slot = ms_seen(M, v.node, 1); if (slot) *slot = w; }
  return w;
}
typedef struct { Marsh *M; Port p; Shape s; long w; } MsArg;
static void *ms_thread(void *u) {
  MsArg *a = u;
  /* (a datatype with no parameters is its own declared type: its fields' descriptors say the rest) */
  char *top = a->s.k == 5 && a->s.dt ? malloc(strlen(a->s.dt) + 4) : NULL; if (top) { sprintf(top, "D%s()", a->s.dt); ms_desc = top; }
  a->w = ms_value(a->M, a->p, a->s, 0); ms_desc = NULL; free(top); return NULL;
}
static long marshal(Marsh *M, Port p, Shape s) {   /* (on a large stack: data is deep) */
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
    /* (the call WITH its arguments first, when some are not numbers yet: that unit is the one that runs, and a
       function of data or of functions compiles no other way -- the function alone is the fallback) */
    Compiled *c = NULL;
    long args[8]; int call = appy, ok;
    int car = lin_precompile_depth ? 0 : (N = n, fun_arity(F));
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
        if (!an[k] && data_value(n, ap[k]) && !list_end(n, ap[k])) an[k] = 2;   /* data already in the net: passed in at call time */
        if (dbg > 1) { long x = 0; int ns = numeral_shape(n, ap[k]); int ok = ns && net_read_i64(n, ap[k], &x); DBG("[arg %d: shape %d read %d (%ld) -> %d]\n", k, ns, ok, x, an[k]); }
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
          c2 = compile_fn_ex(n, F, ap, an);
          cx_n = 0; all = 0;
          if (!c2) { free(tops); return folded; }
          cl = rp.node; DBG("(the whole expression is the unit)\n");
        }
        for (; cx_n > 0 && !c2; cx_n--) {             /* the widest context that compiles */
          c2 = compile_fn_ex(n, F, ap, an);
          if (c2) cl = tops[cx_n];
        }
        if (all && !c2) DBG("(no context of the call compiles: the call alone)\n");
        free(tops); cx_n = 0;
        if (!c2 && !root_mode) c2 = compile_fn_ex(n, F, ap, an);
        double t_c1 = now_ms();
        if (c2) {
          int nn = 0, pi = 0;
          long *xa = malloc(sizeof *xa * (size_t)(car + n_inp + c2->npsh + 1));   /* (the arguments, inputs included) */
          Marsh M; memset(&M, 0, sizeof M); M.n = n; M.c = c2; M.steps0 = n->steps;
          for (int k = 0; k < car && !M.bad; k++) {
            if (an[k] == 1) { net_read_i64(n, ap[k], &xa[nn++]); pi++; }
            else if (an[k] == 2) {
/* (a data argument the unit has NO shape for is one it never looks at -- passed along from call to
                 call, or met by a whole-expression unit where the program names it: nothing is read in for it) */
              if (!c2->npsh || (pi < c2->npsh && c2->psh[pi].k == 0)) { xa[nn++] = 0; pi++; continue; }
              if (pi >= c2->npsh) { M.bad = 1; break; }
              xa[nn++] = marshal(&M, ap[k], c2->psh[pi]); pi++;
              if (dbg > 1) DBG("[argument %d passed in as %d %s: %lx]\n", k, c2->psh[pi - 1].k, c2->psh[pi - 1].dt ? c2->psh[pi - 1].dt : "", (unsigned long)xa[nn - 1]);
            }
          }
          for (int i = 0; i < n_inp && !M.bad; i++, pi++) {   /* the inputs met inside the arguments */
            if (pi >= c2->npsh) { M.bad = 1; break; }
            xa[nn++] = marshal(&M, inp_port[i], c2->psh[pi]);
          }
          if (M.bad) { DBG("an argument could not be read in: the net computes the call\n"); ms_free(&M); free(xa); goto decline_ex; }
          extern int lin_threads;
          double t_m = now_ms();
          long r = c2->fn(xa, lin_threads > 0 ? lin_threads : (int)sysconf(_SC_NPROCESSORS_ONLN));
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
              if (plain && n->tag[out.node] == ROOT) { long *ka = malloc(sizeof *ka * (size_t)(car + 1)); int kn = 0;
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
static int fn_reduce(Net *n, Port *rx, int nred, long limit, int *changed);
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
static void __attribute__((constructor)) fn_load(void) {
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
