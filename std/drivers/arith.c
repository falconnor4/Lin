#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <math.h>

/* ---------------------------------------------------------------------- *
 *  Native scalar arithmetic & comparison semantics (generalized).
 *
 *  The SINGLE authority for pure integer/float arithmetic + comparison
 *  builtins (`lin_add`, `lin_sub`, `lin_mul`, `lin_div`, `lin_mod`,
 *  `lin_pow`, `lin_eq`..`lin_geq`, `lin_ffloor`, every `lin_f*` float op,
 *  `lin_lerp`, `lin_fclamp`).  Exposes one canonical entry point:
 *
 *      int lin_arith_scalar(fn, argc, vals, out, outkind)
 *
 *  so EVERY reduction strategy (base cpu fold in src/io.c, SIMD, GPU, or a
 *  future driver) resolves scalar arithmetic through this ONE table instead of
 *  re-implementing the ops per-driver.  The strategy keeps its own concern —
 *  how it extracts/decodes args from the net and when it folds — and calls
 *  this for the math itself.  New ops are new table rows, not new switch
 *  arms in each driver.
 *
 *  `vals` carries decoded scalars as C longs (int / bool / IEEE-754 double
 *  bits, symmetric with `Val`).  `outkind`: 1=int, 3=bool (out=0/1), 4=float
 *  (out = IEEE-754 bits).  Returns 1 if `fn` is one of our rows, else 0
 *  (declined, so the caller can fall back to core / dlsym).
 * ---------------------------------------------------------------------- */
int lin_arith_scalar(const char *fn, int argc, const long *a, long *out, int *outkind) {
  *outkind = 0;
  if (!fn) return 0;

  /* float binary ops: args are IEEE-754 bits carried as longs; result float */
  if      (fn[0]=='l' && fn[1]=='i' && fn[2]=='n' && !strncmp(fn, "lin_fadd", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x+y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsub", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x-y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmul", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x*y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fdiv", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=y!=0.0?x/y:0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fpow", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=pow(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fatan2", 10)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=atan2(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmin", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x<y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmax", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x>y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  /* float unary ops -> float */
  else if (!strncmp(fn, "lin_fsqrt", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?sqrt(x):0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsin", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=sin(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fcos", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=cos(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ftan", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=tan(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fabs", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=fabs(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsign", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?1.0:-1.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ffract", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x-floor(x); memcpy(out,&r,8); *outkind=4; return 1; }
  /* float comparisons -> Church bool */
  else if (!strncmp(fn, "lin_feq", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x==y; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_flt", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<y;  *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_fleq", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<=y; *outkind=3; return 1; }
  /* float -> int / 3-arg float combinators */
  if (!strncmp(fn, "lin_ffloor", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); *out=(long)floor(x); *outkind=1; return 1; }
  if (!strncmp(fn, "lin_fmin", 8) || !strncmp(fn, "lin_fmax", 8)) { /* handled above */ }
  if (!strncmp(fn, "lin_lerp", 8) && argc >= 3) { double x,y,t; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); memcpy(&t,&a[2],8); double r=x+(y-x)*t; memcpy(out,&r,8); *outkind=4; return 1; }
  if (!strncmp(fn, "lin_fclamp", 10) && argc >= 3) { double x,lo,hi; memcpy(&x,&a[0],8); memcpy(&lo,&a[1],8); memcpy(&hi,&a[2],8); double r=x<lo?lo:(x>hi?hi:x); memcpy(out,&r,8); *outkind=4; return 1; }

  /* integer arithmetic / comparisons */
  if (argc < 2) return 0;                       /* every int op needs 2 args */
  if      (!strncmp(fn, "lin_add", 7)) *out = a[0] + a[1];
  else if (!strncmp(fn, "lin_sub", 7)) *out = a[0] >= a[1] ? a[0] - a[1] : 0;
  else if (!strncmp(fn, "lin_mul", 7)) *out = a[0] * a[1];
  else if (!strncmp(fn, "lin_div", 7)) *out = a[1] ? a[0] / a[1] : 0;
  else if (!strncmp(fn, "lin_mod", 7)) *out = a[1] ? a[0] % a[1] : 0;
  else if (!strncmp(fn, "lin_pow", 7)) { long b=a[0], e=a[1], r=1; while (e>0) { if (e&1) r*=b; b*=b; e>>=1; } *out=r; }
  else if (!strncmp(fn, "lin_eq", 6)) { *out = a[0] == a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_lt", 6)) { *out = a[0] <  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_leq", 7)) { *out = a[0] <= a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_gt", 6)) { *out = a[0] >  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_geq", 7)) { *out = a[0] >= a[1]; *outkind=3; return 1; }
  else return 0;
  *outkind = 1;
  return 1;
}

/* ====================================================================== *
 *  Fold pre-emptor (`LIN_CAP_PREEMPT`, priority 5 — ahead of simd's 10).
 *
 *  The `_ffi`/`_op` native fold used to live in the core's `net_interact`.
 *  The core now keeps only the four correctness rules (β, δ⋈δ, γ⋈δ, ε); the
 *  fold, its saturation guard, and every fold-shaped rewrite moved here.
 *  This driver is a *pre-pass*: it claims a redex class the core would
 *  otherwise β on the active wave, and the core stays complete without it
 *  (a pure-Lin `_op` closure's LAM body IS the semantics; an unfolded `_ffi`
 *  closure is resolved by readback exactly as before).
 *
 *  Two rules the port must keep straight:
 *
 *   - `claim` never strands.  A driver that claims a pair the core never β's
 *     has stranding on its hands, so `reduce` disposes of EVERY pair it was
 *     handed: fold it, force its operands and fold it, or give it back to the
 *     core's β (always correct, just slower).
 *   - THE OPERANDS ARE THUNKS, and the fold is what needs them, so the forcing
 *     belongs here and goes through `net_force` (ABI 3 has no `drain`/`pending`/
 *     `arg_fold`; a driver that wants a concrete operand says so).  Needed order
 *     gives the reducer no reason to have evaluated `(mul 150 150)` in
 *     `(div (mul 150 150) 100)` before the `div` redex is reached; the fold asks
 *     for it.  The shared argument decoder already forces each slot it reads
 *     (src/io.c), and `force_spine` below makes the same demand explicit for a
 *     slot the decoder could not read at all.
 * ====================================================================== */

/* Tri-state result of trying to compute a saturated closure's value. */
enum { EV_NO = 0, EV_READY = 1, EV_WAIT = 2 };

/* read a port's wire (a function, not a macro: `wire_at(n, a, b)` would
   split into three macro arguments at the comma inside the braces) */
static inline Port wire_at(const Net *n, int node, int port) { return n->wire[node * 3 + port]; }
#define IN_NET(n, i) ((i) >= 0 && (i) < (n)->nn)

static const char *nmof(const Net *n, int id) {
  return (id >= 0 && id < n->nn && n->name[id]) ? n->name[id] : "";
}

/* derive the shared-table scalar op name from a DT_OP carrier tag (`_add` -> "lin_add") */
static int op_fn_from_tag(const char *tag, char *fn, int fnmax) {
  if (!tag || tag[0] != '_' || !tag[1]) return 0;
  snprintf(fn, (size_t)fnmax, "lin_%s", tag + 1);
  return 1;
}

/* Consume a node this redex *exclusively* owns.  `lam`/`app` are
   principal-connected to each other, so nothing else can be attached to them,
   but the β-body and the operand spine may be SHARED: a live DUP on that port
   means a sibling redex reaches the same sub-net through the fan, and marking
   the fan (or a node behind it) dead would strand the sibling — the fold would
   then read a destroyed operand and one consumer's result would leak into
   another's.  Shared structure is left for the reachability GC instead. */
static void fold_own(Net *n, Port p) {
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node]) return;
  if (n->tag[p.node] == DUP) return;                 /* behind a fan: not ours alone */
  n->dead[p.node] = 1;
}

/* alloc a concrete value node (int -> Scott numeral, bool -> Church bool, float -> `_fsz` box) */
static Port val_to_port(Net *n, const Val *v) {
  if (v->kind == 3) return net_alloc_bool(n, (int)v->iv);
  if (v->kind == 4) { double d; memcpy(&d, &v->iv, 8); return net_alloc_float(n, d); }
  return net_alloc_scott(n, v->iv);
}

/* dig the `_ffi` closure header at LAM `lam` (shape \_ffi. \_ret. ((_ffi <fn>) <args>))
   into `*fnp` (the fn APP) and `*argp` (the `_cl` arg spine) — same walk the core's
   shared decoder does (net_ffi_fn/net_ffi_args), repeated here so the arg spine port
   is reachable for the saturation guard. */
/* Through a fan, exactly as the core's decoder does: a SHARED closure is reached through a DUP, so
   its body wire leads to the fan's auxiliary and the principal is the body.  Reading it plainly is
   what made a runtime `_ffi` value used twice unfold instead of fold. */
static Port hop(const Net *n, Port p) {
  for (int i = 0; i < n->nn && IN_NET(n, p.node) && !n->dead[p.node] && n->tag[p.node] == DUP; i++)
    p = p.port == 0 ? wire_at(n, p.node, 1) : wire_at(n, p.node, 0);
  return p;
}

static int ffi_header(Net *n, int lam, Port *fnp, Port *argp) {
  if (!IN_NET(n, lam) || n->dead[lam] || n->tag[lam] != LAM) return 0;
  Port r = hop(n, wire_at(n, lam, 2));
  if (!IN_NET(n, r.node) || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = hop(n, wire_at(n, r.node, 2));
  if (!IN_NET(n, a2.node) || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  if (fnp) *fnp = wire_at(n, a2.node, 0);
  if (argp) *argp = wire_at(n, a2.node, 2);
  return 1;
}


/* Compute the concrete value of a saturated pure-Lin `_op` redex (DT_OP LAM `lam`
   applied to its redex APP `app`, whose port 2 carries the raw operand `_cl`-spine).
   EV_NO  : not a foldable op (no scalar provider claims it) -> let the core β the
            pure-Lin fallback body.
   EV_WAIT: our op, but an operand is not concrete yet -> also plain β. */
static int op_eval(Net *n, int lam, int app, Val *v) {
  char fn[256];
  if (!op_fn_from_tag(nmof(n, lam), fn, sizeof fn)) return EV_NO;
  if (!IN_NET(n, app) || n->dead[app] || n->tag[app] != APP) return EV_NO;
  Port argp = wire_at(n, app, 2);
  int slots = net_spine_slots(n, argp);
  Val fargs[8]; memset(fargs, 0, sizeof fargs);
  int argc = net_spine_args(n, argp, fargs, 8);
  if (slots < 1 || slots > 8 || argc < slots) return EV_WAIT;   /* operand spine not readably concrete */
  long c[8] = {0};
  for (int i = 0; i < slots; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return EV_WAIT;
    c[i] = fargs[i].iv;
  }
  long out = 0; int okind = 0;
  if (!lin_arith_scalar(fn, slots, c, &out, &okind)) return EV_NO;   /* declined: pure-Lin β computes it */
  v->kind = okind == 4 ? 4 : (okind == 3 ? 3 : 1);
  v->iv = out;
  return EV_READY;
}

/* Compute the concrete value of a saturated pure-Lin `_ffi` closure `lam`.
   Only PURE `lin_*` builtins fold; side-effecting FFI (`puts`, `dlopen`,
   `getenv`, ...) and `lin_streq` (needs C strings) stay on readback.
   Saturation guard: EVERY operand on the `_cl` spine must be concretely
   readable — checking only the first let later non-concrete operands fold as
   garbage; a nested `_ffi`/`_op` operand must itself be fully concrete (the
   shared dec_arg does that, and a slot it cannot decode is counted skipped). */
static int ffi_eval(Net *n, int lam, Val *v, char *fnout, int fnmax) {
  Port a1, argp;
  if (!ffi_header(n, lam, &a1, &argp)) return EV_WAIT;         /* closure header not formed yet */
  if (!IN_NET(n, a1.node) || a1.port != 1 || n->tag[a1.node] != APP) return EV_WAIT;
  char fn[256];
  if (net_read_string(n, wire_at(n, a1.node, 2), fn, sizeof fn) < 0) return EV_WAIT;
  if (strncmp(fn, "lin_", 4)) return EV_NO;                    /* only pure lin_* builtins fold */
  if (!strncmp(fn, "lin_streq", 9)) return EV_NO;              /* needs C strings, keep readback */
  if (fnout && fnmax > 0) snprintf(fnout, (size_t)fnmax, "%s", fn);

  Val vals[8]; memset(vals, 0, sizeof vals);
  int na = net_ffi_args(n, (Port){lam, 0}, vals, 8);
  int slots = net_spine_slots(n, argp);
  if (slots < 0) { if (na != 0) return EV_WAIT; slots = 0; }   /* not a cons spine: only the empty arg list is concrete */
  else if (slots > 8) return EV_WAIT;
  if (na < slots) return EV_WAIT;                              /* a present operand is not concrete yet */

  long c[8] = {0};
  for (int i = 0; i < slots; i++) {
    int k = vals[i].kind;
    if (k == 2) c[i] = (long)(intptr_t)vals[i].sv;             /* string operand: hand the C string through, as run_ffi does */
    else if (k == 1 || k == 3 || k == 4) c[i] = vals[i].iv;
    else return EV_WAIT;
  }
  long out = 0; int okind = 0;
  if (lin_arith_scalar(fn, slots, c, &out, &okind)) {
    v->kind = okind == 4 ? 4 : (okind == 3 ? 3 : 1);
    v->iv = out;
    return EV_READY;
  }
  /* Core readback builtins that are not scalar-table rows but ARE pure `lin_*`
     closures the evicted in-core fold used to materialise (run_ffi's builtin rows).
     Keeping them here preserves behaviour for `(folded)` / `(i2f n)` / `(float s)`. */
  /* These two OBSERVE the reduction rather than compute anything.  Folding them during
     the AOT build would freeze the build-time answer into the .line artifact (a program
     could then never observe that folds happened at run time), so decline and let the
     runtime's readback answer them.  Same reason the `_ffi` path refuses non-`lin_`
     names: build-time evaluation must be observation-free. */
  if (lin_build_depth > 0 && (!strcmp(fn, "lin_folds") || !strcmp(fn, "lin_folded"))) return EV_NO;
  if (!strcmp(fn, "lin_folds"))  { v->kind = 1; v->iv = lin_fold_total(); return EV_READY; }
  if (!strcmp(fn, "lin_folded")) { v->kind = 3; v->iv = lin_fold_total() > 0; return EV_READY; }
  if (!strcmp(fn, "lin_float") && slots >= 1) {
    double d = (double)c[0]; long rb; memcpy(&rb, &d, 8); v->kind = 4; v->iv = rb; return EV_READY;
  }
  if (!strcmp(fn, "lin_parse_float")) {
    if (slots < 1 || vals[0].kind != 2) return EV_NO;
    double d = strtod(vals[0].sv, NULL); long rb; memcpy(&rb, &d, 8); v->kind = 4; v->iv = rb; return EV_READY;
  }
  return EV_NO;
}

/* ---- the fold rewrites (ports of the evicted lin_fold_op / lin_fold_ffi) ---- */

/* `_op` fold rewiring: `ar = wire(app,1)` is the APP's body-slot partner where β
   threads the result out; inject the value AT `ar` (linking into {app,1} would
   REPLACE `ar` and strand the consumer).  Fall back to {app,1} if `ar` was already
   consumed.  Kills `lam` and `app`. */
static void fold_op_head(Net *n, int lam, int app, const Val *v) {
  Port res = val_to_port(n, v);
  Port ar = wire_at(n, app, 1);
  Port aa = wire_at(n, app, 2);
  Port body = wire_at(n, lam, 2);               /* the pure-Lin β-body residual */
  n->dead[lam] = 1; n->dead[app] = 1;
  fold_own(n, body); fold_own(n, aa);                /* only what this redex owns outright */
  if (ar.node >= 0 && ar.node < n->nn && !n->dead[ar.node])
    net_link(n, res, ar, 1);
  else
    net_link(n, res, (Port){app, 1}, 1);
  lin_fold_bump();
}

/* `_ffi` fold rewiring: link the concrete value to {app, 0} and kill the closure LAM
   (same as the evicted fold_link). */
static void fold_ffi_head(Net *n, int lam, int app, const Val *v) {
  Port res = val_to_port(n, v);
  n->dead[lam] = 1;
  net_link(n, res, (Port){app, 0}, 1);
  lin_fold_bump();
}

/* Force every operand slot of a `_cl` arg spine.  Needed order leaves an operand as a thunk
   until something needs it, and this fold is that something: `(div (mul 150 150) 100)` reaches
   the `div` redex with its first operand still an unreduced `_op` closure.  Reads through the
   shared decoder, so the slot walk is the same one the fold itself uses. */
static void force_spine(Net *n, Port argp) {
  Val tmp;
  int slots = net_spine_slots(n, argp);
  for (int i = 0; i < slots && i < 8; i++) {
    Port cur = net_dhop(n, argp);
    for (int k = 0; k <= i; k++) {
      if (!IN_NET(n, cur.node) || n->tag[cur.node] != LAM) return;
      Port inner = net_dhop(n, wire_at(n, cur.node, 2));
      if (!IN_NET(n, inner.node) || n->tag[inner.node] != LAM) return;
      Port body = net_dhop(n, wire_at(n, inner.node, 2));
      if (!IN_NET(n, body.node) || n->tag[body.node] != APP) return;
      Port ia = net_dhop(n, wire_at(n, body.node, 0));
      if (k == i) { if (IN_NET(n, ia.node) && n->tag[ia.node] == APP) { (void)tmp; net_force(n, wire_at(n, ia.node, 2)); } return; }
      cur = wire_at(n, body.node, 2);
    }
  }
}

/* ---- LinDriver hooks ---- */

/* claim: a DT_OP/DT_FFI closure redex.  The core hands wave pairs in tag order, so normalise
   LAM-first here.  `reduce` disposes of everything claimed, so claiming is always safe. */
static int arith_claim(const Net *ncn, Port p1, Port p2) {
  Net *n = (Net *)ncn;
  if (p1.port || p2.port) return 0;
  if (!IN_NET(n, p1.node) || !IN_NET(n, p2.node)) return 0;
  if (n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (net_wire(n, p1).node != p2.node || net_wire(n, p1).port != p2.port) return 0;
  if (net_wire(n, p2).node != p1.node || net_wire(n, p2).port != p1.port) return 0;
  int lam;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) lam = p1.node;
  else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) lam = p2.node;
  else return 0;
  int c = ctor_tag(nmof(n, lam));
  if (c == DT_OP) { char fn[256]; return op_fn_from_tag(nmof(n, lam), fn, sizeof fn); }
  return c == DT_FFI;
}

/* reduce: fold each claimed redex.  The ABI hands a slice of PAIRS: `nred` counts pairs,
   `redexes` holds 2*nred ports.  Every claimed pair is consumed one way or another: forced
   and folded, or handed back to the core's β, which is always correct (just slower) -- a
   claimed-but-unhandled pair would be dropped from the wave and stranded. */
static int arith_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int done = 0;
  for (int i = 0; i < nred; i++) {
    if (limit > 0 && (long)n->steps >= limit) break;
    Port pa = redexes[2 * i], pb = redexes[2 * i + 1];
    if (pa.port || pb.port) continue;
    if (!IN_NET(n, pa.node) || !IN_NET(n, pb.node)) continue;
    if (n->dead[pa.node] || n->dead[pb.node]) continue;
    int lam, app;
    if (n->tag[pa.node] == LAM && n->tag[pb.node] == APP) { lam = pa.node; app = pb.node; }
    else if (n->tag[pb.node] == LAM && n->tag[pa.node] == APP) { lam = pb.node; app = pa.node; }
    else continue;
    if (net_wire(n, (Port){lam, 0}).node != app || net_wire(n, (Port){app, 0}).node != lam) continue;
    int c = ctor_tag(nmof(n, lam));
    Val v; int ev = EV_NO;
    if (c == DT_OP) ev = op_eval(n, lam, app, &v);
    else if (c == DT_FFI) ev = ffi_eval(n, lam, &v, NULL, 0);
    /* A def is precompiled with its operands still FREE, so a foldable redex can never be ready here.
       Leaving it alone is what keeps the fold: β-ing it would replace the `_op`/`_ffi` head with the
       pure-Lin body, and every later use of the def -- and the baked net itself -- would have lost the
       redex the fold exists for.  The core's `act` list is a wave snapshot, so an unhandled pair is
       simply not re-enqueued into this reduction; the baked net carries the closure, and splicing a
       reference re-enqueues it with concrete operands. */
    if (ev != EV_READY && lin_precompile_depth > 0) continue;
    if (ev == EV_WAIT) {
      /* The operands are not concrete yet.  Under needed order that is the normal state -- nothing
         had a reason to reduce them -- so ask for them and try again. */
      Port argp = (c == DT_OP) ? wire_at(n, app, 2) : (Port){-1, 0};
      if (c == DT_FFI) ffi_header(n, lam, 0, &argp);
      if (IN_NET(n, argp.node)) force_spine(n, argp);
      ev = (c == DT_OP) ? op_eval(n, lam, app, &v) : ffi_eval(n, lam, &v, NULL, 0);
    }
    if (ev == EV_READY) {
      if (c == DT_OP) fold_op_head(n, lam, app, &v); else fold_ffi_head(n, lam, app, &v);
      done++; (*changed)++; n->steps++;
      continue;
    }
    /* Not foldable (an open precompile body, or an operand that is not a value even after
       forcing): hand the redex to the core's own β rather than strand it. */
    if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
  }
  return done;
}

/* ---- registration ----
   Two roles in one plugin:
     - lin_arith_scalar is the shared SEMANTIC authority every strategy calls;
     - lin_arith_driver is the fold PRE-EMPTOR (LIN_CAP_PREEMPT, priority 5, ahead of
       simd's 10) that claims folded redexes before any strategy sees them.  A pre-emptor
       composes with whichever strategy is selected: lin_driver_clear (what `(set_driver
       ...)` calls) drops strategies but keeps pre-emptors.
   std/std.lin loads std/drivers/arith.lin, which is what dlopens this .so; the core itself
   starts with no driver at all. */
LinDriver lin_arith_driver;                                /* defined below; registered by the constructor */
static void __attribute__((constructor)) arith_load(void) {
  lin_scalar_ops_add(lin_arith_scalar);
  static int registered = 0;
  if (registered) return;                               /* constructors can run once per load, never twice */
  registered = 1;
  lin_driver_add(&lin_arith_driver);
}

LinDriver lin_arith_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "arith", .description = "native scalar arithmetic table + `_op`/`_ffi` fold pre-emptor",
  .caps = LIN_CAP_NATIVE_NUM | LIN_CAP_PREEMPT, .priority = 5,   /* before simd(10): claim folds first */
  .claim = arith_claim, .reduce = arith_reduce,
};
