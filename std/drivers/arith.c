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
 *  Three rules the port must keep straight:
 *
 *   - `claim` never strands.  A driver that claims a pair the core never β's
 *     has stranding on its hands, so claim returns 1 only when this driver
 *     will either rewrite the pair right now or PARK it for a later wave:
 *     the LAM carries a DT_OP/DT_FFI carrier, the `_ffi` fn is a pure `lin_*`
 *     builtin, and either every operand decodes to a concrete value (fold
 *     now) or a present operand slot is not concrete yet (wait).  Everything
 *     else returns 0 and is left to plain β.
 *   - THE WAIT IS LOAD-BEARING, and its policy lives here (the core has no
 *     deferral state at all).  `(div (mul 150 150) 100)` is the falsifying
 *     case: the outer `div`'s operand slot still holds the unfolded `_op`
 *     closure `((\_mul <body>) (150::150::nil))`, so its value is not readable
 *     yet.  β-squashing the outer closure there substitutes that *thunk* where
 *     a Scott numeral was expected and yields garbage (HEAD's core comment:
 *     "a pure-lin `_ffi`/`_op` closure with a non-concrete operand must not be
 *     β-squashed here (β-duplication strangles the operand sub-net); defer
 *     (re-queue) so its redexes run first").  So a not-ready pair is PARKED —
 *     held out of the wave exactly as the evicted core's blocked list did —
 *     and `drain` re-enqueues it after the wave empties, once the operand's own
 *     redexes have had their turn.  The bound is the evicted core's
 *     `n->declines < (1 << 15)`: past it `claim` stops claiming pending pairs
 *     and `reduce` releases them to the core's β, which is always correct, so
 *     the redex can never be stranded and the run can never livelock.
 *   - `pending` reports a parked redex so a reduction that ends with one has
 *     not reached a value and must not be baked into a precompiled def.
 *
 *  What is left that a driver alone can see are the two edges the core cannot
 *  reach as a principal×principal redex, offered explicitly through
 *  LinDriver.{arg_fold,materialize}.
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
static int ffi_header(Net *n, int lam, Port *fnp, Port *argp) {
  if (!IN_NET(n, lam) || n->dead[lam] || n->tag[lam] != LAM) return 0;
  Port r = wire_at(n, lam, 2);
  if (!IN_NET(n, r.node) || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = wire_at(n, r.node, 2);
  if (!IN_NET(n, a2.node) || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  if (fnp) *fnp = wire_at(n, a2.node, 0);
  if (argp) *argp = wire_at(n, a2.node, 2);
  return 1;
}

/* Number of operand slots on the `_cl`-spine at `argp` (the shared decoder's walk),
   or -1 when the port is not a cons spine at all (empty arg list / free variable /
   not formed yet).  Used only to detect a spine cell whose operand did not decode:
   the decoder SKIPS such a slot, so `argc < slots` means "not saturated yet". */
static int spine_slot_count(Net *n, Port argp) {
  Port cur = net_dhop(n, argp);
  if (!IN_NET(n, cur.node) || n->dead[cur.node] || n->tag[cur.node] != LAM ||
      ctor_tag(nmof(n, cur.node)) != DT_STR) return -1;          /* arg list is a cons spine */
  Port bn = net_dhop(n, wire_at(n, cur.node, 2));
  if (!IN_NET(n, bn.node) || bn.port != 0 || n->tag[bn.node] != LAM) return -1;
  int slots = 0;
  for (int step = 0; step < n->nn; step++) {
    cur = net_dhop(n, cur);
    if (!IN_NET(n, cur.node) || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
    Port inner = net_dhop(n, wire_at(n, cur.node, 2));
    if (!IN_NET(n, inner.node) || inner.port != 0 || n->tag[inner.node] != LAM) break;
    Port body = net_dhop(n, wire_at(n, inner.node, 2));
    if (!IN_NET(n, body.node) || n->tag[body.node] != APP) break;
    Port ia = net_dhop(n, wire_at(n, body.node, 0));
    if (!IN_NET(n, ia.node) || n->tag[ia.node] != APP) break;
    slots++;
    cur = wire_at(n, body.node, 2);
  }
  return slots;
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
  int slots = spine_slot_count(n, argp);
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
  int slots = spine_slot_count(n, argp);
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

/* ====================================================================== *
 *  The parked set: the waiting policy, and the only state this driver keeps.
 *
 *  A pair this driver claimed but cannot fold YET is parked here instead of
 *  being β-squashed (see the header comment: that β is what produced `=> 1`
 *  for `(div (mul 150 150) 100)`).  It stays out of the wave until the core's
 *  active list drains, at which point `drain` re-enqueues it — by then the
 *  operand's own redexes have run, so the value is usually readable.
 *
 *  Keying is by `Net *`, which is only a key: def_precompile reduces
 *  short-lived STACK Nets, so an address can come back around and a stale slot
 *  would otherwise re-enqueue garbage into an unrelated net.  Two defences:
 *  a fingerprint of the net's own arrays (a reused address with fresh arrays
 *  fails it), and validating EVERY pair against the live net before use
 *  (in-range, not dead, still principal-connected LAM×APP) — a pair from a
 *  smaller net fails that.  Never park while `lin_precompile_depth > 0`, so
 *  precompile nets never enter this table at all.
 * ====================================================================== */
#define ARITH_PARK_SLOTS   8
#define ARITH_DEFER_BUDGET (1L << 15)     /* the evicted core's `declines < (1<<15)` bound */

typedef struct {
  const Net *net;                          /* key; never dereferenced unless it IS the live net */
  const unsigned char *fp_tag, *fp_dead;   /* fingerprint of the keyed net (fresh arrays per net_init) */
  const Port *fp_wire; const Scope *fp_scope; char *const *fp_name; int fp_nn;
  Port *pairs; int npark, pcap;
  long tries;                              /* deferral rounds spent on this net */
} ParkSlot;

static ParkSlot arith_park[ARITH_PARK_SLOTS];
static unsigned arith_park_rr;

static int pair_live(const Net *n, Port a, Port b);   /* fwd: slot_find re-validates parked pairs */

static void slot_forget(ParkSlot *s) { free(s->pairs); memset(s, 0, sizeof *s); }

/* 1 if `s` is still keyed to exactly this net (same address AND same arrays) */
static int slot_is_keyed(const ParkSlot *s, const Net *n) {
  return s->net == n && s->fp_tag == n->tag && s->fp_wire == n->wire && s->fp_dead == n->dead &&
         s->fp_scope == n->scope && s->fp_name == n->name && s->fp_nn == n->nn;
}
static void slot_key(ParkSlot *s, const Net *n) {
  s->net = n; s->fp_tag = n->tag; s->fp_wire = n->wire; s->fp_dead = n->dead;
  s->fp_scope = n->scope; s->fp_name = n->name; s->fp_nn = n->nn;
}
/* the slot keyed to `n`, or NULL; a slot whose key address was reused by a different
   net (fingerprint mismatch) is dropped rather than trusted */
static ParkSlot *slot_find(const Net *n) {
  for (int i = 0; i < ARITH_PARK_SLOTS; i++) {
    ParkSlot *s = &arith_park[i];
    if (!s->net || s->net != n) continue;
    if (slot_is_keyed(s, n)) return s;                    /* same net, arrays unmoved */
    /* The arrays moved: either this net grew and the allocator moved them (the common
       case — a parked redex outlives plenty of net_alloc), or a DIFFERENT net now lives
       at this address.  Re-key only if every parked pair is still a live redex of this
       net; a pair that is not cannot be re-enqueued anyway, and re-keying on a genuine
       redex is harmless even in the aliasing case (the core processes valid pairs). */
    int ok = s->npark > 0;
    for (int j = 0; j < s->npark && ok; j += 2) ok = pair_live(n, s->pairs[j], s->pairs[j + 1]);
    if (!ok) { slot_forget(s); return NULL; }
    slot_key(s, n);
    return s;
  }
  return NULL;
}
/* the slot keyed to `n`, creating one (evicting the least useful) if needed */
static ParkSlot *slot_get(const Net *n) {
  ParkSlot *s = slot_find(n);
  if (s) return s;
  s = NULL;
  for (int i = 0; i < ARITH_PARK_SLOTS; i++) if (!arith_park[i].net) { s = &arith_park[i]; break; }
  if (!s) s = &arith_park[arith_park_rr++ % ARITH_PARK_SLOTS];   /* full: parking is best-effort */
  slot_forget(s);
  slot_key(s, n);
  return s;
}

/* still a live, principal-connected `_op`/`_ffi` closure redex in this net? */
static int pair_live(const Net *n, Port a, Port b) {
  if (a.port || b.port) return 0;
  if (!IN_NET(n, a.node) || !IN_NET(n, b.node)) return 0;
  if (n->dead[a.node] || n->dead[b.node]) return 0;
  if (net_wire(n, a).node != b.node || net_wire(n, a).port != b.port) return 0;
  if (net_wire(n, b).node != a.node || net_wire(n, b).port != a.port) return 0;
  int lam;
  if (n->tag[a.node] == LAM && n->tag[b.node] == APP) lam = a.node;
  else if (n->tag[b.node] == LAM && n->tag[a.node] == APP) lam = b.node;
  else return 0;
  int c = ctor_tag(nmof(n, lam));
  return c == DT_OP || c == DT_FFI;
}

/* hold `a`/`b` out of the wave until the next drain; 0 if it could not be held */
static int park_push(Net *n, Port a, Port b) {
  ParkSlot *s = slot_get(n);
  for (int i = 0; i < s->npark; i += 2)
    if (s->pairs[i].node == a.node && s->pairs[i + 1].node == b.node) return 1;   /* already parked */
  if (s->npark + 2 > s->pcap) {
    int nc = s->pcap ? s->pcap * 2 : 32;
    Port *np = realloc(s->pairs, (size_t)nc * sizeof(Port));
    if (!np) return 0;
    s->pairs = np; s->pcap = nc;
  }
  s->pairs[s->npark++] = a; s->pairs[s->npark++] = b;
  return 1;
}

/* ---- LinDriver hooks ---- */

/* claim: a DT_OP/DT_FFI closure redex this driver will fold now or PARK.  The core
   hands wave pairs in tag order, so normalise LAM-first here.  Nothing is claimed
   that `reduce` cannot then handle — a claimed-but-unhandled pair is dropped from
   the wave and stranded. */
static int arith_claim(const Net *ncn, Port p1, Port p2) {
  Net *n = (Net *)ncn;
  if (p1.port || p2.port) return 0;
  if (!IN_NET(n, p1.node) || !IN_NET(n, p2.node)) return 0;
  if (n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (net_wire(n, p1).node != p2.node || net_wire(n, p1).port != p2.port) return 0;
  if (net_wire(n, p2).node != p1.node || net_wire(n, p2).port != p1.port) return 0;
  int lam, app;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) { lam = p1.node; app = p2.node; }
  else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) { lam = p2.node; app = p1.node; }
  else return 0;
  int c = ctor_tag(nmof(n, lam));
  if (c == DT_OP) {
    char fn[256];
    if (!op_fn_from_tag(nmof(n, lam), fn, sizeof fn)) return 0;
  } else if (c != DT_FFI) return 0;

  /* Open free-variable body (def_precompile): the operands are free vars that never
     become concrete, so folding here would bake a closure around a stale value.
     Report the net as not-a-value instead — this is the relocated
     `lin_stuck_ffi_count` decline: def_precompile then keeps the def textual, which is
     what lets a def that merely CALLS a recursive def keep widening (a baked net freezes
     the unrolling depth).  The pair is left to the core's plain β. */
  if (lin_precompile_depth > 0) { lin_pending_bump(n); return 0; }

  Val v;
  int ev = (c == DT_OP) ? op_eval(n, lam, app, &v) : ffi_eval(n, lam, &v, NULL, 0);
  if (ev == EV_READY) return 1;
  if (ev != EV_WAIT) return 0;                     /* not foldable by us at all: the core β's it */
  /* Foldable class, operand not concrete yet: park it rather than let β squash the
     operand sub-net.  Past the deferral budget stop claiming, so the core β's it and
     the redex is guaranteed to be consumed either way. */
  ParkSlot *s = slot_find(n);
  long tries = s ? s->tries : 0;
  return tries < ARITH_DEFER_BUDGET;
}

/* reduce: fold each claimed redex, or park it if it is not ready yet.  The ABI hands a
   slice of PAIRS: `nred` counts pairs, `redexes` holds 2*nred ports. */
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
    if (ev == EV_READY) {
      if (c == DT_OP) fold_op_head(n, lam, app, &v); else fold_ffi_head(n, lam, app, &v);
      done++; (*changed)++; n->steps++;
      continue;
    }
    if (ev == EV_WAIT && lin_precompile_depth == 0) {
      ParkSlot *s = slot_find(n);
      if (!s || s->tries < ARITH_DEFER_BUDGET) {
        if (park_push(n, (Port){lam, 0}, (Port){app, 0})) {
          /* a deferral spends a step, exactly as the evicted core's did: the core's
             drain-loop livelock guard keys on progress in `steps`. */
          (*changed)++; n->steps++;
          continue;
        }
      }
    }
    /* Not foldable and not parkable (precompile body, budget exhausted, or the shape
       moved under us): hand the redex to the core's own β rather than strand it. */
    if (lin_precompile_depth > 0) lin_pending_bump(n);
    if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
  }
  return done;
}

/* arg_fold: the ARGUMENT edge β is about to substitute.  A saturated closure in an
   argument position (`succ (mul 2 2)`) is never a principal×principal redex, so the
   core offers it here: materialise its value at `target` and the substitution binds a
   concrete scalar instead of a closure that β would duplicate unfolded.
   Ports of the evicted lin_fold_op_arg / lin_fold_ffi_arg.  Only int/bool values are
   re-linked mid-β — float values are box-index encoded and stay on head-fold/readback
   (the evicted code documents why), and an `_ffi` argument is eager-foldable only for
   `lin_ffloor`, the sole int-result `_ffi` op. */
static int arith_arg_fold(Net *n, Port arg, Port target) {
  if (arg.node < 0 || arg.port != 0 || arg.node >= n->nn || n->dead[arg.node]) return 0;
  int lam = -1, redex = -1, is_ffi = 0;
  if (n->tag[arg.node] == LAM) {
    int c = ctor_tag(nmof(n, arg.node));
    if (c == DT_OP) {
      Port r = wire_at(n, arg.node, 0);            /* the APP this LAM is applied to */
      if (!IN_NET(n, r.node) || r.port != 0 || n->dead[r.node] || n->tag[r.node] != APP) return 0;
      lam = arg.node; redex = r.node;
    } else if (c == DT_FFI) { is_ffi = 1; lam = arg.node; }
    else return 0;
  } else if (n->tag[arg.node] == APP) {
    Port h = wire_at(n, arg.node, 0);              /* an APP-headed `_op` redex */
    if (!IN_NET(n, h.node) || h.port != 0 || n->dead[h.node] || n->tag[h.node] != LAM) return 0;
    if (ctor_tag(nmof(n, h.node)) != DT_OP) return 0;
    lam = h.node; redex = arg.node;
  } else return 0;

  if (is_ffi) {
    char fn[256];
    Val v;
    if (ffi_eval(n, lam, &v, fn, sizeof fn) != EV_READY) return 0;
    if (strcmp(fn, "lin_ffloor")) return 0;             /* only the int-result `_ffi` op folds eagerly */
    if (v.kind != 1 && v.kind != 3) return 0;
    Port res = val_to_port(n, &v);
    n->dead[lam] = 1;
    net_link(n, res, target, 1);
    lin_fold_bump();
    return 1;
  }

  Val v;
  if (op_eval(n, lam, redex, &v) != EV_READY) return 0;
  if (v.kind != 1 && v.kind != 3) return 0;             /* int/bool values re-link safely mid-β */
  Port res = val_to_port(n, &v);
  Port body = wire_at(n, lam, 2);                  /* the pure-Lin β-body residual */
  Port aa = wire_at(n, redex, 2);                  /* the operand spine */
  n->dead[lam] = 1; n->dead[redex] = 1;
  fold_own(n, body); fold_own(n, aa);
  net_link(n, res, target, 1);
  lin_fold_bump();
  return 1;
}

/* materialize: the readback pre-pass.  A saturated closure can survive reduction
   embedded where a numeral is expected (the `n` of `\_sz \_ss (_ss (mul 2 2))`, which
   no β redex ever reaches); give the reader a concrete Scott numeral so the spine
   decodes.  Ports the evicted read_int_peek: pure int values only, allocation only
   (the closure itself is left in place). */
static int arith_materialize(Net *n, Port p, Port *out) {
  if (p.node < 0 || p.port != 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;
  int c = ctor_tag(nmof(n, p.node));
  Val v; int ev = EV_NO;
  if (c == DT_FFI) ev = ffi_eval(n, p.node, &v, NULL, 0);
  else if (c == DT_OP) {
    Port r = wire_at(n, p.node, 0);
    if (!IN_NET(n, r.node) || r.port != 0 || n->dead[r.node] || n->tag[r.node] != APP) return 0;
    ev = op_eval(n, p.node, r.node, &v);
  } else return 0;
  if (ev != EV_READY) return 0;
  if (v.kind != 1 || v.iv < 0) return 0;                /* int-valued only: a bool here is not a numeral */
  *out = net_alloc_scott(n, v.iv);
  return 1;
}

/* drain: the active wave emptied.  Re-enqueue every parked pair for `n` that is still
   a live principal-connected closure redex, drop the ones some other rewrite consumed,
   and report how many went back in — the core loops while this is > 0.  A re-enqueued
   pair is re-parked by the next wave if it is still not ready (claim parks it again),
   so nothing is dropped on the floor here: past the deferral budget claim refuses it
   and the core β's it.  An emptied slot is released, so a freed stack Net's address
   can never be mistaken for a later net's. */
static int arith_drain(Net *n) {
  ParkSlot *s = slot_find(n);
  if (!s || s->npark <= 0) return 0;
  int re = 0;
  for (int i = 0; i < s->npark; i += 2) {
    Port a = s->pairs[i], b = s->pairs[i + 1];
    /* Re-enqueue every pair whose NODES are still alive -- deliberately NOT the strict
       structural `pair_live` test.  This is the only place a parked pair is ever put
       back, so dropping one is unrecoverable: the redex would be neither folded (its
       operand never became concrete in the driver's view) nor β-reduced (the core
       never saw it again), it would simply sit in the net, and readback would show the
       closure still applied to its spine with the body reduced -- the `((\_add 13)
       <spine>)` residual.  A pair whose shape shifted under it (another redex rewired
       one of its ports) is therefore put back anyway and re-evaluated by the core; only
       a consumed/destroyed node means there is genuinely nothing left to wait for.
       The evicted core's blocked-list drain did exactly this: one liveness check, then
       re-add everything. */
    if (!IN_NET(n, a.node) || !IN_NET(n, b.node)) continue;
    if (n->dead[a.node] || n->dead[b.node]) continue;
    lin_enqueue(n, a, b);
    re++;
  }
  s->npark = 0;              /* pairs are back in the wave; re-parked there if still pending */
  s->tries += re;            /* one deferral round per retried pair */
  if (re == 0) { slot_forget(s); return 0; }             /* nothing left: drop the key with the pairs */
  return re;
}

/* pending: 1 while a parked redex for `n` is still live, i.e. this reduction has not
   reached a value — def_precompile must not bake such a net.  (The precompile decline
   itself rides Net.driver_pending via lin_pending_bump; this covers a net that ended
   its reduction with work still parked.) */
static int arith_pending(const Net *n) {
  ParkSlot *s = slot_find(n);
  if (!s) return 0;
  for (int i = 0; i < s->npark; i += 2)
    if (pair_live(n, s->pairs[i], s->pairs[i + 1])) return 1;
  return 0;
}

/* ---- registration ----
   Two roles in one plugin:
     - lin_arith_scalar is the shared SEMANTIC authority every strategy calls;
     - lin_arith_driver is the fold PRE-EMPTOR (LIN_CAP_PREEMPT, priority 5, ahead of
       simd's 10) that claims folded redexes before any strategy sees them.  A pre-emptor
       composes with whichever strategy is selected: lin_driver_clear (what `(set_driver
       ...)` calls) drops strategies but keeps pre-emptors.
   main.c dlopens std/drivers/arith.so at startup via lin_scalar_ops_load("arith"), so
   the pre-emptor is always present even with no driver selected. */
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
  .arg_fold = arith_arg_fold, .materialize = arith_materialize,
  .drain = arith_drain, .pending = arith_pending,
};
