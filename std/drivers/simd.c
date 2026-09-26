#include "../../src/lin.h"
#include "../runtime/pattern.h"     /* the structural recognisers and the op vocabulary (LIN_OP_*) */
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <dlfcn.h>

#define SIMD_WIDTH 8
#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

/* ---------------------------------------------------------------------- *
 *  Native scalar arithmetic within the SIMD reducer (current engine).
 *
 *  Since the "integer arithmetic is pure Lin" migration, the scalar ops are
 *  driver-foldable `_op` closures (std/num.lin): a saturated op like
 *  `(add 4 3)` reduces to `((\_add <pure-Lin-beta-body>) <_cl-spine>)`, a
 *  DT_OP-named LAM x APP redex on the active wave.  The base engine folds
 *  these itself in `net_interact` via `lin_fold_op`; THIS driver claims the
 *  same saturated `_op` redexes from the wave first (priority 10) and folds
 *  them natively through the ONE shared scalar table (arith.so), so the SIMD
 *  reducer does the integer arithmetic the base engine would otherwise do.
 *  Float `_ffi` closures are also claimed and folded (the `_ffi` arm).
 *
 *  Correctness: the base engine is the oracle.  The net-side rewiring mirrors
 *  `lin_fold_op`/`lin_fold_ffi` exactly and the arithmetic comes only from the
 *  shared scalar table, so a SIMD fold is bit-identical to the base fold and
 *  to pure-Lin beta reduction.  A driver must CLAIM ONLY redexes it can fold
 *  RIGHT NOW (concrete operands + a claimed op): a claimed-but-unfolded redex
 *  would be removed from the wave, and stranding it would corrupt the run, so
 *  `claim` runs the same readiness predicate the fold uses.  Non-ready `_op`
 *  operands are left to the base engine, which DEFERS them (bounded) until
 *  concrete.
 *  ---------------------------------------------------------------------- */

/* Resolve exported core helpers once through dlsym (-rdynamic exports them).  The spine decoder's
   per-slot expectation travels with the call: EVERY scalar operand here is a number, and a slot that
   is not one in its own structure is declined rather than guessed.
   The SEMANTICS are not resolved here: they come from the core's registry (`lin_scalar_ops_run`),
   because that is where a provider states whether a call to it is a function of its operands alone.  A
   driver that dlsym'd the provider's own symbol would perform calls the provider never vouched for as
   pure -- which a build may not do -- and it would be blind to a provider not loaded yet, where the
   registry is what loads it. */
static int (*g_spine)(Net *, Port, const int *, int, Val *, int);
static const int DOMS_NUM[1] = { DT_NUM };
static void resolve_core(void) {
  if (!g_spine) g_spine = (int (*)(Net *, Port, const int *, int, Val *, int))dlsym(RTLD_DEFAULT, "net_spine_args");
}

/* Which operator is this `_op` redex?  The OPERATOR INDEX is the first slot of its operand list
   (std/num.lin writes it; LIN_OP_* is the enumeration) -- a net carries no label, so `((\_op body)
   spine)` for add and for mul are one shape.  FORCING, which is why `claim` may not call it. */
static int op_head_of(Net *n, Port app, const char **fn, Port *ops) {
  Port head, tail;
  *fn = NULL;
  *ops = (Port){-1, 0};
  if (app.node < 0 || app.node >= n->nn || n->dead[app.node] || n->tag[app.node] != APP) return 0;
  if (!net_read_cell(n, WIRE(n, ((Port){app.node, 2})), &head, &tail)) return 0;
  *fn = lin_op_fn((int)net_read_int(n, head, LIN_ENC_NUM));
  *ops = tail;
  return *fn != NULL;
}

/* decode + evaluate a saturated `_op` redex LAM `lam` x APP `app`; on success
   (concrete operands + claimed op) fills *v and returns 1.  Mirrors the shared
   `lin_fold_op` value path (net_spine_args + lin_arith_scalar). */
static int simd_op_value(Net *n, Port lam, Port app, Val *v) {
  (void)lam;
  const char *fn;
  Port argp;
  if (!op_head_of(n, app, &fn, &argp)) return 0;      /* the operator index, and the operands after it */
  if (!g_spine) resolve_core();
  if (!g_spine) return 0;
  Val fargs[8] = {{0}};
  int argc = g_spine(n, argp, DOMS_NUM, 1, fargs, 8);
  if (argc < 1) return 0;
  long c_args[8] = {0};
  for (int i = 0; i < argc; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return 0;
    c_args[i] = fargs[i].iv;
  }
  long out; int okind = 0;
  if (!lin_scalar_ops_run(fn, argc, c_args, &out, &okind)) return 0;
  if (okind == 4) v->kind = 4; else if (okind == 3) v->kind = 3; else v->kind = 1;
  v->iv = out;
  return 1;
}

/* Pure readiness predicate used by claim: could SIMD fold this `_op` redex now?
   Only claim when every operand is concrete and the shared scalar op is
   claimed; otherwise leave it to the base engine (which defers non-concrete
   operands) rather than strand the redex. */
static int simd_op_ready(const Net *n, Port lam, Port app) {
  (void)lam;
  char fn[256];
  const char *f;
  Port argp;
  if (!op_head_of((Net *)n, app, &f, &argp)) return 0;
  snprintf(fn, sizeof fn, "%s", f);
  if (!g_spine) resolve_core();
  if (!g_spine) return 0;
  Val fargs[8] = {{0}};
  int argc = g_spine((Net *)n, argp, DOMS_NUM, 1, fargs, 8);
  if (argc < 1) return 0;
  long c_args[8] = {0};
  for (int i = 0; i < argc; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return 0;
    c_args[i] = fargs[i].iv;
  }
  long out; int okind = 0;
  return lin_scalar_ops_run(fn, argc, c_args, &out, &okind);
}

/* Fold a saturated `_ffi` closure `lam` applied to `app` (float / legacy FFI).
   Mirrors `lin_fold_ffi`: rewire the concrete datum to the consumer APP head. */
static int (*g_ffi_fn)(Net *, Port, char *, int);
static int (*g_ffi_args)(Net *, Port, const int *, int, Val *, int);
static void resolve_decoder(void) {
  if (!g_ffi_fn) g_ffi_fn = (int (*)(Net *, Port, char *, int))dlsym(RTLD_DEFAULT, "net_ffi_fn");
  if (!g_ffi_args) g_ffi_args = (int (*)(Net *, Port, const int *, int, Val *, int))dlsym(RTLD_DEFAULT, "net_ffi_args");
}
static int ev_ffi(Net *n, Port p, long *v, int *is_bool, int *is_float) {
  resolve_decoder();
  char fn[256];
  if (!g_ffi_fn || !g_ffi_fn(n, (Port){p.node, 0}, fn, sizeof fn)) return 0;
  Val vals[2]; int na = g_ffi_args ? g_ffi_args(n, (Port){p.node, 0}, DOMS_NUM, 1, vals, 2) : 0;
  long a[2] = {0, 0};
  for (int i = 0; i < na && i < 2; i++) a[i] = vals[i].iv;
  *is_bool = 0; *is_float = 0;
  if (na < 1) return 0;
  long out; int okind = 0;
  if (!lin_scalar_ops_run(fn, na, a, &out, &okind)) return 0;
  if (okind == 4) { memcpy(v, &out, 8); *is_float = 1; }
  else if (okind == 3) { *v = out; *is_bool = 1; }
  else *v = out;
  return 1;
}

/* PURE: which head is this redex's LAM?  An `_ffi` closure's body is the `_ret` binder that applies
   the head to itself (the header SHAPE); an `_op` head's body is its pure fallback BODY.  A net
   carries no label, so the shape is the whole of what a name-free net can say -- the same test the
   arith driver makes, because the two must agree on which redexes are theirs. */
static int head_is_ffi(const Net *n, int lam) {
  LinMatch m;
  return lin_pat_match((Net *)n, (Port){lam, 0}, lin_pat_enc_ffi, LIN_PAT_BUDGET_FOR(n), &m);
}

/* claim: a saturated `_op` (pure-Lin arith) or `_ffi` (float/legacy) closure (LAM x APP), the
   native-num class this driver folds.  An `_op` claim additionally gates on operand readiness so an
   unfoldable redex is never stranded. */
static int simd_claim(const Net *n, Port p1, Port p2) {
  if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (p1.port || p2.port) return 0;
  if (WIRE(n,p1).node != p2.node || WIRE(n,p1).port != p2.port) return 0;
  if (WIRE(n,p2).node != p1.node || WIRE(n,p2).port != p1.port) return 0;
  int lam, app;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) { lam = p1.node; app = p2.node; }
  else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) { lam = p2.node; app = p1.node; }
  else return 0;
  if (head_is_ffi(n, lam)) return 1;
  if (!lin_pat_op_head(n, (Port){lam, 0}, NULL)) return 0;
  return simd_op_ready(n, (Port){lam, 0}, (Port){app, 0});
}

/* ---------------------------------------------------------------------- *
 *  SIMD_WIDTH vectorized reduction.
 *
 *  `simd_reduce` processes the claimed `_op`/`_ffi` scalar fold slice in
 *  batches of at most SIMD_WIDTH redexes.  Each batch runs TWO decoupled
 *  passes so the independent value computations can be auto-vectorized and
 *  per-redex overhead (dlsym-pointer checks, branch bookkeeping) is amortized:
 *
 *    Phase A (eval, no net mutation): decode each lane's operands and call the
 *      one shared scalar table, stashing (ok, Val) per lane.  The lanes are
 *      independent and side-effect free, so the compiler is free to SIMD the
 *      scalar-table calls across the batch.
 *    Phase B (apply): rewire each successful lane (kill LAM/body/spine, link
 *      the concrete result) — the net mutation, which must stay sequential.
 *
 *  Correctness is unchanged: the redexes in a driver slice are an independent
 *  (disjoint) set, so evaluating all of a batch's values BEFORE mutating any of
 *  them cannot affect the inputs of the others.  Bit-exactness is preserved
 *  because the value for every lane still comes from the one shared
 *  lin_arith_scalar table and the rewire mirrors lin_fold_op/lin_fold_ffi.
 *  ---------------------------------------------------------------------- */

/* Per-lane result of the eval phase. */
typedef struct { int ok; int lam, app; int kind; int ffi; long iv; } SimdLane;

/* Eval phase for DT_OP: decode + scalar-table the value, no mutation. */
static int simd_eval_op(Net *n, int lam, int app, SimdLane *ln) {
  Val v;
  if (!simd_op_value(n, (Port){lam, 0}, (Port){app, 0}, &v)) return 0;
  ln->kind = v.kind; ln->iv = v.iv; ln->lam = lam; ln->app = app; ln->ok = 1;
  return 1;
}

/* Apply phase for DT_OP: rewire the computed value into the net (mirrors
   simd_fold_op / lin_fold_op). */
static void simd_apply_op(Net *n, SimdLane *ln) {
  Port res;
  if (ln->kind == 4) { double d; memcpy(&d, &ln->iv, 8); res = net_alloc_float(n, d); }
  else if (ln->kind == 3) res = net_alloc_bool(n, (int)ln->iv);
  else res = net_alloc_scott(n, ln->iv);
  int lam = ln->lam, app = ln->app;
  Port ar = WIRE(n, ((Port){app, 1}));
  Port aa = WIRE(n, ((Port){app, 2}));
  Port body = WIRE(n, ((Port){lam, 2}));
  n->dead[lam] = 1; n->dead[app] = 1;
  if (body.node >= 0 && body.node < n->nn) n->dead[body.node] = 1;
  if (aa.node >= 0 && aa.node < n->nn) n->dead[aa.node] = 1;
  if (ar.node >= 0 && ar.node < n->nn && !n->dead[ar.node])
    net_link(n, res, ar, 1);
  else
    net_link(n, res, (Port){app, 1}, 1);
  lin_fold_bump();
}

/* Eval phase for DT_FFI: decode + scalar-table the float/legacy value. */
static int simd_eval_ffi(Net *n, int lam, int app, SimdLane *ln) {
  long v; int is_bool = 0, is_float = 0;
  if (!ev_ffi(n, (Port){lam, 0}, &v, &is_bool, &is_float)) return 0;
  ln->kind = is_float ? 4 : is_bool ? 3 : 1; ln->iv = v;
  ln->lam = lam; ln->app = app; ln->ok = 1;
  return 1;
}

/* Apply phase for DT_FFI (mirrors simd_fold_ffi). */
static void simd_apply_ffi(Net *n, SimdLane *ln) {
  Port res;
  if (ln->kind == 4) { double d; memcpy(&d, &ln->iv, 8); res = net_alloc_float(n, d); }
  else if (ln->kind == 3) res = net_alloc_bool(n, (int)ln->iv);
  else res = net_alloc_scott(n, ln->iv);
  n->dead[ln->lam] = 1;
  net_link(n, res, (Port){ln->app, 0}, 1);
  lin_fold_bump();
}

/* reduce: fold the claimed native-num slice in SIMD_WIDTH batches.  Phase A
   (eval) runs across each batch, then Phase B (apply) rewires the net. */
static int simd_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int consumed = 0;
  int i = 0;
  while (i < nred) {
    if (n->steps >= limit) return consumed;
    /* Phase A: evaluate up to SIMD_WIDTH independent redexes (no mutation). */
    SimdLane batch[SIMD_WIDTH];
    int nb = 0;
    for (; i < nred && nb < SIMD_WIDTH; i++) {
      Port p1 = redexes[i*2], p2 = redexes[i*2+1];
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node] || p1.port || p2.port) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      int lam, app;
      if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) { lam = p1.node; app = p2.node; }
      else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) { lam = p2.node; app = p1.node; }
      else continue;
      int isffi = head_is_ffi(n, lam);
      SimdLane *ln = &batch[nb];
      ln->ok = 0; ln->lam = lam; ln->app = app; ln->ffi = isffi;
      if (!isffi) { if (simd_eval_op(n, lam, app, ln)) nb++; }
      else { if (simd_eval_ffi(n, lam, app, ln)) nb++; }
    }
    /* Phase B: apply the batch's successful lanes (sequential net mutation). */
    for (int k = 0; k < nb; k++) {
      SimdLane *ln = &batch[k];
      if (ln->kind == 4 || ln->kind == 3 || ln->kind == 1) {
        if (!ln->ffi) simd_apply_op(n, ln);
        else simd_apply_ffi(n, ln);
        consumed++; (*changed)++; n->steps++;
      }
    }
  }
  return consumed;
}

LinDriver lin_simd_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),   /* the ABI-5 extension contract: the core reads only these fields */
  .name = "simd", .description = "native scalar (`_op`/`_ffi`) arithmetic fold",
  .caps = LIN_CAP_NATIVE_NUM, .priority = 10,
  .claim = simd_claim, .reduce = simd_reduce,
};