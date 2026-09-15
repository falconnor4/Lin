#include "../../src/lin.h"
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

static const char *nm(Net *n, int id) { return n->name[id] ? n->name[id] : ""; }

/* Resolve exported core helpers once through dlsym (-rdynamic exports them). */
static ScalarOpFn g_scalar;
static int (*g_spine)(Net *, Port, Val *, int);
static void resolve_core(void) {
  if (!g_scalar) g_scalar = (ScalarOpFn)dlsym(RTLD_DEFAULT, "lin_arith_scalar");
  if (!g_spine) g_spine = (int (*)(Net *, Port, Val *, int))dlsym(RTLD_DEFAULT, "net_spine_args");
}

/* derive the shared-table scalar op name from a DT_OP carrier tag (`_add` -> "lin_add") */
static void op_tag_to_fn(const char *tag, char *fn, int fnmax) {
  if (!tag || tag[0] != '_') { fn[0] = 0; return; }
  snprintf(fn, fnmax, "lin_%s", tag + 1);
}

/* decode + evaluate a saturated `_op` redex LAM `lam` x APP `app`; on success
   (concrete operands + claimed op) fills *v and returns 1.  Mirrors the shared
   `lin_fold_op` value path (net_spine_args + lin_arith_scalar). */
static int simd_op_value(Net *n, Port lam, Port app, Val *v) {
  char fn[256];
  op_tag_to_fn(n->name[lam.node] ? n->name[lam.node] : "", fn, sizeof fn);
  if (!fn[0]) return 0;
  if (!g_spine) resolve_core();
  if (!g_spine) return 0;
  Port argp = WIRE(n, ((Port){app.node, 2}));         /* the applied `_cl`-spine */
  Val fargs[8] = {{0}};
  int argc = g_spine(n, argp, fargs, 8);
  if (argc < 1) return 0;
  long c_args[8] = {0};
  for (int i = 0; i < argc; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return 0;
    c_args[i] = fargs[i].iv;
  }
  long out; int okind = 0;
  if (!g_scalar) resolve_core();
  if (!g_scalar || !g_scalar(fn, argc, c_args, &out, &okind)) return 0;
  if (okind == 4) v->kind = 4; else if (okind == 3) v->kind = 3; else v->kind = 1;
  v->iv = out;
  return 1;
}

/* Pure readiness predicate used by claim: could SIMD fold this `_op` redex now?
   Only claim when every operand is concrete and the shared scalar op is
   claimed; otherwise leave it to the base engine (which defers non-concrete
   operands) rather than strand the redex. */
static int simd_op_ready(const Net *n, Port lam, Port app) {
  char fn[256];
  op_tag_to_fn(n->name[lam.node] ? n->name[lam.node] : "", fn, sizeof fn);
  if (!fn[0]) return 0;
  if (!g_spine) resolve_core();
  if (!g_spine) return 0;
  Port argp = n->wire[app.node * 3 + 2];
  Val fargs[8] = {{0}};
  int argc = g_spine((Net *)n, argp, fargs, 8);
  if (argc < 1) return 0;
  long c_args[8] = {0};
  for (int i = 0; i < argc; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return 0;
    c_args[i] = fargs[i].iv;
  }
  long out; int okind = 0;
  if (!g_scalar) resolve_core();
  return g_scalar && g_scalar(fn, argc, c_args, &out, &okind);
}

/* Fold a saturated pure-Lin `_op` closure natively.  Mirrors src/io.c
   `lin_fold_op`: substitute the concrete result for the saturated redex (kill
   LAM, beta-body residual, operand spine) and thread the value out through the
   APP port-1 body-slot partner so the consuming beta continues on the datum. */
static int simd_fold_op(Net *n, int lam, int app) {
  Val v;
  if (!simd_op_value(n, (Port){lam, 0}, (Port){app, 0}, &v)) return 0;
  Port res;
  if (v.kind == 4) { double d; memcpy(&d, &v.iv, 8); res = net_alloc_float(n, d); }
  else if (v.kind == 3) res = net_alloc_bool(n, (int)v.iv);
  else res = net_alloc_scott(n, v.iv);
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
  return 1;
}

/* Fold a saturated `_ffi` closure `lam` applied to `app` (float / legacy FFI).
   Mirrors `lin_fold_ffi`: rewire the concrete datum to the consumer APP head. */
static int (*g_ffi_fn)(Net *, Port, char *, int);
static int (*g_ffi_args)(Net *, Port, Val *, int);
static void resolve_decoder(void) {
  if (!g_ffi_fn) g_ffi_fn = (int (*)(Net *, Port, char *, int))dlsym(RTLD_DEFAULT, "net_ffi_fn");
  if (!g_ffi_args) g_ffi_args = (int (*)(Net *, Port, Val *, int))dlsym(RTLD_DEFAULT, "net_ffi_args");
}
static int ev_ffi(Net *n, Port p, long *v, int *is_bool, int *is_float) {
  resolve_decoder();
  char fn[256];
  if (!g_ffi_fn || !g_ffi_fn(n, (Port){p.node, 0}, fn, sizeof fn)) return 0;
  Val vals[2]; int na = g_ffi_args ? g_ffi_args(n, (Port){p.node, 0}, vals, 2) : 0;
  long a[2] = {0, 0};
  for (int i = 0; i < na && i < 2; i++) a[i] = vals[i].iv;
  *is_bool = 0; *is_float = 0;
  if (na < 1) return 0;
  if (!g_scalar) resolve_core();
  if (!g_scalar) return 0;
  long out; int okind = 0;
  if (!g_scalar(fn, na, a, &out, &okind)) return 0;
  if (okind == 4) { memcpy(v, &out, 8); *is_float = 1; }
  else if (okind == 3) { *v = out; *is_bool = 1; }
  else *v = out;
  return 1;
}
static int simd_fold_ffi(Net *n, int lam, int app) {
  long v; int is_bool = 0, is_float = 0;
  if (!ev_ffi(n, (Port){lam, 0}, &v, &is_bool, &is_float)) return 0;
  Port res;
  if (is_bool) res = net_alloc_bool(n, (int)v);
  else if (is_float) { double d; memcpy(&d, &v, 8); res = net_alloc_float(n, d); }
  else res = net_alloc_scott(n, v);
  n->dead[lam] = 1;
  net_link(n, res, (Port){app, 0}, 1);
  lin_fold_bump();
  return 1;
}

/* claim: a saturated DT_OP (`_op` pure-Lin arith) or DT_FFI (`_ffi` float/legacy)
   closure (LAM x APP), the native-num class this driver folds.  DT_OP claims
   additionally gate on operand readiness so we never strand an unfoldable redex. */
static int simd_claim(const Net *n, Port p1, Port p2) {
  const char *nmc(const Net *nn, int id) {
    return (id >= 0 && id < nn->nn && nn->name[id]) ? nn->name[id] : "";
  }
  if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (p1.port || p2.port) return 0;
  if (WIRE(n,p1).node != p2.node || WIRE(n,p1).port != p2.port) return 0;
  if (WIRE(n,p2).node != p1.node || WIRE(n,p2).port != p1.port) return 0;
  int t;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) {
    t = ctor_tag(nmc(n, p1.node));
    if (t == DT_OP) return simd_op_ready(n, (Port){p1.node,0}, (Port){p2.node,0});
    return t == DT_FFI;
  }
  if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) {
    t = ctor_tag(nmc(n, p2.node));
    if (t == DT_OP) return simd_op_ready(n, (Port){p2.node,0}, (Port){p1.node,0});
    return t == DT_FFI;
  }
  return 0;
}

/* reduce: fold every claimed native-num redex in this slice (already claimed).
   Since claim only admitted ready redexes, simd_fold_* should succeed; a failed
   fold is not counted.  Returns redexes consumed. */
static int simd_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int consumed = 0;
  for (int i = 0; i < nred; i++) {
    if (n->steps >= limit) return consumed;
    Port p1 = redexes[i*2], p2 = redexes[i*2+1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node] || p1.port || p2.port) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    int lam, app, folded = 0;
    if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) { lam = p1.node; app = p2.node; }
    else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) { lam = p2.node; app = p1.node; }
    else continue;
    int c = ctor_tag(nm(n, lam));
    if (c == DT_OP) folded = simd_fold_op(n, lam, app);
    else if (c == DT_FFI) folded = simd_fold_ffi(n, lam, app);
    if (folded) { consumed++; (*changed)++; n->steps++; }
  }
  return consumed;
}

LinDriver lin_simd_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "simd", .description = "native scalar (`_op`/`_ffi`) arithmetic fold",
  .caps = LIN_CAP_NATIVE_NUM, .priority = 10,
  .claim = simd_claim, .reduce = simd_reduce,
};