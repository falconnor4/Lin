#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>
#include <dlfcn.h>

#define SIMD_WIDTH 8
#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
static Port WP(Net *n, int node, int port) { return n->wire[node * 3 + port]; }

/* ---------------------------------------------------------------------- *
 *  Native small-integer arithmetic within the SIMD reducer.
 *
 *  std/drivers/native.lin routes the scalar arithmetic / comparison
 *  primitives through the FFI closure representation, so each operation
 *  reduces to a saturated datum of the shape
 *        \_ffi. \_ret. ((_ffi "lin_*") args)
 *  whose argument list is a `_cl`-spine of Scott numerals.  When such a
 *  datum is applied (a LAM/APP redex on the active wave), this driver
 *  folds it in C: it evaluates the operation over native machine integers
 *  and rewires the result back into the net as a Scott numeral or Church
 *  boole, so the Scott-level consumers around it (and, ifl, min, max, ...)
 *  keep interacting instead of stalling.  The base engine is untouched;
 *  all native-arithmetic logic lives in this driver file.
 * ---------------------------------------------------------------------- */

static const char *nm(Net *n, int id) { return n->name[id] ? n->name[id] : ""; }

/* Shared on-net FFI decoder (std/runtime/decoder.c), resolved once through the
   exported core symbols, so this driver does NOT re-implement the DUP-hop /
   `_cl`-spine arg walk. */
static int (*g_ffi_fn)(Net *, Port, char *, int);
static int (*g_ffi_args)(Net *, Port, Val *, int);
static void resolve_decoder(void) {
  if (!g_ffi_fn) g_ffi_fn = (int (*)(Net *, Port, char *, int))dlsym(RTLD_DEFAULT, "net_ffi_fn");
  if (!g_ffi_args) g_ffi_args = (int (*)(Net *, Port, Val *, int))dlsym(RTLD_DEFAULT, "net_ffi_args");
}

/* Evaluate a single `_ffi` closure whose args are saturated (recursively),
   returning 1 and storing value/type, else 0.  is_bool: result is a Church
   boole; is_float: result is an IEEE-754 double (bits carried in *v as long).
   Decoding + fn lookup go through the SHARED decoder; the arithmetic semantics
   go through the ONE shared scalar-op table (lin_arith_scalar, arith.so). */
static ScalarOpFn g_scalar;
static ScalarOpFn scalar_table(void) {
  if (!g_scalar) g_scalar = (ScalarOpFn)dlsym(RTLD_DEFAULT, "lin_arith_scalar");
  return g_scalar;
}
static int ev_ffi(Net *n, Port p, long *v, int *is_bool, int *is_float) {
  resolve_decoder();
  char fn[256];
  if (!g_ffi_fn || !g_ffi_fn(n, (Port){p.node, 0}, fn, sizeof(fn))) return 0;
  Val vals[2]; int na = g_ffi_args ? g_ffi_args(n, (Port){p.node, 0}, vals, 2) : 0;
  long a[2] = {0, 0};
  for (int i = 0; i < na && i < 2; i++) a[i] = vals[i].iv;
  *is_bool = 0; *is_float = 0;
  if (na < 1) return 0;
  ScalarOpFn tab = scalar_table();
  if (!tab) return 0;                        /* no shared arithmetic table loaded */
  long out; int okind = 0;
  if (!tab(fn, na, a, &out, &okind)) return 0;
  if (okind == 4) { memcpy(v, &out, 8); *is_float = 1; }
  else if (okind == 3) { *v = out; *is_bool = 1; }
  else *v = out;
  return 1;
}

/* Fold a saturated `_ffi` arithmetic closure `lam` applied to `app`.
   On success rewires the numeric/boole result and returns 1, else 0. */
static int simd_fold_ffi(Net *n, int lam, int app) {
  long v; int is_bool = 0, is_float = 0;
  if (!ev_ffi(n, (Port){lam, 0}, &v, &is_bool, &is_float)) return 0;

  Port res;
  if (is_bool) res = net_alloc_bool(n, (int)v);
  else if (is_float) { double d; memcpy(&d, &v, 8); res = net_alloc_float(n, d); }
  else res = net_alloc_scott(n, v);
  /* Substitute the computed datum for the `_ffi` closure: the consumer APP is
     kept alive and re-paired with `res`, so the ordinary LAM/APP rule (a
     Church-boole / Scott-numeral / float-box application) completes the
     selection in a later wave rather than expanding the closure step by step. */
  n->dead[lam] = 1;
  net_link(n, res, (Port){app, 0}, 1);
  lin_fold_bump();
  return 1;
}

/* claim: a saturated `_ffi` arithmetic closure (LAM x APP) — the native-num
   class this driver folds.  Side-effect free; used to partition the wave. */
static int simd_claim(const Net *n, Port p1, Port p2) {
  const char *nmc(const Net *nn, int id) {
    return (id >= 0 && id < nn->nn && nn->name[id]) ? nn->name[id] : "";
  }
  if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (p1.port || p2.port) return 0;
  if (WIRE(n,p1).node != p2.node || WIRE(n,p1).port != p2.port) return 0;
  if (WIRE(n,p2).node != p1.node || WIRE(n,p2).port != p1.port) return 0;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP)
    return ctor_tag(nmc(n, p1.node)) == DT_FFI;
  if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP)
    return ctor_tag(nmc(n, p2.node)) == DT_FFI;
  return 0;
}

/* reduce: fold every native-num redex in this slice (already claimed) into a
   native machine-int result.  Returns redexes consumed. */
static int simd_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int consumed = 0;
  for (int i = 0; i < nred; i++) {
    if (n->steps >= limit) return consumed;
    Port p1 = redexes[i*2], p2 = redexes[i*2+1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node] || p1.port || p2.port) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    int folded = 0;
    if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP)
      folded = simd_fold_ffi(n, p1.node, p2.node);
    else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP)
      folded = simd_fold_ffi(n, p2.node, p1.node);
    if (folded) { consumed++; (*changed)++; n->steps++; }
  }
  return consumed;
}

LinDriver lin_simd_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI,
  .name = "simd", .description = "native small-integer Scott arithmetic fold",
  .caps = LIN_CAP_NATIVE_NUM, .priority = 10,
  .claim = simd_claim, .reduce = simd_reduce,
};