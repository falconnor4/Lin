#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

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

static Port dhop(Net *n, Port p) {
  while (p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP && p.port == 0)
    p = WIRE(n, p);
  return p;
}

static Port ev_arglist(Net *n, Port argp, long out[2], int *nout);

/* Read the fn name of the `_ffi` closure rooted at port p (port 0). */
static int rd_fn(Net *n, Port p, char *fn, int fnmax) {
  Port r = dhop(n, WP(n, p.node, 2));
  if (r.node < 0 || r.port != 0 || n->dead[r.node] || n->tag[r.node] != LAM) return 0;
  Port a2 = dhop(n, WP(n, r.node, 2));
  if (a2.node < 0 || a2.port != 1 || n->dead[a2.node] || n->tag[a2.node] != APP) return 0;
  Port a1 = dhop(n, WP(n, a2.node, 0));
  if (a1.node < 0 || a1.port != 1 || n->dead[a1.node] || n->tag[a1.node] != APP) return 0;
  return net_read_string(n, WP(n, a1.node, 2), fn, (size_t)fnmax) >= 0;
}

/* Evaluate a single `_ffi` closure whose args are saturated (recursively),
   returning 1 and storing value/type, else 0.  is_bool: result is a Church
   boole; is_float: result is an IEEE-754 double (bits carried in *v as long).
   Also used to read an argument, so nested arithmetic composes. */
static int ev_ffi(Net *n, Port p, long *v, int *is_bool, int *is_float) {
  char fn[256];
  if (!rd_fn(n, p, fn, sizeof(fn))) return 0;
  Port r = dhop(n, WP(n, p.node, 2));
  Port a2 = WP(n, r.node, 2);
  if (a2.node < 0) return 0;
  long a[2]; int na = 0; Port argp = WP(n, a2.node, 2);
  ev_arglist(n, argp, a, &na);
  *is_bool = 0; *is_float = 0;

  /* float binary ops: args are IEEE bits carried as longs */
  if      (!strncmp(fn, "lin_fadd", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = x + y; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fsub", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = x - y; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fmul", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = x * y; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fdiv", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = y != 0.0 ? x / y : 0.0; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fpow", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = pow(x, y); memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fatan2", 10)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); double rr = atan2(x, y); memcpy(v, &rr, 8); *is_float = 1; return 1; }
  /* float unary ops */
  if      (!strncmp(fn, "lin_fsqrt", 9)) { if (na < 1) return 0; double x; memcpy(&x, &a[0], 8); double rr = x >= 0.0 ? sqrt(x) : 0.0; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fsin", 8))  { if (na < 1) return 0; double x; memcpy(&x, &a[0], 8); double rr = sin(x); memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_fcos", 8))  { if (na < 1) return 0; double x; memcpy(&x, &a[0], 8); double rr = cos(x); memcpy(v, &rr, 8); *is_float = 1; return 1; }
  else if (!strncmp(fn, "lin_ftan", 8))  { if (na < 1) return 0; double x; memcpy(&x, &a[0], 8); double rr = tan(x); memcpy(v, &rr, 8); *is_float = 1; return 1; }
  /* float comparisons -> bool */
  if      (!strncmp(fn, "lin_feq", 7))  { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); *v = x == y; *is_bool = 1; return 1; }
  else if (!strncmp(fn, "lin_flt", 7))  { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); *v = x < y;  *is_bool = 1; return 1; }
  else if (!strncmp(fn, "lin_fleq", 8)) { if (na < 2) return 0; double x, y; memcpy(&x, &a[0], 8); memcpy(&y, &a[1], 8); *v = x <= y; *is_bool = 1; return 1; }
  /* int/string <-> float coercion */
  if (!strncmp(fn, "lin_float", 9)) { double rr = (double)a[0]; memcpy(v, &rr, 8); *is_float = 1; return 1; }
  if (!strncmp(fn, "lin_ffloor", 10)) { double x; memcpy(&x, &a[0], 8); *v = (long)floor(x); return 1; }

  if (na < 2) return 0; /* every scalar lin_* op needs both saturated args */
  if      (!strncmp(fn, "lin_add", 7)) *v = a[0] + a[1];
  else if (!strncmp(fn, "lin_sub", 7)) *v = a[0] >= a[1] ? a[0] - a[1] : 0;
  else if (!strncmp(fn, "lin_mul", 7)) *v = a[0] * a[1];
  else if (!strncmp(fn, "lin_div", 7)) *v = a[1] ? a[0] / a[1] : 0;
  else if (!strncmp(fn, "lin_mod", 7)) *v = a[1] ? a[0] % a[1] : 0;
  else if (!strncmp(fn, "lin_pow", 7)) { long b0 = a[0], e = a[1], res = 1; while (e > 0) { if (e & 1) res *= b0; b0 *= b0; e >>= 1; } *v = res; }
  else if (!strncmp(fn, "lin_eq", 6))   { *v = a[0] == a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_lt", 6))   { *v = a[0] <  a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_leq", 7))  { *v = a[0] <= a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_gt", 6))   { *v = a[0] >  a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_geq", 7))  { *v = a[0] >= a[1]; *is_bool = 1; }
  else return 0;
  return 1;
}

/* Read a single argument: a Scott numeral, a Church boole, a float box, or a
   nested saturated `_ffi` closure (evaluated recursively).  A float arg stores
   its IEEE-754 bits in *v. */
static Port ev_arglist_arg(Net *n, Port p, long *v, int *is_b) {
  Port q = dhop(n, p);
  if (q.node < 0 || q.node >= n->nn || n->dead[q.node] || n->tag[q.node] != LAM)
    return (Port){-1, 0};
  if (ctor_tag(nm(n, q.node)) == DT_FFI) {
    int is_f = 0;
    if (ev_ffi(n, (Port){q.node, 0}, v, is_b, &is_f)) return p;
    return (Port){-1, 0};
  }
  if (ctor_tag(nm(n, q.node)) == DT_FLOAT) {
    double d; if (!net_read_float(n, q, &d)) return (Port){-1, 0};
    memcpy(v, &d, 8); *is_b = 0; return p;
  }
  if (ctor_tag(nm(n, q.node)) == DT_BOOL) { int b = net_read_bool(n, q); if (b < 0) return (Port){-1, 0}; *v = b; *is_b = 0; return p; }
  long x = net_read_int(n, q);
  if (x < 0) return (Port){-1, 0};
  *v = x; *is_b = 0; return p;
}

/* Collect up to 2 args from the `_cl`-spine list; always succeeds (na updated). */
static Port ev_arglist(Net *n, Port argp, long out[2], int *nout) {
  *nout = 0; Port cur = dhop(n, argp);
  if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) return (Port){-1, 0};
  if (ctor_tag(nm(n, cur.node)) != DT_STR) {
    int ib = 0; if (ev_arglist_arg(n, argp, &out[0], &ib).node >= 0) *nout = 1;
    return cur;
  }
  for (int step = 0; step < n->nn && *nout < 2; step++) {
    cur = dhop(n, cur);
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
    Port inner = dhop(n, WP(n, cur.node, 2));
    if (inner.node < 0 || inner.port != 0 || n->dead[inner.node] || n->tag[inner.node] != LAM) break;
    Port body = dhop(n, WP(n, inner.node, 2));
    if (body.node < 0 || n->dead[body.node] || n->tag[body.node] != APP) break;
    Port ia = dhop(n, WP(n, body.node, 0));
    if (ia.node < 0 || n->dead[ia.node] || n->tag[ia.node] != APP) break;
    int ib = 0;
    if (ev_arglist_arg(n, WP(n, ia.node, 2), &out[*nout], &ib).node < 0) break;
    (*nout)++;
    cur = WP(n, body.node, 2);
  }
  return cur;
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