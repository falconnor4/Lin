#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

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

static Port simd_alloc_scott(Net *n, long k) {
  Scope sc = scope_nil(); Port cur = (Port){-1, 0};
  for (long i = 0; i <= k; i++) {
    Port sz = net_alloc(n, LAM, sc, "_sz"), ss = net_alloc(n, LAM, sc, "_ss");
    net_link(n, (Port){sz.node, 2}, (Port){ss.node, 0}, 0);
    if (i == 0) net_link(n, (Port){ss.node, 2}, (Port){sz.node, 1}, 0);
    else {
      Port app = net_alloc(n, APP, sc, "");
      net_link(n, (Port){app.node, 0}, (Port){ss.node, 1}, 0);
      net_link(n, (Port){app.node, 2}, cur, 0);
      net_link(n, (Port){ss.node, 2}, (Port){app.node, 1}, 0);
    }
    cur = (Port){sz.node, 0};
  }
  return cur;
}

static Port simd_alloc_bool(Net *n, int val) {
  Scope sc = scope_nil();
  Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);
  net_link(n, (Port){bf.node, 2}, (Port){val ? bt.node : bf.node, 1}, 0);
  return (Port){bt.node, 0};
}

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
   returning 1 and storing value / is_bool, else 0.  Also used to read an
   argument, so nested arithmetic composes into a single native fold. */
static int ev_ffi(Net *n, Port p, long *v, int *is_bool) {
  char fn[256];
  if (!rd_fn(n, p, fn, sizeof(fn))) return 0;
  Port r = dhop(n, WP(n, p.node, 2));
  Port a2 = WP(n, r.node, 2);
  if (a2.node < 0) return 0;
  long a[2]; int na = 0; Port argp = WP(n, a2.node, 2);
  ev_arglist(n, argp, a, &na);
  if (na < 2) return 0; /* every lin_* op needs both saturated args */
  *is_bool = 0;
  if (!strncmp(fn, "lin_add", 7)) *v = a[0] + a[1];
  else if (!strncmp(fn, "lin_sub", 7)) *v = a[0] >= a[1] ? a[0] - a[1] : 0;
  else if (!strncmp(fn, "lin_mul", 7)) *v = a[0] * a[1];
  else if (!strncmp(fn, "lin_div", 7)) *v = a[1] ? a[0] / a[1] : 0;
  else if (!strncmp(fn, "lin_mod", 7)) *v = a[1] ? a[0] % a[1] : 0;
  else if (!strncmp(fn, "lin_pow", 7)) { long b0 = a[0], e = a[1], res = 1; while (e > 0) { if (e & 1) res *= b0; b0 *= b0; e >>= 1; } *v = res; }
  else if (!strncmp(fn, "lin_eq", 6)) { *v = a[0] == a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_lt", 6)) { *v = a[0] < a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_leq", 7)) { *v = a[0] <= a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_gt", 6)) { *v = a[0] > a[1]; *is_bool = 1; }
  else if (!strncmp(fn, "lin_geq", 7)) { *v = a[0] >= a[1]; *is_bool = 1; }
  else return 0;
  return 1;
}

/* Read a single argument: a Scott numeral, a Church boole, or a nested
   saturated `_ffi` closure (evaluated recursively). */
static Port ev_arglist_arg(Net *n, Port p, long *v, int *is_b) {
  Port q = dhop(n, p);
  if (q.node < 0 || q.node >= n->nn || n->dead[q.node] || n->tag[q.node] != LAM)
    return (Port){-1, 0};
  if (!strcmp(nm(n, q.node), "_ffi")) {
    if (ev_ffi(n, (Port){q.node, 0}, v, is_b)) return p;
    return (Port){-1, 0};
  }
  if (!strncmp(nm(n, q.node), "_bt", 3)) { int b = net_read_bool(n, q); if (b < 0) return (Port){-1, 0}; *v = b; *is_b = 0; return p; }
  long x = net_read_int(n, q);
  if (x < 0) return (Port){-1, 0};
  *v = x; *is_b = 0; return p;
}

/* Collect up to 2 args from the `_cl`-spine list; always succeeds (na updated). */
static Port ev_arglist(Net *n, Port argp, long out[2], int *nout) {
  *nout = 0; Port cur = dhop(n, argp);
  if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) return (Port){-1, 0};
  if (nm(n, cur.node)[0] != 'c' && strncmp(nm(n, cur.node), "_cl", 3)) {
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
  long v; int is_bool = 0;
  if (!ev_ffi(n, (Port){lam, 0}, &v, &is_bool)) return 0;

  Port res = is_bool ? simd_alloc_bool(n, (int)v) : simd_alloc_scott(n, v);
  /* Substitute the computed datum for the `_ffi` closure: the consumer APP is
     kept alive and re-paired with `res`, so the ordinary LAM/APP rule (a
     Church-boole / Scott-numeral application) completes the selection in a
     later wave rather than expanding the closure step by step. */
  n->dead[lam] = 1;
  net_link(n, res, (Port){app, 0}, 1);
  return 1;
}

static int simd_reduce_wave(Net *n, long limit, int *changed) {
  if (n->atop <= 0 || n->steps >= limit) return 0;
  static Port *curr = NULL; static int curr_cap = 0;
  int wave_cnt = wave_snapshot(n, &curr, &curr_cap);

  int batch_changed = 0;
  int np = wave_cnt / 2;
  if (getenv("LIN_SIMD_DEBUG"))
    fprintf(stderr, "[simd] %d wavefront redexes: native folds + OpenMP fan-out\n", np);

  /* Partition the wave: native small-int arithmetic closures are folded here,
     serially (each one allocates and rewires the net); every remaining redex
     is handed to the base engine's OpenMP-aware interaction core, so the bulk
     of the reduction fans out across cores instead of a single thread. */
  Port *gen = malloc((size_t)wave_cnt * sizeof(Port));
  int ngen = 0;

  for (int i = 0; i < wave_cnt; i += 2) {
    if (n->steps >= limit) {
      for (int j = i; j < wave_cnt; j += 2) {
        if (n->atop + 2 > n->actcap)
          n->act = realloc(n->act, (size_t)(n->actcap = n->actcap ? n->actcap * 2 : 256) * sizeof(Port));
        n->act[n->atop++] = curr[j]; n->act[n->atop++] = curr[j + 1];
      }
      break;
    }
    Port p1 = curr[i], p2 = curr[i + 1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node] || p1.port || p2.port) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port) continue;

    int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
    int folded = 0;
    if (t1 == LAM && t2 == APP && !strcmp(nm(n, p1.node), "_ffi"))
      folded = simd_fold_ffi(n, p1.node, p2.node);
    else if (t2 == LAM && t1 == APP && !strcmp(nm(n, p2.node), "_ffi"))
      folded = simd_fold_ffi(n, p2.node, p1.node);
    if (folded) { batch_changed++; n->steps++; continue; }

    gen[ngen++] = p1; gen[ngen++] = p2;
  }

  if (ngen > 0) lin_reduce_wave_parallel(n, gen, ngen, changed);
  free(gen);
  *changed += batch_changed;
  return 1;
}

LinDriver lin_simd_driver = {"simd", simd_reduce_wave};