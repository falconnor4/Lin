#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
#define NONE ((Port){-1, 0})

static inline int scope_len(Scope s) { return s.sso.is_heap ? (int)s.heap.len : (int)s.sso.len; }
static inline int scope_bit(const Net *n, Scope s, int i) {
  return s.sso.is_heap ? (int)n->sca[s.heap.off + i] : (int)((s.sso.bits >> i) & 1);
}
Scope scope_nil(void) { Scope s; s.raw = 0; return s; }

#define MAX_SC_CAP (1 << 28)

static int in_parallel;
static void sc_ensure_cap(Net *n, int need) {
  if (need <= n->sccap) return;
  int nc = n->sccap ? n->sccap * 2 : 256;
  while (nc < need && nc > 0 && nc < MAX_SC_CAP) nc *= 2;
  if (nc <= 0 || nc > MAX_SC_CAP) nc = (need > MAX_SC_CAP) ? need : MAX_SC_CAP;
  uint64_t *new_sca = realloc(n->sca, (size_t)nc * sizeof(uint64_t));
  if (!new_sca) {
    fprintf(stderr, "error: scope gauge capacity limit exceeded\n");
    exit(1);
  }
  n->sca = new_sca; n->sccap = nc;
}

static int sc_alloc(Net *n, int len) {
  if (len < 0 || n->scn > 0x7fffffff - len) return 0;
  if (!in_parallel) sc_ensure_cap(n, n->scn + len);
  return __atomic_fetch_add(&n->scn, len, __ATOMIC_RELAXED);
}

/* [bit] ++ a ++ b  (paper: non-abelian prefix injection on commutation) */
static Scope scope_cat(Net *n, int bit, Scope a, Scope b) {
  int la = scope_len(a), lb = scope_len(b), total = 1 + la + lb;
  if (total <= 57 && !a.sso.is_heap && !b.sso.is_heap) {
    Scope r; r.raw = 0; r.sso.len = (uint64_t)total;
    r.sso.bits = (uint64_t)(bit & 1) | (a.sso.bits << 1) | (b.sso.bits << (1 + la));
    return r;
  }
  int off = sc_alloc(n, total); n->sca[off] = (uint64_t)(bit & 1);
  for (int i = 0; i < la; i++) n->sca[off + 1 + i] = (uint64_t)scope_bit(n, a, i);
  for (int i = 0; i < lb; i++) n->sca[off + 1 + la + i] = (uint64_t)scope_bit(n, b, i);
  Scope r; r.raw = 0; r.heap.is_heap = 1; r.heap.len = (uint64_t)total; r.heap.off = (uint64_t)off;
  return r;
}

Scope scope_ext(Net *n, Scope s, int bit) {
  int ls = scope_len(s);
  if (ls + 1 <= 57 && !s.sso.is_heap) {
    Scope r; r.raw = 0; r.sso.len = (uint64_t)(ls + 1);
    r.sso.bits = (uint64_t)(bit & 1) | (s.sso.bits << 1);
    return r;
  }
  return scope_cat(n, bit, s, scope_nil());
}

int scope_eq(Net *n, Scope a, Scope b) {
  if (a.raw == b.raw) return 1;
  if (!a.sso.is_heap && !b.sso.is_heap) return 0;
  int la = scope_len(a), lb = scope_len(b);
  if (la != lb) return 0;
  if (!la) return 1;
  for (int i = 0; i < la; i++) if (scope_bit(n, a, i) != scope_bit(n, b, i)) return 0;
  return 1;
}

void net_init(Net *n, int cap) {
  n->cap = cap; n->tag = malloc(cap); n->wire = malloc(cap * 3 * sizeof(Port));
  n->scope = malloc(cap * sizeof(Scope)); n->name = calloc(cap, sizeof(char *));
  n->act = NULL; n->atop = 0; n->actcap = 0; n->dead = calloc(cap, 1);
  n->sca = NULL; n->sccap = 0; n->scn = 0; n->nn = 0; n->steps = 0;
  net_alloc(n, ROOT, scope_nil(), "");
}

void net_free(Net *n) {
  free(n->tag); free(n->wire); free(n->scope); free(n->act); free(n->dead); free(n->sca);
  if (n->name) { for (int i = 0; i < n->nn; i++) free(n->name[i]); free(n->name); }
}

static void net_ensure_cap(Net *n, int need) {
  if (need <= n->cap) return;
  int nc = n->cap ? n->cap * 2 : 256;
  while (nc < need && nc > 0) nc *= 2;
  if (nc <= 0) nc = need;
  n->tag = realloc(n->tag, (size_t)nc); n->wire = realloc(n->wire, (size_t)nc * 3 * sizeof(Port));
  n->scope = realloc(n->scope, (size_t)nc * sizeof(Scope)); n->name = realloc(n->name, (size_t)nc * sizeof(char *));
  memset(n->name + n->cap, 0, (size_t)(nc - n->cap) * sizeof(char *));
  n->dead = realloc(n->dead, (size_t)nc); memset(n->dead + n->cap, 0, (size_t)(nc - n->cap)); n->cap = nc;
}

Port net_alloc(Net *n, int tag, Scope sc, const char *name) {
  if (!in_parallel) net_ensure_cap(n, n->nn + 1);
  int id = __atomic_fetch_add(&n->nn, 1, __ATOMIC_RELAXED);
  n->tag[id] = tag; n->dead[id] = 0; n->scope[id] = sc;
  if (n->name[id]) { free(n->name[id]); n->name[id] = NULL; }
  if (name && name[0]) n->name[id] = strdup(name);
  for (int i = 0; i < 3; i++) n->wire[id * 3 + i] = NONE;
  return (Port){id, 0};
}

static void act_push(Net *n, Port a, Port b) {
  if (n->atop + 2 > n->actcap)
    n->act = realloc(n->act, (size_t)(n->actcap = n->actcap ? n->actcap * 2 : 256) * sizeof(Port));
  n->act[n->atop++] = a; n->act[n->atop++] = b;
}

/* Plugin hook: enqueue an active redex pair into the net's active list.  Used
   by driver plugins (e.g. the GPU kernel) that commit link-rewrites directly
   and must rebuild the continuation set exactly like the base engine does. */
void lin_enqueue(Net *n, Port a, Port b) { act_push(n, a, b); }

/* Driver native-fold accounting: drivers bump this when they fold a redex
   natively instead of letting the base engine expand it.  Exposed so the test
   suite can assert that accelerator folding actually fires. */
static long fold_count;
void lin_fold_bump(void) { __atomic_add_fetch(&fold_count, 1, __ATOMIC_RELAXED); }
long lin_fold_total(void) { return fold_count; }

typedef struct { Port *p; int top, cap; } ActBuf;
static ActBuf *t_act;
static int n_tact;

static void ensure_tact(void) {
#ifdef _OPENMP
  int m = omp_get_max_threads();
  if (m > n_tact) {
    t_act = realloc(t_act, (size_t)m * sizeof(ActBuf));
    for (int i = n_tact; i < m; i++) t_act[i] = (ActBuf){0};
    n_tact = m;
  }
#endif
}

void net_link(Net *n, Port a, Port b, int enqueue) {
  if (a.node < 0 || b.node < 0) return;
  WIRE(n, a) = b; WIRE(n, b) = a;
  if (enqueue && a.port == 0 && b.port == 0) {
#ifdef _OPENMP
    if (in_parallel) {
      int tid = omp_get_thread_num();
      if (t_act[tid].top + 2 > t_act[tid].cap)
        t_act[tid].p = realloc(t_act[tid].p, (size_t)(t_act[tid].cap = t_act[tid].cap ? t_act[tid].cap * 2 : 256) * sizeof(Port));
      t_act[tid].p[t_act[tid].top++] = a; t_act[tid].p[t_act[tid].top++] = b;
      return;
    }
#endif
    act_push(n, a, b);
  }
}

/* the four rules of the scope-gauge calculus (wave-opt-reduction main.hs).
   ERA is an inert terminal: era-principal pairs are simply dropped. */
static int lin_trace = -1; /* cached LIN_TRACE */
int net_interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (lin_trace < 0) lin_trace = getenv("LIN_TRACE") != NULL;
  if (lin_trace)
    fprintf(stderr, "step %ld: %d.%d x %d.%d\n", n->steps, t1, n1, t2, n2);

  if (t1 == LAM && t2 == APP) {
    /* a saturated _ffi closure folds to a concrete value (int/bool/float) here
       rather than beta-reducing, so e.g. float comparisons materialise as
       Church booleans usable by `if` — independent of any accelerator driver. */
    const char *lnm = n->name[n1] ? n->name[n1] : "";
    if (ctor_tag(lnm) == DT_FFI && lin_fold_ffi(n, (Port){n1, 0}, (Port){n2, 0})) return 1;
    Port lv = WIRE(n, ((Port){n1, 1})), lb = WIRE(n, ((Port){n1, 2}));
    Port ar = WIRE(n, ((Port){n2, 1})), aa = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1; n->dead[n2] = 1;
    if (lv.node == n1 && lv.port == 2 && lb.node == n1 && lb.port == 1) {
      net_link(n, aa, ar, 1); /* identity: V = (\x. x) V */
      return 1;
    }
    net_link(n, lv, aa, 1); net_link(n, lb, ar, 1);
    return 1;
  }

  if (t1 == DUP && t2 == DUP) {
    if (!scope_eq(n, n->scope[n1], n->scope[n2]))
      return 0; /* gauge mismatch (dropped) */
    Port a1 = WIRE(n, ((Port){n1, 1})), a2 = WIRE(n, ((Port){n1, 2}));
    Port b1 = WIRE(n, ((Port){n2, 1})), b2 = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1; n->dead[n2] = 1;
    if (a1.node == n2 && a1.port == 1) net_link(n, a2, b2, 1);
    else if (a2.node == n2 && a2.port == 2) net_link(n, a1, b1, 1);
    else if (a1.node == n2 && a1.port == 2) net_link(n, a2, b1, 1);
    else if (a2.node == n2 && a2.port == 1) net_link(n, a1, b2, 1);
    else { net_link(n, a1, b1, 1); net_link(n, a2, b2, 1); }
    return 1;
  }

  if ((t1 == LAM || t1 == APP) && t2 == DUP) {
    Scope sn = n->scope[n1], sd = n->scope[n2];
    Port nv = WIRE(n, ((Port){n1, 1})), nb = WIRE(n, ((Port){n1, 2}));
    Port da = WIRE(n, ((Port){n2, 1})), db = WIRE(n, ((Port){n2, 2}));
    const char *nm = n->name[n1] ? n->name[n1] : "";
    int m1 = net_alloc(n, t1, scope_cat(n, 1, sn, sd), nm).node;
    int m2 = net_alloc(n, t1, scope_cat(n, 2, sn, sd), nm).node;
    int d1 = net_alloc(n, DUP, sd, "").node, d2 = net_alloc(n, DUP, sd, "").node;
    n->dead[n1] = 1; n->dead[n2] = 1;
    net_link(n, (Port){d1, 1}, (Port){m1, 1}, 0); net_link(n, (Port){d1, 2}, (Port){m2, 1}, 0);
    net_link(n, (Port){d2, 1}, (Port){m1, 2}, 0); net_link(n, (Port){d2, 2}, (Port){m2, 2}, 0);
    if (t1 == LAM && nv.node == n1 && nv.port == 2 && nb.node == n1 && nb.port == 1) {
      net_link(n, (Port){d1, 0}, (Port){d2, 0}, 1);
    } else {
      net_link(n, (Port){d1, 0}, nv, 1); net_link(n, (Port){d2, 0}, nb, 1);
    }
    net_link(n, (Port){m1, 0}, da, 1); net_link(n, (Port){m2, 0}, db, 1);
    return 1;
  }
  return 0; /* era or stuck gauge pair: dropped, as in the reference */
}

static void net_compact(Net *n, const unsigned char *reach) {
  int *remap = malloc((size_t)n->nn * sizeof(int)), new_nn = 0;
  for (int i = 0; i < n->nn; i++) {
    if (reach[i] && !n->dead[i]) remap[i] = new_nn++;
    else { remap[i] = -1; if (n->name[i]) { free(n->name[i]); n->name[i] = NULL; } }
  }
  for (int i = 0; i < n->nn; i++) {
    int dst = remap[i];
    if (dst < 0) continue;
    if (dst != i) { n->tag[dst] = n->tag[i]; n->scope[dst] = n->scope[i]; n->name[dst] = n->name[i]; n->name[i] = NULL; }
    for (int p = 0; p < 3; p++) {
      Port w = n->wire[i * 3 + p];
      n->wire[dst * 3 + p] = (w.node >= 0 && w.node < n->nn && remap[w.node] >= 0) ? (Port){remap[w.node], w.port} : NONE;
    }
  }
  memset(n->dead, 0, (size_t)new_nn); n->nn = new_nn; free(remap);
}

typedef struct { Port p1, p2; } Pair;
/* Driver pipeline: drivers are kept sorted by priority (ascending); the core
   waves fan out to every driver in that order.  Each driver *claims* the
   redexes it handles via ->claim and leaves the rest for lower-priority
   drivers and the base engine, so SIMD + GPU + future drivers compose in
   unison on one wave. */
static LinDriver *drv[16]; static int ndrv;
void lin_driver_add(LinDriver *d) {
  if (!d || ndrv >= 16) return;
  if (d->magic != LIN_DRIVER_MAGIC || d->abi != LIN_DRIVER_ABI) {
    fprintf(stderr, "driver '%s': rejected (bad ABI magic 0x%x/abi %u)\n",
            d->name ? d->name : "?", d->magic, d->abi);
    return;
  }
  /* insertion-sort by priority ascending (stable: later-add wins ties) */
  int i = ndrv;
  while (i > 0 && drv[i-1]->priority > d->priority) { drv[i] = drv[i-1]; i--; }
  drv[i] = d; ndrv++;
}
void lin_driver_clear(void) { ndrv = 0; }
LinDriver *lin_get_driver(void) { return ndrv ? drv[ndrv-1] : NULL; }

/* Reduce one interacting wave (`curr[0..wave_cnt)` holds `act`-form pairs,
   an even count) with the base engine's parallel-safe interaction core:
   spatial-disjoint pairs are solved concurrently via OpenMP, the rest (and a
   single-threaded build) serially.  Exposed so driver reducers (e.g. the SIMD
   driver) can fan out a real wave in parallel while handling their own
   optimisations; the base correctness rules all live here. */
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed) {
#ifdef _OPENMP
  ensure_tact();
  int nth = omp_get_max_threads();

  if (nth > 1 && wave_cnt >= 512) {
    int np = wave_cnt / 2, nsec = (n->nn + 63) >> 6;
    Pair *inter = malloc((size_t)np * sizeof(Pair)), *bound = malloc((size_t)np * sizeof(Pair));
    int n_int = 0, n_bnd = 0, sc_need = 0;
    for (int i = 0; i < wave_cnt; i += 2) {
      Port p1 = curr[i], p2 = curr[i + 1];
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;
      int u = p1.node, v = p2.node, su = u >> 6, ok = (su == (v >> 6));
      if (ok) {
        int c[4] = { WIRE(n, ((Port){u, 1})).node, WIRE(n, ((Port){u, 2})).node,
                     WIRE(n, ((Port){v, 1})).node, WIRE(n, ((Port){v, 2})).node };
        for (int k = 0; k < 4; k++) if (c[k] >= 0 && (c[k] >> 6) != su) { ok = 0; break; }
      }
      if (ok) inter[n_int++] = (Pair){p1, p2}; else bound[n_bnd++] = (Pair){p1, p2};
      int lu = scope_len(n->scope[u]), lv = scope_len(n->scope[v]);
      if (1 + lu + lv > 57 || n->scope[u].sso.is_heap || n->scope[v].sso.is_heap) sc_need += 2 * (1 + lu + lv);
    }
    if (n_int > 0) {
      int *head = malloc((size_t)nsec * sizeof(int)), *next = malloc((size_t)n_int * sizeof(int));
      memset(head, -1, (size_t)nsec * sizeof(int));
      for (int i = 0; i < n_int; i++) { int s = inter[i].p1.node >> 6; next[i] = head[s]; head[s] = i; }
      net_ensure_cap(n, n->nn + n_int * 4); sc_ensure_cap(n, n->scn + sc_need);
      in_parallel = 1; int batch_changed = 0;
      #pragma omp parallel for reduction(+:batch_changed) schedule(dynamic)
      for (int s = 0; s < nsec; s++)
        for (int i = head[s]; i >= 0; i = next[i])
          if (WIRE(n, inter[i].p1).node == inter[i].p2.node && !n->dead[inter[i].p1.node] && !n->dead[inter[i].p2.node])
            if (net_interact(n, inter[i].p1, inter[i].p2)) batch_changed++;
      in_parallel = 0; n->steps += n_int; *changed += batch_changed;
      for (int t = 0; t < nth; t++) {
        for (int j = 0; j < t_act[t].top; j += 2) act_push(n, t_act[t].p[j], t_act[t].p[j + 1]);
        t_act[t].top = 0;
      }
      free(head); free(next);
    }
    for (int i = 0; i < n_bnd; i++) {
      Port p1 = bound[i].p1, p2 = bound[i].p2;
      if (p1.node >= 0 && p2.node >= 0 && !n->dead[p1.node] && !n->dead[p2.node] &&
          WIRE(n, p1).node == p2.node && WIRE(n, p2).node == p1.node && !p1.port && !p2.port) {
        if (net_interact(n, p1, p2)) *changed += 1;
        n->steps++;
      }
    }
    free(inter); free(bound);
    return;
  }
#endif
  for (int i = 0; i < wave_cnt; i += 2) {
    Port p1 = curr[i], p2 = curr[i + 1];
    if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;
    if (net_interact(n, p1, p2)) *changed += 1;
    n->steps++;
  }
}

/* Snapshot the active redex list into `*out` (grown via `*cap`), voiding `atop`. */
int wave_snapshot(Net *n, Port **out, int *cap) {
  int cnt = n->atop; if (cnt <= 0) return 0;
  if (cnt > *cap) { free(*out); *out = malloc((size_t)(*cap = cnt) * sizeof(Port)); }
  memcpy(*out, n->act, (size_t)cnt * sizeof(Port));
  n->atop = 0;
  return cnt;
}

long net_reduce(Net *n, long limit) {
  /* Self-collecting nets reduce by the active list; the BFS+compact below
     reclaims memory after it doubles.  Waves fan out to every driver in
     priority order: each claims the redexes it handles, the base engine takes
     the remainder. */
  Port *curr = NULL; int curr_cap = 0;
  unsigned char *reach = NULL; int *q = NULL; long qcap = 0, gcmark = 1L << 20;
  /* per-driver slice buckets (rebuilt each wave) */
  Port *slices[16] = {0}; int scaps[16] = {0}, scnts[16] = {0};
  while (n->steps < limit) {
    int changed = 0;
    while (n->atop > 0 && n->steps < limit) {
      int cnt = wave_snapshot(n, &curr, &curr_cap);
      if (cnt <= 0) break;
      int np = cnt / 2;

      /* partition the wave up-front by driver claim (priority order) */
      for (int di = 0; di < ndrv; di++) scnts[di] = 0;
      int base_cnt = 0;
      static Port *base_rx = NULL; static int base_cap = 0;
      for (int i = 0; i < np; i++) {
        Port p1 = curr[i*2], p2 = curr[i*2+1];
        int assigned = 0;
        for (int di = 0; di < ndrv && !assigned; di++) {
          if (!drv[di]->claim || !drv[di]->claim(n, p1, p2)) continue;
          if (scnts[di] + 2 > scaps[di]) { scaps[di] = scaps[di] ? scaps[di]*2 : 256; slices[di] = realloc(slices[di], (size_t)scaps[di]*sizeof(Port)); }
          slices[di][scnts[di]++] = p1; slices[di][scnts[di]++] = p2;
          assigned = 1;
        }
        if (!assigned) {
          if (base_cnt + 2 > base_cap) { base_cap = base_cap ? base_cap*2 : 256; base_rx = realloc(base_rx, (size_t)base_cap*sizeof(Port)); }
          base_rx[base_cnt++] = p1; base_rx[base_cnt++] = p2;
        }
      }

      /* dispatch each driver's slice (authoritative for its class) */
      for (int di = 0; di < ndrv; di++) {
        if (!scnts[di]) continue;
        drv[di]->reduce(n, slices[di], scnts[di]/2, limit, &changed);
      }
      /* base engine handles the unclaimed remainder */
      if (base_cnt) lin_reduce_wave_parallel(n, base_rx, base_cnt, &changed);
    }
    if (changed == 0 && n->atop == 0) break;
    if (n->atop == 0 && (long)n->nn > gcmark) {
      if ((long)n->nn + 1 > qcap) { free(reach); free(q); qcap = (long)n->nn + 1;
        reach = malloc((size_t)qcap); q = malloc((size_t)qcap * sizeof(int)); }
      memset(reach, 0, (size_t)qcap);
      int qh = 0, qt = 1; reach[0] = 1; q[0] = 0;
      while (qh < qt) { int u = q[qh++];
        for (int p = 0; p < 3; p++) { Port w = WIRE(n, ((Port){u, p}));
          if (w.node >= 0 && w.node < (int)n->nn && !n->dead[w.node] && !reach[w.node]) { reach[w.node] = 1; q[qt++] = w.node; } } }
      net_compact(n, reach);
      gcmark = (long)n->nn * 2 + 64;
      for (int i = 1; i < n->nn; i++) if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
        act_push(n, (Port){i, 0}, n->wire[i * 3]);
    }
  }
  free(reach); free(q); free(curr);
  for (int di = 0; di < ndrv; di++) free(slices[di]);
  return n->steps;
}

Net *net_copy(const Net *n) {
  Net *c = malloc(sizeof(Net)); *c = *n;
  c->tag = malloc(c->cap); memcpy(c->tag, n->tag, c->cap);
  c->wire = malloc(c->cap * 3 * sizeof(Port)); memcpy(c->wire, n->wire, c->cap * 3 * sizeof(Port));
  c->scope = malloc(c->cap * sizeof(Scope)); memcpy(c->scope, n->scope, c->cap * sizeof(Scope));
  c->name = calloc(c->cap, sizeof(char *));
  for (int i = 0; i < n->nn; i++) if (n->name[i]) c->name[i] = strdup(n->name[i]);
  c->dead = malloc(c->cap); memcpy(c->dead, n->dead, c->cap);
  c->sca = n->scn ? malloc((size_t)n->scn * sizeof(uint64_t)) : NULL;
  if (n->scn) memcpy(c->sca, n->sca, (size_t)n->scn * sizeof(uint64_t));
  c->act = NULL; c->actcap = c->atop = 0; c->steps = 0;
  return c;
}