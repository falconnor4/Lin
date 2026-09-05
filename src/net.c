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

static int in_parallel;
static void sc_ensure_cap(Net *n, int need) {
  if (need <= n->sccap) return;
  int nc = n->sccap ? n->sccap * 2 : 256;
  while (nc < need && nc > 0) nc *= 2;
  n->sca = realloc(n->sca, (size_t)nc * sizeof(uint64_t)); n->sccap = nc;
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
  while (nc < need) nc *= 2;
  n->tag = realloc(n->tag, nc); n->wire = realloc(n->wire, (size_t)nc * 3 * sizeof(Port));
  n->scope = realloc(n->scope, (size_t)nc * sizeof(Scope)); n->name = realloc(n->name, (size_t)nc * sizeof(char *));
  memset(n->name + n->cap, 0, (size_t)(nc - n->cap) * sizeof(char *));
  n->dead = realloc(n->dead, nc); memset(n->dead + n->cap, 0, (size_t)(nc - n->cap)); n->cap = nc;
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
static int SC_O; /* scope-oblivious mode: annihilate gauge-mismatched dups */
int net_interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (getenv("LIN_TRACE"))
    fprintf(stderr, "step %ld: %d.%d x %d.%d\n", n->steps, t1, n1, t2, n2);

  if (t1 == LAM && t2 == APP) {
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
    if (!SC_O && !scope_eq(n, n->scope[n1], n->scope[n2]))
      return 0; /* gauge mismatch (except during readback expansion) */
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
static LinDriver *cur_drv;
void lin_set_driver(LinDriver *d) { cur_drv = d; }
LinDriver *lin_get_driver(void) { return cur_drv; }

static void reduce_wavefront(Net *n, long limit, int *changed) {
#ifdef _OPENMP
  ensure_tact();
  int nth = omp_get_max_threads();
#endif
  Port *curr = NULL;
  int curr_cap = 0;
  while (n->atop > 0 && n->steps < limit) {
    if (cur_drv && cur_drv->reduce_wave(n, limit, changed)) continue;
    int wave_cnt = n->atop;
    if (wave_cnt > curr_cap) curr = realloc(curr, (size_t)(curr_cap = wave_cnt) * sizeof(Port));
    memcpy(curr, n->act, (size_t)wave_cnt * sizeof(Port));
    n->atop = 0;
#ifdef _OPENMP
    if (nth > 1 && wave_cnt >= 8) {
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
      free(inter); free(bound); continue;
    }
#endif
    for (int i = 0; i < wave_cnt; i += 2) {
      if (n->steps >= limit) {
        for (int j = i; j < wave_cnt; j += 2) act_push(n, curr[j], curr[j + 1]);
        break;
      }
      Port p1 = curr[i], p2 = curr[i + 1];
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;
      if (net_interact(n, p1, p2)) *changed += 1;
      n->steps++;
    }
  }
  free(curr);
}

long net_reduce(Net *n, long limit) {
  while (n->steps < limit) {
    int changed = 0;
    n->atop = 0;
    unsigned char *reach = calloc((size_t)n->nn, 1);
    int *q = malloc(sizeof(int) * (size_t)(n->nn + 1)), qh = 0, qt = 0;
    reach[0] = 1; q[qt++] = 0;
    while (qh < qt) {
      int u = q[qh++];
      for (int p = 0; p < 3; p++) {
        Port w = WIRE(n, ((Port){u, p}));
        if (w.node >= 0 && w.node < n->nn && !n->dead[w.node] && !reach[w.node]) { reach[w.node] = 1; q[qt++] = w.node; }
      }
    }
    net_compact(n, reach); free(reach); free(q);
    for (int i = 1; i < n->nn; i++) {
      Port w = n->wire[i * 3];
      if (w.port == 0 && w.node > i) act_push(n, (Port){i, 0}, w);
    }
    reduce_wavefront(n, limit, &changed);
    if (getenv("LIN_DUMP"))
      for (int i = 0; i < n->nn; i++) {
        if (n->dead[i]) continue;
        for (int pp = 0; pp < 3; pp++) {
          Port w = n->wire[i * 3 + pp];
          if (w.node >= 0 && (n->wire[w.node * 3 + w.port].node != i || n->wire[w.node * 3 + w.port].port != pp))
            fprintf(stderr, "ASYMMETRY %d.%d -> %d.%d back %d.%d\n", i, pp, w.node, w.port,
                    n->wire[w.node * 3 + w.port].node, n->wire[w.node * 3 + w.port].port);
        }
      }
    if (changed == 0) break;
  }
  return n->steps;
}

/* readback expansion: continue reduction ignoring scope gauge, unfolding
   shared croissants back into the explicit value net.  Only used for
   decoding closed normal forms; the ordinary reducer keeps the gauge. */
long net_reduce_readback(Net *n, long limit) {
  int save = SC_O; SC_O = 1; long s = net_reduce(n, limit); SC_O = save; return s;
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