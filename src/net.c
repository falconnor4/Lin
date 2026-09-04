#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
#define NONE ((Port){-1, -1})

Scope scope_nil(void) { return (Scope){0, 0}; }

/* scopes live in a per-net arena (unbounded free-group words, never mutated) */
static int sc_alloc(Net *n, int len) {
  if (len < 0 || n->scn > 0x7fffffff - len) return 0;
  if (n->scn + len > n->sccap) {
    int nc = n->sccap ? n->sccap * 2 : 256;
    while (nc < n->scn + len && nc > 0) nc *= 2;
    if (nc <= 0) return 0;
    uint64_t *p = realloc(n->sca, (size_t)nc * sizeof(uint64_t));
    if (!p) return 0;
    n->sca = p;
    n->sccap = nc;
  }
  int off = n->scn;
  n->scn += len;
  return off;
}

Scope scope_ext(Net *n, Scope s, int bit) {
  int off = sc_alloc(n, s.len + 1);
  n->sca[off] = bit & 1;
  memcpy(n->sca + off + 1, n->sca + s.off, (size_t)s.len * sizeof(uint64_t));
  return (Scope){s.len + 1, off};
}

/* [bit] ++ a ++ b  (paper: non-abelian prefix injection on commutation) */
static Scope scope_cat(Net *n, int bit, Scope a, Scope b) {
  int off = sc_alloc(n, 1 + a.len + b.len);
  n->sca[off] = bit & 1;
  memcpy(n->sca + off + 1, n->sca + a.off, (size_t)a.len * sizeof(uint64_t));
  memcpy(n->sca + off + 1 + a.len, n->sca + b.off,
         (size_t)b.len * sizeof(uint64_t));
  return (Scope){1 + a.len + b.len, off};
}

int scope_eq(Net *n, Scope a, Scope b) {
  if (a.len != b.len) return 0;
  if (!a.len) return 1;
  return !memcmp(n->sca + a.off, n->sca + b.off, (size_t)a.len * sizeof(uint64_t));
}

void net_init(Net *n, int cap) {
  n->cap = cap;
  n->tag = malloc(cap);
  n->wire = malloc(cap * 3 * sizeof(Port));
  n->scope = malloc(cap * sizeof(Scope));
  n->name = malloc(cap * NAME);
  n->act = NULL; n->atop = 0; n->actcap = 0;
  n->dead = calloc(cap, 1);
  n->sca = NULL; n->sccap = 0; n->scn = 0;
  n->nn = 0; n->steps = 0;
  net_alloc(n, ROOT, scope_nil(), "");
}

void net_free(Net *n) {
  free(n->tag); free(n->wire); free(n->scope);
  free(n->name); free(n->act); free(n->dead); free(n->sca);
}

Port net_alloc(Net *n, int tag, Scope sc, const char *name) {
  if (n->nn >= n->cap) {
    int nc = n->cap * 2;
    n->tag = realloc(n->tag, nc);
    n->wire = realloc(n->wire, (size_t)nc * 3 * sizeof(Port));
    n->scope = realloc(n->scope, (size_t)nc * sizeof(Scope));
    n->name = realloc(n->name, (size_t)nc * NAME);
    n->dead = realloc(n->dead, nc);
    memset(n->dead + n->cap, 0, (size_t)(nc - n->cap));
    n->cap = nc;
  }
  int id = n->nn++;
  n->tag[id] = tag;
  n->dead[id] = 0;
  n->scope[id] = sc;
  snprintf(n->name[id], NAME, "%s", name);
  for (int i = 0; i < 3; i++) n->wire[id * 3 + i] = NONE;
  return (Port){id, 0};
}

static void act_push(Net *n, Port a, Port b) {
  if (n->atop + 2 > n->actcap)
    n->act = realloc(n->act, (size_t)(n->actcap = n->actcap ? n->actcap * 2 : 256) * sizeof(Port));
  n->act[n->atop++] = a;
  n->act[n->atop++] = b;
}

void net_link(Net *n, Port a, Port b, int enqueue) {
  if (a.node < 0 || b.node < 0) return;
  WIRE(n, a) = b;
  WIRE(n, b) = a;
  if (enqueue && a.port == 0 && b.port == 0) act_push(n, a, b);
}

/* the four rules of the scope-gauge calculus (wave-opt-reduction main.hs).
   ERA is an inert terminal: era-principal pairs are simply dropped. */
static int SC_O; /* scope-oblivious mode: annihilate gauge-mismatched dups */
static int interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (getenv("LIN_TRACE"))
    fprintf(stderr, "step %ld: %d.%d x %d.%d\n", n->steps, t1, n1, t2, n2);

  if (t1 == LAM && t2 == APP) {
    Port lv = WIRE(n, ((Port){n1, 1})), lb = WIRE(n, ((Port){n1, 2}));
    Port ar = WIRE(n, ((Port){n2, 1})), aa = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    if (lv.node == n1 && lv.port == 2 && lb.node == n1 && lb.port == 1) {
      net_link(n, aa, ar, 1); /* identity: V = (\x. x) V */
      return 1;
    }
    net_link(n, lv, aa, 1);
    net_link(n, lb, ar, 1);
    return 1;
  }

  if (t1 == DUP && t2 == DUP) {
    if (!SC_O && !scope_eq(n, n->scope[n1], n->scope[n2]))
      return 0; /* gauge mismatch (except during readback expansion) */
    Port a1 = WIRE(n, ((Port){n1, 1})), a2 = WIRE(n, ((Port){n1, 2}));
    Port b1 = WIRE(n, ((Port){n2, 1})), b2 = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1;
    n->dead[n2] = 1;
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
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    char nm[NAME];
    snprintf(nm, NAME, "%s", n->name[n1]);
    int m1 = net_alloc(n, t1, scope_cat(n, 1, sn, sd), nm).node;
    int m2 = net_alloc(n, t1, scope_cat(n, 2, sn, sd), nm).node;
    int d1 = net_alloc(n, DUP, sd, "").node;
    int d2 = net_alloc(n, DUP, sd, "").node;
    net_link(n, (Port){d1, 1}, (Port){m1, 1}, 0);
    net_link(n, (Port){d1, 2}, (Port){m2, 1}, 0);
    net_link(n, (Port){d2, 1}, (Port){m1, 2}, 0);
    net_link(n, (Port){d2, 2}, (Port){m2, 2}, 0);
    if (t1 == LAM && nv.node == n1 && nv.port == 2 && nb.node == n1 && nb.port == 1) {
      net_link(n, (Port){d1, 0}, (Port){d2, 0}, 1);
    } else {
      net_link(n, (Port){d1, 0}, nv, 1);
      net_link(n, (Port){d2, 0}, nb, 1);
    }
    net_link(n, (Port){m1, 0}, da, 1);
    net_link(n, (Port){m2, 0}, db, 1);
    return 1;
  }
  return 0; /* era or stuck gauge pair: dropped, as in the reference */
}

static void reduce_worklist(Net *n, long limit, int *changed) {
  while (n->atop > 0 && n->steps < limit) {
    Port p2 = n->act[--n->atop];
    Port p1 = n->act[--n->atop];
    if (p1.node < 0 || p2.node < 0) continue;
    if (n->dead[p1.node] || n->dead[p2.node]) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port) continue;
    if (p1.port != 0 || p2.port != 0) continue;
    if (interact(n, p1, p2)) *changed += 1;
    n->steps++;
  }
}

/* full reduction to normal form: rescan principal pairs to reach lambda
   bodies, fan-out subterms, and croissant tails (reference:
   reduceToNormalForm). */
long net_reduce(Net *n, long limit) {
  while (n->steps < limit) {
    int changed = 0;
    n->atop = 0;
    /* find nodes reachable from root */
    unsigned char *reach = calloc((size_t)n->nn, 1);
    int *q = malloc(sizeof(int) * (size_t)(n->nn + 1));
    int qh = 0, qt = 0;
    reach[0] = 1;
    q[qt++] = 0;
    while (qh < qt) {
      int u = q[qh++];
      for (int p = 0; p < 3; p++) {
        Port w = WIRE(n, ((Port){u, p}));
        if (w.node >= 0 && w.node < n->nn && !n->dead[w.node] && !reach[w.node]) {
          reach[w.node] = 1;
          q[qt++] = w.node;
        }
      }
    }
    for (int i = 0; i < n->nn; i++) {
      if (n->tag[i] == ROOT || n->dead[i] || !reach[i]) continue;
      Port w = WIRE(n, ((Port){i, 0}));
      if (w.node < 0 || w.port != 0 || w.node <= i) continue;
      if (n->dead[w.node] || !reach[w.node]) continue;
      act_push(n, (Port){i, 0}, w);
    }
    free(reach);
    free(q);
    reduce_worklist(n, limit, &changed);
    if (getenv("LIN_DUMP")) {
      for (int i = 0; i < n->nn; i++) {
        if (n->dead[i]) continue;
        for (int pp = 0; pp < 3; pp++) {
          Port w = n->wire[i * 3 + pp];
          if (w.node < 0) continue;
          if (n->wire[w.node * 3 + w.port].node != i ||
              n->wire[w.node * 3 + w.port].port != pp)
            fprintf(stderr, "ASYMMETRY %d.%d -> %d.%d back %d.%d\n", i, pp,
                    w.node, w.port, n->wire[w.node * 3 + w.port].node,
                    n->wire[w.node * 3 + w.port].port);
        }
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
  int save = SC_O;
  SC_O = 1;
  long s = net_reduce(n, limit);
  SC_O = save;
  return s;
}

Net *net_copy(const Net *n) {
  Net *c = malloc(sizeof(Net));
  c->cap = n->cap;
  c->tag = malloc(c->cap);
  c->wire = malloc(c->cap * 3 * sizeof(Port));
  c->scope = malloc(c->cap * sizeof(Scope));
  c->name = malloc(c->cap * NAME);
  c->act = NULL; c->actcap = 0; c->atop = 0;
  c->dead = malloc(c->cap);
  memcpy(c->dead, n->dead, c->cap);
  c->nn = n->nn; c->steps = 0;
  memcpy(c->tag, n->tag, c->cap);
  memcpy(c->wire, n->wire, c->cap * 3 * sizeof(Port));
  memcpy(c->scope, n->scope, c->cap * sizeof(Scope));
  memcpy(c->name, n->name, c->cap * NAME);
  c->sca = malloc(n->scn * sizeof(uint64_t));
  memcpy(c->sca, n->sca, n->scn * sizeof(uint64_t));
  c->sccap = c->scn = n->scn;
  return c;
}