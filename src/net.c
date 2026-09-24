#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
#define NONE ((Port){-1, 0})

Scope scope_nil(void) { return 0; }
static int in_parallel;   /* a wave is running threaded: no interning there (see below) */

/* ---------------- the level trie ----------------
   A level is a position in the term: the branches taken from the root.  Interning that sequence
   makes equality an int compare, the meet the lowest common ancestor, nesting a walk up, and
   extension an intern -- and representation free: one int per node, one edge per distinct path. */
static void lv_ensure(Net *n, int need) {
  if (need <= n->lvcap) return;
  int nc = n->lvcap ? n->lvcap * 2 : 256;
  while (nc < need) nc *= 2;
  n->lv_parent = realloc(n->lv_parent, (size_t)nc * sizeof(int));
  n->lv_depth = realloc(n->lv_depth, (size_t)nc * sizeof(int));
  n->lv_bit = realloc(n->lv_bit, (size_t)nc);
  n->lvcap = nc;
}
/* the table must stay at most half full, or the probe below never finds an empty slot */
static int lv_hcap_for(int entries) {
  int cap = 1024;
  while (cap < (entries + 1) * 2) { if (cap > (1 << 30)) break; cap *= 2; }
  return cap;
}
static void lv_rehash(Net *n, int cap) {
  n->lv_hcap = cap;
  n->lv_hash = realloc(n->lv_hash, (size_t)cap * sizeof(int));
  memset(n->lv_hash, 0, (size_t)cap * sizeof(int));
  /* ids are 1..nlv: `l < nlv` left the LAST live level out of the table, so looking its path up
     again interned a second id for a path that already had one. */
  for (int l = 1; l <= n->nlv; l++) {
    unsigned h = ((unsigned)n->lv_parent[l] * 2654435761u + (unsigned)n->lv_bit[l]) & (unsigned)(cap - 1);
    while (n->lv_hash[h]) h = (h + 1) & (unsigned)(cap - 1);
    n->lv_hash[h] = l; }

}
static int lv_intern(Net *n, int parent, int bit) {
  if (!n->lv_hcap) lv_rehash(n, lv_hcap_for(n->nlv));
  if ((n->nlv + 1) * 2 > n->lv_hcap) lv_rehash(n, n->lv_hcap * 2);
  unsigned h = ((unsigned)parent * 2654435761u + (unsigned)bit) & (unsigned)(n->lv_hcap - 1);
  while (n->lv_hash[h]) {
    int l = n->lv_hash[h];
    if (n->lv_parent[l] == parent && n->lv_bit[l] == (unsigned char)bit) return l;
    h = (h + 1) & (unsigned)(n->lv_hcap - 1);
  }
  if (n->nlv + 2 > n->lvcap) lv_ensure(n, n->nlv + 2);   /* l = nlv+1 indexes entry l, so the
                                                            arrays need nlv+2 entries, not nlv+1 */
  int l = ++n->nlv;                    /* ids start at 1; 0 is the root */
  n->lv_parent[l] = parent; n->lv_bit[l] = (unsigned char)bit;
  n->lv_depth[l] = parent ? n->lv_depth[parent] + 1 : 1;
  n->lv_hash[h] = l;
  return l;
}
static int lv_depth(Net *n, int l) { return l ? n->lv_depth[l] : 0; }
static int lv_up(Net *n, int l) { return l ? n->lv_parent[l] : 0; }

Scope scope_app(Net *n, Scope s, int bit) { return (Scope)lv_intern(n, (int)s, bit & 1); }
/* is `a` a proper ancestor of `b`?  Used only for the nested-level case below. */
static int scope_within(Net *n, Scope a, Scope b) {
  if (!a || a == b) return 0;
  int d = lv_depth(n, b) - lv_depth(n, a);
  if (d <= 0) return 0;
  int x = (int)b;
  while (d-- > 0) x = lv_up(n, x);
  return (Scope)x == a;
}
#define MAX_SCOPE_STEPS (1 << 16)

/* A deliberate divergence from `wave-opt-reduction`: main.hs labels a commuting copy with the two
   paths CONCATENATED, where this trie takes their lowest common ancestor.  Porting the concatenation
   changed no result and inflated the .line artifacts to 656 KB and 1.76 MB against their 300 KB bound
   -- concatenated paths grow with every commutation.  The compact trie keeps paths short. */
Scope scope_meet(Net *n, Scope a, Scope b) {
  int guard = n->nlv + 2;
  while (lv_depth(n, a) > lv_depth(n, b)) { a = (Scope)lv_up(n, a); if (--guard < 0) goto bad; }
  while (lv_depth(n, b) > lv_depth(n, a)) { b = (Scope)lv_up(n, b); if (--guard < 0) goto bad; }
  while (a != b) { a = (Scope)lv_up(n, a); b = (Scope)lv_up(n, b); if (--guard < 0) goto bad; }
  return a;
bad:
  return 0;
}

int scope_eq(const Net *n, Scope a, Scope b) { (void)n; return a == b; }

/* a grow-only path buffer: the steps from the root down to a level */
static unsigned char *lv_path; static int lv_pathcap;
static unsigned char *lv_path_reserve(int d) {
  if (d > lv_pathcap) { lv_pathcap = d * 2 + 16; lv_path = realloc(lv_path, (size_t)lv_pathcap); }
  return lv_path;
}

Scope scope_rebase(Net *n, const Net *src, Scope lvl, Scope s) {
  /* A level id is local to its net's trie, so a clone's levels must always be re-interned into
     the target -- even when the clone sits at the root level.  (Bit-words could be copied
     across nets verbatim; ids cannot, and doing so silently produced ids that do not exist in
     the target trie.)  result = lvl ++ path_of(s) */
  int cur = (int)lvl;
  if (!s) return (Scope)cur;
  int d = src->lv_depth[s];
  unsigned char *p = lv_path_reserve(d);
  int l = (int)s;
  for (int i = d - 1; i >= 0; i--) { p[i] = src->lv_bit[l]; l = src->lv_parent[l]; }
  for (int i = 0; i < d; i++) cur = lv_intern(n, cur, p[i]);
  return (Scope)cur;
}

/* Install a level trie: level 0 is the root, levels 1..nlv come in id order (parents precede
   children), so depths follow from parents.  nlv == 0 is a valid net. */
void net_level_set(Net *n, int nlv, const int *parent, const unsigned char *bit) {
  lv_ensure(n, nlv + 1);
  n->nlv = nlv;
  n->lv_parent[0] = 0; n->lv_bit[0] = 0; n->lv_depth[0] = 0;
  for (int l = 1; l <= nlv; l++) {
    n->lv_parent[l] = parent[l - 1]; n->lv_bit[l] = bit[l - 1];
    n->lv_depth[l] = n->lv_parent[l] ? n->lv_depth[n->lv_parent[l]] + 1 : 1;
  }
  lv_rehash(n, lv_hcap_for(nlv));
}

int net_level_count(const Net *n) { return n->nlv; }

void net_init(Net *n, int cap) {
  n->cap = cap; n->tag = malloc(cap); n->wire = malloc(cap * 3 * sizeof(Port));
  n->scope = malloc(cap * sizeof(Scope)); n->name = calloc(cap, sizeof(char *));
  n->act = NULL; n->atop = 0; n->actcap = 0; n->dead = calloc(cap, 1);
  n->lv_parent = NULL; n->lv_depth = NULL; n->lv_bit = NULL; n->lv_hash = NULL;
  n->nlv = 0; n->lvcap = 0; n->lv_hcap = 0;
  lv_ensure(n, 1);                      /* the root level always exists */
  n->lv_parent[0] = 0; n->lv_bit[0] = 0; n->lv_depth[0] = 0;
  n->nn = 0; n->steps = 0;
  n->root = NULL; n->nroot = 0; n->rootcap = 0;
  n->dem = calloc((size_t)cap, sizeof(unsigned int)); n->dem_stamp = 0;
  n->vport = calloc((size_t)cap, 1);
  net_alloc(n, ROOT, scope_nil(), "");
}

void net_free(Net *n) {
  free(n->tag); free(n->wire); free(n->scope); free(n->act); free(n->dead); free(n->dem); free(n->vport);
  free(n->lv_parent); free(n->lv_depth); free(n->lv_bit); free(n->lv_hash);
  free(n->root);
  if (n->name) { for (int i = 0; i < n->nn; i++) free(n->name[i]); free(n->name); }
}

void lin_demand(Net *n, Port p) {
  if (p.node < 0 || p.node >= n->nn) return;
  for (int i = 0; i < n->nroot; i++) if (n->root[i].node == p.node && n->root[i].port == p.port) return;
  if (n->nroot >= n->rootcap) {
    n->rootcap = n->rootcap ? n->rootcap * 2 : 8;
    n->root = realloc(n->root, (size_t)n->rootcap * sizeof(Port));
  }
  n->root[n->nroot++] = p;
}

static void net_ensure_cap(Net *n, int need) {
  if (need <= n->cap) return;
  int nc = n->cap ? n->cap * 2 : 256;
  while (nc < need && nc > 0) nc *= 2;
  if (nc <= 0) nc = need;
  n->tag = realloc(n->tag, (size_t)nc); n->wire = realloc(n->wire, (size_t)nc * 3 * sizeof(Port));
  n->scope = realloc(n->scope, (size_t)nc * sizeof(Scope)); n->name = realloc(n->name, (size_t)nc * sizeof(char *));
  memset(n->name + n->cap, 0, (size_t)(nc - n->cap) * sizeof(char *));
  n->dead = realloc(n->dead, (size_t)nc); memset(n->dead + n->cap, 0, (size_t)(nc - n->cap));
  n->dem = realloc(n->dem, (size_t)nc * sizeof(unsigned int));
  memset(n->dem + n->cap, 0, (size_t)(nc - n->cap) * sizeof(unsigned int));   /* 0 = never marked */
  n->vport = realloc(n->vport, (size_t)nc); memset(n->vport + n->cap, 0, (size_t)(nc - n->cap));
  n->cap = nc;
}

Port net_alloc(Net *n, int tag, Scope sc, const char *name) {
  if (!in_parallel) net_ensure_cap(n, n->nn + 1);
  int id = __atomic_fetch_add(&n->nn, 1, __ATOMIC_RELAXED);
  /* While a wave is threaded, growth is skipped: `realloc` would move the arrays out from under
     every worker, which holds raw pointers into them.  The wave reserves up front (4 nodes per
     parallel interaction, which is what the core rules use); this is the check that makes breaking
     that reservation loud instead of writing past the arrays.  Drivers never run in that region --
     claim/reduce are called between waves -- so the reservation is the core's own. */
  if (id >= n->cap) {
    fprintf(stderr, "lin: fatal: allocation past the wave's reservation (node %d, cap %d).\n",
            id, n->cap);
    fflush(stderr);
    abort();
  }
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

/* Plugin hook: enqueue an active redex pair; used by drivers that commit link-rewrites and rebuild the continuation set. */
void lin_enqueue(Net *n, Port a, Port b) { act_push(n, a, b); }

/* Driver native-fold accounting: drivers bump this when folding natively; exposed so tests can assert folding fires. */
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

/* The external boundary of an interacting pair.

   Union the pair's six ports, {n1.0,n1.1,n1.2,n2.0,n2.1,n2.2} as 0..5, along every wire that stays
   inside the pair and along the rule's correspondence `ca[k]~cb[k]`; each class then presents the
   ports it leads to OUTSIDE the pair, and presents exactly two -- join them.  A class presenting none
   is a wire closed inside the pair (beta on `\x.x`) and needs nothing.  No case analysis at all,
   which is what the hand-written per-shape branches used to get wrong. */
static int pfind(int *u, int x) { while (u[x] != x) { u[x] = u[u[x]]; x = u[x]; } return x; }
static void punion(int *u, int a, int b) { a = pfind(u, a); b = pfind(u, b); if (a != b) u[b] = a; }
static void pair_boundary(Net *n, int n1, int n2, const int *ca, const int *cb, int ncor, int link, Port *tgt) {
  Port p[6]; int u[6];
  for (int i = 0; i < 6; i++) {
    p[i] = (Port){i < 3 ? n1 : n2, i % 3}; u[i] = i;
    if (tgt) tgt[i] = (Port){-1, 0};
  }
  for (int i = 0; i < 6; i++) {
    Port w = WIRE(n, p[i]);
    if (w.node == n1) punion(u, i, w.port);
    else if (w.node == n2) punion(u, i, 3 + w.port);
  }
  for (int k = 0; k < ncor; k++) punion(u, ca[k], cb[k]);
  for (int i = 0; i < 6; i++) {
    if (pfind(u, i) != i) continue;
    Port e[2]; int ne = 0, ix[2] = {-1, -1};
    for (int j = 0; j < 6; j++) {
      if (pfind(u, j) != i) continue;
      Port w = WIRE(n, p[j]);
      if (w.node == n1 || w.node == n2) continue;   /* the wire stays inside the pair */
      if (ne < 2) { e[ne] = w; ix[ne] = j; }
      ne++;
    }
    if (ne != 2) continue;                          /* closed inside, or not a two-ended class */
    /* Join them, with no case for the two ports belonging to one node.  Skipping that case (which
       this did, on the grounds that a fan two of whose ports meet is "already represented by that
       fan") is what left a port pointing at a node the rule had just killed: measured on
       `((\x (x x)) c2)`, which then read back as `_` -- a DISCARDED node, not a value -- where the
       general join reads back as a knot whose value applying it recovers.  It is also what the
       reference does: its beta is exactly the two linkings, with no case analysis at all. */
    if (tgt) { tgt[ix[0]] = e[1]; tgt[ix[1]] = e[0]; }
    if (link && ix[0] < ix[1]) net_link(n, e[0], e[1], 1);
  }
}

/* The 2x2 split both duplication rules perform: two copies of each interacting node, cross-connected
   so copy i of the first meets copy j of the second.  One description, so the two cannot drift. */
static void split2(Net *n, int t1, Scope s1a, Scope s1b, const char *nm1,
                   int t2, Scope s2, const char *nm2, int *m1, int *m2, int *d1, int *d2) {
  *m1 = net_alloc(n, t1, s1a, nm1).node; *m2 = net_alloc(n, t1, s1b, nm1).node;
  *d1 = net_alloc(n, t2, s2, nm2).node; *d2 = net_alloc(n, t2, s2, nm2).node;
  net_link(n, (Port){*d1, 1}, (Port){*m1, 1}, 0); net_link(n, (Port){*d1, 2}, (Port){*m2, 1}, 0);
  net_link(n, (Port){*d2, 1}, (Port){*m1, 2}, 0); net_link(n, (Port){*d2, 2}, (Port){*m2, 2}, 0);
}

/* Hand the pair's four auxiliaries to the four copies a duplication rule just made.  Each copy takes
   the place of one auxiliary -- UNLESS two of them are shorted to EACH OTHER, i.e. their class is
   closed inside the pair.  There the two copies must be joined to each other; wiring one onto a port
   of a node the rule has already killed leaves a live node pointing at a discarded one, which is
   exactly what readback reports as `_` (measured on a nested Y-knot: a DUP's aux2 wired to its
   partner's aux2, and the copy for it landed on the dead node's port).
   `t[k]` is what auxiliary k leads to; `cp[k]` is the copy that takes it over. */
static void link_copies(Net *n, int n1, int n2, const Port *t, const int *cp) {
  int inside[4] = {0, 0, 0, 0};
  for (int k = 0; k < 4; k++) {
    int m = t[k].node == n1 ? (t[k].port == 1 ? 0 : 1)
          : t[k].node == n2 ? (t[k].port == 1 ? 2 : 3) : -1;
    if (m < 0 || m <= k || inside[k]) continue;
    inside[k] = inside[m] = 1;
    net_link(n, (Port){cp[k], 0}, (Port){cp[m], 0}, 1);
  }
  for (int k = 0; k < 4; k++) if (!inside[k]) net_link(n, (Port){cp[k], 0}, t[k], 1);
}

/* the four rules of the scope-gauge calculus; ERA is inert (era pairs are dropped) */
static int lin_trace = -1; /* cached LIN_TRACE */

/* Driver pipeline: sorted by priority (ascending); core waves fan out to each in priority order, each
   *claiming* the redexes it handles, so drivers compose.  A driver only ever pre-empts a redex class;
   every rule the core keeps (β, δ⋈δ, γ⋈δ, ε) is complete without one. */
static LinDriver *drv[16]; static int ndrv;

int net_interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (lin_trace < 0) lin_trace = getenv("LIN_TRACE") != NULL;
  if (lin_trace)
    fprintf(stderr, "step %ld: %d.%d x %d.%d\n", n->steps, t1, n1, t2, n2);

  if (t1 == LAM && t2 == APP) {
    n->dead[n1] = 1; n->dead[n2] = 1;
    const int cor_a[2] = {1, 2}, cor_b[2] = {5, 4};
    pair_boundary(n, n1, n2, cor_a, cor_b, 2, 1, NULL);
    return 1;
  }

  if (t1 == DUP && t2 == DUP) {
    if (!scope_eq(n, n->scope[n1], n->scope[n2])) {
      /* Two fans with distinct levels meet: fans are copied by each other (the only alternatives
         are annihilating two unrelated fans -- a wrong value -- or stranding the pair).  What differs
         is the LEVEL the copies carry: d1,d2 split n1's value between n2's two uses and carry sb,
         while m1,m2 carry sa.  Labels are compared only for equality, so a wrong one cannot
         re-duplicate work -- but it can merge two distinct sharing points. */
      Scope sa = n->scope[n1], sb = n->scope[n2];
      Scope qa = sa, qb = sb;
      /* NESTED levels -- one gauge a proper prefix of the other -- are the RECURSIVE sharing point
         and take the ANCESTOR's level.  Without this case the fan duplicates the structure it came
         from for ever (measured: no value in 16M steps), because it is the mechanism by which a
         self-referential sharing point SHARES instead of unrolling. */
      if (scope_within(n, sa, sb)) { qa = qb = sa; }
      else if (scope_within(n, sb, sa)) { qa = qb = sb; }
      Port t[4] = { WIRE(n, ((Port){n1, 1})), WIRE(n, ((Port){n1, 2})),
                    WIRE(n, ((Port){n2, 1})), WIRE(n, ((Port){n2, 2})) };
      const char *nm = n->name[n1] ? n->name[n1] : "";
      int m1, m2, d1, d2;
      split2(n, DUP, qa, qa, nm, DUP, qb, nm, &m1, &m2, &d1, &d2);
      n->dead[n1] = 1; n->dead[n2] = 1;
      const int cp[4] = {d1, d2, m1, m2};
      link_copies(n, n1, n2, t, cp);
      return 1;
    }
    /* Annihilation is the correspondence {a1~b1, a2~b2} (1~4, 2~5) -- the same rewire, so the four
       branches that used to special-case two fans wired to each other are gone. */
    const int cor_a[2] = {1, 2}, cor_b[2] = {4, 5};
    n->dead[n1] = 1; n->dead[n2] = 1;
    pair_boundary(n, n1, n2, cor_a, cor_b, 2, 1, NULL);
    return 1;
  }

  if ((t1 == LAM || t1 == APP) && t2 == DUP) {
    Scope sn = n->scope[n1], sd = n->scope[n2];
    Scope sm = scope_meet(n, sn, sd);        /* the level the two histories share */
    Port t[4] = { WIRE(n, ((Port){n1, 1})), WIRE(n, ((Port){n1, 2})),
                  WIRE(n, ((Port){n2, 1})), WIRE(n, ((Port){n2, 2})) };
    const char *nm = n->name[n1] ? n->name[n1] : "";
    int m1, m2, d1, d2;
    split2(n, t1, scope_app(n, sm, 1), scope_app(n, sm, 2), nm, DUP, sd, "", &m1, &m2, &d1, &d2);
    n->dead[n1] = 1; n->dead[n2] = 1;
    const int cp[4] = {d1, d2, m1, m2};
    link_copies(n, n1, n2, t, cp);
    return 1;
  }
  return 0; /* era or stuck gauge pair: dropped, as in the reference */
}

/* Reclaim every node not reachable from ROOT.  The `.line` container stores ALL nodes and an actual
   evaluation leaves far more dead intermediates than live ones: without this the baked artifact came
   out ~2x LARGER than the un-evaluated one (474 KB vs 224 KB) despite being a value. */
static void net_compact(Net *n, const unsigned char *reach);   /* fwd */

void net_gc(Net *n) {
  if (n->nn <= 1) return;
  unsigned char *reach = malloc((size_t)n->nn + 1);
  int *q = malloc(((size_t)n->nn + 1) * sizeof(int));
  memset(reach, 0, (size_t)n->nn + 1);
  int qh = 0, qt = 1; reach[0] = 1; q[0] = 0;
  while (qh < qt) { int u = q[qh++];
    for (int p = 0; p < 3; p++) { Port w = n->wire[u * 3 + p];
      if (w.node >= 0 && w.node < n->nn && !n->dead[w.node] && !reach[w.node]) { reach[w.node] = 1; q[qt++] = w.node; } } }
  net_compact(n, reach);
  free(reach); free(q);
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
/* Driver registration (the table itself is declared above β, which consults it).  Drivers are sorted by priority
   ascending and the core waves fan out to each in that order, so a driver with a lower priority number pre-empts. */
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
/* `(set_driver ...)`/`driver_clear` selects a *strategy*; pre-emptors are a reduction pre-pass that
   composes with whichever strategy is chosen, so clearing must not silently disable native folding.
   Compacting in place keeps the priority order intact.  Idempotent, because a plugin's constructor
   registers its driver when the .so is dlopen'd and `(set_driver "<its own name>")` would add it
   again, leaving the same reducer to claim every wave twice. */
void lin_driver_clear(void) {
  int w = 0;
  for (int i = 0; i < ndrv; i++) if (drv[i]->caps & LIN_CAP_PREEMPT) drv[w++] = drv[i];
  ndrv = w;
}
/* the active *strategy* (never a pre-emptor), so `(get_driver)` still reports cpu/simd/gpu */
LinDriver *lin_get_driver(void) {
  for (int i = ndrv - 1; i >= 0; i--) if (!(drv[i]->caps & LIN_CAP_PREEMPT)) return drv[i];
  return NULL;
}

/* ---------------- needed order ----------------
   A redex is reduced only when the value the caller observes needs it.  `net_mark_demand` walks from
   the demand roots -- ROOT (the program's result) plus every port lin_demand/net_force registered --
   along the paths a weak head normal form of those ports actually runs through:

     ROOT          -> its wire (the result)
     APP   port 1  -> port 0 (a demanded result demands its function)
     APP   port 2  -> its wire (a demanded application's argument)
     DUP   port 1/2-> port 0 (a use of a shared value demands the sharing point)
     LAM   port 0  -> WHNF: stop, UNLESS a principal faces it, which is the redex to fire
     APP/DUP p. 0  -> same: a facing principal is a redex, otherwise stop
     LAM   port 2  -> stop: a lambda's body is a thunk until the lambda is applied

   Every rule of the calculus is untouched; the filter only decides WHICH active pairs are in a wave.
   A pair off the demand path stays queued in `act` and is picked up by a later wave, which is what
   makes a cycle (a Y-knot) reduce when the recursive call is demanded instead of unrolling for ever. */
static void net_mark_demand(Net *n) {
  unsigned int stamp = ++n->dem_stamp;
  if (!stamp) { for (int i = 0; i < n->cap; i++) n->dem[i] = 0; stamp = n->dem_stamp = 1; }
  int cap = n->nroot + 8, top = 0;
  Port *st = malloc((size_t)cap * sizeof(Port));
  st[top++] = (Port){0, 0};
  for (int i = 0; i < n->nroot; i++) st[top++] = n->root[i];
  while (top > 0) {
    Port p = st[--top];
    for (;;) {
      int u = p.node;
      if (u < 0 || u >= n->nn || n->dead[u]) break;
      /* Visited PER PORT, not per node: an APP reached at its result and at its argument continues
         differently, so a node-level mark would cut the second path off and leave the redexes it
         leads to permanently un-demanded (measured: a Y-knot that stops reducing at depth 4). */
      unsigned char bit = (unsigned char)(1u << p.port);
      if (n->dem[u] == stamp) { if (n->vport[u] & bit) break; n->vport[u] |= bit; }
      else { n->dem[u] = stamp; n->vport[u] = bit; }
      int t = n->tag[u];
      if (t == ROOT) { p = WIRE(n, p); continue; }
      if (t == ERA) break;
      if (t == LAM && p.port != 0) break;               /* binder / body: a thunk until applied */
      if (t == APP && p.port != 0) { p = WIRE(n, ((Port){u, 0})); continue; }  /* result -> function */
      if (t == DUP && p.port != 0) { p = WIRE(n, ((Port){u, 0})); continue; }  /* aux -> sharing point */
      /* At a principal port: WHNF if nothing faces it, a redex pair if a principal does.  Marking
         the facing node is enough -- the wave fires the pair, and the next walk continues past it. */
      Port q = WIRE(n, p);
      if (q.node >= 0 && q.node < n->nn && q.port == 0 && !n->dead[q.node]) {
        int qt = n->tag[q.node];
        if ((t == LAM && (qt == APP || qt == DUP)) || (t != LAM && (qt == LAM || qt == DUP))) {
          if (n->dem[q.node] != stamp) n->vport[q.node] = 0;
          n->dem[q.node] = stamp;
        }
      }
      break;
    }
  }
  free(st);
}

static inline int demanded(const Net *n, Port p) {
  return p.node >= 0 && p.node < n->nn && n->dem[p.node] == n->dem_stamp;
}

/* Is `p` a bare, unreducible lambda -- a value already?  This is the ONE cheap case, and it is the
   common one: readback forces once per port it prints, and most ports of a reduced value ARE such
   lambdas.  Anything else gets a real (wave-wide) reduction: guessing "already in WHNF" more
   aggressively than this is what silently skipped the reductions readback needed. */
static int port_whnf(Net *n, Port p) {
  int u = p.node;
  if (u < 0 || u >= n->nn || n->dead[u]) return 1;
  if (n->tag[u] != LAM || p.port != 0) return 0;      /* not a bare lambda: let the reducer decide */
  Port q = WIRE(n, p);
  return !(q.node >= 0 && q.node < n->nn && q.port == 0 && !n->dead[q.node] &&
           (n->tag[q.node] == APP || n->tag[q.node] == DUP));
}

long net_force(Net *n, Port p) {
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || port_whnf(n, p)) return n->steps;
  int save = n->nroot;
  lin_demand(n, p);
  long s = net_reduce(n, n->steps + (1L << 22));
  n->nroot = save;
  return s;
}

/* Is (p1,p2) still one live redex?  A pair is a redex only while both ends are alive and still
   wired to each other principal-to-principal; the wave snapshot is a snapshot, so any earlier
   interaction in the same wave can invalidate a later pair. */
static inline int redex_live(Net *n, Port p1, Port p2) {
  if (p1.node < 0 || p2.node < 0 || p1.node >= n->nn || p2.node >= n->nn || p1.port || p2.port) return 0;
  if (n->dead[p1.node] || n->dead[p2.node]) return 0;
  return WIRE(n, p1).node == p2.node && WIRE(n, p1).port == p2.port &&
         WIRE(n, p2).node == p1.node && WIRE(n, p2).port == p1.port;
}

/* Frontier scratch: grown, never freed per wave (a driver may hold a wave for a long time). */
static Pair *inter, *bound;
static int *fw_next, *fw_slot, *fw_occ;
static int fw_cap, fw_pair_cap, fw_slot_cap;

/* Reduce one wave of `act`-form pairs (an even count): spatially disjoint pairs run concurrently via
   OpenMP, the rest serially; exposed so a driver's reducer fans out a real wave. */
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed) {
#ifdef _OPENMP
  ensure_tact();
  int nth = omp_get_max_threads();

  if (nth > 1 && wave_cnt >= 512) {
    int np = wave_cnt / 2;
    /* grow-only scratch, so a wave performs no allocation at all */
    if (np > fw_cap) {
      fw_cap = np;
      inter = realloc(inter, (size_t)np * sizeof(Pair));
      bound = realloc(bound, (size_t)np * sizeof(Pair));
    }
    int n_int = 0, n_bnd = 0;
    for (int i = 0; i < wave_cnt; i += 2) {
      Port p1 = curr[i], p2 = curr[i + 1];
      if (!redex_live(n, p1, p2)) continue;
      int u = p1.node, v = p2.node, su = u >> 6, ok = (su == (v >> 6));
      if (ok) {
        int c[4] = { WIRE(n, ((Port){u, 1})).node, WIRE(n, ((Port){u, 2})).node,
                     WIRE(n, ((Port){v, 1})).node, WIRE(n, ((Port){v, 2})).node };
        for (int k = 0; k < 4; k++) if (c[k] >= 0 && (c[k] >> 6) != su) { ok = 0; break; }
      }
      /* gamma-delta allocates level ids, and interning writes the net's shared trie, so those
         pairs run in the serial phase (they were the reason the old code reserved gauge space
         up front); the rest of the batch stays parallel. */
      if (ok && n->tag[u] == DUP && n->tag[v] != DUP) ok = 0;
      if (ok && n->tag[v] == DUP && n->tag[u] != DUP) ok = 0;
      if (ok) inter[n_int++] = (Pair){p1, p2}; else bound[n_bnd++] = (Pair){p1, p2};
    }
    if (n_int > 0) {
      /* Work-efficient frontier: pairs are bucketed by sector in a table sized to the WAVE, only
         occupied buckets are iterated, and every buffer is a grow-only static -- so a wave allocates
         nothing and its dispatch costs O(pairs).  (The previous form memset a sector table sized to
         the NET on every wave: measured, 8 threads came out 2x SLOWER than serial.) */
      int need = 8; while (need < n_int * 2) need *= 2;
      if (need > fw_slot_cap) {
        fw_slot = realloc(fw_slot, (size_t)need * sizeof(int));
        for (int i = fw_slot_cap; i < need; i++) fw_slot[i] = -1;
        fw_slot_cap = need;
      }
      if (n_int > fw_pair_cap) {
        fw_pair_cap = n_int;
        fw_next = realloc(fw_next, (size_t)n_int * sizeof(int));
        fw_occ = realloc(fw_occ, (size_t)n_int * sizeof(int));
      }
      const int mask = need - 1;
      int n_occ = 0;
      for (int i = 0; i < n_int; i++) {
        int sec = inter[i].p1.node >> 6;
        unsigned h = (unsigned)sec & (unsigned)mask;
        while (fw_slot[h] >= 0 && (inter[fw_slot[h]].p1.node >> 6) != sec) h = (h + 1) & (unsigned)mask;
        if (fw_slot[h] < 0) { fw_slot[h] = i; fw_next[i] = -1; fw_occ[n_occ++] = (int)h; }
        else { fw_next[i] = fw_slot[h]; fw_slot[h] = i; }
      }
      net_ensure_cap(n, n->nn + n_int * 4);
      in_parallel = 1; int batch_changed = 0;
      #pragma omp parallel for reduction(+:batch_changed) schedule(dynamic)
      for (int oi = 0; oi < n_occ; oi++) {
        int h = fw_occ[oi];
        for (int i = fw_slot[h]; i >= 0; i = fw_next[i])
          if (redex_live(n, inter[i].p1, inter[i].p2))
            if (net_interact(n, inter[i].p1, inter[i].p2)) batch_changed++;
      }
      in_parallel = 0; n->steps += n_int; *changed += batch_changed;
      for (int t = 0; t < nth; t++) {
        for (int j = 0; j < t_act[t].top; j += 2) act_push(n, t_act[t].p[j], t_act[t].p[j + 1]);
        t_act[t].top = 0;
      }
      for (int oi = 0; oi < n_occ; oi++) fw_slot[fw_occ[oi]] = -1;   /* clear only what we used */
    }
    for (int i = 0; i < n_bnd; i++) {
      Port p1 = bound[i].p1, p2 = bound[i].p2;
      if (redex_live(n, p1, p2)) { if (net_interact(n, p1, p2)) *changed += 1; n->steps++; }
    }
    return;
  }
#endif
  for (int i = 0; i < wave_cnt; i += 2) {
    Port p1 = curr[i], p2 = curr[i + 1];
    if (!redex_live(n, p1, p2)) continue;
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
  /* Self-collecting nets reduce by the active list; BFS+compact reclaims memory after it doubles.
     Each wave re-marks demand and fires only the active pairs the demand walk reached; a pair off
     the demand path is pushed back, so it is still there when something needs it.  A wave in which
     nothing on the demand path could fire means the observed ports are already in WHNF: stop,
     rather than spin on the queued pairs. */
  Port *curr = NULL; int curr_cap = 0;
  Port *base_rx = NULL; int base_cap = 0;
  long gcmark = 1L << 20;
  Port *slices[16] = {0}; int scaps[16] = {0}, scnts[16] = {0};
  while (n->steps < limit) {
    int changed = 0;
    while (n->atop > 0 && n->steps < limit) {
      int before = changed;
      int cnt = wave_snapshot(n, &curr, &curr_cap);
      if (cnt <= 0) break;
      net_mark_demand(n);
      int np = cnt / 2, base_cnt = 0;

      /* partition the wave by demand, then by driver claim (priority order) */
      for (int di = 0; di < ndrv; di++) scnts[di] = 0;
      for (int i = 0; i < np; i++) {
        Port p1 = curr[i*2], p2 = curr[i*2+1];
        /* Off the demand path: keep it queued for when something needs it -- but only while it is
           still a live redex, or a long reduction accumulates pairs no rule can ever fire. */
        if (!demanded(n, p1) || !demanded(n, p2)) { if (redex_live(n, p1, p2)) act_push(n, p1, p2); continue; }
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
      if (changed == before) break;
    }
    if ((long)n->nn > gcmark) {
      net_gc(n);
      n->dem_stamp++;               /* compaction renumbers nodes, so every mark is stale */
      gcmark = (long)n->nn * 2 + 64;
      /* Resume-seed: every live principal pair EXCEPT ROOT's.  A fresh load seeds ROOT's pair too
         (that is what starts the machine); here reduction is already under way and re-adding ROOT
         would count its pair as a step again, so the two seeds are deliberately not one loop. */
      for (int i = 1; i < n->nn; i++) if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
        act_push(n, (Port){i, 0}, n->wire[i * 3]);
    }
    if (changed == 0) break;
  }
  free(curr); free(base_rx);
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
  c->dem = calloc(c->cap, sizeof(unsigned int)); c->dem_stamp = 0;
  c->vport = calloc(c->cap, 1);
  c->nlv = 0; c->lvcap = 0; c->lv_hcap = 0; c->lv_hash = NULL;
  c->lv_parent = NULL; c->lv_depth = NULL; c->lv_bit = NULL;
  net_level_set(c, n->nlv, n->lv_parent + 1, n->lv_bit + 1);   /* rebuild the trie: parents precede children, ids reload directly */
  c->act = NULL; c->actcap = c->atop = 0; c->steps = 0;
  c->root = NULL; c->nroot = 0; c->rootcap = 0;
  return c;
}
