#include "lin.h"
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
#define NONE ((Port){-1, 0})
#define NAT_IN(n, i) ((i) >= 0 && (i) < (n)->nn)

Scope scope_nil(void) { return 0; }
static int in_parallel;   /* a wave is running threaded: no interning there (see below) */
static int reduce_depth;  /* how deep the reducer is; only the outermost may publish or reclaim */
static int nested_reduce; /* a driver's reducer ran inside the wave being dispatched (see net_flush_free) */

/* The driver table (declared here because net_alloc and net_free both consult it).  Sorted by
   priority ascending, and a driver with a lower priority number pre-empts. */
static LinDriver *drv[16]; static int ndrv;
/* Slot ownership is permanent: a cleared driver keeps its slot, so nets holding its state can
   still release it. */
static LinDriver *dslot[LIN_DRV_SLOTS];
static int any_recycle;    /* some driver wants node_recycled: keep the hot path free of the loop */
static int any_state;      /* some driver keeps per-net state (so net_free/net_copy must sweep) */

/* Read only fields that fit inside `size`: this is what makes appending a hook not a break. */
#define DRV_HAS(d, field) ((d)->size >= (uint32_t)(offsetof(LinDriver, field) + sizeof((d)->field)))

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
  n->scope = malloc(cap * sizeof(Scope));
  n->act = NULL; n->atop = 0; n->actcap = 0; n->dead = calloc(cap, 1);
  n->lv_parent = NULL; n->lv_depth = NULL; n->lv_bit = NULL; n->lv_hash = NULL;
  n->nlv = 0; n->lvcap = 0; n->lv_hcap = 0;
  lv_ensure(n, 1);                      /* the root level always exists */
  n->lv_parent[0] = 0; n->lv_bit[0] = 0; n->lv_depth[0] = 0;
  n->nn = 0; n->steps = 0;
  n->root = NULL; n->nroot = 0; n->rootcap = 0; n->free_head = -1; n->nfree = 0; n->pend_head = -1; n->pins = 0;
  n->dem = calloc((size_t)cap, sizeof(unsigned int)); n->dem_stamp = 0;
  n->vport = calloc((size_t)cap, 1);
  memset(n->drv, 0, sizeof n->drv);
  n->nheld = 0;
  net_alloc(n, ROOT, scope_nil());
}

void net_free(Net *n) {
  for (int i = 0; i < n->nheld; i++) {
    LinDriver *d = n->held_drv[i];
    if (d && DRV_HAS(d, release_claim) && d->release_claim)
      d->release_claim(n, d->slot >= 0 && d->slot < LIN_DRV_SLOTS ? n->drv[d->slot] : NULL, &n->held[i]);
  }
  n->nheld = 0;
  for (int i = 0; i < LIN_DRV_SLOTS; i++)
    if (n->drv[i] && dslot[i] && DRV_HAS(dslot[i], state_free) && dslot[i]->state_free)
      dslot[i]->state_free(n, n->drv[i]);
  memset(n->drv, 0, sizeof n->drv);
  free(n->tag); free(n->wire); free(n->scope); free(n->act); free(n->dead); free(n->dem); free(n->vport);
  free(n->lv_parent); free(n->lv_depth); free(n->lv_bit); free(n->lv_hash);
  free(n->root);
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
  n->scope = realloc(n->scope, (size_t)nc * sizeof(Scope));
  n->dead = realloc(n->dead, (size_t)nc); memset(n->dead + n->cap, 0, (size_t)(nc - n->cap));
  n->dem = realloc(n->dem, (size_t)nc * sizeof(unsigned int));
  memset(n->dem + n->cap, 0, (size_t)(nc - n->cap) * sizeof(unsigned int));   /* 0 = never marked */
  n->vport = realloc(n->vport, (size_t)nc); memset(n->vport + n->cap, 0, (size_t)(nc - n->cap));
  n->cap = nc;
}

Port net_alloc(Net *n, int tag, Scope sc) {
  int id = -1;
  /* Reuse a reclaimed slot.  NOT inside a wave: the parallel path reserves room by growing `nn` and
     every worker holds raw pointers into the arrays, so two of them must not race for one free slot.
     THIS is why reclaiming a consumed pair does not yet save memory: rules allocate inside the wave,
     so the pop below is never taken there and `nn` grows regardless of how much was freed.  Measured
     with reaping on and off (steps identical, so the comparison is like for like): sudoku 14106 vs
     14178 slots, bench_loop 36565 vs 36577, nqueens 11510 vs 11854 -- 0.5%, and at most 3%.  The
     freeing is correct and cheap (best-of-5: 3.72 vs 3.70 ms) but dormant; making it pay needs the
     wave to hand each worker a PRIVATE slice of the free list while the region is open, so a worker
     can pop without racing for a slot. */
  
  if (!in_parallel && n->free_head >= 0) {
    id = n->free_head;
    n->free_head = n->wire[id * 3].node;
    n->nfree--;
    n->dem[id] = 0; n->vport[id] = 0;        /* a reused slot is not the node that was marked */
    /* Recycling: the one event a driver cannot observe, and what makes a node-keyed table sound.
       Off unless a driver asks. */
    if (any_recycle)
      for (int i = 0; i < ndrv; i++) {
        LinDriver *d = drv[i];
        if (!DRV_HAS(d, node_recycled) || !d->node_recycled) continue;
        d->node_recycled(n, n->drv[d->slot], id);
      }
  } else {
    if (!in_parallel) net_ensure_cap(n, n->nn + 1);
    id = __atomic_fetch_add(&n->nn, 1, __ATOMIC_RELAXED);
  }
  /* While a wave is threaded, growth is skipped: `realloc` would move the arrays out from under every
     worker holding raw pointers into them.  The wave reserves up front, and this check makes breaking
     that reservation loud instead of writing past the arrays.  Drivers never run in that region. */
  if (id >= n->cap) {
    fprintf(stderr, "lin: fatal: allocation past the wave's reservation (node %d, cap %d).\n",
            id, n->cap);
    fflush(stderr);
    abort();
  }
  n->tag[id] = tag; n->dead[id] = 0; n->scope[id] = sc;
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

/* Cut the wire at `p`, at BOTH ends.  The calculus itself never needs this -- a rule always relinks
   the ports it takes over -- but DISPOSING of a subgraph does: whatever is abandoned must be cut loose,
   or a live node is left pointing into a node that no longer exists.  Cutting is also what erases: the
   subgraph becomes unreachable, and so reclaimable.  This is what `pair_boundary` uses for a class
   whose other end was never wired (an unused binder), and what a driver uses for the subgraph a fold
   replaces.  It is deliberately not a "free": it removes connections and nothing else. */
void lin_pin(Net *n) { n->pins++; }
void lin_unpin(Net *n) { if (n->pins > 0) n->pins--; }

/* How many of `v`'s ports lead to a LIVE node.  A node whose connections all lead into freed nodes
   is as unreachable as one with no wires at all, so the count has to look through to the target. */
static int deg_live(const Net *n, int v) {
  int d = 0;
  for (int p = 0; p < 3; p++) {
    Port w = n->wire[v * 3 + p];
    if (w.node >= 0 && w.node < n->nn && !n->dead[w.node]) d++;
  }
  return d;
}

/* Free `v`, and everything that loses its LAST live connection because of it -- which is the whole of
   "reclamation is inherent to the node architecture": a node is garbage exactly when nothing live
   reaches it, and cutting a wire is the only way that happens, so the cascade is local and needs no
   traversal of the net.  An explicit worklist, because a subgraph can be arbitrarily deep and this
   runs inside a rule. */
/* Is `v` ours to free?  A node that a LIVE node is still wired TO is not: its ports are somebody
   else's structure.  This is the ownership test that was missing, and its absence is what made an
   unconditional free destroy live structure -- a closure reached through a fan is still tagged LAM,
   so no test on the node's own tag can see the sharing.  A one-sided wire (a partner that no longer
   points back) does not make us owned: that is a partner the rules have already relinked away. */
static int unowned(const Net *n, int v) {
  for (int p = 0; p < 3; p++) {
    Port w = n->wire[v * 3 + p];
    if (w.node < 0 || w.node >= n->nn) continue;
    if (n->dead[w.node]) continue;                       /* a dying partner does not own us */
    if (n->wire[w.node * 3 + w.port].node == v && n->wire[w.node * 3 + w.port].port == p) return 0;
  }
  return 1;
}

/* The work itself.  `v` is already marked dead by the caller, which is how a pair that owns each
   other is freed together (marking dead first is also what makes one's death invisible to the
   other's ownership test). */
static void release_now(Net *n, int v) {
  int cap = 32, sp = 0, *st = malloc((size_t)cap * sizeof(int));
  if (!st) return;
  st[sp++] = v;
  while (sp > 0) {
    int u = st[--sp];
    for (int p = 0; p < 3; p++) {
      Port w = WIRE(n, ((Port){u, p}));
      WIRE(n, ((Port){u, p})) = NONE;
      if (w.node < 0 || w.node >= n->nn) continue;
      /* Only clear the partner's wire if it still points back at u.  After a rule has relinked a
         partner, it points somewhere else and that connection is LIVE -- cutting it here would be
         the same mistake, from the other side, that abandoning a subgraph makes. */
      if (WIRE(n, w).node == u && WIRE(n, w).port == p) WIRE(n, w) = NONE;
      /* A partner that has lost its LAST live connection is garbage and goes too.  No ownership test
         is needed here: with no live connections nothing live can be wired to it either. */
      if (!n->dead[w.node] && deg_live(n, w.node) == 0) {
        n->dead[w.node] = 1;
        if (sp == cap) { cap *= 2; st = realloc(st, (size_t)cap * sizeof(int)); }
        st[sp++] = w.node;
      }
    }
    n->tag[u] = ERA;
    n->wire[u * 3] = (Port){n->pend_head, 0};      /* held until the wave's snapshot is gone */
    n->pend_head = u;
    n->nfree++;
  }
  free(st);
}

/* Publish this wave's freed slots: only here does an index become reusable, which is what makes it
   safe for a snapshot, a driver slice or a readback cursor to hold one across the wave that freed
   it. */
static void net_flush_free(Net *n) {
  /* A NESTED reduce must not publish.  Reuse is what makes an index dangerous: a wave snapshot, a
     driver slice or an active-list entry that merely names a FREED slot is rejected by redex_live,
     but one that names a slot since handed to a fresh node passes it, and the stale holder then
     fires a rule on a node it never saw.  Publication belongs to the outermost boundary, where no
     holder of this wave's indices is left. */
  if (reduce_depth > 1) return;
  while (n->pend_head >= 0) {
    int v = n->pend_head;
    n->pend_head = n->wire[v * 3].node;
    n->wire[v * 3] = (Port){n->free_head, 0};
    n->free_head = v;
  }
}

/* Free a node the caller OWNS.  Declines when something live is still wired to it, because then it
   is not garbage, however dead it looks from the caller's side. */
static void net_release(Net *n, int v) {
  if (v < 0 || v >= n->nn || n->dead[v]) return;
  if (!unowned(n, v)) return;
  if (in_parallel || n->pins) return;   /* the SAFEPOINT: a readback walk is holding ports */
  n->dead[v] = 1;
  release_now(n, v);
}

void net_sever(Net *n, Port p) {
  if (p.node < 0 || p.node >= n->nn) return;
  Port w = WIRE(n, p);
  WIRE(n, p) = NONE;
  if (w.node >= 0 && w.node < n->nn && WIRE(n, w).node == p.node && WIRE(n, w).port == p.port)
    WIRE(n, w) = NONE;
  /* Cutting a wire can be the event that makes a node garbage.  Reaping only when the degree has
     reached ZERO is what keeps a shared node alive: it still has its other users. */
  if (deg_live(n, p.node) == 0) net_release(n, p.node);
  if (w.node >= 0 && w.node < n->nn && deg_live(n, w.node) == 0) net_release(n, w.node);
}

/* Reclamation has ONE safepoint, and it is the collector's: `reduce_depth == 1` (the outermost
   reduce, so no readback force is in progress) and `pins == 0` (no walk is holding a port).  Both
   halves are load-bearing for the free list and both were measured: without the depth test a nested
   reduce entered from a driver's reducer publishes slots the wave it is dispatched from still names,
   and without the pins test test/ffi.lin prints its closure unreduced.  A freed slot nobody reuses is
   harmless; REUSE is what turns a stale index into a wrong node, since redex_live rejects a dead slot
   but accepts the fresh node that replaced it. */

/* Retire the two nodes a rule consumed: the rule owns exactly this pair, so they are freed together.
   Both are marked dead first, because their principals are wired to each other and the ownership test
   below would otherwise find a live partner and decline.  Reaping is sound here because every class
   pair_boundary sees is accounted for: a class needs s-1 edges to be connected and has at most `i`
   internal wires plus 2 correspondence edges, while its outside ends number s-2i-u -- so `ne >= 4`
   would need more correspondence edges than beta or delta-delta have.  ne is therefore 0 (closed
   inside the pair), 1 (the unused-binder erasure the rule severs) or 2 (joined). */
static void retire(Net *n, int a, int b) {
  n->dead[a] = 1; n->dead[b] = 1;      /* both ends of the pair go together, so neither owns the other */
  /* A NESTED reduce is entered from net_force, which READBACK calls while it holds ports of its own
   (its cursor, its recursion stack, the result port it is about to inspect).  Reaping there is the
   free-list twin of collecting at a non-safepoint: the slot is handed out again while a handle still
   names it, so the forced chain comes back as NONE and readback stops recognising the value.  The
   same holds for the readback walk itself: net_print pins the whole walk, and the reduce it enters by
   forcing is the OUTERMOST one (reduce_depth == 1), so the depth test alone does not see it -- `pins`
   does.  Measured: with this guard removed, test/ffi.lin prints its closure unreduced. */
  if (reduce_depth > 1 || n->pins || in_parallel || getenv("LIN_NORETIRE")) return;
  release_now(n, a); release_now(n, b);
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
      if (w.node < 0) continue;                     /* an UNCONNECTED port is not an outside end */
      if (ne < 2) { e[ne] = w; ix[ne] = j; }
      ne++;
    }
    /* ONE connected end: the class's other port was never wired -- an unused binder, which the
       compiler leaves unconnected -- so the value the class carries goes NOWHERE.  That is erasure,
       and disconnecting it is what erases: the subgraph it led to becomes unreachable and
       reclaimable.  Counting the unconnected end as a real end instead (the old behaviour) made
       net_link a silent no-op, which left the surviving end pointing at a node this rule had just
       killed: measured, that was 889 such wires on test/map.lin and 581 on sudoku, EVERY one of
       them a beta, and the whole of the collector's unsoundness. */
    if (ne == 1) {
      if (link) net_sever(n, e[0]);
      continue;
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
static void split2(Net *n, int t1, Scope s1a, Scope s1b,
                   int t2, Scope s2, int *m1, int *m2, int *d1, int *d2) {
  *m1 = net_alloc(n, t1, s1a).node; *m2 = net_alloc(n, t1, s1b).node;
  *d1 = net_alloc(n, t2, s2).node; *d2 = net_alloc(n, t2, s2).node;
  net_link(n, (Port){*d1, 1}, (Port){*m1, 1}, 0); net_link(n, (Port){*d1, 2}, (Port){*m2, 1}, 0);
  net_link(n, (Port){*d2, 1}, (Port){*m1, 2}, 0); net_link(n, (Port){*d2, 2}, (Port){*m2, 2}, 0);
}

/* Hand the pair's four auxiliaries to the four copies a duplication rule just made.  Each copy takes
   the place of one auxiliary -- UNLESS two of them are shorted to EACH OTHER, i.e. their class is
   closed inside the pair; there the two copies must be joined to each other, since wiring one onto a
   port of a node the rule has already killed leaves a live node pointing at a discarded one, which is
   what readback reports as `_` (measured on a nested Y-knot: a DUP's aux2 wired to its partner's aux2,
   and the copy for it landed on the dead node's port).  `t[k]` is what auxiliary k leads to; `cp[k]`
   is the copy that takes it over. */
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
    const int cor_a[2] = {1, 2}, cor_b[2] = {5, 4};
    pair_boundary(n, n1, n2, cor_a, cor_b, 2, 1, NULL);
    retire(n, n1, n2);            /* AFTER the boundary: it reads both nodes' wires */
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
      int m1, m2, d1, d2;
      split2(n, DUP, qa, qa, DUP, qb, &m1, &m2, &d1, &d2);
      const int cp[4] = {d1, d2, m1, m2};
      link_copies(n, n1, n2, t, cp);
      retire(n, n1, n2);
      return 1;
    }
    /* Annihilation is the correspondence {a1~b1, a2~b2} (1~4, 2~5) -- the same rewire, so the four
       branches that used to special-case two fans wired to each other are gone. */
    const int cor_a[2] = {1, 2}, cor_b[2] = {4, 5};
    pair_boundary(n, n1, n2, cor_a, cor_b, 2, 1, NULL);
    retire(n, n1, n2);
    return 1;
  }

  if ((t1 == LAM || t1 == APP) && t2 == DUP) {
    Scope sn = n->scope[n1], sd = n->scope[n2];
    Scope sm = scope_meet(n, sn, sd);        /* the level the two histories share */
    Port t[4] = { WIRE(n, ((Port){n1, 1})), WIRE(n, ((Port){n1, 2})),
                  WIRE(n, ((Port){n2, 1})), WIRE(n, ((Port){n2, 2})) };
    int m1, m2, d1, d2;
    split2(n, t1, scope_app(n, sm, 1), scope_app(n, sm, 2), DUP, sd, &m1, &m2, &d1, &d2);
    const int cp[4] = {d1, d2, m1, m2};
    link_copies(n, n1, n2, t, cp);
    retire(n, n1, n2);
    return 1;
  }
  return 0; /* era or stuck gauge pair: dropped, as in the reference */
}

/* Reclaim every node not reachable from ROOT.  The `.line` container stores ALL nodes and an actual
   evaluation leaves far more dead intermediates than live ones: without this the baked artifact came
   out ~2x LARGER than the un-evaluated one (474 KB vs 224 KB) despite being a value. */
/* Reclaim every node not reachable from an OBSERVABLE root, WITHOUT MOVING ANYTHING.

   Reachability starts from ALL the anchors, not from ROOT alone: under needed order the result is
   often nowhere near node 0 (readback registers the port it is forcing as a demand root, and a wave's
   queued pairs are live work whether anything demands them yet).  A ROOT-only trace calls the running
   computation garbage -- measured on test/sudoku.lin: 3 of 14426 live nodes are reachable from ROOT
   alone -- and that was one of the compacting version's two defects.  The other was that it MOVED:
   renumbering silently invalidates every node index something outside the reducer holds (the printer's
   memo arrays are keyed by node; readback and net_force hold ports across calls), and 16 of the 52
   suites then came back with the right lines and the wrong values.  So the unreachable nodes go on a
   free list and are reused by net_alloc: every index stays valid, which keeps an external handle (a
   memo key, a port held by readback, a driver's reference) safe to keep.

   WHY THIS IS SOUND FOR A NON-MOVING COLLECTOR, and was NOT for a moving one.  Wires are the only
   pointers and the mark follows them out of every reachable node, so an unreachable node is pointed
   at by NOTHING reachable: freeing it cannot leave a live node pointing into free space.  A stale
   one-sided wire (a "dangle") is harmless here -- it just makes its target reachable and unfreeable,
   the conservative direction -- where compaction rewrote those wires to NONE, destroying what they
   expressed.  SAFEPOINT: reclaiming only when reduce_depth == 1 and nothing is pinned keeps "no
   external handle is held" true by construction (see net_reduce_body for both measurements). */
void net_gc(Net *n) {
  if (n->nn <= 1) return;
  unsigned char *reach = calloc((size_t)n->nn + 1, 1);
  int *q = malloc(((size_t)n->nn + 1) * sizeof(int));
  int qh = 0, qt = 0;
  #define SEED(v) do { int _v = (v); if (_v >= 0 && _v < n->nn && !n->dead[_v] && !reach[_v]) { reach[_v] = 1; q[qt++] = _v; } } while (0)
  SEED(0);
  for (int i = 0; i < n->nroot; i++) SEED(n->root[i].node);
  for (int i = 0; i + 1 < n->atop; i += 2) { SEED(n->act[i].node); SEED(n->act[i + 1].node); }
  #undef SEED
  while (qh < qt) { int u = q[qh++];
    for (int p = 0; p < 3; p++) { Port w = n->wire[u * 3 + p];
      if (w.node >= 0 && w.node < n->nn && !n->dead[w.node] && !reach[w.node]) { reach[w.node] = 1; q[qt++] = w.node; } } }
  /* Anchors whose node the reduction consumed name nothing now; drop them rather than keep a
     reference to a slot that is about to be reusable. */
  int w = 0;
  for (int i = 0; i < n->nroot; i++)
    if (!n->dead[n->root[i].node]) n->root[w++] = n->root[i];
  n->nroot = w;
  w = 0;
  for (int i = 0; i + 1 < n->atop; i += 2)
    if (!n->dead[n->act[i].node] && !n->dead[n->act[i + 1].node]) {
      n->act[w++] = n->act[i]; n->act[w++] = n->act[i + 1];
    }
  n->atop = w;
  long freed = 0;
  for (int v = 1; v < n->nn; v++) {
    if (n->dead[v] || reach[v]) continue;
    n->dead[v] = 1;
    n->tag[v] = ERA;
    for (int p = 0; p < 3; p++) n->wire[v * 3 + p] = NONE;
    n->wire[v * 3] = (Port){n->free_head, 0};      /* the free list threads through port 0 */
    n->free_head = v;
    freed++;
  }
  n->nfree += (int)freed;
  free(reach); free(q);
}

typedef struct { Port p1, p2; } Pair;
/* Driver registration; the table is declared near the top of this file. */
void lin_driver_add(LinDriver *d) {
  if (!d || ndrv >= 16) return;
  if (d->magic != LIN_DRIVER_MAGIC || d->abi != LIN_DRIVER_ABI) {
    fprintf(stderr, "driver '%s': rejected (bad ABI magic 0x%x/abi %u, core wants %u)\n",
            d->name ? d->name : "?", d->magic, d->abi, LIN_DRIVER_ABI);
    return;
  }
  /* A plugin reads the Net it is handed directly, so it must have been built against this exact
     layout.  Rebuild the plugins (`make plugins`) after touching Net. */
  if (d->net_size != (uint32_t)sizeof(Net)) {
    fprintf(stderr, "driver '%s': rejected (built against a %u-byte Net, this core has %u) -- "
                    "rebuild the plugin\n", d->name ? d->name : "?", d->net_size, (unsigned)sizeof(Net));
    return;
  }
  /* What the plugin was built with, and what it cannot do without.  A `wants` bit the core does
     not know is refused: running a plugin without the capability it asked for is exactly the
     silent-misbehaviour class this check exists to prevent. */
  uint64_t unknown = d->wants & ~(uint64_t)LIN_WANT_ALL;
  if (unknown) {
    fprintf(stderr, "driver '%s': rejected (requires capability 0x%llx, this core has 0x%x) -- "
                    "rebuild the plugin or the core\n", d->name ? d->name : "?",
            (unsigned long long)unknown, (unsigned)LIN_WANT_ALL);
    return;
  }
  if ((d->wants & LIN_WANT_STATE) && (!DRV_HAS(d, state_new) || !d->state_new)) goto missing;
  if ((d->wants & LIN_WANT_RECYCLE) && (!DRV_HAS(d, node_recycled) || !d->node_recycled)) goto missing;
  if ((d->wants & LIN_WANT_CARRY) && (!DRV_HAS(d, carry_save) || !d->carry_save)) goto missing;
  if ((d->wants & LIN_WANT_AOT) && (!DRV_HAS(d, aot) || !d->aot)) goto missing;
  if ((d->wants & LIN_WANT_VALUES) && (!DRV_HAS(d, val_box) || !d->val_box ||
                                       !DRV_HAS(d, val_unbox) || !d->val_unbox)) goto missing;
  if ((d->wants & LIN_WANT_READBACK) && (!DRV_HAS(d, read_value) || !d->read_value ||
                                         !DRV_HAS(d, print) || !d->print ||
                                         !DRV_HAS(d, run_io) || !d->run_io)) goto missing;
  /* A driver keeps one slot for the whole process (its state may already exist in live nets). */
  {
    int slot = -1;
    for (int i = 0; i < LIN_DRV_SLOTS; i++) if (dslot[i] == d) { slot = i; break; }
    if (slot < 0) for (int i = 0; i < LIN_DRV_SLOTS; i++) if (!dslot[i]) { slot = i; break; }
    if (slot < 0) {
      fprintf(stderr, "driver '%s': rejected (no free state slot; LIN_DRV_SLOTS is %d)\n",
              d->name ? d->name : "?", LIN_DRV_SLOTS);
      return;
    }
    d->slot = slot; dslot[slot] = d;
    if (DRV_HAS(d, node_recycled) && d->node_recycled) any_recycle = 1;
    if (DRV_HAS(d, state_new) && d->state_new) any_state = 1;
  }
  /* already dispatching: registration is idempotent, because a plugin's constructor registers it
     when the .so is dlopen'd and `(set_driver "<its own name>")` would add it again -- leaving the
     same reducer to claim every wave twice. */
  for (int i = 0; i < ndrv; i++) if (drv[i] == d) return;
  int i = ndrv;
  while (i > 0 && drv[i-1]->priority > d->priority) { drv[i] = drv[i-1]; i--; }
  drv[i] = d; ndrv++;
  return;
missing:
  fprintf(stderr, "driver '%s': rejected (wants 0x%llx but does not implement it: size %u)\n",
          d->name ? d->name : "?", (unsigned long long)d->wants, d->size);
}
/* `(set_driver ...)`/`driver_clear` selects a *strategy*; pre-emptors are a reduction pre-pass that
   composes with whichever strategy is chosen, so clearing must not silently disable native folding.
   Compacting in place keeps the priority order intact.  Idempotent, because a plugin's constructor
   registers its driver when the .so is dlopen'd and `(set_driver "<its own name>")` would add it
   again, leaving the same reducer to claim every wave twice. */
void lin_driver_clear(void) {
  int w = 0;
  for (int i = 0; i < ndrv; i++)
    if (drv[i]->caps & (LIN_CAP_PREEMPT | LIN_CAP_PROVIDER)) drv[w++] = drv[i];
  ndrv = w;
}
static inline int demanded(const Net *n, Port p);
static inline int redex_live(Net *n, Port p1, Port p2);

/* ---- the claim protocol: a lease on STRUCTURE ------------------------------------------
   A claim is redexes plus the region's EXITS.  Validation is the whole of the core's part and it
   never interprets what a driver matched -- tags, ports and wiring only.  The safety rule is the
   exit rule: a redex is two mutually wired PRINCIPAL ports, so an auxiliary-only boundary cannot
   be crossed by one, and that is what makes a region safe to rewrite in isolation. */
static int claim_in_set(const LinClaim *c, int v) {
  for (int i = 0; i < c->nnodes; i++) if (c->nodes[i] == v) return 1;
  return 0;
}
static int claim_is_exit(const LinClaim *c, int node, int port) {
  for (int i = 0; i < c->nexits; i++)
    if (c->exits[i].node == node && c->exits[i].port == (unsigned)port) return 1;
  return 0;
}
/* Both ends of a redex inside the region: what exclusivity is decided on. */
static int claim_covers(const LinClaim *c, Port a, Port b) {
  return c->nnodes > 0 && claim_in_set(c, a.node) && claim_in_set(c, b.node);
}

int lin_claim_check(Net *n, LinClaim *c, char *why, int whysz) {
  c->nnodes = 0;
  if (c->npairs <= 0 || c->npairs > LIN_MAX_CLAIM_PAIRS || c->nexits > LIN_MAX_CLAIM_EXITS) {
    snprintf(why, (size_t)whysz, "claim shape out of range (%d pairs, %d exits)", c->npairs, c->nexits);
    return 0;
  }
  for (int i = 0; i < c->npairs; i++) {
    Port a = c->pairs[2 * i], b = c->pairs[2 * i + 1];
    if (!redex_live(n, a, b)) { snprintf(why, (size_t)whysz, "claimed pair %d is not a live redex", i); return 0; }
  }
  /* An exit at an auxiliary port cannot be crossed by a redex (which needs two principals). */
  if (c->flags & LIN_CLAIM_REGION)
    for (int i = 0; i < c->nexits; i++) {
      Port e = c->exits[i];
      if (e.port == 0) { snprintf(why, (size_t)whysz, "exit %d is at a principal port", i); return 0; }
      if (!NAT_IN(n, e.node) || n->dead[e.node]) { snprintf(why, (size_t)whysz, "exit %d is not live", i); return 0; }
    }
  /* Without LIN_CLAIM_REGION the claim is just its pairs -- a driver that has not enumerated its
     exits has not defined a region.  With it, the region is the closure stopping at the exits, and
     the exits must be exactly its frontier: what the driver owns is a walk, not a promise. */
  if (!(c->flags & LIN_CLAIM_REGION)) {
    if (c->nexits) { snprintf(why, (size_t)whysz, "exits declared without LIN_CLAIM_REGION"); return 0; }
    for (int i = 0; i < c->npairs; i++)
      for (int k = 0; k < 2; k++) {
        int v = c->pairs[2 * i + k].node;
        if (claim_in_set(c, v)) continue;
        if (c->nnodes >= LIN_CLAIM_NODES) { snprintf(why, (size_t)whysz, "claim too large"); return 0; }
        c->nodes[c->nnodes++] = v;
      }
    return 1;
  }
  for (int i = 0; i < c->npairs; i++)
    for (int k = 0; k < 2; k++) {
      int v = c->pairs[2 * i + k].node;
      if (claim_in_set(c, v)) continue;
      if (c->nnodes >= LIN_CLAIM_NODES) { snprintf(why, (size_t)whysz, "region exceeds %d nodes", LIN_CLAIM_NODES); return 0; }
      c->nodes[c->nnodes++] = v;
    }
  for (int qi = 0; qi < c->nnodes; qi++) {
    int u = c->nodes[qi];
    for (int p = 0; p < 3; p++) {
      if (claim_is_exit(c, u, p)) continue;
      Port w = WIRE(n, ((Port){u, p}));
      if (!NAT_IN(n, w.node) || n->dead[w.node]) continue;
      if (claim_in_set(c, w.node)) continue;
      if (c->nnodes >= LIN_CLAIM_NODES) { snprintf(why, (size_t)whysz, "region exceeds %d nodes", LIN_CLAIM_NODES); return 0; }
      c->nodes[c->nnodes++] = w.node;
    }
  }
  for (int i = 0; i < c->nexits; i++) {
    Port e = c->exits[i];
    if (!claim_in_set(c, e.node)) { snprintf(why, (size_t)whysz, "exit %d is outside the region", i); return 0; }
    Port w = WIRE(n, e);
    if (NAT_IN(n, w.node) && !n->dead[w.node] && claim_in_set(c, w.node)) {
      snprintf(why, (size_t)whysz, "exit %d is internal: it does not leave the region", i);
      return 0;
    }
  }
  return 1;
}

int lin_demanded(const Net *n, Port p) { return demanded((Net *)n, p); }

/* Lazy: a driver may be registered after the net exists (the prelude loads plugins). */
void *lin_driver_state(Net *n, LinDriver *d) {
  if (!n || !d || d->slot < 0 || d->slot >= LIN_DRV_SLOTS) return NULL;
  if (!n->drv[d->slot] && DRV_HAS(d, state_new) && d->state_new) {
    n->drv[d->slot] = d->state_new(n);
  }
  return n->drv[d->slot];
}

/* The core knows the DOMAIN (the registry declares its carriers, since a box is net structure) and
   nothing else: not the encoding, not the table, not the arithmetic. */
static LinDriver *domain_provider(int domain) {
  if (domain < 0 || domain >= 64) return NULL;
  for (int i = 0; i < ndrv; i++) {
    LinDriver *d = drv[i];
    if (!DRV_HAS(d, val_box) || !d->val_box) continue;
    if ((d->domains >> domain) & 1u) return d;
  }
  return NULL;
}

Port net_box_value(Net *n, int domain, const Val *v) {
  LinDriver *d = domain_provider(domain);
  if (!d) return NONE;
  return d->val_box(n, lin_driver_state(n, d), v);
}

int net_unbox_value(Net *n, int domain, Port p, Val *v) {
  LinDriver *d = domain_provider(domain);
  if (!d) return 0;
  return d->val_unbox(n, lin_driver_state(n, d), p, v);
}

/* ---- artifact sections: one opaque blob per driver, tagged with its NAME.  Nothing here knows
   what a blob means, and a section whose driver is absent is loaded on demand: an artifact is
   self-describing, which is what let the float table leave the core safely. */
static LinDriver *driver_by_name(const char *name) {
  for (int i = 0; i < LIN_DRV_SLOTS; i++)
    if (dslot[i] && dslot[i]->name && !strcmp(dslot[i]->name, name)) return dslot[i];
  return NULL;
}

/* Is this driver's PRESENCE part of what the net means?  A net is compiled and reduced under a set of
   drivers, and one that supplies SEMANTICS -- a fold pre-emptor that gives an `_op`/`_ffi` closure its
   value, the scalar table behind it, a value domain's storage -- is not an accelerator the artifact
   can do without: with it gone the same net is a different program.  Measured: `test/runtime_ffi.lin`
   (whose runtime `getenv` makes the build ship it UNREDUCED) never folded its `(add <closure> 1)` in
   the artifact while the interpreter answered 7, because `arith` has no state, so no section named it
   and the artifact ran with no fold pre-emptor.  These are the caps `lin_driver_clear` refuses to
   drop, plus the scalar-table providers; a PURE STRATEGY (FIXED/COMMUTE only, e.g. gpu) is NOT
   carried, because a container runs prelude-free and naming one would bake the host's choice in. */
static int carries_presence(const LinDriver *d) {
  return (d->caps & (LIN_CAP_PREEMPT | LIN_CAP_PROVIDER | LIN_CAP_NATIVE_NUM)) != 0;
}

void lin_driver_carry_write(Net *n, FILE *f) {
  struct { LinDriver *d; void *blob; size_t len; } sec[LIN_DRV_SLOTS];
  uint32_t count = 0;
  for (int i = 0; i < LIN_DRV_SLOTS; i++) {
    LinDriver *d = dslot[i];
    if (!d) continue;
    /* Storage may be process-wide rather than per net (the float table must be), so a section
       depends on the driver having something to carry, not on this net having state.  Its NAME is
       written either way: a section is the driver's PRESENCE as much as its payload, and the reader
       needs nothing more than the name to dlopen whoever supplied it (net_load_line). */
    void *blob = NULL; size_t len = 0;
    int state = DRV_HAS(d, carry_save) && d->carry_save;
    if (state && !d->carry_save(n, n->drv[i], &blob, &len)) { state = 0; blob = NULL; len = 0; }
    if (!state && !carries_presence(d)) continue;   /* a pure strategy with nothing to carry: not ours */
    sec[count].d = d; sec[count].blob = blob; sec[count].len = len;
    count++;
  }
  fwrite(&count, sizeof count, 1, f);
  for (uint32_t k = 0; k < count; k++) {
    size_t nlen = strlen(sec[k].d->name);
    if (nlen >= NAME) nlen = NAME - 1;            /* the writer guarantees what the reader assumes */
    uint8_t nl = (uint8_t)nlen;
    uint32_t l32 = (uint32_t)sec[k].len;
    fwrite(&nl, 1, 1, f);
    fwrite(sec[k].d->name, 1, nl, f);
    fwrite(&l32, sizeof l32, 1, f);
    if (l32) fwrite(sec[k].blob, 1, l32, f);
    free(sec[k].blob);
  }
}

void lin_driver_carry_read(Net *n, FILE *f, uint32_t count) {
  for (uint32_t k = 0; k < count; k++) {
    uint8_t nl = 0;
    char name[NAME] = {0};
    uint32_t l32 = 0;
    if (fread(&nl, 1, 1, f) != 1) return;   /* a section name is shorter than NAME by construction */
    if (fread(name, 1, nl, f) != nl) return;
    name[nl] = 0;
    if (fread(&l32, sizeof l32, 1, f) != 1) return;
    char *blob = malloc(l32 ? l32 : 1);
    if (!blob || (l32 && fread(blob, 1, l32, f) != (size_t)l32)) { free(blob); return; }
    LinDriver *d = driver_by_name(name);
    if (!d) { lin_driver_load(name); d = driver_by_name(name); }   /* the section names its author */
    if (d && DRV_HAS(d, carry_load) && d->carry_load)
      d->carry_load(n, lin_driver_state(n, d), blob, l32);
    free(blob);   /* an unknown section is skipped: an artifact from a newer build still runs */
  }
}

/* A v4 artifact carried the float table inline, before sections existed.  The core knows only that
   v4 meant the DT_FLOAT domain; whoever provides it decides the layout. */
int lin_driver_carry_legacy(Net *n, int domain, const void *blob, size_t len) {
  LinDriver *d = domain_provider(domain);
  if (!d || !DRV_HAS(d, carry_load) || !d->carry_load) return 0;
  return d->carry_load(n, lin_driver_state(n, d), blob, len);
}

/* the active *strategy* (never a pre-emptor or a provider), so `(get_driver)` still reports cpu/simd/gpu */
LinDriver *lin_get_driver(void) {
  for (int i = ndrv - 1; i >= 0; i--)
    if (!(drv[i]->caps & (LIN_CAP_PREEMPT | LIN_CAP_PROVIDER))) return drv[i];
  return NULL;
}

/* Does `d` provide `want`?  Answered from the HOOK the want names -- never from the driver's name --
   which is what keeps a capability replaceable: any driver that implements it is a candidate. */
static int provides(const LinDriver *d, uint64_t want) {
  switch (want) {
  case LIN_WANT_STATE:    return DRV_HAS(d, state_new) && d->state_new;
  case LIN_WANT_RECYCLE:  return DRV_HAS(d, node_recycled) && d->node_recycled;
  case LIN_WANT_CARRY:    return DRV_HAS(d, carry_save) && d->carry_save;
  case LIN_WANT_VALUES:   return DRV_HAS(d, val_box) && d->val_box;
  case LIN_WANT_MATCH:    return DRV_HAS(d, match) && d->match;
  case LIN_WANT_HELD:     return DRV_HAS(d, revalidate) && d->revalidate;
  case LIN_WANT_READBACK: return DRV_HAS(d, print) && d->print && DRV_HAS(d, run_io) && d->run_io;
  default: return 0;
  }
}

LinDriver *lin_driver_wanting(uint64_t want) {
  for (int i = 0; i < ndrv; i++) if (provides(drv[i], want)) return drv[i];
  return NULL;
}

/* The AOT pass point.  The core OFFERS and the driver OWNS: `drv[]` is in priority order, so the
   passes run in it and each sees what the ones before it wrote -- the arbitration the runtime uses.
   LIN_NO_PASS skips every pass, which is what makes each optional: a skipped pass leaves a VALID net,
   and the interpreter path never runs one at all. */
int lin_driver_aot(Net *n, const Term *t, const Scheme *sch) {
  if (!n || !t || getenv("LIN_NO_PASS")) return 0;
  int ran = 0;
  for (int i = 0; i < ndrv; i++)
    if (DRV_HAS(drv[i], aot) && drv[i]->aot && (drv[i]->wants & LIN_WANT_AOT)) {
      drv[i]->aot(n, lin_driver_state(n, drv[i]), t, sch, lin_node_of, NULL); ran++;
    }
  return ran;
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

   No rule of the calculus changes: the filter only decides WHICH active pairs are in a wave, and a
   pair off the demand path stays queued in `act` for a later wave -- which is what makes a cycle (a
   Y-knot) reduce when the recursive call is demanded instead of unrolling for ever. */
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
  /* Only ever TRUNCATE.  A reduction here can reclaim, which rewrites the root array and can drop
     the root this call added; restoring the old COUNT would then claim entries that no longer name
     anything, and the next demand walk would seed itself from stale indices. */
  if (n->nroot > save) n->nroot = save;
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

static long net_reduce_body(Net *n, long limit);

/* Only the OUTERMOST call may reclaim or publish: a nested call is entered from a driver's reducer
   or from net_force, and readback holds ports of its own while net_force runs. */

long net_reduce(Net *n, long limit) {
  if (reduce_depth) nested_reduce = 1;
  reduce_depth++;
  long done = net_reduce_body(n, limit);
  reduce_depth--;
  return done;
}

static long net_reduce_body(Net *n, long limit) {
  /* Each wave re-marks demand and fires only the active pairs the demand walk reached; a pair off
     that path is pushed back, so it is still there when something needs it.  A wave in which nothing
     on the demand path could fire means the observed ports are already in WHNF: stop, rather than
     spin on the queued pairs. */
  Port *curr = NULL; int curr_cap = 0;
  Port *base_rx = NULL; int base_cap = 0;
    /* When reclamation runs: live nodes above this, and no reusable slot left.  1M by default, so the
     suite never reaches it -- hence LIN_GC, which forces the collector on.  (It was dormant at 1M
     while the COLLECTOR was wrong: a ROOT-only root set and a renumbering pass, both now replaced.)
     KNOWN UNSOUND BELOW THE DEFAULT, for two INDEPENDENT reasons, measured by switching parts of the
     block off (whole block skipped: 52/52 output suites; fully on: 33/52; renumbering skipped and
     only the reachability taken: 49/52):
       1. IT MOVES: renumbering invalidates every index something outside the reducer holds, and 16 of
          the 52 suites come back with the right lines and the wrong values (see net_gc above).
       2. IT IS STILL INCOMPLETE.  With the move skipped, modules.lin, numbers.lin and vector.lin still
          truncate (21/31, 37/56, 19/21): some anchor is not in the seed set, so live work is called
          garbage and the run stops early.
     The conclusion is not "tune the threshold" but "reclaim WITHOUT moving" -- a free list, so every
     index stays valid -- and then close the anchor gap: fixing (1) is what makes (2) findable, since
     with stable indices a wrongly reclaimed node is a missing value, not silent corruption. */
  long gcmark = getenv("LIN_GC") ? atol(getenv("LIN_GC")) : (1L << 20);
  Port *slices[16] = {0}; int scaps[16] = {0}, scnts[16] = {0};
  /* per-wave claim scratch: candidates offered, per-pair ownership, claims (one per driver) */
  Port *cand = NULL; int cand_cap = 0, cand_cnt = 0;
  int *owned = NULL; int own_cap = 0;
  LinClaim *claimed = calloc(ndrv ? (size_t)ndrv : 1, sizeof(LinClaim));
  unsigned char have[16] = {0};
  while (n->steps < limit) {
    int changed = 0;
    while (n->atop > 0 && n->steps < limit) {
      int before = changed;
      if (reduce_depth == 1) nested_reduce = 0;
      int cnt = wave_snapshot(n, &curr, &curr_cap);
      if (cnt <= 0) break;
      net_mark_demand(n);
      int np = cnt / 2, base_cnt = 0;

      if (np > own_cap) { own_cap = np * 2 + 64; owned = realloc(owned, (size_t)own_cap * sizeof(int)); }
      for (int i = 0; i < np; i++) owned[i] = -1;
      char why[160];

      /* Held claims first: structure reserved across waves is re-validated and re-reserved before
         anything is offered to anyone, or holding it would mean nothing. */
      for (int h = 0; h < n->nheld; ) {
        LinDriver *d = n->held_drv[h];
        LinClaim *hc = &n->held[h];
        void *st = d->slot >= 0 && d->slot < LIN_DRV_SLOTS ? n->drv[d->slot] : NULL;
        if (DRV_HAS(d, revalidate) && d->revalidate && !d->revalidate(n, st, hc)) hc->npairs = -1;
        if (hc->npairs < 0 || !lin_claim_check(n, hc, why, sizeof why)) {
          if (DRV_HAS(d, release_claim) && d->release_claim) d->release_claim(n, st, hc);
          n->held[h] = n->held[--n->nheld];
          n->held_drv[h] = n->held_drv[n->nheld];
          continue;
        }
        /* Reserve every redex inside, and KEEP it queued: reserving is not consuming, and a held
           pair dropped from the wave would be lost work rather than deferred work.  `act` gets the
           claim again every wave until `revalidate` says the driver is done. */
        for (int i = 0; i < np; i++)
          if (owned[i] < 0 && claim_covers(hc, curr[2 * i], curr[2 * i + 1])) {
            owned[i] = 0;
            act_push(n, curr[2 * i], curr[2 * i + 1]);
          }
        for (int di = 0; di < ndrv; di++)
          if (drv[di] == d && di < 16) { claimed[di] = *hc; have[di] = 1; }
        h++;
      }

      /* Undemanded work stays queued (firing it unrolls a Y-knot); the rest is what drivers see. */
      cand_cnt = 0;
      for (int i = 0; i < np; i++) {
        Port p1 = curr[i * 2], p2 = curr[i * 2 + 1];
        if (!demanded(n, p1) || !demanded(n, p2)) { if (redex_live(n, p1, p2)) act_push(n, p1, p2); continue; }
        if (owned[i] >= 0) continue;
        if (cand_cnt + 2 > cand_cap) { cand_cap = cand_cap ? cand_cap * 2 : 256; cand = realloc(cand, (size_t)cand_cap * sizeof(Port)); }
        cand[cand_cnt++] = p1; cand[cand_cnt++] = p2;
      }

      /* ONE CALL PER DRIVER, before any slice exists -- which is what lets a claim be exact: a matcher
         may inspect and force what it must read, where a per-pair predicate could not (the snapshot
         and every slice are built from the net it would be mutating).  It also keeps dispatch from
         growing with the number of drivers.
         What a driver gets is the wave's redexes; what it OWNS is the region it proposes itself (the
         pairs plus the exits it declares), which the core then validates. */
      int steps_before = n->steps;
      for (int di = 0; di < ndrv; di++) {
        LinDriver *d = drv[di];
        if (!DRV_HAS(d, match) || !d->match) continue;
        LinClaim c;
        memset(&c, 0, sizeof c);
        LinView view;
        view.pairs = cand;
        view.npairs = cand_cnt / 2;      /* pairs, not ports: `pairs` holds 2*npairs ports */
        if (!d->match(n, n->drv[d->slot], &view, &c)) continue;
        if (!lin_claim_check(n, &c, why, sizeof why)) {
          static int warned;
          if (!warned) { warned = 1; fprintf(stderr, "driver '%s': claim refused (%s)\n", d->name ? d->name : "?", why); }
          continue;
        }
        int clash = 0;
        for (int i = 0; i < np && !clash; i++)
          if (owned[i] >= 0 && claim_covers(&c, curr[2 * i], curr[2 * i + 1])) clash = 1;
        if (clash) continue;                      /* a higher-priority driver owns it: try next wave */
        if ((c.flags & LIN_CLAIM_HELD) && n->nheld < 4) {
          n->held[n->nheld] = c;
          n->held_drv[n->nheld] = d;
          n->nheld++;
        }
        /* Reserve every redex INSIDE, not just the listed ones: the region was certified closed, so
           it is the driver's -- exclusion as an invariant, not an ordering accident. */
        for (int i = 0; i < np; i++)
          if (owned[i] < 0 && claim_covers(&c, curr[2 * i], curr[2 * i + 1])) owned[i] = di + 1;
        claimed[di] = c;
        have[di] = 1;
      }
      changed += (int)(n->steps - steps_before);   /* a match that forced made real progress */

      /* Legacy drivers (a pure per-pair predicate) are consulted over what is left. */
      for (int i = 0; i < np; i++) {
        if (owned[i] >= 0) continue;
        Port p1 = curr[i * 2], p2 = curr[i * 2 + 1];
        if (!demanded(n, p1) || !demanded(n, p2)) continue;
        int assigned = 0;
        for (int di = 0; di < ndrv && !assigned; di++) {
          LinDriver *d = drv[di];
          if (have[di] || !DRV_HAS(d, claim) || !d->claim || !d->claim(n, p1, p2)) continue;
          if (scnts[di] + 2 > scaps[di]) { scaps[di] = scaps[di] ? scaps[di]*2 : 256; slices[di] = realloc(slices[di], (size_t)scaps[di]*sizeof(Port)); }
          slices[di][scnts[di]++] = p1; slices[di][scnts[di]++] = p2;
          assigned = 1;
        }
        if (!assigned) {
          if (base_cnt + 2 > base_cap) { base_cap = base_cap ? base_cap*2 : 256; base_rx = realloc(base_rx, (size_t)base_cap*sizeof(Port)); }
          base_rx[base_cnt++] = p1; base_rx[base_cnt++] = p2;
        }
      }

      /* a claim owns a region, so it acts; a legacy driver consumes its slice; base gets the rest */
      for (int di = 0; di < ndrv; di++) {
        LinDriver *d = drv[di];
        if (have[di]) {
          have[di] = 0;
          if (DRV_HAS(d, act) && d->act) changed += d->act(n, n->drv[d->slot], &claimed[di]);
          claimed[di].npairs = 0;
        }
        if (scnts[di]) d->reduce(n, slices[di], scnts[di]/2, limit, &changed);
      }
      /* base engine handles the unclaimed remainder */
      if (base_cnt) lin_reduce_wave_parallel(n, base_rx, base_cnt, &changed);
      /* The snapshot and slices are consumed; their slots become reusable only now -- and only if no
         driver nested back into the reducer, which would have handed them out underneath this wave. */
      if (!nested_reduce) net_flush_free(n);
      if (changed == before) break;
    }
    /* Reclaim only at a safepoint (the outermost reduce), and only when there is something to gain:
       out of reusable slots, with the net above the threshold.  `nn - nfree` is the live node count,
       so the hysteresis tracks what is actually in use rather than what has been allocated. */
    if (reduce_depth == 1 && n->pins == 0 && n->free_head < 0 && (long)(n->nn - n->nfree) > gcmark) {
      net_gc(n);
      gcmark = (long)(n->nn - n->nfree) * 2 + 64;
      /* No resume-seed.  One used to rebuild the active list from every principal pair, which was
         the only way back after compaction had renumbered the net and silently orphaned `act`.
         Remapping the anchors made it unnecessary -- and it was actively wrong under needed order:
         it re-enqueued the pairs the demand filter had deliberately set aside, so a later force
         re-reduced undemanded thunks and a Y-knot unrolled for ever (measured: test/map.lin hangs
         at its third expression).  A freshly LOADED net still seeds explicitly, in net_load_line. */
    }
    if (changed == 0) break;
  }
  net_flush_free(n);
  free(curr); free(base_rx);
  for (int di = 0; di < ndrv; di++) free(slices[di]);
  return n->steps;
}

Net *net_copy(const Net *n) {
  Net *c = malloc(sizeof(Net)); *c = *n;
  c->tag = malloc(c->cap); memcpy(c->tag, n->tag, c->cap);
  c->wire = malloc(c->cap * 3 * sizeof(Port)); memcpy(c->wire, n->wire, c->cap * 3 * sizeof(Port));
  c->scope = malloc(c->cap * sizeof(Scope)); memcpy(c->scope, n->scope, c->cap * sizeof(Scope));
  c->dead = malloc(c->cap); memcpy(c->dead, n->dead, c->cap);
  c->dem = calloc(c->cap, sizeof(unsigned int)); c->dem_stamp = 0;
  c->vport = calloc(c->cap, 1);
  c->nlv = 0; c->lvcap = 0; c->lv_hcap = 0; c->lv_hash = NULL;
  c->lv_parent = NULL; c->lv_depth = NULL; c->lv_bit = NULL;
  net_level_set(c, n->nlv, n->lv_parent + 1, n->lv_bit + 1);   /* rebuild the trie: parents precede children, ids reload directly */
  c->act = NULL; c->actcap = c->atop = 0; c->steps = 0;
  c->root = NULL; c->nroot = 0; c->rootcap = 0; c->free_head = -1; c->nfree = 0; c->pend_head = -1; c->pins = 0;
  /* The copy starts with its own state: a table keyed by node index belongs to the net it came
     from.  A driver that cannot copy starts empty, which is safe because state is always a
     derivation of the net and never the authority. */
  memset(c->drv, 0, sizeof c->drv);
  c->nheld = 0;                       /* a held claim is a lease on ONE net's structure */
  if (any_state)
    for (int i = 0; i < LIN_DRV_SLOTS; i++) {
      LinDriver *d = dslot[i];
      if (!d || !n->drv[i]) continue;
      void *st = lin_driver_state(c, d);
      if (st && DRV_HAS(d, state_copy) && d->state_copy) d->state_copy((Net *)n, n->drv[i], c, st);
    }
  return c;
}
