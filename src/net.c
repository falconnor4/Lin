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
   A level is a position in the term: the sequence of branches taken from the root.  Interning
   that sequence as a trie node makes four operations cheap and exact:
     equality   -> the same id
     meet       -> the lowest common ancestor (LCA)
     nesting    -> walk up from the deeper level
     extension  -> intern (parent, branch)
   and it makes representation free: one int per node, one edge per distinct path, whether the
   path is 3 steps or 300.  The bit-word/heap-table union this replaces spilled long gauges to a
   side table -- 444,380 entries, 97% of a built artifact, for one test program. */
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
  for (int l = 1; l < n->nlv; l++) {
    unsigned h = ((unsigned)n->lv_parent[l] * 2654435761u + (unsigned)n->lv_bit[l]) & (unsigned)(cap - 1);
    while (n->lv_hash[h]) h = (h + 1) & (unsigned)(cap - 1);
    n->lv_hash[h] = l;
  }
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
#define MAX_SCOPE_STEPS (1 << 16)

Scope scope_meet(Net *n, Scope a, Scope b) {
  int guard = n->nlv + 2;
  while (lv_depth(n, a) > lv_depth(n, b)) { a = (Scope)lv_up(n, a); if (--guard < 0) goto bad; }
  while (lv_depth(n, b) > lv_depth(n, a)) { b = (Scope)lv_up(n, b); if (--guard < 0) goto bad; }
  while (a != b) { a = (Scope)lv_up(n, a); b = (Scope)lv_up(n, b); if (--guard < 0) goto bad; }
  return a;
bad:
  return 0;
}

int scope_within(Net *n, Scope a, Scope b) {
  if (!a || a == b) return 0;
  int d = lv_depth(n, b) - lv_depth(n, a);
  if (d <= 0) return 0;
  int x = (int)b;
  while (d-- > 0) x = lv_up(n, x);
  return (Scope)x == a;
}

int scope_eq(Net *n, Scope a, Scope b) { (void)n; return a == b; }

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

/* the container hands the trie back in id order (parents precede children) */
void net_level_set(Net *n, int nlv, const int *parent, const unsigned char *bit) {
  if (nlv <= 0) return;
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
  n->nn = 0; n->steps = 0; n->driver_pending = 0;
  net_alloc(n, ROOT, scope_nil(), "");
}

void net_free(Net *n) {
  free(n->tag); free(n->wire); free(n->scope); free(n->act); free(n->dead);
  free(n->lv_parent); free(n->lv_depth); free(n->lv_bit); free(n->lv_hash);
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

/* four rules of the scope-gauge calculus (wave-opt-reduction main.hs); ERA is inert (era pairs dropped) */
static int lin_trace = -1; /* cached LIN_TRACE */

/* Driver pipeline: sorted by priority (ascending); core waves fan out to each in priority order, each *claiming*
   the redexes it handles, so drivers compose.  Declared up here because β consults it (lin_argfold). */
static LinDriver *drv[16]; static int ndrv;

/* Ask each driver, in priority order, to pre-empt a sub-term β is about to substitute.  A saturated closure in an
   *argument* position is never a principal×principal redex, so a driver can only reach it through this hook.  The
   first driver that materialises `arg` at `target` wins; otherwise β substitutes the term unchanged and the
   pure-Lin fallback body computes it (slower, but exactly). */
static int lin_argfold(Net *n, Port arg, Port target) {
  for (int di = 0; di < ndrv; di++)
    if (drv[di]->arg_fold && drv[di]->arg_fold(n, arg, target)) return 1;
  return 0;
}

int net_interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (lin_trace < 0) lin_trace = getenv("LIN_TRACE") != NULL;
  if (lin_trace)
    fprintf(stderr, "step %ld: %d.%d x %d.%d\n", n->steps, t1, n1, t2, n2);

  if (t1 == LAM && t2 == APP) {
    /* β, and nothing else.  Native folding of `_op`/`_ffi` closures, its saturation guard and its deferral
       policy all live in a driver (std/drivers/arith.so, LIN_CAP_PREEMPT): such a closure is claimed as a redex
       *before* it ever reaches here, so this rule sees only closures no driver wanted and β-reduces their
       pure-Lin fallback body.  That keeps the core a complete calculus on its own — a driver can pre-empt a
       redex class, never replace this rule. */
    Port lv = WIRE(n, ((Port){n1, 1})), lb = WIRE(n, ((Port){n1, 2}));
    Port ar = WIRE(n, ((Port){n2, 1})), aa = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1; n->dead[n2] = 1;
    if (lv.node == n1 && lv.port == 2 && lb.node == n1 && lb.port == 1) {
      /* degenerate binder: for `\x.x` the compiler cross-links the binder and body ports, so there is no
         separate substitution to make — connect argument to result.  This is β itself, not fold machinery:
         without it `((\x x) V)` strands V on a dead node and readback yields nothing. */
      if (lin_argfold(n, aa, ar)) return 1;
      net_link(n, aa, ar, 1); return 1;
    }
    /* Two of beta's four wires can be ports of the SAME fan -- the fan sits between the binder
       and the argument, or between the body and the result, and already relates them (its
       auxiliary carries the value to one side, its principal receives it from the other).
       Linking them would wire a fan's principal to its own auxiliary: a pair no rule fires on,
       which leaves a "normal form" whose value cannot be read back (measured on a knot: the
       printer emitted `?` and the answer was lost).  So substitute on the other pair only, and
       when both pairs are the fan's own ports there is nothing left to link. */
    {
      int fan_ba = (lv.node == aa.node && n->tag[lv.node] == DUP);
      int fan_br = (lb.node == ar.node && n->tag[lb.node] == DUP);
      if (fan_ba && fan_br) return 1;
      if (fan_ba) { net_link(n, lb, ar, 1); return 1; }
      if (fan_br) { net_link(n, lv, aa, 1); return 1; }
    }
    /* A driver may pre-empt the argument before it is substituted: a saturated closure passed as data (e.g. the
       `(mul 2 2)` of `succ (mul 2 2)`) would otherwise be β-duplicated without ever being materialised. */
    if (lin_argfold(n, aa, lv)) { net_link(n, lb, ar, 1); return 1; }
    net_link(n, lv, aa, 1); net_link(n, lb, ar, 1);
    return 1;
  }

  if (t1 == DUP && t2 == DUP) {
    if (!scope_eq(n, n->scope[n1], n->scope[n2])) {
      /* Two fans with distinct levels meet, and the case analysis is the duplication
         discipline.  Fans are copied by each other -- delta_a's auxiliaries each get a
         delta_b, delta_b's each get a delta_a, cross-connected, the same shape as the
         gamma x delta rule below -- because the only alternatives are annihilating two
         unrelated fans (wrong value) or stranding the pair (no reduction).

         What differs is the LEVEL the copies carry, and it is what bounds duplication:

         - NESTED levels (one gauge a proper prefix of the other: the two sharing points
           enclose one another) are related, not independent.  The deeper fan's copies take
           the SHALLOWER level, so the inner sharing point is *shared* between the outer
           copies instead of being re-duplicated once per copy.  Without this, a fan that
           meets its own copies around a cycle duplicates the structure it came from forever
           (measured on a knot: 2,000,000+ steps without a normal form against 33,200 steps /
           1,122 nodes with it, and the whole suite stays oracle-green).
         - INCOMPARABLE levels are genuinely independent sharing points, and their copies
           keep their own names so the two points stay distinct. */
      Scope sa = n->scope[n1], sb = n->scope[n2];
      Scope qa = sa, qb = sb;
      if (scope_within(n, sa, sb)) { qa = sa; qb = sa; }        /* a encloses b: share the inner */
      else if (scope_within(n, sb, sa)) { qa = sb; qb = sb; }   /* b encloses a */
      Port a1 = WIRE(n, ((Port){n1, 1})), a2 = WIRE(n, ((Port){n1, 2}));
      Port b1 = WIRE(n, ((Port){n2, 1})), b2 = WIRE(n, ((Port){n2, 2}));
      const char *nm = n->name[n1] ? n->name[n1] : "";
      int m1 = net_alloc(n, DUP, qa, nm).node;
      int m2 = net_alloc(n, DUP, qa, nm).node;
      int d1 = net_alloc(n, DUP, qb, nm).node, d2 = net_alloc(n, DUP, qb, nm).node;
      n->dead[n1] = 1; n->dead[n2] = 1;
      net_link(n, (Port){d1, 1}, (Port){m1, 1}, 0); net_link(n, (Port){d1, 2}, (Port){m2, 1}, 0);
      net_link(n, (Port){d2, 1}, (Port){m1, 2}, 0); net_link(n, (Port){d2, 2}, (Port){m2, 2}, 0);
      net_link(n, (Port){d1, 0}, a1, 1); net_link(n, (Port){d2, 0}, a2, 1);
      net_link(n, (Port){m1, 0}, b1, 1); net_link(n, (Port){m2, 0}, b2, 1);
      return 1;
    }
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
    Scope sm = scope_meet(n, sn, sd);        /* the level the two histories share */
    Port nv = WIRE(n, ((Port){n1, 1})), nb = WIRE(n, ((Port){n1, 2}));
    Port da = WIRE(n, ((Port){n2, 1})), db = WIRE(n, ((Port){n2, 2}));
    const char *nm = n->name[n1] ? n->name[n1] : "";
    int m1 = net_alloc(n, t1, scope_app(n, sm, 1), nm).node;
    int m2 = net_alloc(n, t1, scope_app(n, sm, 2), nm).node;
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

/* Reclaim every node not reachable from ROOT.  The reduce loop calls this
   opportunistically, and the AOT build calls it before serialising: the `.line`
   container stores ALL nodes, and an actual evaluation leaves far more dead
   intermediates behind than live nodes -- without this the baked artifact came out
   ~2x LARGER than the un-evaluated one (474 KB vs 224 KB) despite being a value. */
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
/* `(set_driver ...)`/`driver_clear` selects a *strategy*; pre-emptors are a reduction pre-pass that composes with
   whichever strategy is chosen, so clearing must not silently disable native folding (or, once Move 2/3 land, the
   AOT sharing decisions that ride the same hook).  Compacting in place keeps the priority order intact. */
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
/* A driver reports that it claimed a redex it could not materialise (Net.driver_pending), or answers directly
   through its own `pending` hook.  The core only asks *whether* the net is a value; the reason stays the driver's. */
void lin_pending_bump(Net *n) { n->driver_pending = 1; }
int lin_any_pending(const Net *n) {
  if (n->driver_pending) return 1;
  for (int i = 0; i < ndrv; i++) if (drv[i]->pending && drv[i]->pending(n)) return 1;
  return 0;
}
/* Readback pre-pass: let a driver turn a sub-term the reducer left as a foldable closure (e.g. a saturated `_ffi`
   closure embedded in a numeral spine, which no β redex ever reached) into a concrete value node.  Returns 1 and
   sets `*out` when a driver materialised it; otherwise the caller decodes `p` as it stands. */
int lin_materialize(Net *n, Port p, Port *out) {
  for (int i = 0; i < ndrv; i++)
    if (drv[i]->materialize && drv[i]->materialize(n, p, out)) return 1;
  return 0;
}

/* Work-efficient frontier scratch: grown, never freed per wave (a driver may hold the
   wave for a long time, so these are file-scope and reused across waves). */
static Pair *inter, *bound;
static int *fw_next, *fw_slot, *fw_occ;
static int fw_cap, fw_pair_cap, fw_slot_cap;

/* Reduce one interacting wave (`curr[0..wave_cnt)` holds `act`-form pairs, an even count): spatial-disjoint pairs run concurrently via OpenMP, the rest serially; exposed so driver reducers fan out a real wave in parallel — the base correctness rules all live here */
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
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;
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
      /* Work-efficient frontier.  The previous form allocated and memset a sector table
         of `nn/64` entries on EVERY wave and then swept all of it, so its cost was
         proportional to the NET rather than to the wave: a 512-pair wave on a 100k-node
         net walked ~1.5k empty sectors, and every wave also paid four mallocs.  Measured,
         8 threads came out 2x SLOWER than serial (2115ms vs 1041ms) over identical
         5,165,799 steps -- all overhead, no speedup.
         Now the pairs are bucketed by sector in a table sized to the WAVE, only the
         occupied buckets are iterated (collected in `occ`), and all buffers are
         grow-only statics, so a wave allocates nothing and its dispatch costs O(pairs).
         The buckets are cleared by walking `occ`, so there is no per-wave memset either. */
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
          if (WIRE(n, inter[i].p1).node == inter[i].p2.node && !n->dead[inter[i].p1.node] && !n->dead[inter[i].p2.node])
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
      if (p1.node >= 0 && p2.node >= 0 && !n->dead[p1.node] && !n->dead[p2.node] &&
          WIRE(n, p1).node == p2.node && WIRE(n, p2).node == p1.node && !p1.port && !p2.port) {
        if (net_interact(n, p1, p2)) *changed += 1;
        n->steps++;
      }
    }
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
  /* Self-collecting nets reduce by the active list; BFS+compact reclaims memory after it doubles; waves fan out to every driver in priority order, base engine takes the remainder */
  Port *curr = NULL; int curr_cap = 0;
  unsigned char *reach = NULL; int *q = NULL; long qcap = 0, gcmark = 1L << 20;
  /* per-driver slice buckets (rebuilt each wave) */
  Port *slices[16] = {0}; int scaps[16] = {0}, scnts[16] = {0};
  long last_drain_steps = -1; int stalled_drains = 0;   /* livelock guard for driver drain loops */
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
    /* The active wave is fully drained.  Give every driver its drain point: a driver that parked a redex because
       its operands were not concrete yet retries it here and re-enqueues what it still expects to materialise.
       The *policy* (how long to wait, when to give up) is the driver's; the core only supplies the point and a
       livelock guard, since a driver that re-enqueues without anything progressing would otherwise spin forever. */
    {
      int re = 0;
      for (int di = 0; di < ndrv; di++) if (drv[di]->drain) re += drv[di]->drain(n);
      if (re > 0) {
        if (n->steps == last_drain_steps) { if (++stalled_drains > 4096) { n->atop = 0; break; } }
        else stalled_drains = 0;
        last_drain_steps = n->steps;
        continue;
      }
      stalled_drains = 0;
    }
    if (changed == 0 && n->atop == 0) break;
    if (n->atop == 0 && (long)n->nn > gcmark) {
      net_gc(n);
      gcmark = (long)n->nn * 2 + 64;
      for (int i = 1; i < n->nn; i++) if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
        act_push(n, (Port){i, 0}, n->wire[i * 3]);
    }
  }
  (void)reach; (void)q; (void)qcap;
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
  c->nlv = n->nlv; c->lvcap = n->nlv + 1; c->lv_hcap = 0; c->lv_hash = NULL;
  c->lv_parent = malloc((size_t)(n->nlv + 1) * sizeof(int));
  c->lv_depth = malloc((size_t)(n->nlv + 1) * sizeof(int));
  c->lv_bit = malloc((size_t)(n->nlv + 1));
  memcpy(c->lv_parent, n->lv_parent, (size_t)(n->nlv + 1) * sizeof(int));
  memcpy(c->lv_depth, n->lv_depth, (size_t)(n->nlv + 1) * sizeof(int));
  memcpy(c->lv_bit, n->lv_bit, (size_t)(n->nlv + 1));
  lv_rehash(c, lv_hcap_for(c->nlv));
  c->act = NULL; c->actcap = c->atop = 0; c->steps = 0; c->driver_pending = 0;
  return c;
}