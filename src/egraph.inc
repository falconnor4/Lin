/* ============================================================================
 * E-graph AOT optimizer -- a PASS, not part of the calculus.
 *
 * Whole-program equality saturation over the expanded term, with sharing-aware extraction.  It may
 * be wrong or absent and every program still compiles and runs (`egraph_optimize` falls back to the
 * term it was given).
 *
 * This is an .inc file: compile.c `#include`s it, so the code is part of that translation unit and
 * the build needs no extra rule.  It lives in src/ but is NOT part of the core the line budget
 * measures -- test/run_tests.sh counts only the .c and .h files here, and that budget exists to
 * keep the CALCULUS readable, not to bound a pass the engine does not need.
 * ========================================================================== */

typedef struct { int type; char name[NAME]; int l, r; } ENode;
typedef struct { int parent, best_node, cost; } EClass;
typedef struct {
  ENode *nodes; int nn, ncap;
  EClass *classes; int nc, ccap;
  int *node_cls;
  int *slot, hcap;        /* (type,name,children) -> e-node, so insertion is not quadratic */
  int *uses;              /* how many e-nodes reference each class: the sharing the pass found */
  int capture;            /* set by eg_subst when a rewrite would capture: the rule then declines */
} EGraph;

static int eg_find(EGraph *g, int c) {
  while (g->classes[c].parent != c) { g->classes[c].parent = g->classes[g->classes[c].parent].parent; c = g->classes[c].parent; }
  return c;
}

/* Opaque/leaf kinds (TDEF no-body, TDEFX, floats) have no egraph structural children: recursing into t->l yielded sentinel -1 as a child and eg_find(-1) OOB — skewed reconstruction (stray `_sz`) broke `lin build` */
static int eg_opaque(int type) {
  switch (type) {
  case TDEF:
  case TDEFX:
  case TFLOAT:
    return 1;
  default:
    return 0;
  }
}

static void eg_union(EGraph *g, int c1, int c2) {
  c1 = eg_find(g, c1); c2 = eg_find(g, c2); if (c1 == c2) return;
  if (g->classes[c1].cost <= g->classes[c2].cost) g->classes[c2].parent = c1; else g->classes[c1].parent = c2;
}

/* The rewrite rules are data: a row per optimization, with whether it is on and how often it
   fired, so a new optimization is a row rather than another arm in the saturation loop.  `eta`
   is kept as a row but is off by default: it fired zero times on every program measured, and the
   whole measured win of this pass is `beta` (`line_ffi` 8,166 -> 7,802 compiled nodes, 122,143 ->
   119,843 bytes, 13 unionations; bytes move with the container format).  LIN_EGRULES=beta,eta turns it on. */
enum { EG_BETA = 1, EG_ETA };
typedef struct { const char *name; int kind; int param; int on; long fires, declines; } EgRule;
static EgRule eg_rules[] = {
  /* name   kind      param  on  fires declines */
  { "beta", EG_BETA,  64,    1,  0,    0 },
  { "eta",  EG_ETA,   0,     0,  0,    0 },
};
#define EG_NRULES ((int)(sizeof eg_rules / sizeof eg_rules[0]))
static int eg_beta_only = 1;
static void eg_rules_init(void) {
  const char *sel = getenv("LIN_EGRULES");
  eg_beta_only = !(sel && strstr(sel, "eta"));
  eg_rules[0].on = 1;
  eg_rules[1].on = !eg_beta_only;
  for (int i = 0; i < EG_NRULES; i++) { eg_rules[i].fires = 0; eg_rules[i].declines = 0; }
}

/* Cost of a form: what the extracted term will weigh. */
static int eg_cost(EGraph *g, ENode *n) {
  if (n->type == TVAR || eg_opaque(n->type)) return 1;
  if (n->type == TLAM) return 2 + g->classes[eg_find(g, n->l)].cost;
  return 3 + g->classes[eg_find(g, n->l)].cost + g->classes[eg_find(g, n->r)].cost;
}

/* e-node lookup by (type, name, children): a hash table, because the linear scan this replaces
   made insertion quadratic in the node cap and was the pass's scaling limit */
static unsigned eg_hash(int type, const char *name, int l, int r) {
  unsigned h = (unsigned)type * 2654435761u;
  for (const char *p = name ? name : ""; *p; p++) h = h * 131u + (unsigned char)*p;
  h = h * 2654435761u + (unsigned)l; h = h * 2654435761u + (unsigned)r;
  return h;
}
static void eg_rehash(EGraph *g, int cap) {
  g->hcap = cap;
  g->slot = realloc(g->slot, (size_t)cap * sizeof(int));
  memset(g->slot, -1, (size_t)cap * sizeof(int));
  for (int i = 0; i < g->nn; i++) {
    ENode *n = &g->nodes[i];
    unsigned h = eg_hash(n->type, n->name, n->l, n->r) & (unsigned)(cap - 1);
    while (g->slot[h] >= 0) h = (h + 1) & (unsigned)(cap - 1);
    g->slot[h] = i;
  }
}
static int eg_lookup(EGraph *g, int type, const char *name, int l, int r) {
  if (g->hcap <= (g->nn + 1) * 2) eg_rehash(g, g->hcap ? g->hcap * 2 : 1024);
  unsigned h = eg_hash(type, name, l, r) & (unsigned)(g->hcap - 1);
  while (g->slot[h] >= 0) {
    ENode *n = &g->nodes[g->slot[h]];
    if (n->type == type && n->l == l && n->r == r && !strcmp(n->name, name ? name : "")) return g->slot[h];
    h = (h + 1) & (unsigned)(g->hcap - 1);
  }
  return -1;
}
static void eg_insert(EGraph *g, int node) {
  unsigned h = eg_hash(g->nodes[node].type, g->nodes[node].name, g->nodes[node].l, g->nodes[node].r) & (unsigned)(g->hcap - 1);
  while (g->slot[h] >= 0) h = (h + 1) & (unsigned)(g->hcap - 1);
  g->slot[h] = node;
}

static int eg_add(EGraph *g, int type, const char *name, int l, int r) {
  if (l >= 0) l = eg_find(g, l);
  if (r >= 0) r = eg_find(g, r);
  int hit = eg_lookup(g, type, name, l, r);
  if (hit >= 0) return eg_find(g, g->node_cls[hit]);
  if (g->nn >= g->ncap) {
    g->nodes = realloc(g->nodes, (size_t)(g->ncap = g->ncap ? g->ncap * 2 : 128) * sizeof(ENode));
    g->node_cls = realloc(g->node_cls, (size_t)g->ncap * sizeof(int));
  }
  if (g->nc >= g->ccap)
    g->classes = realloc(g->classes, (size_t)(g->ccap = g->ccap ? g->ccap * 2 : 128) * sizeof(EClass));
  int nid = g->nn++, cid = g->nc++;
  g->nodes[nid] = (ENode){.type = type, .l = l, .r = r};
  snprintf(g->nodes[nid].name, NAME, "%s", name ? name : "");
  g->node_cls[nid] = cid;
  g->classes[cid] = (EClass){.parent = cid, .best_node = nid, .cost = eg_cost(g, &g->nodes[nid])};
  eg_insert(g, nid);
  return cid;
}

static int eg_add_term(EGraph *g, Term *t) {
  if (!t) return -1;
  if (t->type == TVAR) return eg_add(g, TVAR, t->name, -1, -1);
  if (t->type == TLAM) return eg_add(g, TLAM, t->name, eg_add_term(g, t->l), -1);
  if (t->type == TAPP) return eg_add(g, TAPP, "", eg_add_term(g, t->l), eg_add_term(g, t->r));
  /* TLET is structural, like TAPP: it must keep both children, since they are the whole binding. */
  if (t->type == TLET) return eg_add(g, TLET, t->name, eg_add_term(g, t->l), eg_add_term(g, t->r));
  if (eg_opaque(t->type)) return eg_add(g, t->type, t->name, -1, -1);
  return eg_add_term(g, t->l);
}

static int eg_has_var(EGraph *g, int c, const char *name) {
  c = eg_find(g, c); ENode n = g->nodes[g->classes[c].best_node];
  if (n.type == TVAR) return !strcmp(n.name, name);
  if (n.type == TLAM) return strcmp(n.name, name) && eg_has_var(g, n.l, name);
  if (n.type == TAPP) return eg_has_var(g, n.l, name) || eg_has_var(g, n.r, name);
  /* Conservative for a binding: its value may refer to the name, and declining costs only rewrites. */
  if (n.type == TLET) return 1;
  return 0;
}

/* Substitute `arg` for `name` in class `c`.  Beta is only sound if this is CAPTURE-AVOIDING: the
   argument lands under whatever binders the body has, so a binder whose name occurs free in the
   argument would capture those occurrences and silently change the meaning.  Measured on
   `((\y (((\x (\y x)) y) 5)) 99)`: the correct answer is 99, but substituting under the inner `\y`
   captured the argument's `y`, so the pass rewrote the term to `(\y y)`, extraction preferred that
   form (cost 3 against 9), and `lin build` shipped an artifact printing 5 while the interpreter
   printed 99 -- on the DEFAULT candidate, not just under LIN_AOT_SEARCH.

   Alpha-renaming the binder also fixes the meaning, and was measured: it keeps the rewrite, but
   Lin PRINTS binder names, so the invented name is observable -- the same program came out as
   `(\y%0 y)` from the artifact where the interpreter prints `(\y y)`.  A pass that only ever
   removes work should not be able to alter what a program prints, so a capture-risk rewrite is
   DECLINED instead (`g->capture`), and extraction can then only return a term the compiler would
   have produced anyway.  Every name in the graph survives verbatim. */
static int eg_subst(EGraph *g, int c, const char *name, int arg, int d) {
  if (d > 1024) { g->capture = 1; return c; }
  c = eg_find(g, c); ENode n = g->nodes[g->classes[c].best_node];
  if (n.type == TVAR) return !strcmp(n.name, name) ? arg : c;
  if (n.type == TLAM) {
    if (!strcmp(n.name, name)) return c;
    if (eg_has_var(g, arg, n.name)) { g->capture = 1; return c; }
    return eg_add(g, TLAM, n.name, eg_subst(g, n.l, name, arg, d + 1), -1);
  }
  if (n.type == TAPP)
    return eg_add(g, TAPP, "", eg_subst(g, n.l, name, arg, d + 1), eg_subst(g, n.r, name, arg, d + 1));
  /* A binding is cyclic by construction, so substituting into it is declined rather than guessed at
     (the same signal a capture uses); `eg_has_var` above is conservative for the same reason. */
  if (n.type == TLET) { g->capture = 1; return c; }
  return c;
}

static void eg_saturate(EGraph *g) {
  const int rounds = 4, cap = 32768;      /* measured defaults: more rounds or a bigger cap did not pay */
  eg_rules_init();
  for (int round = 0; round < rounds; round++) {
    int start_n = g->nn;
    /* the cost model asks which classes are shared, so the counts are refreshed per round */
    for (int i = 0; i < start_n && g->nn < cap; i++) {
      ENode n = g->nodes[i]; int cls = eg_find(g, g->node_cls[i]);
      for (int r = 0; r < EG_NRULES; r++) {
        if (!eg_rules[r].on) continue;
        if (eg_rules[r].kind == EG_BETA && n.type == TAPP) {
          int fn_cls = eg_find(g, n.l), bn = g->classes[fn_cls].best_node;
          if (bn >= 0 && bn < g->nn && g->nodes[bn].type == TLAM) {
            int bl = eg_find(g, g->nodes[bn].l);
            if (g->classes[bl].cost <= eg_rules[r].param) {
              char vn[NAME]; snprintf(vn, NAME, "%s", g->nodes[bn].name);
              int before = eg_find(g, cls);
              g->capture = 0;
              int sub = eg_subst(g, g->nodes[bn].l, vn, n.r, 0);
              /* a rewrite that would capture is not applied at all -- see eg_subst */
              if (g->capture) { eg_rules[r].declines++; continue; }
              eg_union(g, cls, sub);
              if (eg_find(g, cls) != before) eg_rules[r].fires++;
            }
          }
        } else if (eg_rules[r].kind == EG_ETA && n.type == TLAM) {
          int body_cls = eg_find(g, n.l), bn = g->classes[body_cls].best_node;
          if (bn >= 0 && bn < g->nn && g->nodes[bn].type == TAPP) {
            int an_node = g->classes[eg_find(g, g->nodes[bn].r)].best_node;
            if (an_node >= 0 && an_node < g->nn) {
              ENode an = g->nodes[an_node];
              if (an.type == TVAR && !strcmp(an.name, n.name) && !eg_has_var(g, g->nodes[bn].l, n.name)) {
                int before = eg_find(g, cls);
                eg_union(g, cls, g->nodes[bn].l);
                if (eg_find(g, cls) != before) eg_rules[r].fires++;
              }
            }
          }
        }
      }
    }
    for (int i = 0; i < g->nn; i++) {
      ENode n = g->nodes[i]; int c = eg_find(g, g->node_cls[i]), cost = eg_cost(g, &n);
      if (cost < g->classes[c].cost) { g->classes[c].cost = cost; g->classes[c].best_node = i; }
    }
  }
}

static Term *eg_extract(EGraph *g, int c, int d) {
  if (d > 2048) return NULL;
  c = eg_find(g, c); ENode n = g->nodes[g->classes[c].best_node];
  if (n.type == TVAR) return term_new(TVAR, n.name, NULL, NULL);
  if (eg_opaque(n.type)) return term_new(n.type, n.name, NULL, NULL);
  if (n.type == TLAM) { Term *l = eg_extract(g, n.l, d + 1); return l ? term_new(TLAM, n.name, l, NULL) : NULL; }
  if (n.type == TAPP) {
    Term *l = eg_extract(g, n.l, d + 1), *r = eg_extract(g, n.r, d + 1);
    if (!l || !r) { term_free(l); term_free(r); return NULL; }
    return term_new(TAPP, "", l, r);
  }
  if (n.type == TLET) {
    Term *l = eg_extract(g, n.l, d + 1), *r = eg_extract(g, n.r, d + 1);
    if (!l || !r) { term_free(l); term_free(r); return NULL; }
    return term_new(TLET, n.name, l, r);
  }
  return NULL;
}

Term *egraph_optimize(Term *t) {
  if (!t) return NULL;
  if (getenv("LIN_NO_EGRAPH")) return term_copy(t);
  EGraph g = {0}; int root = eg_add_term(&g, t); eg_saturate(&g);
  /* how much sharing did saturation expose?  an e-node field pointing at a class is a parent,
     so a class with several parents is a value the program computes more than once */
  g.uses = calloc((size_t)g.nc + 1, sizeof(int));
  int shared = 0;
  if (g.uses) {
    for (int i = 0; i < g.nn; i++) {
      if (g.nodes[i].l >= 0) g.uses[eg_find(&g, g.nodes[i].l)]++;
      if (g.nodes[i].r >= 0) g.uses[eg_find(&g, g.nodes[i].r)]++;
    }
    for (int c = 0; c < g.nc; c++) if (g.uses[c] >= 2) shared++;
  }
  Term *res = (root < 0) ? NULL : eg_extract(&g, root, 0);
  if (getenv("LIN_PASSES")) {
    fprintf(stderr, "[egraph] %d classes, %d e-nodes, %d shared classes, rules:",
            g.nc, g.nn, shared);
    for (int r = 0; r < EG_NRULES; r++) {
      fprintf(stderr, " %s=%s/%ld", eg_rules[r].name, eg_rules[r].on ? "on" : "off", eg_rules[r].fires);
      if (eg_rules[r].declines) fprintf(stderr, "(+%ld capture-declined)", eg_rules[r].declines);
    }
    fprintf(stderr, "\n");
  }
  free(g.nodes); free(g.classes); free(g.node_cls); free(g.slot); free(g.uses);
  return res ? res : term_copy(t);
}
