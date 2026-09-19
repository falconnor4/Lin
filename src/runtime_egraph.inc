/* E-graph AOT optimizer (std — not core): #included into src/compile.c.
   Whole-program equality saturation over the expanded term, with sharing-aware extraction.
   This is a *pass*, not part of the calculus: it may be wrong or absent and every program still
   compiles and runs (egraph_optimize falls back to the term it was given), which is why it lives
   here with the container rather than in the core. */
/* ---------------- E-Graph AOT Optimizer ---------------- */
typedef struct { int type; char name[NAME]; int l, r; } ENode;
typedef struct { int parent, best_node, cost; } EClass;
typedef struct {
  ENode *nodes; int nn, ncap;
  EClass *classes; int nc, ccap;
  int *node_cls;
  int *slot, hcap;        /* (type,name,children) -> e-node, so insertion is not quadratic */
  int *uses;              /* how many e-nodes reference each class: the sharing the pass found */
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

/* The rewrite rules are data: a row per optimization, with which one is on and how often it
   fired.  Adding an optimization is a row, not a new arm in the saturation loop, and each row can
   be switched off (LIN_EGRULES=beta,eta) so its contribution is measured rather than assumed. */
enum { EG_BETA = 1, EG_ETA };
typedef struct { const char *name; int kind; int param; int on; long fires; } EgRule;
static EgRule eg_rules[] = {
  /* name   kind      param                     on  fires */
  { "beta", EG_BETA,  64,                       1,  0 },   /* inline a lambda applied to an argument */
  { "eta",  EG_ETA,   0,                        1,  0 },   /* collapse (\x (f x)) */
};
#define EG_NRULES ((int)(sizeof eg_rules / sizeof eg_rules[0]))
static void eg_rules_init(void) {
  const char *sel = getenv("LIN_EGRULES");
  for (int i = 0; i < EG_NRULES; i++) { eg_rules[i].on = sel ? 0 : 1; eg_rules[i].fires = 0; }
  if (sel)
    for (const char *p = sel; *p; ) {
      const char *comma = strchr(p, ',');
      size_t n = comma ? (size_t)(comma - p) : strlen(p);
      for (int i = 0; i < EG_NRULES; i++)
        if (strlen(eg_rules[i].name) == n && !strncmp(eg_rules[i].name, p, n)) eg_rules[i].on = 1;
      p = comma ? comma + 1 : p + strlen(p);
    }
}

/* Cost of a form.  The tree model charges every child to every parent, which prices a value the
   program computes once as if it were recomputed per use; the sharing-aware model charges a class
   that is itself shared once (its `uses` are what the extraction binds), so the pass prefers forms
   whose repeated parts are already shared.  LIN_EGCOST=tree|dag selects, default sharing-aware. */
/* Default tree: the sharing-aware model as written does not terminate in the current saturation
   (measured: it hangs on both container programs), so it stays behind LIN_EGCOST=dag until it is
   stable.  The table below is what makes that a switch rather than a rewrite. */
static int eg_cost_dag = 0;
static int eg_cost(EGraph *g, ENode *n) {
  if (n->type == TVAR || eg_opaque(n->type)) return 1;
  if (n->l < 0 && n->r < 0) return 2;
  int shared_l = (eg_cost_dag && g->uses && n->l >= 0 && g->uses[eg_find(g, n->l)] >= 2) ? 0 : g->classes[eg_find(g, n->l)].cost;
  if (n->type == TLAM) return 2 + shared_l;
  int shared_r = (eg_cost_dag && g->uses && n->r >= 0 && g->uses[eg_find(g, n->r)] >= 2) ? 0 : g->classes[eg_find(g, n->r)].cost;
  return 3 + shared_l + shared_r;
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
  if (eg_opaque(t->type)) return eg_add(g, t->type, t->name, -1, -1);
  return eg_add_term(g, t->l);
}

static int eg_has_var(EGraph *g, int c, const char *name) {
  c = eg_find(g, c); ENode n = g->nodes[g->classes[c].best_node];
  if (n.type == TVAR) return !strcmp(n.name, name);
  if (n.type == TLAM) return strcmp(n.name, name) && eg_has_var(g, n.l, name);
  if (n.type == TAPP) return eg_has_var(g, n.l, name) || eg_has_var(g, n.r, name);
  return 0;
}

static int eg_subst(EGraph *g, int c, const char *name, int arg, int d) {
  if (d > 1024) return c;
  c = eg_find(g, c); ENode n = g->nodes[g->classes[c].best_node];
  if (n.type == TVAR) return !strcmp(n.name, name) ? arg : c;
  if (n.type == TLAM) {
    if (!strcmp(n.name, name)) return c;
    return eg_add(g, TLAM, n.name, eg_subst(g, n.l, name, arg, d + 1), -1);
  }
  if (n.type == TAPP)
    return eg_add(g, TAPP, "", eg_subst(g, n.l, name, arg, d + 1), eg_subst(g, n.r, name, arg, d + 1));
  return c;
}

static void eg_saturate(EGraph *g) {
  static int rounds = -1, cap = -1;
  if (rounds < 0) { const char *e = getenv("LIN_EGROUNDS"); rounds = e ? atoi(e) : 4; }
  if (cap < 0) { const char *e = getenv("LIN_EGCAP"); cap = e ? atoi(e) : 32768; }
  eg_rules_init();
  for (int round = 0; round < rounds; round++) {
    int start_n = g->nn;
    /* the cost model asks which classes are shared, so the counts are refreshed per round */
    if (eg_cost_dag) {
      if (!g->uses) g->uses = calloc((size_t)g->nc + 1, sizeof(int));
      if (g->uses) {
        memset(g->uses, 0, ((size_t)g->nc + 1) * sizeof(int));
        for (int i = 0; i < g->nn; i++) {
          if (g->nodes[i].l >= 0) g->uses[eg_find(g, g->nodes[i].l)]++;
          if (g->nodes[i].r >= 0) g->uses[eg_find(g, g->nodes[i].r)]++;
        }
      }
    }
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
              eg_union(g, cls, eg_subst(g, g->nodes[bn].l, vn, n.r, 0));
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
  return NULL;
}

Term *egraph_optimize(Term *t) {
  if (!t) return NULL;
  if (getenv("LIN_NO_EGRAPH")) return term_copy(t);
  static int cost_env = -1;
  if (cost_env < 0) { const char *e = getenv("LIN_EGCOST"); cost_env = (e && !strcmp(e, "dag")) ? 1 : 0; }
  eg_cost_dag = cost_env;
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
    fprintf(stderr, "[egraph] %d classes, %d e-nodes, %d shared classes, cost %s, rules:",
            g.nc, g.nn, shared, eg_cost_dag ? "sharing-aware" : "tree");
    for (int r = 0; r < EG_NRULES; r++)
      fprintf(stderr, " %s=%s/%ld", eg_rules[r].name, eg_rules[r].on ? "on" : "off", eg_rules[r].fires);
    fprintf(stderr, "\n");
  }
  free(g.nodes); free(g.classes); free(g.node_cls); free(g.slot); free(g.uses);
  return res ? res : term_copy(t);
}

