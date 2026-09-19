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
  for (int round = 0; round < 4; round++) {
    int start_n = g->nn;
    for (int i = 0; i < start_n && g->nn < 32768; i++) {
      ENode n = g->nodes[i]; int cls = eg_find(g, g->node_cls[i]);
      if (n.type == TAPP) {
        int fn_cls = eg_find(g, n.l), bn = g->classes[fn_cls].best_node;
        if (bn >= 0 && bn < g->nn && g->nodes[bn].type == TLAM) {
          int bl = eg_find(g, g->nodes[bn].l);
          if (g->classes[bl].cost <= 64) {
            char vn[NAME]; snprintf(vn, NAME, "%s", g->nodes[bn].name);
            eg_union(g, cls, eg_subst(g, g->nodes[bn].l, vn, n.r, 0));
          }
        }
      } else if (n.type == TLAM) {
        int body_cls = eg_find(g, n.l), bn = g->classes[body_cls].best_node;
        if (bn >= 0 && bn < g->nn && g->nodes[bn].type == TAPP) {
          int an_node = g->classes[eg_find(g, g->nodes[bn].r)].best_node;
          if (an_node >= 0 && an_node < g->nn) {
            ENode an = g->nodes[an_node];
            if (an.type == TVAR && !strcmp(an.name, n.name) && !eg_has_var(g, g->nodes[bn].l, n.name))
              eg_union(g, cls, g->nodes[bn].l);
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

/* ---------------- extraction that keeps the sharing the graph found ----------------
   A class referenced by more than one e-node used to be emitted once per parent, so the CSE the
   e-graph performs was thrown away before the net was built.  It is now bound with a `let`,
   which the compiler compiles into the same DUP fan a multi-use binder gets: one computation,
   N consumers.  A class currently being extracted is never shared with itself (an equality the
   rules introduced inside it must not make the binding refer to its own value).

   Bindings are wrapped in *discovery* order, which puts the deeper ones outermost -- a binding's
   value is evaluated outside its own binder, so anything that value references has to be in
   scope before it. */
typedef struct { int cls; char name[NAME]; Term *body; } EgBind;
static EgBind *eg_binds; static int eg_nbinds, eg_bcap;
static int *eg_state, *eg_bindof;      /* per class: 0 untouched, 1 in progress, 2 bound */
static int eg_share = 1;
/* A binding's value is evaluated outside its own binder, so a body that references another
   binding needs that one *outside* it -- in a flat nesting that is a dependency order, and the
   discovery order does not provide one (a later-discovered binding can be referenced by an
   earlier one and vice versa).  These record the references so the bindings can be ordered. */
static int (*eg_dep)[2]; static int eg_ndep, eg_depcap;   /* (body i references binding j) */
static int *eg_cur, eg_ncur;
static void eg_dep_add(int i, int j) {
  for (int k = 0; k < eg_ndep; k++) if (eg_dep[k][0] == i && eg_dep[k][1] == j) return;
  if (eg_ndep >= eg_depcap) {
    eg_depcap = eg_depcap ? eg_depcap * 2 : 64;
    eg_dep = realloc(eg_dep, (size_t)eg_depcap * sizeof(*eg_dep));
  }
  eg_dep[eg_ndep][0] = i; eg_dep[eg_ndep][1] = j; eg_ndep++;
}
static Term *eg_x(EGraph *g, int c, int d) {
  if (d > 1024) return NULL;
  c = eg_find(g, c);
  if (eg_state[c] == 1) return NULL;                       /* a cycle the rules created: bail */
  if (eg_state[c] == 2) {
    int j = eg_bindof[c];
    if (eg_ncur > 0) eg_dep_add(eg_cur[eg_ncur - 1], j);
    return term_new(TVAR, eg_binds[j].name, NULL, NULL);
  }
  ENode n = g->nodes[g->classes[c].best_node];
  int structural = (n.type == TLAM || n.type == TAPP);
  int share = eg_share && structural && g->uses[c] >= 2;
  int slot = -1;
  if (share) {
    if (eg_nbinds >= eg_bcap) { eg_bcap = eg_bcap ? eg_bcap * 2 : 64; eg_binds = realloc(eg_binds, (size_t)eg_bcap * sizeof(EgBind)); }
    slot = eg_nbinds++;
    snprintf(eg_binds[slot].name, NAME, "_eg%d", slot);
    eg_binds[slot].cls = c; eg_binds[slot].body = NULL;
    eg_bindof[c] = slot;
  }
  if (structural) eg_state[c] = 1;
  if (share) {
    eg_cur = realloc(eg_cur, (size_t)(eg_ncur + 1) * sizeof(int));
    eg_cur[eg_ncur++] = slot;
  }
  Term *me = NULL;
  if (n.type == TVAR) me = term_new(TVAR, n.name, NULL, NULL);
  else if (eg_opaque(n.type)) me = term_new(n.type, n.name, NULL, NULL);
  else if (n.type == TLAM) { Term *l = eg_x(g, n.l, d + 1); if (l) me = term_new(TLAM, n.name, l, NULL); }
  else if (n.type == TAPP) {
    Term *l = eg_x(g, n.l, d + 1), *r = eg_x(g, n.r, d + 1);
    if (l && r) me = term_new(TAPP, "", l, r); else { term_free(l); term_free(r); }
  }
  if (share) {
    eg_ncur--;                                    /* this binding's body is done */
    eg_binds[slot].body = me;
    eg_state[c] = me ? 2 : 1;
    /* the reference to this binding sits inside the enclosing binding's body (if any), so the
       enclosing one has to be ordered outside it */
    if (me && eg_ncur > 0) eg_dep_add(eg_cur[eg_ncur - 1], slot);
    return me ? term_new(TVAR, eg_binds[slot].name, NULL, NULL) : NULL;
  }
  if (structural) eg_state[c] = 0;
  return me;
}

/* emit `i` after everything its body references (a depth-first order over eg_dep) */
static void eg_wrap_order(int i, int *state, int *order, int *norder, int *cyc) {
  if (i < 0 || i >= eg_nbinds || state[i] == 2) return;
  if (state[i] == 1) { *cyc = 1; return; }
  state[i] = 1;
  for (int k = 0; k < eg_ndep; k++) if (eg_dep[k][0] == i) eg_wrap_order(eg_dep[k][1], state, order, norder, cyc);
  state[i] = 2;
  order[(*norder)++] = i;
}

/* 1 if every generated name in `t` occurs inside its own binder.  Extraction orders the bindings
   by dependency, and a mistake in that order would ship a program with a free variable, so the
   result is checked, and the plain tree extraction used instead when the check fails. */
static int eg_closed_rec(Term *t, unsigned char *bound, int depth) {
  if (!t || depth > 4096) return 1;
  if (t->type == TVAR) {
    for (int i = 0; i < eg_nbinds; i++) if (!strcmp(eg_binds[i].name, t->name)) return bound[i];
    return 1;                                        /* a name the program itself uses */
  }
  if (t->type == TLAM) {
    for (int i = 0; i < eg_nbinds; i++)
      if (!strcmp(eg_binds[i].name, t->name)) {
        if (bound[i]) return eg_closed_rec(t->l, bound, depth + 1);
        bound[i] = 1; int ok = eg_closed_rec(t->l, bound, depth + 1); bound[i] = 0; return ok;
      }
    return eg_closed_rec(t->l, bound, depth + 1);
  }
  if (t->type == TAPP) return eg_closed_rec(t->l, bound, depth + 1) && eg_closed_rec(t->r, bound, depth + 1);
  return 1;
}
static int eg_closed(Term *t) {
  unsigned char *bound = calloc((size_t)eg_nbinds + 1, 1);
  int ok = bound ? eg_closed_rec(t, bound, 0) : 1;
  free(bound);
  return ok;
}

static Term *eg_extract_shared(EGraph *g, int root) {
  Term *res = NULL;
  eg_nbinds = 0;
  free(eg_state); free(eg_bindof);
  eg_state = calloc((size_t)g->nc + 1, sizeof(int));
  eg_bindof = malloc(((size_t)g->nc + 1) * sizeof(int));
  if (!eg_state || !eg_bindof) { free(eg_state); free(eg_bindof); eg_state = eg_bindof = NULL; return NULL; }
  eg_ncur = 0;
  res = (root < 0) ? NULL : eg_x(g, root, 0);
  if (res) {
    int *state = calloc((size_t)eg_nbinds + 1, sizeof(int));
    int *order = malloc(((size_t)eg_nbinds + 1) * sizeof(int));
    int norder = 0, cyc = 0;
    for (int i = 0; i < eg_nbinds && !cyc; i++) eg_wrap_order(i, state, order, &norder, &cyc);
    if (cyc) { term_free(res); res = NULL; }         /* mutually recursive sharing: no plain let */
    else
      for (int k = norder - 1; k >= 0; k--) {        /* deps wrapped last, so they end up outside */
        int i = order[k];
        if (!eg_binds[i].body) { term_free(res); res = NULL; break; }
        char nm[NAME]; snprintf(nm, NAME, "%s", eg_binds[i].name);
        res = term_new(TAPP, "", term_new(TLAM, nm, res, NULL), eg_binds[i].body);
      }
    free(state); free(order);
    if (res && !getenv("LIN_EGNOCHECK") && !eg_closed(res)) { term_free(res); res = NULL; }
  }
  free(eg_state); free(eg_bindof); eg_state = eg_bindof = NULL;
  return res;
}

Term *egraph_optimize(Term *t) {
  if (!t) return NULL;
  if (getenv("LIN_NO_EGRAPH")) return term_copy(t);
  static int share_env = -1;
  if (share_env < 0) share_env = getenv("LIN_EGSHARE") ? atoi(getenv("LIN_EGSHARE")) : 1;
  eg_share = share_env;
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
  Term *res = eg_share ? eg_extract_shared(&g, root)
                       : ((root < 0) ? NULL : eg_extract(&g, root, 0));
  if (getenv("LIN_PASSES"))
    fprintf(stderr, "[egraph] %d classes, %d e-nodes, %d shared classes, saturate %s, extract %s\n",
            g.nc, g.nn, shared, getenv("LIN_NO_EGRAPH") ? "skipped" : "4 rounds",
            eg_share ? "shared (lets)" : "tree (sharing discarded)");
  if (res && res != t) {
    /* A binding is wrapped around the whole term, which is only valid if the shared subterm did
       not need the lambda binders it sat under -- a subterm mentioning a variable that is bound
       above it becomes free.  The compiler is the authority on that: compile a scratch copy and
       keep the sharing only if it compiles. */
    char cerr[256];
    Net probe; net_init(&probe, 64);
    int ok = compile(res, &probe, cerr, sizeof cerr);
    net_free(&probe);
    if (!ok) {
      if (getenv("LIN_PASSES")) fprintf(stderr, "[egraph] shared extraction rejected (%s): using tree\n", cerr);
      term_free(res);
      res = (root < 0) ? NULL : eg_extract(&g, root, 0);
    }
  }
  free(g.nodes); free(g.classes); free(g.node_cls); free(g.slot); free(g.uses);
  return res ? res : term_copy(t);
}

