#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef struct {
  char name[NAME];
  Port bind;
  int count;
  Port *extra;
  int nextra, mextra;
} CVar;

static CVar *cstack;
static int csp, ccsp;
static Net *N;
static jmp_buf CJ;
static char CMSG[256];

static _Noreturn void cfail(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(CMSG, sizeof CMSG, fmt, ap);
  va_end(ap);
  longjmp(CJ, 1);
}

static void push_var(const char *name, Port bind) {
  if (csp >= ccsp) cstack = realloc(cstack, (size_t)(ccsp = ccsp ? ccsp * 2 : 64) * sizeof(CVar));
  CVar *e = &cstack[csp++];
  snprintf(e->name, NAME, "%s", name);
  e->bind = bind; e->count = 0; e->extra = NULL; e->nextra = e->mextra = 0;
}

static void add_extra(CVar *e, Port p) {
  if (e->nextra >= e->mextra) e->extra = realloc(e->extra, (size_t)(e->mextra = e->mextra ? e->mextra * 2 : 8) * sizeof(Port));
  e->extra[e->nextra++] = p;
}

/* left-leaning DUP fan-out tree returning the root principal port */
static Port dup_tree(Port *ts, int nts, Scope sc) {
  if (nts == 1) return ts[0];
  Port d = net_alloc(N, DUP, sc, "");
  net_link(N, (Port){d.node, 1}, ts[0], 0);
  net_link(N, (Port){d.node, 2}, ts[1], 0);
  Port cur = (Port){d.node, 0};
  for (int i = 2; i < nts; i++) {
    Port d2 = net_alloc(N, DUP, sc, "");
    net_link(N, (Port){d2.node, 1}, cur, 0);
    net_link(N, (Port){d2.node, 2}, ts[i], 0);
    cur = (Port){d2.node, 0};
  }
  return cur;
}

/* A fan's gauge is the LEVEL of its sharing point: the path from the term root to the binder
   that owns it.  Two sharing points sit at different positions, so they never share a path --
   equal gauges therefore means "the same sharing point", which makes annihilation sound with
   no counter and no width argument -- and an enclosing binder's path is a prefix of everything
   nested inside it, so scope_meet is a genuine common ancestor (what a fan that meets its own
   copy around a cycle needs).  The unique markers this replaces built words newest-first, so
   their meet compared counter bits and carried no ancestry at all. */
static Scope cur_lvl;      /* the level of the position being compiled; 0 = the term root */
/* the sharing point at the current position; `bit` steps one level in first (a binder's fan
   sits just inside its binder, so it is gauged at the body's level) */
static Scope fan_lvl(void) { return cur_lvl; }
static Scope fan_lvl_at(int bit) { return scope_app(N, cur_lvl, bit); }

/* Clone a pre-reduced define value (closed normal-form net) into N; cut the source ROOT<->value clamp so the clone ties only to the caller.  The clone is
   re-gauged at a fresh level: the body's fans were labelled during its own
   precompile reduction, so splicing it verbatim would give every reference's copy
   identical labels and two independent sharing points would annihilate. */
static Port ct_splice(Def *d, Scope sc) {
  (void)sc;
  Net *s = d->compiled;
  Scope lvl = fan_lvl();
  int n = s->nn, *map = malloc(sizeof(int) * (size_t)(n ? n : 1));
  for (int i = 0; i < n; i++) {
    map[i] = net_alloc(N, s->tag[i], scope_rebase(N, s, lvl, s->scope[i]), s->name[i]).node;
  }
  Port val = s->wire[0]; int vn = val.node;
  for (int i = 0; i < n; i++) {
    if (s->dead[i]) continue;
    for (int p = 0; p < 3; p++) {
      Port w = s->wire[i * 3 + p];
      if (w.node < 0 || (i == 0 && p == 0) || (i == vn && p == (int)val.port)) continue;
      net_link(N, (Port){map[i], p}, (Port){map[w.node], w.port}, 0);
    }
  }
  Port r = (Port){map[vn], val.port}; free(map);
  return r;
}

static Port ct(Term *t, Scope sc) {
  switch (t->type) {
  case TFLOAT: return net_alloc_float(N, strtod(t->name, NULL));
  case TVAR: {
    for (int i = csp - 1; i >= 0; i--) {
      if (strcmp(cstack[i].name, t->name)) continue;
      CVar *e = &cstack[i];
      e->count++;
      if (e->count == 1) return e->bind;
      Port ph = net_alloc(N, ERA, scope_nil(), "");
      add_extra(e, (Port){ph.node, 1});
      return (Port){ph.node, 1};
    }
    cfail("unbound variable '%s'", t->name);
  }
  case TLAM: {
    Port self = net_alloc(N, LAM, fan_lvl(), t->name);
    /* the fan duplicating this binder's occurrences is one sharing point: it is gauged by the
       body's path, which is unique per binder and non-empty even at the root */
    Scope lvl = fan_lvl_at(1);
    push_var(t->name, (Port){self.node, 1});
    int my = csp - 1;
    Scope save = cur_lvl;
    cur_lvl = scope_app(N, cur_lvl, 1);
    Port body = ct(t->l, sc);
    cur_lvl = save;
    net_link(N, (Port){self.node, 2}, body, 0);
    CVar *e = &cstack[my];
    if (e->count == 0) {
      /* unused binder: leave port1 dangling (erasure, as in the reference) */
    } else if (e->count > 1) {
      Port *ts = malloc(sizeof(Port) * (long)e->count);
      ts[0] = N->wire[self.node * 3 + 1];
      for (int i = 0; i < e->nextra; i++) {
        ts[i + 1] = N->wire[e->extra[i].node * 3 + 1];
        N->dead[e->extra[i].node] = 1;
        N->wire[e->extra[i].node * 3 + 1] = (Port){-1, 0};
      }
      Port root = dup_tree(ts, e->count, lvl);
      net_link(N, (Port){self.node, 1}, root, 0);
      free(ts);
    }
    free(e->extra);
    csp--;
    return self;
  }
  case TAPP: {
    /* the child compiles and their links stay interleaved exactly as before: the active-list
       order a compile produces is part of the observable schedule (driver folds key off it) */
    Port a = net_alloc(N, APP, fan_lvl(), "");
    Scope save = cur_lvl;
    cur_lvl = scope_app(N, cur_lvl, 1);
    net_link(N, (Port){a.node, 0}, ct(t->l, sc), 1);
    cur_lvl = scope_app(N, save, 2);
    net_link(N, (Port){a.node, 2}, ct(t->r, sc), 1);
    cur_lvl = save;
    return (Port){a.node, 1};
  }
  case TDEF: {
    Def *dd = def_find(t->name);
    if (!t->l && dd && dd->compiled) return ct_splice(dd, sc); /* precompiled value */
    return ct(t->l, sc);
  }
  }
  return (Port){-1, 0};
}

int compile(Term *t, Net *n, char *err, int errsz) {
  N = n; csp = 0; cur_lvl = 0;
  if (!cstack) { ccsp = 64; cstack = malloc((size_t)ccsp * sizeof(CVar)); }
  if (setjmp(CJ)) {
    snprintf(err, errsz, "%s", CMSG);
    return 0;
  }
  Port r = ct(t, scope_nil());
  net_link(N, (Port){0, 0}, r, 0);
  return 1;
}

/* E-graph AOT optimizer (std — not core).
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

/* The rewrite rules are data: a row per optimization, with whether it is on and how often it
   fired, so a new optimization is a row rather than another arm in the saturation loop.  `eta`
   is kept as a row but is off by default: it fired zero times on every program measured, and the
   whole measured win of this pass is `beta` (`line_ffi` 8,166 -> 7,802 compiled nodes, 122,149 ->
   119,854 bytes, 13 unionations).  LIN_EGRULES=beta,eta turns it on. */
enum { EG_BETA = 1, EG_ETA };
typedef struct { const char *name; int kind; int param; int on; long fires; } EgRule;
static EgRule eg_rules[] = {
  /* name   kind      param  on  fires */
  { "beta", EG_BETA,  64,    1,  0 },
  { "eta",  EG_ETA,   0,     0,  0 },
};
#define EG_NRULES ((int)(sizeof eg_rules / sizeof eg_rules[0]))
static int eg_beta_only = 1;
static void eg_rules_init(void) {
  const char *sel = getenv("LIN_EGRULES");
  eg_beta_only = !(sel && strstr(sel, "eta"));
  eg_rules[0].on = 1;
  eg_rules[1].on = !eg_beta_only;
  for (int i = 0; i < EG_NRULES; i++) eg_rules[i].fires = 0;
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
    for (int r = 0; r < EG_NRULES; r++)
      fprintf(stderr, " %s=%s/%ld", eg_rules[r].name, eg_rules[r].on ? "on" : "off", eg_rules[r].fires);
    fprintf(stderr, "\n");
  }
  free(g.nodes); free(g.classes); free(g.node_cls); free(g.slot); free(g.uses);
  return res ? res : term_copy(t);
}

/* ---------------- .line Binary Container ---------------- */
/* Serializes/deserializes a reduced Net to a self-running .line executable (shebang re-invokes the producing engine) */
static char self_path[4096] = "lin";

void lin_set_self_path(const char *p) {
  if (!p || !*p) return;
  char *rp = realpath(p, NULL);
  snprintf(self_path, sizeof self_path, "%s", rp ? rp : p);
  free(rp);
}

int net_save_line(Net *n, const char *path) {
  FILE *f = fopen(path, "wb"); if (!f) return 0;
  fprintf(f, "#!%s\n", self_path); fwrite("LINE", 1, 4, f);
  uint32_t nnamed = 0; for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) nnamed++;
  uint32_t meta[4] = { 3, (uint32_t)n->nn, (uint32_t)n->nlv, nnamed };
  fwrite(meta, sizeof(uint32_t), 4, f);
  fwrite(n->tag, 1, (size_t)n->nn, f); fwrite(n->dead, 1, (size_t)n->nn, f);
  fwrite(n->wire, sizeof(Port) * 3, (size_t)n->nn, f);
  fwrite(n->scope, sizeof(Scope), (size_t)n->nn, f);
  for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) {
    uint32_t id = i; uint8_t len = (uint8_t)strlen(n->name[i]);
    fwrite(&id, 4, 1, f); fwrite(&len, 1, 1, f); fwrite(n->name[i], 1, len, f);
  }
  /* the level trie: parents come before children by construction, so ids reload directly */
  if (n->nlv > 0) { fwrite(n->lv_parent + 1, sizeof(int), (size_t)n->nlv, f);
                    fwrite(n->lv_bit + 1, 1, (size_t)n->nlv, f); }
  fclose(f); chmod(path, 0755); return 1;
}

int net_load_line(Net *n, const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) return 0;
  char buf[64];
  if (fgets(buf, sizeof buf, f) && buf[0] == '#' && buf[1] == '!') {} else fseek(f, 0, SEEK_SET);
  char magic[4]; uint32_t meta[4];
  if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "LINE", 4) || fread(meta, 4, 4, f) != 4 || meta[0] != 3) {
    fclose(f); return 0;
  }
  int nn = (int)meta[1], nlv = (int)meta[2]; uint32_t nnamed = meta[3];
  net_init(n, nn + 16); n->nn = nn;

  if (fread(n->tag, 1, (size_t)nn, f) != (size_t)nn || fread(n->dead, 1, (size_t)nn, f) != (size_t)nn ||
      fread(n->wire, sizeof(Port) * 3, (size_t)nn, f) != (size_t)nn ||
      fread(n->scope, sizeof(Scope), (size_t)nn, f) != (size_t)nn) { fclose(f); net_free(n); return 0; }
  for (uint32_t k = 0; k < nnamed; k++) {
    uint32_t id = 0; uint8_t len = 0;
    if (fread(&id, 4, 1, f) != 1 || fread(&len, 1, 1, f) != 1) { fclose(f); net_free(n); return 0; }
    n->name[id] = malloc((size_t)len + 1);
    if (fread(n->name[id], 1, len, f) != len) { fclose(f); net_free(n); return 0; }
    n->name[id][len] = 0;
  }
  if (nlv > 0) {
    int *par = malloc((size_t)nlv * sizeof(int));
    unsigned char *bit = malloc((size_t)nlv);
    if (!par || !bit || fread(par, sizeof(int), (size_t)nlv, f) != (size_t)nlv ||
        fread(bit, 1, (size_t)nlv, f) != (size_t)nlv) { free(par); free(bit); fclose(f); net_free(n); return 0; }
    net_level_set(n, nlv, par, bit);
    free(par); free(bit);
  }
  fclose(f);
  /* seed the self-collecting activation queue: the active-redex list is not serialized, so a freshly loaded net has an empty queue; reconstruct all live principal pairs (including ROOT) so it actually reduces */
  for (int i = 0; i < n->nn; i++)
    if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
      lin_enqueue(n, (Port){i, 0}, n->wire[i * 3]);
  return 1;
}