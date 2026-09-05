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

static Port ct(Term *t, Scope sc) {
  switch (t->type) {
  case TVAR: {
    for (int i = csp - 1; i >= 0; i--) {
      if (strcmp(cstack[i].name, t->name)) continue;
      CVar *e = &cstack[i];
      e->count++;
      if (e->count == 1) return e->bind;
      Port ph = net_alloc(N, ERA, sc, "");
      add_extra(e, (Port){ph.node, 1});
      return (Port){ph.node, 1};
    }
    cfail("unbound variable '%s'", t->name);
  }
  case TLAM: {
    Port self = net_alloc(N, LAM, sc, t->name);
    push_var(t->name, (Port){self.node, 1});
    int my = csp - 1;
    Port body = ct(t->l, sc);
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
      Port root = dup_tree(ts, e->count, sc);
      net_link(N, (Port){self.node, 1}, root, 0);
      free(ts);
    }
    free(e->extra);
    csp--;
    return self;
  }
  case TAPP: {
    Port a = net_alloc(N, APP, sc, "");
    net_link(N, (Port){a.node, 0}, ct(t->l, sc), 1);
    net_link(N, (Port){a.node, 2}, ct(t->r, sc), 1);
    return (Port){a.node, 1};
  }
  case TDEF: return ct(t->l, sc);
  }
  return (Port){-1, 0};
}

int compile(Term *t, Net *n, char *err, int errsz) {
  N = n; csp = 0;
  if (!cstack) { ccsp = 64; cstack = malloc((size_t)ccsp * sizeof(CVar)); }
  if (setjmp(CJ)) {
    snprintf(err, errsz, "%s", CMSG);
    return 0;
  }
  Port r = ct(t, scope_nil());
  net_link(N, (Port){0, 0}, r, 0);
  return 1;
}

/* ---------------- E-Graph AOT Optimizer ---------------- */
typedef struct { int type; char name[NAME]; int l, r; } ENode;
typedef struct { int parent, best_node, cost; } EClass;
typedef struct {
  ENode *nodes; int nn, ncap;
  EClass *classes; int nc, ccap;
  int *node_cls;
} EGraph;

static int eg_find(EGraph *g, int c) {
  while (g->classes[c].parent != c) { g->classes[c].parent = g->classes[g->classes[c].parent].parent; c = g->classes[c].parent; }
  return c;
}

static void eg_union(EGraph *g, int c1, int c2) {
  c1 = eg_find(g, c1); c2 = eg_find(g, c2); if (c1 == c2) return;
  if (g->classes[c1].cost <= g->classes[c2].cost) g->classes[c2].parent = c1; else g->classes[c1].parent = c2;
}

static int eg_cost(EGraph *g, ENode *n) {
  if (n->type == TVAR) return 1;
  if (n->type == TLAM) return 2 + g->classes[eg_find(g, n->l)].cost;
  return 3 + g->classes[eg_find(g, n->l)].cost + g->classes[eg_find(g, n->r)].cost;
}

static int eg_add(EGraph *g, int type, const char *name, int l, int r) {
  if (l >= 0) l = eg_find(g, l);
  if (r >= 0) r = eg_find(g, r);
  for (int i = 0; i < g->nn; i++)
    if (g->nodes[i].type == type && g->nodes[i].l == l && g->nodes[i].r == r && !strcmp(g->nodes[i].name, name ? name : ""))
      return eg_find(g, g->node_cls[i]);
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
  return cid;
}

static int eg_add_term(EGraph *g, Term *t) {
  if (!t) return -1;
  if (t->type == TVAR) return eg_add(g, TVAR, t->name, -1, -1);
  if (t->type == TLAM) return eg_add(g, TLAM, t->name, eg_add_term(g, t->l), -1);
  if (t->type == TAPP) return eg_add(g, TAPP, "", eg_add_term(g, t->l), eg_add_term(g, t->r));
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
  for (int round = 0; round < 6; round++) {
    int start_n = g->nn;
    for (int i = 0; i < start_n && g->nn < 32768; i++) {
      ENode n = g->nodes[i]; int cls = eg_find(g, g->node_cls[i]);
      if (n.type == TAPP) {
        int fn_cls = eg_find(g, n.l);
        for (int j = 0; j < start_n; j++)
          if (eg_find(g, g->node_cls[j]) == fn_cls && g->nodes[j].type == TLAM) {
            char vn[NAME]; snprintf(vn, NAME, "%s", g->nodes[j].name);
            eg_union(g, cls, eg_subst(g, g->nodes[j].l, vn, n.r, 0));
          }
      } else if (n.type == TLAM) {
        int body_cls = eg_find(g, n.l);
        for (int j = 0; j < start_n; j++) {
          if (eg_find(g, g->node_cls[j]) == body_cls && g->nodes[j].type == TAPP) {
            ENode an = g->nodes[g->classes[eg_find(g, g->nodes[j].r)].best_node];
            if (an.type == TVAR && !strcmp(an.name, n.name) && !eg_has_var(g, g->nodes[j].l, n.name))
              eg_union(g, cls, g->nodes[j].l);
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
  EGraph g = {0}; int root = eg_add_term(&g, t); eg_saturate(&g);
  Term *res = eg_extract(&g, root, 0);
  free(g.nodes); free(g.classes); free(g.node_cls); return res ? res : term_copy(t);
}

/* ---------------- .line Binary Container ---------------- */
int net_save_line(Net *n, const char *path) {
  FILE *f = fopen(path, "wb"); if (!f) return 0;
  fputs("#!/usr/bin/env lin\n", f); fwrite("LINE", 1, 4, f);
  uint32_t nnamed = 0; for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) nnamed++;
  uint32_t meta[4] = { 2, (uint32_t)n->nn, (uint32_t)n->scn, nnamed };
  fwrite(meta, sizeof(uint32_t), 4, f);
  fwrite(n->tag, 1, (size_t)n->nn, f); fwrite(n->dead, 1, (size_t)n->nn, f);
  fwrite(n->wire, sizeof(Port) * 3, (size_t)n->nn, f); fwrite(n->scope, sizeof(Scope), (size_t)n->nn, f);
  for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) {
    uint32_t id = i; uint8_t len = (uint8_t)strlen(n->name[i]);
    fwrite(&id, 4, 1, f); fwrite(&len, 1, 1, f); fwrite(n->name[i], 1, len, f);
  }
  if (n->scn > 0) fwrite(n->sca, sizeof(uint64_t), (size_t)n->scn, f);
  fclose(f); chmod(path, 0755); return 1;
}

int net_load_line(Net *n, const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) return 0;
  char buf[64];
  if (fgets(buf, sizeof buf, f) && buf[0] == '#' && buf[1] == '!') {} else fseek(f, 0, SEEK_SET);
  char magic[4]; uint32_t meta[4];
  if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "LINE", 4) || fread(meta, 4, 4, f) != 4 || meta[0] != 2) {
    fclose(f); return 0;
  }
  int nn = (int)meta[1], scn = (int)meta[2]; uint32_t nnamed = meta[3];
  net_init(n, nn + 16); n->nn = nn; n->scn = scn;
  if (scn > 0) { n->sccap = scn + 16; n->sca = realloc(n->sca, (size_t)n->sccap * sizeof(uint64_t)); }
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
  if (scn > 0 && fread(n->sca, sizeof(uint64_t), (size_t)scn, f) != (size_t)scn) { fclose(f); net_free(n); return 0; }
  fclose(f); return 1;
}