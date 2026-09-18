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
static uint64_t *cpath; static int cpath_len, cpath_cap;
static void cpath_push(uint64_t b) {
  if (cpath_len >= cpath_cap) {
    cpath_cap = cpath_cap ? cpath_cap * 2 : 1024;
    cpath = realloc(cpath, sizeof(uint64_t) * (size_t)cpath_cap);
  }
  cpath[cpath_len++] = b;
}
/* the sharing point at the current position; `bit` steps one level in first (a binder's fan
   sits just inside its binder, so it is gauged at the body's path) */
static Scope fan_lvl(void) { return scope_from_bits(N, cpath, cpath_len); }
static Scope fan_lvl_at(int bit) { cpath_push((uint64_t)(bit & 1)); Scope s = fan_lvl(); cpath_len--; return s; }

/* Rebuild a source-net scope in the target gauge table; heap-backed ones re-register bit-by-bit into N->sca. */
static Scope sc_rebuild(Net *d, int i) {
  Scope s = d->scope[i];
  if (!s.sso.is_heap) return s;
  return scope_from_bits(N, d->sca + s.heap.off, (int)s.heap.len);
}

/* Clone a pre-reduced define value (closed normal-form net) into N; cut the source ROOT<->value clamp so the clone ties only to the caller.  The clone is
   re-gauged at a fresh level: the body's fans were labelled during its own
   precompile reduction, so splicing it verbatim would give every reference's copy
   identical labels and two independent sharing points would annihilate. */
static Port ct_splice(Def *d, Scope sc) {
  (void)sc;
  Net *s = d->compiled;
  Scope lvl = fan_lvl();
  int n = s->nn, *map = malloc(sizeof(int) * (size_t)(n ? n : 1));
  for (int i = 0; i < n; i++) map[i] = net_alloc(N, s->tag[i], scope_prefix(N, lvl, sc_rebuild(s, i)), s->name[i]).node;
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
    cpath_push(1);
    Port body = ct(t->l, sc);
    cpath_len--;
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
    Port a = net_alloc(N, APP, fan_lvl(), "");
    cpath_push(1);
    Port fn = ct(t->l, sc);
    cpath_len--;
    net_link(N, (Port){a.node, 0}, fn, 1);
    cpath_push(2);
    Port x = ct(t->r, sc);
    cpath_len--;
    net_link(N, (Port){a.node, 2}, x, 1);
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
  N = n; csp = 0; cpath_len = 0;
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

Term *egraph_optimize(Term *t) {
  if (!t) return NULL;
  EGraph g = {0}; int root = eg_add_term(&g, t); eg_saturate(&g);
  Term *res = (root < 0) ? NULL : eg_extract(&g, root, 0);
  free(g.nodes); free(g.classes); free(g.node_cls); return res ? res : term_copy(t);
}

/* ---------------- .line Binary Container (lives in std; see std/runtime/line.c) ---------------- */
#include "runtime_line.inc"