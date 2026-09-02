#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#define MAXU 128

typedef struct {
  char name[NAME];
  Port bind;
  int count;
  int extra[MAXU];
  int nextra;
} CVar;

static CVar cstack[256];
static int csp;
static Net *N;
static jmp_buf CJ;
static char CMSG[256];

_Noreturn static void cfail(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(CMSG, sizeof CMSG, fmt, ap);
  va_end(ap);
  longjmp(CJ, 1);
}

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

static Port ct(Term *t, Scope sc, int depth) {
  switch (t->type) {
  case TVAR: {
    for (int i = csp - 1; i >= 0; i--) {
      if (strcmp(cstack[i].name, t->name)) continue;
      CVar *e = &cstack[i];
      e->count++;
      if (e->count == 1) return e->bind;
      if (e->nextra >= MAXU)
        cfail("variable '%s' used too many times", t->name);
      Port ph = net_alloc(N, ERA, sc, "");
      e->extra[e->nextra++] = ph.node;
      return (Port){ph.node, 1};
    }
    cfail("unbound variable '%s'", t->name);
  }
  case TLAM: {
    Port self = net_alloc(N, LAM, sc, t->name);
    if (csp >= 256) cfail("lambda nesting too deep");
    CVar *e = &cstack[csp++];
    snprintf(e->name, NAME, "%s", t->name);
    e->bind = (Port){self.node, 1};
    e->count = 0;
    e->nextra = 0;
    Port body = ct(t->l, sc, depth + 1);
    net_link(N, (Port){self.node, 2}, body, 0);
    if (e->count == 0) {
      Port er = net_alloc(N, ERA, sc, "");
      net_link(N, (Port){self.node, 1}, er, 0);
    } else if (e->count > 1) {
      Port ts[MAXU + 1];
      ts[0] = N->wire[self.node * 3 + 1];
      for (int i = 0; i < e->nextra; i++)
        ts[i + 1] = N->wire[e->extra[i] * 3 + 1];
      Port root = dup_tree(ts, e->count, sc);
      net_link(N, (Port){self.node, 1}, root, 0);
    }
    csp--;
    return self;
  }
  case TAPP: {
    Port a = net_alloc(N, APP, sc, "");
    Port f = ct(t->l, sc, depth);
    net_link(N,(Port){a.node, 0}, f, 1);
    Port g = ct(t->r, sc, depth);
    net_link(N,(Port){a.node,2}, g, 1);
    return (Port){a.node, 1};
  }
  case TNUM: {
    long k = atol(t->name);
    if (k > 5000) cfail("numeral too large (max 5000)");
    Port cf = net_alloc(N, LAM, sc, "_cf");
    Port cx = net_alloc(N, LAM, sc, "_cx");
    net_link(N, (Port){cf.node, 2}, (Port){cx.node, 0}, 0);
    if (k == 0) {
      net_link(N, (Port){cx.node, 2}, (Port){cx.node, 1}, 0);
    } else {
      Port *ts = malloc(sizeof(Port) * k);
      Port val = (Port){cx.node, 1};
      for (long i = 0; i < k; i++) {
        Port ap = net_alloc(N, APP, sc, "");
        ts[i] = (Port){ap.node, 0};
        net_link(N, (Port){ap.node, 2}, val, 0);
        val = (Port){ap.node, 1};
      }
      net_link(N, (Port){cx.node, 2}, val, 0);
      Port root = dup_tree(ts, (int)k, sc);
      free(ts);
      net_link(N, (Port){cf.node, 1}, root, 0);
    }
    return cf;
  }
  case TLET: {
    Term lam, app;
    memset(&lam, 0, sizeof lam);
    memset(&app, 0, sizeof app);
    lam.type = TLAM;
    snprintf(lam.name, NAME, "%s", t->name);
    lam.l = t->r;
    app.type = TAPP;
    app.l = &lam;
    app.r = t->l;
    return ct(&app, sc, depth);
  }
  case TDEF: return ct(t->l, sc, depth);
  }
  return (Port){-1, -1};
}

int compile(Term *t, Net *n, char *err, int errsz) {
  N = n;
  csp = 0;
  if (setjmp(CJ)) {
    snprintf(err, errsz, "%s", CMSG);
    return 0;
  }
  Port r = ct(t, scope_nil(), 0);
  net_link(N, (Port){0, 0}, r, 0);
  return 1;
}
