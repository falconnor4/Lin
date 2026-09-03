#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

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
  if (csp >= ccsp) {
    ccsp = ccsp ? ccsp * 2 : 64;
    cstack = realloc(cstack, (size_t)ccsp * sizeof(CVar));
  }
  CVar *e = &cstack[csp++];
  snprintf(e->name, NAME, "%s", name);
  e->bind = bind;
  e->count = 0;
  e->extra = NULL;
  e->nextra = e->mextra = 0;
}

static void add_extra(CVar *e, Port p) {
  if (e->nextra >= e->mextra) {
    e->mextra = e->mextra ? e->mextra * 2 : 8;
    e->extra = realloc(e->extra, (size_t)e->mextra * sizeof(Port));
  }
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

static Port ct(Term *t, Scope sc, int depth) {
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
    if (depth > 1000000) cfail("lambda nesting too deep");
    push_var(t->name, (Port){self.node, 1});
    int my = csp - 1;
    Port body = ct(t->l, sc, depth + 1);
    net_link(N, (Port){self.node, 2}, body, 0);
    CVar *e = &cstack[my];
    if (e->count == 0) {
      /* unused binder: leave port1 dangling (erasure, as in the reference) */
    } else if (e->count > 1) {
      Port *ts = malloc(sizeof(Port) * (long)e->count);
      ts[0] = N->wire[self.node * 3 + 1];
      for (int i = 0; i < e->nextra; i++)
        ts[i + 1] = N->wire[e->extra[i].node * 3 + 1];
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
    Port f = ct(t->l, sc, depth);
    net_link(N, (Port){a.node, 0}, f, 1);
    Port g = ct(t->r, sc, depth);
    net_link(N, (Port){a.node, 2}, g, 1);
    return (Port){a.node, 1};
  }
  case TDEF: return ct(t->l, sc, depth);
  }
  return (Port){-1, -1};
}

int compile(Term *t, Net *n, char *err, int errsz) {
  N = n;
  csp = 0;
  if (cstack == NULL) {
    ccsp = 64;
    cstack = malloc((size_t)ccsp * sizeof(CVar));
  }
  if (setjmp(CJ)) {
    snprintf(err, errsz, "%s", CMSG);
    return 0;
  }
  Port r = ct(t, scope_nil(), 0);
  net_link(N, (Port){0, 0}, r, 0);
  return 1;
}