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

#include "runtime_egraph.inc"

/* ---------------- .line Binary Container (lives in std; see std/runtime/line.c) ---------------- */
#include "runtime_line.inc"