#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

enum { TVR, TARROW, TLINK, TLIST };

static jmp_buf TJ;
static char TMSG[256];
static int next_id;

static void tfail(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(TMSG, sizeof TMSG, fmt, ap);
  va_end(ap);
  longjmp(TJ, 1);
}

static Type *tvar(void) {
  Type *t = malloc(sizeof *t); *t = (Type){.kind = TVR, .id = next_id++}; return t;
}
static Type *tarrow(Type *a, Type *b) {
  Type *t = malloc(sizeof *t); *t = (Type){.kind = TARROW, .id = -1, .a = a, .b = b}; return t;
}
static Type *tlist(Type *e) {
  Type *t = malloc(sizeof *t); *t = (Type){.kind = TLIST, .id = -1, .a = e}; return t;
}

static Type *find(Type *t) {
  while (t->kind == TLINK) {
    if (t->a->kind == TLINK) t->a = t->a->a;
    t = t->a;
  }
  return t;
}

static int occurs(Type *v, Type *t) {
  t = find(t);
  if (t == v) return 1;
  if (t->kind == TARROW) return occurs(v, t->a) || occurs(v, t->b);
  if (t->kind == TLIST) return occurs(v, t->a);
  return 0;
}

static void unify(Type *x, Type *y) {
  x = find(x);
  y = find(y);
  if (x == y) return;
  if (x->kind == TARROW && y->kind == TARROW) { unify(x->a, y->a); unify(x->b, y->b); return; }
  if (x->kind == TLIST && y->kind == TLIST) { unify(x->a, y->a); return; }
  if (x->kind == TVR) { if (occurs(x, y)) tfail("infinite type"); x->kind = TLINK; x->a = y; return; }
  if (y->kind == TVR) { if (occurs(y, x)) tfail("infinite type"); y->kind = TLINK; y->a = x; return; }
  tfail("type mismatch");
}

typedef struct { char name[NAME]; Scheme s; } TEnv;
static TEnv *env;
static int envn, envcap;

static void env_push(const char *name, Scheme s) {
  if (envn >= envcap)
    env = realloc(env, (size_t)(envcap = envcap ? envcap * 2 : 128) * sizeof(TEnv));
  snprintf(env[envn].name, NAME, "%s", name);
  env[envn++].s = s;
}

static Scheme *env_find(const char *name) {
  for (int i = envn - 1; i >= 0; i--)
    if (!strcmp(env[i].name, name)) return &env[i].s;
  return NULL;
}

static void fv(Type *t, int *set, int *n) {
  t = find(t);
  if (t->kind == TVR) {
    for (int i = 0; i < *n; i++)
      if (set[i] == t->id) return;
    if (*n < 256) set[(*n)++] = t->id;
    return;
  }
  if (t->kind == TARROW) {
    fv(t->a, set, n);
    fv(t->b, set, n);
  }
  if (t->kind == TLIST) fv(t->a, set, n);
}

static int mid[256];
static Type *mty[256];
static int mn;

static Type *inst_rec(Type *t) {
  t = find(t);
  if (t->kind == TVR) {
    for (int i = 0; i < mn; i++)
      if (mid[i] == t->id) return mty[i];
    return t;
  }
  if (t->kind == TARROW) return tarrow(inst_rec(t->a), inst_rec(t->b));
  if (t->kind == TLIST) return tlist(inst_rec(t->a));
  return t;
}

static Type *instantiate(Scheme *s) {
  mn = 0;
  for (int i = 0; i < s->nq; i++) {
    mid[mn] = s->q[i];
    mty[mn] = tvar();
    mn++;
  }
  return inst_rec(s->t);
}

static Scheme generalize(Type *t) {
  int f[256], fn = 0;
  fv(t, f, &fn);
  for (int i = 0; i < envn; i++) {
    int g[256], gn = 0;
    fv(env[i].s.t, g, &gn);
    for (int j = 0; j < fn; j++) {
      int hit = 0;
      for (int k = 0; k < gn; k++)
        if (f[j] == g[k]) { hit = 1; break; }
      if (hit) {
        f[j] = f[--fn];
        j--;
      }
    }
  }
  Scheme s;
  s.nq = fn;
  memcpy(s.q, f, (size_t)fn * sizeof(int));
  s.t = t;
  return s;
}

static Type *infer(Term *t) {
  switch (t->type) {
  case TVAR: {
    Scheme *s = env_find(t->name);
    if (!s) tfail("unbound variable '%s'", t->name);
    return instantiate(s);
  }
  case TLAM: {
    Type *a = tvar();
    Scheme s;
    s.nq = 0;
    s.t = a;
    env_push(t->name, s);
    Type *b = infer(t->l);
    envn--;
    return tarrow(a, b);
  }
  case TAPP: {
    if (t->l && t->l->type == TLAM) {
      Type *v = infer(t->r);
      env_push(t->l->name, generalize(v));
      Type *b = infer(t->l->l);
      envn--;
      return b;
    }
    Type *f = infer(t->l);
    Type *x = infer(t->r);
    Type *r = tvar();
    unify(f, tarrow(x, r));
    return r;
  }
  case TDEFX: return infer(t->l);
  }
  return NULL;
}

static void env_load_defs(void) {
  envn = 0;
  for (int i = 0; i < ndefs; i++)
    if (defs[i].typed) env_push(defs[i].name, defs[i].sch);
}

int type_check(Term *t, Scheme *out, char *err, int errsz) {
  if (setjmp(TJ)) {
    snprintf(err, errsz, "%s", TMSG);
    return 0;
  }
  env_load_defs();
  *out = generalize(infer(t));
  return 1;
}

int type_check_rec(const char *name, Term *body, Scheme *out, char *err,
                   int errsz) {
  if (setjmp(TJ)) {
    snprintf(err, errsz, "%s", TMSG);
    return 0;
  }
  env_load_defs();
  Type *a = tvar();
  Scheme s;
  s.nq = 0;
  s.t = a;
  env_push(name, s);
  unify(a, infer(body));
  envn--;
  *out = generalize(a);
  return 1;
}

static void print_rec(Type *t, int par) {
  t = find(t);
  if (t->kind == TVR) {
    if (t->id < 26) putchar('a' + t->id);
    else printf("t%d", t->id);
    return;
  }
  if (t->kind == TARROW) {
    if (par) putchar('(');
    print_rec(t->a, 1);
    printf(" -> ");
    print_rec(t->b, 0);
    if (par) putchar(')');
    return;
  }
  if (t->kind == TLIST) {
    printf("list ");
    print_rec(t->a, 1);
    return;
  }
  putchar('?');
}

void scheme_print(Scheme *s) { print_rec(s->t, 0); }

Type *type_var(void) { return tvar(); }
Type *type_arrow(Type *a, Type *b) { return tarrow(a, b); }
Type *type_list(Type *e) { return tlist(e); }

Scheme scheme_all(Type *t) {
  int f[64], fn = 0;
  fv(t, f, &fn);
  Scheme s;
  s.nq = fn;
  memcpy(s.q, f, fn * sizeof(int));
  s.t = t;
  return s;
}
