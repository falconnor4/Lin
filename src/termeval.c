#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Call-by-need normal-order evaluator used as the semantic readback fallback.
   The interaction net reduces optimally and reads back most values directly,
   but some (comparisons, recursion) land in irreducible croissant normal forms
   that the passive readback cannot decode.  For those we evaluate the expanded
   program with a lazy, memoized machine: shared thunks are forced at most once,
   so Church-numeral arithmetic terminates without exponential blowup. */

/* ---------------- arena ---------------- */
typedef struct Blk { struct Blk *next; size_t n; char *p; } Blk;
static Blk *ablks;
static void *xa(size_t n) {
  size_t room = ablks ? (char *)ablks + ablks->n - ablks->p : 0;
  size_t need = (n + 15) & ~(size_t)15;
  if (room < need) {
    size_t cap = need > (1 << 16) ? need : (1 << 16);
    Blk *b = malloc(sizeof *b + cap);
    b->next = ablks;
    b->n = cap;
    ablks = b;
    ablks->p = (char *)(ablks + 1);
  }
  void *r = ablks->p;
  ablks->p += need;
  return r;
}
static void arena_reset(void) {
  Blk *b = ablks;
  while (b) {
    Blk *n = b->next;
    free(b);
    b = n;
  }
  ablks = NULL;
}

/* ---------------- values ---------------- */
typedef struct T T;
typedef struct V V;

struct T {             /* possibly-unevaluated term under an environment */
  Term *e;
  V *env;
  V *memo;             /* result once forced */
};

struct V {
  int kind;            /* 0 bind cell, 1 lambda, 2 stuck app, 3 free var,
                          4 counting chain cell */
  V *env;              /* closure env for kind 1 */
  union {
    Term *t;           /* kind 1: the lambda node */
    struct {
      V *f;
      T *a;
    } ap;              /* kind 2 */
    struct {
      char name[NAME];
      T *val;
      V *up;
    } env;             /* kind 0 bind; kind 3 free var */
    V *next;           /* kind 4 */
  } u;
};

static T *mkth(Term *e, V *env) {
  T *t = xa(sizeof(T));
  t->e = e;
  t->env = env;
  t->memo = NULL;
  return t;
}

static V *mklam(Term *t, V *env) {
  V *v = xa(sizeof(V));
  v->kind = 1;
  v->env = env;
  v->u.t = t;
  return v;
}

static V *mkbind(const char *name, T *val, V *up) {
  V *v = xa(sizeof(V));
  v->kind = 0;
  snprintf(v->u.env.name, NAME, "%s", name);
  v->u.env.val = val;
  v->u.env.up = up;
  return v;
}

static V *mkapp(V *f, T *a) {
  V *v = xa(sizeof(V));
  v->kind = 2;
  v->u.ap.f = f;
  v->u.ap.a = a;
  return v;
}

static V *mktok(const char *name) {
  V *v = xa(sizeof(V));
  v->kind = 3;
  snprintf(v->u.env.name, NAME, "%s", name);
  return v;
}

static V *mkchain(V *next) {
  V *v = xa(sizeof(V));
  v->kind = 4;
  v->u.next = next;
  return v;
}

/* a thunk that already holds its forced value */
static T *mkvalthunk(V *val) {
  T *t = xa(sizeof(T));
  t->e = NULL;
  t->env = NULL;
  t->memo = val;
  return t;
}

static V *force(T *);

static V *envget(V *env, const char *name) {
  for (V *e = env; e; e = e->u.env.up) {
    if (!strcmp(e->u.env.name, name)) return force(e->u.env.val);
  }
  if (getenv("LIN_TRACE"))
    fprintf(stderr, "EVAL unbound var '%s'\n", name);
  return mktok(name);
}

static Term *mknumeral(long k, const char *f, const char *x) {
  Term *cxv = term_new(TVAR, x, NULL, NULL);
  Term *cur = cxv;
  for (long i = 0; i < k; i++)
    cur = term_new(TAPP, "", term_new(TVAR, f, NULL, NULL), cur);
  return term_new(TLAM, f, term_new(TLAM, x, cur, NULL), NULL);
}

static V *force(T *t) {
  if (t->memo) return t->memo;
  Term *e = t->e;
  V *env = t->env;
  V *r = NULL;
  switch (e->type) {
  case TVAR:
    r = envget(env, e->name);
    break;
  case TLAM:
    r = mklam(e, env);
    break;
  case TAPP: {
    V *f = force(mkth(e->l, env));
    T *arg = mkth(e->r, env);
    if (f->kind == 1) {
      Term *lam = f->u.t;
      V *nenv = mkbind(lam->name, arg, f->env);
      r = force(mkth(lam->l, nenv));
    } else if (f->kind == 4) {
      r = mkchain(force(arg));
    } else {
      r = mkapp(f, arg);
    }
    break;
  }
  case TNUM:
    r = mklam(mknumeral(atol(e->name), "_cf", "_cx"), env);
    break;
  default:
    r = mklam(e, env);
  }
  t->memo = r;
  return r;
}

/* ---------------- printing & detection ---------------- */
static void print_val(FILE *o, V *v, int depth);

/* count f-applications on the spine of a numeral lambda node */
static long spine_count(Term *t, const char *f, const char *x) {
  long k = 0;
  Term *cur = t;
  while (cur) {
    if (cur->type == TVAR) return !strcmp(cur->name, x) ? k : -1;
    if (cur->type != TAPP || !cur->l || !cur->r) return -1;
    Term *fun = cur->l;
    if (fun->type != TVAR || strcmp(fun->name, f)) return -1;
    k++;
    if (k > 10000000) return -1;
    cur = cur->r;
  }
  return -1;
}

/* a `_cf` lambda that is a numeral (possibly a numeral applied as function) */
static int is_numeral(V *v) {
  if (v->kind != 1 || !v->u.t || strcmp(v->u.t->name, "_cf")) return 0;
  Term *cx = v->u.t->l;
  return cx && cx->type == TLAM && !strcmp(cx->name, "_cx");
}

/* apply a numeral VALUE to a chain-making f and zero x, counting the result.
   This computes the number even when the value is a closure whose body was
   produced by arithmetic, not a literal term spine. */
static long num_count(V *v) {
  if (v->kind != 1 || !v->u.t || strcmp(v->u.t->name, "_cf")) return -1;
  Term *cx = v->u.t->l;
  if (!cx || cx->type != TLAM || strcmp(cx->name, "_cx")) return -1;
  V *fcnt = mkchain(NULL);                       /* marker f: wrap in a chain */
  V *zero = mkchain(NULL);                       /* marker x: chain end */
  V *ef = mkbind("_cf", mkvalthunk(fcnt), v->env);
  V *ex = mkbind("_cx", mkvalthunk(zero), ef);
  V *res = force(mkth(cx->l, ex));
  long k = 0;
  V *cur = res;
  while (cur && cur->kind == 4) {
    if (!cur->u.next) return k;
    k++;
    if (k > 10000000) return -1;
    cur = cur->u.next;
  }
  return -1;
}

static int is_boolean(V *v) {
  if (v->kind != 1 || !v->u.t || strcmp(v->u.t->name, "_bt")) return -1;
  Term *bf = v->u.t->l;
  if (!bf || bf->type != TLAM || strcmp(bf->name, "_bf")) return -1;
  Term *b = bf->l;
  if (b && b->type == TVAR && !strcmp(b->name, "_bt")) return 1;
  if (b && b->type == TVAR && !strcmp(b->name, "_bf")) return 0;
  return -1;
}

static void print_val(FILE *o, V *v, int depth) {
  if (depth > 100000 || !v) {
    fputs("?", o);
    return;
  }
  if (v->kind == 1) {
    Term *t = v->u.t;
    long k = -1;
    if (t && is_numeral(v)) k = num_count(v);
    if (k < 0 && t && is_numeral(v)) k = spine_count(t->l->l, "_cf", "_cx");
    if (k >= 0) {
      fprintf(o, "%ld", k);
      return;
    }
    int b = is_boolean(v);
    if (b >= 0) {
      fputs(b ? "true" : "false", o);
      return;
    }
    if (t) {
      fprintf(o, "(\\%s ", t->name);
      if (t->l) print_val(o, mklam(t->l, v->env), depth + 1);
      else fputs("?", o);
      fputs(")", o);
    } else {
      fputs("?", o);
    }
    return;
  }
  if (v->kind == 2) {             /* stuck application */
    T *a = v->u.ap.a;
    V *av = a->memo ? a->memo : force(a);
    /* a partially applied numeral prints structurally as (f x) */
    fputs("(", o);
    print_val(o, v->u.ap.f, depth + 1);
    fputs(" ", o);
    print_val(o, av, depth + 1);
    fputs(")", o);
    return;
  }
  if (v->kind == 3) {
    fputs(v->u.env.name, o);
    return;
  }
  fputs("?", o);
}

/* value of the expanded term.  Caller frees the returned string. */
char *term_eval_string(Term *t) {
  arena_reset();
  T *top = mkth(t, NULL);
  V *v = force(top);
  FILE *tmp = tmpfile();
  if (!tmp) {
    arena_reset();
    char *q = malloc(2);
    q[0] = '?';
    q[1] = 0;
    return q;
  }
  print_val(tmp, v, 0);
  long sz = (long)ftell(tmp);
  char *out = malloc(sz + 2);
  rewind(tmp);
  size_t rd = fread(out, 1, sz, tmp);
  (void)rd;
  out[sz] = 0;
  fclose(tmp);
  arena_reset();
  return out;
}