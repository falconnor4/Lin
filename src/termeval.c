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

static Term *mknumeral(long k, const char *f, const char *x) {
  Term *cxv = term_new(TVAR, x, NULL, NULL);
  Term *cur = cxv;
  for (long i = 0; i < k; i++)
    cur = term_new(TAPP, "", term_new(TVAR, f, NULL, NULL), cur);
  return term_new(TLAM, f, term_new(TLAM, x, cur, NULL), NULL);
}

/* Call-by-need force implemented on an explicit frame stack so that deeply
   nested application spines (e.g. a Church numeral of size N) do not
   overflow the C stack.  Frame kinds: APP = apply inner thunk to the value
   once obtained; WRAP = wrap the value in a counting chain cell. */
static V *force(T *t0) {
  enum { FRAME_APP, FRAME_WRAP };
  int cap = 4096, sp = 0;
  unsigned char *kinds = malloc(cap);
  T **fargs = malloc(sizeof(T *) * cap);
  if (!kinds || !fargs) { free(kinds); free(fargs); return mktok("?"); }
#define FGROW()                                                              \
  do {                                                                       \
    if (sp >= cap - 1) {                                                     \
      cap *= 2;                                                              \
      kinds = realloc(kinds, cap);                                           \
      fargs = realloc(fargs, sizeof(T *) * cap);                             \
    }                                                                        \
  } while (0)
  T *t = t0;
  V *val = NULL;
  for (;;) {
    /* phase 1: descend to a memoised value */
    while (t && !t->memo) {
      Term *e = t->e;
      V *env = t->env;
      if (e->type == TAPP) {
        FGROW();
        kinds[sp] = FRAME_APP;
        fargs[sp] = mkth(e->r, env);
        sp++;
        t = mkth(e->l, env);
        continue;
      }
      if (e->type == TLET) {
        Term *lam = term_new(TLAM, e->name, e->r, NULL);
        T *lt = mkth(lam, env);
        lt->memo = mklam(lam, env);
        FGROW();
        kinds[sp] = FRAME_APP;
        fargs[sp] = mkth(e->l, env);
        sp++;
        t = lt;
        continue;
      }
      V *rv;
      if (e->type == TVAR) {
        V *b = NULL;
        for (V *en = env; en; en = en->u.env.up)
          if (!strcmp(en->u.env.name, e->name)) { b = en; break; }
        if (!b) {
          if (getenv("LIN_TRACE"))
            fprintf(stderr, "EVAL unbound var '%s'\n", e->name);
          rv = mktok(e->name);
          t->memo = rv;
          val = rv;
          t = NULL;
          break;
        }
        if (b->u.env.val->memo) {
          rv = b->u.env.val->memo;
          t->memo = rv;
          val = rv;
          t = NULL;
          break;
        }
        t = b->u.env.val; /* descend into the bound thunk (no recursion) */
        continue;
      }
      else if (e->type == TLAM) rv = mklam(e, env);
      else if (e->type == TNUM) rv = mklam(mknumeral(atol(e->name), "_cf", "_cx"), env);
      else rv = mklam(e, env);
      t->memo = rv;
      val = rv;
      t = NULL;
      break;
    }
    if (t && t->memo) { val = t->memo; t = NULL; }
    else if (t) continue; /* fresh descender with no memo: loop back */
    /* phase 2: combine val with pending frames */
    while (sp > 0) {
      if (kinds[sp - 1] == FRAME_WRAP) {
        sp--;
        val = mkchain(val);
        continue;
      }
      T *arg = fargs[sp - 1];
      if (val->kind == 1) {
        Term *lam = val->u.t;
        sp--;
        t = mkth(lam->l, mkbind(lam->name, arg, val->env));
        break;
      }
      if (val->kind == 4) {
        kinds[sp - 1] = FRAME_WRAP;
        t = arg;
        break;
      }
      sp--;
      val = mkapp(val, arg);
    }
    if (sp == 0 && !t) {
      if (t0->memo == NULL) t0->memo = val ? val : mktok("?");
      free(kinds);
      free(fargs);
      return t0->memo;
    }
  }
#undef FGROW
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