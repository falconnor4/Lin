#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

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

/* nominal-type registry: a declared user data type (ADT/struct), optionally with
   a fixed number of type parameters (its arity).  parse_type_atom resolves a
   registered name to a TNOM head with arity arg chains, so two values of the
   same declared type unify (parameter-wise) and different types do not. */
typedef struct { const char *name; int arity; } NomDecl;
static NomDecl noms[512]; static int n_nom = 0;
int nominal_arity(const char *name) {
  for (int i = 0; i < n_nom; i++) if (!strcmp(noms[i].name, name)) return noms[i].arity;
  return -1;
}
int nominal_lookup(const char *name) { return nominal_arity(name) >= 0; }
int nominal_register(const char *name, int arity) {
  if (nominal_lookup(name)) return 0;
  if (n_nom < 512) { char *p = malloc(strlen(name) + 1); strcpy(p, name); noms[n_nom++] = (NomDecl){.name = p, .arity = arity}; return 1; }
  return 0;
}

static Type *tvar(void) { Type *t = malloc(sizeof *t); *t = (Type){.kind = TVR, .id = next_id++}; return t; }
static Type *tarrow(Type *a, Type *b) { Type *t = malloc(sizeof *t); *t = (Type){.kind = TARROW, .id = -1, .a = a, .b = b}; return t; }
/* type-argument chain node: {a = the arg type, b = next TARG or NULL} */
static Type *targ(Type *arg, Type *next) { Type *t = malloc(sizeof *t); *t = (Type){.kind = TARG, .id = -1, .a = arg, .b = next}; return t; }
/* nominal type: `name` copied; `*argp` is a TARG chain of arity type args (or NULL). */
static Type *tnom(const char *name, Type *args) {
  Type *t = malloc(sizeof *t); char *p = malloc(strlen(name) + 1); strcpy(p, name);
  *t = (Type){.kind = TNOM, .id = -1, .name = p, .a = args}; return t;
}
static Type *tnom0(const char *name) { return tnom(name, NULL); }
/* transient reference to a datatype's k-th type parameter (only used while
   building constructor field types; resolved to the head's param var in
   process_datatype).  `id` = parameter index. */
static Type *tparam(int idx) { Type *t = malloc(sizeof *t); *t = (Type){.kind = TPARAM, .id = idx}; return t; }

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
  if (t->kind == TNOM) return t->a && occurs(v, t->a);     /* arg chain */
  if (t->kind == TARG) return occurs(v, t->a) || (t->b && occurs(v, t->b));
  return 0;
}

static void unify(Type *x, Type *y) {
  x = find(x);
  y = find(y);
  if (x == y) return;
  if (x->kind == TARROW && y->kind == TARROW) { unify(x->a, y->a); unify(x->b, y->b); return; }
  /* nominal: equal only when both are the SAME declared type; then unify type
     arguments pairwise.  A nominal value may also be APPLIED as its
     Scott-encoded dispatch (match desugars scrut to application). */
  if (x->kind == TNOM && y->kind == TNOM) {
    if (strcmp(x->name, y->name)) tfail("type mismatch");
    for (Type *xa = x->a, *ya = y->a; xa && ya; xa = xa->b, ya = ya->b) unify(xa->a, ya->a);
    return;
  }
  if (x->kind == TNOM || y->kind == TNOM) {
    if (x->kind == TVR) { x->kind = TLINK; x->a = y; return; }
    if (y->kind == TVR) { y->kind = TLINK; y->a = x; return; }
    /* A nominal unifies with an arrow for Scott dispatch (match scrut) and
       for polymorphic values -- EXCEPT structured containers `list`/`string`,
       which must reject a raw numeral/arrow ((head 5), (cons 1 2) stay errors). */
    if (x->kind == TARROW || y->kind == TARROW) {
      Type *nom = (x->kind == TNOM) ? x : y;
      if (nom->name && (!strcmp(nom->name, "list") || !strcmp(nom->name, "string"))) tfail("type mismatch");
      return;
    }
    tfail("type mismatch");
  }
  if (x->kind == TVR) { if (occurs(x, y)) tfail("infinite type"); x->kind = TLINK; x->a = y; return; }
  if (y->kind == TVR) { if (occurs(y, x)) tfail("infinite type"); y->kind = TLINK; y->a = x; return; }
  tfail("type mismatch");
}

/* Environment entries come in two kinds, and the distinction is what makes
   generalization both order-independent and cheap:

     - a DEFINITION scheme is closed and never mutated after registration, so the
       set of type variables it contributes to the environment is fixed and is
       maintained incrementally in a refcount table (`envrc`) instead of being
       recomputed by walking every scheme on every `generalize` (that walk was
       160k entry scans / 11.9M node visits per std load -- 372 of its 421 ms);

     - a BINDER entry (`\x.` and the self-recursive `f : a` slot) holds a fresh
       variable that unification may LINK LATER, so its contribution cannot be
       cached at push time: `(\x (x 5))` pushes `a`, then `unify(a, num -> c)`
       makes `c` free in the environment through `x`.  Those are resolved when
       `generalize` runs -- O(1) while the root is still a bare variable, and a
       walk only in the rare case that it was linked. */
typedef struct { char name[NAME]; Scheme s; int isdef; } TEnv;
static TEnv *env;
static int envn, envcap;

static void env_push(const char *name, Scheme s) {
  if (envn >= envcap)
    env = realloc(env, (size_t)(envcap = envcap ? envcap * 2 : 128) * sizeof(TEnv));
  snprintf(env[envn].name, NAME, "%s", name);
  env[envn].s = s; env[envn].isdef = 0;
  envn++;
}

static Scheme *env_find(const char *name) {
  for (int i = envn - 1; i >= 0; i--) if (!strcmp(env[i].name, name)) return &env[i].s;
  Def *d = def_find(name);
  return (d && d->typed) ? &d->sch : NULL;
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
  if (t->kind == TNOM) { if (t->a) fv(t->a, set, n); }
  if (t->kind == TARG) { fv(t->a, set, n); if (t->b) fv(t->b, set, n); }
}

/* ---- environment free-variable set (see the TEnv comment): membership is a refcount
   lookup, so `generalize` never iterates the environment and its answer depends on the
   environment as a *set*, not on the order entries were pushed. ---- */
static int *envrc; static int envrc_cap;
static void rc_grow(int id) {
  if (id < envrc_cap) return;
  int nc = envrc_cap ? envrc_cap : 1024;
  while (nc <= id) nc *= 2;
  envrc = realloc(envrc, (size_t)nc * sizeof(int));
  memset(envrc + envrc_cap, 0, (size_t)(nc - envrc_cap) * sizeof(int));
  envrc_cap = nc;
}
static int rc_has(int id) { return id < envrc_cap && envrc[id] > 0; }

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
  if (t->kind == TARG) return targ(inst_rec(t->a), t->b ? inst_rec(t->b) : NULL);
  if (t->kind == TNOM) { Type *n = tnom0(t->name); Type **cur = &n->a; for (Type *k = t->a; k; k = k->b) { *cur = targ(inst_rec(k->a), NULL); cur = &(*cur)->b; } return n; }
  return t;
}

static Type *instantiate(Scheme *s) {
  mn = 0;
  for (int i = 0; i < s->nq; i++) { mid[mn] = s->q[i]; mty[mn++] = tvar(); }
  return inst_rec(s->t);
}

static Scheme generalize(Type *t) {
  int f[256], fn = 0; fv(t, f, &fn);
  /* Binder entries first: O(1) each while the pushed variable is still bare, and only
     an entry whose variable was linked needs the walk. */
  int dyn[256], dn = 0;
  for (int i = 0; i < envn; i++) {
    if (env[i].isdef) continue;
    Type *u = find(env[i].s.t);
    if (u->kind == TVR) { if (dn < 256) dyn[dn++] = u->id; }
    else fv(env[i].s.t, dyn, &dn);
  }
  int q[256], qn = 0;
  for (int j = 0; j < fn; j++) {
    if (rc_has(f[j])) continue;                       /* free in a def scheme's type */
    int hit = 0;
    for (int k = 0; k < dn; k++) if (dyn[k] == f[j]) { hit = 1; break; }
    if (!hit && qn < 256) q[qn++] = f[j];
  }
  Scheme s; s.nq = qn; memcpy(s.q, q, (size_t)qn * sizeof(int)); s.t = t; return s;
}

static Type *infer(Term *t) {
  switch (t->type) {
  case TVAR: {
    Scheme *s = env_find(t->name);
    if (!s) tfail("unbound variable '%s'", t->name);
    return instantiate(s);
  }
  case TLAM: {
    Type *a = tvar(); env_push(t->name, (Scheme){.nq = 0, .t = a});
    Type *b = infer(t->l); envn--; return tarrow(a, b);
  }
  case TAPP: {
    if (t->l && t->l->type == TLAM) {
      env_push(t->l->name, generalize(infer(t->r)));
      Type *b = infer(t->l->l); envn--; return b;
    }
    Type *f = infer(t->l), *x = infer(t->r), *r = tvar();
    unify(f, tarrow(x, r)); return r;
  }
  case TLET: {
    /* The compiler's scope rule, so the two agree: an already-bound name means the value still sees
       the OUTER binding (checked before the new one exists); a new name is in scope for its own
       value -- recursion -- checked monomorphically, which is what keeps that rule sound, and
       generalised for the body. */
    if (env_find(t->name)) {
      Type *v = infer(t->l);
      env_push(t->name, generalize(v));
      Type *b = infer(t->r);
      envn--; return b;
    }
    Type *a = tvar();
    env_push(t->name, (Scheme){.nq = 0, .t = a});
    unify(a, infer(t->l));
    envn--;
    env_push(t->name, generalize(a));
    Type *b = infer(t->r);
    envn--; return b;
  }
  case TDEFX: return infer(t->l);
  case TFLOAT: return tvar();   /* float literal: fresh polymorphic type */
  }
  return NULL;
}

/* Registering a def scheme's free variables happens ONCE PER DEF, not once per check.
   The old code walked all 319 schemes on each of the 512 checks (160k walks, 11.9M node
   visits) purely to rediscover an unchanging answer.  Loading the array itself stays
   per-call but is only a copy, so `env_find` still sees every def. */
static void env_load_defs(void) {
  static int reg_n = 0;                     /* defs whose free variables are already counted */
  for (int i = reg_n; i < ndefs; i++) {
    if (!defs[i].typed) continue;
    int f[256], n = 0; fv(defs[i].sch.t, f, &n);
    for (int j = 0; j < n; j++) { rc_grow(f[j]); envrc[f[j]]++; }
  }
  reg_n = ndefs;
  envn = 0;
  for (int i = 0; i < ndefs; i++) if (defs[i].typed) {
    env_push(defs[i].name, defs[i].sch);
    env[envn - 1].isdef = 1;                /* its contribution is already in envrc */
  }
}

int type_check(Term *t, Scheme *out, char *err, int errsz) {
  if (setjmp(TJ)) { snprintf(err, errsz, "%s", TMSG); return 0; }
  env_load_defs(); *out = generalize(infer(t)); return 1;
}

int type_check_rec(const char *name, Term *body, Scheme *out, char *err, int errsz) {
  if (setjmp(TJ)) { snprintf(err, errsz, "%s", TMSG); return 0; }
  env_load_defs(); Type *a = tvar(); env_push(name, (Scheme){.nq = 0, .t = a});
  unify(a, infer(body)); envn--; *out = generalize(a); return 1;
}

static void print_rec(Type *t, int par) {
  t = find(t);
  if (t->kind == TVR) {
    if (t->id < 26) putchar('a' + t->id); else printf("t%d", t->id);
    return;
  }
  if (t->kind == TARROW) {
    if (par) putchar('(');
    print_rec(t->a, 1); printf(" -> "); print_rec(t->b, 0);
    if (par) putchar(')');
    return;
  }
  if (t->kind == TNOM) { fputs(t->name ? t->name : "?", stdout); for (Type *k = t->a; k; k = k->b) { putchar(' '); print_rec(k->a, 2); } return; }
  if (t->kind == TARG) { print_rec(t->a, 2); return; }
  putchar('?');
}

void scheme_print(Scheme *s) { print_rec(s->t, 0); }
Type *type_var(void) { return tvar(); }
Type *type_arrow(Type *a, Type *b) { return tarrow(a, b); }
Type *type_nominal(const char *name) { return tnom0(name); }
Type *type_arg(Type *arg) { return targ(arg, NULL); }
Type *type_param(int idx) { return tparam(idx); }

Scheme scheme_all(Type *t) {
  int f[64], fn = 0; fv(t, f, &fn);
  Scheme s; s.nq = fn; memcpy(s.q, f, (size_t)fn * sizeof(int)); s.t = t; return s;
}
