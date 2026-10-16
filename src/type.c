#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

static jmp_buf TJB; static jmp_buf *TJ = &TJB;   /* a pointer: a deferred def check runs INSIDE another check */
static char TMSG[256];
static int next_id;

static void tfail(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(TMSG, sizeof TMSG, fmt, ap);
  va_end(ap);
  longjmp(*TJ, 1);
}

/* nominal-type registry: a declared user data type (ADT/struct), optionally with a fixed number of type
   parameters (its arity).  parse_type_atom resolves a registered name to a TNOM head with arity arg
   chains, so two values of the same declared type unify (parameter-wise) and different types do not. */
typedef struct { const char *name; int arity; } NomDecl;
static NomDecl *noms; static int n_nom = 0, nom_cap = 0;
int nominal_arity(const char *name) {
  for (int i = 0; i < n_nom; i++) if (!strcmp(noms[i].name, name)) return noms[i].arity;
  return -1;
}
int nominal_lookup(const char *name) { return nominal_arity(name) >= 0; }
int nominal_register(const char *name, int arity) {
  if (nominal_lookup(name)) return 0;
  if (n_nom == nom_cap) noms = realloc(noms, (size_t)(nom_cap = nom_cap ? nom_cap * 2 : 64) * sizeof *noms);
  char *p = malloc(strlen(name) + 1); strcpy(p, name); noms[n_nom++] = (NomDecl){.name = p, .arity = arity}; return 1;
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

/* ONLY binders live here (`\x.` and the self-recursive `f : a` slot): such an entry is a fresh variable
   unification may LINK LATER, so it cannot be cached at push time.  A def's scheme is closed, is reached
   through `def_find`'s hash, and has its free variables counted once in `envrc` (below). */
typedef struct { const char *name; Scheme s; } TEnv;
static TEnv *env;
static int envn, envcap;

static void env_push(const char *name, Scheme s) {
  if (envn >= envcap)
    env = realloc(env, (size_t)(envcap = envcap ? envcap * 2 : 128) * sizeof(TEnv));
  env[envn].name = name;
  env[envn].s = s;
  envn++;
}

static void def_type(Def *d);
static Scheme *env_find(const char *name) {
  for (int i = envn - 1; i >= 0; i--) if (!strcmp(env[i].name, name)) return &env[i].s;
  Def *d = def_find(name);
  if (d && !d->typed) def_type(d);             /* lazily: the first reference is what types a def */
  return (d && d->typed) ? &d->sch : NULL;
}

typedef struct { int *v; int n, cap; } IL;   /* growable like the refcount table above: a fixed one silently DROPS a free variable past its bound, and a dropped free variable is a wrong type -- the failure mode the datatype arity scope had */
static void il_push(IL *l, int id) { if (l->n == l->cap) l->v = realloc(l->v, (size_t)(l->cap = l->cap ? l->cap * 2 : 64) * sizeof(int)); l->v[l->n++] = id; }

static void fv(Type *t, IL *f) {
  t = find(t);
  if (t->kind == TVR) {
    for (int i = 0; i < f->n; i++)
      if (f->v[i] == t->id) return;
    il_push(f, t->id);
    return;
  }
  if (t->kind == TARROW) { fv(t->a, f); fv(t->b, f); }
  if (t->kind == TNOM) { if (t->a) fv(t->a, f); }
  if (t->kind == TARG) { fv(t->a, f); if (t->b) fv(t->b, f); }
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

static int *mid;
static Type **mty;
static int mn, mcap;

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
  mn = 0; if (s->nq > mcap) { mcap = s->nq; mid = realloc(mid, (size_t)mcap * sizeof(int)); mty = realloc(mty, (size_t)mcap * sizeof *mty); }
  for (int i = 0; i < s->nq; i++) { mid[mn] = s->q[i]; mty[mn++] = tvar(); }
  return inst_rec(s->t);
}

static Scheme generalize(Type *t) {
  IL f = {0}; fv(t, &f);
  IL dyn = {0};   /* binder entries first: O(1) each while the pushed variable is still bare, so only an entry whose variable was linked needs the walk */
  for (int i = 0; i < envn; i++) {
    Type *u = find(env[i].s.t);
    if (u->kind == TVR) il_push(&dyn, u->id);
    else fv(env[i].s.t, &dyn);
  }
  int qn = 0;
  for (int j = 0; j < f.n; j++) {
    int esc = rc_has(f.v[j]);                         /* free in a def scheme's type, so never quantified here */
    for (int k = 0; !esc && k < dyn.n; k++) esc = dyn.v[k] == f.v[j];
    if (!esc) f.v[qn++] = f.v[j];                     /* compact in place: f's buffer becomes the scheme's own */
  }
  free(dyn.v);
  Scheme s; s.nq = qn; s.q = f.v; s.t = t; return s;
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
  case TNUM: return tvar();   /* numeral literal: fresh polymorphic type, as TFLOAT */
  }
  return NULL;
}

/* A def scheme's free variables are counted ONCE PER DEF, not once per check: walking every scheme on every
   check rediscovered an unchanging answer (160k walks), and the lookup must go through `def_find`'s hash --
   pushing the defs into a scan array made it a linear strcmp walk (9.4M entries scanned for the prelude). */
static void count_free(Scheme *s) {
  IL f = {0}; fv(s->t, &f);
  for (int j = 0; j < f.n; j++) { rc_grow(f.v[j]); envrc[f.v[j]]++; }
  free(f.v);
}
static void env_load_defs(int top) {
  static int reg_n = 0;                     /* defs whose free variables are already counted */
  for (int i = reg_n; i < ndefs; i++) if (defs[i].typed) count_free(&defs[i].sch);
  reg_n = ndefs;
  if (top) envn = 0;                        /* the reset is leak recovery, and only the outermost check may do it */
}

/* DEFERRED to the first reference: defs precede their uses, so the graph is a DAG; typing the 591 prelude defs is
   28.7ms of the 61.6ms startup and a program touches a fraction of them.  A scheme typed after `env_load_defs`' watermark has gone by is counted here. */
static void def_type(Def *d) {
  char err[512]; Scheme sch; int sav = envn; const char *nm = strrchr(d->name, '.'); Term *b = d->raw ? d->raw : d->term;
  int ok = d->rec ? type_check_rec(nm ? nm + 1 : d->name, b, &sch, err, sizeof err) : type_check(b, &sch, err, sizeof err);
  envn = sav;
  if (!ok) { printf("error: %s\n", err); return; }   /* an ill-typed def reports at its first use */
  d->sch = sch; d->typed = 1; count_free(&sch);
}

int type_check(Term *t, Scheme *out, char *err, int errsz) {
  jmp_buf jb, *sav = TJ; int top = TJ == &TJB; TJ = &jb;   /* only the OUTERMOST check may reset the binder stack */
  if (setjmp(jb)) { TJ = sav; snprintf(err, errsz, "%s", TMSG); return 0; }
  env_load_defs(top); *out = generalize(infer(t)); TJ = sav; return 1;
}

int type_check_rec(const char *name, Term *body, Scheme *out, char *err, int errsz) {
  jmp_buf jb, *sav = TJ; int top = TJ == &TJB; TJ = &jb;   /* only the OUTERMOST check may reset the binder stack */
  if (setjmp(jb)) { TJ = sav; snprintf(err, errsz, "%s", TMSG); return 0; }
  env_load_defs(top); Type *a = tvar(); env_push(name, (Scheme){.nq = 0, .t = a});
  unify(a, infer(body)); envn--; *out = generalize(a); TJ = sav; return 1;
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
  IL f = {0}; fv(t, &f);
  Scheme s; s.nq = f.n; s.q = f.v; s.t = t; return s;
}
