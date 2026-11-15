#include "lin.h"
#include <ctype.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

void (*lin_ctor_demand)(const char *name);
static const char *S;
static int P;
static jmp_buf PJ;
static char PMSG[256];

static void pfail(const char *msg) {
  snprintf(PMSG, sizeof PMSG, "%s", msg);
  longjmp(PJ, 1);
}

static const char **iset; static size_t iset_n, iset_cap;   /* identifiers: one block each, kept for the run, so a handed-out pointer never moves */
static size_t islot(const char *s, size_t n, size_t cap) { size_t j = 2166136261u; for (size_t i = 0; i < n; i++) j = (j ^ (unsigned char)s[i]) * 16777619u; return j & (cap - 1); }
/* Interning is IDEMPOTENT: the same text returns the same pointer, so a reader that reads one string a million times keeps ONE copy of it. */
const char *lin_intern(const char *s, size_t n) {
  if (iset_n * 2 >= iset_cap) { const char **old = iset; size_t was = iset_cap; iset_cap = iset_cap ? iset_cap * 2 : 64; iset = calloc(iset_cap, sizeof *iset); iset_n = 0;
    for (size_t i = 0; i < was; i++) { if (old[i]) { size_t k = islot(old[i], strlen(old[i]), iset_cap); while (iset[k]) k = (k + 1) & (iset_cap - 1); iset[k] = old[i]; iset_n++; } } free((void *)old); }
  size_t j = islot(s, n, iset_cap);
  while (iset[j]) { if (!strncmp(iset[j], s, n) && !iset[j][n]) return iset[j]; j = (j + 1) & (iset_cap - 1); }
  char *p = malloc(n + 1); memcpy(p, s, n); p[n] = 0; iset[j] = p; iset_n++; return p;
}
const char *lin_internf(const char *fmt, ...) {
  va_list ap, ap2; va_start(ap, fmt); va_copy(ap2, ap);
  int n = vsnprintf(NULL, 0, fmt, ap); va_end(ap); if (n < 0) { va_end(ap2); return ""; }
  char *p = malloc((size_t)n + 1); vsnprintf(p, (size_t)n + 1, fmt, ap2); va_end(ap2); return p;
}

static void skipws(void) {
  for (;;) {
    while (S[P] && isspace((unsigned char)S[P])) P++;
    if (S[P] == ';') { while (S[P] && S[P] != '\n') P++; continue; }
    break;
  }
}

/* Terms come from a pool: a program's front end makes and drops millions of them (every expansion of a
   definition is a copy), and one at a time from malloc that was a quarter of its time.  A released node heads
   the free list (through `l`); a fresh one is carved from a block that doubles. */
static Term *term_pool; static Term *term_blk; static size_t term_left, term_next;
Term *term_new(int type, const char *name, Term *l, Term *r) {
  Term *t = term_pool;
  if (t) term_pool = t->l;
  else {
    if (!term_left) { term_next = term_next ? term_next * 2 : 1024; term_blk = malloc(term_next * sizeof *term_blk); if (!term_blk) { fprintf(stderr, "Error: out of memory\n"); exit(1); } term_left = term_next; }
    t = term_blk++; term_left--;
  }
  *t = (Term){.type = type, .l = l, .r = r};
  t->name = name ? name : ""; return t;
}
void term_release(Term *t) { t->l = term_pool; term_pool = t; }   /* one node, not what it points at */
void term_free(Term *t) { while (t) { Term *r = t->r; term_free(t->l); term_release(t); t = r; } }
Term *term_copy(Term *t) {
  if (!t) return NULL;
  Term *c = term_new(t->type, t->name, term_copy(t->l), term_copy(t->r));
  c->annot = t->annot;            /* a stated type (a literal's, a field's) is part of the term */
  c->nl = t->nl; c->occ = t->occ;   /* (a copy's binders bind the same occurrences in the copy) */
  return c;
}
Term *term_fix(const char *name, Term *body) {
  const char *H = "_fix_h", *X = "_fix_x";
  Term *xx = term_new(TAPP, "", term_new(TVAR, X, 0, 0), term_new(TVAR, X, 0, 0));
  Term *lam = term_new(TLAM, X, term_new(TAPP, "", term_new(TVAR, H, 0, 0), xx), 0);
  Term *y = term_new(TLAM, H, term_new(TAPP, "", term_copy(lam), term_copy(lam)), 0);
  term_free(lam);
  return term_new(TAPP, "", y, term_new(TLAM, name, term_copy(body), 0));
}

int term_refs(Term *t, const char *name) {
  if (!t) return 0;
  switch (t->type) {
  case TVAR: return !strcmp(t->name, name);
  case TLAM: return strcmp(t->name, name) && term_refs(t->l, name);
  case TLET: return strcmp(t->name, name) && (term_refs(t->l, name) || term_refs(t->r, name));
  default: return term_refs(t->l, name) || term_refs(t->r, name);
  }
}

static const char *sym(void) {
  int start = P;
  if (S[P] == '\\' || ((unsigned char)S[P] == 0xce && (unsigned char)S[P + 1] == 0xbb)) P += S[P] == '\\' ? 1 : 2;
  else while (S[P] && !isspace((unsigned char)S[P]) && S[P] != '(' && S[P] != ')') P++;
  return P > start ? lin_intern(S + start, (size_t)(P - start)) : NULL;
}

/* An EXPLICIT thunk, in pure lambda calculus: `(lazy e)` is `(\_ e)` and `(force t)` applies it to the
   identity.  Needed order already never reduces what nothing demands, so this is for code that wants to pass a
   delayed value around as data.  The binder names contain a space, so no source program can capture them. */
static Term *thunk(Term *e) { return term_new(TLAM, " t", e, NULL); }
static Term *unit_id(void) { return term_new(TLAM, " i", term_new(TVAR, " i", NULL, NULL), NULL); }

static int islambda(const char *s) {
  return !strcmp(s, "\\") || !strcmp(s, "lambda") || !strcmp(s, "lam") ||
         !strcmp(s, "\xce\xbb");
}

static int isnum(const char *s) {
  if (*s == '-' && s[1]) s++;                        /* a negative integer literal */
  if (!*s) return 0;
  for (const char *p = s; *p; p++)
    if (!isdigit((unsigned char)*p)) return 0;
  return 1;
}
/* A float literal: optionally '-'/'+', digits with a '.', or an exponent. */
static int isfloat(const char *s) {
  if (!*s) return 0;
  const char *p = s;
  if (*p == '-' || *p == '+') p++;
  if (!isdigit((unsigned char)*p)) return 0;
  if (!strpbrk(p, ".eE")) return 0;
  for (; *p; p++)
    if (!isdigit((unsigned char)*p) && *p != '.' && *p != 'e' && *p != 'E') return 0;
  return 1;
}


static Term *parse_term(void);

/* type annotations: t := atom ('->' t)? ; atom := name | '(' t ')'; scalars bool/num/float + datatypes are nominals */
static Type *parse_type(void);
static const char **tvn;
static Type **tvt;
static int tvnn, tvcap;
/* datatype field-type parsing context: when non-zero, `params` lists the declared
   type-parameter names of the datatype, and a bare type atom matching one becomes
   a TPARAM reference (index into params) instead of a fresh type variable. */
static const char **dt_params; static int dt_np;
static int dt_in = 0;

static Type *parse_type_atom(void) {
  skipws();
  if (S[P] == '(') {
    P++; Type *t = parse_type(); skipws();
    if (S[P] != ')') pfail("type: missing ')'");
    P++; return t;
  }
  const char *nm = sym();
  if (!nm) pfail("type: expected name");
  /* a datatype a library module declares, named before anything of that module is used: the module is read now
     (a type is capitalised; a lower-case name is a type variable) */
  if (!nominal_lookup(nm) && nm[0] >= 'A' && nm[0] <= 'Z' && lin_ctor_demand) {
    /* (reading that module parses its own datatypes: this one's half-read state is kept aside meanwhile) */
    int snp = dt_np, sin = dt_in, stn = tvnn; const char **sp = malloc(sizeof *sp * (size_t)(snp + 1)); for (int i = 0; i < snp; i++) sp[i] = dt_params[i];
    const char **sn = malloc(sizeof *sn * (size_t)(stn + 1)); Type **st = malloc(sizeof *st * (size_t)(stn + 1));
    for (int i = 0; i < stn; i++) { sn[i] = tvn[i]; st[i] = tvt[i]; }
    lin_ctor_demand(nm);
    for (int i = 0; i < snp; i++) dt_params[i] = sp[i]; free(sp); dt_np = snp; dt_in = sin;
    if (tvcap < stn) { tvn = realloc(tvn, sizeof *tvn * (size_t)(tvcap = stn)); tvt = realloc(tvt, sizeof *tvt * (size_t)tvcap); }
    for (int i = 0; i < stn; i++) { tvn[i] = sn[i]; tvt[i] = st[i]; }
    tvnn = stn; free(sn); free(st);
  }
  if (nominal_lookup(nm)) {
    /* generic nominal: consume `arity` type-argument atoms, chained as TARGs. */
    Type *t = type_nominal(nm); Type **cur = &t->a;
    int arity = nominal_arity(nm);
    for (int i = 0; i < arity; i++) { *cur = type_arg(parse_type_atom()); cur = &(*cur)->b; }
    return t;
  }
  if (dt_in) {                        /* a datatype type-param reference (e.g. `a`) */
    for (int i = 0; i < dt_np; i++) if (!strcmp(dt_params[i], nm)) return type_param(i);
  }
  for (int i = 0; i < tvnn; i++) if (!strcmp(tvn[i], nm)) return tvt[i];
  if (tvnn >= tvcap) {
    tvn = realloc(tvn, (size_t)(tvcap = tvcap ? tvcap * 2 : 64) * sizeof *tvn);
    tvt = realloc(tvt, (size_t)tvcap * sizeof *tvt);
  }
  tvn[tvnn] = nm;
  tvt[tvnn] = type_var();
  return tvt[tvnn++];
}

static Type *parse_type(void) {
  Type *a = parse_type_atom();
  skipws();
  if (S[P] == '-' && S[P + 1] == '>') {
    P += 2;
    return type_arrow(a, parse_type());
  }
  return a;
}

static Type *parse_type_top(void) { tvnn = 0; return parse_type(); }

static Term *parse_tail(Term *f) {
  for (;;) {
    skipws();
    if (S[P] == ')') { P++; return f; }
    if (!S[P]) pfail("missing ')'");
    f = term_new(TAPP, "", f, parse_term());
  }
}

/* ---------------- match: patterns compiled to constructor dispatch ----------------
   A datatype value IS its own dispatch: applied to one branch per constructor, in declaration order, it
   picks one and hands it the fields.  So a `match` over declared constructors is compiled here, once, into
   exactly that: rows of patterns become a tree of dispatches (Wadler's / Maranget's column method), with
   `_`, variables, nested constructor patterns and number literals.  Nothing new reaches the net -- a number
   pattern is an `eq` test, a nested pattern is a dispatch on the field -- and a match whose branches are one
   plain pattern per constructor, in order, compiles to the same term it always did.
   It is checked while it is compiled: a constructor no branch covers, and a branch no value can reach, are
   errors (the second catches a misspelt nullary constructor, which would otherwise read as a variable). */
typedef struct Pat { int kind; const char *name; long cid; int k; struct Pat **sub; } Pat;   /* kind: */
enum { P_WILD, P_VAR, P_CTOR, P_NUM };
typedef struct { const char *name, *var; } PBind;
typedef struct { Pat **ps; Term *body; PBind *b; int nb, id; } PRow;
typedef struct { Term *body; const char *text; int uses; } PArm;
static PArm *parms; static int pfresh;
static char PCTXMSG[160];   /* what a branch is missing for, when none is left: "'nil' in a field of 'cons'" */

static void pfailf(const char *fmt, const char *a, const char *b) {
  char m[sizeof PMSG]; snprintf(m, sizeof m, fmt, a, b ? b : ""); pfail(m);
}
static long ctor_find(const char *name) {
  long cid = lin_ctor_lookup(name);
  if (!cid && lin_ctor_demand && strcmp(name, "_")) { lin_ctor_demand(name); cid = lin_ctor_lookup(name); }
  return cid;
}
/* the latest declaration of constructor i of datatype dt (as lin_ctor_lookup: the latest wins) */
static long ctor_of(const char *dt, int i) {
  long best = 0;
  for (long id = 1; lin_ctor_info(id); id++) { const LinCtor *c = lin_ctor_info(id); if (c->i == i && !strcmp(c->dt, dt)) best = id; }
  return best;
}
static Pat *pat_new(int kind, const char *name) { Pat *p = calloc(1, sizeof *p); p->kind = kind; p->name = name; return p; }
/* has: 1 = names a declared constructor, 2 = a literal or nesting (so only the compiled form can mean it) */
static Pat *parse_pat(int top, int *has) {
  skipws();
  if (S[P] == '(') {
    P++; skipws();
    const char *h = sym(); if (!h) pfail("match: bad pattern");
    long cid = ctor_find(h);
    Pat *p = pat_new(P_CTOR, h); p->cid = cid; int cap = 0;
    if (cid) *has |= 1;
    for (;;) {
      skipws(); if (S[P] == ')') { P++; break; }
      if (!S[P]) pfail("missing ')'");
      if (p->k == cap) p->sub = realloc(p->sub, (size_t)(cap = cap ? cap * 2 : 4) * sizeof *p->sub);
      p->sub[p->k++] = parse_pat(0, has);
    }
    if (!top) *has |= 2;
    return p;
  }
  const char *n = sym(); if (!n) pfail("match: bad pattern");
  if (!strcmp(n, "_")) return pat_new(P_WILD, n);
  if (isnum(n)) { *has |= 2; return pat_new(P_NUM, n); }
  long cid = ctor_find(n);
  if (cid && lin_ctor_info(cid)->k == 0) { Pat *p = pat_new(P_CTOR, n); p->cid = cid; *has |= 1; if (!top) *has |= 2; return p; }
  if (!top) *has |= 2;   /* a variable below the top binds a field: only the compiled form has one */
  return pat_new(P_VAR, n);
}
static void pat_vars(Pat *p, const char ***seen, int *n, int *cap) {
  if (p->kind == P_VAR) {
    for (int i = 0; i < *n; i++) if (!strcmp((*seen)[i], p->name)) pfailf("match: '%s' is bound twice in one pattern", p->name, NULL);
    if (*n == *cap) *seen = realloc(*seen, (size_t)(*cap = *cap ? *cap * 2 : 8) * sizeof **seen);
    (*seen)[(*n)++] = p->name;
  }
  if (p->kind == P_CTOR) for (int i = 0; i < p->k; i++) pat_vars(p->sub[i], seen, n, cap);
}
static const char *pfresh_name(void) { return lin_internf(" p%d", pfresh++); }
static Term *pvar(const char *n) { return term_new(TVAR, n, NULL, NULL); }
static PRow prow_bind(PRow r, const char *name, const char *var) {   /* a copy of r with one more binding */
  PBind *b = malloc((size_t)(r.nb + 1) * sizeof *b); if (r.nb) memcpy(b, r.b, (size_t)r.nb * sizeof *b);
  b[r.nb] = (PBind){name, var}; r.b = b; r.nb++; return r;
}
static Term *pleaf(PRow *r) {
  PArm *a = &parms[r->id];
  Term *t = a->uses++ ? term_copy(a->body) : a->body;
  for (int i = r->nb - 1; i >= 0; i--)
    if (strcmp(r->b[i].name, r->b[i].var)) t = term_new(TAPP, "", term_new(TLAM, r->b[i].name, t, NULL), pvar(r->b[i].var));
  return t;
}
static Term *pcompile(const char **vs, int nv, PRow *rows, int nr) {
  if (!nr) pfailf("match: no branch for %s", PCTXMSG[0] ? PCTXMSG : "some values", NULL);
  int c = 0;
  while (c < nv && (rows[0].ps[c]->kind == P_WILD || rows[0].ps[c]->kind == P_VAR)) c++;
  if (c == nv) {   /* the first row matches whatever is left: bind its variables */
    PRow r = rows[0];
    for (int j = 0; j < nv; j++) if (r.ps[j]->kind == P_VAR) r = prow_bind(r, r.ps[j]->name, vs[j]);
    return pleaf(&r);
  }
  /* rows binding column c to a variable: the binding is made now, and the pattern is then a wildcard */
  PRow *rs = malloc((size_t)nr * sizeof *rs);
  for (int j = 0; j < nr; j++) { rs[j] = rows[j]; if (rows[j].ps[c]->kind == P_VAR) rs[j] = prow_bind(rows[j], rows[j].ps[c]->name, vs[c]); }
  Pat *p0 = rows[0].ps[c];
  Term *out;
  if (p0->kind == P_NUM) {
    /* (if (eq v n) <rows that take n> <the rest, still testing v>) */
    PRow *yes = malloc((size_t)nr * sizeof *yes), *no = malloc((size_t)nr * sizeof *no); int ny = 0, nn = 0;
    for (int j = 0; j < nr; j++) {
      Pat *q = rs[j].ps[c];
      if (q->kind == P_CTOR) pfailf("match: '%s' is a constructor, and this column is numbers", q->name, NULL);
      int lit = q->kind == P_NUM, same = lit && !strcmp(q->name, p0->name);
      if (same || !lit) { PRow y = rs[j]; y.ps = malloc((size_t)nv * sizeof *y.ps); memcpy(y.ps, rs[j].ps, (size_t)nv * sizeof *y.ps); y.ps[c] = pat_new(P_WILD, "_"); yes[ny++] = y; }
      if (!same) no[nn++] = rs[j];
    }
    char ctx[sizeof PCTXMSG]; memcpy(ctx, PCTXMSG, sizeof ctx);
    Term *a = pcompile(vs, nv, yes, ny);
    memcpy(PCTXMSG, ctx, sizeof ctx);
    if (!strncmp(ctx, "numbers other than ", 19)) snprintf(PCTXMSG, sizeof PCTXMSG, "%s, %s", ctx, p0->name);
    else snprintf(PCTXMSG, sizeof PCTXMSG, "numbers other than %s%s%s", p0->name, ctx[0] ? " " : "", ctx);
    Term *b = pcompile(vs, nv, no, nn);
    memcpy(PCTXMSG, ctx, sizeof ctx);
    Term *test = term_new(TAPP, "", term_new(TAPP, "", pvar("eq"), pvar(vs[c])), term_new(TNUM, p0->name, NULL, NULL));
    out = term_new(TAPP, "if", term_new(TAPP, "", test, a), b);
    free(yes); free(no);
  } else {
    if (!p0->cid) pfailf("match: '%s' is not a constructor", p0->name, NULL);
    const LinCtor *c0 = lin_ctor_info(p0->cid); const char *dt = c0->dt; int m = c0->m;
    for (int j = 0; j < nr; j++) {
      Pat *q = rs[j].ps[c];
      if (q->kind == P_NUM) pfailf("match: %s is a number, and this column is '%s' values", q->name, dt);
      if (q->kind != P_CTOR) continue;
      if (!q->cid) pfailf("match: '%s' is not a constructor", q->name, NULL);
      const LinCtor *ci = lin_ctor_info(q->cid);
      if (strcmp(ci->dt, dt)) { char m2[sizeof PMSG]; snprintf(m2, sizeof m2, "match: '%s' is a constructor of '%s', not of '%s'", q->name, ci->dt, dt); pfail(m2); }
      if (q->k != ci->k) { char m2[sizeof PMSG]; snprintf(m2, sizeof m2, "match: '%s' has %d field%s, the pattern gives %d", q->name, ci->k, ci->k == 1 ? "" : "s", q->k); pfail(m2); }
    }
    out = pvar(vs[c]);
    char ctx[sizeof PCTXMSG]; memcpy(ctx, PCTXMSG, sizeof ctx);
    for (int i = 0; i < m; i++) {
      long cid = ctor_of(dt, i); const LinCtor *ci = lin_ctor_info(cid); int k = ci->k;
      PRow *sp = malloc((size_t)nr * sizeof *sp); int ns = 0, nv2 = nv - 1 + k;
      for (int j = 0; j < nr; j++) {
        Pat *q = rs[j].ps[c];
        if (q->kind == P_CTOR && strcmp(lin_ctor_info(q->cid)->name, ci->name)) continue;
        PRow y = rs[j]; y.ps = malloc((size_t)(nv2 ? nv2 : 1) * sizeof *y.ps); int w = 0;
        for (int x = 0; x < nv; x++) if (x != c) y.ps[w++] = rs[j].ps[x];
        for (int f = 0; f < k; f++) y.ps[w++] = q->kind == P_CTOR ? q->sub[f] : pat_new(P_WILD, "_");
        sp[ns++] = y;
      }
      /* the fields' names: a lone row's own variables (the term a plain match always was), else fresh */
      const char **v2 = malloc((size_t)(nv2 ? nv2 : 1) * sizeof *v2); int w = 0;
      for (int x = 0; x < nv; x++) if (x != c) v2[w++] = vs[x];
      for (int f = 0; f < k; f++) {
        Pat *q = ns == 1 ? sp[0].ps[nv - 1 + f] : NULL;
        v2[w++] = q && q->kind == P_VAR ? q->name : pfresh_name();
      }
      snprintf(PCTXMSG, sizeof PCTXMSG, "'%s'%s%s", ci->name, ctx[0] ? " " : "", ctx);
      if (ns) snprintf(PCTXMSG, sizeof PCTXMSG, "in a field of '%s'", ci->name);
      Term *lam = pcompile(v2, nv2, sp, ns);
      memcpy(PCTXMSG, ctx, sizeof ctx);
      for (int f = k - 1; f >= 0; f--) lam = term_new(TLAM, v2[nv - 1 + f], lam, NULL);
      lam = term_new(TAPP, "", term_new(TLAM, "_m", lam, NULL), term_new(TNUM, lin_internf("%ld", cid), NULL, NULL));
      out = term_new(TAPP, lin_internf("match:%s", ci->name), out, lam);
      free(sp); free(v2);
    }
  }
  free(rs);
  return out;
}
/* is the scrutinee variable used once, as the head of the top dispatch? then the scrutinee goes there itself */
static Term **phead(Term *t, const char *v) {
  Term **h = NULL;
  while (t && t->type == TAPP && t->name && !strncmp(t->name, "match:", 6)) { if (t->l->type == TVAR) { h = &t->l; break; } t = t->l; }
  return h && !strcmp((*h)->name, v) ? h : NULL;
}
static int pcount(Term *t, const char *v) {   /* occurrences of a (space-named, so never shadowed) variable */
  if (!t) return 0;
  if (t->type == TVAR) return !strcmp(t->name, v);
  return pcount(t->l, v) + pcount(t->r, v);
}
static Term *parse_match(void) {
  Term *scrut = parse_term();
  int cap = 0, n = 0, has = 0; Pat **pats = NULL; PArm *arms = NULL;
  for (;;) {
    skipws();
    if (S[P] != '(') break;
    P++; skipws();
    if (S[P] == ')') { P++; break; }
    if (n == cap) { cap = cap ? cap * 2 : 8; pats = realloc(pats, (size_t)cap * sizeof *pats); arms = realloc(arms, (size_t)cap * sizeof *arms); }
    int ps = P;
    pats[n] = parse_pat(1, &has);
    arms[n].text = lin_intern(S + ps, (size_t)(P - ps)); arms[n].uses = 0;
    arms[n].body = parse_tail(parse_term());
    { const char **seen = NULL; int sn = 0, sc = 0; pat_vars(pats[n], &seen, &sn, &sc); free(seen); }
    n++;
  }
  skipws(); if (S[P] == ')') P++;
  if (!n) pfail("match: no branches");
  if (!(has & 1) && !(has & 2)) {
    /* no declared constructor named: positional dispatch, branch by branch, as written (an undeclared
       Scott encoding the program builds itself) */
    Term *app = scrut;
    for (int j = 0; j < n; j++) {
      Term *lam = arms[j].body;
      Pat *p = pats[j];
      if (p->kind == P_CTOR) for (int i = p->k - 1; i >= 0; i--) lam = term_new(TLAM, p->sub[i]->name, lam, NULL);
      app = term_new(TAPP, lin_internf("match:%s", p->name), app, lam);
    }
    free(pats); free(arms); return app;
  }
  for (int j = 0; j < n; j++) if (pats[j]->kind == P_CTOR && !pats[j]->cid) pfailf("match: '%s' is not a constructor", pats[j]->name, NULL);
  PArm *sav = parms; parms = arms;
  PRow *rows = malloc((size_t)n * sizeof *rows);
  for (int j = 0; j < n; j++) { rows[j].ps = malloc(sizeof *rows[j].ps); rows[j].ps[0] = pats[j]; rows[j].body = arms[j].body; rows[j].b = NULL; rows[j].nb = 0; rows[j].id = j; }
  const char *v0 = lin_internf(" s%d", pfresh++);
  PCTXMSG[0] = 0;
  Term *t = pcompile(&v0, 1, rows, n);
  for (int j = 0; j < n; j++) if (!arms[j].uses) {
    for (int i = 0; i < j; i++) if (pats[i]->kind == P_VAR) {   /* (the usual cause: a misspelt constructor reads as a variable) */
      char m2[sizeof PMSG]; snprintf(m2, sizeof m2, "match: the branch %s is never chosen: '%s' is not a constructor, so it is a variable and takes every value", arms[j].text, pats[i]->name); pfail(m2); }
    pfailf("match: the branch %s is never chosen (an earlier branch takes every value it would)", arms[j].text, NULL);
  }
  parms = sav;
  Term **h = phead(t, v0);
  if (h && pcount(t, v0) == 1) *h = scrut;
  else t = term_new(TAPP, "", term_new(TLAM, v0, t, NULL), scrut);
  free(rows); free(pats); free(arms);
  return t;
}

static Term *parse_atom(const char *kw) {
  if (isnum(kw)) { Term *t = term_new(TNUM, kw, NULL, NULL); return t; }
  if (isfloat(kw)) { Term *t = term_new(TFLOAT, kw, NULL, NULL); return t; }
  return term_new(TVAR, kw, NULL, NULL);
}

static Term *parse_term(void) {
  skipws();
  if (!S[P]) pfail("unexpected end of input");
  if (S[P] == ')') pfail("unexpected ')'");
  if (S[P] == '"') {
    P++; unsigned char dec[4096]; int dlen = 0;
    while (S[P] && S[P] != '"') {
      unsigned char c = (unsigned char)S[P++];
      if (c == '\\' && S[P]) {
        c = (unsigned char)S[P++];
        if (c == 'n') c = '\n'; else if (c == 't') c = '\t'; else if (c == 'r') c = '\r';
        else if (c == 'e') c = 27;
        else if (c == '0' && S[P] >= '0' && S[P] <= '7' && S[P + 1] >= '0' && S[P + 1] <= '7') {
          c = (unsigned char)((S[P] - '0') * 8 + (S[P + 1] - '0')); P += 2;
        } else if (c == '0') c = '\0';
        else if (c == 'x' && isxdigit((unsigned char)S[P]) && isxdigit((unsigned char)S[P + 1])) {
          char h[3] = {S[P], S[P + 1], 0}; c = (unsigned char)strtol(h, NULL, 16); P += 2;
        }
      }
      if (dlen < (int)sizeof(dec)) dec[dlen++] = c;
    }
    if (S[P] != '"') pfail("unterminated string literal");
    P++;
    /* A string is a list of character codes, written as the list encoding ITSELF -- cells \c.\n.((c h) t) ending in
       \c.\n.true -- so a literal needs no library.  Its type, `list num`, is stated on the term (the checker
       trusts an annotated lambda), and the binder names contain a space so nothing can capture them. */
    Term *body = term_new(TLAM, " c", term_new(TLAM, " n", term_new(TLAM, " t", term_new(TLAM, " f",
                   term_new(TVAR, " t", NULL, NULL), NULL), NULL), NULL), NULL);
    for (int i = dlen - 1; i >= 0; i--) {
      char cb[8]; snprintf(cb, sizeof cb, "%d", dec[i]); Term *ch = term_new(TNUM, lin_intern(cb, strlen(cb)), NULL, NULL);
      body = term_new(TLAM, " c", term_new(TLAM, " n", term_new(TAPP, "", term_new(TAPP, "", term_new(TVAR, " c", NULL, NULL), ch), body), NULL), NULL);
    }
    Type *ty = type_nominal("list"); ty->a = type_arg(type_nominal("num"));
    body->annot = ty;
    return body;
  }
  if (S[P] == '(') {
    P++; skipws();
    if (S[P] == '(') return parse_tail(parse_term());
    const char *kw = sym();
    if (!kw) pfail("empty '('");
    if (islambda(kw)) {
      skipws(); const char *var = sym(); if (!var) pfail("lambda: expected binder");
      Term *body = parse_term(); return term_new(TLAM, var, parse_tail(body), NULL);
    }
    if (!strcmp(kw, "define") || !strcmp(kw, "define!")) {
      int typed = !strcmp(kw, "define!");
      skipws(); const char *name = sym(); if (!name) pfail("define: expected name");
      /* the names the net's own protocols use as binders (primitive operations, constructors, match branches):
         a definition of one is read as part of that protocol, and silently computes something else */
      { const char *bare = strrchr(name, '.'); bare = bare ? bare + 1 : name;
        if (!strcmp(bare, "_op") || !strcmp(bare, "_k") || !strcmp(bare, "_c") || !strcmp(bare, "_m")) pfail("define: '_op', '_k', '_c' and '_m' are reserved names"); }
      Type *ty = typed ? parse_type_top() : NULL;
      Term *v = parse_term(); skipws();
      if (S[P] != ')') pfail("define: expected ')'"); else P++;
      Term *t = term_new(typed ? TDEFX : TDEF, name, v, NULL);
      t->annot = ty; return t;
    }
    if (!strcmp(kw, "load")) {
      skipws(); if (S[P] != '"') pfail("load: expected string path");
      int start = ++P;
      while (S[P] && S[P] != '"') { if (S[P] == '\\' && S[P + 1]) P++; P++; }
      if (S[P] != '"') pfail("load: unterminated path");
      const char *path = lin_intern(S + start, (size_t)(P - start));
      P++; skipws();
      if (S[P] != ')') pfail("load: expected ')'"); else P++;
      return term_new(TLOAD, path, NULL, NULL);
    }
    if (!strcmp(kw, "namespace") || !strcmp(kw, "ns") || !strcmp(kw, "module") || !strcmp(kw, "open") || !strcmp(kw, "use")) {
      int isOpen = !strcmp(kw, "open") || !strcmp(kw, "use");
      skipws(); const char *name = sym(); if (!name) pfail("expected name");
      skipws(); if (S[P] != ')') pfail("expected ')'"); else P++;
      return term_new(isOpen ? TOPEN : TNS, name, NULL, NULL);
    }
    if (!strcmp(kw, "export")) {
      /* (export <ns>): re-export every public member of `ns` into the current
         namespace.  Collapses the per-module `(open ns)` + `(define! x ns.x)`
         alias boilerplate. */
      skipws(); const char *name = sym(); if (!name) pfail("expected name");
      skipws(); if (S[P] != ')') pfail("expected ')'"); else P++;
      return term_new(TEXPORT, name, NULL, NULL);
    }
    /* (if c a b) is ((c a) b): a boolean IS a selector (\t.\f.t), so the form needs no library, and needed
       order reduces only the branch that is chosen. */
    if (!strcmp(kw, "if")) {
      Term *c = parse_term(), *a = parse_term(), *b = parse_term(); skipws();
      if (S[P] != ')') { pfail("if: expected (if cond then else)"); } P++;
      return term_new(TAPP, "if", term_new(TAPP, "", c, a), b);   /* the name marks it for the type checker only */
    }
    /* (lazy e) delays e as data; (force t) runs a delayed value. */
    if (!strcmp(kw, "lazy")) {
      Term *e = parse_term(); skipws();
      if (S[P] != ')') { pfail("lazy: expected (lazy expr)"); } P++;
      return thunk(e);
    }
    if (!strcmp(kw, "force")) {
      Term *e = parse_term(); skipws();
      if (S[P] != ')') { pfail("force: expected (force expr)"); } P++;
      return term_new(TAPP, "", e, unit_id());
    }
    if (!strcmp(kw, "match")) return parse_match();
    if (!strcmp(kw, "datatype") || !strcmp(kw, "data")) {
      skipws(); const char *dn;
      /* generic form: (datatype (Name p1 p2 ..) (Ctor f..) ..) declares `Name`
         with |pi| type parameters (arity); otherwise a simple name (arity 0). */
      int arity = 0; int np_ctx = 0;
      if (!dt_params) { dt_params = malloc(64 * sizeof *dt_params); }
      if (S[P] == '(') {
        P++; skipws(); if (!(dn = sym())) pfail("datatype: expected name");
        skipws(); while (S[P] != ')') { const char *pn = sym(); if (!pn) pfail("datatype: bad type param"); dt_params[arity] = pn; arity++; skipws(); }
        P++;
      } else if (!(dn = sym())) pfail("datatype: expected name");
      nominal_register(dn, arity);   /* register early so self-referential field types ((left Tree a)) parse */
      np_ctx = arity;                       /* field types may reference these params */
      /* constructors: (Name f1 f2 ...) where a field is `name` or `(name Type..)`. */
      int prev_in = dt_in, prev_np = dt_np;
      dt_in = (np_ctx > 0); dt_np = np_ctx;
      Term *ctrs = NULL, *tail = NULL;
      skipws();
      while (S[P] == '(') {
        P++; skipws();
        if (S[P] == ')') { P++; continue; }
        const char *cn = sym(); if (!cn) pfail("datatype: expected constructor");
        Term *fields = NULL, *ftail = NULL;
        skipws();
        while (S[P] != ')') {
          const char *fn; Term *fv;
          if (S[P] == '(') {                 /* typed field (name Type..) */
            P++; skipws(); if (!(fn = sym())) pfail("datatype: bad field");
            skipws();
            Type *ty = parse_type();         /* param context active */
            skipws(); if (S[P] != ')') pfail("datatype: bad field type");
            P++;
            fv = term_new(TVAR, fn, NULL, NULL); fv->annot = ty;
          } else {	                         /* bare name: untyped polymorphism */
            if (!(fn = sym())) pfail("datatype: expected field");
            fv = term_new(TVAR, fn, NULL, NULL);
          }
          if (!fields) fields = ftail = fv; else { ftail->r = fv; ftail = fv; }
          skipws();
        }
        P++; /* consume ')' */
        Term *c = term_new(TVAR, cn, fields, NULL);
        if (!ctrs) ctrs = tail = c; else { tail->r = c; tail = c; }
        skipws();
      }
      dt_in = prev_in; dt_np = prev_np;
      skipws(); if (S[P] == ')') P++; /* consume datatype close */
      Term *dt = term_new(TDATATYPE, dn, ctrs, NULL);
      dt->annot = (Type *)(intptr_t)arity;   /* stash arity (annot is not freed by term_free) */
      return dt;
    }
    if (!strcmp(kw, "let")) {
      skipws(); if (S[P] != '(') pfail("let: expected '('"); P++;
      const char **names = NULL; Term **vals = NULL; int nb = 0, ncap = 0;
      for (;;) {
        skipws(); if (S[P] == ')') { P++; break; }
        if (S[P] != '(') pfail("let: expected binding");
        P++; skipws(); const char *vn = sym(); if (!vn) pfail("let: bad binding");
        Term *v = parse_term(); skipws(); if (S[P] != ')') pfail("let: missing ')' in binding");
        P++;
        if (nb >= ncap) {
          names = realloc(names, (size_t)(ncap = ncap ? ncap * 2 : 16) * sizeof *names);
          vals = realloc(vals, (size_t)ncap * sizeof *vals);
        }
        names[nb] = vn; vals[nb++] = v;
      }
      Term *body = parse_tail(parse_term());
      /* A binding is a TLET, not `((\x body) value)`: same scope (each binding is visible in the
         next value and in the body, and now also to itself), but the net is SHARED rather than
         substituted, which is what lets the value refer to the name -- recursion. */
      for (int i = nb - 1; i >= 0; i--)
        body = term_new(TLET, names[i], vals[i], body);
      free(names); free(vals);
      return body;
    }
    return parse_tail(parse_atom(kw));
  }
  const char *kw = sym();
  if (!kw) pfail("unexpected character");
  return parse_atom(kw);
}

static int resync(int start) {
  int p = start, depth = 0;
  while (S[p]) {
    char c = S[p];
    if (c == ';') { while (S[p] && S[p] != '\n') p++; continue; }
    if (c == '(') depth++;
    else if (c == ')') { if (--depth <= 0) return p + 1; }
    else if (depth == 0 && !isspace((unsigned char)c)) {
      while (S[p] && !isspace((unsigned char)S[p]) && S[p] != '(' && S[p] != ')') p++;
      return p;
    }
    p++;
  }
  return p;
}

/* WHERE a form is: the file being read (NULL: a command line or the REPL) and the line its form starts on.
   A loader sets the file; the reader sets the line before handing each form on, and puts both back when it
   returns, so a form that loads another file first still reports its own place. */
const char *lin_parse_file; int lin_form_line;
const char *lin_where(char *buf, size_t n, int line) {
  if (lin_parse_file) snprintf(buf, n, "%s:%d", lin_parse_file, line); else snprintf(buf, n, "line %d", line);
  return buf;
}
static int line_at(int from_line, int from, int to) { for (int i = from; i < to; i++) from_line += S[i] == '\n'; return from_line; }

void parse_forms(const char *src, FormFn fn, void *ud) {
  const char *prev_S = S, *prev_file = lin_parse_file;
  int prev_P = P, prev_line = lin_form_line;
  jmp_buf prev_PJ;
  memcpy(prev_PJ, PJ, sizeof(jmp_buf));

  S = src;
  P = 0;
  volatile int line = 1, lpos = 0;   /* (kept across the longjmp of a parse error) */
  for (;;) {
    skipws();
    if (!S[P]) break;
    int start = P;
    line = line_at(line, lpos, start); lpos = start;
    if (setjmp(PJ)) {
      char msg[400], tmp[300];
      snprintf(msg, sizeof msg, "parse error: %s (at %s)", PMSG, lin_where(tmp, sizeof tmp, S[P] ? line_at(line, start, P) : line));
      lin_form_line = line;
      fn(NULL, msg, ud);
      P = resync(start);
      continue;
    }
    Term *t = parse_term();
    const char *file = lin_parse_file;
    lin_form_line = line;
    fn(t, NULL, ud);
    lin_parse_file = file;
  }

  S = prev_S;
  P = prev_P;
  lin_parse_file = prev_file; lin_form_line = prev_line;
  memcpy(PJ, prev_PJ, sizeof(jmp_buf));
}
