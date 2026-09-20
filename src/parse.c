#include "lin.h"
#include <ctype.h>
#include <setjmp.h>
#include <stdlib.h>
#include <string.h>

static const char *S;
static int P;
static jmp_buf PJ;
static char PMSG[128];

static void pfail(const char *msg) {
  snprintf(PMSG, sizeof PMSG, "%s", msg);
  longjmp(PJ, 1);
}

static void skipws(void) {
  for (;;) {
    while (S[P] && isspace((unsigned char)S[P])) P++;
    if (S[P] == ';') { while (S[P] && S[P] != '\n') P++; continue; }
    break;
  }
}

Term *term_new(int type, const char *name, Term *l, Term *r) {
  Term *t = malloc(sizeof *t); *t = (Term){.type = type, .l = l, .r = r};
  snprintf(t->name, NAME, "%s", name ? name : ""); return t;
}
void term_free(Term *t) { if (t) { term_free(t->l); term_free(t->r); free(t); } }
Term *term_copy(Term *t) { return t ? term_new(t->type, t->name, term_copy(t->l), term_copy(t->r)) : NULL; }

int term_refs(Term *t, const char *name) {
  if (!t) return 0;
  switch (t->type) {
  case TVAR: return !strcmp(t->name, name);
  case TLAM: return strcmp(t->name, name) && term_refs(t->l, name);
  case TLET: return strcmp(t->name, name) && (term_refs(t->l, name) || term_refs(t->r, name));
  default: return term_refs(t->l, name) || term_refs(t->r, name);
  }
}

static int sym(char *buf, int bufsz) {
  int i = 0;
  if (S[P] == '\\' || ((unsigned char)S[P] == 0xce && (unsigned char)S[P + 1] == 0xbb)) {
    int len = S[P] == '\\' ? 1 : 2;
    if (bufsz > len) memcpy(buf, S + P, len);
    P += len;
    buf[len] = 0;
    return len;
  }
  while (S[P] && !isspace((unsigned char)S[P]) && S[P] != '(' && S[P] != ')') {
    if (i < bufsz - 1) buf[i++] = S[P];
    P++;
  }
  buf[i] = 0;
  return i;
}

static int islambda(const char *s) {
  return !strcmp(s, "\\") || !strcmp(s, "lambda") || !strcmp(s, "lam") ||
         !strcmp(s, "\xce\xbb");
}

static int isnum(const char *s) {
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

static Term *scott(long k) {
  Term *cur = term_new(TLAM, "_sz", term_new(TLAM, "_ss", term_new(TVAR, "_sz", 0, 0), 0), 0);
  for (long i = 0; i < k; i++)
    cur = term_new(TLAM, "_sz", term_new(TLAM, "_ss", term_new(TAPP, "", term_new(TVAR, "_ss", 0, 0), cur), 0), 0);
  return cur;
}

static Term *parse_term(void);

/* type annotations: t := atom ('->' t)? ; atom := name | '(' t ')'; scalars bool/num/float + datatypes are nominals */
static Type *parse_type(void);
static char (*tvn)[NAME];
static Type **tvt;
static int tvnn, tvcap;
/* datatype field-type parsing context: when non-zero, `params` lists the declared
   type-parameter names of the datatype, and a bare type atom matching one becomes
   a TPARAM reference (index into params) instead of a fresh type variable. */
static char (*dt_params)[NAME]; static int dt_np;
static int dt_in = 0;

static Type *parse_type_atom(void) {
  skipws();
  if (S[P] == '(') {
    P++; Type *t = parse_type(); skipws();
    if (S[P] != ')') pfail("type: missing ')'");
    P++; return t;
  }
  char nm[NAME];
  if (!sym(nm, NAME)) pfail("type: expected name");
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
  snprintf(tvn[tvnn], NAME, "%s", nm);
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

static Term *parse_atom(const char *kw) {
  if (isnum(kw)) return scott(atol(kw));
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
    Term *body = term_new(TVAR, "list.nil", NULL, NULL);
    for (int i = dlen - 1; i >= 0; i--) {
      Term *ch = scott(dec[i]);
      body = term_new(TAPP, "", term_new(TAPP, "", term_new(TVAR, "list.cons", NULL, NULL), ch), body);
    }
    return body;
  }
  if (S[P] == '(') {
    P++; skipws();
    if (S[P] == '(') return parse_tail(parse_term());
    char kw[NAME];
    if (!sym(kw, NAME)) pfail("empty '('");
    if (islambda(kw)) {
      skipws(); char var[NAME]; if (!sym(var, NAME)) pfail("lambda: expected binder");
      Term *body = parse_term(); return term_new(TLAM, var, parse_tail(body), NULL);
    }
    if (!strcmp(kw, "define") || !strcmp(kw, "define!")) {
      int typed = !strcmp(kw, "define!");
      skipws(); char name[NAME]; if (!sym(name, NAME)) pfail("define: expected name");
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
      int len = P - start; char path[NAME];
      if (len >= NAME) pfail("load: path too long");
      memcpy(path, S + start, (size_t)len); path[len] = '\0'; P++; skipws();
      if (S[P] != ')') pfail("load: expected ')'"); else P++;
      return term_new(TLOAD, path, NULL, NULL);
    }
    if (!strcmp(kw, "namespace") || !strcmp(kw, "ns") || !strcmp(kw, "module") || !strcmp(kw, "open") || !strcmp(kw, "use")) {
      int isOpen = !strcmp(kw, "open") || !strcmp(kw, "use");
      skipws(); char name[NAME]; if (!sym(name, NAME)) pfail("expected name");
      skipws(); if (S[P] != ')') pfail("expected ')'"); else P++;
      return term_new(isOpen ? TOPEN : TNS, name, NULL, NULL);
    }
    if (!strcmp(kw, "export")) {
      /* (export <ns>): re-export every public member of `ns` into the current
         namespace.  Collapses the per-module `(open ns)` + `(define! x ns.x)`
         alias boilerplate. */
      skipws(); char name[NAME]; if (!sym(name, NAME)) pfail("expected name");
      skipws(); if (S[P] != ')') pfail("expected ')'"); else P++;
      return term_new(TEXPORT, name, NULL, NULL);
    }
    if (!strcmp(kw, "match")) {
      /* match => scrut applied to one lambda per case; pat is `_`, a lone name, or (Name v1...vk). Positional Scott dispatch: no type/registry dep. */
      Term *scrut = parse_term();
      Term *app = scrut;
      skipws();
      while (S[P] == '(') {
        P++; skipws();
        if (S[P] == ')') { P++; break; }
        int k = 0; char (*vs)[NAME] = NULL;
        if (S[P] == '(') { /* (Ctor v1...vk) -> bind the fields */
          P++; skipws();
          char ctorhead[NAME]; if (!sym(ctorhead, NAME)) pfail("match: bad pattern");
          int cap = 0;
          for (;;) {
            skipws(); if (S[P] == ')') { P++; break; }
            char vn[NAME]; if (!sym(vn, NAME)) pfail("match: bad field");
            vs = realloc(vs, (size_t)(cap = cap ? cap * 2 : 4) * sizeof *vs);
            snprintf(vs[k++], NAME, "%s", vn);
          }
        } else {
          char pn[NAME]; if (!sym(pn, NAME)) pfail("match: bad pattern"); /* nullary/_ */
        }
        Term *body = parse_tail(parse_term());
        Term *lam = body; /* nullary / wildcard: pass the value directly */
        for (int i = k - 1; i >= 0; i--) lam = term_new(TLAM, vs[i], lam, NULL);
        free(vs);
        app = term_new(TAPP, "", app, lam);
        skipws();
      }
      skipws(); if (S[P] == ')') P++; /* consume match close */
      return app;
    }
    if (!strcmp(kw, "datatype") || !strcmp(kw, "data")) {
      skipws(); char dn[NAME];
      /* generic form: (datatype (Name p1 p2 ..) (Ctor f..) ..) declares `Name`
         with |pi| type parameters (arity); otherwise a simple name (arity 0). */
      int arity = 0; int np_ctx = 0;
      if (!dt_params) { dt_params = malloc(64 * sizeof *dt_params); }
      if (S[P] == '(') {
        P++; skipws(); if (!sym(dn, NAME)) pfail("datatype: expected name");
        skipws(); while (S[P] != ')') { char pn[NAME]; if (!sym(pn, NAME)) pfail("datatype: bad type param"); snprintf(dt_params[arity], NAME, "%s", pn); arity++; skipws(); }
        P++;
      } else if (!sym(dn, NAME)) pfail("datatype: expected name");
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
        char cn[NAME]; if (!sym(cn, NAME)) pfail("datatype: expected constructor");
        Term *fields = NULL, *ftail = NULL;
        skipws();
        while (S[P] != ')') {
          char fn[NAME]; Term *fv;
          if (S[P] == '(') {                 /* typed field (name Type..) */
            P++; skipws(); if (!sym(fn, NAME)) pfail("datatype: bad field");
            skipws();
            Type *ty = parse_type();         /* param context active */
            skipws(); if (S[P] != ')') pfail("datatype: bad field type");
            P++;
            fv = term_new(TVAR, fn, NULL, NULL); fv->annot = ty;
          } else {	                         /* bare name: untyped polymorphism */
            if (!sym(fn, NAME)) pfail("datatype: expected field");
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
      char (*names)[NAME] = NULL; Term **vals = NULL; int nb = 0, ncap = 0;
      for (;;) {
        skipws(); if (S[P] == ')') { P++; break; }
        if (S[P] != '(') pfail("let: expected binding");
        P++; skipws(); char vn[NAME]; if (!sym(vn, NAME)) pfail("let: bad binding");
        Term *v = parse_term(); skipws(); if (S[P] != ')') pfail("let: missing ')' in binding");
        P++;
        if (nb >= ncap) {
          names = realloc(names, (size_t)(ncap = ncap ? ncap * 2 : 16) * sizeof *names);
          vals = realloc(vals, (size_t)ncap * sizeof *vals);
        }
        snprintf(names[nb], NAME, "%s", vn); vals[nb++] = v;
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
  char kw[NAME];
  if (!sym(kw, NAME)) pfail("unexpected character");
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

void parse_forms(const char *src, FormFn fn, void *ud) {
  const char *prev_S = S;
  int prev_P = P;
  jmp_buf prev_PJ;
  memcpy(prev_PJ, PJ, sizeof(jmp_buf));

  S = src;
  P = 0;
  for (;;) {
    skipws();
    if (!S[P]) break;
    int start = P;
    if (setjmp(PJ)) {
      char msg[160];
      snprintf(msg, sizeof msg, "parse error: %s", PMSG);
      fn(NULL, msg, ud);
      P = resync(start);
      continue;
    }
    Term *t = parse_term();
    fn(t, NULL, ud);
  }

  S = prev_S;
  P = prev_P;
  memcpy(PJ, prev_PJ, sizeof(jmp_buf));
}
