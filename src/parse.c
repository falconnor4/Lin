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
  Term *t = malloc(sizeof *t);
  *t = (Term){.type = type, .l = l, .r = r};
  snprintf(t->name, NAME, "%s", name ? name : "");
  return t;
}

void term_free(Term *t) {
  if (t) { term_free(t->l); term_free(t->r); free(t); }
}

Term *term_copy(Term *t) {
  if (!t) return NULL;
  return term_new(t->type, t->name, term_copy(t->l), term_copy(t->r));
}

int term_refs(Term *t, const char *name) {
  if (!t) return 0;
  switch (t->type) {
  case TVAR: return !strcmp(t->name, name);
  case TLAM: return strcmp(t->name, name) && term_refs(t->l, name);
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

static Term *scott(long k) {
  Term *cur = term_new(TLAM, "_sz", term_new(TLAM, "_ss", term_new(TVAR, "_sz", 0, 0), 0), 0);
  for (long i = 0; i < k; i++)
    cur = term_new(TLAM, "_sz", term_new(TLAM, "_ss", term_new(TAPP, "", term_new(TVAR, "_ss", 0, 0), cur), 0), 0);
  return cur;
}

static Term *parse_term(void);

/* type annotations: t := atom ('->' t)? ; atom := name | '(' t ')'
   builtins: num = fresh type variable, bool = p->q->p (fresh vars per use) */
static Type *parse_type(void);
static char (*tvn)[NAME];
static Type **tvt;
static int tvnn, tvcap;

static Type *parse_type_atom(void) {
  skipws();
  if (S[P] == '(') {
    P++;
    Type *t = parse_type();
    skipws();
    if (S[P] != ')') pfail("type: missing ')'");
    P++;
    return t;
  }
  char nm[NAME];
  if (!sym(nm, NAME)) pfail("type: expected name");
  if (!strcmp(nm, "num")) return type_var();
  if (!strcmp(nm, "bool")) { Type *p = type_var(), *q = type_var(); return type_arrow(p, type_arrow(q, p)); }
  if (!strcmp(nm, "list")) return type_list(parse_type_atom());
  for (int i = 0; i < tvnn; i++)
    if (!strcmp(tvn[i], nm)) return tvt[i];
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

static Type *parse_type_top(void) {
  tvnn = 0;
  return parse_type();
}

static Term *parse_tail(Term *f) {
  for (;;) {
    skipws();
    if (S[P] == ')') {
      P++;
      return f;
    }
    if (!S[P]) pfail("missing ')'");
    Term *a = parse_term();
    f = term_new(TAPP, "", f, a);
  }
}

static Term *parse_atom(const char *kw) {
  if (isnum(kw)) return scott(atol(kw));
  return term_new(TVAR, kw, NULL, NULL);
}

static Term *parse_term(void) {
  skipws();
  if (!S[P]) pfail("unexpected end of input");
  if (S[P] == ')') pfail("unexpected ')'");
  if (S[P] == '"') {
    P++;
    int start = P;
    while (S[P] && S[P] != '"') { if (S[P] == '\\' && S[P + 1]) P++; P++; }
    if (S[P] != '"') pfail("unterminated string literal");
    int end = P; P++;
    Term *body = term_new(TVAR, "nil", NULL, NULL);
    for (int i = end - 1; i >= start; i--) {
      char c = S[i];
      if (i > start && S[i - 1] == '\\') {
        if (c == 'n') c = '\n'; else if (c == 't') c = '\t';
        else if (c == 'r') c = '\r'; else if (c == '0') c = '\0';
        i--;
      }
      Term *ch = scott((unsigned char)c);
      body = term_new(TAPP, "", term_new(TAPP, "", term_new(TVAR, "cons", NULL, NULL), ch), body);
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
      for (int i = nb - 1; i >= 0; i--)
        body = term_new(TAPP, "", term_new(TLAM, names[i], body, NULL), vals[i]);
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