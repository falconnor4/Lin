/* readback decoder: the scope-gauge normal form is a shared croissant that
   rarely reduces to an explicit tree; to recover values we decode the
   expanded source term in normal order (exactly the reference's evalBetaFull
   oracle).  `subst` is capture-avoiding: binders that would capture the
   argument are renamed with primes, mirroring the reference main.hs (which
   renames to y++"'"). */
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXD 300000
#define MAXSTEP 20000000

static long steps;

static Term *al(Term *t) { return term_copy(t); }
static Term *lam(const char *n, Term *b) { return term_new(TLAM, n, b, NULL); }
static Term *ap(Term *f, Term *a) { return term_new(TAPP, "", f, a); }

static int step(void) {
  if (++steps > MAXSTEP) { if (getenv("LIN_DBG")) fprintf(stderr,"[dec] STEPLIMIT\n"); return 1; }
  return 0;
}

/* does a name occur (as binder or free var) anywhere in a term? */
static int name_in(const char *nm, Term *t) {
  for (; t; t = t->l) {
    if (!strcmp(t->name, nm)) return 1;
    if (name_in(nm, t->r)) return 1;
  }
  return 0;
}

/* capture-avoiding substitution of x := s in t */
static Term *subst(const char *x, Term *s, Term *t, int depth) {
  if (step()) return NULL;
  if (depth > MAXD || !t) { if (getenv("LIN_DBG")) fprintf(stderr,"[dec] depth\n"); return NULL; }
  switch (t->type) {
  case TVAR:
    return strcmp(t->name, x) ? al(t) : al(s);
  case TLAM: {
    if (!strcmp(t->name, x)) return al(t); /* shadowed */
    if (name_in(t->name, s)) {             /* binder would capture: rename */
      static unsigned long nid;
      char nn[NAME];
      int base = (int)strlen(t->name);
      memcpy(nn, t->name, base);
      int pr = 1;
      for (;;) {
        for (int j = 0; j < pr && base + j < NAME - 1; j++)
          nn[base + j] = '\'';
        if (base + pr < NAME) {
          nn[base + pr] = 0;
          if (!name_in(nn, t->l) && !name_in(nn, s) && strcmp(nn, x)) break;
        }
        ++pr;
        if (pr > 16) break; /* fall back to a counter name below */
      }
      if (pr > 16) {
        do {
          snprintf(nn, NAME, "_u%lu", nid++);
        } while (name_in(nn, t->l) || name_in(nn, s) || !strcmp(nn, x));
      }
      Term *b = subst(t->name, term_new(TVAR, nn, NULL, NULL), t->l,
                      depth + 1);
      if (!b) return NULL;
      b = subst(x, s, b, depth + 1);
      if (!b) return NULL;
      return lam(nn, b);
    }
    Term *b = subst(x, s, t->l, depth + 1);
    if (!b) return NULL;
    return lam(t->name, b);
  }
  case TAPP: {
    Term *f = subst(x, s, t->l, depth + 1);
    if (!f) return NULL;
    Term *a = subst(x, s, t->r, depth + 1);
    if (!a) {
      term_free(f);
      return NULL;
    }
    return ap(f, a);
  }
  }
  return al(t);
}

/* whnf takes ownership of t and returns a new term in WHNF */
static Term *whnf(Term *t) {
  while (t && t->type == TAPP) {
    if (step()) { term_free(t); return NULL; }
    Term *f = whnf(t->l);
    t->l = NULL;
    if (!f) { term_free(t); return NULL; }
    if (f->type == TLAM) {
      Term *sub = subst(f->name, t->r, f->l, 0);
      term_free(f);
      term_free(t);
      t = sub;
    } else {
      Term *r = t->r;
      t->r = NULL;
      term_free(t);
      return term_new(TAPP, "", f, r);
    }
  }
  return t;
}

/* normal order reduction (reference evalBetaFull) */
static Term *nf(Term *t, int depth) {
  if (step()) { term_free(t); return NULL; }
  if (depth > MAXD || !t) { term_free(t); return NULL; }
  t = whnf(t);
  if (!t) return NULL;
  if (t->type == TLAM) {
    Term *b = nf(t->l, depth + 1);
    t->l = NULL;
    char nm[NAME];
    snprintf(nm, NAME, "%s", t->name);
    term_free(t);
    if (!b) return NULL;
    return term_new(TLAM, nm, b, NULL);
  }
  if (t->type == TAPP) {
    Term *l = t->l, *r = t->r;
    t->l = NULL; t->r = NULL;
    term_free(t);
    Term *f = nf(l, depth + 1);
    Term *a = nf(r, depth + 1);
    if (!f || !a) { term_free(f); term_free(a); return NULL; }
    return term_new(TAPP, "", f, a);
  }
  return t;
}

/* print a lambda term (structural, matching the net readback style).  Data is
   recognized on the std-library Curry encodings (reserved binder names): a
   lambda \f.\x. body spells a church numeral when named _cf/_cx and a
   boolean when named _bt/_bf; every other lambda prints as a plain lambda. */
static void pt(Term *t, int depth) {
  if (!t || depth > 3000) {
    fputs("?", stdout);
    return;
  }
  switch (t->type) {
  case TVAR:
    fputs(t->name, stdout);
    return;
  case TLAM: {
    Term *b = t->l;
    if (b && b->type == TLAM) {
      Term *body = b->l;
      if (!strncmp(t->name, "_cf", 3) && !strncmp(b->name, "_cx", 3)) {
        long k = 0;
        while (body && body->type == TAPP && body->l &&
               body->l->type == TVAR && !strcmp(body->l->name, t->name)) {
          k++;
          body = body->r;
        }
        if (body && body->type == TVAR && !strcmp(body->name, b->name)) {
          printf("%ld", k);
          return;
        }
        if (!body || body->type == TVAR) { /* erased tail => same numeral */
          printf("%ld", k);
          return;
        }
      } else if (!strncmp(t->name, "_bt", 3) && !strncmp(b->name, "_bf", 3) &&
                 body && body->type == TVAR) {
        fputs(!strcmp(body->name, t->name) ? "true" : "false", stdout);
        return;
      }
    }
    fputs("(\\", stdout);
    fputs(t->name, stdout);
    putchar(' ');
    pt(t->l, depth + 1);
    putchar(')');
    return;
  }
  case TAPP:
    putchar('(');
    pt(t->l, depth + 1);
    putchar(' ');
    pt(t->r, depth + 1);
    putchar(')');
    return;
  }
}

/* decode a closed term via the minimal normalizer; returns 0 on success */
int term_decode(Term *t) {
  steps = 0;
  Term *r = nf(term_copy(t), 0);
  if (!r) {
    if (getenv("LIN_DBG")) fprintf(stderr, "[decoder] nf failed\n");
    return 1;
  }
  pt(r, 0);
  term_free(r);
  return 0;
}