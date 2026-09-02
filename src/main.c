#include "lin.h"
#include <stdlib.h>
#include <string.h>

Def defs[1024];
int ndefs = 0;

static long STEP_LIMIT = 1L << 24;

Def *def_find(const char *name) {
  for (int i = ndefs - 1; i >= 0; i--)
    if (!strcmp(defs[i].name, name)) return &defs[i];
  return NULL;
}

/* inline definitions at use sites; guard prevents recursive expansion,
   binders shadow definition names */
Term *expand_defs(Term *t, char guard[][NAME], int ng) {
  if (!t) return NULL;
  if (t->type == TVAR) {
    for (int i = 0; i < ng; i++)
      if (!strcmp(guard[i], t->name))
        return term_new(TVAR, t->name, NULL, NULL);
    Def *d = def_find(t->name);
    if (!d) return term_new(TVAR, t->name, NULL, NULL);
    if (ng >= 63) {
      fprintf(stderr, "error: expansion too deep\n");
      exit(1);
    }
    snprintf(guard[ng], NAME, "%s", d->name);
    Term *body = term_copy(d->term);
    Term *e = expand_defs(body, guard, ng + 1);
    term_free(body);
    return e;
  }
  Term *c = term_new(t->type, t->name, NULL, NULL);
  int bound = (t->type == TLAM || t->type == TLET) && ng < 63;
  if (bound) snprintf(guard[ng], NAME, "%s", t->name);
  if (t->type == TLET) {
    char saved[NAME];
    snprintf(saved, NAME, "%s", guard[ng]);
    c->l = expand_defs(t->l, guard, ng);
    snprintf(guard[ng], NAME, "%s", saved);
    c->r = expand_defs(t->r, guard, ng + bound);
  } else {
    c->l = expand_defs(t->l, guard, ng + bound);
    c->r = expand_defs(t->r, guard, ng + bound);
  }
  return c;
}

void eval_form(Term *t) {
  Scheme sch;
  char err[512];
  if (!type_check(t, &sch, err, sizeof err)) {
    printf("error: %s\n", err);
    return;
  }
  char guard[64][NAME];
  Term *ex = expand_defs(t, guard, 0);
  Net net;
  net_init(&net, 1 << 16);
  if (!compile(ex, &net, err, sizeof err)) {
    printf("error: %s\n", err);
    net_free(&net);
    term_free(ex);
    return;
  }
  if (getenv("LIN_FULL")) {
    net_reduce_full(&net, STEP_LIMIT);
  } else {
    net_reduce_whnf(&net, STEP_LIMIT);
  }
  if (getenv("LIN_DUMP")) {
    for (int i = 0; i < net.nn; i++) {
      static const char *tn[] = { "LAM", "APP", "DUP", "ERA", "ROOT" };
      fprintf(stderr, "%2d %-4s %s", i, tn[net.tag[i]], net.name[i]);
      for (int p = 0; p < 3; p++) {
        Port w = net.wire[i * 3 + p];
        if (w.node >= 0) fprintf(stderr, "  [%d]<->%d.%d", p, w.node, w.port);
      }
      fprintf(stderr, "\n");
    }
    for (int i = 0; i < net.nn; i++) {
      static const char *tn[] = { "LAM", "APP", "DUP", "ERA", "ROOT" };
      Port w = net.wire[i * 3 + 0];
      if (net.tag[i] == ROOT || net.dead[i]) continue;
      if (w.node < 0 || w.port != 0 || w.node <= i || net.dead[w.node]) continue;
      int a = net.tag[i], b = net.tag[w.node];
      if ((a == LAM && b == APP) || (a == APP && b == LAM) ||
          (a == DUP && b == DUP))
        fprintf(stderr, "   LIVE-REDEX %s%d x %s%d\n", tn[a], i, tn[b], w.node);
    }
  }
  if (getenv("LIN_DBG")) {
    fprintf(stderr, "EXIT_DUMP\n");
    /* recurse with a small stack-explicit printer to see NULL children */
    typedef struct { Term *t; int depth; } S;
    S *st = malloc(sizeof(S) * 100000);
    int sp = 0;
    st[sp++] = (S){ ex, 0 };
    while (sp) {
      S s = st[--sp];
      Term *x = s.t;
      fprintf(stderr, "%*s", s.depth * 2, "");
      if (!x) { fprintf(stderr, "NULL\n"); continue; }
      fprintf(stderr, "(%d%s%s", x->type,
              x->type == TVAR || x->type == TLAM ? " " : "",
              x->type == TVAR || x->type == TLAM ? x->name : "");
      if (x->l) st[sp++] = (S){ x->l, s.depth + 1 };
      else if (x->type != TNUM && x->type != TVAR)
        fprintf(stderr, " %%%dLNULL", x->type);
      if (x->r) st[sp++] = (S){ x->r, s.depth + 1 };
      else if (x->type != TNUM && x->type != TVAR)
        fprintf(stderr, " %%%dRNULL", x->type);
      fprintf(stderr, ")\n");
    }
    free(st);
  }
  printf("=> ");
  if (net_print(&net)) {
    /* irreducible croissant normal form: fall back to a term-level
       normal-order reduction of the expanded program */
    char *s = term_eval_string(ex);
    fputs(s, stdout);
    free(s);
  }
  putchar('\n');
  net_free(&net);
  term_free(ex);
}

/* Y = \f. ((\x. f (x x)) (\x. f (x x))) */
static Term *y_term(void) {
  Term *half = term_new(
      TLAM, "x",
      term_new(TAPP, "", term_new(TVAR, "f", NULL, NULL),
               term_new(TAPP, "", term_new(TVAR, "x", NULL, NULL),
                        term_new(TVAR, "x", NULL, NULL))),
      NULL);
  Term *half2 = term_new(
      TLAM, "x",
      term_new(TAPP, "", term_new(TVAR, "f", NULL, NULL),
               term_new(TAPP, "", term_new(TVAR, "x", NULL, NULL),
                        term_new(TVAR, "x", NULL, NULL))),
      NULL);
  return term_new(TLAM, "f", term_new(TAPP, "", half, half2), NULL);
}

static void process_def(Term *t) {
  if (ndefs >= 1024) {
    printf("error: too many definitions\n");
    return;
  }
  if (def_find(t->name)) {
    printf("error: redefinition of '%s'\n", t->name);
    return;
  }
  char err[512];
  Scheme sch;
  int rec = term_refs(t->l, t->name);
  int ok;
  if (t->type == TDEFX) {
    sch = scheme_all((Type *)t->annot);
    ok = 1;
  } else {
    ok = rec ? type_check_rec(t->name, t->l, &sch, err, sizeof err)
             : type_check(t->l, &sch, err, sizeof err);
  }
  if (!ok) {
    printf("error: %s\n", err);
    return;
  }
  Def *d = &defs[ndefs++];
  snprintf(d->name, NAME, "%s", t->name);
  d->sch = sch;
  d->typed = 1;
  if (rec) {
    Term *lam = term_new(TLAM, t->name, t->l, NULL);
    t->l = NULL;
    d->term = term_new(TAPP, "", y_term(), lam);
  } else {
    d->term = t->l;
    t->l = NULL;
  }
}

static void form_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) {
    printf("error: %s\n", perr);
    return;
  }
  if (t->type == TDEF || t->type == TDEFX) {
    process_def(t);
    term_free(t);
    return;
  }
  eval_form(t);
  term_free(t);
}

static char *read_file(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) return NULL;
  fseek(f, 0, SEEK_END);
  long sz = ftell(f);
  fseek(f, 0, SEEK_SET);
  char *buf = malloc(sz + 1);
  if (!buf || fread(buf, 1, sz, f) != (size_t)sz) {
    fclose(f);
    free(buf);
    return NULL;
  }
  buf[sz] = 0;
  fclose(f);
  return buf;
}

static int load_file(const char *path) {
  char *src = read_file(path);
  if (!src) return 0;
  parse_forms(src, form_cb, NULL);
  free(src);
  return 1;
}

static Term *first_form;

static void cap_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) {
    printf("error: %s\n", perr);
    return;
  }
  if (!first_form) first_form = t;
  else term_free(t);
}

static void do_type(const char *expr) {
  first_form = NULL;
  parse_forms(expr, cap_cb, NULL);
  if (!first_form) return;
  Scheme sch;
  char err[512];
  if (type_check(first_form, &sch, err, sizeof err)) {
    scheme_print(&sch);
    putchar('\n');
  } else {
    printf("error: %s\n", err);
  }
  term_free(first_form);
}

static void do_goi(const char *expr) {
  first_form = NULL;
  parse_forms(expr, cap_cb, NULL);
  if (!first_form) return;
  char guard[64][NAME];
  Term *ex = expand_defs(first_form, guard, 0);
  Net net;
  net_init(&net, 1 << 16);
  char err[512];
  if (compile(ex, &net, err, sizeof err)) {
long long d1 = goi_det(&net);
    net_reduce(&net, STEP_LIMIT);
    long long d2 = goi_det(&net);
    printf("goi: before %lld, after %lld\n", d1, d2);
  } else {
    printf("error: %s\n", err);
  }
  net_free(&net);
  term_free(ex);
  term_free(first_form);
}

static void repl(void) {
  char line[8192];
  printf("lin 0.1 - interaction combinator language\n");
  printf("commands: :type <expr>  :goi <expr>  :load <file>  :help  :q\n");
  for (;;) {
    printf("lin> ");
    fflush(stdout);
    if (!fgets(line, sizeof line, stdin)) break;
    size_t len = strlen(line);
    while (len && (line[len - 1] == '\n' || line[len - 1] == '\r'))
      line[--len] = 0;
    if (!len) continue;
    if (!strcmp(line, ":q") || !strcmp(line, ":quit")) break;
    if (!strcmp(line, ":help")) {
      printf("  (\\x body)         lambda (also: lambda, lam, U+03BB)\n");
      printf("  (f a b ...)       application, left associative\n");
      printf("  (let ((x v)) b)   local binding\n");
      printf("  (define n t)      top-level definition (auto Y for recursion)\n");
      printf("  (define! n T t)   trusted definition with type annotation T\n");
      printf("                    (types: -> ( ) num bool, lowercase = var)\n");
      printf("  123               Church numeral literal\n");
      printf("  ; comment\n");
      continue;
    }
    if (!strncmp(line, ":load ", 6)) {
      if (!load_file(line + 6)) printf("error: cannot read '%s'\n", line + 6);
      continue;
    }
    if (!strncmp(line, ":type ", 6)) {
      do_type(line + 6);
      continue;
    }
    if (!strncmp(line, ":goi ", 5)) {
      do_goi(line + 5);
      continue;
    }
    parse_forms(line, form_cb, NULL);
  }
}

int main(int argc, char **argv) {
  if (getenv("LIN_STEPS")) STEP_LIMIT = atol(getenv("LIN_STEPS"));
  const char *std = getenv("LIN_STD");
  if (!std) std = "std/std.lin";
  if (!load_file(std))
    fprintf(stderr, "warning: standard library not found at '%s'\n", std);
  if (argc > 1) {
    for (int i = 1; i < argc; i++)
      if (!load_file(argv[i]))
        fprintf(stderr, "error: cannot read '%s'\n", argv[i]);
    return 0;
  }
  repl();
  return 0;
}
