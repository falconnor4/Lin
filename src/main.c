#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include "lin.h"
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>

static void bump_stack(void) {
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl)) return;
  rl.rlim_cur = 1L << 30;
  if (rl.rlim_max != RLIM_INFINITY && rl.rlim_cur > rl.rlim_max)
    rl.rlim_cur = rl.rlim_max;
  setrlimit(RLIMIT_STACK, &rl);
}

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
  int bound = (t->type == TLAM || t->type == TDEF) && ng < 63;
  if (bound) snprintf(guard[ng], NAME, "%s", t->name);
  c->l = expand_defs(t->l, guard, ng + bound);
  c->r = expand_defs(t->r, guard, ng);
  return c;
}

void eval_form(Term *t) {
  char err[512];
  Scheme sch;
  if (t->type == TDEF || t->type == TDEFX)
    return; /* definitions handled separately in main loop */
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
  net_reduce(&net, STEP_LIMIT);
  if (getenv("LIN_DUMP")) {
    fprintf(stderr, "steps=%ld nn=%d\n", net.steps, net.nn);
    for (int i = 0; i < net.nn; i++) {
      static const char *tn[] = { "LAM", "APP", "DUP", "ERA", "ROOT" };
      fprintf(stderr, "%2d %-4s %s D=%d sc=", i, tn[net.tag[i]], net.name[i],
              net.dead[i]);
      for (int k = 0; k < net.scope[i].len; k++)
        fprintf(stderr, "%llu", (unsigned long long)net.sca[net.scope[i].off + k]);
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
      if (w.node < 0 || w.port != 0 || w.node <= i || net.dead[w.node])
        continue;
      fprintf(stderr, "   LIVE-REDEX %s%d x %s%d\n", tn[net.tag[i]], i,
              tn[net.tag[w.node]], w.node);
    }
  }
  printf("=> ");
  net_print(&net);
  putchar('\n');
  net_free(&net);
  term_free(ex);
}

/* Z = \_f. ((\_x. _f (\_v. _x _x _v)) (\_x. _f (\_v. _x _x _v))) */
static Term *y_term(void) {
  Term *xxv = term_new(TAPP, "",
                       term_new(TAPP, "", term_new(TVAR, "_x", NULL, NULL),
                                term_new(TVAR, "_x", NULL, NULL)),
                       term_new(TVAR, "_v", NULL, NULL));
  Term *lam_v = term_new(TLAM, "_v", xxv, NULL);
  Term *half = term_new(TLAM, "_x",
                        term_new(TAPP, "", term_new(TVAR, "_f", NULL, NULL), lam_v),
                        NULL);
  return term_new(TLAM, "_f", term_new(TAPP, "", half, term_copy(half)), NULL);
}

static void process_def(Term *t) {
  if (ndefs >= 1024) {
    printf("error: too many definitions\n");
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

#include <unistd.h>
#include <limits.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

static char loaded_paths[512][PATH_MAX];
static int n_loaded = 0;
static char dir_stack[64][PATH_MAX];
static int dir_sp = 0;

static int is_already_loaded(const char *canon) {
  for (int i = 0; i < n_loaded; i++)
    if (!strcmp(loaded_paths[i], canon)) return 1;
  return 0;
}

static void mark_loaded(const char *canon) {
  if (n_loaded < 512) {
    snprintf(loaded_paths[n_loaded++], PATH_MAX, "%s", canon);
  }
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

static int resolve_path(const char *rel, char *out, size_t out_sz) {
  (void)out_sz;
  char cand[PATH_MAX];
  if (rel[0] != '/' && dir_sp > 0) {
    snprintf(cand, sizeof cand, "%s/%s", dir_stack[dir_sp - 1], rel);
    if (access(cand, R_OK) == 0 && realpath(cand, out)) return 1;
  }
  if (access(rel, R_OK) == 0 && realpath(rel, out)) return 1;
  const char *std_dir = getenv("LIN_STD_DIR");
  if (!std_dir) std_dir = "std";
  snprintf(cand, sizeof cand, "%s/%s", std_dir, rel);
  if (access(cand, R_OK) == 0 && realpath(cand, out)) return 1;
  return 0;
}

static int load_file(const char *path);

static void form_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) {
    printf("error: %s\n", perr);
    return;
  }
  if (t->type == TLOAD) {
    if (!load_file(t->name))
      printf("error: cannot load '%s'\n", t->name);
    term_free(t);
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

static int load_file(const char *path) {
  char full[PATH_MAX];
  if (!resolve_path(path, full, sizeof full)) return 0;
  if (is_already_loaded(full)) return 1;
  mark_loaded(full);

  char *src = read_file(full);
  if (!src) return 0;

  char dir[PATH_MAX];
  snprintf(dir, sizeof dir, "%s", full);
  char *last_slash = strrchr(dir, '/');
  if (last_slash) *last_slash = '\0';
  else snprintf(dir, sizeof dir, ".");

  if (dir_sp < 64) {
    snprintf(dir_stack[dir_sp++], PATH_MAX, "%s", dir);
  }

  parse_forms(src, form_cb, NULL);

  if (dir_sp > 0) dir_sp--;
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
  bump_stack();
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