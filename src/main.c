#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include "lin.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>

static void bump_stack(void) {
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl)) return;
  rl.rlim_cur = 1L << 30;
  if (rl.rlim_max != RLIM_INFINITY && rl.rlim_cur > rl.rlim_max)
    rl.rlim_cur = rl.rlim_max;
  setrlimit(RLIMIT_STACK, &rl);
}

Def *defs;
int ndefs = 0, defcap = 0;

static long STEP_LIMIT = 1L << 24;
static int bench_mode = 0;

Def *def_find(const char *name) {
  for (int i = ndefs - 1; i >= 0; i--)
    if (!strcmp(defs[i].name, name)) return &defs[i];
  return NULL;
}

typedef struct { char (*names)[NAME]; int count, cap; } Guard;

static void guard_push(Guard *g, const char *name) {
  if (g->count >= g->cap)
    g->names = realloc(g->names, (size_t)(g->cap = g->cap ? g->cap * 2 : 64) * sizeof *g->names);
  snprintf(g->names[g->count++], NAME, "%s", name);
}

static int guard_has(Guard *g, const char *name) {
  for (int i = 0; i < g->count; i++)
    if (!strcmp(g->names[i], name)) return 1;
  return 0;
}

static Term *expand(Term *t, Guard *g) {
  if (!t) return NULL;
  if (t->type == TVAR) {
    if (guard_has(g, t->name))
      return term_new(TVAR, t->name, NULL, NULL);
    Def *d = def_find(t->name);
    if (!d) return term_new(TVAR, t->name, NULL, NULL);
    guard_push(g, d->name);
    Term *body = term_copy(d->term);
    Term *e = expand(body, g);
    term_free(body);
    g->count--;
    return e;
  }
  Term *c = term_new(t->type, t->name, NULL, NULL);
  int bound = (t->type == TLAM || t->type == TDEF);
  if (bound) guard_push(g, t->name);
  c->l = expand(t->l, g);
  if (bound) g->count--;
  c->r = expand(t->r, g);
  return c;
}

Term *expand_defs(Term *t) {
  Guard g = {0};
  Term *res = expand(t, &g);
  free(g.names);
  return res;
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
  Term *ex = expand_defs(t);
  Net net;
  net_init(&net, 1 << 16);
  if (!compile(ex, &net, err, sizeof err)) {
    printf("error: %s\n", err);
    net_free(&net);
    term_free(ex);
    return;
  }
  struct timespec t0, t1;
  long long d1 = 0, d2 = 0;
  if (bench_mode) {
    d1 = goi_det(&net);
    clock_gettime(CLOCK_MONOTONIC, &t0);
  }
  net_reduce(&net, STEP_LIMIT);
  if (bench_mode) {
    clock_gettime(CLOCK_MONOTONIC, &t1);
    d2 = goi_det(&net);
  }

  printf("=> ");
  net_print(&net);
  putchar('\n');
  if (bench_mode) {
    double ms = (t1.tv_sec - t0.tv_sec) * 1000.0 + (t1.tv_nsec - t0.tv_nsec) / 1000000.0;
    fprintf(stderr, "[bench] %ld steps | %d nodes | %.2f ms | GoI det: %lld -> %lld\n",
            net.steps, net.nn, ms, d1, d2);
  }
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
  if (ndefs >= defcap)
    defs = realloc(defs, (size_t)(defcap = defcap ? defcap * 2 : 128) * sizeof(Def));
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

static char (*loaded_paths)[PATH_MAX];
static int n_loaded = 0, loaded_cap = 0;
static char (*dir_stack)[PATH_MAX];
static int dir_sp = 0, dir_cap = 0;

static int is_already_loaded(const char *canon) {
  for (int i = 0; i < n_loaded; i++)
    if (!strcmp(loaded_paths[i], canon)) return 1;
  return 0;
}

static void mark_loaded(const char *canon) {
  if (n_loaded >= loaded_cap)
    loaded_paths = realloc(loaded_paths, (size_t)(loaded_cap = loaded_cap ? loaded_cap * 2 : 64) * sizeof *loaded_paths);
  snprintf(loaded_paths[n_loaded++], PATH_MAX, "%s", canon);
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

  if (dir_sp >= dir_cap)
    dir_stack = realloc(dir_stack, (size_t)(dir_cap = dir_cap ? dir_cap * 2 : 16) * sizeof *dir_stack);
  snprintf(dir_stack[dir_sp++], PATH_MAX, "%s", dir);

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
  Term *ex = expand_defs(first_form);
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

static int paren_balance(const char *s, int *in_str) {
  int bal = 0;
  for (int i = 0; s[i]; i++) {
    if (*in_str) {
      if (s[i] == '\\' && s[i + 1]) { i++; continue; }
      if (s[i] == '"') *in_str = 0;
      continue;
    }
    if (s[i] == ';') break;
    if (s[i] == '"') { *in_str = 1; continue; }
    if (s[i] == '(') bal++;
    else if (s[i] == ')') bal--;
  }
  return bal;
}

static void repl(void) {
  char buf[65536];
  char line[8192];
  int buf_len = 0, depth = 0, in_str = 0;
  printf("lin 0.1 - interaction combinator language\n");
  printf("commands: :type <expr>  :goi <expr>  :load <file>  :help  :q\n");
  for (;;) {
    printf(depth > 0 || in_str ? "...  " : "lin> ");
    fflush(stdout);
    if (!fgets(line, sizeof line, stdin)) break;
    size_t len = strlen(line);
    while (len && (line[len - 1] == '\n' || line[len - 1] == '\r'))
      line[--len] = 0;

    if (depth == 0 && !in_str) {
      if (!len) continue;
      if (!strcmp(line, ":q") || !strcmp(line, ":quit")) break;
      if (!strcmp(line, ":help")) {
        printf("(\\x body) lambda | (f a b) app | (let ((x v)) b) | (define n t) | 123 Scott\n");
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
    }

    int delta = paren_balance(line, &in_str);
    depth += delta;
    if (depth < 0) depth = 0;

    if (buf_len + (int)len + 2 < (int)sizeof(buf)) {
      memcpy(buf + buf_len, line, len);
      buf_len += len;
      buf[buf_len++] = '\n';
      buf[buf_len] = 0;
    }

    if (depth == 0 && !in_str) {
      parse_forms(buf, form_cb, NULL);
      buf_len = 0;
    }
  }
}

static void print_usage(const char *prog) {
  printf("usage: %s [-e expr] [-b] [-h] [-v] [files...]\n", prog);
}

int main(int argc, char **argv) {
  bump_stack();
  if (getenv("LIN_STEPS")) STEP_LIMIT = atol(getenv("LIN_STEPS"));
  const char *std = getenv("LIN_STD");
  if (!std) std = "std/std.lin";
  if (!load_file(std))
    fprintf(stderr, "warning: standard library not found at '%s'\n", std);

  int ran_eval = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) {
      print_usage(argv[0]);
      return 0;
    }
    if (!strcmp(argv[i], "-v") || !strcmp(argv[i], "--version")) {
      printf("lin 0.1 - interaction combinator language\n");
      return 0;
    }
    if (!strcmp(argv[i], "-b") || !strcmp(argv[i], "--bench")) {
      bench_mode = 1;
      continue;
    }
    if (!strcmp(argv[i], "-e") || !strcmp(argv[i], "--eval")) {
      if (i + 1 >= argc) {
        fprintf(stderr, "error: %s requires an argument\n", argv[i]);
        return 1;
      }
      parse_forms(argv[++i], form_cb, NULL);
      ran_eval = 1;
      continue;
    }
    if (argv[i][0] == '-') {
      fprintf(stderr, "unknown option: %s\n", argv[i]);
      print_usage(argv[0]);
      return 1;
    }
    if (!load_file(argv[i]))
      fprintf(stderr, "error: cannot read '%s'\n", argv[i]);
    ran_eval = 1;
  }
  if (!ran_eval) repl();
  return 0;
}