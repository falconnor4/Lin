#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include "lin.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/resource.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static void bump_stack(void) {
  struct rlimit rl;
  if (!getrlimit(RLIMIT_STACK, &rl)) {
    rl.rlim_cur = (rl.rlim_max != RLIM_INFINITY && (1L << 30) > rl.rlim_max) ? rl.rlim_max : (1L << 30);
    setrlimit(RLIMIT_STACK, &rl);
  }
}

Def *defs;
int ndefs = 0, defcap = 0;

static long STEP_LIMIT = 1L << 24;
/* Bounded so `lin build` cannot hang on a program that does not terminate at build
   time: the residual is then simply "what the compiler did not finish". */
static long AOT_STEP_LIMIT = 1L << 22;
static int bench_mode = 0;

char curr_ns[NAME] = "";
char open_ns[32][NAME];
int n_open_ns = 0;

void set_namespace(const char *name) {
  if (!name || !*name || !strcmp(name, "_") || !strcmp(name, "root")) curr_ns[0] = '\0';
  else snprintf(curr_ns, sizeof curr_ns, "%s", name);
}
void open_namespace(const char *name) {
  if (!name || !*name) return;
  for (int i = 0; i < n_open_ns; i++) if (!strcmp(open_ns[i], name)) return;
  if (n_open_ns < 32) snprintf(open_ns[n_open_ns++], NAME, "%s", name);
}
static Def *lookup_raw(const char *s) {
  for (int i = ndefs - 1; i >= 0; i--) if (!strcmp(defs[i].name, s)) return &defs[i];
  return NULL;
}
Def *def_find(const char *name) {
  char qn[NAME * 2 + 2]; Def *d;
  if (strchr(name, '.')) return lookup_raw(name);
  if (curr_ns[0]) { snprintf(qn, sizeof qn, "%s.%s", curr_ns, name); if ((d = lookup_raw(qn))) return d; }
  for (int o = n_open_ns - 1; o >= 0; o--) {
    snprintf(qn, sizeof qn, "%s.%s", open_ns[o], name);
    if ((d = lookup_raw(qn))) return d;
  }
  return lookup_raw(name);
}

typedef struct { char (*names)[NAME]; int count, cap; } Guard;
static void guard_push(Guard *g, const char *name) {
  if (g->count >= g->cap) g->names = realloc(g->names, (size_t)(g->cap = g->cap ? g->cap * 2 : 64) * sizeof *g->names);
  snprintf(g->names[g->count++], NAME, "%s", name);
}
static int guard_has(Guard *g, const char *name) {
  for (int i = 0; i < g->count; i++) if (!strcmp(g->names[i], name)) return 1;
  return 0;
}

/* !=0 while def_precompile reduces an open body.  It is the core's one statement to drivers about precompilation:
   the operands here are free variables that never become concrete, so a driver must not fold (a baked closure
   would capture a stale value).  Which redexes that affects is the driver's business. */
int lin_precompile_depth = 0;
/* !=0 while the AOT build is partially evaluating the program.  Distinct from
   lin_precompile_depth: that one says "operands are free variables"; this one says
   "this reduction is happening at BUILD time, so nothing the program would OBSERVE at
   run time may be baked into the artifact".  A driver that folds a probe like
   (lin_folds)/(lin_folded) would otherwise freeze the build-time answer into the
   .line file and the program could never observe anything else. */
int lin_build_depth = 0;

/* The one pipeline: a term becomes a reduced net the same way in every mode — expand defines,
   (AOT only) optimize, compile, run the core to the mode's limit.  `depth` raises the single
   build-time marker the reduction happens under.  Returns steps run, or -1 if it did not compile. */
enum { DEPTH_RUN = 0, DEPTH_PRECOMPILE = 1, DEPTH_BUILD = 2 };
static long reduce_term(Term *t, Net *net, int optimize, int depth, long limit, int *compiled, char *err, int errsz) {
  Term *ex = expand_defs(t);
  Term *opt = optimize ? egraph_optimize(ex) : ex;
  int ok = compile(opt, net, err, errsz);
  if (opt != ex) term_free(opt);
  if (!ok) { term_free(ex); return -1; }
  if (compiled) *compiled = net->nn;
  if (depth == DEPTH_PRECOMPILE) lin_precompile_depth++;
  else if (depth == DEPTH_BUILD) lin_build_depth++;
  long steps = net_reduce(net, limit);
  if (depth == DEPTH_PRECOMPILE) lin_precompile_depth--;
  else if (depth == DEPTH_BUILD) lin_build_depth--;
  term_free(ex);
  return steps;
}

/* Non-recursive define: evaluate once and cache the reduced net so each reference clones it; recursive/too-big bodies keep the textual path. */
static void def_precompile(Def *d) {
  /* A build-time decision, not a rule: a candidate may ask for every define to stay textual. */
  if (getenv("LIN_PRECOMPILE") && !strcmp(getenv("LIN_PRECOMPILE"), "0")) return;
  if (d->comp_tried) return;
  d->comp_tried = 1;
  if (d->rec) return;
  char err[512]; Net src; net_init(&src, 1 << 14);
  long full = reduce_term(d->term, &src, 0, DEPTH_PRECOMPILE, STEP_LIMIT, NULL, err, sizeof err);
  /* A driver that claimed a redex it could not materialise here leaves the body not-a-value: β went on to destroy
     a closure the driver would have folded, so the baked net is broken for composed use.  Decline the cache and
     keep the def textual.  Once Move 3 chooses precompile-vs-textual AOT this try-and-decline becomes a decision
     made up front; the *signal* stays the same generic one, so no driver policy leaks into the core either way. */
  if (full < 0 || full >= STEP_LIMIT || lin_any_pending(&src)) { net_free(&src); return; }
  d->compiled = net_copy(&src); net_free(&src);
}

static Term *expand(Term *t, Guard *g) {
  if (!t) return NULL;
  if (t->type == TVAR) {
    if (guard_has(g, t->name)) return term_new(TVAR, t->name, NULL, NULL);
    Def *d = def_find(t->name);
    if (!d) return term_new(TVAR, t->name, NULL, NULL);
    if (!d->expanded) {
      guard_push(g, d->name); Term *body = term_copy(d->term);
      d->expanded = expand(body, g); term_free(body); g->count--;
    }
    def_precompile(d);
    if (d->compiled) return term_new(TDEF, d->name, NULL, NULL); /* value marker */
    return term_copy(d->expanded);
  }
  Term *c = term_new(t->type, t->name, NULL, NULL);
  int bound = (t->type == TLAM || t->type == TDEF);
  if (bound) guard_push(g, t->name);
  c->l = expand(t->l, g); if (bound) g->count--;
  c->r = expand(t->r, g); return c;
}

Term *expand_defs(Term *t) {
  Guard g = {0}; Term *res = expand(t, &g); free(g.names); return res;
}

/* Benchmark accounting.  `eval_form` reduces the net *before* its
   recursion-sentinel check, so `run_and_report` used to re-reduce an
   already-reduced net and its timer always read 0.00 ms while `net->steps`
   showed the real total.  The reduction that happens is recorded here instead,
   and the effect-continuation re-reductions in `net_run_io` are added to it, so
   the reported time covers getting the net to a value (not compile/readback). */
static int bench_measured;            /* a caller already reduced and timed it */
static double bench_ms;
static long long bench_goi0, bench_goi1;

static double ms_since(struct timespec a, struct timespec b) {
  return (b.tv_sec - a.tv_sec) * 1000.0 + (b.tv_nsec - a.tv_nsec) / 1000000.0;
}

static void run_and_report(Net *net) {
  struct timespec t0, t1;
  if (!bench_measured) {                 /* nobody reduced this net yet: do it here */
    if (bench_mode) {
      bench_goi0 = goi_det(net); clock_gettime(CLOCK_MONOTONIC, &t0);
      net_reduce(net, STEP_LIMIT);
      clock_gettime(CLOCK_MONOTONIC, &t1); bench_goi1 = goi_det(net);
      bench_ms = ms_since(t0, t1);
    } else {
      net_reduce(net, STEP_LIMIT);
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &t0);
  int no_io = !net_run_io(net, STEP_LIMIT);
  clock_gettime(CLOCK_MONOTONIC, &t1);
  if (no_io) { printf("=> "); net_print(net); putchar('\n'); }
  if (bench_mode) {
    fprintf(stderr, "[bench] %ld steps | %d nodes | %.2f ms | GoI det: %lld -> %lld\n",
            net->steps, net->nn, bench_ms + ms_since(t0, t1), bench_goi0, bench_goi1);
    bench_measured = 0;
  }
}

/* (recursion builders defined below eval_form; forward decls) */
static const char REC_SENTINEL[];
static int lam_arity(Term *t);
static Term *build_bound_rec(const char *name, Term *body, int k);

/* Is a node named `nm` alive and reachable from ROOT?  Detects the `_rec` recursion sentinel surviving a truncated run (depth exceeded the bound). */
static int net_has_reachable(Net *net, const char *nm) {
  if (!nm) return 0;
  unsigned char *reach = malloc((size_t)(net->nn + 1));
  memset(reach, 0, (size_t)(net->nn + 1));
  int *q = malloc((size_t)(net->nn + 1) * sizeof(int)); int qh = 0, qt = 1; q[0] = 0; reach[0] = 1;
  int found = 0;
  while (qh < qt) { int u = q[qh++];
    if (net->name[u] && !strcmp(net->name[u], nm)) { found = 1; break; }
    for (int p = 0; p < 3; p++) { Port w = net->wire[u*3+p];
      if (w.node >= 0 && w.node < net->nn && !net->dead[w.node] && !reach[w.node]) { reach[w.node] = 1; q[qt++] = w.node; } } }
  free(reach); free(q); return found;
}

/* Double every recursive def's unravelling bound and clear its expansion so the next attempt compiles a deeper chain (O(log depth) re-evaluations). */
static int widen_recursion(void) {
  int wid = 0;
  for (int i = 0; i < ndefs; i++) if (defs[i].rec && defs[i].rec_body) {
    defs[i].rec_k = defs[i].rec_k < (1 << 22) ? defs[i].rec_k * 2 : defs[i].rec_k;
    term_free(defs[i].term);
    defs[i].term = build_bound_rec(defs[i].rec_name, defs[i].rec_body, defs[i].rec_k);
    wid = 1;
  }
  /* EVERY def's cached expansion may have inlined a recursive body's unrolling, not just
     the recursive defs themselves: `num.eq` merely *calls* `num._peq`, so clearing only
     `defs[i].rec` left its expansion pinned to the old depth.  The net then came out
     byte-identical on every round, the `_rec` sentinel never cleared, and widening doubled
     the bound forever -- re-expanding a larger chain each time (96ms, 192ms, 372ms ...
     21.8s) for no change in the result.  Clearing all of them is what makes the wider
     bound actually reach the compiled graph. */
  if (wid) for (int i = 0; i < ndefs; i++) {
    term_free(defs[i].expanded); defs[i].expanded = NULL;
    /* A precompiled net is the other place the old depth can hide, and it is the one that
       matters when NO driver is loaded: with nothing to report the body un-materialised,
       a def like `num.eq` IS baked, at whatever k was current, and clearing only the term
       expansion then leaves widening with nothing to widen.  Baking is a cache, so drop
       it and let the next use bake again at the new depth. */
    if (defs[i].compiled) { net_free(defs[i].compiled); free(defs[i].compiled); defs[i].compiled = NULL; }
    defs[i].comp_tried = 0;
  }
  return wid;
}

void eval_form(Term *t) {
  char err[512]; Scheme sch;
  if (t->type == TDEF || t->type == TDEFX || t->type == TNS || t->type == TOPEN) return;
  if (!type_check(t, &sch, err, sizeof err)) { printf("error: %s\n", err); return; }
  for (int round = 0; round < 16; round++) {
    Term *ex = expand_defs(t); Net net; net_init(&net, 1 << 16);
    if (!compile(ex, &net, err, sizeof err)) { printf("error: %s\n", err); net_free(&net); term_free(ex); return; }
    struct timespec b0, b1;
    bench_measured = bench_mode;
    if (bench_mode) { bench_goi0 = goi_det(&net); clock_gettime(CLOCK_MONOTONIC, &b0); }
    net_reduce(&net, STEP_LIMIT);
    if (bench_mode) { clock_gettime(CLOCK_MONOTONIC, &b1); bench_goi1 = goi_det(&net); bench_ms = ms_since(b0, b1); }
    if (net_has_reachable(&net, REC_SENTINEL)) {   /* self-recursion exceeded k */
      net_free(&net); term_free(ex);
      if (!widen_recursion()) { printf("error: recursion depth exceeded unravelling bound\n"); return; }
      continue;
    }
    run_and_report(&net); net_free(&net); term_free(ex); return;
  }
}

/* Count the arity (leading \x binders) of a function body so the bounded self-unravelling base term gets the right number of slots. */
static int lam_arity(Term *t) {
  int k = 0;
  while (t && t->type == TLAM) { k++; t = t->l; }
  return k;
}

static const char REC_SENTINEL[] = "_rec";
/* Dynamic (widening) self-recursion: replace the stranding Y-fixpoint with a *finite* unravelling `Y_k f = f (... base ...)` (k apps) whose innermost `base` carries the reserved `_rec` sentinel; confluent for depth<=k, and if depth exceeds k the sentinel survives ROOT-reachable so eval_form re-drives with doubled k */
static Term *build_bound_rec(const char *name, Term *body, int k) {
  int ar = lam_arity(body);
  Term *zero = term_new(TLAM, REC_SENTINEL, term_new(TLAM, REC_SENTINEL, term_new(TVAR, REC_SENTINEL, 0, 0), 0), 0);
  Term *base = zero;
  for (int i = 0; i < ar; i++) { char a[NAME]; snprintf(a, sizeof a, "_r%d", i); base = term_new(TLAM, a, base, NULL); }
  Term *cur = base;
  for (int i = 0; i < k; i++) {
    Term *f = term_new(TLAM, name, term_copy(body), NULL);
    cur = term_new(TAPP, "", f, cur);
  }
  return cur;
}

static void qualify_free(Term *t, Guard *b) {
  if (!t) return;
  if (t->type == TVAR && !strchr(t->name, '.') && !guard_has(b, t->name) && curr_ns[0]) {
    char qn[NAME * 2 + 2]; snprintf(qn, sizeof qn, "%s.%s", curr_ns, t->name);
    if (lookup_raw(qn)) { strncpy(t->name, qn, NAME - 1); t->name[NAME - 1] = 0; }
  }
  int bound = (t->type == TLAM);
  if (bound) guard_push(b, t->name);
  qualify_free(t->l, b); qualify_free(t->r, b);
  if (bound) b->count--;
}

/* (datatype Name (Ctor f...) ...): Scott-encode each constructor C_i (\f1..\fk \d0..\d_{m-1}).  Each becomes an ordinary inferred def, so it type-checks like hand-written Scott encoding */
static void process_def(Term *t);
static Term *scott_ctor(const char *dn, int idx, Term *fields, int m) {
  (void)dn;
  char dslot[NAME]; snprintf(dslot, sizeof dslot, "_d%d", idx);
  /* curried application (d_idx f1 f2 ...) */
  Term *app = term_new(TVAR, dslot, NULL, NULL);
  for (Term *f = fields; f; f = f->r) app = term_new(TAPP, "", app, term_new(TVAR, f->name, NULL, NULL));
  /* dispatch binders are innermost: \f1..\fk \d0..\d_{m-1} (d_i f1..fk) */
  Term *lam = app;
  for (int i = m - 1; i >= 0; i--) { char dn2[NAME]; snprintf(dn2, sizeof dn2, "_d%d", i); lam = term_new(TLAM, dn2, lam, NULL); }
  char (*fs)[NAME] = NULL; int nf = 0, cap = 0;
  for (Term *f = fields; f; f = f->r) { fs = realloc(fs, (size_t)(cap = cap ? cap * 2 : 8) * sizeof *fs); snprintf(fs[nf++], NAME, "%s", f->name); }
  for (int i = nf - 1; i >= 0; i--) lam = term_new(TLAM, fs[i], lam, NULL);
  free(fs);
  return lam;
}

/* Substitute a datatype's declared type-param references (TPARAM, `id` = param
   index) in a constructor field type with the head's concrete param variables. */
static Type *resolve_dt_type(Type *ty, Type **params) {
  if (!ty) return type_var();                       /* bare (untyped) field */
  if (ty->kind == TPARAM) return params[ty->id];    /* datatype type param -> head var */
  if (ty->kind == TARROW) return type_arrow(resolve_dt_type(ty->a, params), resolve_dt_type(ty->b, params));
  if (ty->kind == TARG) return type_arg(resolve_dt_type(ty->a, params));
  if (ty->kind == TNOM) {
    Type *n = type_nominal(ty->name); Type **cur = &n->a;
    for (Type *k = ty->a; k; k = k->b) { *cur = type_arg(resolve_dt_type(k->a, params)); cur = &(*cur)->b; }
    return n;
  }
  return ty;                                        /* TVR / TLINK */
}
static void process_datatype(Term *t) {
  int arity = (t->annot) ? (int)(intptr_t)t->annot : 0;    /* (datatype (Name p..) ..) arity; default 0 */
  nominal_register(t->name, arity);                         /* declare `Name` nominal with arity */
  int m = 0; for (Term *c = t->l; c; c = c->r) m++;
  int idx = 0;
  for (Term *c = t->l; c; c = c->r, idx++) {
    Term *lam = scott_ctor(t->name, idx, c->l, m);
    /* constructor type: fresh-params -> Name p1..pk.  A field with a declared
       type (annot) contributes that type (param refs resolved); an untyped field
       (no annot) contributes a fresh polymorphic var. */
    Type *head = type_nominal(t->name); Type **hp = &head->a;
    Type *params[16];
    for (int ip = 0; ip < arity && ip < 16; ip++) { params[ip] = type_var(); *hp = type_arg(params[ip]); hp = &(*hp)->b; }
    Type *ct = head;
    Type *args[16]; int nf = 0;
    for (Term *f = c->l; f; f = f->r) if (nf < 16) args[nf++] = resolve_dt_type(f->annot, params);
    for (int i = nf - 1; i >= 0; i--) ct = type_arrow(args[i], ct);  /* fields left-to-right */
    Term *def = term_new(TDEFX, c->name, lam, NULL); def->annot = ct;
    process_def(def);                                   /* takes ownership of lam */
  }
}

static void process_def(Term *t) {
  if (ndefs >= defcap) defs = realloc(defs, (size_t)(defcap = defcap ? defcap * 2 : 128) * sizeof(Def));
  char err[512]; Scheme sch;
  int rec = term_refs(t->l, t->name);
  int ok = (t->type == TDEFX) ? (sch = scheme_all((Type *)t->annot), 1)
           : rec ? type_check_rec(t->name, t->l, &sch, err, sizeof err)
                 : type_check(t->l, &sch, err, sizeof err);
  if (!ok) { printf("error: %s\n", err); return; }
  Guard b = {0}; qualify_free(t->l, &b); free(b.names);
  Def *d = &defs[ndefs++];
  if (curr_ns[0] && !strchr(t->name, '.')) {
    char qn[NAME * 2 + 2]; snprintf(qn, sizeof qn, "%s.%s", curr_ns, t->name);
    strncpy(d->name, qn, NAME - 1); d->name[NAME - 1] = 0;
  } else {
    strncpy(d->name, t->name, NAME - 1); d->name[NAME - 1] = 0;
  }
  d->sch = sch; d->typed = 1; d->rec = rec;
  if (rec) {
    /* Unravelling bound: nested recursive defines multiply k^depth, so k is the multiplier on
       the whole front end.  Depth is unknowable statically but need not be guessed
       pessimistically -- `widen_recursion` doubles k and recompiles if the `_rec` sentinel
       survives, so a small k is correct and only programs that recurse deeper pay for it.
       NOT a sound optimization axis below 6: the AOT candidate search (`LIN_AOT_SEARCH=1`) found
       k = 4 the byte winner on every program tried (`selfrecursion.lin` 21,608 B against 55,899 B),
       but at k = 4 `test/selfrecursion.lin` returns 0 for `(fact 3)` where the answer is 6 -- the
       unravelling ran out and the `_rec` sentinel was not detected, so no widening fired and a
       wrong value was returned silently.  A build-time search may not trade correctness for bytes,
       so the bound stays 6 and DESIGN.md 11.2 records the hazard.  LIN_REC_K overrides. */
    d->rec_k = getenv("LIN_REC_K") ? atoi(getenv("LIN_REC_K")) : 6;
    if (d->rec_k < 1) d->rec_k = 1;
    d->rec_body = t->l;                                /* keep body for widening */
    /* The binder must carry the name the body's SELF-REFERENCES actually use, which is
       `t->name` and NOT the namespace-qualified `d->name`: qualify_free ran before this
       def existed, so `lookup_raw("num._peq")` was still NULL and the self-reference was
       never rewritten.  Widening used to rebuild with the qualified name, producing a
       chain whose binders no longer matched the body ("unbound variable '_peq'"). */
    snprintf(d->rec_name, NAME, "%s", t->name);
    d->term = build_bound_rec(d->rec_name, t->l, d->rec_k);
  } else {
    d->rec_k = 0; d->rec_body = NULL; d->rec_name[0] = 0; d->term = t->l;
  }
  d->expanded = NULL; d->compiled = NULL; d->comp_tried = 0;
  t->l = NULL;
}

#include <unistd.h>
#include <limits.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

static char (*loaded_paths)[PATH_MAX];
static int n_loaded = 0, loaded_cap = 0, dir_sp = 0, dir_cap = 0;
static char (*dir_stack)[PATH_MAX];

static int is_already_loaded(const char *canon) {
  for (int i = 0; i < n_loaded; i++) if (!strcmp(loaded_paths[i], canon)) return 1;
  return 0;
}
static void mark_loaded(const char *canon) {
  if (n_loaded >= loaded_cap) loaded_paths = realloc(loaded_paths, (size_t)(loaded_cap = loaded_cap ? loaded_cap * 2 : 64) * sizeof *loaded_paths);
  snprintf(loaded_paths[n_loaded++], PATH_MAX, "%s", canon);
}

static char *read_file(const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) return NULL;
  fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET);
  char *buf = malloc((size_t)sz + 1);
  if (!buf || fread(buf, 1, (size_t)sz, f) != (size_t)sz) { fclose(f); free(buf); return NULL; }
  buf[sz] = 0; fclose(f); return buf;
}

static int resolve_path(const char *rel, char *out, size_t out_sz) {
  (void)out_sz;
  char cand[PATH_MAX];
  const char *std_dir = getenv("LIN_STD_DIR") ?: "std";
  const char *sub = !strncmp(rel, "std/", 4) ? rel + 4 : rel;
  /* A `std/`-prefixed load names a standard-library module.  When LIN_STD_DIR is
     explicitly configured (e.g. a packaged /nix/store std), that configured dir
     MUST win over a coincidental ./std sitting in the process CWD — otherwise a
     checkout run overrides the configured std with a local one, mixing two stds
     and stranding private defs (e.g. num._padd unbound when a second num.lin is
     loaded on top of the configured one).  So resolve `std/...` against
     LIN_STD_DIR first; a plain (non-`std/`) relative load still falls through to
     the CWD / loading-file-relative lookup below. */
  if (rel[0] != '/' && !strncmp(rel, "std/", 4)) {
    snprintf(cand, sizeof cand, "%s/%s", std_dir, sub);
    if (access(cand, R_OK) == 0 && realpath(cand, out)) return 1;
  }
  if (rel[0] != '/' && dir_sp > 0) {
    snprintf(cand, sizeof cand, "%s/%s", dir_stack[dir_sp - 1], rel);
    if (access(cand, R_OK) == 0 && realpath(cand, out)) return 1;
  }
  if (access(rel, R_OK) == 0 && realpath(rel, out)) return 1;
  snprintf(cand, sizeof cand, "%s/%s", std_dir, sub);
  if (access(cand, R_OK) == 0 && realpath(cand, out)) return 1;
  return 0;
}

static int load_file(const char *path);
static void load_std(void) {
  const char *std = getenv("LIN_STD") ? getenv("LIN_STD") : "std/std.lin";
  if (!load_file(std)) fprintf(stderr, "warning: standard library not found at '%s'\n", std);
}

static int building = 0;
static Term *build_term = NULL;

static int run_line_file(const char *path) {
  Net net; if (!net_load_line(&net, path)) return 0;
  run_and_report(&net); net_free(&net); return 1;
}

static void export_namespace(const char *name);   /* (export <ns>) re-export */
static void form_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) { printf("error: %s\n", perr); return; }
  if (t->type == TLOAD) { if (!load_file(t->name)) printf("error: cannot load '%s'\n", t->name); }
  else if (t->type == TNS) set_namespace(t->name);
  else if (t->type == TOPEN) open_namespace(t->name);
  else if (t->type == TEXPORT) export_namespace(t->name);
  else if (t->type == TDEF || t->type == TDEFX) process_def(t);
  else if (t->type == TDATATYPE) process_datatype(t);
  else if (building) { if (build_term) term_free(build_term); build_term = term_copy(t); }
  else eval_form(t);
  term_free(t);
}

/* (export <ns>): re-export every public member of `ns` into the current namespace, mirroring hand-written `(define! y ns.y)` aliases but preserving each scheme + recursion metadata so exported names reduce exactly as their qualified originals */
static void export_namespace(const char *name) {
  if (!name || !*name) return;
  char pfx[NAME + 2]; snprintf(pfx, sizeof pfx, "%s.", name);
  int pflen = (int)strlen(pfx);
  /* Re-export by routing each public member through process_def as the exact `(define x ns.x)` alias shape the hand-written modules used, so each gets identical type-checking/qualification/precompile (avoiding closure-bake differences).  Collect names first so appending can't invalidate iteration */
  static char (*out)[NAME]; static int outcap = 0;
  int nout = 0;
  for (int i = 0; i < ndefs; i++) {
    const char *dn = defs[i].name;
    if (strncmp(dn, pfx, (size_t)pflen)) continue;
    const char *suffix = dn + pflen;
    if (!*suffix || strchr(suffix, '.')) continue;          /* only direct members */
    if (suffix[0] == '_') continue;                         /* `_`-prefixed = private */
    if (nout >= outcap) out = realloc(out, (size_t)(outcap = outcap ? outcap * 2 : 64) * sizeof *out);
    snprintf(out[nout++], NAME, "%s", suffix);
  }
  for (int k = 0; k < nout; k++) {
    char qn[NAME * 2 + 2];
    if (curr_ns[0]) snprintf(qn, sizeof qn, "%s.%s", curr_ns, out[k]);
    else snprintf(qn, sizeof qn, "%s", out[k]);
    char fullname[NAME * 2 + 2]; snprintf(fullname, sizeof fullname, "%s.%s", name, out[k]);
    process_def(term_new(TDEF, out[k], term_new(TVAR, fullname, NULL, NULL), NULL));
  }
}

static int load_file(const char *path) {
  if (!building && run_line_file(path)) return 1;
  char full[PATH_MAX];
  if (!resolve_path(path, full, sizeof full)) return 0;
  if (is_already_loaded(full)) return 1;
  mark_loaded(full);

  char *src = read_file(full);
  if (!src) return 0;

  char dir[PATH_MAX]; snprintf(dir, sizeof dir, "%s", full);
  char *last_slash = strrchr(dir, '/');
  if (last_slash) *last_slash = '\0'; else snprintf(dir, sizeof dir, ".");

  if (dir_sp >= dir_cap) dir_stack = realloc(dir_stack, (size_t)(dir_cap = dir_cap ? dir_cap * 2 : 16) * sizeof *dir_stack);
  snprintf(dir_stack[dir_sp++], PATH_MAX, "%s", dir);

  char prev_ns[NAME]; snprintf(prev_ns, sizeof prev_ns, "%s", curr_ns); int prev_n_open = n_open_ns;
  parse_forms(src, form_cb, NULL);
  snprintf(curr_ns, sizeof curr_ns, "%s", prev_ns); n_open_ns = prev_n_open;

  if (dir_sp > 0) dir_sp--;
  free(src);
  return 1;
}

/* AOT decision search (std — not core).
 *
 * The artifact is the deliverable, so a build-time decision is made by building the candidates and
 * measuring them, not by a pass order someone fixed earlier.  Two numbers decide: the work the
 * runtime still has to do (the residual's own reduction, which is what "AOT moved the work out"
 * means) and how many bytes ship.  The candidate space is the set of decisions this pass can vary
 * in-process -- the e-graph configuration, whether a define is precompiled or kept textual, and the
 * unravelling bound -- and the table below is data, so the space is a row list rather than a chain
 * of ifs.
 *
 * Default is a single candidate (the measured-best configuration).  `LIN_AOT_SEARCH=1` explores the
 * table and ships the winner, reporting every candidate's numbers, which is how the default itself
 * was chosen. */

typedef struct { const char *name; const char *egraph; const char *rules; int precompile; int rec_k; } AotCand;

static const AotCand aot_default_cand = { "default", NULL, NULL, 1, 6 };
/* The unravelling bound is deliberately NOT a search axis: lowering it made `(fact 3)` return 0
   without the sentinel firing (DESIGN.md 11.2), i.e. a candidate can trade correctness for bytes.
   A decision axis belongs here only when every candidate on it is correct. */
static const AotCand aot_cands[] = {
  /* name           e-graph   rules   precompile  rec_k */
  { "default",      NULL,     NULL,   1,          6  },
  { "textual-defs", NULL,     NULL,   0,          6  },
  { "no-egraph",    "off",    NULL,   1,          6  },
  { "rules=eta",    NULL,     "eta",  1,          6  },
};
#define AOT_NCANDS ((int)(sizeof aot_cands / sizeof aot_cands[0]))

typedef struct { long bytes, rsteps; int compiled, residual, aot_steps; int ok; } AotStats;

/* forget everything a previous candidate baked: a define's expansion, its precompiled net, and the
   unravelling its recursive term was built at (the same reset `widen_recursion` performs) */
static void aot_reset_defs(int rec_k) {
  for (int i = 0; i < ndefs; i++) {
    Def *d = &defs[i];
    term_free(d->expanded); d->expanded = NULL;
    if (d->compiled) { net_free(d->compiled); free(d->compiled); d->compiled = NULL; }
    d->comp_tried = 0;
    if (d->rec && d->rec_body) {
      d->rec_k = rec_k;
      term_free(d->term);
      d->term = build_bound_rec(d->rec_name, d->rec_body, rec_k);
    }
  }
}

static void aot_apply_cand(const AotCand *c) {
  if (c->egraph && !strcmp(c->egraph, "off")) setenv("LIN_NO_EGRAPH", "1", 1);
  else unsetenv("LIN_NO_EGRAPH");
  if (c->rules) setenv("LIN_EGRULES", c->rules, 1); else unsetenv("LIN_EGRULES");
  if (c->precompile) unsetenv("LIN_PRECOMPILE"); else setenv("LIN_PRECOMPILE", "0", 1);
}

/* one full pipeline: expand -> optimize -> compile -> build-time reduce -> compact -> save, then
   measure the artifact by loading it back and reducing it (the path a user's `./prog` takes, and
   effect-free: net_reduce never runs an effect) */
static int aot_run(const AotCand *c, Term *build_term, const char *out_f, AotStats *st) {
  char err[512];
  memset(st, 0, sizeof *st);
  aot_apply_cand(c);
  aot_reset_defs(c->rec_k);
  Net net; net_init(&net, 1 << 16);
  /* AOT: run the reduction the runtime would otherwise run, and bake whatever is left.  net_reduce
     is stuck exactly at an IO effect or a non-pure FFI closure, so the artifact keeps the work that
     genuinely needs the runtime and `net_run_io` still finds its continuation intact. */
  long baked = reduce_term(build_term, &net, 1, DEPTH_BUILD, AOT_STEP_LIMIT, &st->compiled, err, sizeof err);
  if (baked < 0) { fprintf(stderr, "error: %s\n", err); net_free(&net); return 0; }
  st->aot_steps = (int)baked; st->residual = net.nn;
  net_gc(&net);
  if (!net_save_line(&net, out_f)) { net_free(&net); return 0; }
  FILE *f = fopen(out_f, "rb");
  if (f) { fseek(f, 0, SEEK_END); st->bytes = ftell(f); fclose(f); }
  Net run;
  st->rsteps = -1;
  if (net_load_line(&run, out_f)) {
    lin_build_depth++;
    st->rsteps = net_reduce(&run, AOT_STEP_LIMIT);
    lin_build_depth--;
    net_free(&run);
  }
  net_free(&net);
  st->ok = 1;
  return 1;
}

/* the objective: the work left for the runtime first (an AOT build exists to remove it), the bytes
   shipped second.  `LIN_AOT_OBJ=bytes` flips the priority for deployment-size questions. */
static int aot_better(const AotStats *a, const AotStats *b, int bytes_first) {
  if (!b->ok) return 1;
  if (!a->ok) return 0;
  if (bytes_first) {
    if (a->bytes != b->bytes) return a->bytes < b->bytes;
    return a->rsteps < b->rsteps;
  }
  if (a->rsteps != b->rsteps) return a->rsteps < b->rsteps;
  return a->bytes < b->bytes;
}

static int aot_search(Term *build_term, const char *out_f) {
  int bytes_first = getenv("LIN_AOT_OBJ") && !strcmp(getenv("LIN_AOT_OBJ"), "bytes");
  int nc = 1, best = -1;
  AotStats best_st; memset(&best_st, 0, sizeof best_st);
  char tmp[4096];
  if (getenv("LIN_AOT_SEARCH")) nc = AOT_NCANDS;
  for (int i = 0; i < nc; i++) {
    const AotCand *c = (nc == 1) ? &aot_default_cand : &aot_cands[i];
    snprintf(tmp, sizeof tmp, "%s.cand%d", out_f, i);
    AotStats st;
    if (!aot_run(c, build_term, tmp, &st)) { remove(tmp); continue; }
    if (getenv("LIN_PASSES"))
      fprintf(stderr, "[aot]   candidate %-12s artifact=%ld B, runtime=%ld steps, compile=%d nodes\n",
              c->name, st.bytes, st.rsteps, st.compiled);
    if (best < 0 || aot_better(&st, &best_st, bytes_first)) { best_st = st; best = i; }
    else remove(tmp);
  }
  if (best < 0) { fprintf(stderr, "error: no candidate produced an artifact\n"); return 1; }
  snprintf(tmp, sizeof tmp, "%s.cand%d", out_f, best);
  if (rename(tmp, out_f) != 0) { fprintf(stderr, "error: cannot write '%s'\n", out_f); return 1; }
  if (getenv("LIN_PASSES") && best_st.ok)
    fprintf(stderr, "[aot] chosen %s: artifact=%ld B, residual=%d nodes, runtime=%ld reduce steps "
                    "(effects excluded), compile=%d nodes\n",
            (nc == 1) ? aot_default_cand.name : aot_cands[best].name, best_st.bytes, best_st.residual,
            best_st.rsteps, best_st.compiled);
  return 0;
}

static int do_build(const char *in_f, const char *out_f) {
  building = 1; build_term = NULL;
  if (!load_file(in_f)) { fprintf(stderr, "error: cannot read '%s'\n", in_f); return 1; }
  if (!build_term && def_find("main")) build_term = term_new(TVAR, "main", NULL, NULL);
  if (!build_term) { fprintf(stderr, "error: no expression to build in '%s'\n", in_f); return 1; }
  char err[512]; Scheme sch;
  if (!type_check(build_term, &sch, err, sizeof err)) { fprintf(stderr, "error: %s\n", err); return 1; }
  /* The artifact is the deliverable, so the build's decisions are the ones the measurements choose. */
  int rc = aot_search(build_term, out_f);
  term_free(build_term);
  building = 0; build_term = NULL;
  return rc;
}

static Term *first_form;

static void cap_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) printf("error: %s\n", perr);
  else if (!first_form) first_form = t;
  else term_free(t);
}

static void do_type(const char *expr) {
  first_form = NULL; parse_forms(expr, cap_cb, NULL); if (!first_form) return;
  Scheme sch; char err[512];
  if (type_check(first_form, &sch, err, sizeof err)) { scheme_print(&sch); putchar('\n'); }
  else printf("error: %s\n", err);
  term_free(first_form);
}

static void do_goi(const char *expr) {
  first_form = NULL; parse_forms(expr, cap_cb, NULL); if (!first_form) return;
  Term *ex = expand_defs(first_form); Net net; net_init(&net, 1 << 16); char err[512];
  if (compile(ex, &net, err, sizeof err)) {
    long long d1 = goi_det(&net); net_reduce(&net, STEP_LIMIT);
    printf("goi: before %lld, after %lld\n", d1, goi_det(&net));
  } else printf("error: %s\n", err);
  net_free(&net); term_free(ex); term_free(first_form);
}

static int paren_balance(const char *s, int *in_str) {
  int bal = 0;
  for (int i = 0; s[i]; i++) {
    if (*in_str) { if (s[i] == '\\' && s[i + 1]) i++; else if (s[i] == '"') *in_str = 0; continue; }
    if (s[i] == ';') break;
    if (s[i] == '"') { *in_str = 1; continue; }
    if (s[i] == '(') bal++; else if (s[i] == ')') bal--;
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
      if (!strncmp(line, ":load ", 6) || !strncmp(line, ":l ", 3)) {
        const char *p = line + (line[2] == ' ' ? 3 : 6); while (*p == ' ') p++;
        if (!load_file(p)) printf("error: cannot read '%s'\n", p);
        continue;
      }
      if (!strncmp(line, ":type ", 6) || !strncmp(line, ":t ", 3)) {
        const char *p = line + (line[2] == ' ' ? 3 : 6); while (*p == ' ') p++;
        do_type(p); continue;
      }
      if (!strncmp(line, ":goi ", 5)) { do_goi(line + 5); continue; }
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

int lin_threads = 0;

static void print_usage(const char *prog) {
  printf("usage: %s [build <file.lin> [-o <file.line>]] [-e expr] [-b] [-t threads] [-h] [-v] [files...]\n", prog);
}

int main(int argc, char **argv) {
  bump_stack();
  ctor_init_builtins();
  lin_scalar_ops_load("arith"); /* register std/drivers/arith.so scalar-op providers for the base engine */
  lin_set_self_path(argv[0]);
  if (getenv("LIN_STEPS")) STEP_LIMIT = atol(getenv("LIN_STEPS"));
  if (getenv("LIN_THREADS")) lin_threads = atoi(getenv("LIN_THREADS"));
#ifdef _OPENMP
  if (lin_threads > 0) omp_set_num_threads(lin_threads); else if (!getenv("OMP_NUM_THREADS")) omp_set_num_threads(1); /* default serial; -t/LIN_THREADS/OMP_NUM_THREADS fan out */
#endif

  if (argc > 1 && (!strcmp(argv[1], "build") || !strcmp(argv[1], "--build"))) {
    load_std();
    if (argc < 3) { fprintf(stderr, "usage: lin build <file.lin> [-o <file.line>]\n"); return 1; }
    const char *in_f = argv[2], *out_f = NULL;
    for (int i = 3; i < argc; i++) if (!strcmp(argv[i], "-o") && i + 1 < argc) out_f = argv[++i];
    char auto_out[PATH_MAX];
    if (!out_f) {
      snprintf(auto_out, sizeof auto_out, "%s", in_f);
      char *dot = strrchr(auto_out, '.');
      if (dot && !strcmp(dot, ".lin")) strcpy(dot, ".line");
      else snprintf(auto_out + strlen(auto_out), sizeof auto_out - strlen(auto_out), ".line");
      out_f = auto_out;
    }
    return do_build(in_f, out_f);
  }

  if (argc == 2 && run_line_file(argv[1])) return 0;

  load_std();
  int ran_eval = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) { print_usage(argv[0]); return 0; }
    if (!strcmp(argv[i], "-v") || !strcmp(argv[i], "--version")) { printf("lin 0.1\n"); return 0; }
    if (!strcmp(argv[i], "-b") || !strcmp(argv[i], "--bench")) { bench_mode = 1; continue; }
    if (!strcmp(argv[i], "-t") || !strcmp(argv[i], "--threads")) {
      if (++i >= argc) { fprintf(stderr, "error: -t requires an argument\n"); return 1; }
      lin_threads = atoi(argv[i]);
#ifdef _OPENMP
      omp_set_num_threads(lin_threads);
#endif
      continue;
    }
    if (!strcmp(argv[i], "-e") || !strcmp(argv[i], "--eval")) {
      if (++i >= argc) { fprintf(stderr, "error: -e requires an argument\n"); return 1; }
      parse_forms(argv[i], form_cb, NULL); ran_eval = 1; continue;
    }
    if (argv[i][0] == '-') { fprintf(stderr, "unknown option: %s\n", argv[i]); print_usage(argv[0]); return 1; }
    if (!load_file(argv[i])) fprintf(stderr, "error: cannot read '%s'\n", argv[i]);
    ran_eval = 1;
  }
  if (!ran_eval) repl();
  return 0;
}
