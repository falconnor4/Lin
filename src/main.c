#define _POSIX_C_SOURCE 200809L
#define _DEFAULT_SOURCE
#include "lin.h"
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>
#include <ctype.h>
#include <stdint.h>
#include <sys/resource.h>
#ifdef _OPENMP
#include <omp.h>
static inline void set_omp_th(int t) { if (t > 0) omp_set_num_threads(t); }
#else
static inline void set_omp_th(int t) { (void)t; }
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

static long STEP_LIMIT = LONG_MAX;   /* no ceiling: the engine ALREADY stops when a wave fires nothing (the observed ports are in WHNF), so a budget never ended a reduction -- it only cut off the ones that needed more.  LIN_STEPS sets a watchdog; the message at the end reports it when one is set. */
/* Bounded so `lin build` cannot hang on a program that does not terminate at build
   time: the residual is then simply "what the compiler did not finish". */
static int bench_mode = 0;

const char *curr_ns = "";
static const char **open_ns; static int n_open_ns = 0, open_ns_cap = 0;

void set_namespace(const char *name) {
  curr_ns = (!name || !*name || !strcmp(name, "_") || !strcmp(name, "root")) ? "" : name;
}
void open_namespace(const char *name) {
  if (!name || !*name) return;
  for (int i = 0; i < n_open_ns; i++) if (!strcmp(open_ns[i], name)) return;
  if (n_open_ns == open_ns_cap) open_ns = realloc(open_ns, (size_t)(open_ns_cap = open_ns_cap ? open_ns_cap * 2 : 8) * sizeof *open_ns);
  open_ns[n_open_ns++] = name;
}
/* Definitions only ever append, and the latest of a name wins: an open-addressed index from the name to its
   latest definition, grown with the table (a prelude makes thousands of lookups; a scan per lookup was a third
   of startup). */
static int *def_ix; static size_t def_ixcap;
static size_t def_hash(const char *s) { size_t h = 1469598103934665603ull; for (; *s; s++) h = (h ^ (unsigned char)*s) * 1099511628211ull; return h; }
static void def_index(int i) {
  if ((size_t)ndefs * 2 >= def_ixcap) {
    free(def_ix); def_ixcap = def_ixcap ? def_ixcap * 2 : 1024;
    while ((size_t)ndefs * 2 >= def_ixcap) def_ixcap *= 2;
    def_ix = malloc(def_ixcap * sizeof *def_ix);
    for (size_t k = 0; k < def_ixcap; k++) def_ix[k] = -1;
    for (int j = 0; j < ndefs; j++) if (j != i) def_index(j);   /* (in order: a later one replaces an earlier) */
  }
  for (size_t k = def_hash(defs[i].name) & (def_ixcap - 1);; k = (k + 1) & (def_ixcap - 1)) {
    if (def_ix[k] < 0 || !strcmp(defs[def_ix[k]].name, defs[i].name)) { def_ix[k] = i; return; }
  }
}
static Def *lookup_raw(const char *s) {
  if (!def_ixcap) return NULL;
  for (size_t k = def_hash(s) & (def_ixcap - 1); def_ix[k] >= 0; k = (k + 1) & (def_ixcap - 1))
    if (!strcmp(defs[def_ix[k]].name, s)) return &defs[def_ix[k]];
  return NULL;
}
/* `ns.name` for a LOOKUP: built in a scratch buffer, so a miss -- most of them -- allocates nothing (formatting and
   keeping a string per probe was a sixth of startup).  A hit's name is the definition's own. */
static const char *dotted(const char *ns, const char *name) {
  static char *buf; static size_t cap;
  size_t a = strlen(ns), b = strlen(name);
  if (a + b + 2 > cap) { cap = (a + b + 2) * 2; buf = realloc(buf, cap); }
  memcpy(buf, ns, a); buf[a] = '.'; memcpy(buf + a + 1, name, b + 1);
  return buf;
}
Def *def_find(const char *name) {
  Def *d;
  if (strchr(name, '.')) return lookup_raw(name);
  if (curr_ns[0] && (d = lookup_raw(dotted(curr_ns, name)))) return d;
  for (int o = n_open_ns - 1; o >= 0; o--) {
    if ((d = lookup_raw(dotted(open_ns[o], name)))) return d;
  }
  return lookup_raw(name);
}

typedef struct { const char **names; int count, cap; } Guard;
static void guard_push(Guard *g, const char *name) {
  if (g->count >= g->cap) g->names = realloc(g->names, (size_t)(g->cap = g->cap ? g->cap * 2 : 64) * sizeof *g->names);
  g->names[g->count++] = name;
}
static int guard_has(Guard *g, const char *name) {
  for (int i = 0; i < g->count; i++) if (!strcmp(g->names[i], name)) return 1;
  return 0;
}

/* !=0 while def_precompile reduces an open body.  It is the core's one statement to drivers about precompilation:
   the operands here are free variables that never become concrete, so a driver must not fold (a baked closure
   would capture a stale value).  Which redexes that affects is the driver's business. */
int lin_precompile_depth = 0;
/* !=0 while the AOT build is partially evaluating the program.  Distinct from lin_precompile_depth
   (operands are free variables): this one says the reduction is happening at BUILD time, so nothing the
   program would OBSERVE at run time may be baked into the artifact -- a driver that folded a probe like
   (lin_folds)/(lin_folded) would freeze the build-time answer into the .line file for ever. */
int lin_build_depth = 0;

/* The one pipeline: a term becomes a reduced net the same way in every mode — expand defines,
   (AOT only) optimize, compile, (AOT only) offer the drivers their passes, run the core to the
   mode's limit.  `depth` raises the single build-time marker the reduction happens under.
   Returns steps run, or -1 if it did not compile. */
enum { DEPTH_RUN = 0, DEPTH_PRECOMPILE = 1, DEPTH_BUILD = 2 };
static const Scheme *build_sch;      /* the program's inferred type: what the AOT pass point is handed */
/* SHRINKING REDUCTIONS, before the term becomes a net.  `((\x B) A)` with x used at most once in B is
   B[x := A] (or just B): the term only gets smaller, and in an optimal evaluator no work moves -- a redex is
   shared across copies wherever it sits, so substituting under a lambda duplicates nothing.  What it buys is
   SIZE, and size is what the oracle pays for on every call: a recursive function's body is copied per call,
   and an inlined operator's operand list arrives as unreduced `_cl_cons` applications (each operator ~75
   nodes, copied every time).  The operator protocol's own binders (`_op`, `_k`) are left alone: their shape
   is what the fold drivers recognize (std/runtime/pattern.h).  Substitution renames a binder that would
   capture. */
/* Scoping as the compiler has it (compile.c, TLET): a lambda shadows its body; a `let` named like an
   ENCLOSING binder shadows only its body -- its value means the enclosing one -- and every name counted or
   renamed below is one an enclosing binder owns. */
/* how often x occurs free in t -- counted to 2: every question asked of it is "none, one, or more" */
static int shrink_count_to(const Term *t, const char *x, int lim) {   /* (stops at lim) */
  int c = 0;
  for (; t && c < lim; t = t->r) {                   /* (the right spine iteratively: argument lists are long there) */
    if (t->type == TVAR) return c + ((t->name == x) || !strcmp(t->name, x));
    if (t->type == TLAM && t->name && ((t->name == x) || !strcmp(t->name, x))) return c;          /* shadowed */
    if (t->type == TLET && t->name && !strcmp(t->name, x)) return c + shrink_count_to(t->l, x, lim - c);   /* value: ours */
    c += shrink_count_to(t->l, x, lim - c);
  }
  return c > lim ? lim : c;
}
static int shrink_count(const Term *t, const char *x) { return shrink_count_to(t, x, 2); }
static int shrink_free(const Term *t, const char *x) { return shrink_count_to(t, x, 1) > 0; }
static int shrink_seq;
static void shrink_rename(Term *t, const char *from, const char *to) {   /* free occurrences of `from` in t */
  if (!t) return;
  if (t->type == TVAR) { if (!strcmp(t->name, from)) t->name = to; return; }
  if (t->type == TLAM && t->name && !strcmp(t->name, from)) return;
  if (t->type == TLET && t->name && !strcmp(t->name, from)) { shrink_rename(t->l, from, to); return; }
  shrink_rename(t->l, from, to); shrink_rename(t->r, from, to);
}
enum { SP_ARGS = 64, SP_SLOTS = 4 * SP_ARGS };       /* one batch: a 64-bit mask of parameters, 4 table slots each (a wider list takes the general path) */
typedef struct { const char *nm[SP_SLOTS]; signed char ix[SP_SLOTS]; } SpTab;
static unsigned sp_hash(const char *s) { unsigned h = 2166136261u; for (; *s; s++) h = (h ^ (unsigned char)*s) * 16777619u; return h; }
static int sp_find(const SpTab *T, const char *nm) {
  for (unsigned j = sp_hash(nm) & (SP_SLOTS - 1); T->nm[j]; j = (j + 1) & (SP_SLOTS - 1)) if (T->nm[j] == nm || !strcmp(T->nm[j], nm)) return T->ix[j];
  return -1;
}
static void sp_put(SpTab *T, const char *nm, int ix) {
  unsigned j = sp_hash(nm) & (SP_SLOTS - 1);
  while (T->nm[j]) j = (j + 1) & (SP_SLOTS - 1);
  T->nm[j] = nm; T->ix[j] = (signed char)ix;
}
static int shrink_protocol(const char *x);
static void sp_names(const Term *t, SpTab *C, int *n) {   /* every name an argument mentions (a superset of its free ones) */
  for (; t; t = t->r) {
    /* (never a protocol binder's name: those occurrences are bound inside the argument, and renaming an `_op`
       binder elsewhere would take its head out of the protocol -- it would be beta-reduced like any lambda) */
    if (t->name && t->name[0] && (t->type == TVAR) && !shrink_protocol(t->name) && *n < SP_SLOTS / 2 && sp_find(C, t->name) < 0) { sp_put(C, t->name, 0); (*n)++; }
    if (t->type == TVAR) return;
    sp_names(t->l, C, n);
  }
}
/* (the names the argument being substituted mentions, when they fit the table: a binder among them is renamed) */
static const SpTab *ss_names;
/* t[x := a]: consumes t, copies a at the (single) occurrence */
static Term *shrink_subst(Term *t, const char *x, const Term *a) {
  if (!t) return NULL;
  if (t->type == TVAR) {
    if (!strcmp(t->name, x)) { term_free(t); return term_copy((Term *)a); }
    return t;
  }
  if (t->type == TLAM && t->name) {
    if (!strcmp(t->name, x)) return t;              /* shadowed: nothing below is x */
    if (ss_names ? sp_find(ss_names, t->name) >= 0 : (shrink_free(a, t->name) && shrink_free(t, x))) {   /* the binder would capture a free name of a */
      const char *fresh = lin_internf(" s%d", shrink_seq++);
      shrink_rename(t->l, t->name, fresh);
      t->name = fresh;
    }
  }
  if (t->type == TLET && t->name) {
    if (!strcmp(t->name, x)) { t->l = shrink_subst(t->l, x, a); return t; }   /* the value means our x */
    if (ss_names ? sp_find(ss_names, t->name) >= 0 : (shrink_free(a, t->name) && shrink_free(t->r, x))) {   /* the body would capture a free name of a */
      const char *fresh = lin_internf(" s%d", shrink_seq++);
      shrink_rename(t->r, t->name, fresh);          /* (the value's occurrences mean the enclosing one) */
      t->name = fresh;
    }
  }
  t->l = shrink_subst(t->l, x, a);
  t->r = shrink_subst(t->r, x, a);
  return t;
}
/* A WHOLE ARGUMENT LIST AT ONCE.  `((\p1 .. \pk body) a1 .. ak)` -- a constructor or a selector of many fields
   applied -- is k betas, and one at a time each walks the body: quadratic in k.  Here the body is walked once to
   count every parameter and once to substitute the linear ones.  Only when no argument mentions a parameter's
   name (then the order of the betas cannot matter); otherwise the one-at-a-time path below does it. */
static void sp_count(const Term *t, const SpTab *T, uint64_t mask, unsigned char *cnt) {
  for (; t && mask; t = t->r) {
    if (t->type == TVAR) { int i = sp_find(T, t->name); if (i >= 0 && ((mask >> i) & 1) && cnt[i] < 2) cnt[i]++; return; }
    if (t->type == TLAM && t->name) { int i = sp_find(T, t->name); if (i >= 0) mask &= ~((uint64_t)1 << i); sp_count(t->l, T, mask, cnt); return; }
    sp_count(t->l, T, mask, cnt);                    /* (a let's value sees the enclosing names; its body, the let's) */
    if (t->type == TLET && t->name) { int i = sp_find(T, t->name); if (i >= 0) mask &= ~((uint64_t)1 << i); }
  }
}
static Term *sp_subst(Term *t, const SpTab *T, uint64_t mask, Term **args, const SpTab *C) {
  if (!t || !mask) return t;
  if (t->type == TVAR) {
    int i = sp_find(T, t->name);
    if (i >= 0 && ((mask >> i) & 1)) { Term *a = args[i]; args[i] = NULL; term_free(t); return a; }   /* (its one occurrence: the argument moves) */
    return t;
  }
  if (t->type == TLAM && t->name) {
    int i = sp_find(T, t->name); if (i >= 0) mask &= ~((uint64_t)1 << i);
    if (sp_find(C, t->name) >= 0) { const char *fresh = lin_internf(" s%d", shrink_seq++); shrink_rename(t->l, t->name, fresh); t->name = fresh; }
    t->l = sp_subst(t->l, T, mask, args, C);
    return t;
  }
  t->l = sp_subst(t->l, T, mask, args, C);
  if (t->type == TLET && t->name) {
    int i = sp_find(T, t->name); if (i >= 0) mask &= ~((uint64_t)1 << i);
    if (sp_find(C, t->name) >= 0) { const char *fresh = lin_internf(" s%d", shrink_seq++); shrink_rename(t->r, t->name, fresh); t->name = fresh; }
  }
  t->r = sp_subst(t->r, T, mask, args, C);
  return t;
}
static int shrink_protocol(const char *x);
static Term *shrink(Term *t);
static Term *shrink_spine(Term *t) {                  /* NULL: not such a redex (nothing was touched) */
  int n = 0; Term *h = t;
  while (h && h->type == TAPP) { n++; h = h->l; }
  if (n < 2 || n > SP_ARGS || !h || h->type != TLAM) return NULL;
  Term *lam[SP_ARGS], *arg[SP_ARGS], *app[SP_ARGS]; Term *b = h; SpTab T; memset(&T, 0, sizeof T);
  for (int i = 0; i < n; i++) {
    if (!b || b->type != TLAM || !b->name || shrink_protocol(b->name) || sp_find(&T, b->name) >= 0) return NULL;
    lam[i] = b; sp_put(&T, b->name, i); b = b->l;
  }
  { Term *a = t; for (int i = n - 1; i >= 0; i--) { app[i] = a; arg[i] = a->r; a = a->l; } }
  SpTab C; memset(&C, 0, sizeof C); int nc = 0;
  for (int i = 0; i < n; i++) sp_names(arg[i], &C, &nc);
  if (nc >= SP_SLOTS / 2) return NULL;
  for (int i = 0; i < n; i++) if (sp_find(&C, lam[i]->name) >= 0) return NULL;   /* an argument names a parameter */
  for (int i = 0; i < n; i++) arg[i] = shrink(arg[i]);
  b = shrink(b);
  unsigned char cnt[SP_ARGS] = {0};
  sp_count(b, &T, n == SP_ARGS ? ~(uint64_t)0 : (((uint64_t)1 << n) - 1), cnt);
  uint64_t once = 0; int again = 0;
  for (int i = 0; i < n; i++) {
    if (cnt[i] == 1) { once |= (uint64_t)1 << i; again |= arg[i] && arg[i]->type == TLAM; }
    else if (cnt[i] == 0) { term_free(arg[i]); arg[i] = NULL; }
  }
  b = sp_subst(b, &T, once, arg, &C);
  for (int i = n - 1; i >= 0; i--) {                 /* a parameter used more than once keeps its redex */
    if (cnt[i] >= 2) { lam[i]->l = b; lam[i]->nl = 1; app[i]->l = lam[i]; app[i]->r = arg[i]; b = app[i]; }
    else { term_release(lam[i]); term_release(app[i]); }
  }
  return again ? shrink(b) : b;
}
static int shrink_protocol(const char *x) { return !strcmp(x, "_op") || !strcmp(x, "_k") || !strcmp(x, "_c") || !strcmp(x, "_m"); }
static Term *shrink(Term *t) {
  if (!t) return NULL;
  if (t->type == TAPP) { Term *r = shrink_spine(t); if (r) return r; }
  t->l = shrink(t->l);
  t->r = shrink(t->r);
  /* a `let` nothing names (its value refers to itself or not at all) is never demanded: it goes */
  if (t->type == TLET && t->name && !shrink_free(t->r, t->name)) {
    Term *body = t->r; t->r = NULL; term_free(t); return body;
  }
  if (t->type == TAPP && t->l && t->l->type == TLAM && t->l->name && !shrink_protocol(t->l->name)) {   /* (an annotation is the checker's, which has run) */
    Term *lam = t->l, *arg = t->r;
    /* (a binder found used twice stays so: substituting into its body renames around it, never removes a use) */
    int uses = lam->nl ? 2 : shrink_count(lam->l, lam->name);
    if (uses > 1) lam->nl = 1;
    if (uses <= 1) {
      Term *body = lam->l; lam->l = NULL;
      /* a new redex can only appear where a LAMBDA landed in function position; anything else leaves the body
         (already shrunk) as it is -- re-walking it per beta was quadratic in a long argument list */
      int again = uses == 1 && arg && arg->type == TLAM;
      if (uses == 1) {
        SpTab C; memset(&C, 0, sizeof C); int nc = 0;
        sp_names(arg, &C, &nc);
        const SpTab *sv = ss_names; ss_names = nc < SP_SLOTS / 2 ? &C : NULL;
        body = shrink_subst(body, lam->name, arg);
        ss_names = sv;
      }
      term_free(arg); term_release(lam); term_release(t);
      return again ? shrink(body) : body;
    }
  }
  return t;
}

static long reduce_term(Term *t, Net *net, int optimize, int depth, long limit, int *compiled, char *err, int errsz) {
  Term *ex = expand_defs(t);
  Term *opt = optimize ? egraph_optimize(ex) : ex;
  if (opt != ex && !getenv("LIN_NO_SHRINK")) opt = shrink(opt);   /* what the e-graph's rewrites leave linear */
  int ok = compile(opt, net, err, errsz);
  if (!ok) { if (opt != ex) term_free(opt); term_free(ex); return -1; }
  if (compiled) *compiled = net->nn;
  if (depth == DEPTH_PRECOMPILE) lin_precompile_depth++;
  else if (depth == DEPTH_BUILD) lin_build_depth++;
  /* THE PASS POINT, and the only place the core mentions it: AOT is one very large wave with full
     information and no step limit, so a driver decides here, ONCE, what the runtime would otherwise
     re-derive every wave.  Offered under the build marker (a pass cannot bake an observation the
     program would make at run time) and before compaction, so what it rewrites is what ships.  A pass's
     subject is the value a build EVALUATED, so a pass that would encode a cone it could not evaluate
     must DECLINE instead (std/drivers/arith.c: the encoding read is the test) -- measured otherwise,
     with the build keeping its partial evaluation: `test/runtime_ffi.lin`'s declined `getenv` shipped
     ROOT inside `arith`'s num box and the artifact printed the payload as structure for ever. */
  if (depth == DEPTH_BUILD) lin_driver_aot(net, opt, build_sch);
  long steps = net_reduce(net, limit);
  /* Needed order leaves a term's un-demanded thunks alone, which is exactly right at RUN time and
     useless to a build: what a build wants to bake is the VALUE, so it observes the root itself. */
  if (depth != DEPTH_RUN) net_force(net, (Port){0, 0});
  if (depth == DEPTH_BUILD) lin_driver_aot(net, opt, build_sch);
  if (depth == DEPTH_PRECOMPILE) lin_precompile_depth--;
  else if (depth == DEPTH_BUILD) lin_build_depth--;
  if (opt != ex) term_free(opt);
  term_free(ex);
  return steps;
}

/* Non-recursive define: evaluate once and cache the reduced net so each reference clones it.  A
   recursive def is a Y-knot and is spliced textually: its net IS a cycle, so baking a copy would
   only duplicate the knot. */
static void def_precompile(Def *d) {
  /* A build-time decision, not a rule -- OFF unless asked for: eager reduce_term per define costs more than the splice saves. */
  if (!getenv("LIN_PRECOMPILE") || strcmp(getenv("LIN_PRECOMPILE"), "1")) return;
  if (d->comp_tried) return;
  d->comp_tried = 1;
  if (d->rec) return;
  char err[512]; Net src; net_init(&src, 1 << 14);
  long full = reduce_term(d->term, &src, 0, DEPTH_PRECOMPILE, STEP_LIMIT, NULL, err, sizeof err);
  /* `act` is what net_reduce could NOT fire because nothing demanded it, so a non-empty list means the body
     still has unreduced work.  Under needed order that is the normal case (and `(fact 5)` bakes no value at
     all until something asks for it), so caching would store the term, not a value -- and it would ALSO hide
     the body from the e-graph pass, which is measured on the expanded term (`test/aot_equiv.py`). */
  if (full < 0 || full >= STEP_LIMIT || src.atop > 0) { net_free(&src); return; }
  d->compiled = net_copy(&src); net_free(&src);
}

/* THE DEFINITIONS BEING EXPANDED, innermost last.  A reference to one of them is a CYCLE through definitions --
   mutual recursion -- and is closed by a fixpoint at the definition it re-enters (`back`).  An expansion made
   inside such a cycle names an ENCLOSING definition, so it depends on where it was expanded and is not cached
   (`dep`).  A definition's body is expanded with a FRESH guard: the binders at its use site are not in its
   scope, and letting them be would let a local `mul` capture the library's. */
static Def **ds; static unsigned char *ds_back, *ds_dep; static int dsn, dscap;
static Term *expand(Term *t, Guard *g);

/* AN OPERATOR'S MEANING IS SHARED CODE.  An `_op` head carries its operator's pure meaning,
   `((\_op ((\_k MEANING) _op)) operands)`, which runs only when no driver folds the operator.  Expanded
   like ordinary code, every use of an operator would carry its own copy of everything the meaning names --
   a soft-float `fmul` is ~90k nodes, and `bench/mandel.lin`'s twenty float operations built 2M nodes before
   the first step.  But a meaning is the same closed code at every use, so it is built ONCE per top-level
   form: inside a meaning (the body of the reserved binder `_k`), a definition is referenced by a stable
   name (" m:<def>"), and the form is wrapped in one `let` per definition so referenced, dependencies
   outermost.  The net then shares each meaning across all its uses, and copies of it are made
   incrementally, as far as a use needs (optimal sharing).  NOT ordinary code: an operator inside a shared
   body sees its operands superposed (one per copy) until the copying is done, so a fold there declines,
   and the folds are where ordinary code's speed is.  Types are not involved: checking ran before
   expansion, on the names.  A definition being expanded right now (a cycle) stays a name: term_fix
   closes it. */
static int in_meaning;
typedef struct { Def *d; const char *name; } MeaningDef;
static MeaningDef *gm; static int ngm, cgm, gm_on;
static const char *m_name(Def *d) { return lin_internf(" m:%s", d->name); }
static int gm_has(Def *d) { for (int i = 0; i < ngm; i++) if (gm[i].d == d) return 1; return 0; }
static Term *expand_def_body(Def *d, int meaning, int *owned);
static void gm_need(Def *d);
static void gm_scan(const Term *t) {                /* every " m:" name an expansion refers to is bound */
  if (!t) return;
  if (t->type == TVAR && !strncmp(t->name, " m:", 3)) { Def *d = def_find(t->name + 3); if (d) gm_need(d); return; }
  gm_scan(t->l); gm_scan(t->r);
}
static void gm_need(Def *d) {
  if (gm_has(d)) return;
  int owned = 0;
  Term *e = expand_def_body(d, 1, &owned);
  if (!e || owned) { if (owned) term_free(e); return; }   /* (an uncacheable one is expanded in place: see expand) */
  gm_scan(e);                                       /* its dependencies first: they are bound outside it */
  if (gm_has(d)) return;
  if (ngm >= cgm) gm = realloc(gm, (size_t)(cgm = cgm ? cgm * 2 : 16) * sizeof *gm);
  gm[ngm++] = (MeaningDef){ d, m_name(d) };
}

static Term *expand(Term *t, Guard *g) {
  if (!t) return NULL;
  if (t->type == TVAR) {
    if (guard_has(g, t->name)) return term_new(TVAR, t->name, NULL, NULL);
    Def *d = def_find(t->name);
    if (!d) return term_new(TVAR, t->name, NULL, NULL);
    for (int i = dsn - 1; i >= 0; i--)
      if (ds[i] == d) {                             /* a cycle: close it at ds[i], and what lies inside depends on it */
        ds_back[i] = 1;
        for (int j = i + 1; j < dsn; j++) ds_dep[j] = 1;
        return term_new(TVAR, d->name, NULL, NULL);
      }
    int owned = 0;
    Term *x = expand_def_body(d, in_meaning, &owned);
    if (!x) return NULL;
    if (owned || d->compiled) { if (gm_on) gm_scan(x); return x; }
    if (in_meaning && gm_on) { gm_need(d); return term_new(TVAR, m_name(d), NULL, NULL); }   /* see in_meaning */
    if (gm_on) gm_scan(x);
    return term_copy(x);
  }
  Term *c = term_new(t->type, t->name, NULL, NULL);
  c->annot = t->annot;            /* a literal's stated type travels with it (a string is an annotated lambda) */
  /* TLET binds in both children: the value may refer to itself, which is the recursion. */
  int bound = (t->type == TLAM || t->type == TDEF || t->type == TLET);
  int meaning = t->type == TLAM && !strcmp(t->name, "_k");   /* an operator's meaning: see in_meaning */
  if (bound) guard_push(g, t->name);
  in_meaning += meaning;
  c->l = expand(t->l, g);
  in_meaning -= meaning;
  if (bound && t->type != TLET) g->count--;     /* a let's name is also bound in its body (the right child) */
  c->r = expand(t->r, g);
  if (bound && t->type == TLET) g->count--;
  return c;
}

/* A definition's expansion in the given mode (cached, unless it depends on an enclosing definition being
   expanded -- then it is the caller's to own).  A precompiled one is its value marker. */
static Term *expand_def_body(Def *d, int meaning, int *owned) {
  *owned = 0;
  Term **slot = meaning ? &d->expanded_sh : &d->expanded;   /* one expansion per mode */
  {
    if (!*slot) {
      if (dsn >= dscap) { dscap = dscap ? dscap * 2 : 32; ds = realloc(ds, (size_t)dscap * sizeof *ds);
                          ds_back = realloc(ds_back, (size_t)dscap); ds_dep = realloc(ds_dep, (size_t)dscap); }
      int me = dsn++; ds[me] = d; ds_back[me] = ds_dep[me] = 0;
      Term *body = term_copy(d->term), *e;
      int save = in_meaning; in_meaning = meaning;
      { Guard fresh = {0}; e = expand(body, &fresh); free(fresh.names); }
      in_meaning = save;
      term_free(body);
      if (ds_back[me]) { Term *fx = term_fix(d->name, e); term_free(e); e = fx; }   /* mutual recursion: a fixpoint */
      int dep = ds_dep[me];
      dsn--;
      if (dep) { *owned = 1; return e; }           /* depends on an enclosing definition: not cacheable, the caller's */
      *slot = e;
    }
    def_precompile(d);
    if (d->compiled) return term_new(TDEF, d->name, NULL, NULL); /* value marker */
    return *slot;
  }
}
Term *expand_defs(Term *t) {
  /* one set of shared meanings per top-level form (see in_meaning); a nested call keeps its own */
  MeaningDef *sgm = gm; int sn = ngm, sc = cgm, son = gm_on;
  gm = NULL; ngm = cgm = 0; gm_on = 1;
  Guard g = {0}; Term *res = expand(t, &g); free(g.names);
  for (int i = ngm - 1; i >= 0; i--)                /* dependencies come first in gm: they end up outermost */
    res = term_new(TLET, gm[i].name, term_copy(gm[i].d->expanded_sh), res);
  free(gm);
  gm = sgm; ngm = sn; cgm = sc; gm_on = son;
  if (!getenv("LIN_NO_SHRINK")) res = shrink(res);  /* (see shrink) */
  return res;
}

/* Benchmark accounting.  `eval_form` reduces the net *before* its recursion-sentinel check, so
   `run_and_report` used to re-reduce an already-reduced net and its timer always read 0.00 ms while
   `net->steps` showed the real total.  The reduction that happens is recorded here instead, plus the
   effect-continuation re-reductions in `net_run_io`, so the reported time covers getting the net to a
   value (not compile/readback). */
static int bench_measured;            /* a caller already reduced and timed it */
static double bench_ms;
static long long bench_goi0, bench_goi1;

static double ms_since(struct timespec a, struct timespec b) {
  return (b.tv_sec - a.tv_sec) * 1000.0 + (b.tv_nsec - a.tv_nsec) / 1000000.0;
}

/* The prelude is infrastructure, not the program: a top-level expression in a std module is an
   initialisation step (std/drivers/arith.lin activates the native scalar table that way), and
   printing `=> ...` for it would land in the program's own output.  A `; expect` line cannot tell
   the two apart, so a load of the prelude evaluates its forms quietly. */
static int quiet_forms = 0;

/* What the compiler KNOWS about the observed result, passed to readback so it decodes instead of
   guessing: the head of the form's type, when it names one of the builtin value domains.  An arrow
   or a type variable is not a value domain (-1), and a user datatype is a pure-Lin term whose
   encoding is its own -- readback prints the structure, which is the honest answer. */
static int type_domain(Type *t) {
  lin_result_desc = NULL;
  while (t && t->kind == TLINK) t = t->a;
  if (!t || t->kind != TNOM || !t->name) return -1;
  if (!strcmp(t->name, "num")) return DT_NUM;
  if (!strcmp(t->name, "bool")) return DT_BOOL;
  if (!strcmp(t->name, "float")) return DT_FLOAT;
  if (!strcmp(t->name, "list")) {                   /* a list IS the string encoding: cells of values */
    static char *ldesc; free(ldesc); ldesc = type_desc(t); lin_result_desc = ldesc;   /* (its elements' type, for the reader) */
    return DT_STR;
  }
  for (long id = 1; lin_ctor_info(id); id++) if (!strcmp(lin_ctor_info(id)->dt, t->name)) {
    static char *desc; free(desc); desc = type_desc(t); lin_result_desc = desc;   /* (its type, for the reader) */
    return LIN_DOM_DATA;
  }
  return -1;
}

/* ---- the program cache (see lin.h) ---- */
uint64_t lin_form_key; int lin_form_idx = -1, lin_form_domain; void *lin_form_net;
static LinFormRecall form_recall; static LinFormCommit form_commit;
void lin_form_register(LinFormRecall r, LinFormCommit c) { form_recall = r; form_commit = c; }
static int form_count, form_bad, form_nest, form_skip;   /* expressions seen; one was not cacheable; inside a load; results already printed */
static int term_impure(const Term *t) {              /* an effect or a foreign call: its answer is not the source's alone */
  for (; t; t = t->r) {
    if (t->type == TLAM && t->name && (!strcmp(t->name, "_ffi") || !strcmp(t->name, "_eff"))) return 1;
    if (term_impure(t->l)) return 1;
  }
  return 0;
}
static void run_and_report(Net *net, int domain) {
  struct timespec t0, t1;
  { const char *dp = getenv("LIN_DUMP_NET"); if (dp) net_save_line(net, dp); }   /* test/netdump.py reads the dump */
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
  /* net_print is what OBSERVES the value -- FFI dispatch (and so a prelude's `(set_driver ...)`)
     happens there -- so it always runs; only the `=> ` line is suppressed for the prelude. */
  int shown = lin_form_key && !form_nest && form_skip > 0;   /* (a run from the cache printed this one before it gave up) */
  if (shown) form_skip--;
  if (no_io && !quiet_forms && !shown) printf("=> ");
  if (no_io && !shown) net_print(net, domain);
  if (no_io && !quiet_forms && !shown) putchar('\n');
  if (!no_io && lin_form_key) form_bad = 1;
  if (bench_mode) {
    fprintf(stderr, "[bench] %ld steps | %d nodes (%d live) | %.2f ms | GoI det: %lld -> %lld\n",
            net->steps, net->nn, net->nn - net->nfree, bench_ms + ms_since(t0, t1), bench_goi0, bench_goi1);
    if (getenv("LIN_LEAKCHECK")) {   /* DIAGNOSTIC ONLY: how much live structure the result still reaches */
      unsigned char *r = calloc((size_t)net->nn, 1); int *q = malloc(sizeof(int) * (size_t)net->nn), h = 0, t = 0, era = 0, dup = 0;
      r[0] = 1; q[t++] = 0;
      while (h < t) { int u = q[h++]; for (int k = 0; k < 3; k++) { Port w = net->wire[u * 3 + k];
        if (w.node >= 0 && w.node < net->nn && !net->dead[w.node] && !r[w.node]) { r[w.node] = 1; q[t++] = w.node; } } }
      for (int i = 0; i < net->nn; i++) if (!net->dead[i] && !r[i]) { era += net->tag[i] == ERA; dup += net->tag[i] == DUP; }
      fprintf(stderr, "[leak] %d reachable, %d live unreachable (%d ERA, %d DUP), %d queued redexes\n",
              t, net->nn - net->nfree - t, era, dup, net->atop / 2);
      free(r); free(q);
    }
    bench_measured = 0;
  }
}

/* (recursion builders: term_fix in parse.c; the Y-knot needs no bound and no widening pass) */

void eval_form(Term *t) {
  char err[512]; Scheme sch;
  if (t->type == TDEF || t->type == TDEFX || t->type == TNS || t->type == TOPEN) return;
  int track = lin_form_key && !form_nest && !quiet_forms;
  if (track) { form_count++; lin_form_idx = -1; }
  if (!type_check(t, &sch, err, sizeof err)) { printf("error: %s\n", err); if (track) form_bad = 1; return; }
  Term *ex = expand_defs(t); Net net; net_init(&net, 1 << 10);
  if (!compile(ex, &net, err, sizeof err)) { printf("error: %s\n", err); net_free(&net); term_free(ex); if (track) form_bad = 1; return; }
  if (track) {
    int dom = type_domain(sch.t);
    if (form_bad || term_impure(ex) || !(dom == DT_NUM || dom == DT_BOOL || dom == DT_FLOAT)) form_bad = 1;
    else { lin_form_idx = form_count - 1; lin_form_domain = dom; lin_form_net = &net; }
  }
  struct timespec b0, b1;
  bench_measured = bench_mode;
  if (bench_mode) { bench_goi0 = goi_det(&net); clock_gettime(CLOCK_MONOTONIC, &b0); }
  long steps = net_reduce(&net, STEP_LIMIT);
  if (bench_mode) { clock_gettime(CLOCK_MONOTONIC, &b1); bench_goi1 = goi_det(&net); bench_ms = ms_since(b0, b1); }
  /* `steps >= STEP_LIMIT` means the reduction stopped because it ran out of budget, not because it
     reached a value.  Printing the net regardless is how a *partial* graph becomes the answer with
     exit status 0: measured, `(fib 12)` printed 0 where the answer is 144. */
  if (steps >= STEP_LIMIT) printf("error: no value within %ld reduction steps\n", STEP_LIMIT);
  else run_and_report(&net, type_domain(sch.t));
  if (track) { lin_form_idx = -1; lin_form_net = NULL; }
  net_free(&net); term_free(ex);
}

static void qualify_free(Term *t, Guard *b) {
  if (!t) return;
  if (t->type == TVAR && !strchr(t->name, '.') && !guard_has(b, t->name) && curr_ns[0]) {
    Def *qd = lookup_raw(dotted(curr_ns, t->name));
    if (qd) t->name = qd->name;
  }
  int bound = (t->type == TLAM || t->type == TLET);   /* a let's name is bound in its value and body */
  if (bound) guard_push(b, t->name);
  qualify_free(t->l, b); qualify_free(t->r, b);
  if (bound) b->count--;
}

/* (datatype Name (Ctor f...) ...): Scott-encode each constructor C_i (\f1..\fk \d0..\d_{m-1}).  Each becomes an ordinary inferred def, so it type-checks like hand-written Scott encoding */
static void process_def(Term *t);
static Term *scott_ctor(const char *dn, int idx, Term *fields, int m, long id) {
  (void)dn;
  const char *dslot = lin_internf("_d%d", idx);
  /* curried application (d_idx f1 f2 ...) */
  Term *app = term_new(TVAR, dslot, NULL, NULL);
  for (Term *f = fields; f; f = f->r) app = term_new(TAPP, "", app, term_new(TVAR, f->name, NULL, NULL));
  /* ...stating which constructor it is: `((\_c APP) ID)` (lin.h, the constructor registry) */
  app = term_new(TAPP, "", term_new(TLAM, "_c", app, NULL), term_new(TNUM, lin_internf("%ld", id), NULL, NULL));
  /* dispatch binders are innermost: \f1..\fk \d0..\d_{m-1} (d_i f1..fk) */
  Term *lam = app;
  for (int i = m - 1; i >= 0; i--) { const char *dn2 = lin_internf("_d%d", i); lam = term_new(TLAM, dn2, lam, NULL); }
  const char **fs = NULL; int nf = 0, cap = 0;
  for (Term *f = fields; f; f = f->r) { if (nf == cap) fs = realloc(fs, (size_t)(cap = cap ? cap * 2 : 8) * sizeof *fs); fs[nf++] = f->name; }
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
    int nfields = 0; for (Term *f = c->l; f; f = f->r) nfields++;
    long id = lin_ctor_register(t->name, curr_ns[0] && !strchr(c->name, '.') ? lin_internf("%s.%s", curr_ns, c->name) : c->name, m, idx, nfields);
    { char *fd = NULL; size_t fl = 0;                   /* (the declared field types, for a reader: lin.h) */
      for (Term *f = c->l; f; f = f->r) { char *d1 = type_desc(f->annot); size_t l1 = strlen(d1);
        fd = realloc(fd, fl + l1 + 1); memcpy(fd + fl, d1, l1 + 1); fl += l1; free(d1); }
      lin_ctor_set_fdesc(id, fd ? fd : ""); free(fd); }
    Term *lam = scott_ctor(t->name, idx, c->l, m, id);
    /* constructor type: fresh-params -> Name p1..pk.  A field with a declared
       type (annot) contributes that type (param refs resolved); an untyped field
       (no annot) contributes a fresh polymorphic var. */
    Type *head = type_nominal(t->name); Type **hp = &head->a;
    Type **params = calloc((size_t)(arity ? arity : 1), sizeof *params);   /* the DATA's sizes, not a constant: a fixed array would silently drop parameters or fields, and a dropped field changes the type inferred */
    for (int ip = 0; ip < arity; ip++) { params[ip] = type_var(); *hp = type_arg(params[ip]); hp = &(*hp)->b; }
    Type *ct = head; Type **args = NULL; int nf = 0;
    for (Term *f = c->l; f; f = f->r) { args = realloc(args, (size_t)(nf + 1) * sizeof *args); args[nf++] = resolve_dt_type(f->annot, params); }
    for (int i = nf - 1; i >= 0; i--) ct = type_arrow(args[i], ct);  /* fields left-to-right */
    free(params); free(args);
    Term *def = term_new(TDEFX, c->name, lam, NULL); def->annot = ct;
    process_def(def);                                   /* takes ownership of lam */
  }
}

static void process_def(Term *t) {
  if (ndefs >= defcap) defs = realloc(defs, (size_t)(defcap = defcap ? defcap * 2 : 128) * sizeof(Def));
  Scheme sch; sch.nq = 0; sch.t = NULL;   /* TDEF's scheme is inferred on first reference; TDEFX's IS the annotation */
  int rec = term_refs(t->l, t->name);
  if (t->type == TDEFX) sch = scheme_all((Type *)t->annot);
  Guard b = {0}; qualify_free(t->l, &b); free(b.names);
  Def *d = &defs[ndefs++];
  if (curr_ns[0] && !strchr(t->name, '.')) {
    const char *qn = lin_internf("%s.%s", curr_ns, t->name);
    d->name = qn;
  } else {
    d->name = t->name;
  }
  def_index((int)(d - defs));
  d->sch = sch; d->typed = (t->type == TDEFX); d->rec = rec; d->raw = NULL;
  /* A self-referential body becomes the standard fixpoint `Y (\name. body)`.  The binder carries
     `t->name` and NOT the namespace-qualified `d->name`: qualify_free runs before this def exists,
     so the body's self-references are still spelled the unqualified way. */
  if (rec) { d->raw = t->l; d->term = term_fix(t->name, t->l); }   /* the fix consumes nothing: the unfixed body stays for the deferred check */
  else d->term = t->l;
  t->l = NULL;
  d->expanded = NULL; d->expanded_sh = NULL; d->compiled = NULL; d->comp_tried = 0; d->typing = 0;
}

#include <unistd.h>

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
  /* A `std/`-prefixed load names a standard-library module.  A configured LIN_STD_DIR (a packaged
     /nix/store std) MUST win over a coincidental ./std in the process CWD — otherwise a checkout run
     overrides the configured std with a local one, mixing two stds and stranding private defs (e.g.
     num._padd unbound when a second num.lin is loaded on top of the configured one).  A plain relative
     load still falls through to the CWD / loading-file-relative lookup below. */
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
/* LAZY MODULES.  A module whose top-level forms only DEFINE (definitions, namespaces, exports, loads, opens) has
   no effect until a program names something it defines, so the prelude does not parse it: a cheap scan of its
   text lists the names loading it would define, and the first form that names one loads it -- at a form
   boundary, so no definition is mid-flight while the table grows.  Resolution is unchanged: a name is looked up
   in the same order (current namespace, opened ones newest first, then global), and a module that would supply
   the first candidate is loaded before the lookup.  So the std can grow without costing a program that does not
   use it anything. */
static int lazy_ok;                                  /* (only while loading the prelude) */
typedef struct { char *path; int loaded; } LazyMod;
static LazyMod *lzm; static int nlzm, clzm;
static const char **lzk; static int *lzv; static size_t lzcap, lzn;
static int lazy_forced(const char *full) { for (int i = 0; i < nlzm; i++) if (lzm[i].loaded && !strcmp(lzm[i].path, full)) return 1; return 0; }
static int lazy_pending(const char *full) { for (int i = 0; i < nlzm; i++) if (!lzm[i].loaded && !strcmp(lzm[i].path, full)) return 1; return 0; }
static void lz_put(const char *name, int mod) {
  if ((lzn + 1) * 2 >= lzcap) {
    const char **ok = lzk; int *ov = lzv; size_t oc = lzcap;
    lzcap = lzcap ? lzcap * 2 : 1024; lzk = calloc(lzcap, sizeof *lzk); lzv = malloc(lzcap * sizeof *lzv); lzn = 0;
    for (size_t i = 0; i < oc; i++) if (ok[i]) lz_put(ok[i], ov[i]);
    free(ok); free(ov);
  }
  for (size_t k = def_hash(name) & (lzcap - 1);; k = (k + 1) & (lzcap - 1)) {
    if (!lzk[k]) { lzk[k] = name; lzv[k] = mod; lzn++; return; }
    if (!strcmp(lzk[k], name)) { lzv[k] = mod; return; }
  }
}
static int lz_get(const char *name) {
  if (!lzcap) return -1;
  for (size_t k = def_hash(name) & (lzcap - 1); lzk[k]; k = (k + 1) & (lzcap - 1)) if (!strcmp(lzk[k], name)) return lzv[k];
  return -1;
}
/* The scan: top-level forms only, strings and comments skipped.  0 = not pure (load it now). */
static int lz_tok(const char *s, int *i, char *out, int cap) {
  while (s[*i] && (isspace((unsigned char)s[*i]) || s[*i] == ';')) { if (s[*i] == ';') while (s[*i] && s[*i] != '\n') (*i)++; else (*i)++; }
  int n = 0;
  if (s[*i] == '"') {                                  /* a string token: its text without quotes */
    (*i)++;
    while (s[*i] && s[*i] != '"') { if (s[*i] == '\\' && s[*i + 1]) (*i)++; if (n < cap - 1) out[n++] = s[*i]; (*i)++; }
    if (s[*i] == '"') (*i)++;
  } else while (s[*i] && !isspace((unsigned char)s[*i]) && s[*i] != '(' && s[*i] != ')' && s[*i] != ';') { if (n < cap - 1) out[n++] = s[*i]; (*i)++; }
  out[n] = 0; return n;
}
/* skip whitespace and comments; then, at a '(', the balanced form (strings and comments inside skipped) */
static void lz_ws(const char *s, int *i) {
  while (s[*i] && (isspace((unsigned char)s[*i]) || s[*i] == ';')) { if (s[*i] == ';') while (s[*i] && s[*i] != '\n') (*i)++; else (*i)++; }
}
static void lz_skip_form(const char *s, int *i) {
  int depth = 0;
  do {
    char c = s[*i];
    if (!c) return;
    if (c == ';') { while (s[*i] && s[*i] != '\n') (*i)++; continue; }
    if (c == '"') { (*i)++; while (s[*i] && s[*i] != '"') { if (s[*i] == '\\' && s[*i + 1]) (*i)++; (*i)++; } if (s[*i]) (*i)++; continue; }
    if (c == '(') depth++; else if (c == ')') depth--;
    (*i)++;
  } while (depth > 0);
}
static int lazy_register(const char *full, const char *src) {
  const char **names = NULL; int nn = 0, cn = 0, pure = 1;
  size_t sl = strlen(src) + 1;                         /* (a token is never longer than the text) */
  char *ns = calloc(sl, 1), *tok = malloc(sl), *arg = malloc(sl);
#define LZ_ADD(nm) do { if (nn >= cn) names = realloc(names, (size_t)(cn = cn ? cn * 2 : 64) * sizeof *names); names[nn++] = (nm); } while (0)
#define LZ_QUAL(a) (ns[0] && !strchr((a), '.') ? lin_internf("%s.%s", ns, (a)) : lin_intern((a), strlen(a)))
  for (int i = 0; pure; ) {
    lz_ws(src, &i);
    if (!src[i]) break;
    if (src[i] != '(') { pure = 0; break; }            /* a bare atom at top level: an expression */
    int start = i; i++;
    if (!lz_tok(src, &i, tok, (int)sl)) { pure = 0; break; }
    if (!strcmp(tok, "define") || !strcmp(tok, "define!")) {
      if (!lz_tok(src, &i, arg, (int)sl)) { pure = 0; break; }
      LZ_ADD(LZ_QUAL(arg));
    } else if (!strcmp(tok, "namespace")) {
      lz_tok(src, &i, arg, (int)sl);
      snprintf(ns, sl, "%s", (!strcmp(arg, "_") || !strcmp(arg, "root")) ? "" : arg);
    } else if (!strcmp(tok, "export")) {
      lz_tok(src, &i, arg, (int)sl);
      size_t al = strlen(arg); int found = 0, n0 = nn;
      for (int k = 0; k < n0; k++)
        if (!strncmp(names[k], arg, al) && names[k][al] == '.' && !strchr(names[k] + al + 1, '.') && names[k][al + 1] != '_') {
          const char *suf = names[k] + al + 1; found = 1;
          LZ_ADD(ns[0] ? lin_internf("%s.%s", ns, suf) : suf);
        }
      if (!found) pure = 0;                            /* (re-exporting another file's namespace: load it now) */
    } else if (!strcmp(tok, "datatype") || !strcmp(tok, "data")) {
      /* its constructors are definitions (and a match names them while it is being READ: see lin_ctor_demand) */
      lz_ws(src, &i);
      if (src[i] == '(') lz_skip_form(src, &i); else lz_tok(src, &i, arg, (int)sl);   /* the type's name */
      for (;;) {
        lz_ws(src, &i);
        if (!src[i] || src[i] == ')') break;
        if (src[i] == '(') { int j = i + 1; if (lz_tok(src, &j, arg, (int)sl)) LZ_ADD(LZ_QUAL(arg)); lz_skip_form(src, &i); }
        else if (lz_tok(src, &i, arg, (int)sl)) LZ_ADD(LZ_QUAL(arg)); else { pure = 0; break; }
      }
    } else if (strcmp(tok, "load") && strcmp(tok, "open")) pure = 0;   /* (a dependency loads when this module does) */
    i = start; lz_skip_form(src, &i);
  }
#undef LZ_ADD
#undef LZ_QUAL
  free(ns); free(tok); free(arg);
  if (!pure || !nn) { free(names); return 0; }
  if (nlzm >= clzm) lzm = realloc(lzm, (size_t)(clzm = clzm ? clzm * 2 : 32) * sizeof *lzm);
  lzm[nlzm] = (LazyMod){ strdup(full), 0 };
  for (int k = 0; k < nn; k++) lz_put(names[k], nlzm);
  nlzm++; free(names);
  return 1;
}
/* Load what a name, as a program spells it here, would resolve to -- if a pending module supplies the first
   candidate in lookup order. */
static int lazy_try(const char *cand) {               /* 1: this candidate settles the lookup */
  if (lookup_raw(cand)) return 1;
  int m = lz_get(cand);
  if (m < 0 || lzm[m].loaded) return 0;
  lzm[m].loaded = 1;
  int sq = quiet_forms, sl = lazy_ok; const char *prev_ns = curr_ns; int prev_open = n_open_ns;
  quiet_forms = 1; lazy_ok = 1;                        /* (its own dependencies stay lazy) */
  char path[PATH_MAX]; snprintf(path, sizeof path, "%s", lzm[m].path);
  form_nest++; load_file(path); form_nest--;         /* (a library module: the key covers the library) */
  quiet_forms = sq; lazy_ok = sl; curr_ns = prev_ns; n_open_ns = prev_open;
  return 1;
}
static void lazy_demand(const char *name) {
  if (!nlzm || !name || !*name) return;
  if (strchr(name, '.')) { lazy_try(name); return; }
  if (curr_ns[0] && lazy_try(dotted(curr_ns, name))) return;
  for (int o = n_open_ns - 1; o >= 0; o--) if (lazy_try(dotted(open_ns[o], name))) return;
  lazy_try(name);
}
static void lazy_demand_term(const Term *t) {
  for (; t; t = t->r) {                                /* (iterating the right spine: long applications are deep there) */
    if (t->type == TVAR) { lazy_demand(t->name); return; }
    lazy_demand_term(t->l);
  }
}
static void load_std(void) {
  const char *std = getenv("LIN_STD") ? getenv("LIN_STD") : "std/std.lin";
  quiet_forms = 1;
  lin_out = fopen("/dev/null", "w");
  lazy_ok = !getenv("LIN_EAGER_STD");
  lin_ctor_demand = lazy_demand;
  int ok = load_file(std);
  lazy_ok = 0;
  if (lin_out) fclose(lin_out);
  lin_out = NULL;
  quiet_forms = 0;
  if (!ok) fprintf(stderr, "warning: standard library not found at '%s'\n", std);
}

static int building = 0;
static Term *build_term = NULL;
/* The READER's last delivery while building was an error, i.e. the program's final form never parsed.
   A build compiles the LAST expression of the file (`build_term`), so building a truncated prefix would
   ship an artifact for a program the interpreter refuses -- measured: test/types.lin ends in an
   unterminated `(1`, the interpreter reports `parse error: missing ')'` as that form's outcome, and the
   artifact printed the 500 of the form BEFORE it.  A read error a LATER form supersedes is harmless:
   the interpreter continues form by form, and so does the build. */
static int build_read_err = 0;

static int run_line_file(const char *path) {
  Net net; if (!net_load_line(&net, path)) return 0;
  /* A v8 container carries the DOMAIN of its result (the build's type of it): a float is a numeral, so the
     structure alone cannot say "float".  An older one carries none, and readback decodes what the structure
     determines by itself. */
  run_and_report(&net, lin_line_domain); net_free(&net); return 1;
}

static void export_namespace(const char *name);   /* (export <ns>) re-export */
static void form_cb(Term *t, const char *perr, void *ud) {
  (void)ud;
  if (perr) { build_read_err = 1; printf("error: %s\n", perr); return; }
  build_read_err = 0;
  if (t->type == TDEF || t->type == TDEFX || (t->type != TLOAD && t->type != TNS && t->type != TOPEN && t->type != TEXPORT && t->type != TDATATYPE))
    lazy_demand_term(t->type == TDEF || t->type == TDEFX ? t->l : t);   /* (what this form names, loaded first) */
  if (t->type == TLOAD) {
    if (lin_form_key && !form_nest && strncmp(t->name, "std/", 4)) form_bad = 1;   /* (another source file: not in the key) */
    form_nest++; if (!load_file(t->name)) printf("error: cannot load '%s'\n", t->name); form_nest--;
  }
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
  const char *pfx = lin_internf("%s.", name);
  int pflen = (int)strlen(pfx);
  /* Re-export by routing each public member through process_def as the exact `(define x ns.x)` alias shape the hand-written modules used, so each gets identical type-checking/qualification/precompile (avoiding closure-bake differences).  Collect names first so appending can't invalidate iteration */
  static const char **out; static int outcap = 0;
  int nout = 0;
  for (int i = 0; i < ndefs; i++) {
    const char *dn = defs[i].name;
    if (strncmp(dn, pfx, (size_t)pflen)) continue;
    const char *suffix = dn + pflen;
    if (!*suffix || strchr(suffix, '.')) continue;          /* only direct members */
    if (suffix[0] == '_') continue;                         /* `_`-prefixed = private */
    if (nout >= outcap) out = realloc(out, (size_t)(outcap = outcap ? outcap * 2 : 64) * sizeof *out);
    out[nout++] = suffix;
  }
  for (int k = 0; k < nout; k++) {
    const char *fullname = lin_internf("%s.%s", name, out[k]);
    process_def(term_new(TDEF, out[k], term_new(TVAR, fullname, NULL, NULL), NULL));
  }
}

static int load_file(const char *path) {
  if (!building && run_line_file(path)) return 1;
  char full[PATH_MAX];
  if (!resolve_path(path, full, sizeof full)) return 0;
  if (is_already_loaded(full) || lazy_pending(full)) return 1;
  char *src = read_file(full);
  if (!src) return 0;
  if (lazy_ok && !lazy_forced(full) && lazy_register(full, src)) { free(src); return 1; }   /* a pure module: read when a program names it */
  mark_loaded(full);
  char dir[PATH_MAX]; snprintf(dir, sizeof dir, "%s", full);
  char *last_slash = strrchr(dir, '/');
  if (last_slash) *last_slash = '\0'; else snprintf(dir, sizeof dir, ".");
  if (dir_sp >= dir_cap) dir_stack = realloc(dir_stack, (size_t)(dir_cap = dir_cap ? dir_cap * 2 : 16) * sizeof *dir_stack);
  snprintf(dir_stack[dir_sp++], PATH_MAX, "%s", dir);
  const char *prev_ns = curr_ns; int prev_n_open = n_open_ns;
  parse_forms(src, form_cb, NULL);
  curr_ns = prev_ns; n_open_ns = prev_n_open;
  if (dir_sp > 0) dir_sp--;
  free(src);
  return 1;
}

/* AOT decision search (std — not core).  The artifact is the deliverable, so a build-time decision is made by
 * building the candidates and measuring them: the work the runtime still has to do (the residual's own reduction
 * -- what "AOT moved the work out" means) and how many bytes ship.  The candidate space is a row list, not a chain
 * of ifs; `LIN_AOT_SEARCH=1` explores it and ships the winner, with every candidate's numbers. */

typedef struct { const char *name; const char *egraph; const char *rules; int precompile; } AotCand;

/* Predcompiling a def means EVALUATING it the first time it is referenced.  Under needed order that
   buys nothing -- the def's body is a thunk until something demands it, so what gets baked is the
   term -- while it hides the body from the e-graph pass, which is measured on the expanded term.  The
   default therefore stays textual, and the precompiling shape remains a searchable row. */
static const AotCand aot_default_cand = { "default", NULL, NULL, 0 };
static const AotCand aot_cands[] = {
  /* name           e-graph   rules   precompile */
  { "default",      NULL,     NULL,   0 },
  { "precompiled",  NULL,     NULL,   1 },
  { "no-egraph",    "off",    NULL,   0 },
  { "rules=eta",    NULL,     "eta",  0 },
};
#define AOT_NCANDS ((int)(sizeof aot_cands / sizeof aot_cands[0]))

typedef struct { long bytes, rsteps; int compiled, residual, aot_steps; int ok; } AotStats;

/* forget everything a previous candidate baked: a define's expansion and its precompiled net */
static void aot_reset_defs(void) {
  for (int i = 0; i < ndefs; i++) {
    Def *d = &defs[i];
    term_free(d->expanded); d->expanded = NULL;
    term_free(d->expanded_sh); d->expanded_sh = NULL;
    if (d->compiled) { net_free(d->compiled); free(d->compiled); d->compiled = NULL; }
    d->comp_tried = 0;
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
  aot_reset_defs();
  Net net; net_init(&net, 1 << 10);
  /* AOT: run the reduction the runtime would otherwise run, and bake whatever is left.  Needed order stops at the
     first effect or observation, so the artifact keeps only what genuinely needs the runtime, and a Y-knot is left
     as the cycle it is instead of being unrolled to a guessed bound.  AN OBSERVING BUILD KEEPS THE WORK IT DID, and
     what it observed is not made here: the fold that needs it declines (io.c's one gate) and the redex it declined
     STAYS in the net (std/drivers/arith.c, the rule a precompiled def's free operands already had), so the artifact
     folds it at run time, after the observation its own environment makes -- one pass, and the partial evaluation
     ships.  Measured without the gate: `lin build` of test/runtime_ffi.lin ran the program's own `getenv` and froze
     the answer (built with N=2 the artifact printed 3 for every N; built without N it printed 1 where the
     interpreter prints 7).  Against discarding the whole net and recompiling: test/runtime_ffi.lin 483 -> 204 ms
     with the artifact's own work falling from 106 reduce steps to 1, and test/build_observe.lin 5953 -> 193 ms with
     498739 steps -> 1. */
  lin_build_observed = 0;
  long baked = reduce_term(build_term, &net, 1, DEPTH_BUILD, STEP_LIMIT, &st->compiled, err, sizeof err);
  if (baked < 0) { fprintf(stderr, "error: %s\n", err); net_free(&net); return 0; }
  st->aot_steps = (int)baked; st->residual = net.nn;
  if (!net_save_line(&net, out_f)) { net_free(&net); return 0; }
  FILE *f = fopen(out_f, "rb");
  if (f) { fseek(f, 0, SEEK_END); st->bytes = ftell(f); fclose(f); }
  Net run;
  st->rsteps = -1;
  if (net_load_line(&run, out_f)) {
    lin_build_depth++;
    st->rsteps = net_reduce(&run, STEP_LIMIT);
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
  building = 1; build_term = NULL; build_read_err = 0;
  if (!load_file(in_f)) { fprintf(stderr, "error: cannot read '%s'\n", in_f); return 1; }
  /* The interpreter REFUSES a final form it cannot read (it reports the reader's error as that
     form's outcome), so a build must refuse it too: the expression it would compile is an earlier
     form, i.e. a different program.  Agreeing on refusing is the only honest agreement here. */
  if (build_read_err) { fprintf(stderr, "error: cannot build '%s': its last form did not parse\n", in_f); return 1; }
  if (!build_term && def_find("main")) build_term = term_new(TVAR, "main", NULL, NULL);
  if (!build_term) { fprintf(stderr, "error: no expression to build in '%s'\n", in_f); return 1; }
  char err[512]; Scheme sch;
  if (!type_check(build_term, &sch, err, sizeof err)) { fprintf(stderr, "error: %s\n", err); return 1; }
  lin_line_domain = type_domain(sch.t);           /* the artifact says what its result MEANS (a float is a numeral) */
  build_sch = &sch;                    /* the AOT pass point is handed the types the compiler inferred */
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
  lazy_demand_term(first_form);                    /* (a library name it uses: its module is read now) */
  Scheme sch; char err[512];
  if (type_check(first_form, &sch, err, sizeof err)) { scheme_print(&sch); putchar('\n'); }
  else printf("error: %s\n", err);
  term_free(first_form);
}

static void do_goi(const char *expr) {
  first_form = NULL; parse_forms(expr, cap_cb, NULL); if (!first_form) return;
  Term *ex = expand_defs(first_form); Net net; net_init(&net, 1 << 10); char err[512];
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
    if (s[i] == '"') { *in_str = 1; continue; } if (s[i] == '(') bal++; else if (s[i] == ')') bal--;
  }
  return bal;
}

static void repl(void) {
  char *buf = NULL, *line = NULL; size_t buf_cap = 0, line_cap = 0;
  int buf_len = 0, depth = 0, in_str = 0;
  printf("lin 0.1 - interaction combinator language\n");
  printf("commands: :type <expr>  :goi <expr>  :load <file>  :help  :q\n");
  for (;;) {
    printf(depth > 0 || in_str ? "...  " : "lin> ");
    fflush(stdout);
    if (getline(&line, &line_cap, stdin) < 0) break;
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

    if (buf_len + (int)len + 2 > (int)buf_cap) buf = realloc(buf, buf_cap = (size_t)(buf_len + (int)len + 2) * 2);
    memcpy(buf + buf_len, line, len);
    buf_len += len;
    buf[buf_len++] = '\n';
    buf[buf_len] = 0;

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

/* THE PROGRAM, FROM THE CACHE.  The key is everything the program's answers can depend on: its text, the library
   and drivers on disk, this binary, and the settings in the environment (not the thread count: a pure program's
   answer does not depend on it). */
#include <dirent.h>
#include <sys/stat.h>
extern char **environ;
static uint64_t key_mix(uint64_t h, const void *p, size_t n) { const unsigned char *b = p; for (size_t i = 0; i < n; i++) h = (h ^ b[i]) * 1099511628211ULL; return h; }
static uint64_t key_stat(uint64_t h, const char *path) {
  struct stat st; if (stat(path, &st)) return key_mix(h, "?", 1);
  h = key_mix(h, path, strlen(path)); h = key_mix(h, &st.st_size, sizeof st.st_size);
  h = key_mix(h, &st.st_mtim, sizeof st.st_mtim); return h;
}
static uint64_t key_dir(uint64_t h, const char *dir) {   /* (names in directory order: a reordering is a miss, never a wrong hit) */
  DIR *d = opendir(dir); if (!d) return key_mix(h, "!", 1);
  for (struct dirent *e; (e = readdir(d)); ) {
    if (e->d_name[0] == '.') continue;
    const char *p = lin_internf("%s/%s", dir, e->d_name);
    h = key_stat(h, p);
  }
  closedir(d); return h;
}
static uint64_t program_key(const char *src) {
  uint64_t h = 1469598103934665603ULL;
  h = key_mix(h, "lin-form-1", 10);
  h = key_mix(h, src, strlen(src));
  h = key_stat(h, "/proc/self/exe");
  const char *sd = getenv("LIN_STD_DIR") ?: "std";
  h = key_dir(h, sd); h = key_dir(h, lin_internf("%s/drivers", sd)); h = key_dir(h, lin_internf("%s/runtime", sd));
  for (char **e = environ; e && *e; e++) if (!strncmp(*e, "LIN_", 4) && strncmp(*e, "LIN_THREADS=", 12) && strncmp(*e, "LIN_CACHE_DEBUG=", 16)) h = key_mix(h, *e, strlen(*e));
  return h ? h : 1;
}
static int load_main_file(const char *path) {
  char full[PATH_MAX]; char *src;
  int dbgc = getenv("LIN_CACHE_DEBUG") != NULL;
  /* (a diagnostic setting, or one that changes how a program is run, asks for the run in full) */
  static const char *const full_run[] = { "LIN_FN_", "LIN_NO_", "LIN_DUMP_", "LIN_GPU_", "LIN_AOT_", "LIN_NATIVE_DEBUG=", "LIN_TRACE=", "LIN_STEPS=",
    "LIN_LEAKCHECK=", "LIN_WAVE_STATS=", "LIN_PASSES=", "LIN_EGRULES=", "LIN_PRECOMPILE=", "LIN_READBACK=", "LIN_EAGER_STD=" };
  for (char **e = environ; e && *e; e++) if (!strncmp(*e, "LIN_", 4))
    for (int k = 0; k < N_OF(full_run); k++) if (!strncmp(*e, full_run[k], strlen(full_run[k]))) return load_file(path);
  if (!form_recall || !resolve_path(path, full, sizeof full) || !(src = read_file(full))) return load_file(path);
  if (!strncmp(src, "#!", 2) && strstr(path, ".line")) { free(src); return load_file(path); }   /* (an artifact) */
  uint64_t key = program_key(src); free(src);
  int idx = 0;
  for (;; idx++) {
    long w; int kind, dom;
    int r = form_recall(key, idx, lin_threads, &w, &kind, &dom);
    if (r == 0 && idx > 0) { if (dbgc) fprintf(stderr, "[cache] %d expression%s run from compiled units\n", idx, idx == 1 ? "" : "s"); return 1; }   /* every expression ran from its compiled unit */
    if (r <= 0) break;
    Net net; net_init(&net, 16);
    Port v = kind == 3 ? net_alloc_bool(&net, w != 0) : net_alloc_scott(&net, w);
    net_link(&net, (Port){0, 0}, v, 0);
    lin_result_desc = NULL;
    run_and_report(&net, dom);
    net_free(&net);
  }
  form_skip = idx; form_count = 0; form_bad = 0; lin_form_key = key;
  int ok = load_file(path);
  lin_form_key = 0;
  if (dbgc) fprintf(stderr, "[cache] %s\n", ok && !form_bad && form_count > 0 ? "evaluated; offered to the cache" : "evaluated; not cacheable");
  if (ok && !form_bad && form_count > 0 && form_commit) form_commit(key, form_count);
  return ok;
}

int main(int argc, char **argv) {
  bump_stack();
  lin_domains_init();
  /* No driver is loaded by default: the core runs pure Lin, and a program asks for an accelerator
     with `(set_driver "simd")` / `(load "std/drivers/...")`.  std/std.lin activates std/drivers/
     arith.lin, which is where the shared scalar-op table comes from. */
  lin_set_self_path(argv[0]);
  if (getenv("LIN_STEPS")) STEP_LIMIT = atol(getenv("LIN_STEPS"));
  if (getenv("LIN_THREADS")) lin_threads = atoi(getenv("LIN_THREADS"));
  set_omp_th(lin_threads); if (!lin_threads && !getenv("OMP_NUM_THREADS")) set_omp_th(1);

  if (argc > 1 && (!strcmp(argv[1], "build") || !strcmp(argv[1], "--build"))) {
    load_std();
    if (argc < 3) { fprintf(stderr, "usage: lin build <file.lin> [-o <file.line>]\n"); return 1; }
    const char *in_f = argv[2], *out_f = NULL;
    for (int i = 3; i < argc; i++) {
      if (!strcmp(argv[i], "-o") && i + 1 < argc) out_f = argv[++i];
      else if (!strcmp(argv[i], "-t") && i + 1 < argc) set_omp_th(lin_threads = atoi(argv[++i]));
    }
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
      set_omp_th(lin_threads = atoi(argv[i]));
      continue;
    }
    if (!strcmp(argv[i], "-e") || !strcmp(argv[i], "--eval")) {
      if (++i >= argc) { fprintf(stderr, "error: -e requires an argument\n"); return 1; }
      parse_forms(argv[i], form_cb, NULL); ran_eval = 1; continue;
    }
    if (argv[i][0] == '-') { fprintf(stderr, "unknown option: %s\n", argv[i]); print_usage(argv[0]); return 1; }
    /* (the one program of the run: the cache may answer for it) */
    if (!(i == argc - 1 && !ran_eval && !bench_mode ? load_main_file(argv[i]) : load_file(argv[i]))) fprintf(stderr, "error: cannot read '%s'\n", argv[i]);
    ran_eval = 1;
  }
  if (!ran_eval) repl();
  return 0;
}
