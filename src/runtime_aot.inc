/* AOT decision search (std — not core): #included into src/main.c.
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
  Term *ex = expand_defs(build_term);
  Term *opt = egraph_optimize(ex);
  Net net; net_init(&net, 1 << 16);
  if (!compile(opt, &net, err, sizeof err)) {
    fprintf(stderr, "error: %s\n", err);
    net_free(&net); term_free(opt); term_free(ex);
    return 0;
  }
  st->compiled = net.nn;
  /* AOT: run the reduction the runtime would otherwise run, and bake whatever is left.  net_reduce
     is stuck exactly at an IO effect or a non-pure FFI closure, so the artifact keeps the work that
     genuinely needs the runtime and `net_run_io` still finds its continuation intact. */
  lin_build_depth++;
  st->aot_steps = (int)net_reduce(&net, AOT_STEP_LIMIT);
  lin_build_depth--;
  st->residual = net.nn;
  net_gc(&net);
  if (!net_save_line(&net, out_f)) { net_free(&net); term_free(opt); term_free(ex); return 0; }
  FILE *f = fopen(out_f, "rb");
  if (f) { fseek(f, 0, SEEK_END); st->bytes = ftell(f); fclose(f); }
  Net run;
  if (net_load_line(&run, out_f)) {
    lin_build_depth++;
    st->rsteps = net_reduce(&run, AOT_STEP_LIMIT);
    lin_build_depth--;
    net_free(&run);
  } else st->rsteps = -1;
  net_free(&net); term_free(opt); term_free(ex);
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
