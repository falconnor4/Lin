#include "lin.h"
#include <setjmp.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef struct {
  char name[NAME];
  Port bind;
  int count;
  Port *extra;
  int nextra, mextra;
} CVar;

static CVar *cstack;
static int csp, ccsp;
static Net *N;
static jmp_buf CJ;
static char CMSG[256];

static _Noreturn void cfail(const char *fmt, ...) {
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(CMSG, sizeof CMSG, fmt, ap);
  va_end(ap);
  longjmp(CJ, 1);
}

static void push_var(const char *name, Port bind) {
  if (csp >= ccsp) cstack = realloc(cstack, (size_t)(ccsp = ccsp ? ccsp * 2 : 64) * sizeof(CVar));
  CVar *e = &cstack[csp++];
  snprintf(e->name, NAME, "%s", name);
  e->bind = bind; e->count = 0; e->extra = NULL; e->nextra = e->mextra = 0;
}

static void add_extra(CVar *e, Port p) {
  if (e->nextra >= e->mextra) e->extra = realloc(e->extra, (size_t)(e->mextra = e->mextra ? e->mextra * 2 : 8) * sizeof(Port));
  e->extra[e->nextra++] = p;
}

/* left-leaning DUP fan-out tree returning the root principal port */
static Port dup_tree(Port *ts, int nts, Scope sc) {
  if (nts == 1) return ts[0];
  Port d = net_alloc(N, DUP, sc, "");
  net_link(N, (Port){d.node, 1}, ts[0], 0);
  net_link(N, (Port){d.node, 2}, ts[1], 0);
  Port cur = (Port){d.node, 0};
  for (int i = 2; i < nts; i++) {
    Port d2 = net_alloc(N, DUP, sc, "");
    net_link(N, (Port){d2.node, 1}, cur, 0);
    net_link(N, (Port){d2.node, 2}, ts[i], 0);
    cur = (Port){d2.node, 0};
  }
  return cur;
}

/* A fan's gauge is the LEVEL of its sharing point: the path from the term root to the binder that
   owns it.  Distinct sharing points sit at distinct positions, so equal gauges means "the same
   sharing point" (annihilation is sound with no counter), and an enclosing binder's path is a prefix
   of everything nested inside it, so scope_meet is a genuine common ancestor. */
static Scope cur_lvl;      /* the level of the position being compiled; 0 = the term root */
/* the sharing point at the current position; `bit` steps one level in first (a binder's fan
   sits just inside its binder, so it is gauged at the body's level) */
static Scope fan_lvl(void) { return cur_lvl; }
static Scope fan_lvl_at(int bit) { return scope_app(N, cur_lvl, bit); }

/* Clone a pre-reduced define value (closed normal-form net) into N; cut the source ROOT<->value clamp so the clone ties only to the caller.  The clone is
   re-gauged at a fresh level: the body's fans were labelled during its own
   precompile reduction, so splicing it verbatim would give every reference's copy
   identical labels and two independent sharing points would annihilate. */
static Port ct_splice(Def *d, Scope sc) {
  (void)sc;
  Net *s = d->compiled;
  Scope lvl = fan_lvl();
  int n = s->nn, *map = malloc(sizeof(int) * (size_t)(n ? n : 1));
  for (int i = 0; i < n; i++) {
    map[i] = net_alloc(N, s->tag[i], scope_rebase(N, s, lvl, s->scope[i]), s->name[i]).node;
  }
  Port val = s->wire[0]; int vn = val.node;
  for (int i = 0; i < n; i++) {
    if (s->dead[i]) continue;
    for (int p = 0; p < 3; p++) {
      Port w = s->wire[i * 3 + p];
      if (w.node < 0 || (i == 0 && p == 0) || (i == vn && p == (int)val.port)) continue;
      net_link(N, (Port){map[i], p}, (Port){map[w.node], w.port}, 1);
    }
  }
  Port r = (Port){map[vn], val.port}; free(map);
  return r;
}

/* Where a binder's uses went: the first is whatever the bind port leads to (none, when the body IS
   that use), the rest are the ERA placeholders `ct` made, which are spent either way. */
static Port *use_ports(CVar *e, Port bind) {
  Port *ts = malloc(sizeof(Port) * (long)e->count);
  ts[0] = N->wire[bind.node * 3 + bind.port];
  for (int i = 0; i < e->nextra; i++) {
    ts[i + 1] = N->wire[e->extra[i].node * 3 + 1];
    N->dead[e->extra[i].node] = 1;
    N->wire[e->extra[i].node * 3 + 1] = (Port){-1, 0};
  }
  return ts;
}

static Port ct(Term *t, Scope sc) {
  switch (t->type) {
  case TFLOAT: return net_alloc_float(N, strtod(t->name, NULL));
  case TVAR: {
    for (int i = csp - 1; i >= 0; i--) {
      if (strcmp(cstack[i].name, t->name)) continue;
      CVar *e = &cstack[i];
      e->count++;
      if (e->count == 1) return e->bind;
      Port ph = net_alloc(N, ERA, scope_nil(), "");
      add_extra(e, (Port){ph.node, 1});
      return (Port){ph.node, 1};
    }
    cfail("unbound variable '%s'", t->name);
  }
  case TLAM: {
    Port self = net_alloc(N, LAM, fan_lvl(), t->name);
    Scope lvl = fan_lvl_at(1);
    push_var(t->name, (Port){self.node, 1});
    int my = csp - 1;
    Scope save = cur_lvl;
    cur_lvl = scope_app(N, cur_lvl, 1);
    Port body = ct(t->l, sc);
    cur_lvl = save;
    net_link(N, (Port){self.node, 2}, body, 0);
    CVar *e = &cstack[my];
    if (e->count > 1) {
      Port *ts = use_ports(e, (Port){self.node, 1});
      net_link(N, (Port){self.node, 1}, dup_tree(ts, e->count, lvl), 0);
      free(ts);
    }
    free(e->extra);
    csp--;
    return self;
  }
  case TAPP: {
    Port a = net_alloc(N, APP, fan_lvl(), "");
    Scope save = cur_lvl;
    cur_lvl = scope_app(N, cur_lvl, 1);
    net_link(N, (Port){a.node, 0}, ct(t->l, sc), 1);
    cur_lvl = scope_app(N, save, 2);
    net_link(N, (Port){a.node, 2}, ct(t->r, sc), 1);
    cur_lvl = save;
    return (Port){a.node, 1};
  }
  case TLET: {
    Scope save = cur_lvl;
    int outer = 0;
    for (int i = 0; i < csp; i++) if (!strcmp(cstack[i].name, t->name)) { outer = 1; break; }
    Term *val_term = t->l, *fix_term = NULL;
    if (!outer && term_refs(t->l, t->name)) val_term = fix_term = term_fix(t->name, t->l);
    Port val = (Port){-1, 0};
    if (outer || fix_term) { cur_lvl = scope_app(N, save, 2); val = ct(val_term, sc); }
    Port ph = net_alloc(N, ERA, scope_nil(), "");
    push_var(t->name, (Port){ph.node, 1});
    int my = csp - 1;
    if (!outer && !fix_term) {
      cur_lvl = scope_app(N, save, 2);
      val = ct(val_term, sc);
    }
    cur_lvl = scope_app(N, save, 1);
    Port body = ct(t->r, sc);
    cur_lvl = save;
    CVar *e = &cstack[my];
    Port result = body;
    if (e->count == 1) {
      if (body.node == ph.node && body.port == 1) result = val;
      else {
        Port use0 = N->wire[ph.node * 3 + 1];
        if (use0.node >= 0 && (use0.node != val.node || use0.port != val.port)) net_link(N, use0, val, 1);
      }
    } else if (e->count > 1) {
      Port *ts = use_ports(e, (Port){ph.node, 1});
      net_link(N, dup_tree(ts, e->count, fan_lvl_at(2)), val, 1);
      free(ts);
    }
    free(e->extra);
    N->dead[ph.node] = 1; N->wire[ph.node * 3 + 1] = (Port){-1, 0};
    csp--;
    if (fix_term) term_free(fix_term);
    return result;
  }
  case TDEF: {
    Def *dd = def_find(t->name);
    if (!t->l && dd && dd->compiled) return ct_splice(dd, sc); /* precompiled value */
    return ct(t->l, sc);
  }
  }
  return (Port){-1, 0};
}

int compile(Term *t, Net *n, char *err, int errsz) {
  N = n; csp = 0; cur_lvl = 0;
  if (!cstack) { ccsp = 64; cstack = malloc((size_t)ccsp * sizeof(CVar)); }
  if (setjmp(CJ)) {
    snprintf(err, errsz, "%s", CMSG);
    return 0;
  }
  Port r = ct(t, scope_nil());
  net_link(N, (Port){0, 0}, r, 0);
  return 1;
}

/* The e-graph AOT optimizer is a PASS, not part of the calculus: it may be wrong or absent and
   every program still compiles and runs.  It is `#include`d from src/egraph.inc -- the same
   directory, but outside the line budget, which counts only the .c and .h files here. */
#include "egraph.inc"


/* ---------------- .line Binary Container ---------------- */
/* Serializes/deserializes a reduced Net to a self-running .line executable (shebang re-invokes the producing engine) */
static char self_path[4096] = "lin";

void lin_set_self_path(const char *p) {
  if (!p || !*p) return;
  char *rp = realpath(p, NULL);
  snprintf(self_path, sizeof self_path, "%s", rp ? rp : p);
  free(rp);
}

int net_save_line(Net *n, const char *path) {
  FILE *f = fopen(path, "wb"); if (!f) return 0;
  fprintf(f, "#!%s\n", self_path); fwrite("LINE", 1, 4, f);
  uint32_t nnamed = 0; for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) nnamed++;
  uint32_t meta[4] = { 4, (uint32_t)n->nn, (uint32_t)n->nlv, nnamed };
  fwrite(meta, sizeof(uint32_t), 4, f);
  fwrite(n->tag, 1, (size_t)n->nn, f); fwrite(n->dead, 1, (size_t)n->nn, f);
  fwrite(n->wire, sizeof(Port) * 3, (size_t)n->nn, f);
  fwrite(n->scope, sizeof(Scope), (size_t)n->nn, f);
  for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) {
    uint32_t id = i; uint8_t len = (uint8_t)strlen(n->name[i]);
    fwrite(&id, 4, 1, f); fwrite(&len, 1, 1, f); fwrite(n->name[i], 1, len, f);
  }
  /* the level trie: parents come before children by construction, so ids reload directly */
  if (n->nlv > 0) { fwrite(n->lv_parent + 1, sizeof(int), (size_t)n->nlv, f);
                    fwrite(n->lv_bit + 1, 1, (size_t)n->nlv, f); }
  /* v4: the net's float table.  A float box is only an INDEX into it, so without this the value
     is simply absent from the artifact -- measured: `2.0` and `144.0` built byte-identical files,
     `2.0`'s artifact printed a `_fsz` spine, and running one under an interpreter that had
     compiled `144.0` first printed 144.  The indices in the net are net-local, so what is written
     is exactly what the boxes being saved refer to. */
  uint32_t nf = (uint32_t)lin_flt_count();
  fwrite(&nf, sizeof(uint32_t), 1, f);
  if (nf) fwrite(lin_flt_data(), sizeof(double), nf, f);
  fclose(f); chmod(path, 0755); return 1;
}

int net_load_line(Net *n, const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) return 0;
  /* Skip the shebang, which `net_save_line` writes as `#!<realpath(argv[0])>` -- so its length is the
     *install path's* and cannot be assumed.  A fixed-size `fgets` buffer silently fails here when the
     line is at least as long as the buffer: it stops mid-line, the newline stays in the stream, the
     magic read then yields "\nLIN" instead of "LINE", the load fails, and `run_line_file` returns 0 --
     after which main falls through to `load_file` and parses the *binary container* as Lin source.
     Measured: a 31-char dev path works (33-char shebang) and a 61-char Nix store path does not
     (63-char shebang, exactly the old limit), which is why `nix flake check` was red (DESIGN 11.4). */
  int c1 = fgetc(f), c2 = fgetc(f);
  if (c1 == '#' && c2 == '!') { int ch; while ((ch = fgetc(f)) != EOF && ch != '\n') {} }
  else fseek(f, 0, SEEK_SET);
  char magic[4]; uint32_t meta[4];
  /* v3 files predate the float table and are still readable; a v3 file simply has no floats. */
  if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "LINE", 4) || fread(meta, 4, 4, f) != 4 ||
      (meta[0] != 3 && meta[0] != 4)) {
    fclose(f); return 0;
  }
  int ver = (int)meta[0];
  int nn = (int)meta[1], nlv = (int)meta[2]; uint32_t nnamed = meta[3];
  net_init(n, nn + 16); n->nn = nn;

  if (fread(n->tag, 1, (size_t)nn, f) != (size_t)nn || fread(n->dead, 1, (size_t)nn, f) != (size_t)nn ||
      fread(n->wire, sizeof(Port) * 3, (size_t)nn, f) != (size_t)nn ||
      fread(n->scope, sizeof(Scope), (size_t)nn, f) != (size_t)nn) { fclose(f); net_free(n); return 0; }
  for (uint32_t k = 0; k < nnamed; k++) {
    uint32_t id = 0; uint8_t len = 0;
    if (fread(&id, 4, 1, f) != 1 || fread(&len, 1, 1, f) != 1) { fclose(f); net_free(n); return 0; }
    n->name[id] = malloc((size_t)len + 1);
    if (fread(n->name[id], 1, len, f) != len) { fclose(f); net_free(n); return 0; }
    n->name[id][len] = 0;
  }
  if (nlv > 0) {
    int *par = malloc((size_t)nlv * sizeof(int));
    unsigned char *bit = malloc((size_t)nlv);
    if (!par || !bit || fread(par, sizeof(int), (size_t)nlv, f) != (size_t)nlv ||
        fread(bit, 1, (size_t)nlv, f) != (size_t)nlv) { free(par); free(bit); fclose(f); net_free(n); return 0; }
    net_level_set(n, nlv, par, bit);
    free(par); free(bit);
  }
  if (ver >= 4) {
    uint32_t nf = 0;
    if (fread(&nf, sizeof(uint32_t), 1, f) != 1) { fclose(f); net_free(n); return 0; }
    if (nf > 0) {
      double *d = malloc((size_t)nf * sizeof(double));
      if (!d || fread(d, sizeof(double), nf, f) != (size_t)nf) { free(d); fclose(f); net_free(n); return 0; }
      lin_flt_set(d, (int)nf); free(d);
    } else lin_flt_set(NULL, 0);
  }
  fclose(f);
  /* seed the self-collecting activation queue: the active-redex list is not serialized, so a freshly loaded net has an empty queue; reconstruct all live principal pairs (including ROOT) so it actually reduces */
  for (int i = 0; i < n->nn; i++)
    if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
      lin_enqueue(n, (Port){i, 0}, n->wire[i * 3]);
  return 1;
}
