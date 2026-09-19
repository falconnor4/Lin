#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <dlfcn.h>
#include <math.h>

static Net *N;
#define NNM(n, i) ((i) >= 0 && (i) < (n)->nn && (n)->name[i] ? (n)->name[i] : "")
static inline Port wire(Port p) { return N->wire[p.node * 3 + p.port]; }

/* float box: a `_fsz`-spine Scott numeral indexes a global double table (no IEEE bits in the numeral). */
static double *fltbox; static int nfltbox, cfltbox;

static Port alloc_scott_named(Net *n, long k, const char *szn, const char *ssn) {
  Scope sc = scope_nil(); Port cur = (Port){-1, 0};
  for (long i = 0; i <= k; i++) {
    Port sz = net_alloc(n, LAM, sc, szn), ss = net_alloc(n, LAM, sc, ssn);
    net_link(n, (Port){sz.node, 2}, (Port){ss.node, 0}, 0);
    if (i == 0) net_link(n, (Port){ss.node, 2}, (Port){sz.node, 1}, 0);
    else {
      Port app = net_alloc(n, APP, sc, "");
      net_link(n, (Port){app.node, 0}, (Port){ss.node, 1}, 0);
      net_link(n, (Port){app.node, 2}, cur, 0);
      net_link(n, (Port){ss.node, 2}, (Port){app.node, 1}, 0);
    }
    cur = (Port){sz.node, 0};
  }
  return cur;
}

Port net_alloc_float(Net *n, double d) {
  if (nfltbox >= cfltbox) { cfltbox = cfltbox ? cfltbox * 2 : 64; fltbox = realloc(fltbox, (size_t)cfltbox * sizeof(double)); }
  int idx = nfltbox++; fltbox[idx] = d;
  return alloc_scott_named(n, idx, "_fsz", "_fss");
}
#define MAX_CTOR 64
static Constructor ctors[MAX_CTOR];
static int nctors = 0;

static int ctor_lookup(const char *name) {
  if (!name || !name[0]) return -1;
  for (int i = 0; i < nctors; i++)
    if (!strcmp(ctors[i].carrier, name) || (ctors[i].carrier2 && !strcmp(ctors[i].carrier2, name))) return i;
  return -1;
}
int ctor_tag(const char *name) { int i = ctor_lookup(name); return i >= 0 ? ctors[i].tag : -1; }
int ctor_register(const char *name, int tag, const char *c1, const char *c2) {
  (void)name;
  if (nctors >= MAX_CTOR) return -1;
  ctors[nctors++] = (Constructor){.tag = tag, .carrier = c1, .carrier2 = c2};
  return nctors - 1;
}
void ctor_init_builtins(void) {
  if (nctors) return;
  /* Fold builtin scalars into the nominal-type registry so parse_type_atom resolves
     bool/num/float to distinct TNOM heads via nominal_lookup. */
  nominal_register("bool", 0);
  nominal_register("num", 0);
  nominal_register("float", 0);
  nominal_register("list", 1);
  ctor_register("_sz", DT_NUM, "_sz", "_ss");
  ctor_register("_bt", DT_BOOL, "_bt", "_bf");
  ctor_register("_cl", DT_STR, "_cl", "_nl");
  ctor_register("c", DT_STR, "c", "n");   /* std list cons/nil string spine */
  ctor_register("_ffi", DT_FFI, "_ffi", "_ret");
  ctor_register("_fsz", DT_FLOAT, "_fsz", "_fss"); /* float box: Scott index into fltbox */
  /* DT_OP tag carriers are *named LAM*s: a saturated arith op is a driver-foldable redex with a pure-Lin β-body fallback. */
  ctor_register("_add", DT_OP, "_add", NULL); ctor_register("_sub", DT_OP, "_sub", NULL);
  ctor_register("_mul", DT_OP, "_mul", NULL); ctor_register("_div", DT_OP, "_div", NULL);
  ctor_register("_mod", DT_OP, "_mod", NULL); ctor_register("_pow", DT_OP, "_pow", NULL);
  ctor_register("_eq",  DT_OP, "_eq",  NULL); ctor_register("_lt",  DT_OP, "_lt",  NULL);
  ctor_register("_gt",  DT_OP, "_gt",  NULL); ctor_register("_leq", DT_OP, "_leq", NULL);
  ctor_register("_geq", DT_OP, "_geq", NULL);
  /* monadic IO/effect continuations: an open set of effect kinds, so new effects are added by registration */
  ctor_register("_iod", DT_EFF, "_iod", NULL);
  ctor_register("_iop", DT_EFF, "_iop", NULL);
  ctor_register("_ior", DT_EFF, "_ior", NULL);
  ctor_register("_iow", DT_EFF, "_iow", NULL);
}

static Port alloc_scott(Net *n, long k) {
  Scope sc = scope_nil(); Port cur = (Port){-1, 0};
  for (long i = 0; i <= k; i++) {
    Port sz = net_alloc(n, LAM, sc, "_sz"), ss = net_alloc(n, LAM, sc, "_ss");
    net_link(n, (Port){sz.node, 2}, (Port){ss.node, 0}, 0);
    if (i == 0) net_link(n, (Port){ss.node, 2}, (Port){sz.node, 1}, 0);
    else {
      Port app = net_alloc(n, APP, sc, "");
      net_link(n, (Port){app.node, 0}, (Port){ss.node, 1}, 0);
      net_link(n, (Port){app.node, 2}, cur, 0);
      net_link(n, (Port){ss.node, 2}, (Port){app.node, 1}, 0);
    }
    cur = (Port){sz.node, 0};
  }
  return cur;
}

/* --- Geometry of Interaction (GoI) Value Marshaling --- */
static inline Port dup_hop(Net *n, Port p) {
  for (int step = 0; step < n->nn && p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP; step++) {
    if (p.port == 0) p = n->wire[p.node * 3 + 1];
    else p = n->wire[p.node * 3 + 0];
  }
  return p;
}

static Val run_ffi(Net *n, Port p); /* fwd */

/* Scott-spine walk: count succ layers (optional `peek` folds embedded `_ffi` closures per layer); 1 at zero-terminal (count set) or 0 malformed. */
static int scott_peel(Net *n, Port p, int carrier, int (*peek)(Net *, Port *), long *count) {
  for (int step = 0; step < n->nn; step++) {
    p = dup_hop(n, p);
    if (peek && !peek(n, &p)) return 0;
    if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM ||
        ctor_tag(NNM(n, p.node)) != carrier) return 0;
    int sz = p.node; Port ss_p = dup_hop(n, wire((Port){sz, 2}));
    if (ss_p.node < 0 || ss_p.node >= n->nn || n->dead[ss_p.node] || n->tag[ss_p.node] != LAM ||
        ctor_tag(NNM(n, ss_p.node)) != carrier) return 0;
    int ss = ss_p.node; Port body = dup_hop(n, wire((Port){ss, 2}));
    if (body.node < 0 || body.node >= n->nn || n->dead[body.node]) return 0;
    if (body.node == sz && body.port == 1) return 1;              /* zero terminal */
    if (n->tag[body.node] == APP) {
      Port fn = dup_hop(n, wire((Port){body.node, 0}));
      if (fn.node == ss && fn.port == 1) { (*count)++; p = wire((Port){body.node, 2}); continue; }
    }
    return 0;
  }
  return 0;
}

/* On read, give a driver the chance to materialise a closure the reducer left embedded (e.g. the `n` of
   `\_sz \_ss (_ss (mul 2 2))`, which no β redex ever reached) so the numeral decodes.  The core has no opinion
   about which closures those are — that is the driver's fold policy. */
static int read_int_peek(Net *n, Port *cur) {
  Port out;
  if ((*cur).node >= 0 && (*cur).node < n->nn && !n->dead[(*cur).node] && n->tag[(*cur).node] == LAM &&
      lin_materialize(n, *cur, &out))
    *cur = out;
  return 1;
}

long net_read_int(Net *n, Port p) {
  N = n; long count = 0;
  return scott_peel(n, p, DT_NUM, read_int_peek, &count) ? count : -1;
}

/* Extract a float box (`_fsz` spine whose value is a fltbox index). */
int net_read_float(Net *n, Port p, double *out) {
  N = n; long count = 0;
  if (!scott_peel(n, p, DT_FLOAT, 0, &count)) return 0;
  if (count < nfltbox) { *out = fltbox[count]; return 1; }
  return 0;
}

/* Extract Church boolean: _bt / _bf */
int net_read_bool(Net *n, Port p) {
  N = n;
  if (p.node < 0 || p.node >= n->nn || n->tag[p.node] != LAM || ctor_tag(NNM(n, p.node)) != DT_BOOL) return -1;
  Port bf = wire((Port){p.node, 2});
  if (bf.node < 0 || bf.port != 0 || n->tag[bf.node] != LAM || ctor_tag(NNM(n, bf.node)) != DT_BOOL) return -1;
  Port cur = wire((Port){bf.node, 2});
  for (int step = 0; step < n->nn; step++) {
    if (cur.node < 0 || n->dead[cur.node]) return -1;
    if (cur.node == p.node && cur.port == 1) return 1;
    if (cur.node == bf.node && cur.port == 1) return 0;
    if (n->tag[cur.node] == DUP) cur = wire((Port){cur.node, 0});
    else break;
  }
  return -1;
}

static inline Port skip_dup(Net *n, Port p) {
  while (p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP) p = wire((Port){p.node, 0});
  return p;
}

/* dig the `_ffi`-closure header at LAM `lam` (shape \_ffi. \_ret. ((_ffi <fn>) <args>)) into `*a1` (fn APP) and `*argp` (`_cl`-spine) */
static int ffi_header(Net *n, Port lam, Port *a1, Port *argp) {
  Port r = wire((Port){lam.node, 2});
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = wire((Port){r.node, 2});
  if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  if (a1) *a1 = wire((Port){a2.node, 0});
  if (argp) *argp = wire((Port){a2.node, 2});
  return 1;
}

int net_read_string(Net *n, Port p, char *buf, size_t max) {
  N = n;
  size_t len = 0;
  Port cur = p;
  for (int step = 0; step < n->nn && len + 1 < max; step++) {
    cur = skip_dup(n, cur);
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
    if (ctor_tag(NNM(n, cur.node)) != DT_STR) break;

    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node < 0 || bn.port != 0 || n->tag[bn.node] != LAM) break;
    if (ctor_tag(NNM(n, bn.node)) != DT_STR) break;

    Port body = skip_dup(n, wire((Port){bn.node, 2}));
    if (body.node < 0) break;
    if (n->tag[body.node] == LAM) { buf[len] = 0; return (int)len; }
    if (n->tag[body.node] == APP) {
      Port inner = skip_dup(n, wire((Port){body.node, 0}));
      if (inner.node >= 0 && n->tag[inner.node] == APP) {
        long ch = net_read_int(n, wire((Port){inner.node, 2}));
        if (ch >= 0 && ch < 256) buf[len++] = (char)ch;
      }
      cur = wire((Port){body.node, 2});
      continue;
    }
    break;
  }
  if (len > 0) { buf[len] = 0; return (int)len; }
  return -1;
}

static Val run_ffi(Net *n, Port p);

/* arg decoding now lives in the shared net_ffi_args / std/runtime/decoder.c */

/* Builtin dispatch: table rows for simple int/bool/str; side-effectors (exit) handled before the table, else dlsym. */
#define B1(n, e) if (!strcmp(fn, n)) { v.kind = 1, v.iv = (long)(e); return v; }
#define B3(n, e) if (!strcmp(fn, n)) { v.kind = 3, v.iv = (long)(e); return v; }
/* resolve a driver: "cpu" -> base engine, else LinDriver sym / lin_<name>_driver / std/drivers plugin */
static void *resolve_driver(const char *dn) {
  if (!strcmp(dn, "cpu")) return NULL;
  char sym[NAME + 16]; snprintf(sym, sizeof sym, "lin_%s_driver", dn);
  void *s = dlsym(RTLD_DEFAULT, dn);
  if (!s) s = dlsym(RTLD_DEFAULT, sym);
  if (!s) {
    const char *dir = getenv("LIN_STD_DIR");
    char path[4096];
    snprintf(path, sizeof path, "%s/drivers/%s.so", dir ? dir : "std", dn);
    if (dlopen(path, RTLD_NOW | RTLD_GLOBAL)) s = dlsym(RTLD_DEFAULT, sym);
  }
  return s;
}

/* run_ffi is *open*: drivers register ScalarOpFn providers (arith.so first); first claiming `fn` supplies the result. outkind 1=int,3=bool,4=float-bits */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
static ScalarOpFn scalar_ops[16]; static int n_scalar_ops = 0;
void lin_scalar_ops_add(ScalarOpFn f) { if (n_scalar_ops < 16) scalar_ops[n_scalar_ops++] = f; }

/* dlopen a std/drivers plugin by its `<sym>_driver` symbol (idempotent); its constructor registers providers. */
void lin_scalar_ops_load(const char *sym) {
  if (!sym || !sym[0]) return;
  char sfx[256], path[4096];
  snprintf(sfx, sizeof sfx, "%s_driver", sym);
  if (dlsym(RTLD_DEFAULT, sfx)) return;                 /* already loaded */
  const char *dir = getenv("LIN_STD_DIR");
  snprintf(path, sizeof path, "%s/drivers/%s.so", dir ? dir : "std", sym);
  if (dlopen(path, RTLD_NOW | RTLD_GLOBAL)) return;
  fprintf(stderr, "warning: driver plugin '%s' not found (looked for '%s')\n", sym, path);
}

static Val run_ffi(Net *n, Port p) {
  Val v = {0};
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM || ctor_tag(NNM(n, p.node)) != DT_FFI) return v;
  Port r = skip_dup(n, wire((Port){p.node, 2})); if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM || ctor_tag(NNM(n, r.node)) != DT_FFI) return v;
  Port a2 = skip_dup(n, wire((Port){r.node, 2})); if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return v;
  Port a1 = skip_dup(n, wire((Port){a2.node, 0})); if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return v;

  char fn[256];
  if (net_read_string(n, wire((Port){a1.node, 2}), fn, sizeof(fn)) < 0) return v;
  Val fargs[8] = {{0}};
  int argc = net_ffi_args(n, (Port){p.node, 0}, fargs, 8);
  long c_args[8] = {0}; char sbufs[8][4096];
  for (int i = 0; i < argc; i++)
    if (fargs[i].kind == 2) { snprintf(sbufs[i], 4096, "%s", fargs[i].sv); c_args[i] = (long)(intptr_t)sbufs[i]; }
    else c_args[i] = fargs[i].iv;

  if (!strcmp(fn, "exit")) { exit(argc > 0 ? (int)c_args[0] : 0); return v; }
  if (!strcmp(fn, "driver_get")) { LinDriver *d = lin_get_driver(); v.kind = 2; snprintf(v.sv, sizeof(v.sv), "%s", d ? d->name : "cpu"); return v; }
  if (!strcmp(fn, "driver_set") || !strcmp(fn, "driver_add") || !strcmp(fn, "driver_clear")) {
    if (!strcmp(fn, "driver_clear")) { lin_driver_clear(); v.kind = 1; v.iv = 1; return v; }
    const char *dn = argc > 0 ? (char *)c_args[0] : "cpu";
    void *s = resolve_driver(dn);
    if (strcmp(dn, "cpu") && !s) { v.kind = 1; v.iv = 0; return v; }
    if (strcmp(fn, "driver_add")) lin_driver_clear();   /* set resets first; add appends */
    if (s) lin_driver_add((LinDriver *)s);
    v.kind = 1; v.iv = 1; return v;
  }
  /* Delegate to registered native scalar-op providers (e.g. arith.so); first provider that owns `fn` supplies it. */
  if (n_scalar_ops > 0) {
    long out; int okind = 0;
    for (int s = 0; s < n_scalar_ops; s++)
      if (scalar_ops[s](fn, argc, c_args, &out, &okind)) {
        if (okind == 4) v.kind = 4;
        else if (okind == 3) v.kind = 3;
        else v.kind = 1;
        v.iv = out;
        return v;
      }
  }
  if (!strcmp(fn, "lin_folds")) { v.kind = 1; v.iv = lin_fold_total(); return v; }
  B3("lin_folded", lin_fold_total() > 0);
  /* String-typed-arg only: np closure carrying an INT/BOOL/FLOAT where a
     string is expected (e.g. a residual under an accelerator driver) must NOT
     strcmp()/strtod()/strlen/dlsym-call through an int-garbage pointer — that
     segfaults.  Guard each on its argument kind: a known string FFI with a
     non-string arg yields a clean no-value instead of a crash. */
  if (fargs[0].kind != 2 && argc > 0 &&
      (!strcmp(fn, "lin_parse_float") || !strcmp(fn, "lin_streq") ||
       !strcmp(fn, "dlopen") || !strcmp(fn, "puts") || !strcmp(fn, "getenv")))
    return v;
  if (fargs[0].kind == 2) {
    if (!strcmp(fn, "lin_parse_float") && argc > 0) { double d = strtod((char *)c_args[0], NULL); long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
    if (!strcmp(fn, "lin_streq") && argc >= 2 && fargs[1].kind == 2) { v.kind = 3; v.iv = !strcmp((char *)c_args[0], (char *)c_args[1]); return v; }
    if (!strcmp(fn, "dlopen") && argc > 0) { v.kind = 1; v.iv = (long)(intptr_t)dlopen((char *)c_args[0], RTLD_NOW | RTLD_GLOBAL); return v; }
    if (!strcmp(fn, "puts") && argc > 0) { v.kind = 1; v.iv = puts((char *)c_args[0]); return v; }
    if (!strcmp(fn, "getenv") && argc > 0) { char *ev = getenv((char *)c_args[0]); v.kind = 2; snprintf(v.sv, sizeof(v.sv), "%s", ev ? ev : "(null)"); return v; }
  }
  if (!strcmp(fn, "lin_float")) { double d = (double)c_args[0]; long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
  fflush(stdout); void *sym = dlsym(RTLD_DEFAULT, fn);
  if (!sym) { fprintf(stderr, "ffi: symbol '%s' not found\n", fn); return v; }
  long (*f)() = (long (*)())sym;
  v.kind = 1; v.iv = (argc <= 0) ? f() : (argc == 1) ? f(c_args[0]) : (argc == 2) ? f(c_args[0], c_args[1]) :
           (argc == 3) ? f(c_args[0], c_args[1], c_args[2]) : f(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5], c_args[6], c_args[7]);
  return v;
}

Port net_alloc_bool(Net *n, int val) {
  Scope sc = scope_nil(); Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);
  net_link(n, (Port){bf.node, 2}, (Port){val ? bt.node : bf.node, 1}, 0);
  return (Port){bt.node, 0};
}

Port net_alloc_scott(Net *n, long k) { return alloc_scott(n, k); }

/* readback / IO-effect runtime + shared on-net FFI decoder live in std (not the core); included so they share this TU's statics */
/* Lin readback / IO-effect runtime (std — not core). #included into src/io.c: value rendering, net printer, and the monadic IO/effect runner (_iod/_iop/_ior/_iow), sharing io.c's statics. */

/* render one decoded value to a stream (1=int, 2=str, 3=bool, 4=float); returns 1 if rendered, else 0 */
static int render_val(FILE *f, Val v) {
  if (v.kind == 1) fprintf(f, "%ld", v.iv);
  else if (v.kind == 2) fputs(v.sv, f);
  else if (v.kind == 3) fputs(v.iv ? "true" : "false", f);
  else if (v.kind == 4) { double d; memcpy(&d, &v.iv, 8); fprintf(f, "%g", d); }
  else return 0;
  fflush(f); return 1;
}

/* Decode a non-FFI port as a value: string (2), int (1), bool (3), float (4). */
static Val decode(Net *n, Port p) {
  Val v = {0};
  if (net_read_string(n, p, v.sv, sizeof(v.sv)) >= 0) v.kind = 2;
  else { double d; if (net_read_float(n, p, &d)) { memcpy(&v.iv, &d, 8); v.kind = 4; } }
  if (!v.kind && (v.iv = net_read_int(n, p)) >= 0) v.kind = 1;
  if (!v.kind && (v.iv = net_read_bool(n, p)) >= 0) v.kind = 3;
  return v;
}

static int net_try_ffi(Net *n, Port p) {
  return render_val(stdout, run_ffi(n, p));
}

static unsigned char *vis_print = NULL;
/* capacity of vis_print (and 3x for viz_txt).  Printing can ALLOCATE: node 0's
   LAM case calls net_read_int, whose readback peek asks the drivers to
   materialise a closure, and a driver does that with net_alloc_scott.  So
   `N->nn` grows while we print and the arrays must be indexed against the
   capacity they were allocated with, not against the current node count. */
static size_t vis_cap = 0;

/* Readback renders into a buffer so a shared (DAG) subterm is rendered ONCE and
   replayed from a memo on later visits; re-walking it was exponential in the number
   of sharing points (bench_combinators: 62 s of printing for 1.1 s of reduction). */
static char *ob_buf = NULL; static size_t ob_len, ob_cap;
static char **viz_txt = NULL;      /* memo: node*3+port -> rendered text */
static long qmarks = 0;            /* '?' (cycle/over-depth) marks emitted so far */

static void ob_need(size_t k) {
  if (ob_len + k + 1 > ob_cap) {
    size_t c = ob_cap ? ob_cap : 256;
    while (c < ob_len + k + 1) c *= 2;
    ob_buf = realloc(ob_buf, c); ob_cap = c;
  }
}
static void ob_putc(int c) { ob_need(1); ob_buf[ob_len++] = (char)c; }
static void ob_puts(const char *s) { size_t k = strlen(s); ob_need(k); memcpy(ob_buf + ob_len, s, k); ob_len += k; }
static void ob_printf(const char *f, ...) {
  char tmp[128]; va_list ap; va_start(ap, f);
  int k = vsnprintf(tmp, sizeof tmp, f, ap); va_end(ap);
  if (k > 0) ob_puts(tmp);
}

/* Render a port representation into the output buffer. */
static void print_port(Port p, int depth) {
  if (depth > N->nn || p.node < 0 || p.node >= N->nn) { ob_putc('?'); qmarks++; return; }
  if (N->dead[p.node]) { ob_putc('_'); return; }
  if (N->tag[p.node] == LAM && p.port == 1) { ob_puts(NNM(N, p.node)); return; }
  size_t key = (size_t)p.node * 3 + (size_t)p.port;
  int in_vis = (size_t)p.node < vis_cap, in_txt = key < vis_cap * 3;
  if (viz_txt && in_txt && viz_txt[key]) { ob_puts(viz_txt[key]); return; }
  if (vis_print && in_vis && vis_print[p.node]) { ob_putc('?'); qmarks++; return; }
  if (vis_print && in_vis) vis_print[p.node] = 1;
  long q0 = qmarks; size_t o0 = ob_len;
  switch (N->tag[p.node]) {
  case ROOT: print_port(wire(p), depth + 1); break;
  case ERA: ob_putc('_'); break;
  case DUP: print_port(p.port == 0 ? wire((Port){p.node, 1}) : wire((Port){p.node, 0}), depth + 1); break;
  case APP:
    ob_putc('('); print_port(wire((Port){p.node, 0}), depth + 1); ob_putc(' ');
    print_port(wire((Port){p.node, 2}), depth + 1); ob_putc(')'); break;
  case LAM:
    if (p.port == 0) {
      double d; if (net_read_float(N, p, &d)) { ob_printf("%g", d); break; }
      long v = net_read_int(N, p); if (v >= 0) { ob_printf("%ld", v); break; }
      int b = net_read_bool(N, p); if (b >= 0) { ob_puts(b ? "true" : "false"); break; }
      ob_printf("(\\%s ", NNM(N, p.node)); print_port(wire((Port){p.node, 2}), depth + 1); ob_putc(')'); break;
    }
    print_port(wire(p), depth + 1); break;
  }
  if (vis_print && in_vis) vis_print[p.node] = 0;
  /* memoise only context-free renders: a '?' on the way in means this text was
     shaped by an in-progress ancestor (a real cycle), so it must not be replayed. */
  if (viz_txt && in_txt && qmarks == q0) {
    size_t k = ob_len - o0;
    char *t = malloc(k + 1);
    if (t) { memcpy(t, ob_buf + o0, k); t[k] = 0; viz_txt[key] = t; }
  }
}

int net_print(Net *n) {
  N = n;
  Port r = dup_hop(n, wire((Port){0, 0}));
  if (r.node >= 0 && r.node < n->nn && n->tag[r.node] == LAM) {
    if (net_try_ffi(n, r)) return 0;
    Val v = decode(n, r);
    if (v.kind == 2) { printf("\"%s\"", v.sv); return 0; }
    if (render_val(stdout, v)) return 0;
  }
  vis_cap = (size_t)(n->nn + 1);
  vis_print = calloc(vis_cap, 1);
  viz_txt = calloc(vis_cap * 3, sizeof *viz_txt);
  ob_len = 0; qmarks = 0;
  print_port(r, 0);
  fwrite(ob_buf, 1, ob_len, stdout);
  if (viz_txt) { for (size_t i = 0; i < vis_cap * 3; i++) free(viz_txt[i]); free(viz_txt); viz_txt = NULL; }
  free(vis_print); vis_print = NULL; vis_cap = 0;
  return 0;
}

static Port net_alloc_string(Net *n, const char *s) {
  Scope sc = scope_nil();
  Port c_nil = net_alloc(n, LAM, sc, "_cl"), n_nil = net_alloc(n, LAM, sc, "_nl");
  Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){c_nil.node, 2}, (Port){n_nil.node, 0}, 0); net_link(n, (Port){n_nil.node, 2}, (Port){bt.node, 0}, 0);
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);       net_link(n, (Port){bf.node, 2}, (Port){bt.node, 1}, 0);
  Port cur = (Port){c_nil.node, 0};
  for (long i = (long)strlen(s) - 1; i >= 0; i--) {
    Port ch = net_alloc_scott(n, (unsigned char)s[i]);
    Port c_lam = net_alloc(n, LAM, sc, "_cl"), n_lam = net_alloc(n, LAM, sc, "_nl");
    Port a1 = net_alloc(n, APP, sc, ""), a2 = net_alloc(n, APP, sc, "");
    net_link(n, (Port){c_lam.node, 2}, (Port){n_lam.node, 0}, 0);
    net_link(n, (Port){a1.node, 0}, (Port){c_lam.node, 1}, 0); net_link(n, (Port){a1.node, 2}, ch, 0);
    net_link(n, (Port){a2.node, 0}, (Port){a1.node, 1}, 0); net_link(n, (Port){a2.node, 2}, cur, 0);
    net_link(n, (Port){n_lam.node, 2}, (Port){a2.node, 1}, 0);
    cur = (Port){c_lam.node, 0};
  }
  return cur;
}

static void chomp(char *s) { size_t l = strlen(s); if (l > 0 && s[l - 1] == '\n') s[l - 1] = 0; }
static void read_stream(FILE *f, char *buf, size_t sz, int is_pipe) {
  if (!f) return;
  size_t nr = fread(buf, 1, sz - 1, f);
  buf[nr] = 0;
  chomp(buf);
  if (is_pipe) pclose(f); else fclose(f);
}
static void read_stdin(char *buf, size_t sz) { if (!fgets(buf, (int)sz, stdin)) buf[0] = 0; else chomp(buf); }

static inline int is_io_tag(const char *s) { return ctor_tag(s) == DT_EFF; }

/* apply effect continuation `fn` to value `arg`, relink ROOT, and re-reduce: the single monadic step shared by every effect (print/read/wait/ffi) */
static void eff_apply(Net *n, Port fn, Port arg) {
  Port app = net_alloc(n, APP, scope_nil(), "");
  net_link(n, (Port){app.node, 0}, fn, 1); net_link(n, (Port){app.node, 2}, arg, 1);
  net_link(n, (Port){0, 0}, (Port){app.node, 1}, 1);
}

int net_run_io(Net *n, long step_limit) {
  N = n;
  int did_io = 0;
  for (;;) {
    Port r = dup_hop(n, wire((Port){0, 0}));
    if (r.node < 0 || r.node >= n->nn || n->dead[r.node] || n->tag[r.node] != LAM) break;
    if (!strcmp(NNM(n, r.node), "_iod")) return 1;
    if (!strcmp(NNM(n, r.node), "_iop")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      if (a0.node < 0 || n->tag[a0.node] != APP) break;
      Port a00 = dup_hop(n, wire((Port){a0.node, 0}));
      FILE *out_fp = stdout;
      Port msg_p = dup_hop(n, wire((Port){a0.node, 2}));
      if (a00.node >= 0 && n->tag[a00.node] == APP) {
        long dst_fd = net_read_int(n, dup_hop(n, wire((Port){a00.node, 2})));
        if (dst_fd == 2) out_fp = stderr;
      }
      if (!net_try_ffi(n, msg_p)) {
        Val mv = decode(n, msg_p);
        if (!render_val(out_fp, mv)) fputs("?", out_fp);
      }
      fflush(out_fp);
      Port next_p = wire((Port){body.node, 2});
      if (next_p.node >= 0 && next_p.node < n->nn && !n->dead[next_p.node] && n->tag[next_p.node] == LAM && !is_io_tag(NNM(n, next_p.node)))
        eff_apply(n, next_p, net_alloc_scott(n, 0));
      else net_link(n, (Port){0, 0}, next_p, 1);
      net_reduce(n, step_limit);
      did_io = 1;
      continue;
    }
    if (!strcmp(NNM(n, r.node), "_ior") || !strcmp(NNM(n, r.node), "_iow")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      Port cb = wire((Port){body.node, 2});
      Port src_p = (a0.node >= 0 && n->tag[a0.node] == APP) ? dup_hop(n, wire((Port){a0.node, 2})) : (Port){-1, 0};

      char in_buf[4096] = {0};
      long res_int = -1; int is_int = 0;
      Val fv = (src_p.node >= 0) ? run_ffi(n, src_p) : (Val){0};
      if (fv.kind == 1) { res_int = fv.iv; is_int = 1; }
      else if (fv.kind == 3) is_int = 2;                      /* bool result */
      else if (fv.kind == 2) snprintf(in_buf, sizeof(in_buf), "%s", fv.sv);
      else if (src_p.node < 0) read_stdin(in_buf, sizeof(in_buf));
      else {
        long fd = net_read_int(n, src_p);
        if (fd == 0) read_stdin(in_buf, sizeof(in_buf));
        else if (fd > 0) { ssize_t nr = read((int)fd, in_buf, sizeof(in_buf) - 1); if (nr > 0) { in_buf[nr] = 0; chomp(in_buf); } }
        else {
          char src[1024];
          if (net_read_string(n, src_p, src, sizeof(src)) >= 0) {
            if (!strcmp(src, "stdin") || !strcmp(src, "0")) read_stdin(in_buf, sizeof(in_buf));
            else if (src[0] == '!' || !strncmp(src, "cmd:", 4)) read_stream(popen(src[0] == '!' ? src + 1 : src + 4, "r"), in_buf, sizeof(in_buf), 1);
            else if (!strncmp(src, "sleep:", 6)) { res_int = strtol(src + 6, NULL, 10); if (res_int > 0) usleep((useconds_t)(res_int * 1000)); is_int = 1; }
            else read_stream(fopen(!strncmp(src, "file:", 5) ? src + 5 : src, "r"), in_buf, sizeof(in_buf), 0);
          }
        }
      }
      char *endptr = NULL;
      long val = (!is_int && in_buf[0]) ? strtol(in_buf, &endptr, 10) : -1;
      Port arg = (is_int == 2) ? net_alloc_bool(n, (int)fv.iv) : is_int ? net_alloc_scott(n, res_int) : (in_buf[0] && endptr && !*endptr && val >= 0) ? net_alloc_scott(n, val) : net_alloc_string(n, in_buf);
      eff_apply(n, cb, arg);
      net_reduce(n, step_limit); did_io = 1; continue;
    }
    break;
  }
  return did_io;
}
/* Shared on-net decoder (std — not core): #included into src/io.c shares its statics; EXPORTED so driver plugins reuse the same arg-spine / DUP-hop walker.  A saturated `_ffi` closure is `\_ffi. \_ret. ((_ffi "lin_*") args)` with args a `_cl`-spine of scalars. */

/* Deref a DUP (port 0) chain to the underlying wire; pure, no allocation. */
Port net_dhop(Net *n, Port p) {
  N = n;
  return skip_dup(n, p);
}

/* Read the fn name of the `_ffi` closure rooted at port p (port 0). */
int net_ffi_fn(Net *n, Port p, char *fn, int fnmax) {
  N = n;
  Port a1;
  if (!ffi_header(n, p, &a1, 0)) return 0;
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return 0;
  return net_read_string(n, wire((Port){a1.node, 2}), fn, (size_t)fnmax) >= 0;
}

/* decode a single argument port into a Val (int/bool/float/string directly; a nested `_ffi` closure folds first); 1 on success */
static int dec_arg(Net *n, Port p, Val *v) {
  N = n;
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;
  if (ctor_tag(NNM(n, p.node)) == DT_FFI) { *v = run_ffi(n, (Port){p.node, 0}); return v->kind != 0; }
  if (ctor_tag(NNM(n, p.node)) == DT_FLOAT) { double d; if (!net_read_float(n, p, &d)) return 0; memcpy(&v->iv, &d, 8); v->kind = 4; return 1; }
  if (ctor_tag(NNM(n, p.node)) == DT_BOOL) { int b = net_read_bool(n, p); if (b < 0) return 0; v->iv = b; v->kind = 3; return 1; }
  if (ctor_tag(NNM(n, p.node)) == DT_STR) { if (net_read_string(n, p, v->sv, sizeof(v->sv)) < 0) return 0; v->kind = 2; return 1; }
  long x = net_read_int(n, p); if (x < 0) return 0; v->iv = x; v->kind = 1; return 1;
}

/* decode a `_cl`-spine arg list at port `argp` into up to `max` Vals — the single spine walk shared by `_ffi` (net_ffi_args) and `_op` fold (net_spine_args); sets `*skipped` when a PRESENT slot isn't decodable (nested `_op`/closure yet to fold), which net_reduce uses to defer the outer fold; a single non-spine arg is decoded too */
static int decode_spine(Net *n, Port argp, Val *vals, int max, int *skipped) {
  if (skipped) *skipped = 0;
  int argc = 0; Port cur = skip_dup(n, argp);
  if (cur.node >= 0 && cur.node < n->nn && n->tag[cur.node] == LAM &&
      ctor_tag(NNM(n, cur.node)) == DT_STR) {
    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node >= 0 && bn.port == 0 && n->tag[bn.node] == LAM) {
      for (int step = 0; step < n->nn && argc < max; step++) {
        cur = skip_dup(n, cur);
        if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
        Port inner = skip_dup(n, wire((Port){cur.node, 2}));
        if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) break;
        Port body = skip_dup(n, wire((Port){inner.node, 2}));
        if (body.node < 0 || n->tag[body.node] != APP) break;
        Port ia = skip_dup(n, wire((Port){body.node, 0}));
        if (ia.node >= 0 && n->tag[ia.node] == APP) {
          if (dec_arg(n, wire((Port){ia.node, 2}), &vals[argc])) argc++;
          else if (skipped) *skipped = 1;             /* present slot, not yet concrete */
        }
        cur = wire((Port){body.node, 2});
      }
    }
  }
  if (skipped && !*skipped && argc == 0 && dec_arg(n, argp, &vals[0])) argc = 1;
  return argc;
}

/* walk the `_cl`-spine arg list of the `_ffi` closure rooted at `lam` (same shape as net_ffi_fn); delegates to decode_spine */
int net_ffi_args(Net *n, Port lam, Val *vals, int max) {
  N = n;
  Port argp;
  if (!ffi_header(n, lam, 0, &argp)) return 0;
  return decode_spine(n, argp, vals, max, 0);
}

/* decode a `_cl`-spine arg list at port `argp` (not inside a closure body): the `_op` redex fold reads a saturated arith op's raw operands this way; exported so driver plugins reuse the shared decoder */
int net_spine_args(Net *n, Port argp, Val *vals, int max) {
  N = n;
  return decode_spine(n, argp, vals, max, 0);
}

