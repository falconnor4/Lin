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
#include "runtime_io.inc"
#include "runtime_decoder.inc"

