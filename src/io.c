#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <dlfcn.h>
#include <math.h>

static Net *N;
#define NNM(n, i) ((i) >= 0 && (i) < (n)->nn && (n)->name[i] ? (n)->name[i] : "")
static inline Port wire(Port p) { return N->wire[p.node * 3 + p.port]; }

/* ---------------- float box (side table) ----------------
   A concrete float in the net is a `_fsz`-spine Scott numeral whose value is a
   small index into a process-global double table.  Indexing (not bit-packing)
   sidesteps the sign-bit problem: a double's IEEE bits are not stored in the
   numeral, so no giant/negative Scott counts arise. */
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
  ctor_register("_sz", DT_NUM, "_sz", "_ss");
  ctor_register("_bt", DT_BOOL, "_bt", "_bf");
  ctor_register("_cl", DT_STR, "_cl", "_nl");
  ctor_register("c", DT_STR, "c", "n");   /* std list cons/nil string spine */
  ctor_register("_ffi", DT_FFI, "_ffi", "_ret");
  ctor_register("_fsz", DT_FLOAT, "_fsz", "_fss"); /* float box: Scott index into fltbox */
  /* monadic IO/effect continuations: an open set of effect kinds keyed here,
     so new effects are added by registration rather than new branches */
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
static int lin_ffi_peek(Net *n, Port lam, Val *vout, int argfold); /* fwd */

long net_read_int(Net *n, Port p) {
  N = n; long count = 0; Port cur = p;
  for (int step = 0; step < n->nn; step++) {
    cur = dup_hop(n, cur);
    /* An embedded saturated `_ffi` arithmetic closure (e.g. the `n` of
       `\_sz \_ss (_ss (mul 2 2))`) never folded during reduction; fold it on
       read so the surrounding numeral decodes.  Pure int/bool results only. */
    if (cur.node >= 0 && cur.node < n->nn && !n->dead[cur.node] && n->tag[cur.node] == LAM) {
      const char *cn = n->name[cur.node];
      if (cn && ctor_tag(cn) == DT_FFI) {
        long v = -1;
        Val vv; if (lin_ffi_peek(n, (Port){cur.node, 0}, &vv, 1) && vv.kind == 1) v = vv.iv;
        if (v >= 0) cur = net_alloc_scott(n, v);
      }
    }
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM || ctor_tag(NNM(n, cur.node)) != DT_NUM) return -1;
    int sz = cur.node; Port ss_p = dup_hop(n, wire((Port){sz, 2}));
    if (ss_p.node < 0 || ss_p.node >= n->nn || n->dead[ss_p.node] || n->tag[ss_p.node] != LAM || ctor_tag(NNM(n, ss_p.node)) != DT_NUM) return -1;
    int ss = ss_p.node; Port body = dup_hop(n, wire((Port){ss, 2}));
    if (body.node < 0 || body.node >= n->nn || n->dead[body.node]) return -1;
    if (body.node == sz && body.port == 1) return count;
    if (n->tag[body.node] == APP) {
      Port fn = dup_hop(n, wire((Port){body.node, 0}));
      if (fn.node == ss && fn.port == 1) { count++; cur = wire((Port){body.node, 2}); continue; }
    }
    return -1;
  }
  return -1;
}

/* Extract a float box (`_fsz` spine whose value is a fltbox index). */
int net_read_float(Net *n, Port p, double *out) {
  N = n; long count = 0; Port cur = p;
  for (int step = 0; step < n->nn; step++) {
    cur = dup_hop(n, cur);
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM || ctor_tag(NNM(n, cur.node)) != DT_FLOAT) return 0;
    int sz = cur.node; Port ss_p = dup_hop(n, wire((Port){sz, 2}));
    if (ss_p.node < 0 || ss_p.node >= n->nn || n->dead[ss_p.node] || n->tag[ss_p.node] != LAM || ctor_tag(NNM(n, ss_p.node)) != DT_FLOAT) return 0;
    int ss = ss_p.node; Port body = dup_hop(n, wire((Port){ss, 2}));
    if (body.node < 0 || body.node >= n->nn || n->dead[body.node]) return 0;
    if (body.node == sz && body.port == 1) { if (count < nfltbox) { *out = fltbox[count]; return 1; } return 0; }
    if (n->tag[body.node] == APP) {
      Port fn = dup_hop(n, wire((Port){body.node, 0}));
      if (fn.node == ss && fn.port == 1) { count++; cur = wire((Port){body.node, 2}); continue; }
    }
    return 0;
  }
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

static int unpack_arg(Net *n, Port p, long *out_val, char *str_buf, size_t str_max) {
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;
  if (ctor_tag(NNM(n, p.node)) == DT_FFI) {
    Val v = run_ffi(n, p);
    if (v.kind == 1 || v.kind == 3 || v.kind == 4) { *out_val = v.iv; return 1; }
    if (v.kind == 2) { snprintf(str_buf, str_max, "%s", v.sv); *out_val = (long)(intptr_t)str_buf; return 1; }
  }
  if (ctor_tag(NNM(n, p.node)) == DT_FLOAT) { double d; if (net_read_float(n, p, &d)) { memcpy(out_val, &d, 8); return 1; } }
  if (ctor_tag(NNM(n, p.node)) == DT_BOOL) { int b = net_read_bool(n, p); if (b >= 0) { *out_val = b; return 1; } }
  if (ctor_tag(NNM(n, p.node)) == DT_STR) {
    int len = net_read_string(n, p, str_buf, str_max); if (len >= 0) { *out_val = (long)(intptr_t)str_buf; return 1; }
  }
  long v = net_read_int(n, p); return v >= 0 ? (*out_val = v, 1) : 0;
}

static int unpack_args(Net *n, Port arg_p, long *args, char str_bufs[8][4096], int max_args) {
  int argc = 0; Port cur = skip_dup(n, arg_p);
  if (cur.node >= 0 && cur.node < n->nn && n->tag[cur.node] == LAM &&
      ctor_tag(NNM(n, cur.node)) == DT_STR) {
    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node >= 0 && bn.port == 0 && n->tag[bn.node] == LAM) {
      for (int step = 0; step < n->nn && argc < max_args; step++) {
        cur = skip_dup(n, cur);
        if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
        Port inner = skip_dup(n, wire((Port){cur.node, 2}));
        if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) break;
        Port body = skip_dup(n, wire((Port){inner.node, 2}));
        if (body.node < 0 || n->tag[body.node] != APP) break;
        Port ia = skip_dup(n, wire((Port){body.node, 0}));
        if (ia.node >= 0 && n->tag[ia.node] == APP) {
          unpack_arg(n, wire((Port){ia.node, 2}), &args[argc], str_bufs[argc], 4096); argc++;
        }
        cur = wire((Port){body.node, 2});
      }
      if (argc > 0) return argc;
    }
  }
  return unpack_arg(n, arg_p, &args[0], str_bufs[0], 4096) ? 1 : 0;
}

/* Check if root is an FFI invocation: \_ffi. \_ret. ((_ffi fn) args) */
/* Builtin dispatch: try one named FFI.  Simple int/bool/str builtins are one
   table row each (name -> kind/expr); anything else resolves via dlsym (always
   an int result).  Side-effectors that must run and not return a value
   (exit) are handled specially before the table. */
#define B1(n, e) if (!strcmp(fn, n)) { v.kind = 1, v.iv = (long)(e); return v; }
#define B3(n, e) if (!strcmp(fn, n)) { v.kind = 3, v.iv = (long)(e); return v; }
/* Resolve a wavefront reduction driver by name: "cpu" -> base engine, else a
   LinDriver symbol looked up by exact name, by lin_<name>_driver, or by loading
   <LIN_STD_DIR>/drivers/<name>.so as a plugin.  Open, uniform plugin protocol. */
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

/* ------------------------------------------------------------------ *
 *  General native scalar-op extension hook: run_ffi is *open* — a driver
 *  plugin registers ScalarOpFn providers that own classes of scalar ops
 *  (arith.so is the first; arithmetic stays out of the core).  First provider
 *  (registration order) that claims `fn` supplies the result; non-movable core
 *  C (memory/device/OS, float parsing, string compare, fold accounting) never
 *  routes through this.  outkind: 1 int, 3 bool, 4 float-bits. */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
static ScalarOpFn scalar_ops[16]; static int n_scalar_ops = 0;
void lin_scalar_ops_add(ScalarOpFn f) { if (n_scalar_ops < 16) scalar_ops[n_scalar_ops++] = f; }

/* dlopen a std/drivers plugin by its `<sym>_driver` symbol (idempotent); its
   constructor registers scalar-op providers with the core. */
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
  long c_args[8] = {0}; char sbufs[8][4096];
  int argc = unpack_args(n, wire((Port){a2.node, 2}), c_args, sbufs, 8);

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
  /* Delegate to registered native scalar-op providers (e.g. std/drivers/
     arith.so).  First provider that owns `fn` supplies the scalar result;
     anything unclaimed falls to the core's non-movable rows / dlsym. */
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
  if (!strcmp(fn, "lin_parse_float")) { double d = strtod(argc > 0 ? (char*)c_args[0] : "0", NULL); long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
  if (!strcmp(fn, "lin_float")) { double d = (double)c_args[0]; long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
  B3("lin_streq", argc >= 2 && !strcmp((char *)c_args[0], (char *)c_args[1]));
  B1("dlopen", (long)(intptr_t)dlopen(argc > 0 ? (char *)c_args[0] : NULL, RTLD_NOW | RTLD_GLOBAL));
  B1("puts", puts(argc > 0 ? (char *)c_args[0] : ""));
  if (!strcmp(fn, "getenv")) { char *ev = getenv(argc > 0 ? (char *)c_args[0] : ""); v.kind = 2; snprintf(v.sv, sizeof(v.sv), "%s", ev ? ev : "(null)"); return v; }
  fflush(stdout); void *sym = dlsym(RTLD_DEFAULT, fn);
  if (!sym) { fprintf(stderr, "ffi: symbol '%s' not found\n", fn); return v; }
  long (*f)() = (long (*)())sym;
  v.kind = 1; v.iv = (argc <= 0) ? f() : (argc == 1) ? f(c_args[0]) : (argc == 2) ? f(c_args[0], c_args[1]) :
           (argc == 3) ? f(c_args[0], c_args[1], c_args[2]) : f(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5], c_args[6], c_args[7]);
  return v;
}

/* Compute a saturated _ffi closure's concrete value (pure lin_* only).
   Shared by the head-fold and the eager argument-fold so composed arithmetic
   materialises regardless of position. */
static int ffi_ops_concrete(Net *n, Port lam); /* fwd */
int lin_precompile_depth = 0; /* set around def_precompile's net_reduce */
int lin_stuck_ffi_count = 0;  /* _ffi closure β-consumed during a free-var precompile */
static int lin_ffi_peek(Net *n, Port lam, Val *vout, int argfold) {
  if (lin_precompile_depth > 0) return 0; /* free-var body: don't fold yet */
  char fn[256];
  Port r = wire((Port){lam.node, 2});
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = wire((Port){r.node, 2});
  if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  Port a1 = wire((Port){a2.node, 0});
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return 0;
  if (net_read_string(n, wire((Port){a1.node, 2}), fn, sizeof(fn)) < 0) return 0;
  if (strncmp(fn, "lin_", 4)) return 0;      /* only pure lin_* builtins fold */
  if (!strncmp(fn, "lin_streq", 9)) return 0; /* needs C strings, keep readback */
  /* Saturation guard: only fold a FULLY-saturated closure whose operands are
     all concrete — otherwise the fold reads garbage and bakes a wrong value. */
  if (!ffi_ops_concrete(n, (Port){lam.node, 0})) return 0;
  if (argfold) {
    /* Eager argument-fold: only pure scalar INTEGER arithmetic/comparison
       closures are re-entrancy-safe to fold mid-reduction.  String-arg ops
       (lin_parse_float) and float-box results are excluded — they keep using
       head-fold + readback, which avoids the strtod-on-garbage regression. */
    static const char *safe[] = {
      "lin_add","lin_sub","lin_mul","lin_div","lin_mod","lin_pow",
      "lin_eq","lin_lt","lin_leq","lin_gt","lin_geq","lin_ffloor"
    };
    int ok = 0;
    for (int s = 0; s < (int)(sizeof safe / sizeof safe[0]); s++) if (!strcmp(fn, safe[s])) { ok = 1; break; }
    if (!ok) return 0;
  }
  Val v = run_ffi(n, (Port){lam.node, 0});
  if (v.kind != 1 && v.kind != 3 && v.kind != 4) return 0;
  if (argfold && v.kind == 4) return 0; /* floats stay on head-fold/readback */
  *vout = v; return 1;
}

/* Are all of `lam`'s operands concretely readable (Scott int / Church bool /
   float / string) or a recursively-foldable pure-lin_* closure?  Walks the
   arg `_cl`-spine like unpack_args (previously it landed on the APP node and
   validated only the FIRST operand, letting later non-concrete operands fold
   as garbage — the `(min 4 5)`-as-if stranding). */
static int ffi_ops_concrete(Net *n, Port lam) {
  Port r = wire((Port){lam.node, 2});
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = wire((Port){r.node, 2});
  if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  Port cur = skip_dup(n, wire((Port){a2.node, 2}));
  if (cur.node < 0 || cur.node >= n->nn || n->tag[cur.node] != LAM ||
      ctor_tag(NNM(n, cur.node)) != DT_STR) return 0;   /* arg list is a cons spine */
  if (skip_dup(n, wire((Port){cur.node, 2})).port != 0) return 0;
  for (int step = 0; step < n->nn; step++) {
    Port inner = skip_dup(n, wire((Port){cur.node, 2}));
    if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) return 1;
    Port body = skip_dup(n, wire((Port){inner.node, 2}));
    if (body.node < 0 || n->tag[body.node] != APP) return 1;
    Port ia = skip_dup(n, wire((Port){body.node, 0}));
    if (ia.node < 0 || n->tag[ia.node] != APP) return 1;
    Port ap = skip_dup(n, wire((Port){ia.node, 2}));
    if (ap.node < 0 || ap.node >= n->nn || n->dead[ap.node] || n->tag[ap.node] != LAM) return 0;
    if (ctor_tag(NNM(n, ap.node)) == DT_FLOAT) { double d; if (!net_read_float(n, ap, &d)) return 0; }
    else if (ctor_tag(NNM(n, ap.node)) == DT_BOOL) { if (net_read_bool(n, ap) < 0) return 0; }
    else if (ctor_tag(NNM(n, ap.node)) == DT_STR) { char sb[64]; if (net_read_string(n, ap, sb, sizeof sb) < 0) return 0; }
    else if (ctor_tag(NNM(n, ap.node)) == DT_FFI) {
      if (lin_precompile_depth > 0) return 0;           /* free-var context: not concrete */
      if (lin_ffi_needs_operand(n, ap)) return 0;       /* nested closure not fully concrete */
      Val nv = run_ffi(n, ap);
      if (nv.kind != 1 && nv.kind != 3 && nv.kind != 4) return 0;
    }
    else if (net_read_int(n, ap) < 0) return 0;
    cur = skip_dup(n, wire((Port){body.node, 2}));
  }
  return 1;
}

/* Non-destructive pre-scan for the reducer: 1 if a pure-lin `_ffi` closure is
   blocked solely because an operand is not yet concrete (e.g. a still-live
   `(min 4 5)` result) rather than malformed — so the reducer DEFERS the
   head-redex instead of β-destroying the closure (the confluence-preserving
   routing behind the composed-`if` fix). */
int lin_ffi_needs_operand(Net *n, Port lam) {
  if (n->dead[lam.node] || n->tag[lam.node] != LAM) return 0;
  if (n->name[lam.node] && ctor_tag(n->name[lam.node]) != DT_FFI) return 0;
  return !ffi_ops_concrete(n, lam);
}

/* Fold a saturated _ffi closure into a concrete net value during reduction, so
   FFI results (notably float comparisons -> Church booleans) become usable by
   Scott consumers instead of only materialising at readback.  Only PURE `lin_*`
   arithmetic/comparison closures are folded; side-effecting FFI (puts, exit,
   dlopen, driver_set, getenv) stays readback-only. */
static Port val_to_port(Net *n, Val v) {           /* alloc concrete value node */
  if (v.kind == 1) return net_alloc_scott(n, v.iv);
  if (v.kind == 3) return net_alloc_bool(n, (int)v.iv);
  double d; memcpy(&d, &v.iv, 8); return net_alloc_float(n, d);
}
int lin_fold_ffi(Net *n, Port lam, Port app) {
  Val v; N = n;
  if (!lin_ffi_peek(n, lam, &v, 0)) {
    /* During an open free-var precompile, a _ffi closure consumed as a
       boolean/function cannot fold (operands not concrete) and would be
       β-destroyed; flag the containing def as uncacheable. */
    if (lin_precompile_depth > 0) lin_stuck_ffi_count++;
    return 0;
  }
  Port res = val_to_port(n, v);
  n->dead[lam.node] = 1;
  n->declines = 0; /* a fold is real progress: reset the deferral budget */
  net_link(n, res, (Port){app.node, 0}, 1);
  return 1;
}

/* Fold saturated `_ffi` closures wherever they are embedded (not just at a
   beta head/arg), so closures captured inside a caller's body (e.g. the `n` of
   `\_sz \_ss (_ss n)` in `succ (mul 2 2)`) still materialise at a fixed point.
   Scans non-dead LAM nodes named `_ffi`; for each saturated pure-scalar closure,
   replaces it in place by linking its concrete value to the closure's own
   output wire.  Returns how many were folded (0 = none). */
int lin_fold_ffi_arg(Net *n, Port lam, Port out) {
  Val v; N = n;
  if (lam.port != 0 || lam.node < 0 || lam.node >= n->nn || n->dead[lam.node] || n->tag[lam.node] != LAM) return 0;
  if (ctor_tag(n->name[lam.node] ? n->name[lam.node] : "") != DT_FFI) return 0;
  if (!lin_ffi_peek(n, lam, &v, 1)) return 0;
  /* Only fold concrete INTEGER / BOOL scalar results as beta arguments.  Float
     closures keep using the head-fold + readback path (floats are box-index
     encoded and re-linking mid-beta is unsafe), which also covers the
     composed-float cases (`(fadd (float "2.5") (float "3.5"))`). */
  if (v.kind != 1 && v.kind != 3) return 0;
  Port res = val_to_port(n, v);
  n->dead[lam.node] = 1;
  net_link(n, res, out, 1);
  return 1;
}

Port net_alloc_bool(Net *n, int val) {
  Scope sc = scope_nil(); Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);
  net_link(n, (Port){bf.node, 2}, (Port){val ? bt.node : bf.node, 1}, 0);
  return (Port){bt.node, 0};
}

Port net_alloc_scott(Net *n, long k) { return alloc_scott(n, k); }

/* Readback / IO-effect runtime lives in std (not the core); included here so it
   shares this TU's statics (N, wire, skip_dup, dup_hop, run_ffi). */
#include "../std/runtime/io.c"

