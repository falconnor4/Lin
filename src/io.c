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

long net_read_int(Net *n, Port p) {
  N = n; long count = 0; Port cur = p;
  for (int step = 0; step < n->nn; step++) {
    cur = dup_hop(n, cur);
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
  B1("lin_add", c_args[0] + c_args[1]);
  B1("lin_sub", c_args[0] >= c_args[1] ? c_args[0] - c_args[1] : 0);
  B1("lin_mul", c_args[0] * c_args[1]);
  B1("lin_div", c_args[1] ? c_args[0] / c_args[1] : 0);
  B1("lin_mod", c_args[1] ? c_args[0] % c_args[1] : 0);
  B1("lin_pow", ({ long b = c_args[0], e = c_args[1], r = 1; while (e > 0) { if (e & 1) r *= b; b *= b; e >>= 1; } r; }));
  /* float builtins: args are IEEE-754 bits carried as longs; result kind=4 */
  #define FA(n, e) if (!strcmp(fn, n)) { double a, b; memcpy(&a, &c_args[0], 8); memcpy(&b, &c_args[1], 8); double r = (e); long rb; memcpy(&rb, &r, 8); v.kind = 4; v.iv = rb; return v; }
  #define FU(n, e) if (!strcmp(fn, n)) { double a; memcpy(&a, &c_args[0], 8); double r = (e); long rb; memcpy(&rb, &r, 8); v.kind = 4; v.iv = rb; return v; }
  #define FC(n, e) if (!strcmp(fn, n)) { double a, b; memcpy(&a, &c_args[0], 8); memcpy(&b, &c_args[1], 8); v.kind = 3; v.iv = (e); return v; }
  FA("lin_fadd", a + b);   FA("lin_fsub", a - b);
  FA("lin_fmul", a * b);   FA("lin_fdiv", b != 0.0 ? a / b : 0.0);
  FU("lin_fsqrt", a >= 0.0 ? sqrt(a) : 0.0);
  FU("lin_fsin", sin(a));  FU("lin_fcos", cos(a));  FU("lin_ftan", tan(a));
  FA("lin_fatan2", atan2(a, b));   FA("lin_fpow", pow(a, b));
  FC("lin_feq", a == b);   FC("lin_flt", a < b);   FC("lin_fleq", a <= b);
  #undef FA
  #undef FU
  #undef FC
  B1("lin_ffloor", ({ double a; memcpy(&a, &c_args[0], 8); (long)floor(a); }));
  if (!strcmp(fn, "lin_folds")) { v.kind = 1; v.iv = lin_fold_total(); return v; }
  B3("lin_folded", lin_fold_total() > 0);
  if (!strcmp(fn, "lin_parse_float")) { double d = strtod(argc > 0 ? (char*)c_args[0] : "0", NULL); long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
  if (!strcmp(fn, "lin_float")) { double d = (double)c_args[0]; long rb; memcpy(&rb, &d, 8); v.kind = 4; v.iv = rb; return v; }
  B3("lin_streq", argc >= 2 && !strcmp((char *)c_args[0], (char *)c_args[1]));
  B3("lin_eq", c_args[0] == c_args[1]);  B3("lin_lt", c_args[0] < c_args[1]);
  B3("lin_leq", c_args[0] <= c_args[1]); B3("lin_gt", c_args[0] > c_args[1]);
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

/* Render one decoded value to a stream (1=int, 2=str, 3=bool, 4=float); returns
   1 if a value rendered, 0 if none. */
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

/* Print a port representation to stdout */
static void print_port(Port p, int depth) {
  if (depth > N->nn || p.node < 0 || p.node >= N->nn) { putchar('?'); return; }
  if (N->dead[p.node]) { putchar('_'); return; }
  if (N->tag[p.node] == LAM && p.port == 1) { fputs(NNM(N, p.node), stdout); return; }
  if (vis_print && vis_print[p.node]) { putchar('?'); return; }
  if (vis_print) vis_print[p.node] = 1;
  switch (N->tag[p.node]) {
  case ROOT: print_port(wire(p), depth + 1); break;
  case ERA: putchar('_'); break;
  case DUP: print_port(p.port == 0 ? wire((Port){p.node, 1}) : wire((Port){p.node, 0}), depth + 1); break;
  case APP:
    putchar('('); print_port(wire((Port){p.node, 0}), depth + 1); putchar(' ');
    print_port(wire((Port){p.node, 2}), depth + 1); putchar(')'); break;
  case LAM:
    if (p.port == 1) { fputs(NNM(N, p.node), stdout); break; }
    if (p.port == 0) {
      long v = net_read_int(N, p); if (v >= 0) { printf("%ld", v); break; }
      int b = net_read_bool(N, p); if (b >= 0) { fputs(b ? "true" : "false", stdout); break; }
      printf("(\\%s ", NNM(N, p.node)); print_port(wire((Port){p.node, 2}), depth + 1); putchar(')'); break;
    }
    print_port(wire(p), depth + 1); break;
  }
  if (vis_print) vis_print[p.node] = 0;
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
  vis_print = calloc((size_t)(n->nn + 1), 1);
  print_port(r, 0);
  free(vis_print); vis_print = NULL;
  return 0;
}

Port net_alloc_bool(Net *n, int val) {
  Scope sc = scope_nil(); Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);
  net_link(n, (Port){bf.node, 2}, (Port){val ? bt.node : bf.node, 1}, 0);
  return (Port){bt.node, 0};
}

Port net_alloc_scott(Net *n, long k) { return alloc_scott(n, k); }

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

/* Apply effect continuation `fn` to value `arg`, relink ROOT, and re-reduce:
   the single monadic step shared by every effect (print/read/wait/ffi). */
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

