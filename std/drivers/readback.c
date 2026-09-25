/* ============================================================================
 * readback.c -- observing a reduced net: decode, print, run effects, dispatch FFI.
 *
 * The core reduces and shares.  Turning the reduced net back into a value -- decoding a
 * port, printing the net, running its effects, and the FFI dispatch those need -- is not
 * reduction, so it is not the core's: this driver supplies it, and the core keeps three
 * thin dispatchers (src/io.c net_print / net_run_io / net_read_value) that hand the work
 * to whichever driver declares LIN_WANT_READBACK.
 *
 * NO NODE CARRIES A NAME, so every value read here is read under an EXPECTATION:
 *
 *   - the OBSERVED RESULT is read as the DOMAIN the program's type says it means.  main.c
 *     type-checks every top-level form, so the meaning is known and is passed into net_print;
 *     Scott zero, Church TRUE and the empty list are one net, and only that expectation can
 *     tell them apart.  When the type says nothing (`.line` artifacts, a form of arrow type),
 *     the printer decodes only the shapes ONE domain claims and writes the net itself for the
 *     rest -- the honest fallback, never a guess.
 *   - an `_ffi` call's OPERANDS are read as the SIGNATURE of the symbol being called (the
 *     language's FFI convention, declared once per symbol below): a net cannot carry the C
 *     types of a call, and the caller is the only place that knows them.
 *   - an `_op`/`_ffi` HEADER is recognized by shape (std/runtime/pattern.h), and the OPERATOR
 *     of an `_op` is the first slot of its operand list -- an index into the language's op
 *     vocabulary (std/num.lin), because "which operator" is not in the wiring.
 *
 * The cut from the core is by REACHABILITY, not taste: everything here is reachable only from
 * printing, from an effect, or from `_ffi` dispatch.  What stayed in the core is what a driver
 * calls back into -- the encoding readers (net_read_int / net_read_string / net_read_float), the
 * one arg-spine decoder (net_spine_args / net_ffi_args), the force that keeps a port naming its
 * value across a reduction (net_force_val) and the fan walk a SHARED subterm is reached through
 * (net_dup_hop).  Those are net structure and reduction; this file is policy about how an
 * observed value is written down.
 *
 * A PROVIDER, not a strategy: LIN_CAP_PROVIDER, so `(set_driver ...)` -- which selects a
 * reducer and must not drop infrastructure the runtime depends on -- leaves readback
 * registered, exactly as values.c does for value storage.
 *
 * carry_save writes an EMPTY section on purpose.  A `.line` artifact runs with NO prelude,
 * so no `(set_driver "readback")` form is ever evaluated again at run time; a zero-length
 * NAMED section is what makes the artifact load this driver by name and therefore still
 * print (src/net.c lin_driver_carry_write / lin_driver_carry_read).
 * ==========================================================================*/
#include "../../src/lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <unistd.h>
#include <dlfcn.h>
#include <stdlib.h>

static Net *N;
/* The net writer, defined beside `print_body` and declared here because the io path prints a message
   with it too -- the same renderer, so the two can never drift. */
static void print_struct(FILE *f, Port r, int domain);
/* Where readback's VALUE is written.  The core owns the stream: a prelude load aims it at a sink so
   the effects its top-level forms perform still run (dispatch happens HERE) without joining the
   program's own output, which a `; expect` line would then be one line off from. */
#define OUT (lin_out ? lin_out : stdout)
static inline Port wire(Port p) { return N->wire[p.node * 3 + p.port]; }
static inline int live(Port p) { return p.node >= 0 && p.node < N->nn && !N->dead[p.node]; }

/* render one decoded value to a stream (1=int, 2=str, 3=bool, 4=float); returns 1 if rendered, else 0 */
static int render_val(FILE *f, Val v) {
  if (v.kind == 1) fprintf(f, "%ld", v.iv);
  else if (v.kind == 2) fputs(v.sv, f);
  else if (v.kind == 3) fputs(v.iv ? "true" : "false", f);
  else if (v.kind == 4) { double d; memcpy(&d, &v.iv, 8); fprintf(f, "%g", d); }
  else return 0;
  fflush(f); return 1;
}

/* ---------------- value decoding, under an expectation or without one ----------------
   `decode` is the expectation: the caller states the DOMAIN the value means, and the registry
   (src/io.c) turns that into the encoding its structure must have.  A value whose structure is
   not that domain's -- including one the reduction has not reached -- reads as kind 0, which is
   the caller's cue to write the net instead. */
static Val decode(Net *n, Port p, int domain) {
  Val v = {0};
  switch (domain) {
  case DT_NUM: { long x = net_read_int(n, p, LIN_ENC_NUM); if (x >= 0) { v.iv = x; v.kind = 1; } break; }
  case DT_BOOL: { long b = net_read_int(n, p, LIN_ENC_BOOL); if (b >= 0) { v.iv = b; v.kind = 3; } break; }
  case DT_STR: if (net_read_string(n, p, LIN_ENC_NUM, v.sv, sizeof v.sv) >= 0) v.kind = 2; break;
  case DT_FLOAT: { double d; if (net_read_float(n, p, &d)) { memcpy(&v.iv, &d, 8); v.kind = 4; } break; }
  /* DT_FFI deliberately has NO case: dispatching a closure is `run_ffi`, which the callers do
     explicitly.  Routing it through here would call back into net_read_value, which is where this
     decode is reached from, and that is an infinite regress rather than a decode. */
  default: break;
  }
  return v;
}

/* Is `p` a STRING the structure determines on its own?  A cell chain whose payloads are numbers
   with at least one layer each: a payload that is the bare terminal (`\b0.\b1.b0`) is the same net
   as TRUE and as nil, so reading it as a character would be a guess -- and `net_read_string` has
   no way to know that, which is why this check exists here and not there. */
static int str_determined(Net *n, Port p, char *buf, size_t max) {
  size_t len = 0;
  Port cur = p;
  for (int step = 0; step < n->nn && len + 1 < max; step++) {
    Port head, tail;
    if (!net_read_cell(n, cur, &head, &tail)) {
      long k = net_read_int(n, cur, LIN_ENC_STR);      /* the nil terminal ends the chain */
      if (k == 0) { buf[len] = 0; return len > 0; }
      break;
    }
    long ch = net_read_int(n, head, LIN_ENC_NUM);
    if (ch <= 0 || ch > 255) break;                    /* a bare terminal payload: ambiguous */
    buf[len++] = (char)ch;
    cur = tail;
  }
  if (len > 0) { buf[len] = 0; return 1; }
  return 0;
}

/* WHAT AN UNLABELLED NET READS AS.  With no expectation to state, only the shapes ONE domain
   claims are decoded: an `_ffi` closure (dispatching it IS the observation), a float box (its own
   shape, with the provider's table as the authority), a NUMERAL CHAIN (one layer or more), and a
   string that the structure determines.  A shape TWO domains claim is NOT decoded: `\b0.\b1.b0`
   is the numeral zero, TRUE and the empty list at once, and the geometry cannot choose. */
static Val value_any(Net *n, Port p) {
  Val v = {0};
  double d;
  if (net_read_float(n, p, &d)) { memcpy(&v.iv, &d, 8); v.kind = 4; return v; }
  long k = net_read_int(n, p, LIN_ENC_NUM);
  if (k > 0) { v.iv = k; v.kind = 1; return v; }
  if (str_determined(n, p, v.sv, sizeof v.sv)) { v.kind = 2; return v; }
  return v;                                            /* kind 0: the caller writes the net */
}

/* resolve a driver: "cpu" -> base engine, else LinDriver sym / lin_<name>_driver / std/drivers plugin */
static void *resolve_driver(const char *dn) {
  if (!strcmp(dn, "cpu")) return NULL;
  char sym[NAME + 16]; snprintf(sym, sizeof sym, "lin_%s_driver", dn);
  void *s = dlsym(RTLD_DEFAULT, dn);
  if (!s) s = dlsym(RTLD_DEFAULT, sym);
  /* The core's loader is what dlopens `$LIN_STD_DIR/drivers/<name>.so`; a plugin's construction
     registers it with the core, which is why finding it here is enough to have it dispatched. */
  if (!s && lin_driver_load(dn)) s = dlsym(RTLD_DEFAULT, sym);
  return s;
}

/* ---------------- the FFI convention ----------------
   What an `_ffi` call's OPERANDS mean is the SIGNATURE of the symbol, and this table is where the
   language states it -- the net cannot, because a closure's argument list is a spine of values whose
   shapes are shared with every other domain.  A symbol whose operands are all `long` (which is what
   the dispatch below passes) needs no row: the DEFAULT is the number domain.  The float family is
   recognized by the `lin_f` prefix the std's float module uses. */
static int is_float_fn(const char *fn) {
  if (strncmp(fn, "lin_f", 5)) return 0;
  /* the exceptions inside the prefix: the fold counters, the int->float cast, and the string parse */
  return strcmp(fn, "lin_folds") && strcmp(fn, "lin_folded") && strcmp(fn, "lin_float") &&
         strcmp(fn, "lin_parse_float");
}
static int str_fn(const char *fn) {
  return !strcmp(fn, "puts") || !strcmp(fn, "getenv") || !strcmp(fn, "system") ||
         !strcmp(fn, "dlopen") || !strcmp(fn, "lin_parse_float") || !strcmp(fn, "fopen") ||
         !strcmp(fn, "driver_set") || !strcmp(fn, "driver_add");
}
/* the domain slot `i` of the call `fn` is in (`ndoms` entries, the last one repeating) */
static void arg_doms(const char *fn, int doms[2], int *ndoms) {
  int two_str = !strcmp(fn, "lin_streq") || !strcmp(fn, "fopen");
  if (is_float_fn(fn)) { doms[0] = DT_FLOAT; *ndoms = 1; }
  else if (two_str) { doms[0] = DT_STR; doms[1] = DT_STR; *ndoms = 2; }
  else if (str_fn(fn)) { doms[0] = DT_STR; *ndoms = 1; }
  else { doms[0] = DT_NUM; *ndoms = 1; }
}

/* Builtin dispatch: table rows for simple int/bool/str; side-effectors (exit) handled before the table, else dlsym. */
#define B3(n, e) if (!strcmp(fn, n)) { v.kind = 3; v.iv = (long)(e); return v; }

static Val run_ffi(Net *n, Port p) {
  Val v = {0};
  N = n;
  p = net_dhop(n, p);
  Port a1, argp;
  /* The header is the closure's SHAPE (\_ffi.\_ret.((_ffi <fn>) <args>)), which is what a net with
     no labels can offer: which symbol it is lives in its own argument list, as a string.  The dig is
     PURE, so asking it about a port that turns out not to be a closure costs two wires and cannot
     reduce anything. */
  if (!net_ffi_header(n, (Port){p.node, 0}, &a1, &argp)) return v;
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return v;

  char fn[256];
  /* A NON-EMPTY name: `net_read_string` answers 0 for a nil payload, and the header SHAPE is shared
     with the std's own `ccallN` helpers (`\fn.\args.((_ffi fn) args)`), so the empty read is how such
     a helper used to be dispatched as a call to the symbol "" (measured on `(v3scale 2.0 (vec3 ...))`).
     No foreign symbol is nameless, so the empty read is not this closure. */
  if (net_read_string(n, wire((Port){a1.node, 2}), LIN_ENC_NUM, fn, sizeof(fn)) <= 0) return v;
  int doms[2], ndoms;
  arg_doms(fn, doms, &ndoms);
  Val fargs[8] = {{0}};
  int argc = net_spine_args(n, argp, doms, ndoms, fargs, 8);
  /* Never call a symbol unless every operand is there: guessing the arity called libc `getenv()` with
     no arguments at all and segfaulted (a three-deep `_ffi` nest inside a precompiled define).  Fewer
     decoded values than slots = not foldable yet, so decline and let the redex be retried. */
  int slots = net_spine_slots(n, argp);
  if (slots < 0 ? argc != 0 : (slots > 8 || argc < slots)) return v;
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
  /* Delegate to the core's registry of native scalar-op providers (e.g. arith.so); the first provider
     that owns `fn` supplies it, and the registry pulls std/drivers/arith.so in on its first ask. */
  long out; int okind = 0;
  if (lin_scalar_ops_run(fn, argc, c_args, &out, &okind)) {
    if (okind == 4) v.kind = 4;
    else if (okind == 3) v.kind = 3;
    else v.kind = 1;
    v.iv = out;
    return v;
  }
  if (!strcmp(fn, "lin_folds")) { v.kind = 1; v.iv = lin_fold_total(); return v; }
  B3("lin_folded", lin_fold_total() > 0);
  /* String-typed-arg only: a closure carrying an INT/BOOL/FLOAT where a
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

static int net_try_ffi(Net *n, Port p) {
  return render_val(OUT, run_ffi(n, p));
}

/* ---------------- the effect encoding ----------------
   std/io.lin writes an effect as

       \e. ((((e <code>) p0) p1) p2)

   -- the tag's OWN binder applied to the effect's CODE first, then its payloads.  A code is a
   numeral of the language's number encoding, which is how the language states an index, and it is
   what makes the effects tellable apart with no label: `io_print msg next` and `io_wait src cb` are
   OTHERWISE THE SAME NET (a payload and a continuation).  The code's payload count is fixed
   (below), so a lambda that merely applies its own binder to a number is not mistaken for one. */
enum { EFF_DONE = 0, EFF_PRINT, EFF_WRITE, EFF_WAIT, EFF_N };
/* How many payloads each code carries.  EVERY code carries at least two, and that is what keeps an
   effect apart from the language's own data: `\k.((k a) b)` is a PAIR and `\c.\n.((c h) t)` is a LIST
   CELL, so an effect with fewer payloads than two would make every such VALUE read as a finished
   effect -- measured: `(pair true false)` printed nothing, swallowed as `io_done`. */
static const int eff_pay[EFF_N] = { 2, 2, 3, 2 };

/* dig the effect at `p`: 1 when `p` is one, with its code and its payload ports in APPLICATION
   order (pay[0] is applied first).  The OBSERVED port is forced -- an effect is only there once the
   reduction reached it -- and the body below it is then READ, never demanded: forcing a payload or a
   continuation here would evaluate work nothing asked for, and on a recursive net that is what
   unrolls the knot the reducer deliberately left alone (the code is a literal numeral, so reading it
   costs nothing). */
static int eff_dig(Net *n, Port p, int *code, Port pay[3], int *npay) {
  Port l = net_dup_hop(n, net_force_val(n, p));
  if (l.node < 0 || l.node >= n->nn || n->dead[l.node] || n->tag[l.node] != LAM) return 0;
  Port cur = net_dhop(n, wire((Port){l.node, 2}));
  Port tmp[3]; int np = 0;
  for (int step = 0; step < 8; step++) {
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || cur.port != 1 ||
        n->tag[cur.node] != APP) return 0;
    Port fn = net_dhop(n, wire((Port){cur.node, 0}));
    if (fn.node == l.node && fn.port == 1) {           /* the tag's own binder: the code is here */
      long c = net_read_int(n, wire((Port){cur.node, 2}), LIN_ENC_NUM);
      if (c < 0 || c >= EFF_N || np != eff_pay[c]) return 0;
      for (int i = 0; i < np; i++) pay[i] = tmp[np - 1 - i];
      if (npay) *npay = np;
      if (code) *code = (int)c;
      return 1;
    }
    if (np >= 3) return 0;
    tmp[np++] = wire((Port){cur.node, 2});
    cur = net_dhop(n, wire((Port){cur.node, 0}));
  }
  return 0;
}

/* A non-forcing "is this an effect?" test, for the continuation check below: the shape only. */
static int eff_shape(Net *n, Port p) {
  for (int step = 0; step < n->nn && p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP; step++)
    p = p.port == 0 ? wire((Port){p.node, 1}) : wire((Port){p.node, 0});
  if (!live(p) || n->tag[p.node] != LAM) return 0;
  Port cur = wire((Port){p.node, 2});
  for (int step = 0; step < 8; step++) {
    if (!live(cur) || cur.port != 1 || n->tag[cur.node] != APP) return 0;
    Port fn = wire((Port){cur.node, 0});
    if (fn.node == p.node && fn.port == 1) return n->tag[wire((Port){cur.node, 2}).node] != ERA;
    cur = wire((Port){cur.node, 0});
  }
  return 0;
}

/* The string encoding, built here because readback is who needs one (an input line, a command's
   output): cells of character-code numerals, with the nil terminal. */
static Port net_alloc_string(Net *n, const char *s) {
  Scope sc = scope_nil();
  Port c_nil = net_alloc(n, LAM, sc), n_nil = net_alloc(n, LAM, sc);
  net_link(n, (Port){c_nil.node, 2}, (Port){n_nil.node, 0}, 0);
  net_link(n, (Port){n_nil.node, 2}, (Port){n_nil.node, 1}, 0);      /* select-second: the nil cell */
  Port cur = (Port){c_nil.node, 0};
  for (long i = (long)strlen(s) - 1; i >= 0; i--) {
    Port ch = net_alloc_scott(n, (unsigned char)s[i]);
    Port c_lam = net_alloc(n, LAM, sc), n_lam = net_alloc(n, LAM, sc);
    Port a1 = net_alloc(n, APP, sc), a2 = net_alloc(n, APP, sc);
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

/* apply effect continuation `fn` to value `arg`, relink ROOT, and re-reduce: the single monadic step shared by every effect (print/read/wait/ffi) */
static void eff_apply(Net *n, Port fn, Port arg) {
  Port app = net_alloc(n, APP, scope_nil());
  net_link(n, (Port){app.node, 0}, fn, 1); net_link(n, (Port){app.node, 2}, arg, 1);
  net_link(n, (Port){0, 0}, (Port){app.node, 1}, 1);
}

static long run_io_body(Net *n, long step_limit) {
  N = n;
  int did_io = 0;
  for (;;) {
    Port r = net_dup_hop(n, net_force_val(n, wire((Port){0, 0})));  /* an effect is only visible once reached */
    int code; Port pay[3]; int npay;
    if (!eff_dig(n, r, &code, pay, &npay)) break;
    if (code == EFF_DONE) return 1;
    if (code == EFF_PRINT || code == EFF_WRITE) {
      FILE *out_fp = stdout;
      Port msg_p, next_p;
      if (code == EFF_WRITE) {                          /* `io_write_to dst msg next`: dst 2 = stderr */
        long dst = net_read_int(n, pay[0], LIN_ENC_NUM);
        if (dst == 2) out_fp = stderr;
        msg_p = pay[1]; next_p = pay[2];
      } else { msg_p = pay[0]; next_p = pay[1]; }
      if (!net_try_ffi(n, msg_p)) {
        Val mv = value_any(n, msg_p);
        /* A message the structure does not determine -- `(io_print (not false) ...)` hands over the
           bare terminal, which is the numeral zero, TRUE and nil at once -- is written as the NET IT
           IS, exactly as the top-level readback writes one.  There is no expectation to decode it
           with: an effect payload carries no domain (the `_eff` encoding states a payload COUNT and
           nothing else, std/io.lin), and the reader that used to resolve this read it off the node's
           carrier name, which is the thing this net no longer has.  Guessing a domain would be the
           name-sniffing the design removed; `?` was not an answer at all. */
        if (!render_val(out_fp, mv)) print_struct(out_fp, msg_p, -1);
      }
      fflush(out_fp);
      /* The continuation is applied to a unit value unless it IS already an effect (a monadic
         chain): an effect value is what the program returns, so it must not be applied to one. */
      if (live(next_p) && n->tag[next_p.node] == LAM && !eff_shape(n, next_p))
        eff_apply(n, next_p, net_alloc_scott(n, 0));
      else net_link(n, (Port){0, 0}, next_p, 1);
      net_reduce(n, step_limit);
      did_io = 1;
      continue;
    }
    /* EFF_WAIT: `io_wait src cb`.  The source may be a descriptor, a command, a file, a timer or an
       FFI result, and the answer is handed to the continuation -- as a bool, a number or a string,
       whichever the source produced. */
    {
      Port src_p = pay[0], cb = pay[1];
      char in_buf[4096] = {0};
      long res_int = -1; int is_int = 0;
      Val fv = (src_p.node >= 0) ? run_ffi(n, src_p) : (Val){0};
      if (fv.kind == 1) { res_int = fv.iv; is_int = 1; }
      else if (fv.kind == 3) is_int = 2;                      /* bool result */
      else if (fv.kind == 2) snprintf(in_buf, sizeof(in_buf), "%s", fv.sv);
      else if (src_p.node < 0) read_stdin(in_buf, sizeof(in_buf));
      else {
        long fd = net_read_int(n, src_p, LIN_ENC_NUM);
        if (fd == 0) read_stdin(in_buf, sizeof(in_buf));
        else if (fd > 0) { ssize_t nr = read((int)fd, in_buf, sizeof(in_buf) - 1); if (nr > 0) { in_buf[nr] = 0; chomp(in_buf); } }
        else {
          char src[1024];
          if (net_read_string(n, src_p, LIN_ENC_NUM, src, sizeof(src)) >= 0) {
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
  }
  return did_io;
}

/* ---------------- value rendering, net printer ---------------- */

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
static int *viz_depth = NULL;      /* ... and the binder depth it was rendered at (see pp_push) */
static long qmarks = 0;            /* '?' (unexpressible sharing / over-depth) marks emitted so far */
static long dmarks = 0;            /* '_' marks emitted for a node the reduction DISCARDED */

/* The binders currently being printed, innermost last.  An occurrence carries no name of its own --
   print_port renders it from the binder node its wire leads to -- and a net has no stored name to
   fall back on: a source binder name is not part of the net's MEANING (α-equivalent nets ARE one
   net).  The printer therefore GENERATES the name at render time from the binder DEPTH it
   introduces: a, b, ... z, a1, ... .  Depth is what a reader needs -- nested binders never collide,
   and two sibling binders may share a name because their scopes do not overlap -- and it is
   deterministic, so the same net always prints the same text. */
static struct { int node; char printed[NAME]; } *pp_stack;
static int pp_top = 0, pp_cap = 0;

static void binder_name(int depth, char *out, size_t outsz) {
  int d = depth < 0 ? 0 : depth;
  if (d < 26) snprintf(out, outsz, "%c", 'a' + d);
  else snprintf(out, outsz, "%c%d", 'a' + (d % 26), d / 26);
}
static const char *pp_lookup(int node) {
  for (int i = pp_top - 1; i >= 0; i--) if (pp_stack[i].node == node) return pp_stack[i].printed;
  return NULL;
}
static const char *pp_push(int node) {
  if (pp_top >= pp_cap) pp_stack = realloc(pp_stack, (size_t)(pp_cap = pp_cap ? pp_cap * 2 : 32) * sizeof *pp_stack);
  pp_stack[pp_top].node = node;
  binder_name(pp_top, pp_stack[pp_top].printed, NAME);
  return pp_stack[pp_top++].printed;
}

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
/* render a decoded value into the output buffer; 1 when it rendered */
static int ob_val(Val v) {
  if (v.kind == 1) ob_printf("%ld", v.iv);
  else if (v.kind == 2) { ob_putc('"'); ob_puts(v.sv); ob_putc('"'); }
  else if (v.kind == 3) ob_puts(v.iv ? "true" : "false");
  else if (v.kind == 4) { double d; memcpy(&d, &v.iv, 8); ob_printf("%g", d); }
  else return 0;
  return 1;
}

/* Render a port representation into the output buffer.

   `dom` is the DOMAIN the position is expected to mean (-1 = the caller has none): the observed
   result's type at the root, and nothing below it -- a net does not type its own subterms, and
   inventing one is the guess this whole design refuses to make.  With no expectation, only the
   shapes ONE domain claims are decoded (value_any) and everything else prints as the net it is.

   SHARED NORMAL FORMS -- the marker below is not a bug to "fix" by unfolding.  Optimal sharing leaves
   normal forms that are not trees, and arriving back at a node already on the print stack emits `?`.
   The VALUE is unaffected (applying the knot gives the exact answer).  Unfolding was measured and is
   WRONG as well as costly: it under-counts on one fan branch and over-counts on re-entry, because a
   knot is genuinely recursive.  Readback prints the sharing and reports the marker on stderr so it can
   never pass for an answer. */
static void print_port(Port p, int depth, int dom) {
  if (p.node < 0 || p.node >= N->nn) { ob_putc('?'); qmarks++; return; }
  /* Everything the printer is about to render is observed, so it is forced first: under needed
     order a sub-term the program never demanded is still an unreduced thunk, and printing it as
     written would report the term instead of its value. */
  p = net_force_val(N, p);
  if (depth > N->nn || p.node < 0 || p.node >= N->nn) { ob_putc('?'); qmarks++; return; }
  if (N->dead[p.node]) { ob_putc('_'); dmarks++; return; }
  if (N->tag[p.node] == LAM && p.port == 1) {
    const char *nm = pp_lookup(p.node);
    /* An occurrence whose binder is not on the print stack: the shared net has no tree that binds
       it, which is the same thing the `?` mark says everywhere else. */
    if (nm) ob_puts(nm); else { ob_putc('?'); qmarks++; }
    return;
  }
  size_t key = (size_t)p.node * 3 + (size_t)p.port;
  int in_vis = (size_t)p.node < vis_cap, in_txt = key < vis_cap * 3;
  if (viz_txt && in_txt && viz_txt[key] && viz_depth[key] == pp_top) { ob_puts(viz_txt[key]); return; }
  if (vis_print && in_vis && vis_print[p.node]) { ob_putc('?'); qmarks++; return; }
  if (vis_print && in_vis) vis_print[p.node] = 1;
  long q0 = qmarks; size_t o0 = ob_len;
  switch (N->tag[p.node]) {
  case ROOT: print_port(wire(p), depth + 1, dom); break;
  case ERA: ob_putc('_'); break;
  case DUP: print_port(p.port == 0 ? wire((Port){p.node, 1}) : wire((Port){p.node, 0}), depth + 1, dom); break;
  case APP:
    ob_putc('('); print_port(wire((Port){p.node, 0}), depth + 1, -1); ob_putc(' ');
    print_port(wire((Port){p.node, 2}), depth + 1, -1); ob_putc(')'); break;
  case LAM:
    if (p.port == 0) {
      /* AN `_FFI` CLOSURE'S VALUE IS WHAT DISPATCHING IT PRODUCES, and that is true of a closure
         NESTED in the term as much as of the observed result -- `print_body` already dispatches the
         result, and a tuple slot (`(v3y (vec3 0.0 (fmul 2.0 2.0) 0.0))`) went undecoded without this
         and printed as the closure it is written as.  The dig is pure and two wires deep on a port
         that turns out not to be a closure, so asking first costs nothing. */
      if (ob_val(run_ffi(N, p))) break;
      if (dom >= 0 ? ob_val(decode(N, p, dom)) : ob_val(value_any(N, p))) break;
      ob_printf("(\\%s ", pp_push(p.node));
      print_port(wire((Port){p.node, 2}), depth + 1, -1); ob_putc(')'); pp_top--; break;
    }
    print_port(wire(p), depth + 1, dom); break;
  }
  if (vis_print && in_vis) vis_print[p.node] = 0;
  /* Memoise only context-free renders: a '?' on the way in means this text was shaped by an
     in-progress ancestor (a real cycle), so it must not be replayed -- and neither may a text
     whose binder names were generated for a DIFFERENT depth, which is why the depth is stored
     beside it (an α-name is a function of the scope the text lands in). */
  if (viz_txt && in_txt && qmarks == q0) {
    size_t k = ob_len - o0;
    char *t = malloc(k + 1);
    if (t) { memcpy(t, ob_buf + o0, k); t[k] = 0; viz_txt[key] = t; viz_depth[key] = pp_top; }
  }
}

/* Write the net at `r` -- as it is, sharing and all -- to `f`, through the one renderer.  The
   bookkeeping the walk needs (the sharing memo, the buffer) belongs to the RENDERER, not to the
   top-level readback, because `io_print` renders with it too. */
static void print_struct(FILE *f, Port r, int domain) {
  vis_cap = (size_t)(N->nn + 1);
  vis_print = calloc(vis_cap, 1);
  viz_txt = calloc(vis_cap * 3, sizeof *viz_txt);
  viz_depth = calloc(vis_cap * 3, sizeof *viz_depth);
  ob_len = 0; qmarks = 0; dmarks = 0;
  print_port(r, 0, domain);
  fwrite(ob_buf, 1, ob_len, f);
  fflush(f);
  if (viz_txt) { for (size_t i = 0; i < vis_cap * 3; i++) free(viz_txt[i]); free(viz_txt); viz_txt = NULL; }
  free(viz_depth); viz_depth = NULL;
  free(vis_print); vis_print = NULL; vis_cap = 0;
}

static int print_body(Net *n, int domain) {
  N = n;
  Port r = net_dup_hop(n, net_force_val(n, wire((Port){0, 0})));   /* the result is observed here */
  if (r.node >= 0 && r.node < n->nn && n->tag[r.node] == LAM) {
    /* Observing an `_ffi` closure IS its effect, so it is dispatched first whatever the type says. */
    if (render_val(OUT, run_ffi(n, r))) return 0;
    /* The type is the expectation when there is one; without it only what the structure determines
       is decoded.  Either way a value that does not hold is written as the net it is. */
    Val v = domain >= 0 ? decode(n, r, domain) : value_any(n, r);
    if (v.kind == 2) { fprintf(OUT, "\"%s\"", v.sv); fflush(OUT); return 0; }
    if (render_val(OUT, v)) return 0;
  }
  print_struct(OUT, r, domain);
  /* Neither mark is an answer, and both used to be emitted silently with exit status 0.  They mean
     different things, so they are reported differently -- on STDERR, so a test that compares stdout
     (test/expect.sh) is unaffected, and so the value on stdout stays exactly what it was.
       '_' -- the readback walked into a node the reduction had already discarded.  That is a
              malformed normal form, not sharing: a live wire points at a dead node, so the result
              is NOT a value.  Reported as an error because it is one.
       '?' -- the walk re-entered a node on its own stack, or met a binder no printed scope binds.
              The value is still correct (forcing it with `count` or applying it gives the exact
              answer -- see test/optimality.py), but the kernel/shared form cannot be written as a
              tree, and readback prints the sharing rather than unfolding it on purpose: unfolding is
              the blow-up optimal reduction avoids.  Two different shared values can print the same
              text, so a '?'-bearing result must not be treated as an answer by anything downstream.
              See print_port for the decision. */
  if (dmarks) {
    fprintf(stderr, "lin: readback reached a node the reduction had discarded (%ld mark(s)); "
                    "the result is not a value\n", dmarks);
    fflush(stderr);
  } else if (qmarks) {
    fprintf(stderr, "lin: note: readback of a shared normal form (%ld mark(s)); the value is "
                    "correct but the printed text is not unique -- force it with `count` or by "
                    "applying it\n", qmarks);
    fflush(stderr);
  }
  return 0;
}

/* ---- the driver's hooks ---------------------------------------------------------------- */

/* One value observed at `p`, as the DOMAIN the caller states: an `_ffi` closure is dispatched here,
   and the encoding readers answer everything else (a scalar is net structure, so decoding it is
   not a policy question).  A closure is dispatched at its PRINCIPAL port -- the port the header walk
   starts from -- because the port the value was reached by may be a bound-variable occurrence. */
static int rb_read_value(Net *n, void *st, Port p, int domain, Val *v) {
  (void)st;
  if (domain == DT_FFI || domain < 0) {
    /* A slot can still be an unreduced thunk: forcing it is what turns it into the closure whose
       value the caller is after, and this is readback -- the observer -- so demanding it is legal.
       A port names a POSITION as often as it names a term (a cell's head slot holds the port its
       term occupies), so the far end of the wire is tried too: one of the two IS the value. */
    Val r = run_ffi(n, net_force_val(n, p));
    if (!r.kind) {
      Port far = wire(net_force_val(n, p));
      if (far.node != p.node || far.port != p.port) r = run_ffi(n, far);
    }
    if (r.kind) { *v = r; return 1; }
  }
  Val d = domain >= 0 ? decode(n, p, domain) : value_any(n, p);
  if (!d.kind) return 0;
  *v = d;
  return 1;
}

/* Pinned for the whole walk: readback holds ports (its cursor, its recursion, its memo keys) across
   the forces it makes, and a reclaimed slot is REUSED, so a collection underneath it would silently
   re-point them. */
static int rb_print(Net *n, void *st, int domain) {
  (void)st;
  lin_pin(n);
  int rc = print_body(n, domain);
  lin_unpin(n);
  return rc;
}
static long rb_run_io(Net *n, void *st, long limit) {
  (void)st;
  lin_pin(n);
  long rc = run_io_body(n, limit);
  lin_unpin(n);
  return rc;
}

/* An EMPTY, NAMED section: an artifact therefore loads this driver by name at run time, which is what
   lets a `.line` file -- whose prelude forms are never re-evaluated -- still print.  Nothing is
   carried, so the container still learns a name and not a meaning. */
static int rb_carry_save(Net *n, void *st, void **blob, size_t *len) {
  (void)n; (void)st;
  *blob = NULL;
  *len = 0;
  return 1;
}

LinDriver lin_readback_driver;
static void __attribute__((constructor)) readback_load(void) {
  static int registered = 0;
  if (registered) return;
  registered = 1;
  lin_driver_add(&lin_readback_driver);
}

LinDriver lin_readback_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "readback", .description = "readback: value decode, printing and effect/FFI dispatch",
  .caps = LIN_CAP_PROVIDER, .priority = 0,
  .wants = LIN_WANT_READBACK,
  .read_value = rb_read_value, .print = rb_print, .run_io = rb_run_io,
  .carry_save = rb_carry_save,
};
