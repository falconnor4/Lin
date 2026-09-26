#include "../../src/lin.h"
#include "../runtime/pattern.h"     /* the structural recognisers and the op vocabulary (LIN_OP_*) */
#include <stdlib.h>
#include <string.h>
#include <stddef.h>
#include <math.h>

/* ---------------------------------------------------------------------- *
 *  Native scalar arithmetic & comparison semantics (generalized).
 *
 *  The SINGLE authority for pure integer/float arithmetic + comparison
 *  builtins (`lin_add`, `lin_sub`, `lin_mul`, `lin_div`, `lin_mod`,
 *  `lin_pow`, `lin_eq`..`lin_geq`, `lin_ffloor`, every `lin_f*` float op,
 *  `lin_lerp`, `lin_fclamp`).  Exposes one canonical entry point:
 *
 *      int lin_arith_scalar(fn, argc, vals, out, outkind)
 *
 *  so EVERY reduction strategy (base cpu fold in src/io.c, SIMD, GPU, or a
 *  future driver) resolves scalar arithmetic through this ONE table instead of
 *  re-implementing the ops per-driver.  The strategy keeps its own concern —
 *  how it extracts/decodes args from the net and when it folds — and calls
 *  this for the math itself.  New ops are new table rows, not new switch
 *  arms in each driver.
 *
 *  `vals` carries decoded scalars as C longs (int / bool / IEEE-754 double
 *  bits, symmetric with `Val`).  `outkind`: 1=int, 3=bool (out=0/1), 4=float
 *  (out = IEEE-754 bits).  Returns 1 if `fn` is one of our rows, else 0
 *  (declined, so the caller can fall back to core / dlsym).
 * ---------------------------------------------------------------------- */
/* THE TABLE'S OWN VOCABULARY, for the OWNERSHIP QUERY (`argc < 0`, src/lin.h): the one place the names
   the rows below answer to are stated as data, so a caller can ask "is this call yours?" WITHOUT
   operands -- a caller that had to read operands to find out would force a precompiled def's free
   variables (measured: test/sat_verify.lin, 295 ms -> 82 s).  The entries mirror the rows' own prefix
   tests exactly, and that is the point of the list: a name the table answers to but this list misses
   costs only a fold (the call is made at run time instead), while a name this list claims and the table
   does NOT answer to would let a build perform a call nobody supplies.  The two cast rows this driver
   performs itself (`lin_float`, `lin_parse_float`) and the reduction probes a build must not fold
   (`lin_folds`, `lin_folded`) are declared beside those rows, not here. */
static int arith_supplies(const char *fn) {
  static const char *const rows[] = {
    "lin_fadd", "lin_fsub", "lin_fmul", "lin_fdiv", "lin_fpow", "lin_fatan2", "lin_fmin", "lin_fmax",
    "lin_fsqrt", "lin_fsin", "lin_fcos", "lin_ftan", "lin_fabs", "lin_fsign", "lin_ffract",
    "lin_feq", "lin_flt", "lin_fleq", "lin_ffloor", "lin_lerp", "lin_fclamp",
    "lin_add", "lin_sub", "lin_mul", "lin_div", "lin_mod", "lin_pow",
    "lin_eq", "lin_lt", "lin_leq", "lin_gt", "lin_geq", NULL };
  for (int i = 0; fn && rows[i]; i++) if (!strncmp(fn, rows[i], strlen(rows[i]))) return 1;
  return 0;
}

int lin_arith_scalar(const char *fn, int argc, const long *a, long *out, int *outkind) {
  *outkind = 0;
  if (!fn) return 0;
  if (argc < 0) return arith_supplies(fn);        /* the ownership query: no operands, no computing */

  /* float binary ops: args are IEEE-754 bits carried as longs; result float */
  if      (fn[0]=='l' && fn[1]=='i' && fn[2]=='n' && !strncmp(fn, "lin_fadd", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x+y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsub", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x-y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmul", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x*y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fdiv", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=y!=0.0?x/y:0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fpow", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=pow(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fatan2", 10)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=atan2(x,y); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmin", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x<y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fmax", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); double r=x>y?x:y; memcpy(out,&r,8); *outkind=4; return 1; }
  /* float unary ops -> float */
  else if (!strncmp(fn, "lin_fsqrt", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?sqrt(x):0.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsin", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=sin(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fcos", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=cos(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ftan", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=tan(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fabs", 8)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=fabs(x); memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_fsign", 9)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x>=0.0?1.0:-1.0; memcpy(out,&r,8); *outkind=4; return 1; }
  else if (!strncmp(fn, "lin_ffract", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); double r=x-floor(x); memcpy(out,&r,8); *outkind=4; return 1; }
  /* float comparisons -> Church bool */
  else if (!strncmp(fn, "lin_feq", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x==y; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_flt", 7)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<y;  *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_fleq", 8)) { if (argc < 2) return 0; double x,y; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); *out=x<=y; *outkind=3; return 1; }
  /* float -> int / 3-arg float combinators */
  if (!strncmp(fn, "lin_ffloor", 10)) { if (argc < 1) return 0; double x; memcpy(&x,&a[0],8); *out=(long)floor(x); *outkind=1; return 1; }
  if (!strncmp(fn, "lin_fmin", 8) || !strncmp(fn, "lin_fmax", 8)) { /* handled above */ }
  if (!strncmp(fn, "lin_lerp", 8) && argc >= 3) { double x,y,t; memcpy(&x,&a[0],8); memcpy(&y,&a[1],8); memcpy(&t,&a[2],8); double r=x+(y-x)*t; memcpy(out,&r,8); *outkind=4; return 1; }
  if (!strncmp(fn, "lin_fclamp", 10) && argc >= 3) { double x,lo,hi; memcpy(&x,&a[0],8); memcpy(&lo,&a[1],8); memcpy(&hi,&a[2],8); double r=x<lo?lo:(x>hi?hi:x); memcpy(out,&r,8); *outkind=4; return 1; }

  /* integer arithmetic / comparisons */
  if (argc < 2) return 0;                       /* every int op needs 2 args */
  if      (!strncmp(fn, "lin_add", 7)) *out = a[0] + a[1];
  else if (!strncmp(fn, "lin_sub", 7)) *out = a[0] >= a[1] ? a[0] - a[1] : 0;
  else if (!strncmp(fn, "lin_mul", 7)) *out = a[0] * a[1];
  else if (!strncmp(fn, "lin_div", 7)) *out = a[1] ? a[0] / a[1] : 0;
  else if (!strncmp(fn, "lin_mod", 7)) *out = a[1] ? a[0] % a[1] : 0;
  else if (!strncmp(fn, "lin_pow", 7)) { long b=a[0], e=a[1], r=1; while (e>0) { if (e&1) r*=b; b*=b; e>>=1; } *out=r; }
  else if (!strncmp(fn, "lin_eq", 6)) { *out = a[0] == a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_lt", 6)) { *out = a[0] <  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_leq", 7)) { *out = a[0] <= a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_gt", 6)) { *out = a[0] >  a[1]; *outkind=3; return 1; }
  else if (!strncmp(fn, "lin_geq", 7)) { *out = a[0] >= a[1]; *outkind=3; return 1; }
  else return 0;
  *outkind = 1;
  return 1;
}

/* ====================================================================== *
 *  Fold pre-emptor (`LIN_CAP_PREEMPT`, priority 5 — ahead of simd's 10).
 *
 *  The `_ffi`/`_op` native fold used to live in the core's `net_interact`.
 *  The core now keeps only the four correctness rules (β, δ⋈δ, γ⋈δ, ε); the
 *  fold, its saturation guard, and every fold-shaped rewrite moved here.
 *  This driver is a *pre-pass*: it claims a redex class the core would
 *  otherwise β on the active wave, and the core stays complete without it
 *  (a pure-Lin `_op` closure's LAM body IS the semantics; an unfolded `_ffi`
 *  closure is resolved by readback exactly as before).
 *
 *  Two rules the port must keep straight:
 *
 *   - `claim` never strands.  A driver that claims a pair the core never β's
 *     has stranding on its hands, so `reduce` disposes of EVERY pair it was
 *     handed: fold it, force its operands and fold it, or give it back to the
 *     core's β (always correct, just slower).
 *   - THE OPERANDS ARE THUNKS, and the fold is what needs them, so the forcing
 *     belongs here and goes through `net_force` (ABI 3 has no `drain`/`pending`/
 *     `arg_fold`; a driver that wants a concrete operand says so).  Needed order
 *     gives the reducer no reason to have evaluated `(mul 150 150)` in
 *     `(div (mul 150 150) 100)` before the `div` redex is reached; the fold asks
 *     for it.  The shared argument decoder already forces each slot it reads
 *     (src/io.c), and `force_spine` below makes the same demand explicit for a
 *     slot the decoder could not read at all.
 * ====================================================================== */

/* Tri-state result of trying to compute a saturated closure's value. */
enum { EV_NO = 0, EV_READY = 1, EV_WAIT = 2 };

/* read a port's wire (a function, not a macro: `wire_at(n, a, b)` would
   split into three macro arguments at the comma inside the braces) */
static inline Port wire_at(const Net *n, int node, int port) { return n->wire[node * 3 + port]; }
#define IN_NET(n, i) ((i) >= 0 && (i) < (n)->nn)

/* Which head is a redex's LAM?  An `_ffi` closure's body is the `_ret` binder that applies the head
   to itself (the header SHAPE, std/runtime/pattern.h); an `_op` head's body is its pure fallback
   BODY.  A net with no labels says exactly this much and no more -- `ctor_tag(nmof(n, lam))` is what
   this used to read, and a carrier name is the one thing a raw net cannot offer.  PURE: the matcher
   never forces and never allocates, which is what `claim` requires. */
static int head_is_ffi(const Net *n, int lam) {
  LinMatch m;
  return lin_pat_match((Net *)n, (Port){lam, 0}, lin_pat_enc_ffi, LIN_PAT_BUDGET_FOR(n), &m);
}

/* The OPERATOR and its OPERANDS, read in ONE step.  Both live in the same cell -- the operator's
   INDEX is its head (std/num.lin writes it; LIN_OP_* in pattern.h is the enumeration) and the
   operands are its tail -- and reading that cell twice is NOT the same as reading it once: the first
   read FORCES the list into being (it is a compiled application until something walks it) and a force
   re-aims the port it fired on, so the second read can land on a different cell.  Measured: an `add`
   whose operand list was read twice folded with the OPERATOR INDEX as its first operand (0+1 for
   6+1).  FORCING, so this is `reduce`'s question, never `claim`'s. */
static int op_head_of(Net *n, int app, const char **fn, Port *ops) {
  Port head, tail;
  *fn = NULL;
  *ops = (Port){-1, 0};
  if (!IN_NET(n, app) || n->dead[app] || n->tag[app] != APP) return 0;
  if (!net_read_cell(n, wire_at(n, app, 2), &head, &tail)) return 0;
  long code = net_read_int(n, head, LIN_ENC_NUM);
  *fn = lin_op_fn((int)code);
  *ops = tail;
  return *fn != NULL;
}

/* IS THIS REDEX'S RESULT SHARED?  β joins the closure's body port to the APP's result port, so a live
   fan on EITHER of those two ports says the body graph is shared -- and when the sharing came from
   copying a closure (`(let ((f (\x BODY))) ...)`, the fan being the copy of f's body) that graph is
   OPEN: its own argument fans are wired to the copies' binders, so each copy binds them to its OWN
   operand and the copies do NOT compute the same value.
   The fold computes the value ONCE, with whichever operand happened to be forced first, and writes it
   into that shared port, so the fan hands that single value to BOTH copies.  Measured on
   `(let ((f (\x (add x 5)))) (add (f 1) (f 2)))`: the first use's redex folds to 6 and the fan gives
   the second use 6 as well -- 12 where 13 is right.  Handing the redex back to the core's β instead
   gives 13 (and so does the whole suite with this pre-emptor disabled), which is what pins the FOLD,
   and not the net, as the defect.
   Declining costs one wave and no more: β lets the fan resolve, each copy becomes a fresh `_op` redex
   whose result port is no longer shared, and the fold takes those.  PURE -- `claim` may call it. */
static int result_shared(const Net *n, int lam, int app) {
  const Port p[2] = { wire_at(n, lam, 2), wire_at(n, app, 1) };   /* the two ports β joins */
  for (int i = 0; i < 2; i++) {
    int f = p[i].node;
    if (!IN_NET(n, f) || n->dead[f] || n->tag[f] != DUP) continue;
    for (int a = 1; a <= 2; a++) {
      Port w = wire_at(n, f, a);
      if (!IN_NET(n, w.node) || n->dead[w.node]) continue;
      if (n->tag[w.node] == DUP) return 1;                    /* the copy fans on to another copy */
      if (n->tag[w.node] == LAM && w.port == 2) return 1;     /* the fan feeds another copy's BODY */
    }
  }
  return 0;
}

/* every scalar operand of an `_op`/`_ffi` is a NUMBER: the language's arithmetic takes numbers, and
   a slot in another domain is not this fold's */
static const int DOMS_NUM[1] = { DT_NUM };

/* Consume a node this redex *exclusively* owns.  `lam`/`app` are
   principal-connected to each other, so nothing else can be attached to them,
   but the β-body and the operand spine may be SHARED: a live DUP on that port
   means a sibling redex reaches the same sub-net through the fan, and marking
   the fan (or a node behind it) dead would strand the sibling — the fold would
   then read a destroyed operand and one consumer's result would leak into
   another's.  Shared structure is left for the reachability GC instead. */
/* Dispose of a node the fold owns outright: kill it AND cut every wire that led to it.
   Cutting is the part that was missing.  Marking a node dead leaves the wires that pointed at it in
   place, so a live node is left pointing into a node that no longer exists -- measured, that was the
   WHOLE of the remaining dangling-wire count (0 with this driver absent, 889 wires on test/map.lin
   and 581 on sudoku with it), and it is what made moving reclamation unsound: compaction turns such
   a wire into NONE, losing the connection, and renumbering can revive the freed index as a different
   node.  Cut the subgraph loose instead and it is simply unreachable, and so reclaimable.
   A fan on the port means the sub-net is SHARED -- a sibling reaches it too -- so it is not ours to
   kill; the core's reachability reclaims it once the last user is gone. */
static void fold_kill(Net *n, int v) {
  if (v < 0 || v >= n->nn || n->dead[v]) return;
  if (n->tag[v] == DUP) return;
  /* SEVER, do not reap.  Reaping frees the node outright and clears its ports, which is only sound
     for a node the caller owns EXCLUSIVELY -- and this driver cannot prove that: a closure reached
     through a fan is still tagged LAM, so the tag test above does not see the sharing, and an
     unconditional free took the other user's structure with it (measured: every FFI suite broke,
     with the closures coming back unreduced because the copy `run_ffi` needs had been freed under it).
     Severing is the conservative form and it reclaims the same way: each cut frees whatever reaches
     zero live connections, and a shared node still has its other user, so it survives. */
  for (int p = 0; p < 3; p++) net_sever(n, (Port){v, p});
  n->dead[v] = 1;
}

/* alloc a concrete value node (int -> Scott numeral, bool -> Church bool, float -> `_fsz` box) */
static Port val_to_port(Net *n, const Val *v) {
  if (v->kind == 3) return net_alloc_bool(n, (int)v->iv);
  if (v->kind == 4) { double d; memcpy(&d, &v->iv, 8); return net_alloc_float(n, d); }
  return net_alloc_scott(n, v->iv);
}

/* dig the `_ffi` closure header at LAM `lam` (shape \_ffi. \_ret. ((_ffi <fn>) <args>))
   into `*fnp` (the fn APP) and `*argp` (the `_cl` arg spine) — same walk the core's
   shared decoder does (net_ffi_fn/net_ffi_args), repeated here so the arg spine port
   is reachable for the saturation guard. */
/* Through a fan, exactly as the core's decoder does: a SHARED closure is reached through a DUP, so
   its body wire leads to the fan's auxiliary and the principal is the body.  Reading it plainly is
   what made a runtime `_ffi` value used twice unfold instead of fold. */
static Port hop(const Net *n, Port p) {
  for (int i = 0; i < n->nn && IN_NET(n, p.node) && !n->dead[p.node] && n->tag[p.node] == DUP; i++)
    p = p.port == 0 ? wire_at(n, p.node, 1) : wire_at(n, p.node, 0);
  return p;
}

static int ffi_header(Net *n, int lam, Port *fnp, Port *argp) {
  if (!IN_NET(n, lam) || n->dead[lam] || n->tag[lam] != LAM) return 0;
  Port r = hop(n, wire_at(n, lam, 2));
  if (!IN_NET(n, r.node) || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = hop(n, wire_at(n, r.node, 2));
  if (!IN_NET(n, a2.node) || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  if (fnp) *fnp = wire_at(n, a2.node, 0);
  if (argp) *argp = wire_at(n, a2.node, 2);
  return 1;
}


/* Compute the concrete value of a saturated pure-Lin `_op` redex (DT_OP LAM `lam`
   applied to its redex APP `app`, whose port 2 carries the raw operand `_cl`-spine).
   EV_NO  : not a foldable op (no scalar provider claims it) -> let the core β the
            pure-Lin fallback body.
   EV_WAIT: our op, but an operand is not concrete yet -> also plain β. */
static int op_eval(Net *n, int lam, int app, Val *v) {
  const char *fn;
  Port argp;
  if (result_shared(n, lam, app)) return EV_NO;      /* a shared result is the core's β to take */
  if (!op_head_of(n, app, &fn, &argp)) return EV_NO;
  int slots = net_spine_slots(n, argp);
  Val fargs[8]; memset(fargs, 0, sizeof fargs);
  int argc = net_spine_args(n, argp, DOMS_NUM, 1, fargs, 8);
  if (slots < 1 || slots > 8 || argc < slots) return EV_WAIT;   /* operand spine not readably concrete */
  long c[8] = {0};
  for (int i = 0; i < slots; i++) {
    if (fargs[i].kind != 1 && fargs[i].kind != 3 && fargs[i].kind != 4) return EV_WAIT;
    c[i] = fargs[i].iv;
  }
  long out = 0; int okind = 0;
  /* Through the registry, like every other call this driver resolves: an `_op` head's operator comes
     from the fixed pure-Lin vocabulary (LIN_OP_*), and the provider that supplies it states its purity
     where it registers. */
  if (!lin_scalar_ops_run(fn, slots, c, &out, &okind)) return EV_NO;  /* declined: pure-Lin β computes it */
  v->kind = okind == 4 ? 4 : (okind == 3 ? 3 : 1);
  v->iv = out;
  return EV_READY;
}

/* THIS DRIVER'S OWN `_ffi` ROWS, and which of them it DECLARES pure.  That declaration is what makes
   the build rule a CAPABILITY and not a naming convention: the rule used to be the `lin_` PREFIX, which
   trusted an effectful `lin_*` symbol and refused a pure callable that was not spelled `lin_`.
     - the two casts are functions of their operands, so a build may fold them;
     - `lin_streq` is pure too but needs C strings this fold does not build: declared pure, DECLINED
       below, and readback performs it (at build time as at run time);
     - the two fold counters OBSERVE the REDUCTION: folding them in a build would freeze the build's own
       fold count into the artifact, so they are supplied here but NOT declared pure, and the gate
       stops a build at them while readback answers them at run time.
   Every other symbol is one this driver does not supply -- undeclared, hence an observation. */
static int ffi_row(const char *fn) {
  return !strcmp(fn, "lin_float") || !strcmp(fn, "lin_parse_float") || !strcmp(fn, "lin_streq") ||
         !strcmp(fn, "lin_folds") || !strcmp(fn, "lin_folded");
}
static int ffi_row_pure(const char *fn) {
  return ffi_row(fn) && strcmp(fn, "lin_folds") && strcmp(fn, "lin_folded");
}

/* Compute the concrete value of a saturated `_ffi` closure `lam`.  Whether a call may be folded is the
   PROVIDER's declaration (registered with `lin_scalar_ops_add`, consulted through the registry) plus
   this driver's own rows' declaration above, never a naming convention.  Side-effecting FFI (`puts`,
   `dlopen`, `getenv`, ...) and an undeclared foreign symbol reach the gate and decline there.
   Saturation guard: EVERY operand on the `_cl` spine must be concretely
   readable — checking only the first let later non-concrete operands fold as
   garbage; a nested `_ffi`/`_op` operand must itself be fully concrete (the
   shared dec_arg does that, and a slot it cannot decode is counted skipped). */
static int ffi_eval(Net *n, int lam, Val *v, char *fnout, int fnmax) {
  Port a1, argp;
  if (!ffi_header(n, lam, &a1, &argp)) return EV_WAIT;         /* closure header not formed yet */
  if (!IN_NET(n, a1.node) || a1.port != 1 || n->tag[a1.node] != APP) return EV_WAIT;
  char fn[256];
  if (net_read_string(n, wire_at(n, a1.node, 2), LIN_ENC_NUM, fn, sizeof fn) < 0) return EV_WAIT;
  /* TWO QUESTIONS, BOTH ANSWERED BEFORE ANY OPERAND IS READ -- because reading a spine is what FORCES
     it, and a call that is not this fold's must not have its operands forced to find that out (measured:
     decoding every closure's spine to classify it took test/sat_verify.lin from 295 ms to 82 s).
       1. IS IT THIS FOLD'S CALL?  `ffi_row` is this driver's own rows; everything else has to be
          supplied by a provider that DECLARED its calls pure, and the registry is asked as a QUESTION
          (the ownership query, `argc < 0`) rather than by making the call.
       2. MAY A BUILD MAKE IT NOW?  The core's one gate: it stops a build at the calls nobody declared
          pure, so a reduction that would bake the program's own observation does not happen. */
  long q = 0; int qk = 0;
  if (!ffi_row(fn) && !lin_scalar_ops_run(fn, -1, NULL, &q, &qk)) return EV_NO;
  if (!lin_build_gate(fn, ffi_row_pure(fn))) return EV_NO;
  if (fnout && fnmax > 0) snprintf(fnout, (size_t)fnmax, "%s", fn);

  Val vals[8]; memset(vals, 0, sizeof vals);
  /* The operands of a foldable builtin are numbers: the string-typed rows are declined below, and a
     closure operand is dispatched by the reader itself. */
  /* THE SPINE THIS WALK ALREADY HAS, not a second header dig for it: `ffi_header` above just produced
     `argp`, and asking `net_ffi_args` re-walks the closure through the core's (stricter) header test,
     so the two can disagree about a SHARED closure and the arg list silently comes back empty --
     measured on `(let ((x (float "2.5"))) (fadd x x))`, where the arity guard then read 2 slots and 0
     decoded operands and the fold declined for ever.  One dig, one spine. */
  int na = net_spine_args(n, argp, DOMS_NUM, 1, vals, 8);
  int slots = net_spine_slots(n, argp);
  if (slots < 0) { if (na != 0) return EV_WAIT; slots = 0; }   /* not a cons spine: only the empty arg list is concrete */
  else if (slots > 8) return EV_WAIT;
  if (na < slots) return EV_WAIT;                              /* a present operand is not concrete yet */

  long c[8] = {0};
  for (int i = 0; i < slots; i++) {
    int k = vals[i].kind;
    if (k == 2) c[i] = (long)(intptr_t)vals[i].sv;             /* string operand: hand the C string through, as run_ffi does */
    else if (k == 1 || k == 3 || k == 4) c[i] = vals[i].iv;
    else return EV_WAIT;
  }
  long out = 0; int okind = 0;
  if (lin_scalar_ops_run(fn, slots, c, &out, &okind)) {        /* a provider DECLARED this call pure */
    v->kind = okind == 4 ? 4 : (okind == 3 ? 3 : 1);
    v->iv = out;
    return EV_READY;
  }
  /* Core readback builtins that are not scalar-table rows but ARE pure closures
      the evicted in-core fold used to materialise (run_ffi's builtin rows).
      Keeping them here preserves behaviour for `(folded)` / `(i2f n)` / `(float s)`, all of which
      passed the gate above; the two reduction probes below did NOT pass it under a build marker and
      never reach here there -- they stay for readback to answer at RUN time. */
  if (!strcmp(fn, "lin_folds"))  { v->kind = 1; v->iv = lin_fold_total(); return EV_READY; }
  if (!strcmp(fn, "lin_folded")) { v->kind = 3; v->iv = lin_fold_total() > 0; return EV_READY; }
  if (!strcmp(fn, "lin_float") && slots >= 1) {
    double d = (double)c[0]; long rb; memcpy(&rb, &d, 8); v->kind = 4; v->iv = rb; return EV_READY;
  }
  if (!strcmp(fn, "lin_parse_float")) {
    if (slots < 1 || vals[0].kind != 2) return EV_NO;
    double d = strtod(vals[0].sv, NULL); long rb; memcpy(&rb, &d, 8); v->kind = 4; v->iv = rb; return EV_READY;
  }
  return EV_NO;
}

/* ---- the fold rewrites (ports of the evicted lin_fold_op / lin_fold_ffi) ---- */

/* `_op` fold rewiring: `ar = wire(app,1)` is the APP's body-slot partner where β
   threads the result out; inject the value AT `ar` (linking into {app,1} would
   REPLACE `ar` and strand the consumer).  Fall back to {app,1} if `ar` was already
   consumed.  Kills `lam` and `app`. */
static void fold_op_head(Net *n, int lam, int app, const Val *v) {
  Port res = val_to_port(n, v);
  Port ar = wire_at(n, app, 1);
  /* ORDER MATTERS: the value takes the redex's place BEFORE anything is severed.  Severing `app`'s
     result port removes `ar`'s connection, and with the cascade in net_sever a node that loses its
     last live connection is reclaimed -- so linking afterwards would hand the value to a consumer
     that had just been freed as garbage (measured: every FFI suite, whose closures came back
     unreduced).  Connected first, `ar` is live and the sever leaves it alone. */
  if (ar.node >= 0 && ar.node < n->nn && !n->dead[ar.node])
    net_link(n, res, ar, 1);
  else
    net_link(n, res, (Port){app, 1}, 1);
  fold_kill(n, lam); fold_kill(n, app);
  /* The β-body and the operand spine are NOT ours to sever: `(\x BODY)` copied by a fan still reads as
     a plain LAM, so a redex whose spine sits behind (or in front of) a copy of the SAME operand list
     sees two redexes reaching one structure, and cutting it here destroyed the sibling's operands --
     measured, that is the whole of `(let ((f (\x (add x 1)))) (add (f 1) (f 2)))` folding its second
     application with the first one's value (4 for 5).  Cutting `app`'s operand port already detaches
     the spine from the redex, and the reachability GC reclaims what nobody else reaches: the
     conservative form, and the one this driver's own header documents. */
  lin_fold_bump();
}

/* `_ffi` fold rewiring: link the concrete value to {app, 0} and kill the closure LAM
   (same as the evicted fold_link). */
static void fold_ffi_head(Net *n, int lam, int app, const Val *v) {
  Port res = val_to_port(n, v);
  net_link(n, res, (Port){app, 0}, 1);              /* the value takes the closure's place */
  fold_kill(n, lam);                                /* and the closure, body included, is cut loose */
  lin_fold_bump();
}

/* Force every operand slot of a `_cl` arg spine.  Needed order leaves an operand as a thunk
   until something needs it, and this fold is that something: `(div (mul 150 150) 100)` reaches
   the `div` redex with its first operand still an unreduced `_op` closure.  Reads through the
   shared decoder, so the slot walk is the same one the fold itself uses. */
static void force_spine(Net *n, Port argp) {
  int slots = net_spine_slots(n, argp);
  for (int i = 0; i < slots && i < 8; i++) {
    Port cur = net_dhop(n, net_force_val(n, argp));
    for (int k = 0; k <= i; k++) {
      Port head, next;
      if (!net_read_cell(n, cur, &head, &next)) break;
      if (k == i) { net_force(n, head); break; }
      cur = next;
    }
  }
}

/* ---- LinDriver hooks ---- */

/* claim: an `_op` head or an `_ffi` closure redex, recognized BY SHAPE.  The core hands wave pairs in
   tag order, so normalise LAM-first here.  `reduce` disposes of everything claimed (fold it, or hand
   it back to the core's β), so claiming is always safe -- which is what lets this claim on the head's
   shape alone and leave "is this an op the table has a row for" to `reduce`, where forcing the
   operand list is legal. */
static int arith_claim(const Net *ncn, Port p1, Port p2) {
  Net *n = (Net *)ncn;
  if (p1.port || p2.port) return 0;
  if (!IN_NET(n, p1.node) || !IN_NET(n, p2.node)) return 0;
  if (n->dead[p1.node] || n->dead[p2.node]) return 0;
  if (net_wire(n, p1).node != p2.node || net_wire(n, p1).port != p2.port) return 0;
  if (net_wire(n, p2).node != p1.node || net_wire(n, p2).port != p1.port) return 0;
  int lam;
  if (n->tag[p1.node] == LAM && n->tag[p2.node] == APP) lam = p1.node;
  else if (n->tag[p2.node] == LAM && n->tag[p1.node] == APP) lam = p2.node;
  else return 0;
  if (head_is_ffi(n, lam)) return 1;
  return lin_pat_op_head(n, (Port){lam, 0}, NULL);
}

/* reduce: fold each claimed redex.  The ABI hands a slice of PAIRS: `nred` counts pairs,
   `redexes` holds 2*nred ports.  Every claimed pair is consumed one way or another: forced
   and folded, or handed back to the core's β, which is always correct (just slower) -- a
   claimed-but-unhandled pair would be dropped from the wave and stranded. */
static int arith_reduce(Net *n, Port *redexes, int nred, long limit, int *changed) {
  int done = 0;
  for (int i = 0; i < nred; i++) {
    if (limit > 0 && (long)n->steps >= limit) break;
    Port pa = redexes[2 * i], pb = redexes[2 * i + 1];
    if (pa.port || pb.port) continue;
    if (!IN_NET(n, pa.node) || !IN_NET(n, pb.node)) continue;
    if (n->dead[pa.node] || n->dead[pb.node]) continue;
    int lam, app;
    if (n->tag[pa.node] == LAM && n->tag[pb.node] == APP) { lam = pa.node; app = pb.node; }
    else if (n->tag[pb.node] == LAM && n->tag[pa.node] == APP) { lam = pb.node; app = pa.node; }
    else continue;
    if (net_wire(n, (Port){lam, 0}).node != app || net_wire(n, (Port){app, 0}).node != lam) continue;
    int ffi = head_is_ffi(n, lam);
    Val v; int ev = EV_NO;
    /* FORCE FIRST, READ AFTER.  Reading a compiled operand list means walking structure that is still
       a chain of applications, and every read forces the slot it reads -- which rebuilds the very
       cells the walk is standing on.  One up-front pass (force_spine forces the list, its cells and
       each slot, and never the slots' own structure) leaves a net that does not move under the walk.
       Not while a def is being precompiled: its operands are FREE variables, and forcing those is
       what walks a knot that never becomes a value. */
    if (!ffi && lin_precompile_depth == 0 && lin_pat_op_head(n, (Port){lam, 0}, NULL)) {
      Port list = wire_at(n, app, 2);
      if (IN_NET(n, list.node)) force_spine(n, list);
    }
    if (!ffi && lin_pat_op_head(n, (Port){lam, 0}, NULL)) ev = op_eval(n, lam, app, &v);
    else if (ffi) ev = ffi_eval(n, lam, &v, NULL, 0);
    /* A NOT-READY FOLD IS LEFT ALONE WHILE A BUILD MARKER IS UP, which is what a build KEEPS: β-ing it
       would replace the `_op`/`_ffi` head with the pure-Lin body, and the artifact would have lost the
       redex the fold exists for.  A precompiled def's operands are FREE variables, so a foldable redex
       can never be ready there; and at AOT build time an OBSERVATION leaves exactly this state -- the
       gate refused the call the operand needs, so the operand is not concrete -- and the redex must
       SURVIVE into the artifact for the fold to take it there, after the observation the artifact's own
       environment makes.  Measured without the build marker here: test/runtime_ffi.lin's `(add rt 1)`
       shipped with its redex β'd away and the artifact printed `(\a (\b (\c b)))` for every N instead
       of the answer.  The core's `act` list is a wave snapshot, so an unhandled pair is simply not
       re-enqueued into this reduction; the shipped net carries the closure. */
    if (ev != EV_READY && (lin_precompile_depth > 0 || lin_build_depth > 0)) continue;
    if (ev == EV_WAIT) {
      /* The operands are not concrete yet.  Under needed order that is the normal state -- nothing
         had a reason to reduce them -- so ask for them and try again. */
      Port argp = ffi ? (Port){-1, 0} : wire_at(n, app, 2);
      if (ffi) ffi_header(n, lam, 0, &argp);
      if (IN_NET(n, argp.node)) force_spine(n, argp);
      ev = ffi ? ffi_eval(n, lam, &v, NULL, 0) : op_eval(n, lam, app, &v);
    }
    if (ev == EV_READY) {
      if (!ffi) fold_op_head(n, lam, app, &v); else fold_ffi_head(n, lam, app, &v);
      done++; (*changed)++; n->steps++;
      continue;
    }
    /* Not foldable (an open precompile body, or an operand that is not a value even after
       forcing): hand the redex to the core's own β rather than strand it. */
    if (net_interact(n, (Port){lam, 0}, (Port){app, 0})) { (*changed)++; n->steps++; }
  }
  return done;
}

/* ====================================================================== *
 *  THE AOT PASS: this driver's build-time decision about its own domain
 * ====================================================================== *
 *  The compiler OFFERS the pass point (LinDriver.aot, src/main.c); this driver owns
 *  what its pass does.  What it receives is the whole program with full information
 *  and no step limit: the expanded term, the TYPES the compiler inferred for it, the
 *  net it compiled to, and a term -> port map that lives only for the call.  What it
 *  may emit is a rewrite -- of the term or of the net -- or its own opaque carry
 *  section.  Nothing else, and nothing that outlives the build.
 *
 *  WHY THIS PASS, AND WHY IT IS AN ENCODING CHOICE
 *  ----------------------------------------------
 *  Measured on the corpus before it existed (Stage 1): `lin build` already bakes every
 *  closed numeric cone -- all 30 suites come out of the build with runtime=1 reduce
 *  step and 0 runtime folds -- so a pass whose payoff is FOLDING has nothing left to
 *  buy, and the region hand-out machinery has no consumer at all.  What the AOT path
 *  really loses is MEANING: a container carries no type, so an artifact is read with
 *  no domain to state, and this driver's two domains are exactly the ones whose
 *  encodings are shared with other domains:
 *
 *      `\b0.\b1.b0`   is the numeral ZERO, Church TRUE and the empty list at once
 *      `\b0.\b1.b1`   is Church FALSE and the nil cell
 *
 *  so readback may decode only what the STRUCTURE determines, and 14 of the 30 suites
 *  printed a lambda structure from the artifact where the interpreter printed the
 *  value (`test/nqueens.lin`: `true` comes back `(\a (\b a))`).  The fix is the one
 *  the brief names: this driver chooses an UNAMBIGUOUS ENCODING for the values its
 *  domain OBSERVES -- the LIN_ENC_BOX precedent, one binder further out
 *  (std/runtime/pattern.h, LIN_BOX_NUM / LIN_BOX_BOOL) -- at AOT time, where the
 *  compiler's inferred type is still available to say which domain is meant.
 *
 *  The box IS the derivation: it is net structure, so readback recognises it with no
 *  expectation and no table, and there is nothing keyed by node index for a recycled
 *  slot to make stale.  A pass that cannot decide (no scheme, a result that is not
 *  this driver's domain, a root the compiler does not confirm) declines and leaves the
 *  program exactly as it was -- which is why the whole thing is optional and the
 *  interpreter path never runs it. */
static int arith_aot(Net *n, void *st, const Term *t, const Scheme *sch,
                     Port (*node_of)(void *ctx, const Term *), void *ctx) {
  (void)st;
  Type *ty = sch ? sch->t : NULL;
  while (ty && ty->kind == TLINK) ty = ty->a;
  int dom = -1;
  if (ty && ty->kind == TNOM && ty->name) {
    if (!strcmp(ty->name, "num")) dom = LIN_BOX_NUM;
    else if (!strcmp(ty->name, "bool")) dom = LIN_BOX_BOOL;
  }
  if (dom < 0) return 0;
  /* THE CORRESPONDENCE IS CHECKED, NOT TRUSTED.  A pass rewrites the net the compiler built, so the
     only port it may touch is the one the compiler says it built -- and it has to be the port ROOT is
     wired to, or this is not the observed result and the pass has nothing to say about it. */
  Port v = node_of(ctx, t);
  Port root = net_wire(n, (Port){0, 0});
  if (!IN_NET(n, v.node) || root.node != v.node || root.port != v.port) return 0;
  /* SPECIALISE THE CONE AT BUILD TIME, and do it BEFORE the encoding is chosen.  A box at ROOT stops
     the build's own root-forcing at a LAM -- needed order's walk follows ROOT's wire and no further --
     so wrapping the value without this bakes an UNREDUCED thunk and moves the program's real work
     into readback: measured on test/nqueens.lin, 7933 steps forced at PRINT time (27 ms against
     0.3 ms) while the build's own metric reported "1 reduce step" and could not see it.  So the value
     is evaluated HERE, while ROOT still names it: the same needed-order wave and the same root force
     the build runs afterwards, on the port the box is about to move out of its way.  AOT is one very
     large wave with full information and no step limit, and this is that wave; it runs under the build
     marker, so nothing the program would observe at run time can be baked by it. */
  net_reduce(n, n->steps + (1L << 22));
  net_force(n, (Port){0, 0});
  /* AND CHOOSE THE ENCODING -- BUT ONLY FOR A VALUE THE BUILD ACTUALLY HAS.  A box STATES its payload's
     domain, so there is nothing to state unless the payload IS a value of that domain, and a build that
     had to DECLINE an observation is holding a STUCK cone: boxing that makes readback print the payload
     as structure for ever.  Measured with the build keeping its partial evaluation (src/main.c's aot_run
     no longer discards it): test/runtime_ffi.lin -- whose whole point is that N exists only at RUN time
     -- came out of this pass as `(\a (\b (\c b)))` for EVERY N instead of the answer.  The test is the
     domain's own encoding read, the FORCING one: it completes the layers of a value that is there (the
     same wave the pass already runs) and declines on a cone that is not.  Nothing here is observation-
     free by assumption -- the read runs under the build marker, so the gate refuses what it may not do. */
  int enc = dom == LIN_BOX_NUM ? LIN_ENC_NUM : LIN_ENC_BOOL;
  if (0 && net_read_int(n, net_wire(n, (Port){0, 0}), enc) < 0) return 0;
  /* `lin_pat_box_build` relinks the value into the box, so ROOT's own wire is the only thing left
     pointing at the old place, and the box takes it (re-read: the read above forces, and a force
     re-aims the port it fired on). */
  net_link(n, (Port){0, 0}, lin_pat_box_build(n, net_wire(n, (Port){0, 0}), dom), 0);
  return 1;
}

/* ---- registration ----
   Two roles in one plugin:
     - lin_arith_scalar is the shared SEMANTIC authority every strategy calls;
     - lin_arith_driver is the fold PRE-EMPTOR (LIN_CAP_PREEMPT, priority 5, ahead of
       simd's 10) that claims folded redexes before any strategy sees them.  A pre-emptor
       composes with whichever strategy is selected: lin_driver_clear (what `(set_driver
       ...)` calls) drops strategies but keeps pre-emptors.
   std/std.lin loads std/drivers/arith.lin, which is what dlopens this .so; the core itself
   starts with no driver at all. */
LinDriver lin_arith_driver;                                /* defined below; registered by the constructor */
static void __attribute__((constructor)) arith_load(void) {
  /* The table DECLARES ITS PURITY here, once, for every row: each is arithmetic on its operands, so a
     build may fold one and bake the value (src/io.c's gate is what turns that declaration into the
     rule).  A provider that cannot say this of its calls registers with 0 and a build stops at it. */
  lin_scalar_ops_add(lin_arith_scalar, 1);
  static int registered = 0;
  if (registered) return;                               /* constructors can run once per load, never twice */
  registered = 1;
  lin_driver_add(&lin_arith_driver);
}

LinDriver lin_arith_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),   /* the ABI-5 extension contract: the core reads only these fields */
  .name = "arith", .description = "native scalar arithmetic table + `_op`/`_ffi` fold pre-emptor",
  .caps = LIN_CAP_NATIVE_NUM | LIN_CAP_PREEMPT, .priority = 5,   /* before simd(10): claim folds first */
  .claim = arith_claim, .reduce = arith_reduce,
  .wants = LIN_WANT_AOT, .aot = arith_aot,   /* the driver's own build-time pass, offered by the core */
};
