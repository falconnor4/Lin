#ifndef LIN_H
#define LIN_H
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>

#define NAME 256

/* ---------------- core terms (pure untyped lambda) ---------------- */
enum { TVAR, TLAM, TAPP, TDEF, TDEFX, TLOAD, TNS, TOPEN, TDATATYPE, TFLOAT, TEXPORT };
typedef struct Type { int kind, id; struct Type *a, *b; const char *name; } Type;
/* type-kinds (shared: type.c and the datatype processor in main.c use these) */
enum { TVR, TARROW, TLINK, TNOM, TARG, TPARAM };
typedef struct Term {
  int type;
  char name[NAME];
  struct Term *l, *r;
  Type *annot;
} Term;

/* ---------------- interaction net ---------------- */
enum { LAM, APP, DUP, ERA, ROOT };

typedef struct { int node:30; unsigned int port:2; } Port;
typedef union { uint64_t raw; struct { uint64_t is_heap:1, len:6, bits:57; } sso; struct { uint64_t is_heap:1, len:31, off:32; } heap; } Scope;

typedef struct {
  int cap, nn; unsigned char *tag; Port *wire; Scope *scope; char **name;
  Port *act; int atop, actcap; unsigned char *dead; uint64_t *sca; int sccap, scn;
  long steps;
  /* A driver claims a redex it cannot materialise yet (operands not concrete, or an open precompile body) and
     reports it here.  The core never interprets the reason — it only uses it to know the net is not a value, so
     def_precompile must not bake it.  The policy is entirely the driver's. */
  unsigned char driver_pending;
} Net;

/* wire of a port (drivers read the graph directly) */
static inline Port net_wire(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }

Port net_alloc(Net *n, int tag, Scope sc, const char *name);
void net_link(Net *n, Port a, Port b, int enqueue);
void net_init(Net *n, int cap); void net_free(Net *n); int net_interact(Net *n, Port a, Port b);
long net_reduce(Net *n, long limit);
Net *net_copy(const Net *n); Scope scope_nil(void);
/* reclaim every node not reachable from ROOT (identity-preserving; safe at any point a
   net is a value or a residual -- the AOT build compacts before serialising) */
void net_gc(Net *n);
/* drop gauge-table entries no live node references (call before serialising: the container
   stores the whole table, and an AOT evaluation leaves far more gauges than live nodes) */
void net_trim_scopes(Net *n);
int scope_eq(Net *n, Scope a, Scope b);
Scope scope_prefix(Net *n, Scope lvl, Scope s);
Scope scope_from_bits(Net *n, const uint64_t *bits, int len);

/* ---------------- driver ABI ---------------- */
/* Drivers reduce a redex *class*; core waves fan out to each in priority order, each claiming the redexes it handles.
   The core owns the four correctness rules (β, δ⋈δ, γ⋈δ, ε) and is complete with no driver loaded: a driver can only
   *pre-empt* a redex class before the core reaches it, never replace a rule.  Deep optimisation strategies (native
   scalar folding, thread/GPU wave policy, Lévy bracketing) live entirely in drivers. */
#define LIN_DRIVER_MAGIC 0x4C494E44u            /* 'LIND' */
/* ABI 2 appends arg_fold/materialize/drain/pending and adds LIN_CAP_PREEMPT.  The append itself is
   designated-initialiser safe, but a .so built against ABI 1 is *smaller* than this struct, so reading the new
   fields would run past its end: the bump makes the core reject such a driver loudly instead.  Rebuild plugins. */
#define LIN_DRIVER_ABI   2u
#define LIN_CAP_NATIVE_NUM 0x01u                 /* satur `_ffi` arithmetic */
#define LIN_CAP_FIXED      0x02u                 /* beta / annihilate / erase */
#define LIN_CAP_COMMUTE    0x04u                 /* LAM|APP x DUP (allocating) */
/* A pre-emptor is a reduction *pre-pass*, not a strategy: it claims redex classes the core would otherwise handle
   (native folds, guarded deferral) and composes with whichever strategy is selected.  `lin_driver_clear` — what
   `(set_driver ...)` calls — drops strategies but KEEPS pre-emptors, so selecting "cpu"/"simd"/"gpu" never silently
   disables the fold pre-pass. */
#define LIN_CAP_PREEMPT    0x08u

typedef struct LinDriver {
  uint32_t magic;                                /* must be LIN_DRIVER_MAGIC */
  uint32_t abi;                                  /* must be LIN_DRIVER_ABI   */
  const char *name, *description;
  uint64_t caps;                                 /* OR of LIN_CAP_* bits      */
  int priority;                                  /* lower runs earlier        */
  int (*claim)(const Net *n, Port p1, Port p2);  /* pure: can this driver handle this redex? */
  int (*reduce)(Net *n, Port *redexes, int nred, long limit, int *changed); /* consume claimed slice */
  /* ---- ABI 2 optional hooks (NULL = not implemented) ---- */
  /* Pre-empt a sub-term sitting in a β *argument* position (e.g. the saturated `(mul 2 2)` of `succ (mul 2 2)`).
     A driver never sees that shape as a principal×principal redex, so the core offers it explicitly: return 1 if
     `arg` was materialised as a value at `target`, 0 to let plain β substitute it. */
  int (*arg_fold)(Net *n, Port arg, Port target);
  /* Readback pre-pass: materialise a sub-term the reducer left as a driver-foldable closure (e.g. a saturated
     `_ffi` closure embedded in a numeral spine) into `*out`; return 0 to leave `p` alone. */
  int (*materialize)(Net *n, Port p, Port *out);
  /* The active wave drained.  Retry whatever this driver parked because its operands were not concrete yet,
     re-enqueueing via lin_enqueue(); return the number of pairs re-enqueued (0 = nothing left to wait for).  The
     waiting policy — how long to wait, when to give up and let the core β it — belongs to the driver. */
  int (*drain)(Net *n);
  /* 1 if this driver still holds un-materialised work for `n` (a parked redex it never folded).  A reduction that
     ends with a driver pending has not reached a value, so its result must not be baked into a precompiled def. */
  int (*pending)(const Net *n);
} LinDriver;

void lin_driver_add(LinDriver *d); void lin_driver_clear(void); LinDriver *lin_get_driver(void);
/* 1 if any loaded driver still holds un-materialised work for `n` (Net.driver_pending or LinDriver.pending) */
int lin_any_pending(const Net *n);
/* a driver reports that it claimed a redex it could not materialise (see Net.driver_pending) */
void lin_pending_bump(Net *n);
/* readback pre-pass: 1 and `*out` set when a driver materialised a foldable closure at `p` (see LinDriver.materialize) */
int lin_materialize(Net *n, Port p, Port *out);
int wave_snapshot(Net *n, Port **out, int *cap);
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed);
void lin_enqueue(Net *n, Port a, Port b); /* push an active redex pair (plugin hook) */
void lin_fold_bump(void);  long lin_fold_total(void); /* driver native-fold accounting */
/* ---- General native scalar-op extension hook: plugins register a ScalarOpFn provider for a class of ops (arith.so first); run_ffi tries providers in order ---- */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
void lin_scalar_ops_add(ScalarOpFn f);
/* dlopen std/drivers/<sym>.so (idempotent) so its constructor registers ops */
void lin_scalar_ops_load(const char *sym);
/* Canonical shared scalar-op table (std/drivers/arith.so): the single arithmetic authority any reduction strategy may call */
int lin_arith_scalar(const char *fn, int argc, const long *args, long *out, int *outkind);

/* ---------------- parser ---------------- */
typedef void (*FormFn)(Term *, const char *, void *);
void parse_forms(const char *src, FormFn fn, void *ud);
Term *term_new(int type, const char *name, Term *l, Term *r); Term *term_copy(Term *t);
void term_free(Term *t); int term_refs(Term *t, const char *name);

/* ---------------- types ---------------- */
typedef struct { int nq, q[256]; Type *t; } Scheme;
int type_check(Term *t, Scheme *out, char *err, int errsz);
int type_check_rec(const char *name, Term *body, Scheme *out, char *err, int errsz);
void scheme_print(Scheme *s);
Type *type_var(void); Type *type_arrow(Type *a, Type *b); Type *type_nominal(const char *name); Type *type_arg(Type *arg); Type *type_param(int idx);
int nominal_lookup(const char *name); int nominal_register(const char *name, int arity);
int nominal_arity(const char *name);
Scheme scheme_all(Type *t);

/* ---------------- compile & aot & .line ---------------- */
int compile(Term *t, Net *n, char *err, int errsz);
Term *egraph_optimize(Term *t);
int net_save_line(Net *n, const char *path); int net_load_line(Net *n, const char *path);
void lin_set_self_path(const char *p); /* .line shebang = this absolute path */

/* ---------------- datatype registry: a value domain is keyed by its carrier node names; decoders consult ctor_tag ---------------- */
enum { DT_NUM, DT_BOOL, DT_STR, DT_FFI, DT_EFF, DT_FLOAT, DT_OP, DT_MAX };
typedef struct {
  int tag;                 /* builtin DT_* or -1 for user types */
  const char *carrier;     /* primary lambda carrier name, e.g. "_sz" */
  const char *carrier2;    /* second carrier (num=_ss, bool=_bf, str=_nl), or NULL */
} Constructor;
/* ---------------- readback ---------------- */
typedef struct { int kind; long iv; char sv[4096]; } Val;  /* kind: 0 none,1 int,2 str,3 bool,4 float (iv=IEEE bits) */
long net_read_int(Net *n, Port p); int net_read_bool(Net *n, Port p);
int net_read_float(Net *n, Port p, double *out);
int net_read_string(Net *n, Port p, char *buf, size_t max); int net_run_io(Net *n, long step_limit);
int net_print(Net *n);
/* ---- Fold machinery does NOT live here: the `_ffi`/`_op` native fold, its saturation guards, its deferral policy
   and the "this def is not materialised" decline all belong to std/drivers/arith.so (a LIN_CAP_PREEMPT driver),
   reached through LinDriver.{claim,reduce,arg_fold,materialize,drain,pending}.  What the core keeps is the four
   correct rules and the mechanisms a driver needs to pre-empt them; with no driver loaded the same programs still
   reduce exactly, by plain β of the pure-Lin fallback bodies. ---- */
/* ---- Shared on-net FFI decoder (std/runtime/decoder.c): driver plugins reuse the one arg-spine / DUP-hop walker for the `_ffi` `_cl`-spine decode ---- */
Port net_dhop(Net *n, Port p);                          /* deref a DUP(port0) chain */
int  net_ffi_fn(Net *n, Port p, char *fn, int fnmax);   /* fn name of a _ffi closure */
int  net_ffi_args(Net *n, Port lam, Val *vals, int max); /* decode arg spine into Vals */
int  net_spine_args(Net *n, Port argp, Val *vals, int max); /* decode a `_cl`-spine at a port */
/* !=0 while def_precompile reduces an open body: a driver must not fold there, since the operands are free vars
   that never become concrete and a baked closure would capture a stale value */
extern int lin_precompile_depth;
/* !=0 while the AOT build is partially evaluating: a driver must not bake anything the
   program would observe at RUN time (e.g. a (lin_folds) probe) into the artifact */
extern int lin_build_depth;
/* datatype registry (populated by builtins + `datatype` forms) */
int  ctor_tag(const char *name); /* builtin domain DT_*, or -1 */
int  ctor_register(const char *name, int tag, const char *c1, const char *c2);
void ctor_init_builtins(void);
Port net_alloc_scott(Net *n, long k); Port net_alloc_bool(Net *n, int v);
Port net_alloc_float(Net *n, double d);

/* ---------------- goi ---------------- */
long long goi_det(Net *n);

/* ---------------- main / defs ---------------- */
typedef struct { char name[NAME]; Term *term, *expanded; Scheme sch; int typed, rec;
                 int rec_k; Term *rec_body;   /* widening self-recursion bound + original body */
                 char rec_name[NAME];         /* binder name the recursive self-refs use (see widen_recursion) */
                 Net *compiled; int comp_tried; } Def;
extern Def *defs;
extern int ndefs, lin_threads;
Def *def_find(const char *name);
void set_namespace(const char *name); void open_namespace(const char *name);
Term *expand_defs(Term *t);
void eval_form(Term *t);

#endif