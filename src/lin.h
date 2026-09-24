#ifndef LIN_H
#define LIN_H
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>

#define NAME 256

/* ---------------- core terms (pure untyped lambda) ---------------- */
enum { TVAR, TLAM, TAPP, TDEF, TDEFX, TLOAD, TNS, TOPEN, TDATATYPE, TFLOAT, TEXPORT,
       /* (let ((n v)) b): ONE net shared by every use of `n`, value included, so a use of
          `n` inside `v` closes a cycle.  That is recursion, and it needs no unrolling. */
       TLET };
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
/* A gauge is a LEVEL, held as an id into the net's level trie (0 = the term root).  Interning
   makes equal paths equal ids net-wide, so equality is an integer compare, the meet is the
   lowest common ancestor, and "nested inside" is a walk up the trie.  Nothing spills to a side
   table, so a 300-step path costs exactly what a 3-step path does. */
typedef uint32_t Scope;

typedef struct {
  int cap, nn; unsigned char *tag; Port *wire; Scope *scope; char **name;
  Port *act; int atop, actcap; unsigned char *dead;
  /* level trie: lv_parent[l]/lv_bit[l] are the trie edge into level l; nlv is its size.  Branches
     are {1, 0}: scope_app masks `bit & 1` (net.c), and the compiler passes 1 for a function
     position / lambda body and 2 for an argument, so branch 2 folds onto branch 0.  There is no
     separate "knot namespace" — node dumps put argument-position nodes at paths like `0` and `01`. */
  int *lv_parent, *lv_depth, *lv_hash, nlv, lvcap, lv_hcap;
  unsigned char *lv_bit;
  /* Needed order: demand roots are the ports a value is observed at.  ROOT is always one; net_force
     and lin_demand add the rest.  `dem[i] == dem_stamp` means node i is on a demand path, so marks
     are invalidated by bumping the stamp (no O(nn) clear, and compaction needs no remap). */
  Port *root; int nroot, rootcap;
  unsigned int *dem, dem_stamp; unsigned char *vport;
  long steps;
} Net;

/* wire of a port (drivers read the graph directly) */
static inline Port net_wire(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }

Port net_alloc(Net *n, int tag, Scope sc, const char *name);
void net_link(Net *n, Port a, Port b, int enqueue);
void net_init(Net *n, int cap); void net_free(Net *n); int net_interact(Net *n, Port a, Port b);
long net_reduce(Net *n, long limit);
/* Evaluate the spine from `p` to a weak head normal form (or the step budget), by registering `p`
   as a demand root and running the needed-order reducer.  Re-entrant and local. */
long net_force(Net *n, Port p);
/* Register an extra demand root: a port whose weak head normal form the caller is about to observe. */
void lin_demand(Net *n, Port p);
Net *net_copy(const Net *n); Scope scope_nil(void);
/* reclaim every node not reachable from ROOT (identity-preserving; safe at any point a
   net is a value or a residual -- the AOT build compacts before serialising) */
void net_gc(Net *n);
int scope_eq(const Net *n, Scope a, Scope b);
Scope scope_app(Net *n, Scope s, int bit);   /* one step deeper */
Scope scope_meet(Net *n, Scope a, Scope b);   /* lowest common ancestor */
/* place `s` (a level in `src`) under `lvl` in `n`: what a spliced clone's gauges need */
Scope scope_rebase(Net *n, const Net *src, Scope lvl, Scope s);
int net_level_count(const Net *n);
void net_level_set(Net *n, int nlv, const int *parent, const unsigned char *bit);

/* ---------------- driver ABI ---------------- */
#define LIN_DRIVER_MAGIC 0x4C494E44u            /* 'LIND' */
#define LIN_DRIVER_ABI   3u
#define LIN_CAP_NATIVE_NUM 0x01u                 /* satur `_ffi` arithmetic */
#define LIN_CAP_FIXED      0x02u                 /* beta / annihilate / erase */
#define LIN_CAP_COMMUTE    0x04u                 /* LAM|APP x DUP (allocating) */
#define LIN_CAP_PREEMPT    0x08u

typedef struct LinDriver {
  uint32_t magic;                                /* must be LIN_DRIVER_MAGIC */
  uint32_t abi;                                  /* must be LIN_DRIVER_ABI   */
  const char *name, *description;
  uint64_t caps;                                 /* OR of LIN_CAP_* bits      */
  int priority;                                  /* lower runs earlier        */
  int (*claim)(const Net *n, Port p1, Port p2);  /* pure: can this driver handle this redex? */
  int (*reduce)(Net *n, Port *redexes, int nred, long limit, int *changed); /* consume claimed slice */
} LinDriver;

void lin_driver_add(LinDriver *d); void lin_driver_clear(void); LinDriver *lin_get_driver(void);
int wave_snapshot(Net *n, Port **out, int *cap);
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed);
void lin_enqueue(Net *n, Port a, Port b); /* push an active redex pair (plugin hook) */
void lin_fold_bump(void);  long lin_fold_total(void); /* driver native-fold accounting */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
void lin_scalar_ops_add(ScalarOpFn f);
void lin_scalar_ops_load(const char *sym);
int lin_arith_scalar(const char *fn, int argc, const long *args, long *out, int *outkind);

/* ---------------- parser ---------------- */
typedef void (*FormFn)(Term *, const char *, void *);
void parse_forms(const char *src, FormFn fn, void *ud);
Term *term_new(int type, const char *name, Term *l, Term *r); Term *term_copy(Term *t);
void term_free(Term *t); int term_refs(Term *t, const char *name);
Term *term_fix(const char *name, Term *body);

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
/* where readback writes; NULL = stdout.  A prelude load points it at a sink so that the effects its
   top-level forms perform still run (FFI dispatch happens in readback) without joining the output. */
extern FILE *lin_out;
/* ---- Fold machinery does NOT live here: the `_ffi`/`_op` native fold, its saturation guards and its
   deferral policy all belong to std/drivers/arith.so (a LIN_CAP_PREEMPT driver), reached through
   LinDriver.{claim,reduce}.  A driver that needs a concrete operand forces it with net_force.  The core keeps
   the four correct rules and the mechanisms a driver needs to pre-empt them; with no driver loaded the same
   programs still reduce exactly, by plain β of the pure-Lin fallback bodies. ---- */
/* ---- Shared on-net FFI decoder (std/runtime/decoder.c): driver plugins reuse the one arg-spine / DUP-hop walker for the `_ffi` `_cl`-spine decode ---- */
Port net_dhop(Net *n, Port p);                          /* deref a DUP(port0) chain */
int  net_ffi_fn(Net *n, Port p, char *fn, int fnmax);   /* fn name of a _ffi closure */
int  net_ffi_args(Net *n, Port lam, Val *vals, int max); /* decode arg spine into Vals */
int  net_spine_args(Net *n, Port argp, Val *vals, int max); /* decode a `_cl`-spine at a port */
int  net_spine_slots(Net *n, Port argp); /* operand count of a `_cl` arg list (-1: not a cons spine) */
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
/* The float box table: boxes carry an INDEX, so the .line container has to carry the table. */
int lin_flt_count(void); const double *lin_flt_data(void); void lin_flt_set(const double *d, int n);

/* ---------------- goi ---------------- */
long long goi_det(Net *n);

/* ---------------- main / defs ---------------- */
typedef struct { char name[NAME]; Term *term, *expanded; Scheme sch; int typed, rec;
                 Net *compiled; int comp_tried; } Def;
extern Def *defs;
extern int ndefs, lin_threads;
Def *def_find(const char *name);
void set_namespace(const char *name); void open_namespace(const char *name);
Term *expand_defs(Term *t);
void eval_form(Term *t);

#endif
