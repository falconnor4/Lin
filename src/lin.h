#ifndef LIN_H
#define LIN_H
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>

#define NAME 256

/* ---------------- core terms (pure untyped lambda) ---------------- */
enum { TVAR, TLAM, TAPP, TDEF, TDEFX, TLOAD, TNS, TOPEN, TDATATYPE, TFLOAT };
typedef struct Type { int kind, id; struct Type *a, *b; } Type;
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
  Port *blocked; int nblocked, blockedcap;
  long steps, declines;
} Net;

Port net_alloc(Net *n, int tag, Scope sc, const char *name);
void net_link(Net *n, Port a, Port b, int enqueue);
void net_init(Net *n, int cap); void net_free(Net *n); int net_interact(Net *n, Port a, Port b);
long net_reduce(Net *n, long limit);
Net *net_copy(const Net *n); Scope scope_nil(void);
Scope scope_ext(Net *n, Scope s, int bit); int scope_eq(Net *n, Scope a, Scope b);

/* ---------------- driver ABI ---------------- */
/* Drivers reduce a redex *class*; core waves fan out to each in priority order, each claiming the redexes it handles. */
#define LIN_DRIVER_MAGIC 0x4C494E44u            /* 'LIND' */
#define LIN_DRIVER_ABI   1u
#define LIN_CAP_NATIVE_NUM 0x01u                 /* satur `_ffi` arithmetic */
#define LIN_CAP_FIXED      0x02u                 /* beta / annihilate / erase */
#define LIN_CAP_COMMUTE    0x04u                 /* LAM|APP x DUP (allocating) */

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
/* ---- General native scalar-op extension hook ----
   Plugins register a ScalarOpFn provider implementing a class of native scalar
   ops (arith.so is the first consumer); run_ffi tries providers in order. */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
void lin_scalar_ops_add(ScalarOpFn f);
/* dlopen std/drivers/<sym>.so (idempotent) so its constructor registers ops */
void lin_scalar_ops_load(const char *sym);
/* Canonical shared scalar-op table (implemented by std/drivers/arith.so):
   the single arithmetic authority that any reduction strategy may call. */
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
Type *type_var(void); Type *type_arrow(Type *a, Type *b);
Type *type_list(Type *e); Scheme scheme_all(Type *t);

/* ---------------- compile & aot & .line ---------------- */
int compile(Term *t, Net *n, char *err, int errsz);
Term *egraph_optimize(Term *t);
int net_save_line(Net *n, const char *path); int net_load_line(Net *n, const char *path);
void lin_set_self_path(const char *p); /* .line shebang = this absolute path */

/* ---------------- datatype registry ----------------
   A value domain (num, bool, string, ffi/effect) is keyed by carrier node names; decoders consult this table (ctor_tag). */
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
/* Fold a saturated _ffi closure (LAM x APP) natively into a concrete net value during reduction; returns 1 on success. */
int lin_fold_ffi(Net *n, Port lam, Port app);
/* Fold a saturated pure-Lin arithmetic-op closure (DT_OP named LAM); reads tag + operands via shared scalar table. */
int lin_fold_op(Net *n, Port lam, Port app);
/* Fold a saturated pure-Lin `_op` closure appearing as a beta ARGUMENT (not head) */
int lin_fold_op_arg(Net *n, Port lam, Port out);
/* 1 if an `_op` head-redex's applied operands are not yet decodable and should be deferred rather than β-squashed */
int lin_op_needs_operand(Net *n, Port lam, Port app);
/* non-destructive pre-scan: 1 if a pure-lin _ffi closure is blocked solely by a non-concrete operand and should be deferred */
int lin_ffi_needs_operand(Net *n, Port lam);
/* Fold a saturated _ffi closure appearing as a beta ARGUMENT (not head); see io.c */
int lin_fold_ffi_arg(Net *n, Port lam, Port out);
/* ---- Shared on-net FFI decoder (implemented by std/runtime/decoder.c) ----
   Driver plugins reuse ONE arg-spine / DUP-hop walker for the `_ffi` `_cl`-spine decode. */
Port net_dhop(Net *n, Port p);                          /* deref a DUP(port0) chain */
int  net_ffi_fn(Net *n, Port p, char *fn, int fnmax);   /* fn name of a _ffi closure */
int  net_ffi_args(Net *n, Port lam, Val *vals, int max); /* decode arg spine into Vals */
int  net_spine_args(Net *n, Port argp, Val *vals, int max); /* decode a `_cl`-spine at a port */
/* !=0 while def_precompile reduces an open body: suppress folding so it never runs on non-concrete operands */
extern int lin_precompile_depth;
/* bumped when a foldable head-closure is consumed unfolded during precompile */
extern int lin_stuck_ffi_count;
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
                 Net *compiled; int comp_tried; } Def;
extern Def *defs;
extern int ndefs, lin_threads;
Def *def_find(const char *name);
void set_namespace(const char *name); void open_namespace(const char *name);
Term *expand_defs(Term *t);
void eval_form(Term *t);

#endif