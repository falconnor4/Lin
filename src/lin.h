#ifndef LIN_H
#define LIN_H
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>

#define NAME 256

/* ---------------- core terms (pure untyped lambda) ---------------- */
enum { TVAR, TLAM, TAPP, TDEF, TDEFX, TLOAD, TNS, TOPEN, TDATATYPE };
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
  long steps;
} Net;

Port net_alloc(Net *n, int tag, Scope sc, const char *name);
void net_link(Net *n, Port a, Port b, int enqueue);
void net_init(Net *n, int cap); void net_free(Net *n); int net_interact(Net *n, Port a, Port b);
long net_reduce(Net *n, long limit);
Net *net_copy(const Net *n); Scope scope_nil(void);
Scope scope_ext(Net *n, Scope s, int bit); int scope_eq(Net *n, Scope a, Scope b);
typedef struct LinDriver { const char *name; int (*reduce_wave)(Net *n, long limit, int *changed); } LinDriver;
void lin_driver_add(LinDriver *d); void lin_driver_clear(void); LinDriver *lin_get_driver(void);
int wave_snapshot(Net *n, Port **out, int *cap);
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed);

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

/* ---------------- datatype registry ----------------
   A value domain (num, bool, string, ffi/effect) is keyed by its carrier node
   names; builtins are pre-registered so the readback layer decodes and renders
   them, and user code can register more (see `datatype`).  Decoders consult
   this table (ctor_tag) instead of comparing specific name strings. */
enum { DT_NUM, DT_BOOL, DT_STR, DT_FFI, DT_EFF, DT_MAX };
typedef struct {
  int tag;                 /* builtin DT_* or -1 for user types */
  const char *carrier;     /* primary lambda carrier name, e.g. "_sz" */
  const char *carrier2;    /* second carrier (num=_ss, bool=_bf, str=_nl), or NULL */
} Constructor;
/* ---------------- readback ---------------- */
typedef struct { int kind; long iv; char sv[4096]; } Val;   /* kind: 0 none,1 int,2 str,3 bool */
long net_read_int(Net *n, Port p); int net_read_bool(Net *n, Port p);
int net_read_string(Net *n, Port p, char *buf, size_t max); int net_run_io(Net *n, long step_limit);
int net_print(Net *n);
/* datatype registry (populated by builtins + `datatype` forms) */
int  ctor_tag(const char *name); /* builtin domain DT_*, or -1 */
int  ctor_register(const char *name, int tag, const char *c1, const char *c2);
void ctor_init_builtins(void);
Port net_alloc_scott(Net *n, long k); Port net_alloc_bool(Net *n, int v);

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