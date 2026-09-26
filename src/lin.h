#ifndef LIN_H
#define LIN_H
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stddef.h>

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
/* A type scheme, declared here because the driver ABI hands a pass the inferred types and that hook
   is defined long before the type interface below. */
typedef struct { int nq, q[256]; Type *t; } Scheme;

/* ---------------- interaction net ---------------- */
enum { LAM, APP, DUP, ERA, ROOT };

typedef struct { int node:30; unsigned int port:2; } Port;
/* A gauge is a LEVEL: an id into the net's level trie (0 = the term root).  Interning makes equal
   paths equal ids net-wide, so equality is an integer compare, the meet is the lowest common
   ancestor, and "nested inside" is a walk up -- a 300-step path costs what a 3-step one does. */
typedef uint32_t Scope;

/* ---- claiming: a lease on STRUCTURE, not on values ----
   A driver identifies structure it can optimize and asks the core to reserve it: a set of redexes plus
   the region's EXITS, validated before the driver may touch it.  Nothing here knows what a driver
   matches or why (tags, ports, wiring only), so a loop compiler, a fusion pass and a scalar folder
   share one protocol.  Every exit must be at an AUXILIARY port: a redex is two mutually wired
   principal ports, so such a boundary cannot be crossed by one -- the whole safety argument for
   rewriting a region in isolation. */
#define LIN_MAX_CLAIM_PAIRS 32
#define LIN_MAX_CLAIM_EXITS 16
#define LIN_CLAIM_NODES     128     /* a bounded region: the core walks it per claim, so it is capped */
#define LIN_CLAIM_REGION 0x01u      /* validate the closure and reserve every redex inside it */
#define LIN_CLAIM_HELD   0x02u      /* keep this claim across waves (see revalidate) */

typedef struct {
  uint32_t flags;
  Port pairs[2 * LIN_MAX_CLAIM_PAIRS];
  int  npairs;                      /* redexes this claim consumes */
  Port exits[LIN_MAX_CLAIM_EXITS];
  int  nexits;                      /* the region's frontier: auxiliary ports, exhaustively */
  int  nodes[LIN_CLAIM_NODES];      /* filled by lin_claim_check: the reserved region */
  int  nnodes;
} LinClaim;

/* What a driver is offered in the match phase: this wave's unclaimed redexes.  A driver is
   consulted ONCE per wave, not once per pair, which keeps dispatch from growing with the number of
   drivers.  What it OWNS is the region it proposes ITSELF -- redexes plus the exits it declares --
   and the core validates that claim before the driver may touch the structure.  The offer is
   this-wave scratch and read-only: read it, never keep it. */
typedef struct { Port *pairs; int npairs; } LinView;

/* Per-net state slots, one per registered driver: where a driver keeps its own tables.  The
   core only allocates, releases and copies them; it never looks inside. */
#define LIN_DRV_SLOTS 8

struct LinDriver;                  /* defined below: a net holds the claims a driver asked to keep */
typedef struct LinDriver LinDriver;

typedef struct {
  int cap, nn; unsigned char *tag; Port *wire; Scope *scope;
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
  /* Reclaimed node slots, threaded through their own port 0.  Reclamation never moves a node, so
     every index stays valid and an external handle (a memo key, a port readback holds) is safe. */
  int free_head, nfree;
  /* Slots freed during a wave.  They are NOT published to free_head until the wave's snapshot is
     gone: an index the snapshot still holds would otherwise be revived as a different node. */
  int pend_head;
  /* Nonzero while readback is walking the net holding ports.  A reclaimed slot is REUSED, so a
     cursor held across a collection would silently name a different node; readback therefore pins. */
  int pins;
  unsigned int *dem, dem_stamp; unsigned char *vport;
  /* A driver's tables for THIS net: kept here so their lifetime is the net's -- created lazily,
     released with it, copied with it.  A table keyed by node index is only meaningful beside its
     net, and node slots are RECYCLED, so a stale index names a different node. */
  void *drv[LIN_DRV_SLOTS];
  /* Claims to keep across waves.  The core holds them because the core enforces exclusivity: a
     held region stays reserved while the driver builds what it will optimize. */
  LinClaim held[4];
  LinDriver *held_drv[4];
  int nheld;
  long steps;
} Net;

/* wire of a port (drivers read the graph directly) */
static inline Port net_wire(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }

/* `tag`, wiring and gauge: a node has NO name.  A carrier label is not structure -- Scott zero and
   Church TRUE are one net -- so anything that needs to know what a node MEANS states the encoding it
   expects (LIN_ENC_* above, and the readers that take one). */
Port net_alloc(Net *n, int tag, Scope sc);
void net_link(Net *n, Port a, Port b, int enqueue);
/* Cut the wire at `p` at both ends: what disposes of a subgraph, and what erases (see net.c). */
void net_sever(Net *n, Port p);
/* Readback holds ports across nested reductions, so it pins the net: no reclamation while pinned. */
void lin_pin(Net *n); void lin_unpin(Net *n);
void net_init(Net *n, int cap); void net_free(Net *n); int net_interact(Net *n, Port a, Port b);
long net_reduce(Net *n, long limit);
/* Evaluate the spine from `p` to a weak head normal form (or the step budget), by registering `p`
   as a demand root and running the needed-order reducer.  Re-entrant and local. */
long net_force(Net *n, Port p);
/* Force `p` to WHNF and return a port that still names the value: what readback needs, and the reason
   the core owns it (the caller would otherwise hold a port the rule it fired consumed). */
Port net_force_val(Net *n, Port p);
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

/* A decoded value: the ABI's common currency between the core's readers and a driver's storage.
   kind: 0 none, 1 int, 2 str, 3 bool, 4 float (iv carries IEEE-754 bits). */
typedef struct { int kind; long iv; char sv[4096]; } Val;

/* ---------------- value ENCODINGS: the SHAPE a value is written in ----------------
   A value DOMAIN (DT_*) is what a value MEANS; an ENCODING (LIN_ENC_*) is the net STRUCTURE it is
   written in, and the two are different questions: Scott zero (`\sz.\ss.sz`), Church TRUE and the
   empty list are ONE net, so nobody may recover a node's meaning from the node.  The EXPECTATION is
   the reader's, and one given none (a raw net from anywhere) must decline rather than guess.
   DT_FLOAT is where this bites: its values are a BOXED INDEX (LIN_ENC_BOX) into a provider's table,
   so the domain -- or the table's bounds -- is what says "2.5" rather than "2". */
enum { LIN_ENC_NUM, LIN_ENC_BOOL, LIN_ENC_CONS, LIN_ENC_STR, LIN_ENC_OP, LIN_ENC_FFI,
       LIN_ENC_EFF, LIN_ENC_BOX };

/* ---------------- driver ABI ---------------- */
#define LIN_DRIVER_MAGIC 0x4C494E44u            /* 'LIND' */
/* ABI 4 adds `net_size`: a plugin reads the Net it is handed DIRECTLY (n->tag, n->wire, n->dead), so a
   field added to Net shifts every offset and it silently reads the wrong memory -- measured, a `fold`
   that simply stopped firing with the plugin still passing every ABI check.  ABI 6 is the ENCODING
   change: a net carries no carrier names, so `read_value`/`print` take the encoding (LIN_ENC_*) /
   the domain (DT_*) the caller expects, and the number moves. */
#define LIN_DRIVER_ABI   6u
#define LIN_CAP_NATIVE_NUM 0x01u                 /* satur `_ffi` arithmetic */
#define LIN_CAP_FIXED      0x02u                 /* beta / annihilate / erase */
#define LIN_CAP_COMMUTE    0x04u                 /* LAM|APP x DUP (allocating) */
#define LIN_CAP_PREEMPT    0x08u
/* Supplies storage or semantics the runtime depends on (a value domain's table, an encoding).
   Like a pre-emptor it is not a *strategy*, so `(set_driver ...)` must not drop it. */
#define LIN_CAP_PROVIDER   0x10u

/* Hooks a driver cannot work without.  A `wants` bit the core cannot satisfy -- including one it
   does not know -- refuses the plugin rather than running it without it: the ABI-4 lesson applied
   to capabilities instead of layout. */
#define LIN_WANT_STATE    0x01u   /* per-net state, released with the net */
#define LIN_WANT_RECYCLE  0x02u   /* node_recycled */
#define LIN_WANT_CARRY    0x04u   /* carry_save / carry_load */
#define LIN_WANT_VALUES   0x08u   /* val_box / val_unbox for a DT_* domain */
#define LIN_WANT_MATCH    0x10u   /* match / act: claim by shape, once per wave */
#define LIN_WANT_HELD     0x20u   /* revalidate / release_claim: claims across waves */
#define LIN_WANT_READBACK 0x40u   /* read_value / print / run_io: observing a reduced net */
#define LIN_WANT_AOT      0x80u   /* aot: a build-time pass this driver owns */
#define LIN_WANT_ALL      (LIN_WANT_STATE | LIN_WANT_RECYCLE | LIN_WANT_CARRY | LIN_WANT_VALUES | \
                           LIN_WANT_MATCH | LIN_WANT_HELD | LIN_WANT_READBACK | LIN_WANT_AOT)

/* The interface is EXTENSIBLE BY SIZE (the point of this ABI): a plugin sets `size` to the struct
   as it was built, the core reads only fields that fit, so appending a hook is not a break.  The
   ABI number moves only when an existing field's MEANING changes. */


struct LinDriver {
  uint32_t magic;                                /* must be LIN_DRIVER_MAGIC  */
  uint32_t abi;                                  /* must be LIN_DRIVER_ABI    */
  uint32_t net_size;                             /* must be sizeof(Net); see above */
  const char *name, *description;
  uint64_t caps;                                 /* OR of LIN_CAP_* bits      */
  int priority;                                  /* lower runs earlier        */
  int (*claim)(const Net *n, Port p1, Port p2);  /* pure: can this driver handle this redex? */
  int (*reduce)(Net *n, Port *redexes, int nred, long limit, int *changed); /* consume claimed slice */
  /* ---- ABI 5, append-only; every field optional ---- */
  uint32_t size;                                 /* sizeof(LinDriver); bounds what the core reads */
  uint64_t wants;                                /* LIN_WANT_* this driver requires */
  uint64_t domains;                              /* bitmask of DT_* whose storage it holds */
  int slot;                                      /* assigned by the core at registration */
  void *(*state_new)(Net *n);                    /* a net's tables for this driver, or NULL */
  void  (*state_free)(Net *n, void *st);
  /* net_copy: fill `dst_st` from `st`.  Optional -- state is a derivation of the net, so a driver
     that cannot copy simply starts empty in the copy, which is safe and never authoritative. */
  void  (*state_copy)(Net *n, void *st, Net *dst, void *dst_st);
  /* A freed slot has been handed out again: any table entry keyed by `node` is about a node that
     no longer exists.  This is the one event only the core knows, and it is why a driver may key
     tables by node index at all. */
  void  (*node_recycled)(Net *n, void *st, int node);
  /* Value storage for the domains in `domains`.  A box stays net STRUCTURE (the shape is the
     registry's business, above), so the core keeps no value, no table and no arithmetic; it only
     asks the provider that declared the domain. */
  Port  (*val_box)(Net *n, void *st, const Val *v);
  int   (*val_unbox)(Net *n, void *st, Port p, Val *v);
  /* Opaque artifact sections: whatever the driver needs carried through a .line round trip, so
     the container never learns what a table means. */
  int   (*carry_save)(Net *n, void *st, void **blob, size_t *len);
  int   (*carry_load)(Net *n, void *st, const void *blob, size_t len);
  /* `match` runs once per wave BEFORE any slice exists, which is what makes a claim exact: it may
     inspect and force (how a shape behind a thunk becomes readable) and claims only what it can act
     on.  `act` rewrites inside the region the core validated. */
  int   (*match)(Net *n, void *st, LinView *view, LinClaim *out);
  int   (*act)(Net *n, void *st, LinClaim *owned);
  int   (*revalidate)(Net *n, void *st, LinClaim *held);   /* 1 keep, 0 drop */
  void  (*release_claim)(Net *n, void *st, LinClaim *c);
  /* Observing the net: what the core does NOT do, because turning a reduced net back into a value --
     decoding a port, printing it, running its effects and dispatching the FFI those need -- is not
     reduction.  The core keeps thin dispatchers (net_print / net_run_io / net_read_value, src/io.c)
     that hand the work to whichever driver declares LIN_WANT_READBACK. */
  int  (*read_value)(Net *n, void *st, Port p, int domain, Val *v); /* decode one value, as `domain` */
  int  (*print)(Net *n, void *st, int domain);             /* walk the net and write the result */
  long (*run_io)(Net *n, void *st, long limit);            /* run the net's effects */
  /* ---- ABI 6, append-only: the AOT PASS POINT.  The compiler OFFERS it, the driver OWNS the pass:
     called once per AOT build in priority order with the expanded term, the types the compiler
     inferred for it, the net, and a term -> port map as a CALLBACK that is compile-time only -- never
     serialised, never stored, so a pass cannot smuggle the compiler's knowledge of meaning past the
     build.  It may emit a rewrite of the term or the net, or its own opaque section
     (carry_save/carry_load), and nothing else.  A pass that declines leaves the net as it found it;
     every pass is OPTIONAL (LIN_NO_PASS); and at runtime a section is a DERIVATION of the net
     (node_recycled invalidates it), never the authority. */
  int  (*aot)(Net *n, void *st, const Term *t, const Scheme *sch,
              Port (*node_of)(void *ctx, const Term *t), void *ctx);
};

/* Validate a claim and fill in `nodes`: every exit auxiliary and on the frontier, every pair live,
   the region bounded.  0 = refused, with the reason in `why`.  A driver PROPOSES its region (the
   pairs it wants and the exits it declares) and this is the whole of the core's part: structure,
   never meaning -- so the caller states its own boundary and the exit rule is what it must satisfy. */
int lin_claim_check(Net *n, LinClaim *c, char *why, int whysz);

/* Is this port's node on the demand path?  A matcher prefers demanded structure: firing undemanded
   work is what unrolls a Y-knot, so it defers instead (LIN_CLAIM_HELD). */
int lin_demanded(const Net *n, Port p);

void lin_driver_add(LinDriver *d); void lin_driver_clear(void); LinDriver *lin_get_driver(void);
/* The first registered driver providing `want`, or NULL: found by the HOOK the want names, never by a
   driver's name, so the core can reach a capability without knowing who supplies it. */
LinDriver *lin_driver_wanting(uint64_t want);
/* dlopen a driver plugin by name (idempotent); an artifact's sections use this to load whoever
   wrote them, so a container is self-describing without the core knowing any driver. */
int lin_driver_load(const char *name);
/* This driver's tables for `n`, created on first use and released with the net. */
void *lin_driver_state(Net *n, LinDriver *d);
/* Storage for a value domain, resolved to whichever driver declared it (NONE / 0 if none). */
Port net_box_value(Net *n, int domain, const Val *v);
int  net_unbox_value(Net *n, int domain, Port p, Val *v);
/* Opaque artifact sections: one per driver that has state to carry, tagged with its name and
   handed back on load (a section whose driver is absent is loaded on demand, so an artifact is
   self-describing).  The container never learns what a section means. */
void lin_driver_carry_write(Net *n, FILE *f);
void lin_driver_carry_read(Net *n, FILE *f, uint32_t count);
int  lin_driver_carry_legacy(Net *n, int domain, const void *blob, size_t len);
/* A BOXED INDEX (LIN_ENC_BOX): the shape a domain whose value is an ENTRY IN A TABLE writes, which is
   the generic primitive a value provider builds its own boxes with.  Net structure, not policy. */
Port net_box_index(Net *n, long i);
long net_peel_index(Net *n, Port p);
int wave_snapshot(Net *n, Port **out, int *cap);
void lin_reduce_wave_parallel(Net *n, Port *curr, int wave_cnt, int *changed);
void lin_enqueue(Net *n, Port a, Port b); /* push an active redex pair (plugin hook) */
void lin_fold_bump(void);  long lin_fold_total(void); /* driver native-fold accounting */
typedef int (*ScalarOpFn)(const char *fn, int argc, const long *args, long *out, int *outkind);
void lin_scalar_ops_add(ScalarOpFn f);
void lin_scalar_ops_load(const char *sym);
/* Hand `fn` to the registered providers (first that owns it supplies the result); 1 on success.  The
   registry is the core's because plugins register into it, so whoever dispatches, it stays here. */
int lin_scalar_ops_run(const char *fn, int argc, const long *args, long *out, int *outkind);
int lin_arith_scalar(const char *fn, int argc, const long *args, long *out, int *outkind);

/* ---------------- parser ---------------- */
typedef void (*FormFn)(Term *, const char *, void *);
void parse_forms(const char *src, FormFn fn, void *ud);
Term *term_new(int type, const char *name, Term *l, Term *r); Term *term_copy(Term *t);
void term_free(Term *t); int term_refs(Term *t, const char *name);
Term *term_fix(const char *name, Term *body);

/* ---------------- types ---------------- */
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
/* THE PASS POINT.  Offer every registered driver its AOT pass (LIN_WANT_AOT), in priority order, on
   the compilation of `t`.  Every pass is OPTIONAL (LIN_NO_PASS skips them all): a skipped one must
   leave a net that still runs correctly, and the interpreter path never runs one.  A build that ships
   its program UNREDUCED makes no offer at all: a pass's subject is the value a build EVALUATED, and
   such a build has none by the caller's own decision (src/main.c, the pass point). */
int lin_driver_aot(Net *n, const Term *t, const Scheme *sch);
/* The term -> port map the core hands a pass: {-1,0} for a term it did not compile itself. */
Port lin_node_of(void *ctx, const Term *t);
int net_save_line(Net *n, const char *path); int net_load_line(Net *n, const char *path);
void lin_set_self_path(const char *p); /* .line shebang = this absolute path */

/* ---------------- the ENCODING REGISTRY: domain -> the shape it is written in ----------------
   A driver's `domains` mask names MEANINGS (DT_*) because that is what a provider holds storage
   for; the shape behind each is the registry's business, and it is keyed by ENCODING, never by a
   carrier string: nothing about a node says which domain it belongs to (see LIN_ENC_* above). */
enum { DT_NUM, DT_BOOL, DT_STR, DT_FFI, DT_FLOAT, DT_OP, DT_MAX };
/* Register the builtin domains.  A `datatype` form registers its own (main.c): a user constructor
   gets no encoding of its own -- it is a pure-Lin term, and whoever reads it reads the term. */
void lin_domains_init(void);
/* The core's readers.  EVERY one takes the encoding it expects; none of them consults a node's
   label, so a raw net reads exactly as a compiled one does.  A value that is not in the expected
   encoding -- including one that is still an unreduced thunk -- is DECLINED, never guessed. */
long net_read_int(Net *n, Port p, int enc);          /* layers: a numeral's value, a list's length,
                                                        a BOOL's 1/0; -1 when `p` is not that encoding */
int  net_read_string(Net *n, Port p, int pay_enc, char *buf, size_t max); /* cell chain; pay_enc = the char-code encoding */
/* One cell of the language's cons encoding: `*head`/`*tail` when `p` is a cell, 0 otherwise.  The
   cell shape is the one every spine walk agrees on, so it is exported once (readback walks it to
   check a payload, a driver to read an operand list). */
int  net_read_cell(Net *n, Port p, Port *head, Port *tail);
int  net_read_float(Net *n, Port p, double *out);    /* the DT_FLOAT provider's table, via its index */
long net_run_io(Net *n, long limit);
/* Write the observed result.  `domain` is what the program's TYPE says the result means (a DT_*,
   or -1 when the type is unknown), so readback decodes with the meaning the compiler computed
   instead of guessing one off a node. */
int net_print(Net *n, int domain);
/* One value observed at `p`, which the caller states the DOMAIN of: a slot's expectation is what it
   MEANS (num / bool / float / string / closure), and the registry above says what shape that is.
   The decoder is the READBACK provider's (net_read_value); the reading primitives above are net
   structure and stay in the core. */
int net_read_value(Net *n, Port p, int domain, Val *v);
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
Port net_dup_hop(Net *n, Port p);                       /* deref it the way an arriving port implies */
int  net_ffi_fn(Net *n, Port p, char *fn, int fnmax);   /* fn name of a _ffi closure */
int  net_ffi_header(Net *n, Port lam, Port *fnp, Port *argp); /* dig \_ffi.\_ret.((_ffi fn) args) */
/* The operand list of a saturated closure.  `doms[i]` is the DOMAIN slot i is expected to be (the
   last entry repeats): the caller that knows what it is reading states it, and a slot that is not
   in that domain -- including one that is not concrete YET -- is left undecoded, which is how a
   fold tells "not ready" from "not my redex".  The CELL shape is the language's one cons encoding
   (LIN_ENC_CONS), so it is not a parameter: what varies is what the slots MEAN. */
int  net_ffi_args(Net *n, Port lam, const int *doms, int ndoms, Val *vals, int max);
int  net_spine_args(Net *n, Port argp, const int *doms, int ndoms, Val *vals, int max);
int  net_spine_slots(Net *n, Port argp); /* operand count of a cell-spine (-1: not a cons spine) */
/* !=0 while def_precompile reduces an open body: a driver must not fold there, since the operands are free vars
   that never become concrete and a baked closure would capture a stale value */
extern int lin_precompile_depth;
/* !=0 while the AOT build is partially evaluating: a driver must not bake anything the
   program would observe at RUN time (e.g. a (lin_folds) probe) into the artifact */
extern int lin_build_depth;
/* Raised by whoever declines to dispatch an FFI call whose value is not a function of its operands
   while a build marker is up (`lin_build_depth` / `lin_precompile_depth`): a build may not make the
   program's observations.  The build then ships the program UNREDUCED instead of partially
   evaluating it -- see aot_run.  Cleared before each build-time reduction. */
extern int lin_build_observed;
Port net_alloc_scott(Net *n, long k); Port net_alloc_bool(Net *n, int v);
Port net_alloc_float(Net *n, double d);
/* Float boxes are net structure like any other; the TABLE behind the index is a driver's
   (std/drivers/values.c, the DT_FLOAT provider), reached through net_box_value /
   net_unbox_value.  net_alloc_float / net_read_float below are thin calls into it. */

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
