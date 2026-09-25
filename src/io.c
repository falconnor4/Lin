#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>

/* ============================================================================
 * The core's value readers: net STRUCTURE in, a value out -- under an encoding the CALLER states.
 *
 * There is no per-node label to consult.  Scott zero (`\b0.\b1.b0`), Church TRUE and the empty list
 * are ONE net, so which value a node holds cannot be recovered from the node: the EXPECTATION is the
 * only source of meaning -- the type the compiler computed, a domain a driver declared, a slot's FFI
 * signature -- and a reader that has none must DECLINE (readback then prints the structure) rather
 * than guess.  The core keeps the encoding WALKS (below), the generic box builders, the one arg-spine
 * decoder and the thin dispatchers to whichever driver declares LIN_WANT_READBACK; what a value MEANS
 * beyond its shape -- the table behind a float box, FFI dispatch -- is never the core's.
 * ==========================================================================*/
static Net *N;
/* Where readback's VALUE is written.  Loading the prelude must still EVALUATE its top-level forms
   -- FFI dispatch happens in readback, so `(set_driver "arith")` in std/drivers/arith.lin only runs
   when the value is observed -- but it must not land in the program's own output, which a `; expect`
   line would then be one line off from.  The prelude therefore points this at a sink, and the READBACK
   driver (std/drivers/readback.c) is who writes into it. */
FILE *lin_out = NULL;

static inline int live(const Net *n, Port p) { return p.node >= 0 && p.node < n->nn && !n->dead[p.node]; }
static inline Port wr(const Net *n, Port p) { return n->wire[p.node * 3 + p.port]; }

void lin_domains_init(void) {
  /* The builtin scalar domains are also nominal TYPES, so that parse_type_atom resolves
     bool/num/float/list to distinct TNOM heads and the compiler can hand readback the expected
     domain of an observed result.  Nothing here is keyed by a carrier name any more. */
  nominal_register("bool", 0);
  nominal_register("num", 0);
  nominal_register("float", 0);
  nominal_register("list", 1);
}

/* ---------------- fan walks ---------------- */
/* Follow principal-to-principal through any chain of fans: `dup_hop` is the crossing walk (it reads
   whichever auxiliary the arriving port implies), `skip_dup` the plain one readback uses when a shared
   subterm stands for one value.  Both are bounded by the net's size, because a fan chain may be
   CYCLIC (two fans whose principals face each other are an un-contracted DUPxDUP redex) and an
   unguarded walk then spins with no step count advancing; on overflow they return the DUP port they
   stopped on, and callers check the tag they need, so it degrades to "not a value". */
static inline Port dup_hop(Net *n, Port p) {
  for (int step = 0; step < n->nn && live(n, p) && n->tag[p.node] == DUP; step++)
    p = p.port == 0 ? wr(n, (Port){p.node, 1}) : wr(n, (Port){p.node, 0});
  return p;
}
static inline Port skip_dup(Net *n, Port p) {
  for (int step = 0; step < n->nn && live(n, p) && n->tag[p.node] == DUP; step++)
    p = wr(n, (Port){p.node, 0});
  return p;
}
/* Deref a DUP (port 0) chain to the underlying wire; pure, no allocation. */
Port net_dhop(Net *n, Port p) { return skip_dup(n, p); }
/* The crossing fan walk, exported for the same reason: a driver reading a shared subterm must reach
   it exactly the way the core does, or it reads a fan instead of the value. */
Port net_dup_hop(Net *n, Port p) { N = n; return dup_hop(n, p); }

/* Force the value at `p` and return a port that still names it.
   Readback holds the VALUE end of a wire, and forcing fires the redex that end may itself name; β then
   consumes BOTH nodes of the pair and `p` dies with them, so every later read sees a discarded node
   and the value prints as `_`.  pair_boundary joins the pair's body port to the port its RESULT was
   wired to, so the value is one hop past the consumer's end -- which the rule never touches -- and
   that is where the port is re-aimed.  Without this, forcing during readback destroyed the thing it
   was forcing.  FORCING IS REDUCTION, which is why the primitive is the core's. */
Port net_force_val(Net *n, Port p) {
  for (int i = 0; i < 32; i++) {
    if (p.node < 0 || p.node >= n->nn) return p;
    Port s = wr(n, p);
    if (!n->dead[p.node]) net_force(n, p);
    if (!n->dead[p.node]) return p;
    if (s.node < 0 || s.node >= n->nn || n->dead[s.node]) return p;
    Port v = wr(n, s);
    if (v.node < 0 || v.node >= n->nn || n->dead[v.node]) return p;
    if (v.node == p.node && v.port == p.port) return p;
    p = v;
  }
  return p;
}

/* ---------------- the encoding walks ----------------
   Every layer is FORCED before it is read: under needed order a cell can still hold an unreduced
   thunk, and reading it is what demands it (readback is the consumer, so readback forces).  A layer
   that is not the expected encoding's -- or not a normal form yet -- DECLINES; nothing is guessed.
     NUM   `\b0.\b1.b0` ZERO     `\b0.\b1.(b1 tail)` successor        (BOOL: the same two, read as
     CONS  `\c.\n.<value>` NIL   `\h.\t.\c.\n.((c h) t)` cell           TRUE / FALSE; STR: the
                                                                        cell shapes with a payload)
*/
enum { L_TERMINAL, L_INDUCTIVE, L_FALSE };
typedef struct { int layer; Port head, tail; } Layer;

/* `\b0.\b1.b0` (first) / `\b0.\b1.b1` (second): the shape ZERO, TRUE and NIL share with FALSE. */
static int sel_layer(Net *n, Port p, int second) {
  p = dup_hop(n, net_force_val(n, p));
  if (!live(n, p) || n->tag[p.node] != LAM) return 0;
  Port w = dup_hop(n, net_force_val(n, wr(n, (Port){p.node, 2})));
  if (w.port != 0 || !live(n, w) || n->tag[w.node] != LAM) return 0;
  Port b = dup_hop(n, net_force_val(n, wr(n, (Port){w.node, 2})));
  if (b.node != (second ? w.node : p.node) || b.port != 1) return 0;
  return 1;
}

/* `\b0.\b1.(b1 tail)`: a successor layer.  The LAYER APPLIES ITS OWN SECOND BINDER, which is what
   makes this shape a numeral and not a cell (a cell applies an inner LAM). */
static int succ_layer(Net *n, Port p, Port *tail) {
  p = dup_hop(n, net_force_val(n, p));
  if (!live(n, p) || n->tag[p.node] != LAM) return 0;
  Port w = dup_hop(n, net_force_val(n, wr(n, (Port){p.node, 2})));
  if (w.port != 0 || !live(n, w) || n->tag[w.node] != LAM) return 0;
  Port body = dup_hop(n, net_force_val(n, wr(n, (Port){w.node, 2})));
  if (!live(n, body) || n->tag[body.node] != APP) return 0;
  Port fn = dup_hop(n, net_force_val(n, wr(n, (Port){body.node, 0})));
  if (fn.node != w.node || fn.port != 1) return 0;
  if (tail) *tail = wr(n, (Port){body.node, 2});
  return 1;
}

/* `\h.\t.\c.\n.((c h) t)`: one cell.  `\c.\n.<value>` / `\b0.\b1.b1`: the terminal (nil), which is
   the same test for num.lin's `_cl_nil` and list.lin's `\c.\n.true` nil. */
static int cell_layer(Net *n, Port p, Port *head, Port *tail) {
  /* THE PLAIN FAN WALK, not the crossing one: a SPINE reached through a fan stands for one value, and
     `dup_hop` (which reads whichever auxiliary the arriving port implies) is for the binder wiring a
     NUMERAL needs.  Measuring the difference: a shared closure `(let ((f (\x (add x 1)))) (add (f 1)
     (f 2)))` folded with the FIRST use's operand twice -- 4 where 5 is right. */
  p = skip_dup(n, net_force_val(n, p));
  if (!live(n, p) || n->tag[p.node] != LAM) return 0;
  Port c = skip_dup(n, net_force_val(n, wr(n, (Port){p.node, 2})));
  if (c.port != 0 || !live(n, c) || n->tag[c.node] != LAM) return 0;
  Port body = skip_dup(n, net_force_val(n, wr(n, (Port){c.node, 2})));
  if (!live(n, body) || n->tag[body.node] != APP) return 0;
  Port ia = skip_dup(n, net_force_val(n, wr(n, (Port){body.node, 0})));
  if (!live(n, ia) || n->tag[ia.node] != APP) return 0;
  if (head) *head = wr(n, (Port){ia.node, 2});
  if (tail) *tail = wr(n, (Port){body.node, 2});
  return 1;
}
int net_read_cell(Net *n, Port p, Port *head, Port *tail) { return cell_layer(n, p, head, tail); }
static int nil_layer(Net *n, Port p) {
  p = skip_dup(n, net_force_val(n, p));
  if (!live(n, p) || n->tag[p.node] != LAM) return 0;
  Port c = skip_dup(n, net_force_val(n, wr(n, (Port){p.node, 2})));
  if (c.port != 0 || !live(n, c) || n->tag[c.node] != LAM) return 0;
  Port body = skip_dup(n, net_force_val(n, wr(n, (Port){c.node, 2})));
  return live(n, body) && n->tag[body.node] == LAM;
}
static int cons_layer(Net *n, Port p, Layer *out) {
  Port h, t;
  if (cell_layer(n, p, &h, &t)) { out->layer = L_INDUCTIVE; out->head = h; out->tail = t; return 1; }
  if (nil_layer(n, p)) { out->layer = L_TERMINAL; out->head = out->tail = (Port){-1, 0}; return 1; }
  return 0;
}

/* One layer of the expected encoding at `p`.  0 = `p` is not that encoding's layer (or not a
   normal form yet). */
static int enc_layer(Net *n, Port p, int enc, Layer *out) {
  out->head = out->tail = (Port){-1, 0};
  switch (enc) {
  case LIN_ENC_NUM:
    if (sel_layer(n, p, 0)) { out->layer = L_TERMINAL; return 1; }
    if (succ_layer(n, p, &out->tail)) { out->layer = L_INDUCTIVE; return 1; }
    return 0;
  case LIN_ENC_BOOL:
    if (sel_layer(n, p, 0)) { out->layer = L_TERMINAL; return 1; }
    if (sel_layer(n, p, 1)) { out->layer = L_FALSE; return 1; }
    return 0;
  case LIN_ENC_CONS:
  case LIN_ENC_STR:
    return cons_layer(n, p, out);
  default:
    return 0;                       /* OP/FFI/EFF are headers, not layer chains: see below */
  }
}

/* How many INDUCTIVE layers from `p` down to the encoding's terminal: a numeral's value, a list's
   length, and for BOOL 1 (select-first, TRUE) or 0 (select-second).  -1 when `p` is not that encoding. */
long net_read_int(Net *n, Port p, int enc) {
  long count = 0;
  for (int step = 0; step < n->nn; step++) {
    Layer L;
    if (!enc_layer(n, p, enc, &L)) return -1;
    if (enc == LIN_ENC_BOOL) return L.layer == L_TERMINAL;
    if (L.layer != L_INDUCTIVE) return count;
    count++;
    p = L.tail;
  }
  return -1;
}

/* A cell chain whose PAYLOAD is in `pay_enc` -- a string is this with a numeral (char code) payload.
   The payload's encoding is an argument for the same reason every other one is: a list of lists is the
   same cell, so the cell alone does not say what is inside it. */
int net_read_string(Net *n, Port p, int pay_enc, char *buf, size_t max) {
  size_t len = 0;
  Port cur = p;
  for (int step = 0; step < n->nn && len + 1 < max; step++) {
    Layer L;
    if (!cons_layer(n, cur, &L)) break;
    if (L.layer != L_INDUCTIVE) { buf[len] = 0; return (int)len; }   /* the nil terminal */
    /* A payload must be a NUMBER the structure determines ON ITS OWN -- one layer or more.  A payload
       that is the bare terminal (`\b0.\b1.b0`) is also TRUE and nil, so reading it as a character
       would be a guess; and a payload that is itself a CELL is a 1-element list whose "cell" is an
       `_ffi` closure's header (the two ARE one net: `\c.\n.((c h) t)` and `\_ffi.\_ret.((_ffi fn)
       args)`), so it is not a string either.  Both are skipped, exactly as an unreadable payload
       always was. */
    long ch = net_read_int(n, L.head, pay_enc);
    if (ch > 0 && ch < 256) buf[len++] = (char)ch;
    cur = L.tail;
  }
  if (len > 0) { buf[len] = 0; return (int)len; }
  return -1;
}

/* Decoding a float box is entirely the provider's: the core hands it the port, because the box's shape
   is not what makes it a float -- the TABLE is. */
int net_read_float(Net *n, Port p, double *out) {
  N = n;
  Val v;
  memset(&v, 0, sizeof v);
  if (!net_unbox_value(n, DT_FLOAT, p, &v) || v.kind != 4) return 0;
  memcpy(out, &v.iv, 8);
  return 1;
}

/* ---------------- the encodings' builders (net structure, not policy) ---------------- */
static Port alloc_scott(Net *n, long k) {
  Scope sc = scope_nil(); Port cur = (Port){-1, 0};
  for (long i = 0; i <= k; i++) {
    Port sz = net_alloc(n, LAM, sc), ss = net_alloc(n, LAM, sc);
    net_link(n, (Port){sz.node, 2}, (Port){ss.node, 0}, 0);
    if (i == 0) net_link(n, (Port){ss.node, 2}, (Port){sz.node, 1}, 0);
    else {
      Port app = net_alloc(n, APP, sc);
      net_link(n, (Port){app.node, 0}, (Port){ss.node, 1}, 0);
      net_link(n, (Port){app.node, 2}, cur, 0);
      net_link(n, (Port){ss.node, 2}, (Port){app.node, 1}, 0);
    }
    cur = (Port){sz.node, 0};
  }
  return cur;
}
Port net_alloc_scott(Net *n, long k) { return alloc_scott(n, k); }

/* A BOXED INDEX: `\b0.\b1.(b0 (b1 i))` -- deliberately NOT the number encoding, which is what makes a
   box readable with no expectation at all (a numeral applies ONE binder per layer, a box BOTH). */
Port net_box_index(Net *n, long i) {
  Scope sc = scope_nil();
  Port a = net_alloc(n, LAM, sc), b = net_alloc(n, LAM, sc);
  Port ia = net_alloc(n, APP, sc), oa = net_alloc(n, APP, sc);
  Port idx = alloc_scott(n, i);
  net_link(n, (Port){a.node, 2}, (Port){b.node, 0}, 0);      /* a's body IS the second binder */
  net_link(n, (Port){b.node, 2}, (Port){oa.node, 1}, 0);     /* b's body is the outer application */
  net_link(n, (Port){oa.node, 0}, (Port){a.node, 1}, 0);     /* ... whose function is a's binder */
  net_link(n, (Port){oa.node, 2}, (Port){ia.node, 1}, 0);    /* ... applied to the inner one */
  net_link(n, (Port){ia.node, 0}, (Port){b.node, 1}, 0);
  net_link(n, (Port){ia.node, 2}, idx, 0);                   /* ... which is applied to the index */
  return (Port){a.node, 0};
}
static int box_layer(Net *n, Port p, Port *idx) {
  p = dup_hop(n, net_force_val(n, p));
  if (!live(n, p) || n->tag[p.node] != LAM) return 0;
  Port b = dup_hop(n, net_force_val(n, wr(n, (Port){p.node, 2})));
  if (b.port != 0 || !live(n, b) || n->tag[b.node] != LAM) return 0;
  Port oa = dup_hop(n, net_force_val(n, wr(n, (Port){b.node, 2})));
  if (oa.port != 1 || !live(n, oa) || n->tag[oa.node] != APP) return 0;
  Port f1 = dup_hop(n, net_force_val(n, wr(n, (Port){oa.node, 0})));
  if (f1.node != p.node || f1.port != 1) return 0;           /* the FIRST binder, applied */
  Port ia = dup_hop(n, net_force_val(n, wr(n, (Port){oa.node, 2})));
  if (ia.port != 1 || !live(n, ia) || n->tag[ia.node] != APP) return 0;
  Port f2 = dup_hop(n, net_force_val(n, wr(n, (Port){ia.node, 0})));
  if (f2.node != b.node || f2.port != 1) return 0;           /* the SECOND binder, applied */
  if (idx) *idx = wr(n, (Port){ia.node, 2});
  return 1;
}
long net_peel_index(Net *n, Port p) {
  Port idx;
  if (!box_layer(n, p, &idx)) return -1;
  return net_read_int(n, idx, LIN_ENC_NUM);
}

Port net_alloc_bool(Net *n, int val) {
  Scope sc = scope_nil(); Port bt = net_alloc(n, LAM, sc), bf = net_alloc(n, LAM, sc);
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);
  net_link(n, (Port){bf.node, 2}, (Port){val ? bt.node : bf.node, 1}, 0);
  return (Port){bt.node, 0};
}

/* A thin call into the DT_FLOAT provider.  A missing provider is a misconfiguration, reported once
   the way a missing scalar table is (`lin_scalar_ops_load`), not a silent wrong answer. */
Port net_alloc_float(Net *n, double d) {
  Val v;
  memset(&v, 0, sizeof v);
  v.kind = 4;
  memcpy(&v.iv, &d, 8);
  Port p = net_box_value(n, DT_FLOAT, &v);
  if (p.node < 0) {
    static int warned;
    if (!warned) {
      warned = 1;
      fprintf(stderr, "lin: no driver provides the float domain -- load std/drivers/values.lin "
                      "(`(set_driver \"values\")`)\n");
    }
  }
  return p;
}

/* ---------------- the closure headers ----------------
   Neither says its operator: an `_op`'s is the first slot of its operand list (an index into the
   language's vocabulary, std/num.lin) and an `_ffi` closure names its symbol in its argument list.
   See std/num.lin and pattern.h for the shapes a driver tells apart. */

/* dig the `_ffi`-closure header at LAM `lam` (shape \_ffi. \_ret. ((_ffi <fn>) <args>)) into `*a1` (fn APP) and `*argp` (arg-spine).
   PURE -- it reads wires and tags and never forces.  Forcing here would run the reducer from inside a
   reader, and a reader is reached FROM the reducer (a driver decoding an operand calls this through
   net_read_value): that re-entry lands on the same closure and repeats for ever.  A caller that needs
   a closure's body reduced says so itself, in a place where reduction is legal (`reduce`, `match`).
   Through `dup_hop`: a closure the reduction SHARED is reached through a fan, so its body wire leads
   to a DUP auxiliary whose principal is the body -- the copy and the original do not have separate
   bodies -- and reading it plainly would find the fan instead. */
int net_ffi_header(Net *n, Port lam, Port *a1, Port *argp) {
  Port r = dup_hop(n, wr(n, (Port){lam.node, 2}));
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM) return 0;
  Port a2 = dup_hop(n, wr(n, (Port){r.node, 2}));
  if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  Port fn = wr(n, (Port){a2.node, 0});                  /* the `<fn>` application */
  if (fn.port != 1 || n->tag[fn.node] != APP) return 0;
  /* THE WIRING THAT MAKES IT AN `_ffi` CLOSURE: the fn application applies THE CLOSURE'S OWN BINDER.
     Without this test every `\x.\y.((f y) x)`-shaped net -- std/ffi.lin's own `ffi` is one -- walks
     the same three wires and would be dispatched as a closure whose "argument list" is the closure
     itself: measured, an infinite regress (each dispatch re-enters the same node). */
  /* The occurrence must be bound by THIS closure's own binder, and a SHARED closure is reached
     through fans on BOTH sides of that binder: a copy's binder port leads to a fan whose crossing
     walk lands on the ORIGINAL occurrence, while that occurrence still names the original binder.
     So the two sides are compared where they RESOLVE, never by the node they are entered at.  That
     is also what keeps the `\x.\y.((f y) x)` regress out: there the closure's binder is the
     ARGUMENT of the body's application (port 2), not the function the fn application applies. */
  Port a = dup_hop(n, wr(n, (Port){lam.node, 1}));    /* this closure's own binder, fans resolved */
  Port b = dup_hop(n, wr(n, (Port){fn.node, 0}));     /* the binder the fn occurrence applies */
  if (a.node != fn.node || a.port != 0) return 0;
  if (!live(n, b) || b.port != 1 || n->tag[b.node] != LAM) return 0;
  if (a1) *a1 = fn;
  if (argp) *argp = wr(n, (Port){a2.node, 2});
  return 1;
}

/* Read the fn name of the `_ffi` closure rooted at port p (port 0): a string, so the payload of its
   cells is the number encoding (a char code). */
int net_ffi_fn(Net *n, Port p, char *fn, int fnmax) {
  Port a1;
  if (!net_ffi_header(n, p, &a1, 0)) return 0;
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return 0;
  return net_read_string(n, wr(n, (Port){a1.node, 2}), LIN_ENC_NUM, fn, (size_t)fnmax) > 0;
}

/* ---------------- the one arg-spine walk ----------------
   EXPORTED so driver plugins reuse it: the CELL is the language's one cons encoding, and the caller
   states what each slot MEANS (`doms`).  A slot that is not decodable is left undecoded, which is how
   a fold tells "an operand is not concrete YET" from "this is not my redex". */
static int spine_entry(Net *n, Port argp) {
  Layer L;
  return cons_layer(n, argp, &L);
}

/* Operand count of a cell-spine; -1 means it is not one, so only an empty list reads as concrete.
   The ONE authority on whether a spine is fully present: fewer decoded values than slots means an
   operand is not concrete YET, and a fold must be declined rather than guessed. */
int net_spine_slots(Net *n, Port argp) {
  Port cur = skip_dup(n, net_force_val(n, argp));
  if (!spine_entry(n, cur)) return -1;
  int slots = 0;
  for (int step = 0; step < n->nn; step++) {
    Layer L;
    if (!cons_layer(n, cur, &L)) break;
    if (L.layer != L_INDUCTIVE) break;
    slots++;
    cur = net_force_val(n, L.tail);
  }
  return slots;
}

/* Decode one slot into a Val.  `dom` is the EXPECTATION the caller states -- the signature of the
   symbol being called, a driver's own operand domain -- and it is tried first, because it is the only
   thing that can decide a shape TWO domains claim (`\b0.\b1.b0` is zero, TRUE and nil at once).
   Where the expectation does not hold, the slot's structure may still determine the value ON ITS OWN,
   and using it is not a guess: a box is not a numeral, a numbered chain is not a cell, and a cons
   chain of numbers is not either.  What is deliberately NOT here is a preference ORDER between
   domains -- that would be exactly the name-sniffing this design removed. */
static int dec_arg(Net *n, Port p, int dom, Val *v) {
  /* A NESTED CLOSURE comes first: what a slot's expectation is about is the VALUE, and a closure's
     value is what dispatching it produces -- `(fadd (float "2.5") (float "3.5"))` has closures where
     floats belong, and `(lin_parse_float (getenv "N"))` has one where a string belongs.  Dispatching
     is the readback provider's, and its own shape test is pure, so a slot that already IS a value
     pays only a walk of two wires. */
  if (net_read_value(n, p, DT_FFI, v) && v->kind) return 1;
  switch (dom) {
  case DT_NUM: {
    long x = net_read_int(n, p, LIN_ENC_NUM);
    if (x >= 0) { v->iv = x; v->kind = 1; return 1; }
    break;
  }
  case DT_BOOL: {
    long b = net_read_int(n, p, LIN_ENC_BOOL);
    if (b >= 0) { v->iv = b; v->kind = 3; return 1; }
    break;
  }
  case DT_STR:
    if (net_read_string(n, p, LIN_ENC_NUM, v->sv, sizeof v->sv) >= 0) { v->kind = 2; return 1; }
    break;
  case DT_FLOAT: {
    double d;
    if (net_read_float(n, p, &d)) { memcpy(&v->iv, &d, 8); v->kind = 4; return 1; }
    break;
  }
  case DT_FFI:
    if (net_read_value(n, p, DT_FFI, v)) return 1;
    break;
  default:
    break;                        /* an OP/EFF closure is not a scalar operand */
  }
  /* what the STRUCTURE determines by itself (see above) */
  double d;
  if (net_read_float(n, p, &d)) { memcpy(&v->iv, &d, 8); v->kind = 4; return 1; }
  long x = net_read_int(n, p, LIN_ENC_NUM);
  if (x > 0) { v->iv = x; v->kind = 1; return 1; }
  if (net_read_string(n, p, LIN_ENC_NUM, v->sv, sizeof v->sv) > 0) { v->kind = 2; return 1; }
  return 0;
}

/* Decode a spine's slots, each under `doms[i]` (the last entry repeats; a caller with a single
   expectation passes one).  Returns the number of slots decoded, which the caller compares against
   net_spine_slots: fewer means a PRESENT slot is not (yet) decodable -- a nested closure that has
   not folded, an operand that is still a thunk -- so the caller defers instead of folding garbage.
   A single non-spine argument is decoded too: an `_ffi` arg list of one element is sometimes passed
   unwrapped. */
int net_spine_args(Net *n, Port argp, const int *doms, int ndoms, Val *vals, int max) {
  int argc = 0;
  Port cur = skip_dup(n, net_force_val(n, argp));
  if (ndoms <= 0) return 0;
  if (!spine_entry(n, cur)) return dec_arg(n, argp, doms[0], &vals[0]) ? 1 : 0;
  for (int step = 0; step < n->nn && argc < max; step++) {
    Layer L;
    if (!cons_layer(n, cur, &L)) break;
    if (L.layer != L_INDUCTIVE) break;
    int dom = doms[step < ndoms ? step : ndoms - 1];
    if (dec_arg(n, L.head, dom, &vals[argc])) argc++;
    /* THE TAIL IS RE-READ FROM THE LIVE CELL: decoding a slot FORCES it, and a force can rebuild the
       very cell the walk is standing on (the list of a compiled closure is a chain of applications
       until something walks it).  Carrying the tail across the decode hands the next slot a port
       into structure that no longer exists -- measured: an `add` folded with its OPERATOR INDEX as
       an operand.  The core's own walker re-read it for the same reason. */
    Port h2, t2;
    if (!cell_layer(n, cur, &h2, &t2)) break;
    cur = t2;
  }
  return argc;
}

/* walk the arg list of the `_ffi` closure rooted at `lam` (same shape as net_ffi_fn) */
int net_ffi_args(Net *n, Port lam, const int *doms, int ndoms, Val *vals, int max) {
  Port argp;
  if (!net_ffi_header(n, lam, 0, &argp)) return 0;
  return net_spine_args(n, argp, doms, ndoms, vals, max);
}

/* One value observed at `p`, of the DOMAIN the caller states, by the READBACK provider: the ONE place
   the core's own decoders ask for an observation they cannot make themselves (the spine walk meets an
   `_ffi` closure as an operand).  The core keeps no FFI dispatch and no policy about what a value is. */
int net_read_value(Net *n, Port p, int domain, Val *v) {
  LinDriver *d = lin_driver_wanting(LIN_WANT_READBACK);
  return d ? d->read_value(n, lin_driver_state(n, d), p, domain, v) : 0;
}

/* dlopen a driver plugin by name (idempotent): how a self-describing artifact reaches whoever wrote
   it.  `<name>_driver` is the symbol every plugin exports, which makes a NAME-only section enough. */
int lin_driver_load(const char *name) {
  if (!name || !name[0]) return 0;
  char sym[NAME + 16], path[4096];
  snprintf(sym, sizeof sym, "lin_%s_driver", name);
  if (dlsym(RTLD_DEFAULT, sym)) return 1;               /* already loaded */
  const char *dir = getenv("LIN_STD_DIR");
  snprintf(path, sizeof path, "%s/drivers/%s.so", dir ? dir : "std", name);
  if (!dlopen(path, RTLD_NOW | RTLD_GLOBAL)) return 0;
  return dlsym(RTLD_DEFAULT, sym) != NULL;
}

/* The native scalar table is a REGISTRY the plugins write into (arith.so registers lin_arith_scalar at
   construction), so it is the core's however the dispatch is packaged.  Dispatch is *open*: the first
   provider that owns `fn` supplies it.  outkind 1=int, 3=bool, 4=float-bits. */
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

/* The native scalar ops the std's float and ffi modules reach for come from std/drivers/arith.so.  The
   core loads NO driver by default, so the first program that asks for one pulls the plugin in here. */
int lin_scalar_ops_run(const char *fn, int argc, const long *args, long *out, int *outkind) {
  if (n_scalar_ops == 0) lin_scalar_ops_load("arith");
  for (int s = 0; s < n_scalar_ops; s++) if (scalar_ops[s](fn, argc, args, out, outkind)) return 1;
  return 0;
}

/* ---------------- readback dispatch ----------------
   Printing, running effects and dispatching FFI OBSERVE a net rather than reduce it, so they live in a
   driver and the core keeps only these dispatchers (found by CAPABILITY: whoever declares
   LIN_WANT_READBACK supplies the hooks).  What the core DOES decide, because the type checker is here,
   is the DOMAIN of the observed result: `net_print` is handed the meaning the compiler computed. */
/* WHICH readback provider is a DEFAULT, not something the core knows: `LIN_READBACK` names it, so an
   embedder supplies its own, and a container names its own explicitly through its section (and wins,
   because a section carries the name the artifact was built with).  The core decides nothing about
   how a value is written; it only knows that SOME driver declares the capability. */
static const char *readback_name(void) {
  const char *n = getenv("LIN_READBACK");
  return (n && n[0]) ? n : "readback";
}

static LinDriver *readback_driver(void) {
  static LinDriver *found;
  if (found) return found;
  found = lin_driver_wanting(LIN_WANT_READBACK);
  if (found) return found;
  /* Bootstrap, exactly as the scalar table does (`lin_scalar_ops_load`): a `.line` artifact runs with
     NO prelude, so no `(set_driver ...)` form is ever evaluated, and its zero-length named section is
     what names the driver to load (net.c lin_driver_carry_read).  Without that, and without this, an
     artifact would reduce correctly and print nothing. */
  const char *want = readback_name();
  lin_driver_load(want);
  found = lin_driver_wanting(LIN_WANT_READBACK);
  if (!found) {
    static int warned;
    if (!warned++)
      fprintf(stderr, "lin: no readback driver: cannot print or run effects -- load "
                      "std/drivers/%s.lin (`(set_driver \"%s\")`), or point LIN_READBACK at "
                      "another provider\n", want, want);
  }
  return found;
}

int net_print(Net *n, int domain) {
  LinDriver *d = readback_driver();
  return d ? d->print(n, lin_driver_state(n, d), domain) : 0;
}

long net_run_io(Net *n, long limit) {
  LinDriver *d = readback_driver();
  return d ? d->run_io(n, lin_driver_state(n, d), limit) : 0;
}
