/* ============================================================================
 * Lin Standard Library: the shared STRUCTURAL PATTERN MATCHER
 * ============================================================================
 * A driver that optimizes structure has to RECOGNIZE structure first, and every
 * such driver otherwise hand-rolls the same walk: range-check a node index,
 * check it against `dead[]`, read a wire, check a tag, check a carrier name
 * through `ctor_tag`, follow a `_cl` operand spine, and -- the part that is
 * always wrong the first time -- bound its own recursion so a cyclic net cannot
 * spin it.  This header is that walk, once, as DATA instead of as code: a driver
 * writes patterns (static const arrays/structs, no string DSL, no parser) and
 * gets bounded, liveness-checked, cycle-safe traversal back.
 *
 * HEADER-ONLY ON PURPOSE.  A driver `#include "../runtime/pattern.h"` and the
 * matcher compiles into that plugin; there is no library to link and no build
 * rule to keep in sync, exactly like std/drivers/selftest.h.
 *
 *
 * WHAT THE MATCHER MAY AND MAY NOT DO
 * -----------------------------------
 * 1. IT IS PURE.  A match NEVER mutates the net and NEVER forces anything: no
 *    net_alloc, no net_link, no net_force, no net_interact.  Anything that needs
 *    a value or a weak head normal form must be forced by the CALLER and then
 *    re-matched.  That is legal in the match phase (a driver's `match` runs once
 *    per wave BEFORE any slice exists, so it may inspect and force) and illegal
 *    in a per-pair `claim`, where the wave snapshot and every slice are already
 *    built from the net being read.  Every reader below that would have to force
 *    therefore comes in two forms and says which is which: `lin_pat_num_nf`
 *    (structural, pure, the only one a pure context may use) and `lin_pat_num`
 *    (net_read_int, FORCING, i.e. reduction).  The two are not interchangeable:
 *    forcing inside a `claim` mutates the net out from under the wave.
 *
 * 2. TERMINATION, STRUCTURALLY.  Three mechanisms, no reliance on any single one:
 *      - an IN-PROGRESS SET of (node, pattern position) pairs.  Re-entering a
 *        pattern at a node already being matched up the current path is an
 *        infinite regress by construction, so it fails the match rather than
 *        recursing.  Siblings never collide (each pops before the next starts).
 *      - `P_CYCLE(i, sub)` NAMES A FIXPOINT: the first visit binds slot i and
 *        descends; arriving at the same node again with the same index succeeds
 *        immediately, WITHOUT descending.  That is how a cyclic net (a Y-knot, a
 *        lazy stream's own tail) is matched as a finite pattern instead of being
 *        unrolled forever.
 *      - a per-match BUDGET (steps).  Exhausting it is a clean DECLINE: the match
 *        returns 0 and the caller must treat it as "no match", never as a partial
 *        one.  A match that returns 1 is complete; bindings, slots and the covered
 *        set are only meaningful then.
 *
 * 3. BOUNDS AND LIVENESS.  Every node index taken from the net is range-checked
 *    AND checked against `dead[]` before it is dereferenced (the core's own
 *    convention, see NAT_IN in src/net.c), and so is every node reached through a
 *    wire.  A pattern that walks off the net -- a dead node, a NONE wire, an index
 *    past `nn` -- declines.  The walk itself is bounded by the net's size, exactly
 *    as the core's own spine walkers are.
 *
 * 4. NO FAN HOPPING BY DEFAULT.  A port is read as it is wired: a structural view
 *    is what an optimality-aware rewrite needs, because "this thunk is used twice"
 *    is invisible through a hop.  `P_FAN(sub)` is how a pattern says, explicitly,
 *    "follow the DUP chain here and match `sub` on the other side" -- a
 *    value-level view.
 *
 *
 * THE VOCABULARY
 * --------------
 *   P_ANY                 any LIVE node (this is what bounds the match: -1/out of
 *                         range/dead is not a node).
 *   P_TAG(t)              node tag equals t (LAM|APP|DUP|ERA|ROOT).
 *   P_OP_HEAD             the port is the head of a saturated `_op` redex, recognized by
 *                         the marker std/num.lin writes on it (see lin_pat_op_head).
 *                         NO PATTERN READS A NAME: a net has none, and WHICH operator an
 *                         `_op` head is lives in the OPERAND LIST (see LIN_OP_* below),
 *                         never on a node.
 *   P_AT(port, sub)       the current position ARRIVED at port `port` (0 is the
 *                         principal port), and `sub` matches here.
 *   P_PORT(port, sub)     the wire at `port` OF THE CURRENT NODE must lead to a
 *                         node matching `sub`.  The sub-pattern sees the wire's
 *                         own port, so `P_AT(0, ...)` after it constrains the
 *                         ARRIVING port -- which is how principal-to-principal
 *                         wiring ("a redex") is stated.
 *   P_SPINE(sub)          a `_cl` operand spine of unknown length, every slot
 *                         matching `sub`.  Binds the slot count and the slot ports.
 *   P_SPINE_MIN(n, sub)   ... with at least n slots.
 *   P_SPINE_N(n, sub)     ... with exactly n slots.
 *   P_SPINE_HEAD(sub, tail)  the cons half: the FIRST slot must match `sub` and the
 *                         rest of the list (at the cell's tail port) must match
 *                         `tail` -- another P_SPINE_HEAD, or P_SPINE_N(0, ...) for
 *                         the end.  P_SPINE applies ONE pattern to every slot, so a
 *                         list of unlike requirements (slot 0 bound and slot 1
 *                         required to be the same node, say) is spelled with this.
 *   P_BIND(i)             bind the current Port (node AND port) to slot i.
 *   P_REF(i)              the SAME NODE as slot i -- how a pattern states sharing.
 *                         Node identity, not port equality, which is the point:
 *                         one value used twice is reached at two different ports
 *                         of the same node (a fan's two outputs).
 *   P_NOT(sub)            negative constraint: `sub` must NOT match here.  Nothing
 *                         it binds or covers escapes -- its whole effect is rolled
 *                         back, whether it succeeded or failed.
 *   P_FAN(sub)            follow the DUP chain (net_dhop) and match `sub` there.
 *   P_CYCLE(i, sub)       name the fixpoint at slot i and match `sub` here; a
 *                         repeat visit at the same node succeeds as the back edge.
 *   P_CYCLE_REF(i)        the fixpoint named i must be here (no descent).
 *   P_PRED(fn, ctx)       an arbitrary PURE C predicate over (Net*, Port, void*).
 *   P_ALL(a, b)           conjunction at one position, and P_ALL3(a, b, c) for three
 *                         (the AND is associative, so nesting them is "and" as well).
 *
 * A pattern is DATA: every macro below evaluates to a `const LinPat *` naming a
 * compound literal, so patterns nest as values and are read as one expression.
 * A pattern must outlive the match: declare it at file scope, or as a local in
 * the function that matches with it (never return one).
 *
 * EXAMPLE -- an `_op` redex whose operand list holds exactly two operands.
 * The root is the APP's principal port; slot 0 is the operator LAM, slot 1 is the
 * APP, slots[0..1] are the two operands:
 *
 *   static const LinPat *const OP_REDEX_2 =
 *     P_AT(0, P_ALL(
 *       P_BIND(1),                               // slot 1: the APP (the root)
 *       P_ALL(P_TAG(APP),
 *         P_ALL(P_PORT(0, P_AT(0, P_ALL(
 *                P_BIND(0),                      // slot 0: the operator LAM
 *                P_ALL(P_TAG(LAM), P_ALL(P_OP_HEAD,
 *                  P_PORT(0, P_AT(0, P_REF(1)))))))),   // wired back: a redex
 *               P_PORT(2, P_SPINE_N(3, P_ANY))))));      // ... and code + its two operands
 *
 * Reading it: the root arrives at port 0 (a principal) and is an APP (slot 1); its
 * port-0 wire arrives at the principal port of a LAM (slot 0) that is an `_op` HEAD
 * and whose port-0 wire leads back to slot 1 -- the mutual principal wiring that
 * makes the pair a redex; and its port-2 wire is a cons spine of at least three
 * slots (the operator INDEX and its operands), each of them any live node.  A driver
 * then reads m.bind[0].node, m.bind[1].node and m.slots[0..m.nslots).
 *
 *
 * THE CLAIM BRIDGE
 * ----------------
 * A match records the nodes it matched positively (its COVERED set; nodes reached
 * only inside P_NOT are excluded, and P_ANY contributes the node it accepted).
 * From that set two things follow mechanically, and both are what the claim
 * protocol wants:
 *   - the REDEXES it consumed: every mutually-wired principal pair INSIDE the
 *     covered set is a redex the match owns (that is the definition of a redex,
 *     not a guess);
 *   - the REGION'S EXITS: the auxiliary ports of covered nodes whose wire leaves
 *     the covered set.  An exit may only be auxiliary -- a redex is two mutually
 *     wired principals, so such a boundary cannot be crossed.
 * `lin_pat_claim` fills a LinClaim from the match, so a driver does
 * `match -> lin_pat_claim -> lin_claim_check` and never hand-builds a claim.
 * Coverage is capped (LIN_PAT_NODES); on overflow the match still succeeds but
 * lin_pat_claim refuses, because a truncated region is not a region.
 *
 *
 * THE CACHE
 * ---------
 * `LinPatCache` is the reuse half of a driver's per-net state: a small
 * direct-mapped table keyed by NODE INDEX, holding whatever a driver derived about a
 * node (a decode, a shape id, a value).  It is a cache of a DERIVATION of the net,
 * NEVER the authority: the net is.  An entry is invalid the moment
 *   - the slot is recycled -- node indices are handed out again, so a stale entry
 *     names a DIFFERENT node.  Only the core knows when that happens, which is
 *     exactly what the `node_recycled` hook is for: call lin_pat_cache_drop there;
 *   - the driver stops holding the region it derived the entry inside (a released
 *     claim, a rewritten slice, a compacted net): call lin_pat_cache_invalidate,
 *     which invalidates every entry at once by bumping an epoch.
 * A driver that cannot observe those events must clear the cache instead of
 * trusting it.  Reading a stale entry is a wrong answer, not a slow one.
 * ========================================================================== */
#ifndef LIN_PATTERN_H
#define LIN_PATTERN_H

/* A driver normally includes ../../src/lin.h itself (that is where LinDriver,
   Net, Port and the core primitives are); the guard keeps this header usable on
   its own without including it twice under two different relative paths. */
#ifndef LIN_H
#include "../../src/lin.h"
#endif
#include <string.h>

/* ---------------------------------------------------------------------------
 * limits: fixed sizes keep the matcher allocation-free, so it is usable from a
 * driver hook where the net cannot grow (a realloc would move the arrays a
 * concurrent worker holds pointers into).
 * ------------------------------------------------------------------------- */
#define LIN_PAT_SLOTS   8     /* spine slot ports recorded per match          */
#define LIN_PAT_BINDS   8     /* P_BIND / P_REF slots                         */
#define LIN_PAT_CYCLES  4     /* P_CYCLE fixpoints                            */
#define LIN_PAT_NODES  64     /* covered nodes (for lin_pat_claim)            */
#define LIN_PAT_DEPTH  48     /* pattern recursion depth (independent of budget) */

/* The budget to hand a match over this net.  A match's work is bounded by the
   net it walks (every step descends to a node or is stopped by one), so a
   generous constant factor of the net's size cannot decline a match the net
   could support -- while still being a bound the caller owns and can tighten. */
#define LIN_PAT_BUDGET_FOR(n) (256L + 16L * (long)((n) ? (n)->nn : 0))

/* ---------------------------------------------------------------------------
 * the pattern itself
 * ------------------------------------------------------------------------- */
typedef struct LinPat LinPat;
typedef int (*LinPatPred)(const Net *n, Port p, void *ctx);

enum {
  LIN_P_ANY, LIN_P_TAG, LIN_P_AT, LIN_P_PORT,
  LIN_P_SPINE, LIN_P_SPINE_HEAD, LIN_P_BIND, LIN_P_REF, LIN_P_NOT, LIN_P_FAN,
  LIN_P_CYCLE, LIN_P_CYCLE_REF, LIN_P_PRED, LIN_P_ALL
};

struct LinPat {
  unsigned char kind;
  unsigned char port;      /* LIN_P_AT / LIN_P_PORT: the port number            */
  short idx;               /* LIN_P_BIND / LIN_P_REF / LIN_P_CYCLE*: the slot   */
  int arg;                 /* LIN_P_TAG: the tag                                 */
  int min, max;            /* LIN_P_SPINE: slot-count bounds (max < 0 = any)    */
  LinPatPred pred;         /* LIN_P_PRED                                        */
  void *ctx;
  const LinPat *a, *b;     /* sub-pattern(s)                                    */
};

#define P_ANY          (&(const LinPat){ .kind = LIN_P_ANY })
#define P_TAG(t)       (&(const LinPat){ .kind = LIN_P_TAG, .arg = (t) })
#define P_AT(pt, s)    (&(const LinPat){ .kind = LIN_P_AT, .port = (pt), .a = (s) })
#define P_PORT(pt, s)  (&(const LinPat){ .kind = LIN_P_PORT, .port = (pt), .a = (s) })
#define P_SPINE(s)     (&(const LinPat){ .kind = LIN_P_SPINE, .min = 0, .max = -1, .a = (s) })
#define P_SPINE_MIN(n, s) (&(const LinPat){ .kind = LIN_P_SPINE, .min = (n), .max = -1, .a = (s) })
#define P_SPINE_N(n, s)   (&(const LinPat){ .kind = LIN_P_SPINE, .min = (n), .max = (n), .a = (s) })
#define P_SPINE_HEAD(sub, tail) (&(const LinPat){ .kind = LIN_P_SPINE_HEAD, .a = (sub), .b = (tail) })
#define P_BIND(i)      (&(const LinPat){ .kind = LIN_P_BIND, .idx = (i) })
#define P_REF(i)       (&(const LinPat){ .kind = LIN_P_REF, .idx = (i) })
#define P_NOT(s)       (&(const LinPat){ .kind = LIN_P_NOT, .a = (s) })
#define P_FAN(s)       (&(const LinPat){ .kind = LIN_P_FAN, .a = (s) })
#define P_CYCLE(i, s)  (&(const LinPat){ .kind = LIN_P_CYCLE, .idx = (i), .a = (s) })
#define P_CYCLE_REF(i) (&(const LinPat){ .kind = LIN_P_CYCLE_REF, .idx = (i) })
#define P_PRED(f, c)   (&(const LinPat){ .kind = LIN_P_PRED, .pred = (f), .ctx = (c) })
#define P_ALL(x, y)    (&(const LinPat){ .kind = LIN_P_ALL, .a = (x), .b = (y) })
#define P_ALL3(x, y, z) P_ALL(x, P_ALL(y, z))

/* ---------------------------------------------------------------------------
 * the result
 * ------------------------------------------------------------------------- */
typedef struct {
  const Net *n;
  Port root;               /* the port the match started at                    */
  int  ok;
  long used;               /* steps this attempt consumed; meaningful either way, so a
                              caller can see how far a DECLINED match walked */
  int  nslots;             /* slots every spine in the pattern contributed      */
  Port slots[LIN_PAT_SLOTS];      /* ... their ports, in match order (capped)   */
  int  nbind, bind_set;           /* nbind = highest slot + 1; bind_set a mask  */
  Port bind[LIN_PAT_BINDS];
  int  ncyc, cyc_set;
  Port cyc[LIN_PAT_CYCLES];
  int  nnodes, overflow;          /* the covered set (overflow: it did not fit) */
  int  nodes[LIN_PAT_NODES];
  /* internal: the budget and the in-progress set that make recursion terminate. */
  long budget;
  int  nin;
  const LinPat *ipat[LIN_PAT_DEPTH];
  Port ipport[LIN_PAT_DEPTH];
} LinMatch;

/* ---------------------------------------------------------------------------
 * helpers a pattern predicate uses (the core's own conventions)
 * ------------------------------------------------------------------------- */
static inline int lin_pat_live(const Net *n, int i) {
  return i >= 0 && i < n->nn && !n->dead[i];
}
static inline void lin_pat_cover(LinMatch *m, int node) {
  if (!lin_pat_live(m->n, node)) return;
  for (int i = 0; i < m->nnodes; i++) if (m->nodes[i] == node) return;
  if (m->nnodes >= LIN_PAT_NODES) { m->overflow = 1; return; }
  m->nodes[m->nnodes++] = node;
}
static inline int lin_pat_covered(const LinMatch *m, int node) {
  for (int i = 0; i < m->nnodes; i++) if (m->nodes[i] == node) return 1;
  return 0;
}
static inline int lin_pat_bound(const LinMatch *m, int i) {
  return i >= 0 && i < LIN_PAT_BINDS && (m->bind_set >> i) & 1;
}
static inline Port lin_pat_bind(const LinMatch *m, int i, Port dflt) {
  return lin_pat_bound(m, i) ? m->bind[i] : dflt;
}
static inline int lin_pat_bind_slot(LinMatch *m, int i, Port p) {
  if (i < 0 || i >= LIN_PAT_BINDS) return 0;
  if ((m->bind_set >> i) & 1) return 0;      /* already bound: say P_REF, not bind again */
  m->bind[i] = p;
  m->bind_set |= 1 << i;
  if (i + 1 > m->nbind) m->nbind = i + 1;
  return 1;
}

/* ---------------------------------------------------------------------------
 * the matcher
 * ------------------------------------------------------------------------- */
static inline int lin_pat_at(LinMatch *m, Port p, const LinPat *pat);

/* One `_cl` cell: `\c. \n. ((c h) t)` (std/num.lin's `_cl_cons`).  On success `*slot` is the
   port the head h is observed at, `*next` is the tail t, and 1 is returned; 0 means `p` is not
   a well-formed cell.  This is the cell shape the CORE's own walkers read (net_spine_slots,
   decode_spine), so a driver's read and the interpreter's read cannot drift, and everything
   reached on the way is part of the match's covered region. */
static inline int lin_pat_cell(LinMatch *m, Port p, Port *slot, Port *next) {
  const Net *n = m->n;
  Port cur, c2, body, ia;
  if (m->budget <= 0) return 0;
  m->budget--; m->used++;
  cur = net_dhop((Net *)n, p);
  if (!lin_pat_live(n, cur.node) || n->tag[cur.node] != LAM) return 0;
  c2 = net_dhop((Net *)n, net_wire(n, (Port){cur.node, 2}));
  if (c2.port != 0 || !lin_pat_live(n, c2.node) || n->tag[c2.node] != LAM) return 0;
  body = net_dhop((Net *)n, net_wire(n, (Port){c2.node, 2}));
  if (!lin_pat_live(n, body.node) || n->tag[body.node] != APP) return 0;
  ia = net_dhop((Net *)n, net_wire(n, (Port){body.node, 0}));
  if (!lin_pat_live(n, ia.node) || n->tag[ia.node] != APP) return 0;
  lin_pat_cover(m, cur.node); lin_pat_cover(m, c2.node);
  lin_pat_cover(m, body.node); lin_pat_cover(m, ia.node);
  *slot = net_wire(n, (Port){ia.node, 2});
  *next = net_wire(n, (Port){body.node, 2});
  return 1;
}

/* PURE: the nil terminal of the cons encoding (`\c.\n.<value>`), which is also the shape of a
   zero-erased numeral layer and of the select-second `_cl_nil`.  NO FORCING (a spine that is still a
   thunk is not a spine yet, and the matcher's contract is that a match may not reduce). */
static inline int lin_pat_nil_at(const Net *n, Port p) {
  Port c = net_dhop((Net *)n, p), q, b;
  if (!lin_pat_live(n, c.node) || n->tag[c.node] != LAM) return 0;
  q = net_dhop((Net *)n, net_wire(n, (Port){c.node, 2}));
  if (q.port != 0 || !lin_pat_live(n, q.node) || n->tag[q.node] != LAM) return 0;
  b = net_dhop((Net *)n, net_wire(n, (Port){q.node, 2}));
  return lin_pat_live(n, b.node) && n->tag[b.node] == LAM;
}

/* PURE: the first cell of a spine, for a caller that only wants what is AT it (the operator index
   at slot 0 and the operand list after it).  No forcing: a spine that is still a thunk is not one. */
static inline int lin_pat_cell_at(const Net *n, Port p, Port *head, Port *tail) {
  LinMatch m;
  memset(&m, 0, sizeof m);
  m.n = n;
  m.budget = LIN_PAT_BUDGET_FOR(n);
  return lin_pat_cell(&m, p, head, tail);
}

/* The spine: the cons-cell operand list the core's own walkers read.  The ENTRY must be a cell or
   the nil -- the structure, which is all a net with no labels offers -- and the cells after it are
   checked the same way; the walk ENDS where the cell chain stops, so the count this binds is the
   well-formed prefix.  Every slot must match `sub`: a slot that does not is a FAILED match, not the
   end of the list.  Nothing here forces -- an operand list that is still a thunk is not a spine yet
   and the match declines (force it first, then re-match). */
static inline int lin_pat_spine(LinMatch *m, Port p, const LinPat *pat) {
  const Net *n = m->n;
  Port cur = net_dhop((Net *)n, p), next = p;
  int k = 0;
  /* PURELY: the entry must be a cell or the nil.  Reading it with a FORCING reader here would run the
     reducer from inside a matcher -- and the reducer consults drivers, whose match hooks call this --
     which is an unbounded regress (measured: a match driver segfaulted on its own stack). */
  { Port eh, et;
    if (!lin_pat_cell_at(n, cur, &eh, &et) && !lin_pat_nil_at(n, cur)) return 0; }
  lin_pat_cover(m, cur.node);
  for (int step = 0; step < n->nn; step++) {
    if (m->budget <= 0) return 0;            /* out of budget: decline, never truncate */
    Port slot;
    if (!lin_pat_cell(m, next, &slot, &next)) break;
    if (!lin_pat_at(m, slot, pat->a)) return 0;
    if (m->nslots < LIN_PAT_SLOTS) m->slots[m->nslots] = slot;
    m->nslots++;
    k++;
  }
  if (k < pat->min) return 0;
  if (pat->max >= 0 && k > pat->max) return 0;
  return 1;
}

/* The cons half of a spine: the first slot must match `sub` and the REST of the list, at the
   cell's tail port, must match `tail`.  It is pure cell structure -- the `_cl` carrier is
   P_SPINE's business -- so it nests under a P_SPINE and spells a list of UNLIKE requirements. */
static inline int lin_pat_spine_head(LinMatch *m, Port p, const LinPat *pat) {
  Port slot, next;
  if (!lin_pat_cell(m, p, &slot, &next)) return 0;
  if (!lin_pat_at(m, slot, pat->a)) return 0;
  if (m->nslots < LIN_PAT_SLOTS) m->slots[m->nslots] = slot;
  m->nslots++;
  return lin_pat_at(m, next, pat->b);
}

static inline int lin_pat_at_in(LinMatch *m, Port p, const LinPat *pat) {
  const Net *n = m->n;
  switch (pat->kind) {
  case LIN_P_ANY:
    if (!lin_pat_live(n, p.node)) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  case LIN_P_TAG:
    if (!lin_pat_live(n, p.node) || n->tag[p.node] != pat->arg) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  case LIN_P_PRED:
    if (!lin_pat_live(n, p.node)) return 0;
    if (!pat->pred || !pat->pred(n, p, pat->ctx)) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  case LIN_P_AT:
    return p.port == (unsigned)pat->port && lin_pat_at(m, p, pat->a);
  case LIN_P_PORT:
    if (!lin_pat_live(n, p.node)) return 0;
    if (pat->port > 2) return 0;
    lin_pat_cover(m, p.node);
    return lin_pat_at(m, net_wire(n, (Port){p.node, pat->port}), pat->a);
  case LIN_P_FAN:
    return lin_pat_at(m, net_dhop((Net *)n, p), pat->a);
  case LIN_P_ALL:
    return lin_pat_at(m, p, pat->a) && lin_pat_at(m, p, pat->b);
  case LIN_P_BIND:
    if (!lin_pat_live(n, p.node)) return 0;
    if (!lin_pat_bind_slot(m, pat->idx, p)) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  case LIN_P_REF:
    if (!lin_pat_live(n, p.node)) return 0;
    if (!lin_pat_bound(m, pat->idx) || m->bind[pat->idx].node != p.node) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  case LIN_P_NOT: {
    /* A negative constraint observes, it does not own: nothing it bound, counted
       or covered survives -- whether it succeeded or failed.  The budget it spent
       is NOT returned: the work happened. */
    int bs = m->bind_set, cs = m->cyc_set, nn = m->nnodes, ns = m->nslots;
    int r = lin_pat_at(m, p, pat->a);
    m->bind_set = bs; m->cyc_set = cs; m->nnodes = nn; m->nslots = ns;
    return !r;
  }
  case LIN_P_CYCLE: {
    int i = pat->idx;
    if (i < 0 || i >= LIN_PAT_CYCLES || !lin_pat_live(n, p.node)) return 0;
    if ((m->cyc_set >> i) & 1) {
      if (m->cyc[i].node != p.node) return 0;   /* the fixpoint is a different node */
      lin_pat_cover(m, p.node);
      return 1;                                 /* the back edge: succeed, do not descend */
    }
    m->cyc[i] = p;
    m->cyc_set |= 1 << i;
    if (i + 1 > m->ncyc) m->ncyc = i + 1;
    lin_pat_cover(m, p.node);
    return lin_pat_at(m, p, pat->a);
  }
  case LIN_P_CYCLE_REF: {
    int i = pat->idx;
    if (i < 0 || i >= LIN_PAT_CYCLES || !lin_pat_live(n, p.node)) return 0;
    if (!((m->cyc_set >> i) & 1) || m->cyc[i].node != p.node) return 0;
    lin_pat_cover(m, p.node);
    return 1;
  }
  case LIN_P_SPINE:
    return lin_pat_spine(m, p, pat);
  case LIN_P_SPINE_HEAD:
    return lin_pat_spine_head(m, p, pat);
  default:
    return 0;
  }
}

static inline int lin_pat_at(LinMatch *m, Port p, const LinPat *pat) {
  if (!pat || m->budget <= 0) return 0;
  m->budget--; m->used++;
  /* the in-progress set: (node, pattern position) again on this path can only be
     an infinite regress, so it fails instead of recursing forever. */
  for (int i = 0; i < m->nin; i++)
    if (m->ipat[i] == pat && m->ipport[i].node == p.node) return 0;
  if (m->nin >= LIN_PAT_DEPTH) return 0;
  m->ipat[m->nin] = pat;
  m->ipport[m->nin] = p;
  m->nin++;
  int r = lin_pat_at_in(m, p, pat);
  m->nin--;
  return r;
}

/* Match `pat` with the root at `root`.  1 = matched (m holds the bindings, the slots
   and the covered set), 0 = declined, in which case nothing in m may be read as a
   result.  `budget` bounds the work: see LIN_PAT_BUDGET_FOR. */
static inline int lin_pat_match(Net *n, Port root, const LinPat *pat, long budget, LinMatch *m) {
  memset(m, 0, sizeof *m);
  m->n = n;
  m->root = root;
  m->budget = budget > 0 ? budget : 0;
  m->bind_set = 0; m->cyc_set = 0;
  if (!n || !pat || m->budget <= 0) return 0;
  if (!lin_pat_at(m, root, pat)) return 0;
  m->ok = 1;
  return 1;
}

/* The same, over an unordered candidate pair: a wave offers redexes as two ports
   whose order is not the pattern's business, so the first that matches wins. */
static inline int lin_pat_match_pair(Net *n, Port p1, Port p2, const LinPat *pat,
                                     long budget, LinMatch *m) {
  return lin_pat_match(n, p1, pat, budget, m) || lin_pat_match(n, p2, pat, budget, m);
}

/* ---------------------------------------------------------------------------
 * the two numeral readers -- and the difference that matters
 * ------------------------------------------------------------------------- */

/* STRUCTURAL, PURE: peel a numeral that is already a normal form, without forcing, under the
   encoding the caller expects (LIN_ENC_NUM for a number; the enc-based readers further down are the
   general form, and this is the name a driver has always used for the common case).  A layer whose
   argument is still a thunk (an unreduced application) makes the next layer's test fail, so a
   partially reduced numeral DECLINES instead of being demanded: this is the only reader a pure
   context (a `claim`, a per-pair predicate) may use. */
static inline int lin_pat_num_nf(const Net *n, Port p, long *out);

/* FORCING: the same value, every layer demanded and reduced first.  The reader a caller uses when
   it needs the value and is allowed to reduce (the match phase, readback). */
static inline long lin_pat_num(Net *n, Port p) {
  return n ? net_read_int(n, p, LIN_ENC_NUM) : -1;
}

/* ---------------------------------------------------------------------------
 * STRUCTURAL RECOGNISERS: the runtime's encodings read off STRUCTURE
 * ---------------------------------------------------------------------------
 * The readers above recognise a numeral through the datatype REGISTRY, which is
 * keyed by the carrier NAMES the compiler stamps on nodes ("_sz"/"_ss").  A RAW
 * net -- tags and wiring only, no names -- has none of that, so the encodings the
 * runtime uses have to be recognisable from STRUCTURE instead.  These are those
 * recognisers.
 *
 * WHY EVERY RECOGNISER TAKES THE EXPECTED ENCODING AS AN ARGUMENT
 * --------------------------------------------------------------
 * It cannot be sniffed off the node.  These two nets are structurally IDENTICAL up
 * to alpha-equivalence, differing ONLY in the carrier names:
 *
 *   Scott zero   alloc_scott_named(n, 0, "_sz", "_ss")           (src/io.c:22)
 *                LAM a with wire(a,2) = {b,0}, LAM b with wire(b,2) = {a,1}
 *   Church true  net_alloc_bool(n, 1)                            (src/io.c:60)
 *                the SAME wire pattern, carriers "_bt"/"_bf"
 *
 * so no structural test can tell a numeral from a selector -- and the same holds
 * for `_cl_nil` ("_cl"/"_nl", also select-second) and Church FALSE, which is one
 * pattern again; and `parse.c`'s numeral literal compiles to the very same wires.
 * A recogniser that "worked out" the encoding from the node would have to read a
 * name, which is exactly what a raw net does not have.  Therefore the EXPECTATION
 * is the CALLER's (or the value's TYPE, where the registry names the carriers):
 * these take an explicit `enc`, and the net is only asked whether its STRUCTURE is
 * the one that encoding prescribes.  A driver that does not know the encoding of
 * the value it is looking at has nothing to recognise and must not guess.
 *
 * THE ENCODINGS (each is a pair of carriers, or a header shape, in CORE net
 * structure; src/io.c's registry and builders are the authority on what they are):
 *   LIN_ENC_NUM   Scott numeral: zero / successor      (alloc_scott_named)
 *   LIN_ENC_BOOL  Church boolean: select-first/second  (net_alloc_bool)
 *   LIN_ENC_CONS  the `_cl` cons cell and nil          (std/num.lin's _cl_cons)
 *   LIN_ENC_STR   a cons cell whose payload is a numeral (a char code), and nil
 *   LIN_ENC_OP    the saturated `_op` header: LAM|APP mutual principals + operands
 *   LIN_ENC_FFI   the `_ffi` closure header \_ffi.\_ret.((_ffi <fn>) <args>)
 *
 * NON-FORCING AND FORCING, next to `lin_pat_num_nf` / `lin_pat_num` above: the
 * `_nf` forms are PURE (they never force, so a value that is not yet a normal form
 * DECLINES instead of being demanded -- the only kind usable from a `claim`), and
 * the forms without `_nf` force each layer first, i.e. they REDUCE.  None of them
 * reads a name either.
 * ------------------------------------------------------------------------- */

/* which layer of an encoding a shape is: the terminal (zero / true / nil), an
   inductive layer (a successor layer / a cons cell), or the second selector
   (false).  NUM and CONS/STR have terminal + inductive; BOOL has two terminals. */
#define LIN_L_TERMINAL  0
#define LIN_L_INDUCTIVE 1
#define LIN_L_FALSE     2

/* `\b0.\b1.b0` -- SELECT-FIRST: the Scott numeral ZERO, the Church boolean TRUE
   and the `_cl` NIL cell.  ONE pattern for all three, because they ARE one net
   (see the header note): which of them the caller is looking at is the `enc` it
   passes, never something this pattern could tell.  bind0 = the outer LAM,
   bind1 = the second LAM. */
static const LinPat *const lin_pat_enc_first = P_FAN(P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_PORT(2, P_FAN(P_ALL3(P_BIND(1), P_TAG(LAM),
    P_PORT(2, P_FAN(P_AT(1, P_REF(0)))))))));

/* `\b0.\b1.b1` -- SELECT-SECOND: the Church boolean FALSE and the `_cl` NIL cell.
   Two layers here, two nodes, and no name anywhere.  bind0 = the outer LAM,
   bind1 = the second LAM (the one selected). */
static const LinPat *const lin_pat_enc_second = P_FAN(P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_PORT(2, P_FAN(P_ALL3(P_BIND(1), P_TAG(LAM),
    P_PORT(2, P_FAN(P_AT(1, P_REF(1)))))))));

/* `\b0.\b1.((b1 <payload>) <tail>)` -- ONE successor layer of a Scott numeral:
   the layer applies its OWN second binder (`b1`, the `_ss` carrier in an annotated
   net) to the rest of the numeral.  bind0 = the LAM, bind1 = the applied binder,
   bind2 = the application, bind3 = the tail (the rest of the numeral, as the Port
   the tail is observed at -- bind3 is what the next layer is matched on).  This is
   what alloc_scott_named builds AND what parse.c's numeral literal compiles to. */
static const LinPat *const lin_pat_enc_succ = P_FAN(P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_PORT(2, P_FAN(P_ALL3(P_BIND(1), P_TAG(LAM),
    P_PORT(2, P_FAN(P_ALL(P_BIND(2), P_ALL(P_TAG(APP),
      P_ALL(P_PORT(0, P_FAN(P_AT(1, P_REF(1)))),      /* the layer's own binder, applied */
            P_PORT(2, P_BIND(3))))))))))));           /* ... to the rest of the numeral */

/* A `_cl` cons cell `\h.\t.\c.\n.((c h) t)`: the cell shape the core's own walkers
   read (net_spine_slots, decode_spine, lin_pat_cell), so a driver's read and the
   interpreter's cannot drift.  bind0 = the `c` LAM, bind1 = the `n` LAM, bind2 =
   the body APP, bind3 = the inner APP that applies c, bind4 = the HEAD port,
   bind5 = the TAIL port.  The cell states no payload requirement: which value
   belongs in slot 4 is the caller's expectation (P_SPINE_HEAD is how a pattern
   states it), which is the whole of the LIN_ENC_CONS / LIN_ENC_STR difference.
   Its two halves are named, since the cell nests three deep. */
static const LinPat *const lin_pat_enc_cell_ia =
  P_FAN(P_ALL3(P_BIND(3), P_TAG(APP), P_PORT(2, P_BIND(4))));
static const LinPat *const lin_pat_enc_cell_body =
  P_FAN(P_ALL(P_BIND(2), P_ALL(P_TAG(APP),
    P_ALL(P_PORT(0, lin_pat_enc_cell_ia), P_PORT(2, P_BIND(5))))));
static const LinPat *const lin_pat_enc_cell = P_FAN(P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_PORT(2, P_FAN(P_AT(0, P_ALL3(P_BIND(1), P_TAG(LAM),
    P_PORT(2, lin_pat_enc_cell_body)))))));

/* The `_op` closure header: a LAM and an APP at MUTUALLY WIRED PRINCIPAL ports --
   a redex -- whose APP carries the operand list at port 2.  bind0 = the operator
   LAM, bind1 = the APP, bind2 = the operand-list port.  WHICH operator it is lives
   in the LAM's carrier name, which a raw net does not have: the caller says "read
   this port as an `_op`" (the DT_OP expectation), and reads the list with
   lin_pat_enc_cell (or forces it first: on a compiled net the list is still an
   unbuilt application until something walks it). */
static const LinPat *const lin_pat_enc_op = P_AT(0, P_ALL(
  P_BIND(1), P_ALL(P_TAG(APP),
    P_ALL(P_PORT(0, P_AT(0, P_ALL(P_BIND(0), P_ALL(P_TAG(LAM),
           P_PORT(0, P_AT(0, P_REF(1))))))),
          P_PORT(2, P_BIND(2))))));

/* The `_ffi` closure header `\_ffi.\_ret.((_ffi <fn>) <args>)`, exactly the shape
   net_ffi_header digs: bind0 = the outer LAM, bind1 = `_ret`, bind2 = the header
   APP (arrived at its port 1), bind3 = the `<fn>` APP (whose port 2 is the fn-name
   string), bind4 = the fn-name port, bind5 = the argument-list port. */
static const LinPat *const lin_pat_enc_ffi_fn =
  P_FAN(P_AT(1, P_ALL3(P_BIND(3), P_TAG(APP), P_PORT(2, P_BIND(4)))));
static const LinPat *const lin_pat_enc_ffi_hdr =
  P_FAN(P_AT(1, P_ALL3(P_BIND(2), P_TAG(APP),
    P_ALL(P_PORT(0, lin_pat_enc_ffi_fn), P_PORT(2, P_BIND(5))))));
static const LinPat *const lin_pat_enc_ffi = P_FAN(P_ALL3(
  P_BIND(0), P_TAG(LAM),
  P_PORT(2, P_FAN(P_AT(0, P_ALL3(P_BIND(1), P_TAG(LAM),
    P_PORT(2, lin_pat_enc_ffi_hdr)))))));

/* The pattern for a LAYER of an expected encoding: NULL when the (enc, layer) pair
   names no shape, which is how the caller's expectation is spelled as data.  The
   OP and FFI headers have one shape each, so their layer is ignored. */
static inline const LinPat *lin_pat_enc_shape(int enc, int layer) {
  switch (enc) {
  case LIN_ENC_NUM:  return layer == LIN_L_INDUCTIVE ? lin_pat_enc_succ : lin_pat_enc_first;
  case LIN_ENC_BOOL: return layer == LIN_L_FALSE ? lin_pat_enc_second : lin_pat_enc_first;
  case LIN_ENC_CONS:
  case LIN_ENC_STR:  return layer == LIN_L_INDUCTIVE ? lin_pat_enc_cell : lin_pat_enc_second;
  case LIN_ENC_OP:   return lin_pat_enc_op;
  case LIN_ENC_FFI:  return lin_pat_enc_ffi;
  default: return NULL;
  }
}

/* Which layer of the expected encoding `enc` is at `p`?  1 and the layer id in
   `*layer` when the STRUCTURE there is one of that encoding's layers, 0 when it is
   not -- and a value that is not yet a normal form declines rather than being
   demanded (PURE).  `m`, when given, keeps the bindings of the layer that matched;
   the patterns' header says what each slot is. */
static inline int lin_pat_enc_layer_of(const Net *n, Port p, int enc, int *layer, LinMatch *m) {
  LinMatch local;
  if (!m) m = &local;
  if (enc == LIN_ENC_NUM || enc == LIN_ENC_BOOL) {
    if (lin_pat_match((Net *)n, p, lin_pat_enc_first, LIN_PAT_BUDGET_FOR(n), m)) {
      *layer = LIN_L_TERMINAL; return 1;
    }
  }
  if (enc == LIN_ENC_BOOL) {
    if (lin_pat_match((Net *)n, p, lin_pat_enc_second, LIN_PAT_BUDGET_FOR(n), m)) {
      *layer = LIN_L_FALSE; return 1;
    }
    return 0;
  }
  if (enc == LIN_ENC_NUM) {
    if (lin_pat_match((Net *)n, p, lin_pat_enc_succ, LIN_PAT_BUDGET_FOR(n), m)) {
      *layer = LIN_L_INDUCTIVE; return 1;
    }
    return 0;
  }
  if (enc == LIN_ENC_CONS || enc == LIN_ENC_STR) {
    if (lin_pat_match((Net *)n, p, lin_pat_enc_cell, LIN_PAT_BUDGET_FOR(n), m)) {
      *layer = LIN_L_INDUCTIVE; return 1;
    }
    if (lin_pat_match((Net *)n, p, lin_pat_enc_second, LIN_PAT_BUDGET_FOR(n), m)) {
      *layer = LIN_L_TERMINAL; return 1;
    }
    return 0;
  }
  return 0;
}

/* How many INDUCTIVE layers from `p` down to the encoding's terminal, PURELY: a
   numeral's value for LIN_ENC_NUM, a list's/string's length for LIN_ENC_CONS, and
   for LIN_ENC_BOOL 1 (select-first, true) or 0 (select-second, false).  Every
   layer is matched separately, so a layer whose tail is still a thunk (an
   unreduced application) fails the next layer's test and the whole read DECLINES
   instead of demanding it.  This is `lin_pat_num_nf` with the expected encoding
   supplied by the CALLER -- the form that works on a net with no names. */
static inline int lin_pat_enc_num_nf(const Net *n, Port p, int enc, long *out) {
  long cnt = 0;
  if (!n || enc == LIN_ENC_OP || enc == LIN_ENC_FFI) return 0;
  for (int step = 0; step < n->nn; step++) {
    int layer; LinMatch m;
    if (!lin_pat_enc_layer_of(n, p, enc, &layer, &m)) return 0;
    if (enc == LIN_ENC_BOOL) { if (out) *out = (layer == LIN_L_TERMINAL); return 1; }
    if (layer != LIN_L_INDUCTIVE) { if (out) *out = cnt; return 1; }
    cnt++;
    p = enc == LIN_ENC_NUM ? m.bind[3] : m.bind[5];    /* NUM: the tail; a cell: its tail */
  }
  return 0;
}

/* The FORCING sibling: every layer is reduced to a normal form first
   (net_force_val), so a partially reduced value reads.  This is REDUCTION -- legal
   in a match phase or from readback, and NOT in a pure context -- and it still
   consults no name, which is what makes it usable on a raw net. */
static inline int lin_pat_enc_num(Net *n, Port p, int enc, long *out) {
  long cnt = 0;
  if (!n || enc == LIN_ENC_OP || enc == LIN_ENC_FFI) return 0;
  for (int step = 0; step < n->nn; step++) {
    int layer; LinMatch m;
    p = net_force_val(n, p);
    if (!lin_pat_enc_layer_of((const Net *)n, p, enc, &layer, &m)) return 0;
    if (enc == LIN_ENC_BOOL) { if (out) *out = (layer == LIN_L_TERMINAL); return 1; }
    if (layer != LIN_L_INDUCTIVE) { if (out) *out = cnt; return 1; }
    cnt++;
    p = net_force_val(n, enc == LIN_ENC_NUM ? m.bind[3] : m.bind[5]);
  }
  return 0;
}

/* A STRING CELL: the cons cell whose PAYLOAD is a numeral of the encoding the
   caller expects (a char code).  The cell alone does not say that -- a list of
   lists is the same cell -- so the payload's encoding is an argument here exactly
   as the value's is above, and the composite is a WALK rather than one pattern
   because the payload is a value of unknown length: its finite half is
   `lin_pat_enc_cell`, which a caller uses directly when the payload is its own
   business.  `codes` collects up to `max` payload values and `*nout` gets the
   count; a list that does not fit, or a payload that is not that encoding's normal
   form, DECLINES rather than truncating.  PURE. */
static inline int lin_pat_enc_str_nf(const Net *n, Port p, int pay_enc, long *codes, int max, int *nout) {
  int cnt = 0;
  if (!n) return 0;
  if (nout) *nout = 0;
  for (int step = 0; step < n->nn; step++) {
    int layer; LinMatch m;
    if (!lin_pat_enc_layer_of(n, p, LIN_ENC_STR, &layer, &m)) return 0;
    if (layer != LIN_L_INDUCTIVE) { if (nout) *nout = cnt; return 1; }   /* the nil cell ends it */
    long code;
    if (cnt >= max) return 0;                                           /* would not fit */
    if (!lin_pat_enc_num_nf(n, m.bind[4], pay_enc, &code)) return 0;
    if (codes) codes[cnt] = code;
    cnt++;
    p = m.bind[5];
  }
  return 0;
}

/* The FORCING sibling of the string walk: each cell AND each payload is reduced
   first, so a string whose chars are still thunks reads.  REDUCTION. */
static inline int lin_pat_enc_str(Net *n, Port p, int pay_enc, long *codes, int max, int *nout) {
  int cnt = 0;
  if (!n) return 0;
  if (nout) *nout = 0;
  for (int step = 0; step < n->nn; step++) {
    int layer; LinMatch m;
    p = net_force_val(n, p);
    if (!lin_pat_enc_layer_of((const Net *)n, p, LIN_ENC_STR, &layer, &m)) return 0;
    if (layer != LIN_L_INDUCTIVE) { if (nout) *nout = cnt; return 1; }
    long code;
    if (cnt >= max) return 0;
    m.bind[4] = net_force_val(n, m.bind[4]);
    if (!lin_pat_enc_num(n, m.bind[4], pay_enc, &code)) return 0;
    if (codes) codes[cnt] = code;
    cnt++;
    p = net_force_val(n, m.bind[5]);
  }
  return 0;
}

/* ---------------------------------------------------------------------------
 * the claim bridge
 * ------------------------------------------------------------------------- */

/* The covered region's exits: the AUXILIARY ports of covered nodes whose wire
   leaves the covered set.  Returns the count, or -1 if they do not all fit (a
   region with a frontier nobody can enumerate is not a claimable region). */
static inline int lin_pat_region_exits(const LinMatch *m, Port *out, int max) {
  const Net *n = m->n;
  int ne = 0;
  if (m->overflow) return -1;
  for (int i = 0; i < m->nnodes; i++) {
    int u = m->nodes[i];
    if (!lin_pat_live(n, u)) continue;
    for (int p = 1; p < 3; p++) {          /* auxiliary ports only: a principal
                                              boundary could be crossed by a redex */
      Port w = net_wire(n, (Port){u, p});
      if (!lin_pat_live(n, w.node) || lin_pat_covered(m, w.node)) continue;
      if (ne >= max) return -1;
      if (out) out[ne] = (Port){u, p};
      ne++;
    }
  }
  return ne;
}

/* Fill `c` from a successful match: the redexes the match consumed (every
   mutually-wired principal pair inside the covered set) plus, when
   LIN_CLAIM_REGION is set, the region's exits -- the derived frontier followed by
   the caller's own `exits` (a driver that knows a boundary the walk cannot see).
   Without LIN_CLAIM_REGION a claim is just its redexes, so `nexits` must be 0.
   Returns 1 on a well-formed claim; the core still validates it
   (lin_claim_check), which is the authority on whether the region is real. */
static inline int lin_pat_claim(const LinMatch *m, LinClaim *c, const Port *exits,
                                int nexits, uint32_t flags) {
  const Net *n = m->n;
  if (!m->ok || m->overflow || m->nnodes <= 0) return 0;
  memset(c, 0, sizeof *c);
  c->flags = flags;
  for (int i = 0; i < m->nnodes; i++) {
    int u = m->nodes[i];
    if (!lin_pat_live(n, u)) continue;
    Port w = net_wire(n, (Port){u, 0});
    if (w.port != 0 || !lin_pat_live(n, w.node)) continue;
    if (!lin_pat_covered(m, w.node)) continue;
    if (u > w.node) continue;                       /* one pair per redex */
    Port bk = net_wire(n, w);
    if (bk.node != u || bk.port != 0) continue;     /* mutual: otherwise not a redex */
    if (c->npairs >= LIN_MAX_CLAIM_PAIRS) return 0;
    c->pairs[2 * c->npairs] = (Port){u, 0};
    c->pairs[2 * c->npairs + 1] = w;
    c->npairs++;
  }
  if (!c->npairs) return 0;
  if (flags & LIN_CLAIM_REGION) {
    int ne = lin_pat_region_exits(m, c->exits, LIN_MAX_CLAIM_EXITS);
    if (ne < 0) return 0;
    c->nexits = ne;
    for (int i = 0; i < nexits; i++) {
      if (c->nexits >= LIN_MAX_CLAIM_EXITS) return 0;
      c->exits[c->nexits++] = exits[i];
    }
  } else if (nexits) {
    return 0;                       /* the core refuses exits without a region */
  }
  return 1;
}

/* ---------------------------------------------------------------------------
 * the per-net match cache (a derivation, never the authority)
 * ------------------------------------------------------------------------- */
typedef struct { int node; unsigned gen; long val; } LinPatCacheEnt;
typedef struct { LinPatCacheEnt *e; int cap; unsigned gen; } LinPatCache;

/* `store` is the caller's memory (a driver's state, so it dies with the net and is
   copied with it): the matcher allocates nothing.  Entries are direct-mapped by
   node index, so a table that is too small loses entries rather than growing. */
static inline void lin_pat_cache_init(LinPatCache *c, LinPatCacheEnt *store, int cap) {
  c->e = store;
  c->cap = cap > 0 ? cap : 0;
  c->gen = 1;
  if (c->e && c->cap) memset(c->e, 0, sizeof *c->e * (size_t)c->cap);
}
static inline void lin_pat_cache_drop(LinPatCache *c, int node) {
  if (!c->e || c->cap <= 0) return;
  c->e[(unsigned)node % (unsigned)c->cap].gen = 0;
}
static inline int lin_pat_cache_get(const LinPatCache *c, int node, long *val) {
  if (!c->e || c->cap <= 0) return 0;
  const LinPatCacheEnt *e = &c->e[(unsigned)node % (unsigned)c->cap];
  if (e->gen != c->gen || e->node != node) return 0;
  if (val) *val = e->val;
  return 1;
}
static inline void lin_pat_cache_put(LinPatCache *c, int node, long val) {
  if (!c->e || c->cap <= 0) return;
  LinPatCacheEnt *e = &c->e[(unsigned)node % (unsigned)c->cap];
  e->node = node; e->gen = c->gen; e->val = val;
}
/* Every entry at once: the driver stopped holding the region it derived them in
   (a released claim, a rewritten slice, a compacted net).  O(1). */
static inline void lin_pat_cache_invalidate(LinPatCache *c) {
  if (!c->e || c->cap <= 0) return;
  if (++c->gen == 0) { c->gen = 1; memset(c->e, 0, sizeof *c->e * (size_t)c->cap); }
}

#endif /* LIN_PATTERN_H */

/* ---------------------------------------------------------------------------
 * the DT_OP encoding: which OPERATOR a saturated `_op` is
 * ---------------------------------------------------------------------------
 * Nothing on a node says "I am `add`": the head of `((\_add (_padd a b)) spine)` and the same net
 * for `mul` are ONE shape, so `ctor_tag(name)` was the only thing that ever told them apart and a raw
 * net cannot offer it.  The language therefore marks the HEAD (see lin_pat_op_head) and writes the
 * operator's INDEX as the FIRST slot of the operand list -- a numeral, which is the encoding the language already has for an index -- and this
 * enumeration is that index, next to the scalar-table row it names.  std/num.lin is the other half of
 * the agreement: a new operator is a row here plus a definition there, never a label on a node.
 * ------------------------------------------------------------------------- */
enum { LIN_OP_ADD = 0, LIN_OP_MUL, LIN_OP_SUB, LIN_OP_EQ, LIN_OP_LT, LIN_OP_LEQ, LIN_OP_GT,
       LIN_OP_GEQ, LIN_OP_DIV, LIN_OP_MOD, LIN_OP_POW, LIN_OP_N };
static inline const char *lin_op_fn(int code) {
  static const char *const names[LIN_OP_N] = {
    "lin_add", "lin_mul", "lin_sub", "lin_eq", "lin_lt", "lin_leq", "lin_gt", "lin_geq",
    "lin_div", "lin_mod", "lin_pow"
  };
  return (code >= 0 && code < LIN_OP_N) ? names[code] : NULL;
}

/* PURE: the port is the HEAD of a saturated `_op` redex.
 *
 * A net carries no label, so the head has to SAY what it is by its shape -- and a shape that BOTH a
 * plain beta redex and an operator share is no use: `(\x.(f x)) arg` and `((\op BODY) spine)` are
 * one shape, which is why the fold used to read a carrier name here and why "the body is an
 * application" is NOT a test (every `\x.(f x)` would pass it).  std/num.lin therefore writes an
 * operator head as
 *
 *     \op. ((\_k <pure fallback>) op)          -- and applies THAT to the operand list
 *
 * so the head's OWN BINDER is the ARGUMENT of the body's application, and that application's function
 * is itself a redex.  A `\x.(f x)` uses its binder as the argument too, but its function is a
 * VARIABLE OCCURRENCE -- an auxiliary arriving at port 1 of the binder's LAM -- where an operator's
 * function is a lambda's PRINCIPAL port.  Reading two wires and two tags: no force, no allocation,
 * which is what `claim` requires (`reduce`'s operand decoding may force; this may not).
 *
 * Applying the head to its list beta-reduces the marker away, leaving exactly the pure fallback in
 * `_k`'s place -- so a driver that declines still gets the exact answer by plain beta. */
static inline int lin_pat_op_head(const Net *n, Port p, void *ctx) {
  (void)ctx;
  if (!n || p.port != 0 || !lin_pat_live(n, p.node) || n->tag[p.node] != LAM) return 0;
  Port use = net_wire(n, (Port){p.node, 1});
  if (use.port != 2 || !lin_pat_live(n, use.node) || n->tag[use.node] != APP) return 0;
  Port fn = net_wire(n, (Port){use.node, 0});
  return fn.port == 0 && lin_pat_live(n, fn.node) && n->tag[fn.node] == LAM;
}
/* parenthesized: P_PRED carries a comma, so an unguarded macro would split as TWO arguments
   wherever it is nested (`P_NOT(P_OP_HEAD)`), which is exactly how it first failed to compile. */
#define P_OP_HEAD (P_PRED(lin_pat_op_head, NULL))

/* PURE: the operator index a saturated `_op` at `app` states, or -1 when it states none.  The index
   is the head of the operand list's first cell; the OPERANDS are that cell's tail. */
static inline int lin_pat_op_code(const Net *n, int app) {
  Port head, ops;
  if (!lin_pat_live(n, app) || n->tag[app] != APP) return -1;
  if (!lin_pat_cell_at(n, net_wire(n, (Port){app, 2}), &head, &ops)) return -1;
  long code = -1;
  if (!lin_pat_enc_num_nf(n, head, LIN_ENC_NUM, &code)) return -1;
  return (code >= 0 && code < LIN_OP_N) ? (int)code : -1;
}
/* PURE: the operand list of the same redex -- the spine AFTER the operator index. */
static inline Port lin_pat_op_args(const Net *n, int app) {
  Port head, ops;
  if (!lin_pat_live(n, app) || n->tag[app] != APP) return (Port){-1, 0};
  if (!lin_pat_cell_at(n, net_wire(n, (Port){app, 2}), &head, &ops)) return (Port){-1, 0};
  return ops;
}

/* The pure NUM reader declared above IS the LIN_ENC_NUM case of the enc-based walk. */
static inline int lin_pat_num_nf(const Net *n, Port p, long *out) {
  return lin_pat_enc_num_nf(n, p, LIN_ENC_NUM, out);
}
