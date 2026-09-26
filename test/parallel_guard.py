#!/usr/bin/env python3
r"""The driver ABI's failure modes must be diagnosed, not silently absorbed.

ABI 3 deleted the four legacy hooks (`arg_fold`, `materialize`, `drain`, `pending`) and with them the
two ways a driver could break the core's invariants:

1. `arg_fold` ran INSIDE a parallel wave, where `net_alloc` cannot grow the net (a `realloc` would
   move the tag/wire/scope/name arrays out from under every worker holding raw pointers into them).
   Measured before the guard: an ASan heap-buffer-overflow, a SIGSEGV, `free(): invalid pointer`.
   A driver no longer gets a hook in that region at all -- `claim`/`reduce` run between waves -- and a
   driver that needs a concrete operand now asks for it with `net_force` rather than being handed one.

2. `drain` could re-enqueue work without making progress.  `net_reduce` bounded that with a livelock
   guard, and the guard used to drop the active list and `break` with no signal -- a truncated net
   could then be printed as the answer instead of being reported as not-a-value.  ABI 3 has no drain
   loop: a driver re-enqueues inside `reduce`, and `net_reduce` stops as soon as a wave makes no
   progress, so a driver that only re-enqueues TERMINATES the run rather than spinning in it.

What is left to test is therefore (a) that the ABI bump is actually enforced -- an ABI-2 plugin is
smaller than the ABI-3 struct, so reading it would run past its end and the core must reject it
loudly instead -- and (b) that a driver which claims every redex and then does nothing still leaves
the run TERMINATING, rather than hanging or quietly reporting a value it never computed.

The last two probes are about a net with NO ANNOTATIONS AT ALL.  A net used to carry carrier names
("_sz", "_cl") on its nodes and everything that read a value consulted them; it is now tags, wiring
and gauges alone -- alpha-equivalent nets are ONE net -- so the shared matcher grew structural
recognisers whose EXPECTED ENCODING is an argument, never something sniffed off the node
(std/runtime/pattern.h), and the claim protocol lets a driver state the region it wants.  Probe 11
builds a net by hand -- no name on any node -- recognises shapes in it, proposes a region around its
redex, gets it certified, rewrites it and reads the result back structurally.  Probe 12 takes a COMPILER's
net and shows a structural driver recognising and folding it, with the compiler's TYPE supplying the
result's meaning: the answer is the same value it was (4), read structurally AND PRINTED, because
readback is handed the domain the type checker computed.  That inversion is the point of the
probe: it used to assert that a net with its names cleared could not be printed.

This test compiles those drivers from strings into a scratch std tree -- they are NOT part of the
shipped std.  A compiler is needed to build the probes; where none is found the test SKIPS loudly
rather than passing quietly, so a CI that loses its toolchain is visible.

usage: parallel_guard.py <lin-binary> <std-dir>
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile

PROLOGUE = r'''
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
'''

# --- probe 1: a plugin built against the DELETED ABI must be rejected, not trusted --------------
DRIVER_ABI2 = PROLOGUE + r'''
static int old_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 0; }
static int old_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;
}
LinDriver lin_abiprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = 2u,     /* the deleted ABI: fewer fields than this core reads */
  .net_size = (uint32_t)sizeof(Net),
  .name = "abiprobe", .description = "an ABI-2 plugin",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = old_claim, .reduce = old_reduce,
};
'''

# --- probe 2: claim everything, compute nothing, and re-enqueue forever ------------------------
PROBE_BODY = PROLOGUE + r'''
static int noclaim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 1; }
static int noreduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)lim; (void)ch;
  for (int i = 0; i < nr; i++) lin_enqueue(n, rx[2 * i], rx[2 * i + 1]);   /* no progress, ever */
  return 0;
}
LinDriver lin_noprog_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .name = "noprog", .description = "claims every redex and re-enqueues it without progress",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .claim = noclaim, .reduce = noreduce,
};
'''

# --- probe 3: a capability the core does not have must be refused, not ignored -----------------
# A plugin states what it cannot work without.  Running it anyway is the failure mode this check
# exists for: the plugin would take a code path that assumes a hook it never got.
DRIVER_UNKNOWN_WANT = PROLOGUE + r'''
static int w_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 0; }
static int w_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;
}
LinDriver lin_wantprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "wantprobe", .description = "requires a capability this core does not have",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .wants = (1ull << 40),
  .claim = w_claim, .reduce = w_reduce,
};
'''

# --- probe 4: a want that does not fit in the struct the plugin was built with ------------------
# `size` is what makes the interface extensible: the core may only read fields that fit, so a
# plugin whose struct ends before the hook it needs must be refused rather than read past its end.
DRIVER_SHORT_STRUCT = PROLOGUE + r'''
#include <stddef.h>
static int s_claim(const Net *n, Port a, Port b) { (void)n; (void)a; (void)b; return 0; }
static int s_reduce(Net *n, Port *rx, int nr, long lim, int *ch) {
  (void)n; (void)rx; (void)nr; (void)lim; (void)ch; return 0;
}
LinDriver lin_shortprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)offsetof(LinDriver, carry_save),   /* the struct as this plugin was built ends here */
  .name = "shortprobe", .description = "wants a hook beyond its own struct",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .wants = LIN_WANT_CARRY,
  .claim = s_claim, .reduce = s_reduce,
};
'''

# --- probe 5: the claim protocol -- match once per wave, act on a region --------------------
# `match` runs before any slice exists, so a matcher may inspect and force; the claim it returns is
# validated by the core, and the pairs inside it are then excluded from every other driver and from
# the base engine.  The probe claims plain-lambda redexes, beta-reduces them itself, and reports how
# many it acted on: the answer must still be right, and the base engine must NOT also fire them.
DRIVER_MATCH = PROLOGUE + r'''
static long m_acts;
static int m_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)st;
  for (int i = 0; i < view->npairs; i++) {
    Port a = view->pairs[2 * i], b = view->pairs[2 * i + 1];
    if (a.node < 0 || a.node >= n->nn || b.node < 0 || b.node >= n->nn) continue;
    int lam = -1;
    if (n->tag[a.node] == LAM && n->tag[b.node] == APP) lam = a.node;
    else if (n->tag[b.node] == LAM && n->tag[a.node] == APP) lam = b.node;
    if (lam < 0) continue;
    /* A foldable head -- an `_ffi` header or an `_op` head -- belongs to arith, so the base engine
       must keep those redexes.  With no label on any node the SHAPE decides (std/runtime/pattern.h):
       an `_ffi` header's body is the `_ret` binder, and an `_op` head's binder is the ARGUMENT of
       its body's application. */
    {
      Port body = n->wire[lam * 3 + 2];
      if (body.node >= 0 && body.node < n->nn && !n->dead[body.node] && n->tag[body.node] == LAM)
        continue;                                            /* an `_ffi` closure */
      Port use = n->wire[lam * 3 + 1];
      if (use.port == 2 && use.node >= 0 && use.node < n->nn && !n->dead[use.node] &&
          n->tag[use.node] == APP) {
        Port fn = n->wire[use.node * 3 + 0];
        if (fn.port == 0 && fn.node >= 0 && fn.node < n->nn && !n->dead[fn.node] &&
            n->tag[fn.node] == LAM) continue;                 /* an `_op` head */
      }
    }
    memset(out, 0, sizeof *out);
    out->npairs = 1; out->pairs[0] = a; out->pairs[1] = b;
    return 1;
  }
  return 0;
}
static int m_act(Net *n, void *st, LinClaim *c) {
  (void)st;
  int done = 0;
  for (int i = 0; i < c->npairs; i++)
    if (net_interact(n, c->pairs[2 * i], c->pairs[2 * i + 1])) { done++; m_acts++; }
  return done;
}
static void m_report(void) { fprintf(stderr, "[matchprobe] acts=%ld\n", m_acts); }
LinDriver lin_matchprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "matchprobe", .description = "claims and reduces plain-lambda redexes itself",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH,
  .match = m_match, .act = m_act,
};
__attribute__((constructor)) static void m_init(void) { atexit(m_report); }
'''

# --- probe 6: a claim the core must REFUSE, and the run must survive ---------------------------
# The exit is at a PRINCIPAL port.  That is the rule that makes a region safe to rewrite in
# isolation (a redex is two mutually wired principal ports, so an auxiliary-only boundary cannot be
# crossed by one), so a driver that declares otherwise is not allowed to own the structure.
DRIVER_BADREGION = PROLOGUE + r'''
static int b_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)st;
  if (view->npairs < 1) return 0;
  memset(out, 0, sizeof *out);
  out->flags = LIN_CLAIM_REGION;
  out->npairs = 1; out->pairs[0] = view->pairs[0]; out->pairs[1] = view->pairs[1];
  out->nexits = 1; out->exits[0] = (Port){view->pairs[0].node, 0};   /* principal: refused */
  return 1;
}
static int b_act(Net *n, void *st, LinClaim *c) { (void)n; (void)st; (void)c; return 0; }
LinDriver lin_badregion_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "badregion", .description = "claims a region with an exit at a principal port",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH,
  .match = b_match, .act = b_act,
};
'''

# --- probe 7: a HELD claim -- deferral that is not loss ---------------------------------------
# The driver claims a redex, does nothing with it on the first wave, and only fires it on the
# second: the core must keep it reserved AND keep it queued in the meantime, so deferring work
# cannot lose it.  `revalidate` is the driver saying when it is finished.
DRIVER_HELD = PROLOGUE + r'''
static int h_acts, h_reval, h_claimed, h_done;
static int h_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)n; (void)st;
  if (h_claimed || view->npairs < 1) return 0;
  memset(out, 0, sizeof *out);
  out->flags = LIN_CLAIM_HELD;
  out->npairs = 1; out->pairs[0] = view->pairs[0]; out->pairs[1] = view->pairs[1];
  h_claimed = 1;
  return 1;
}
static int h_act(Net *n, void *st, LinClaim *c) {
  (void)st;
  if (h_acts++ == 0) return 0;                    /* first wave: hold it and do nothing */
  int done = 0;
  for (int i = 0; i < c->npairs; i++)
    if (net_interact(n, c->pairs[2 * i], c->pairs[2 * i + 1])) done++;
  h_done = 1;
  return done;
}
static int h_revalidate(Net *n, void *st, LinClaim *c) { (void)n; (void)st; (void)c; h_reval++; return !h_done; }
static void h_report(void) { fprintf(stderr, "[heldprobe] acts=%d reval=%d\n", h_acts, h_reval); }
LinDriver lin_heldprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "heldprobe", .description = "holds a claim across a wave before acting on it",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH | LIN_WANT_HELD,
  .match = h_match, .act = h_act, .revalidate = h_revalidate,
};
__attribute__((constructor)) static void h_init(void) { atexit(h_report); }
'''

# --- probe 8: the shared matcher -- a pattern match drives a claim ----------------------------
# std/runtime/pattern.h is the header-only matcher a driver compiles into itself.  This probe
# uses it end to end: a pattern recognizes a plain-lambda beta redex, `lin_pat_claim` turns the
# match into a claim (the redexes the match consumed, and the region's EXITS derived from the
# nodes it covered -- the driver never hand-builds a claim), `lin_claim_check` certifies it, and
# the driver fires what the core then leaves alone.  Two things must hold: the answer stays
# right, and -- because the matcher is PURE -- a match that walks the net and then DECLINES
# leaves `nn` and `steps` exactly as they were.  That is what makes the same matcher usable
# from `claim`, where forcing would move the net out from under the wave.
PROLOGUE_PAT = PROLOGUE + '#include "../runtime/pattern.h"\n'

DRIVER_PATCLAIM = PROLOGUE_PAT + r'''
/* A plain-lambda beta redex: a live APP at a principal port whose port-0 wire arrives at the
   principal port of a live LAM.  A net carries no label, so "plain" is decided by SHAPE: a redex
   whose head is a foldable closure (an `_op` head or an `_ffi` header) belongs to arith, and the
   base engine must keep those. */
static int pc_plain_lam(const Net *n, Port p, void *ctx) {
  (void)ctx;
  return p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == LAM &&
         !lin_pat_op_head(n, p, NULL);
}
static const LinPat *const PC_BETA = P_AT(0, P_ALL(
  P_BIND(1), P_ALL(P_TAG(APP),
    P_PORT(0, P_AT(0, P_ALL(P_BIND(0),
      P_ALL(P_TAG(LAM), P_PRED(pc_plain_lam, NULL))))))));

/* A pattern that WALKS and then declines: the purity assertion needs a match that really
   traversed structure, not one that stopped at its first test. */
static int pc_never(const Net *n, Port p, void *ctx) { (void)n; (void)p; (void)ctx; return 0; }
static const LinPat *const PC_DECLINE =
  P_ALL(P_PORT(2, P_SPINE(P_ANY)), P_PRED(pc_never, NULL));

static long pc_claims, pc_acts, pc_region, pc_plain, pc_pure, pc_impure;
static int pc_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)st;
  if (view->npairs < 1) return 0;
  {
    long nn0 = n->nn, st0 = n->steps;
    LinMatch m;
    (void)lin_pat_match(n, view->pairs[0], PC_DECLINE, LIN_PAT_BUDGET_FOR(n), &m);
    if (n->nn == nn0 && n->steps == st0) pc_pure++; else pc_impure++;
  }
  for (int i = 0; i < view->npairs; i++) {
    LinMatch m;
    char why[160];
    if (!lin_pat_match_pair(n, view->pairs[2 * i], view->pairs[2 * i + 1], PC_BETA,
                            LIN_PAT_BUDGET_FOR(n), &m))
      continue;
    if (lin_pat_claim(&m, out, NULL, 0, LIN_CLAIM_REGION) &&
        lin_claim_check(n, out, why, sizeof why)) { pc_region++; pc_claims++; return 1; }
    if (lin_pat_claim(&m, out, NULL, 0, 0) && lin_claim_check(n, out, why, sizeof why)) {
      pc_plain++; pc_claims++; return 1;
    }
  }
  return 0;
}
static int pc_act(Net *n, void *st, LinClaim *c) {
  (void)st;
  int done = 0;
  for (int i = 0; i < c->npairs; i++)
    if (net_interact(n, c->pairs[2 * i], c->pairs[2 * i + 1])) { done++; pc_acts++; }
  return done;
}
static void pc_report(void) {
  fprintf(stderr, "[patclaim] claims=%ld acts=%ld region=%ld plain=%ld pure=%ld impure=%ld\n",
          pc_claims, pc_acts, pc_region, pc_plain, pc_pure, pc_impure);
}
LinDriver lin_patclaim_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "patclaim", .description = "matches a shape with the shared matcher and claims it",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH,
  .match = pc_match, .act = pc_act,
};
__attribute__((constructor)) static void pc_init(void) { atexit(pc_report); }
'''

# --- probe 9: P_BIND/P_REF -- "the same node twice" is not "two equal nodes" -------------------
# Sharing in the net is ONE node reached at two ports (a fan's two outputs are ports of a single
# node), so a pattern that states sharing states NODE identity -- P_REF -- while its twin demands
# two different nodes.  The driver builds both shapes itself (the match phase may rewrite the
# net): a spine whose two slots are the same node at two ports, and a spine whose two slots are
# two nodes with the same tag and carrier.  The patterns must separate them -- nothing else in
# the vocabulary can -- and the same pair of patterns is also run over a spine the COMPILER
# produced, so the distinction is shown on a real net and not only on a built one.
DRIVER_PATSHARE = PROLOGUE_PAT + r'''
LinDriver lin_patshare_driver;
typedef struct { Port shared, distinct; LinPatCacheEnt store[64]; LinPatCache cache; } Spines;

/* A cons cell `\c.\n.((c h) t)` whose head is `slot` and whose tail is `tail`, and the nil cell
   that ends a list (std/num.lin's `_cl_cons`/`_cl_nil` SHAPES, as net_spine_slots reads them --
   built here, with no name on any node, so the two sharing shapes exist to be told apart). */
static Port ps_nil(Net *n) {
  Scope sc = scope_nil();
  Port c = net_alloc(n, LAM, sc), nn = net_alloc(n, LAM, sc);
  net_link(n, (Port){c.node, 2}, (Port){nn.node, 0}, 0);
  net_link(n, (Port){nn.node, 2}, (Port){nn.node, 1}, 0);
  return (Port){c.node, 0};
}
static Port ps_cell(Net *n, Port slot, Port tail) {
  Scope sc = scope_nil();
  Port c = net_alloc(n, LAM, sc), nn = net_alloc(n, LAM, sc);
  Port body = net_alloc(n, APP, sc), ia = net_alloc(n, APP, sc);
  net_link(n, (Port){c.node, 2}, (Port){nn.node, 0}, 0);
  net_link(n, (Port){nn.node, 2}, (Port){body.node, 0}, 0);
  net_link(n, (Port){body.node, 0}, (Port){ia.node, 0}, 0);
  net_link(n, (Port){body.node, 2}, tail, 0);
  net_link(n, (Port){ia.node, 2}, slot, 0);
  return (Port){c.node, 0};
}
/* The cache's contract, exercised once per net: what a driver relies on when it keys a
   derivation by NODE INDEX -- a hit, and then no hit after the slot was recycled (an event only
   the core knows, which is what the node_recycled hook is for) or after the region the entry was
   derived inside was released (the driver's own event, O(1) for every entry at once). */
static int ps_cache_ok;                    /* the cache's contract held (see ps_cache_contract) */
static int ps_cache_contract(void) {
  LinPatCacheEnt store[8];
  LinPatCache c;
  long v;
  lin_pat_cache_init(&c, store, 8);
  if (lin_pat_cache_get(&c, 7, &v)) return 0;              /* nothing stored yet */
  lin_pat_cache_put(&c, 7, 42);
  if (!lin_pat_cache_get(&c, 7, &v) || v != 42) return 0;  /* a hit */
  lin_pat_cache_drop(&c, 7);                               /* the slot was recycled */
  if (lin_pat_cache_get(&c, 7, &v)) return 0;
  lin_pat_cache_put(&c, 7, 42);
  lin_pat_cache_invalidate(&c);                            /* the region was released */
  if (lin_pat_cache_get(&c, 7, &v)) return 0;
  return 1;
}

static void *ps_state_new(Net *n) {
  Spines *s = calloc(1, sizeof *s);
  if (!s) return NULL;
  /* the driver's per-net tables: a cache keyed by NODE INDEX, which is only meaningful beside
     the net it is about (slots are recycled) -- see node_recycled below. */
  lin_pat_cache_init(&s->cache, s->store, 64);
  ps_cache_ok = ps_cache_contract();
  Port one = net_alloc(n, LAM, scope_nil());
  Port two = net_alloc(n, LAM, scope_nil());
  Port three = net_alloc(n, LAM, scope_nil());
  s->shared   = ps_cell(n, (Port){one.node, 0},
                ps_cell(n, (Port){one.node, 1}, ps_nil(n)));      /* one node, two ports */
  s->distinct = ps_cell(n, (Port){two.node, 0},
                ps_cell(n, (Port){three.node, 0}, ps_nil(n)));    /* two equal nodes   */
  return s;
}
/* The one event only the core knows: a freed slot has been handed out again, so any entry keyed
   by that index is about a node that no longer exists. */
static void ps_node_recycled(Net *n, void *st, int node) {
  (void)n;
  Spines *s = st;
  if (s) lin_pat_cache_drop(&s->cache, node);
}
static void ps_state_free(Net *n, void *st) {
  (void)n;
  Spines *s = st;
  if (s) lin_pat_cache_invalidate(&s->cache);   /* every entry at once, before the storage dies */
  free(st);
}

/* P_SPINE_HEAD is the cons half of P_SPINE: the first slot binds slot 0 and the rest of the list
   carries the next requirement -- which is what a list of UNLIKE requirements needs. */
static const LinPat *const PS_SAME = P_SPINE_HEAD(P_BIND(0),
  P_SPINE_HEAD(P_REF(0), P_SPINE_N(0, P_ANY)));
static const LinPat *const PS_DIFF = P_SPINE_HEAD(P_BIND(0),
  P_SPINE_HEAD(P_ALL(P_ANY, P_NOT(P_REF(0))), P_SPINE_N(0, P_ANY)));
static const LinPat *const PS_APP_SAME = P_ALL(P_TAG(APP), P_PORT(2, PS_SAME));
static const LinPat *const PS_APP_DIFF = P_ALL(P_TAG(APP), P_PORT(2, PS_DIFF));
static const LinPat *const PS_APP = P_ALL(P_BIND(0), P_TAG(APP));   /* ... and name the APP */

static long ps_sh_same, ps_sh_diff, ps_di_same, ps_di_diff, ps_prog_same, ps_prog_diff, ps_forced;
static long ps_hits, ps_miss;
/* The operand list of a compiled program is an application until something walks it, and the
   matcher NEVER forces: the probe does (net_spine_slots -- the interpreter's own operand-shape
   authority) and matches again.  Forcing is legal in the match phase, and illegal in a claim. */
static int ps_try(Net *n, Port p, const LinPat *pat) {
  LinMatch m;
  if (n->dead[p.node] || n->tag[p.node] != APP) return 0;
  if (lin_pat_match(n, p, pat, LIN_PAT_BUDGET_FOR(n), &m)) return 1;
  Port argp = net_wire(n, (Port){p.node, 2});
  if (argp.node < 0 || argp.node >= n->nn) return 0;
  if (net_spine_slots(n, argp) != 2) return 0;
  ps_forced++;
  return lin_pat_match(n, p, pat, LIN_PAT_BUDGET_FOR(n), &m);
}
static int ps_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)out;
  Spines *s = st ? st : lin_driver_state(n, &lin_patshare_driver);
  LinMatch m;
  if (s) {
    if (lin_pat_match(n, s->shared, PS_SAME, LIN_PAT_BUDGET_FOR(n), &m)) ps_sh_same++;
    if (lin_pat_match(n, s->shared, PS_DIFF, LIN_PAT_BUDGET_FOR(n), &m)) ps_sh_diff++;
    if (lin_pat_match(n, s->distinct, PS_SAME, LIN_PAT_BUDGET_FOR(n), &m)) ps_di_same++;
    if (lin_pat_match(n, s->distinct, PS_DIFF, LIN_PAT_BUDGET_FOR(n), &m)) ps_di_diff++;
  }
  for (int i = 0; i < view->npairs; i++) {
    Port a = view->pairs[2 * i], b = view->pairs[2 * i + 1];
    if (!lin_pat_match_pair(n, a, b, PS_APP, LIN_PAT_BUDGET_FOR(n), &m)) continue;
    if (ps_try(n, a, PS_APP_SAME) || ps_try(n, b, PS_APP_SAME)) ps_prog_same++;
    /* ... and the same test through the driver's cache: a derivation of the net keyed by node
       index, reused across waves, dropped when the core says the slot was recycled. */
    if (s) {
      int app = m.bind[0].node;
      long hit;
      if (lin_pat_cache_get(&s->cache, app, &hit)) { ps_hits++; if (hit) ps_prog_diff++; continue; }
      ps_miss++;
      hit = ps_try(n, (Port){app, 0}, PS_APP_DIFF);
      lin_pat_cache_put(&s->cache, app, hit);
      if (hit) ps_prog_diff++;
    } else if (ps_try(n, a, PS_APP_DIFF) || ps_try(n, b, PS_APP_DIFF)) {
      ps_prog_diff++;
    }
  }
  return 0;
}
static void ps_report(void) {
  fprintf(stderr, "[patshare] shared_same=%ld shared_diff=%ld distinct_same=%ld distinct_diff=%ld "
                  "prog_same=%ld prog_diff=%ld forced=%ld cache_ok=%d lookups=%ld\n",
          ps_sh_same, ps_sh_diff, ps_di_same, ps_di_diff, ps_prog_same, ps_prog_diff, ps_forced,
          ps_cache_ok, ps_hits + ps_miss);
}
LinDriver lin_patshare_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "patshare", .description = "tells the same node twice from two equal nodes",
  .caps = LIN_CAP_PREEMPT, .priority = 1,
  .wants = LIN_WANT_MATCH | LIN_WANT_STATE | LIN_WANT_RECYCLE,
  .state_new = ps_state_new, .state_free = ps_state_free, .node_recycled = ps_node_recycled,
  .match = ps_match,
};
__attribute__((constructor)) static void ps_init(void) { atexit(ps_report); }
'''

# --- probe 10: P_CYCLE -- a fixpoint is matched once, and the walk still terminates ------------
# The driver builds a real knot in its per-net state (the match phase may rewrite the net): a def
# whose body refers back to the def, which is the shape a recursive definition compiles to.  The
# return is through an AUXILIARY port, so nothing here is a redex and the core has nothing to
# fire -- the cycle simply stays.  A P_CYCLE pattern names the fixpoint and so matches it as a
# FINITE pattern; a pattern with no fixpoint and no base case, walking the same net, must be
# stopped by the matcher's in-progress set instead of spinning -- which is what the bounded step
# count below asserts.
DRIVER_PATCYCLE = PROLOGUE_PAT + r'''
LinDriver lin_patcycle_driver;
typedef struct { Port root; } Knot;
static void *pk_state_new(Net *n) {
  Knot *k = calloc(1, sizeof *k);
  if (!k) return NULL;
  Scope sc = scope_nil();
  Port v = net_alloc(n, LAM, sc);
  Port a = net_alloc(n, APP, sc);
  net_link(n, (Port){v.node, 2}, (Port){a.node, 1}, 0);   /* the body is the application */
  net_link(n, (Port){a.node, 0}, (Port){v.node, 1}, 0);   /* ... which refers back to v    */
  net_link(n, (Port){a.node, 2}, (Port){v.node, 0}, 0);   /* and one more way round        */
  k->root = v;
  return k;
}
static void pk_state_free(Net *n, void *st) { (void)n; free(st); }

/* `\v. (v's body is an APP whose principal is v)`: the fixpoint, named at slot 0. */
static const LinPat *const PK_KNOT = P_CYCLE(0, P_ALL(
  P_TAG(LAM), P_PORT(2, P_ALL(P_TAG(APP), P_PORT(0, P_CYCLE_REF(0))))));
/* No fixpoint, no base case: this walks port 2 forever on a cyclic net. */
static const LinPat pk_forever = { .kind = LIN_P_PORT, .port = 2, .a = &pk_forever };

static long pk_cycle, pk_cycused, pk_endless, pk_endused;
static int pk_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)out;
  Knot *k = st ? st : lin_driver_state(n, &lin_patcycle_driver);
  if (!k || view->npairs < 1) return 0;
  {
    LinMatch m;
    if (lin_pat_match(n, k->root, PK_KNOT, LIN_PAT_BUDGET_FOR(n), &m)) {
      pk_cycle++; pk_cycused += m.used;
    }
  }
  {
    LinMatch m;    /* 64 steps is the budget; the guard must stop this in a handful */
    if (!lin_pat_match(n, k->root, &pk_forever, 64, &m)) { pk_endless++; pk_endused += m.used; }
  }
  return 0;
}
static void pk_report(void) {
  fprintf(stderr, "[patcycle] cycle=%ld cycused=%ld endless=%ld endused=%ld\n",
          pk_cycle, pk_cycused, pk_endless, pk_endused);
}
LinDriver lin_patcycle_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "patcycle", .description = "matches a cyclic knot with P_CYCLE and terminates",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH | LIN_WANT_STATE,
  .state_new = pk_state_new, .state_free = pk_state_free,
  .match = pk_match,
};
__attribute__((constructor)) static void pk_init(void) { atexit(pk_report); }
'''

# --- probe 11: a RAW net -- no carrier name anywhere, recognised by STRUCTURE ----------------
# Part 2's recognisers exist because the runtime's encodings must be readable from structure: a raw
# net has no "_sz"/"_cl" label to consult.  This probe builds a small net with nameless nodes
# -- every node nameless -- and then (a) recognises shapes in it with the recognisers, (b) proposes
# and claims a region around one of its redexes (pairs it states itself, exits it declares itself,
# certified by `lin_claim_check`), and (c) rewrites it, reading the result back STRUCTURALLY.
#
# The two nets the recognisers cannot be allowed to confuse are built here too: the SAME wire pattern
# (LAM a with wire(a,2)={b,0}, LAM b with wire(b,2)={a,1}) is read once as a Scott numeral ZERO and
# once as the Church boolean TRUE, and the whole point is that only the caller's expectation decides
# -- so the marker reports both readings of one node, and reports that the numeral reader REFUSES the
# select-second shape.  Nothing in the region may carry a name (`named=0`), which is what makes the
# claim evidence that the region really was found from wiring alone.
DRIVER_RAWNET = PROLOGUE_PAT + r'''
LinDriver lin_rawnet_driver;

/* ---- RAW builders: net_alloc with an EMPTY carrier name everywhere ---------- */
static Port raw_num(Net *n, long k) {                    /* alloc_scott_named, unnamed */
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
static Port raw_sel(Net *n, int second) {                 /* net_alloc_bool, unnamed */
  Scope sc = scope_nil(); Port a = net_alloc(n, LAM, sc), b = net_alloc(n, LAM, sc);
  net_link(n, (Port){a.node, 2}, (Port){b.node, 0}, 0);
  net_link(n, (Port){b.node, 2}, (Port){second ? b.node : a.node, 1}, 0);
  return (Port){a.node, 0};
}
static Port raw_cell(Net *n, Port head, Port tail) {      /* the `_cl` cell, unnamed */
  Scope sc = scope_nil();
  Port c = net_alloc(n, LAM, sc), nn = net_alloc(n, LAM, sc);
  Port body = net_alloc(n, APP, sc), ia = net_alloc(n, APP, sc);
  net_link(n, (Port){c.node, 2}, (Port){nn.node, 0}, 0);
  net_link(n, (Port){nn.node, 2}, (Port){body.node, 1}, 0);
  net_link(n, (Port){body.node, 0}, (Port){ia.node, 1}, 0);
  net_link(n, (Port){ia.node, 0}, (Port){c.node, 1}, 0);
  net_link(n, (Port){ia.node, 2}, head, 0);
  net_link(n, (Port){body.node, 2}, tail, 0);
  return (Port){c.node, 0};
}
static Port raw_ffi(Net *n) {                             /* the `_ffi` header, unnamed */
  Scope sc = scope_nil();
  Port l0 = net_alloc(n, LAM, sc), l1 = net_alloc(n, LAM, sc);
  Port hdr = net_alloc(n, APP, sc), fn = net_alloc(n, APP, sc);
  net_link(n, (Port){l0.node, 2}, (Port){l1.node, 0}, 0);
  net_link(n, (Port){l1.node, 2}, (Port){hdr.node, 1}, 0);
  net_link(n, (Port){hdr.node, 0}, (Port){fn.node, 1}, 0);
  net_link(n, (Port){fn.node, 0}, (Port){l0.node, 1}, 0);
  net_link(n, (Port){fn.node, 2}, raw_sel(n, 1), 0);      /* the fn-name slot   */
  net_link(n, (Port){hdr.node, 2}, raw_sel(n, 1), 0);     /* the argument list  */
  return (Port){l0.node, 0};
}

typedef struct {
  Port num7, sel_first, sel_second, str, ffi, lam, app, sink, ru, rw, rz;
  int done, pure, det, named, cells, ffi_ok, str_n, region_nodes, region_exits, region_pairs, ok;
  int reuse, reuse_pairs, reuse_exits;
  long matches, num, as_num, as_bool, as_false, wrong, claims, acts, after;
} Raw;
static Raw rn_rep;                              /* the marker, copied out of the per-net state */

static void rn_snap(Raw *s) { Raw tmp = *s; rn_rep = tmp; }

static void *rn_state_new(Net *n) {
  Raw *s = calloc(1, sizeof *s);
  if (!s) return NULL;
  s->as_num = s->as_bool = s->as_false = s->after = -1;
  s->num7 = raw_num(n, 7);
  s->sel_first = raw_sel(n, 0);
  s->sel_second = raw_sel(n, 1);
  s->str = raw_cell(n, raw_num(n, 4), raw_cell(n, raw_num(n, 5), raw_sel(n, 1)));
  s->ffi = raw_ffi(n);
  /* the region under test: `\x.<num7>` applied to a raw numeral, with a sink as the consumer.
     It is NOT ROOT: the program's own answer must stay intact, which the test checks.  The pair is
     linked with enqueue=0, so it is never in a wave and only this driver fires it. */
  s->lam = net_alloc(n, LAM, scope_nil());
  s->app = net_alloc(n, APP, scope_nil());
  s->sink = net_alloc(n, LAM, scope_nil());
  net_link(n, (Port){s->lam.node, 2}, s->num7, 0);
  net_link(n, (Port){s->lam.node, 0}, (Port){s->app.node, 0}, 0);
  net_link(n, (Port){s->app.node, 2}, raw_num(n, 5), 0);
  net_link(n, (Port){s->app.node, 1}, (Port){s->sink.node, 0}, 0);
  /* A second region, where a LATER growth must invalidate an exit recorded earlier: u's auxiliary
     port leads to z (an exit when it is first seen) and z is then grown in through a PRINCIPAL
     boundary, which would leave that exit pointing INSIDE the region -- precisely what
     lin_claim_check refuses ("exit is internal").  The cut must drop it, so this is the shape that
     pins the "hand it straight to lin_claim_check" half of the partitioner's contract. */
  s->ru = net_alloc(n, APP, scope_nil());
  s->rw = net_alloc(n, APP, scope_nil());
  s->rz = net_alloc(n, APP, scope_nil());
  net_link(n, (Port){s->ru.node, 0}, (Port){s->rw.node, 1}, 0);
  net_link(n, (Port){s->ru.node, 1}, (Port){s->rz.node, 2}, 0);
  net_link(n, (Port){s->rw.node, 0}, (Port){s->rz.node, 0}, 0);      /* the redex inside */
  /* demand roots, so the collector (which honours them) keeps the raw nodes alive */
  lin_demand(n, s->num7); lin_demand(n, s->sel_first); lin_demand(n, s->sel_second);
  lin_demand(n, s->str); lin_demand(n, s->ffi); lin_demand(n, (Port){s->lam.node, 0});
  lin_demand(n, (Port){s->app.node, 0}); lin_demand(n, (Port){s->sink.node, 0});
  lin_demand(n, (Port){s->ru.node, 0});
  return s;
}
static void rn_state_free(Net *n, void *st) { (void)n; free(st); }

static int rn_match(Net *n, void *st, LinView *view, LinClaim *out) {
  Raw *s = st ? st : lin_driver_state(n, &lin_rawnet_driver);
  if (!s || s->done) return 0;
  LinMatch m;
  int l;
  long codes[8]; int nch = 0;
  /* What the core offers is this wave's REDEXES (`view->pairs`).  The REGION is the driver's own to
     propose: the view carries no candidate regions, so what this probe pins is that a driver that
     states its own pairs and exits gets them certified by the core's validator. */
  if (!view->pairs || view->npairs < 1) { rn_snap(s); return 0; }
  /* every recogniser, on a net whose nodes carry NO name at all */
  if (lin_pat_enc_num_nf(n, s->num7, LIN_ENC_NUM, &s->num)) s->matches++;
  if (lin_pat_enc_layer_of(n, s->num7, LIN_ENC_NUM, &l, &m) && l == LIN_L_INDUCTIVE) s->matches++;
  if (lin_pat_match(n, s->num7, lin_pat_enc_succ, LIN_PAT_BUDGET_FOR(n), &m)) s->matches++;
  /* the SAME structure under two expectations: the caller's `enc` is the only thing that can tell
     a Scott numeral from a Church boolean -- and the numeral reader must REFUSE the false shape */
  if (lin_pat_enc_num_nf(n, s->sel_first, LIN_ENC_NUM, &s->as_num)) s->matches++;
  if (lin_pat_enc_num_nf(n, s->sel_first, LIN_ENC_BOOL, &s->as_bool)) s->matches++;
  if (lin_pat_enc_num_nf(n, s->sel_second, LIN_ENC_BOOL, &s->as_false)) s->matches++;
  { long junk = -1; if (lin_pat_enc_num_nf(n, s->sel_second, LIN_ENC_NUM, &junk)) s->wrong++; }
  if (lin_pat_match(n, s->str, lin_pat_enc_cell, LIN_PAT_BUDGET_FOR(n), &m)) { s->cells++; s->matches++; }
  if (lin_pat_enc_str_nf(n, s->str, LIN_ENC_NUM, codes, 8, &nch)) {
    s->str_n = nch;
    if (nch == 2 && codes[0] == 4 && codes[1] == 5) s->matches++;
  }
  if (lin_pat_match(n, s->ffi, lin_pat_enc_ffi, LIN_PAT_BUDGET_FOR(n), &m)) { s->ffi_ok++; s->matches++; }
  /* The driver proposes its OWN region: the redex it wants plus the exits it declares.  This one
     (`ru`/`rw`/`rz`) is reached from the redex through AUXILIARY ports alone, so its closure really
     is interaction-closed and it declares no exits -- `lin_claim_check` walks the closure, finds
     `ru` through `rw`'s auxiliary port, and certifies the region as it stands.  Nothing is acted on:
     this is the validator's contract on a region a driver chose. */
  {
    LinClaim c;
    char why[160];
    memset(&c, 0, sizeof c);
    c.flags = LIN_CLAIM_REGION;
    c.npairs = 1; c.pairs[0] = (Port){s->rw.node, 0}; c.pairs[1] = (Port){s->rz.node, 0};
    s->reuse = lin_claim_check(n, &c, why, sizeof why);
    s->reuse_pairs = c.npairs; s->reuse_exits = c.nexits;
  }
  /* The region under test, again the driver's own statement: the redex plus the three auxiliary
     ports that leave it.  Validating it twice must give the same region (the walk is deterministic)
     and must not touch the net (nn and steps unchanged): a validator that forced or allocated would
     move the structure out from under the wave that is holding it. */
  {
    long nn0 = n->nn, st0 = n->steps;
    LinClaim c1, c2;
    char why[160];
    memset(&c1, 0, sizeof c1);
    c1.flags = LIN_CLAIM_REGION;
    c1.npairs = 1; c1.pairs[0] = (Port){s->lam.node, 0}; c1.pairs[1] = (Port){s->app.node, 0};
    c1.exits[0] = (Port){s->lam.node, 2};       /* the body slot: leads out to the numeral */
    c1.exits[1] = (Port){s->app.node, 1};       /* the continuation: the sink */
    c1.exits[2] = (Port){s->app.node, 2};       /* the argument */
    c1.nexits = 3;
    c2 = c1;
    int ok1 = lin_claim_check(n, &c1, why, sizeof why);
    int ok2 = lin_claim_check(n, &c2, why, sizeof why);
    s->pure = (n->nn == nn0 && n->steps == st0);
    s->det = ok1 && ok2 && c1.npairs == c2.npairs && c1.nexits == c2.nexits && c1.nnodes == c2.nnodes &&
             !memcmp(c1.nodes, c2.nodes, sizeof(int) * (size_t)c1.nnodes) &&
             !memcmp(c1.exits, c2.exits, sizeof(Port) * (size_t)c1.nexits);
    if (!ok1) { rn_snap(s); return 0; }
    s->region_nodes = c1.nnodes; s->region_exits = c1.nexits; s->region_pairs = c1.npairs;
    s->named = 0;                      /* a net carries no names at all: nothing to count */
    s->claims++;
    s->done = 1;
    *out = c1;
    rn_snap(s);
    return 1;
  }
}
static int rn_act(Net *n, void *st, LinClaim *c) {
  Raw *s = st;
  int done = 0;
  for (int i = 0; i < c->npairs; i++)
    if (net_interact(n, c->pairs[2 * i], c->pairs[2 * i + 1])) { done++; if (s) s->acts++; }
  if (s) {
    Port r = net_wire(n, s->sink);             /* the sink took the result of the rewrite */
    s->ok = lin_pat_enc_num_nf(n, r, LIN_ENC_NUM, &s->after) && s->after == 7;
    rn_snap(s);
  }
  return done;
}
static void rn_report(void) {
  fprintf(stderr, "[rawnet] matches=%ld num=%ld as_num=%ld as_bool=%ld as_false=%ld wrong=%ld "
                  "cells=%d str_n=%d ffi=%d det=%d pure=%d named=%d pairs=%d nodes=%d exits=%d "
                  "claims=%ld acts=%ld after=%ld ok=%d reuse=%d reuse_pairs=%d reuse_exits=%d\n",
          rn_rep.matches, rn_rep.num, rn_rep.as_num, rn_rep.as_bool, rn_rep.as_false, rn_rep.wrong,
          rn_rep.cells, rn_rep.str_n, rn_rep.ffi_ok, rn_rep.det, rn_rep.pure, rn_rep.named,
          rn_rep.region_pairs, rn_rep.region_nodes, rn_rep.region_exits, rn_rep.claims, rn_rep.acts,
          rn_rep.after, rn_rep.ok, rn_rep.reuse, rn_rep.reuse_pairs, rn_rep.reuse_exits);
}
LinDriver lin_rawnet_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "rawnet", .description = "recognises and rewrites structure in a raw, unannotated net",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH | LIN_WANT_STATE,
  .state_new = rn_state_new, .state_free = rn_state_free,
  .match = rn_match, .act = rn_act,
};
__attribute__((constructor)) static void rn_init(void) { atexit(rn_report); lin_driver_add(&lin_rawnet_driver); }
'''

# --- probe 12: a COMPILER net, recognised by STRUCTURE alone -------------------------------
# The same recognisers, on a net the COMPILER produced -- and a compiled net IS a raw net now: the
# compiler stamps no label on any node, so this probe is the whole evidence that nothing about the
# runtime needs one.  The driver recognizes the `_op` closure header structurally, forces its operand
# list (a compiled list is an unbuilt application until something walks it), reads the operators and
# operands as numerals of the expected encoding, claims the region and folds it.  It also reads the
# program's answer with the STRUCTURE readers only, in every run.
#
# THE ASSERTION THIS PROBE USED TO MAKE IS INVERTED.  It asserted that a stripped net could NOT be
# printed (`=> 4` must not appear), because readback identified values by ctor_tag(name).  Readback
# now takes the DOMAIN the compiler's type computed, so the same net prints `=> 4` and the structural
# read agrees.  LIN_STRIP_FOLD separates "recognises" from "recognises and folds"; the stripped=
# counter stays in the report and must be 0: there is nothing left to strip.
DRIVER_STRIPPER = PROLOGUE_PAT + r'''
static Port sp_num(Net *n, long k) {                      /* a RAW numeral: no carrier name */
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
static void sp_kill(Net *n, int v) {
  if (v < 0 || v >= n->nn || n->dead[v] || n->tag[v] == DUP) return;
  for (int p = 0; p < 3; p++) net_sever(n, (Port){v, p});
  n->dead[v] = 1;
}

static long sp_stripped, sp_hdr, sp_lists, sp_claims, sp_acts, sp_folded, sp_ops[2], sp_value, sp_answer, sp_reads;
static int sp_opcode = -1;
static int  sp_answer_ok, sp_lam, sp_app;

typedef struct { long ops[4]; int nops, seen, opcode; } St;
LinDriver lin_stripper_driver;

static void *sp_state_new(Net *n) { (void)n; return calloc(1, sizeof(St)); }
static void sp_state_free(Net *n, void *st) { (void)n; free(st); }

/* The operand list of a saturated `_op`, read STRUCTURALLY: a cell chain whose FIRST slot is the
   OPERATOR INDEX (std/num.lin writes it from the language's op vocabulary) and whose remaining slots
   are the operands, each read as a numeral of the encoding the caller expects. */
static int sp_read_ops(Net *n, Port p, long *ops, int *nout, int *opcode) {
  int k = 0;
  for (int step = 0; step < 64; step++) {
    LinMatch m;
    if (lin_pat_match(n, p, lin_pat_enc_cell, LIN_PAT_BUDGET_FOR(n), &m)) {
      long v;
      if (!lin_pat_enc_num_nf(n, m.bind[4], LIN_ENC_NUM, &v)) return 0;
      if (k == 0) *opcode = (int)v;                   /* slot 0: WHICH operator this is */
      else { if (k > 4) return 0; ops[k - 1] = v; }
      k++;
      p = m.bind[5];
      continue;
    }
    if (lin_pat_match(n, p, lin_pat_enc_second, LIN_PAT_BUDGET_FOR(n), &m)) { *nout = k - 1; return k > 1; }
    return 0;
  }
  return 0;
}

/* The answer at the program's own result port, read with the STRUCTURE readers only and with no
   forcing at all: a value that is not yet a normal form declines, so a mid-reduction read cannot
   latch a wrong number.  The last successful read is the answer. */
static void sp_read_answer(Net *n) {
  Port r = net_wire(n, (Port){0, 0});
  long v = -1;
  sp_reads++;
  if (lin_pat_enc_num_nf(n, r, LIN_ENC_NUM, &v)) { sp_answer = v; sp_answer_ok = 1; }
}

static int sp_match(Net *n, void *st, LinView *view, LinClaim *out) {
  St *s = st ? st : lin_driver_state(n, &lin_stripper_driver);
  if (!s) return 0;
  if (!s->seen) s->seen = 1;
  sp_read_answer(n);
  if (sp_folded) return 0;
  for (int i = 0; i < view->npairs; i++) {
    LinMatch m;
    char why[160];
    LinClaim c;
    if (!lin_pat_match_pair(n, view->pairs[2 * i], view->pairs[2 * i + 1], lin_pat_enc_op,
                            LIN_PAT_BUDGET_FOR(n), &m))
      continue;
    sp_hdr++;
    /* Forcing is legal in the match phase, and the re-read afterwards is the interpreter's own
       discipline (forcing can consume the node the port names).  Only a list whose two payloads are
       the numerals this probe folds is the redex it wants: the header SHAPE cannot say which op it
       is, and a raw net cannot tell it either -- which op is the caller's expectation. */
    Port cur = net_force_val(n, m.bind[2]);
    s->nops = 0;
    if (!sp_read_ops(n, cur, s->ops, &s->nops, &s->opcode)) continue;
    sp_opcode = s->opcode;                          /* WHICH operator, stated by the net itself */
    sp_lists++;
    if (s->nops != 2) continue;
    if (!getenv("LIN_STRIP_FOLD")) continue;        /* recognised; the core reduces it itself */
    /* The region the driver proposes: the `_op` redex it matched, with the four auxiliary ports
       that leave it (the marker binder, the body, the continuation and the operand spine).  The
       core validates it; there is no candidate cut to receive it from. */
    memset(&c, 0, sizeof c);
    c.flags = LIN_CLAIM_REGION;
    c.npairs = 1;
    c.pairs[0] = (Port){m.bind[0].node, 0}; c.pairs[1] = (Port){m.bind[1].node, 0};
    c.exits[0] = (Port){m.bind[0].node, 1}; c.exits[1] = (Port){m.bind[0].node, 2};
    c.exits[2] = (Port){m.bind[1].node, 1}; c.exits[3] = (Port){m.bind[1].node, 2};
    c.nexits = 4;
    if (!lin_claim_check(n, &c, why, sizeof why)) continue;
    sp_lam = m.bind[0].node; sp_app = m.bind[1].node;
    sp_opcode = s->opcode;                          /* WHICH operator, stated by the net itself */
    sp_ops[0] = s->ops[0]; sp_ops[1] = s->ops[1];
    sp_claims++;
    *out = c;
    return 1;
  }
  return 0;
}

static int sp_act(Net *n, void *st, LinClaim *c) {
  (void)c; (void)st;
  if (!sp_claims || sp_folded) return 0;
  /* the fold: the operands came from the structure, the result is built as a RAW numeral */
  sp_value = sp_ops[0] * sp_ops[1];
  Port res = sp_num(n, sp_value);
  Port ar = net_wire(n, (Port){sp_app, 1});
  if (ar.node >= 0 && ar.node < n->nn && !n->dead[ar.node]) net_link(n, res, ar, 1);
  else net_link(n, res, (Port){sp_app, 1}, 1);
  sp_kill(n, sp_lam); sp_kill(n, sp_app);
  sp_folded++; sp_acts++;
  sp_read_answer(n);
  return 1;
}
static void sp_report(void) {
  fprintf(stderr, "[strip] stripped=%ld op_hdr=%ld lists=%ld ops=%ld,%ld opcode=%d value=%ld "
                  "claims=%ld acts=%ld answer=%ld answer_ok=%d reads=%ld\n",
          sp_stripped, sp_hdr, sp_lists, sp_ops[0], sp_ops[1], sp_opcode, sp_value, sp_claims,
          sp_acts, sp_answer, sp_answer_ok, sp_reads);
}
LinDriver lin_stripper_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "stripper", .description = "clears every carrier name, then recognises by structure",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH | LIN_WANT_STATE,
  .state_new = sp_state_new, .state_free = sp_state_free,
  .match = sp_match, .act = sp_act,
};
__attribute__((constructor)) static void sp_init(void) { atexit(sp_report); lin_driver_add(&lin_stripper_driver); }
'''

PROGRAM = '''(load "std/drivers/driver.lin")
(set_driver "%s")
((\\x x) (mul 2 2))
'''
REJECT = "rejected"
VALUE = re.compile(r"^=> .+", re.M)


def run(argv, timeout=120, env=None):
    try:
        p = subprocess.run(argv, capture_output=True, text=True, timeout=timeout,
                           stdin=subprocess.DEVNULL, env=env)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return -9, "", "TIMEOUT"


def main():
    if len(sys.argv) < 3:
        print(__doc__.strip().splitlines()[-1])
        return 2
    lin, std_dir = os.path.abspath(sys.argv[1]), os.path.abspath(sys.argv[2])
    cc = shutil.which("cc") or shutil.which("gcc")
    if not cc:
        print("parallel_guard: SKIPPED (no cc/gcc to build the probe drivers); the driver-failure "
              "paths are untested in this environment")
        return 0
    # `lin.h` comes from the SOURCE tree, which is not where the installed std is: a packaged run
    # (nix's test derivation) has `$out/bin` and `$out/share/lin/std` but no `src/`.  The test file
    # itself lives beside the header, so that is the lookup that works in both.
    here = os.path.dirname(os.path.abspath(__file__))
    hdr = None
    for cand in (os.path.join(here, os.pardir, "src", "lin.h"),
                 os.path.join(os.path.dirname(std_dir), "src", "lin.h")):
        if os.path.exists(cand):
            hdr = os.path.abspath(cand)
            break
    if not hdr:
        print("parallel_guard: SKIPPED (src/lin.h not found; the probe drivers cannot be built)")
        return 0
    tmp = tempfile.mkdtemp()
    std = os.path.join(tmp, "std")
    shutil.copytree(std_dir, std, symlinks=True)
    for d, _, _ in os.walk(std):
        os.chmod(d, 0o755)          # a packaged std is read-only; the probes are written into it
    inc = os.path.join(tmp, "inc")
    os.makedirs(inc)
    shutil.copy(hdr, inc)
    env = dict(os.environ, LIN_STD=os.path.join(std, "std.lin"), LIN_STD_DIR=std)
    bad = []

    def build(name, source):
        c = os.path.join(std, "drivers", name + ".c")
        so = os.path.join(std, "drivers", name + ".so")
        with open(c, "w") as fh:
            fh.write(source)
        rc, _, err = run([cc, "-O2", "-std=c99", "-fopenmp", "-fPIC", "-shared", "-I", inc,
                          "-o", so, c, "-ldl", "-lm"])
        return None if (rc == 0 and os.path.exists(so)) else err.strip().split("\n")[0][:160]

    # -- 1. an ABI-2 plugin is rejected loudly ----------------------------------------------
    why = build("abiprobe", DRIVER_ABI2)
    if why:
        print("parallel_guard: SKIPPED (ABI probe did not compile: %s)" % why)
        return 0
    prog = os.path.join(tmp, "abi.lin")
    with open(prog, "w") as fh:
        fh.write(PROGRAM % "abiprobe")
    rc, out, serr = run([lin, prog], env=env)
    if REJECT not in serr:
        bad.append("an ABI-2 plugin was not rejected; the core would read a struct the plugin does "
                   "not have (rc=%d, stderr=%r)" % (rc, serr.strip()[-200:]))
    if "=> 4" not in out:
        bad.append("with the ABI-2 plugin rejected the core still had to compute the answer itself "
                   "(the base engine is complete without any driver); got %r" % out.strip()[-120:])

    # -- 2. a driver that claims everything must not make the run hang ---------------------
    why = build("noprog", PROBE_BODY)
    if why:
        print("parallel_guard: SKIPPED (no-progress probe did not compile: %s)" % why)
        return 0
    prog2 = os.path.join(tmp, "noprog.lin")
    with open(prog2, "w") as fh:
        fh.write(PROGRAM % "noprog")
    rc, out, _ = run([lin, "-t", "1", prog2], timeout=120, env=env)
    if rc == -9:
        bad.append("a driver that claims every redex and never progresses left the run HANGING "
                   "(timeout): net_reduce must stop as soon as a wave makes no progress")
    elif rc != 0:
        bad.append("the no-progress run exited %d; a driver that declines to reduce must leave the "
                   "run terminating and reporting, not failing (stdout=%r)" % (rc, out.strip()[-160:]))

    # -- 3/4. the capability contract ------------------------------------------------------
    for name, src, want in (("wantprobe", DRIVER_UNKNOWN_WANT, "capability"),
                            ("shortprobe", DRIVER_SHORT_STRUCT, "does not implement")):
        why = build(name, src)
        if why:
            print("parallel_guard: SKIPPED (%s probe did not compile: %s)" % (name, why))
            return 0
        p = os.path.join(tmp, name + ".lin")
        with open(p, "w") as fh:
            fh.write(PROGRAM % name)
        rc, out, serr = run([lin, p], env=env)
        if REJECT not in serr or want not in serr:
            bad.append("a plugin requiring a %s the core cannot supply was not refused with a "
                       "reason (rc=%d, stderr=%r)" % (want, rc, serr.strip()[-200:]))
        if "=> 4" not in out:
            bad.append("a refused %s probe must not stop the run from computing its answer "
                       "(got %r)" % (want, out.strip()[-120:]))

    # -- 5/6/7. the claim protocol ---------------------------------------------------------
    for name, src, prog, want in (
            ("matchprobe", DRIVER_MATCH, '((\\x x) (mul 2 2))', "=> 4"),
            ("badregion", DRIVER_BADREGION, '((\\x x) (mul 2 2))', "=> 4"),
            ("heldprobe", DRIVER_HELD, '(mul (mul 4 4) (mul 4 4))', "=> 256")):
        why = build(name, src)
        if why:
            print("parallel_guard: SKIPPED (%s probe did not compile: %s)" % (name, why))
            return 0
        p = os.path.join(tmp, name + ".lin")
        with open(p, "w") as fh:
            fh.write(PROGRAM % name + prog + "\n")
        rc, out, serr = run([lin, p], env=env)
        if want not in out:
            bad.append("%s: the answer through the claim protocol is wrong (want %r, got %r)"
                       % (name, want, out.strip()[-160:]))
        if name == "matchprobe":
            m = re.search(r"\[matchprobe\] acts=(\d+)", serr)
            if not m or int(m.group(1)) < 1:
                bad.append("matchprobe never acted through the claim protocol (stderr=%r)" % serr.strip()[-160:])
        if name == "badregion":
            if "claim refused" not in serr:
                bad.append("a region with an exit at a PRINCIPAL port was not refused (stderr=%r)"
                           % serr.strip()[-160:])
        if name == "heldprobe":
            m = re.search(r"\[heldprobe\] acts=(\d+) reval=(\d+)", serr)
            if not m or int(m.group(1)) < 2 or int(m.group(2)) < 1:
                bad.append("a held claim was not carried across a wave and acted on later (stderr=%r)"
                           % serr.strip()[-160:])

    # -- 8/9/10. the shared matcher (std/runtime/pattern.h) --------------------------------
    # A driver that recognizes structure gets its patterns from the library instead of
    # hand-rolling the walk; what is asserted here is what the library promises: a match can
    # drive the claim protocol, matching is PURE, sharing is NODE identity, and a cyclic net
    # is matched -- not unrolled -- so the walk terminates.
    for name, src in (("patclaim", DRIVER_PATCLAIM),
                      ("patshare", DRIVER_PATSHARE),
                      ("patcycle", DRIVER_PATCYCLE)):
        why = build(name, src)
        if why:
            print("parallel_guard: SKIPPED (%s probe did not compile: %s)" % (name, why))
            return 0

    def matcher_run(name, prog, want):
        p = os.path.join(tmp, name + ".lin")
        with open(p, "w") as fh:
            fh.write(PROGRAM % name + prog + "\n")
        rc, out, serr = run([lin, p], env=env)
        if want not in out:
            bad.append("%s: the answer through the matcher is wrong (want %r, got %r)"
                       % (name, want, out.strip()[-160:]))
        return rc, out, serr

    # 8. match -> lin_pat_claim -> lin_claim_check -> act, and the matcher never mutates.
    _, _, serr = matcher_run("patclaim", '((\\x x) (mul 2 2))', "=> 4")
    m = re.search(r"\[patclaim\] claims=(\d+) acts=(\d+) region=(\d+) plain=(\d+) pure=(\d+) impure=(\d+)", serr)
    if not m:
        bad.append("patclaim never reported through the matcher (stderr=%r)" % serr.strip()[-200:])
    else:
        claims, acts, region, _plain, pure, impure = (int(x) for x in m.groups())
        if claims < 1 or acts < 1:
            bad.append("a pattern match did not reach the claim protocol (claims=%d acts=%d)" % (claims, acts))
        if region < 1:
            bad.append("lin_pat_claim did not produce a REGION claim the core certifies: the exits it "
                       "derives from the matched nodes were never accepted (region=%d, stderr=%r)"
                       % (region, serr.strip()[-200:]))
        if pure < 1 or impure:
            bad.append("the matcher is not pure: a match that declined changed nn/steps "
                       "(pure=%d impure=%d)" % (pure, impure))

    # 9. P_BIND/P_REF: one node reached at two ports is sharing; two equal nodes are not.
    _, _, serr = matcher_run("patshare", '(mul 2 2)', "=> 4")
    m = re.search(r"\[patshare\] shared_same=(\d+) shared_diff=(\d+) distinct_same=(\d+) "
                  r"distinct_diff=(\d+) prog_same=(\d+) prog_diff=(\d+) forced=(\d+) "
                  r"cache_ok=(\d+) lookups=(\d+)", serr)
    if not m:
        bad.append("patshare never reported (stderr=%r)" % serr.strip()[-200:])
    else:
        sh_same, sh_diff, di_same, di_diff, pg_same, pg_diff, cache_ok, lookups = (
            int(m.group(k)) for k in (1, 2, 3, 4, 5, 6, 8, 9))
        if sh_same < 1 or sh_diff:
            bad.append("a spine whose two slots are the SAME node (one node at two ports) was not "
                       "recognized as sharing (shared_same=%d shared_diff=%d)" % (sh_same, sh_diff))
        if di_same or di_diff < 1:
            bad.append("two EQUAL but distinct nodes were not told apart from one shared node "
                       "(distinct_same=%d distinct_diff=%d)" % (di_same, di_diff))
        if pg_diff < 1 or pg_same:
            bad.append("the same two patterns did not separate the two operands of a spine the "
                       "COMPILER built (prog_same=%d prog_diff=%d)" % (pg_same, pg_diff))
        if lookups < 1:
            bad.append("the matcher's per-net cache was never consulted on a real wave")
        if not cache_ok:
            bad.append("the per-net match cache did not honour its contract: a hit, and no hit "
                       "after the slot was recycled or the region was released")

    # 10. P_CYCLE matches a knot and terminates; an unbounded pattern is stopped, not hung.
    _, _, serr = matcher_run("patcycle", '((\\x x) (mul 2 2))', "=> 4")
    m = re.search(r"\[patcycle\] cycle=(\d+) cycused=(\d+) endless=(\d+) endused=(\d+)", serr)
    if not m:
        bad.append("patcycle never reported (stderr=%r)" % serr.strip()[-200:])
    else:
        cycle, endless, endused = int(m.group(1)), int(m.group(3)), int(m.group(4))
        if cycle < 1:
            bad.append("a P_CYCLE pattern did not match the cyclic structure")
        if endless < 1:
            bad.append("a pattern with no fixpoint was not declined on the cyclic net")
        elif endused > 16 * endless:
            bad.append("the cyclic walk was stopped by the step BUDGET (%d steps over %d attempts), "
                       "not by the in-progress guard: the walk is not terminating structurally"
                       % (endused, endless))

    # -- 11. a RAW net recognised, claimed and rewritten by structure alone ---------------------
    # Every node is built with an empty carrier name, so nothing the recognisers do can come from
    # `name[]`; the region is the driver's own statement about wiring (one redex plus its auxiliary
    # exits), certified by the claim protocol, and the result of the rewrite is read back with the
    # same structural readers.
    why = build("rawnet", DRIVER_RAWNET)
    if why:
        print("parallel_guard: SKIPPED (rawnet probe did not compile: %s)" % why)
        return 0
    _, out, serr = matcher_run("rawnet", '((\\x x) (mul 2 2))', "=> 4")
    m = re.search(r"\[rawnet\] matches=(\d+) num=(-?\d+) as_num=(-?\d+) as_bool=(-?\d+) "
                  r"as_false=(-?\d+) wrong=(\d+) cells=(\d+) str_n=(\d+) ffi=(\d+) det=(\d+) "
                  r"pure=(\d+) named=(\d+) pairs=(\d+) nodes=(\d+) exits=(\d+) claims=(\d+) "
                  r"acts=(\d+) after=(-?\d+) ok=(\d+) reuse=(\d+) reuse_pairs=(\d+) "
                  r"reuse_exits=(\d+)", serr)
    if not m:
        bad.append("rawnet never reported (stderr=%r)" % serr.strip()[-200:])
    else:
        (ran_matches, ran_num, ran_asnum, ran_asbool, ran_asfalse, ran_wrong, ran_cells, ran_strn,
         ran_ffi, ran_det, ran_pure, ran_named, ran_pairs, ran_nodes, ran_exits, ran_claims,
         ran_acts, ran_after, ran_ok, ran_reuse, ran_rpairs, ran_rexits) = (int(x) for x in m.groups())
        if ran_matches < 6 or ran_num != 7:
            bad.append("the structural recognisers did not read the RAW numeral 7 (matches=%d num=%d, "
                       "stderr=%r)" % (ran_matches, ran_num, serr.strip()[-160:]))
        if not (ran_asnum == 0 and ran_asbool == 1):
            bad.append("the SAME structure was not readable under two expectations: as a numeral the "
                       "select-first shape is 0 (%d) and as a boolean it is true (%d) -- this is the "
                       "pair that no structural test may try to tell apart" % (ran_asnum, ran_asbool))
        if ran_asfalse != 0 or ran_wrong:
            bad.append("the expected encoding was not respected: the numeral reader must REFUSE the "
                       "select-second shape (it accepted it %d time(s)) and the boolean reader must "
                       "read it as false (it read %d)" % (ran_wrong, ran_asfalse))
        if ran_cells < 1 or ran_strn != 2 or ran_ffi < 1:
            bad.append("the cons cell / string cell / `_ffi` header were not recognised from "
                       "structure alone (cells=%d str_n=%d ffi=%d)" % (ran_cells, ran_strn, ran_ffi))
        if not ran_det or not ran_pure:
            bad.append("lin_claim_check must be deterministic and must not mutate the net "
                       "(det=%d pure=%d)" % (ran_det, ran_pure))
        if ran_named:
            bad.append("the region contains %d NAMED nodes: this probe's net has no names, so the "
                       "cut did not come from wiring alone" % ran_named)
        if not (ran_pairs == 1 and ran_nodes == 2 and ran_exits == 3 and ran_claims == 1):
            bad.append("the driver's own region was not certified as stated (pairs=%d nodes=%d "
                       "exits=%d claims=%d): one redex plus its three auxiliary exits must certify "
                       "to that region through lin_claim_check" % (ran_pairs, ran_nodes, ran_exits, ran_claims))
        if ran_acts != 1 or ran_after != 7 or not ran_ok:
            bad.append("the rewrite of the raw region did not produce the right result "
                       "(acts=%d after=%d ok=%d)" % (ran_acts, ran_after, ran_ok))
        if not ran_reuse or ran_rpairs != 1 or ran_rexits != 0:
            bad.append("a region a driver declared CLOSED (no exits) was not certified "
                       "(reuse=%d pairs=%d exits=%d): the validator must walk the closure through the "
                       "auxiliary ports and accept a region nothing leaves" % (ran_reuse, ran_rpairs, ran_rexits))

    # -- 12. a name-stripped compiler net --------------------------------------------------------
    # The same structure readers, over a net the compiler built and every `name[]` entry cleared.
    # Run three ways: untouched (the core's own answer), stripped without folding (the program's own
    # reduction, read structurally), and stripped with a structural fold.
    why = build("stripper", DRIVER_STRIPPER)
    if why:
        print("parallel_guard: SKIPPED (stripper probe did not compile: %s)" % why)
        return 0

    def strip_run(tag, env_extra, prog='(mul 2 2)', want="=> 4"):
        p = os.path.join(tmp, "strip_%s.lin" % tag)
        with open(p, "w") as fh:
            fh.write(PROGRAM % "stripper" + prog + "\n")
        e = dict(env, **env_extra)
        rc, out, serr = run([lin, p], env=e)
        m = re.search(r"\[strip\] stripped=(\d+) op_hdr=(\d+) lists=(\d+) ops=(-?\d+),(-?\d+) "
                      r"opcode=(-?\d+) value=(-?\d+) claims=(\d+) acts=(\d+) answer=(-?\d+) "
                      r"answer_ok=(\d+) reads=(\d+)", serr)
        return out, serr, (tuple(int(x) for x in m.groups()) if m else None)

    # 12a. the compiler's net: the core prints the answer, and the structural reader agrees.
    out, serr, g = strip_run("plain", {})
    if "=> 4" not in out:
        bad.append("a compiled net must print its answer (got %r)" % out.strip()[-160:])
    if not g:
        bad.append("stripper never reported (stderr=%r)" % serr.strip()[-200:])
    elif g[0] != 0:
        bad.append("a net has no carrier names left to clear (stripped=%d)" % g[0])

    # 12b. the same net, recognised only by STRUCTURE: the program's own reduction is unchanged, the
    # structural read of the answer says 4, AND -- the inversion this probe exists for -- readback
    # writes it as `=> 4`, because main.c hands it the domain the compiler's type computed.
    out_ns, serr_ns, g = strip_run("nofold", {})
    if not g:
        bad.append("stripper never reported on the structural run (stderr=%r)" % serr_ns.strip()[-200:])
    else:
        stripped, op_hdr, lists, o0, o1, opcode, value, claims, acts, answer, answer_ok = g[:11]
        if stripped != 0:
            bad.append("a net carries no carrier names, so nothing may be cleared (stripped=%d)"
                       % stripped)
        if op_hdr < 1 or lists < 1:
            bad.append("a structural driver no longer recognises the `_op` header and its operand "
                       "list (op_hdr=%d lists=%d)" % (op_hdr, lists))
        if opcode != 1:
            bad.append("the operator's INDEX must come out of the net's own operand list (the "
                       "program is a `mul`, LIN_OP_MUL == 1; got opcode=%d)" % opcode)
        if not answer_ok or answer != 4:
            bad.append("the program's answer is still 4 by the core's own rules, read structurally "
                       "(got answer=%d answer_ok=%d)" % (answer, answer_ok))
        if "=> 4" not in out_ns:
            bad.append("readback no longer prints `=> 4` for a net with no labels: the compiler's "
                       "type is what states the result's domain, so it must (stdout=%r)"
                       % out_ns.strip()[-160:])

    # 12c. the same, folded by the structural driver: the recognisers drive a real fold.
    out_f, serr_f, g = strip_run("fold", {"LIN_STRIP_FOLD": "1"})
    if not g:
        bad.append("stripper never reported on the folded run (stderr=%r)" % serr_f.strip()[-200:])
    else:
        stripped, op_hdr, lists, o0, o1, opcode, value, claims, acts, answer, answer_ok = g[:11]
        if op_hdr < 1 or lists < 1 or (o0, o1) != (2, 2):
            bad.append("the `_op` header and its two operands were not recognised structurally "
                       "(op_hdr=%d lists=%d ops=%d,%d)" % (op_hdr, lists, o0, o1))
        if value != 4 or claims < 1 or acts < 1:
            bad.append("the structural fold did not claim its region and fold (value=%d claims=%d "
                       "acts=%d)" % (value, claims, acts))
        if not answer_ok or answer != 4:
            bad.append("the folded result read structurally is wrong (answer=%d answer_ok=%d)"
                       % (answer, answer_ok))

    if bad:
        for b in bad:
            print("FAIL " + b)
        print("parallel_guard: %d problem(s)" % len(bad))
        return 1
    print("parallel_guard: OK (an ABI-2 plugin is rejected instead of read past its end; a driver "
          "that claims every redex and never progresses terminates the run; a plugin requiring a "
          "capability the core cannot supply, or one that does not fit its own struct, is refused "
          "with a reason and the run still computes its answer; a match/act driver claims a region "
          "and the base engine leaves it alone; a bad region is refused; a held claim survives a "
          "wave and is acted on later without losing the work; a pattern match drives the claim "
          "protocol with the exits derived from what it matched; matching is pure; P_BIND/P_REF "
          "tells one shared node from two equal ones; P_CYCLE matches a knot and terminates; a net "
          "built by hand, with no name on any node, is recognised by structure, has its own region "
          "certified by the claim protocol, is rewritten, and the result is read back structurally; a "
          "COMPILER net carries no labels either -- the `_op` header, the operator INDEX inside its "
          "operand list and the operands themselves are all recognised structurally, the program's "
          "reduction answer is unchanged (4), and readback PRINTS it as `=> 4` from the domain the "
          "compiler's type computed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
