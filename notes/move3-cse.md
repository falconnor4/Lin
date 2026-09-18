# Move 3 (SHARING AS AN E-GRAPH DECISION): CSE → fan introduction, measured

Status: **implemented, measured, and reverted.**  The pass worked, and it made the
AOT artifacts dramatically worse.  Recording the numbers and the reason so the next
attempt starts from the finding instead of repeating it.

## What was built

A term-level CSE pass (`cse_share`, ~200 lines in `src/compile.c`) run in `do_build`
right after `egraph_optimize`, motivated by a real gap: the e-graph *discovers*
equality and then throws the sharing away, because `eg_extract` rebuilds a TREE — a
class with two parents is emitted twice.  The pass put the sharing back as variables,
which `compile` turns into DUP fans via `ct`'s existing `dup_tree`.

It analyses the expanded term into structural classes (hash-consed on
`type/name/child-class`), counts occurrences, and for each class with `count >= 2` and
`cost >= 4` inserts one binding at the **lowest common ancestor** of the occurrences.

## Six real bugs found while getting it to fire

Worth keeping, because each was silent:

1. `closed`-only sharing found nothing: `expand_defs` inlines every callee, so
   arguments always sit *under* the callee's own lambdas.  Measured: 104 repeated
   classes, **0** with `cost >= 4`.
2. A depth-equality gate ("never hoist past a binder") rejected everything for the same
   reason.  Relaxed deliberately: an unused binder is **erased** by `ct` (its port is left
   dangling), so hoisting cannot force evaluation of a sub-term whose binder is unused —
   the strictness hazard is handled by erasure, not by refusing to hoist.  Capture is
   handled separately by requiring the sub-term's free variables to be in scope at the
   LCA and unshadowed between the LCA and each occurrence.
3. `cse_occ_head`/`cse_ins_next` were allocated *before* `cse_close`, which **adds
   classes** — writing past the allocation (silent crash, no artifact produced).
4. The class hash was fixed at 1024 slots while interning one class per node (~27k);
   a full table makes the probe loop never find an empty slot — an infinite hang.
   Needs rehashing with a load factor.
5. A class whose representative sits on its own insertion path re-applied its own
   binding forever — infinite recursion.  Guarded with `c == self`.
6. LCA equalised by *lambda* depth instead of **tree** depth, so the parent walk
   overran the root and returned -1 for every candidate; and tree depth was then
   assigned by the parent *after* the subtree walk, giving grandchildren wrong values.
   It must be passed down at push time.

After those, on `scratch/progs/cse.lin` (`(add (mul 6 7) (mul 6 7))`):

```
[aot] cse: 221 sub-terms shared, 618479 nodes of duplicate work removed
[aot] compile: 61524 -> 2230 nodes      (27x smaller)
```

## Why it was reverted: the artifact gets much worse

Correctness held throughout (`CSE_OK: 84`, and `line_ffi`'s `FFI_LINE_OK: 144`).  The
problem is the **residual**, measured against the committed no-CSE build (which already
compacts with `net_gc`):

| artifact | no CSE | with CSE |
|---|---|---|
| `line_binary.line` | 106,243 B / 3,835 nodes | **309,113 B / 11,668 nodes** |
| `line_ffi.line` | 92,853 B / 3,397 nodes | **2,785,843 B / 107,258 nodes** |
| `line_ffi` build-time steps | 114,909 | 173,004 |

Three times worse on one test and **thirty times worse** on the other, and *more*
build-time reduction on both.  The reason is structural: sharing turns a duplicated
computation into a **thunk referenced by a fan**.  Once the value has been consumed, the
un-shared version has nothing left to keep — each copy reduced to a constant and was
erased — whereas the shared version leaves the fan and the sub-net behind it still
*reachable*, so `net_gc` (correctly) cannot reclaim it, and the container — which stores
every node — serialises it.

## What has to exist first

This is the "erasure is passive" gap DESIGN.md already records: `net_interact` has no
ε×δ rule, so an ERA meeting a DUP is dropped and erasure happens only by leaving ports
dangling.  A fan whose auxiliaries are both consumed therefore never goes away, and
sharing cannot pay.  So the ordering is:

1. **active erasure (ε×δ propagation) in the core.**  ε is already one of the four core
   rules, and it is currently inert — this is the rule doing its job, not a new rule.
   DESIGN.md warns the naive "erase both auxiliaries" form is unsound when a fan
   straddles an erase boundary, so the gauge discipline has to be respected.
2. re-land CSE and re-measure; it should then be able to show a *smaller* residual,
   which is the whole point.

Until then, CSE is a pass that shrinks the compiled net 27× and makes the shipped
artifact 30× bigger, so it does not ship.  The pass source is in this note's history
rather than the tree; the six bug notes above are the expensive part and they are kept.

## CORRECTION: active erasure is NOT what sharing was waiting for

I hypothesised that a spent fan was pinning the shared sub-net, so making erasure
active (ε×δ / ε×γ, now landed in the core and suite- and oracle-green) would let
CSE pay.  **That is falsified.**  Re-measured with active erasure in the core:

| artifact | no CSE | with CSE (active erasure) |
|---|---|---|
| `line_binary.line` | 106,243 B / 3,832 nodes | 309,113 B / 11,668 nodes |
| `line_ffi.line` | 92,853 B / 3,397 nodes | 2,785,843 B / 107,258 nodes |

Identical to the pre-erasure numbers — erasure changed nothing here, and CSE still
*increases* build-time work (`line_ffi`: 114,909 → 173,004 steps).  The rewrite also
regressed correctness (`FFI_LINE_OK: 144` → `?`), so it was reverted a second time.

## The real cause: a fan COPIES, it does not SHARE

`ε×δ` cannot help because the problem is not that spent fans linger.  It is that a fan
meeting a redex *commutes* — γ⋈δ turns one redex into **two** — so CSE's "shared"
sub-term is not reduced once and read twice; it is duplicated into two computations that
then each reduce.  That is exactly the measured signature: more steps and a bigger
residual, while the compiled net is 27× smaller (the duplication is deferred into the
fan instead of being materialised at compile time).

Genuine sharing requires the two copies to be **identified when they meet**, which is
what Lamping's brackets/abstractors exist for: the fan carries an identifier, the
abstractor guards the term, and when the two copies are recognised the fan annihilates
and the work collapses to one reduction.  Lin's gauges + `scope_meet` are the *level*
discipline and are landed and oracle-green, but there are no brackets or abstractors —
which is precisely DESIGN.md's "optimal for acyclic sharing; full Levy-optimality for
cyclic sharing needs the bracket machinery, which belongs in a driver, not the core".

**So the order was wrong, and this is the correction that matters:** CSE is a *decision*
about what to share, and a decision is worthless without a *discipline* that makes
sharing actually share.  The bracket/abstractor strategy (a driver, per the Move 4 spec:
"brackets/abstractors only as a driver-level Levy strategy, never in the core") has to
exist FIRST; only then can a sharing decision be measured, let alone be profitable.

Active erasure stays: it is one of the four core rules, it was inert, and it is now
doing its job against the full suite and the independent oracle.  It is just not the
thing that unblocks sharing.

## Tree sharing: measured properly, and my label hypothesis is dead

Active erasure is REVERTED (`f23f572`).  It did not pay, and the only reason to carry
it would have been the knot; it is a clean revert if the knot later needs it.

### Sharing works, and gets better with more uses

My earlier "copying vs sharing" table was built on an additive model (M per mul, A per
add) that I never validated -- and `(mul 6 7)` alone is 21,661 steps while two of them in
context measured 129,009, so the model was simply wrong.  Re-measured against real
baselines, with the computation WRITTEN OUT rather than predicted (pure beta, no arith
driver, so steps reflect sharing rather than folding):

| uses of a let-bound value | copy (written out) | shared | ratio |
|---|---|---|---|
| 2 | 129,009 | 71,041 | 0.55 |
| 3 | 581,837 | 230,124 | 0.40 |
| 4 | 795,577 | 268,007 | 0.34 |

So fan-based tree sharing WORKS, and its advantage GROWS with the number of uses.  There
is no "degrades to copying at 3+" defect, and therefore no support for the fan-tree gauge
collision I proposed to fix -- so that fix was NOT implemented.  (For the record the code
fact is real: `dup_tree` gives every DUP in one tree the same `sc`, while DESIGN.md says a
gauge must identify exactly one sharing point.  The data says it does not matter here.)

### The real anomaly: cost is wildly shape-sensitive at EQUAL use count

Same value, same number of uses, same number of `add`s -- only the association differs:

| shape | uses | steps |
|---|---|---|
| `(add (add v v) v)`   | 3 | 230,124 |
| `(add v (add v v))`   | 3 | **92,172** |
| `(add (add v v) (add v v))` | 4 | 268,007 |
| `(add v (add v (add v v)))` | 4 | **121,535** |

2.2-2.5x on identical work.  A bare `add` is 431 steps, so this is not the adds: some
shapes are duplicating the shared computation.  Marginals per extra use are also
non-monotonic (159k, 518k, 93k for one extra `add`).

### What is NOT established (do not build on it)

The four shapes above differ in *add association*, so this measurement does NOT isolate
whether the cause is (a) the fan tree `dup_tree` builds, (b) the ORDER in which uses
consume their copies, or (c) add association itself.  The isolating experiment is to hold
the term fixed and change ONLY `dup_tree`, and separately hold the fan tree fixed and vary
only the association.  That experiment has NOT been run.

Working hypothesis, explicitly unproven: the engine reduces in a fixed wave order, so a
fan can duplicate a still-UNREDUCED redex before that redex is reduced, and a later use
then redoes the work.  That is exactly the failure Levy-optimal reduction exists to avoid
-- fan out AFTER reducing, not before -- which would put the real optimality work in
reduction ORDER and the fan/copy discipline, not in fan labels.  If that is right, it is
also why CSE (which creates the multi-use sharing in the first place) increased work: it
creates sharing that the engine then re-duplicates.

## Isolated: the fan tree is NOT the cause -- cost is a REDUCTION-ORDER property

Ran the isolating experiment.  `dup_tree` was given a switchable variant that feeds the
shared value to the DUP serving the FIRST use instead of the LAST (`LIN_DUPTREE=1`), i.e.
the only thing varied is which end of the caterpillar the value arrives at and therefore
which use receives its copy first.  Same term, same use count, same fan count.

    term                          default   fan-tree reversed
    (add (add v v) v)             230124    230124
    (add v (add v v))              92172     92172
    (add (add v v) (add v v))     268007    268007
    (add v (add v (add v v)))     121535    121535

Identical to the step.  So the fan tree's construction order is irrelevant, and the
2.2-2.5x spread is a property of the TERM's own association -- that is, of the ORDER in
which the computation's redexes meet the fans.

Conclusion, now grounded rather than hypothesised: **reduction cost here is dominated by
reduction ORDER, not by fan structure.**  The engine takes pairs out of `act` in insertion
order and fires whatever comes up, including gamma-delta (fan-meets-agent) commutation,
which duplicates an agent that may still be an UNREDUCED redex.  A later use then redoes
that work.  Reducing the redex BEFORE the fan duplicates it -- "fan out after reducing,
not before" -- is exactly what Levy-optimal reduction is for, and it is the thing this
engine has no mechanism for.  It also explains why CSE increased work while shrinking the
compiled net: CSE manufactures multi-use sharing, and a non-optimal schedule then
re-duplicates it.

Next experiment (cheap, 3 lines, tests the order hypothesis directly): vary the SCHEDULE at
a fixed term -- e.g. drain `act` LIFO instead of FIFO, or for a driver claim LAM|APP x DUP
pairs and defer gamma-delta until nothing else is pending.  If cost moves materially, the
order policy is the lever and the optimality work belongs in the scheduler / a strategy
driver, not in the sharing pass.
