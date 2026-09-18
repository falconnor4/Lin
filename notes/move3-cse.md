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
