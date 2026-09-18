# Move 1 (EVICT the fold machinery): port notes

Status: `std/drivers/fold.c` exists (untracked, inert until a load site is added) and the port
works for the direct cases, but two findings mean the plan in `DESIGN.md` needs correcting
before it can land.

## What works

`std/drivers/fold.c` is a `LinDriver` (`claim` + `reduce`) that claims `_op` carrier redexes
(LAM named `_…` with `ctor_tag == DT_OP` meeting its APP), decodes the operand spine with
`net_spine_args`, takes the value from `lin_arith_scalar`, allocates it with
`net_alloc_scott/bool/float`, and rewires the redex exactly as the core's `lin_fold_op` did
(kill lam+app, `own()` the body and spine — skipping DUPs — and link the value at
`wire(app,1)`).  With the core's head-fold call site removed and this driver loaded
(`lin_scalar_ops_load("fold")`), the direct cases are correct and fast: `(add 1 2)` -> 3,
`(mul 2 3)` -> 6, `(let ((g (mul 2))) (g 3))` -> 6, ~450 ms each (HEAD: the same, in-core).

Two API lessons worth keeping:

- the driver `reduce` hook receives a slice of **pairs**: `nred` is the pair count and the
  array holds `2*nred` ports (the core calls it as `reduce(n, slices[di], scnts[di]/2, …)`),
  and the wave hands pairs in **tag order**, so a driver must normalise (LAM first) itself —
  `net_interact` does that for the core, a driver does not get it for free.  Both mistakes
  showed up as a fold that computed the right value and threaded it to the wrong slot
  (`((\_add 3) <spine>)`), and then as claimed pairs silently never reduced.

## Finding 1: the WAIT is load-bearing — "decline to beta" is not enough

Removing the `_op` deferral (the blocked list) and letting the driver's core fallback
(`net_interact` -> beta) handle an unfolderable redex **hangs `(eq 42 42)`**: `scott_arith`
prints its correct values up to `3` and then stalls, exactly the point and symptom of the
round-8/9 experiment (where the last printed value was also `3`).  That is the deferral's own
comment being right — beta of a closure whose operand is still being computed "strangles the
operand sub-net".  So a fold driver needs a **waiting policy of its own**; declining into beta
is not a substitute.  The simplest correct one is the same shape as the core's: park the pair
and re-examine it after the wave drains (a driver can hold that state as a small static array,
since it is called per wave on one net).

## Finding 2: the argument edge cannot be intercepted by a driver

`fold_arg` (the identity / eager-argument edge inside beta) folds a saturated closure that sits
in an *argument* position.  A driver only sees principal-principal redexes, so it cannot see
that shape; removing the core edge and relying on the driver leaves the `succ (mul 2 2)` case
unfolded.  Restoring the edge is what kept `scott_arith` moving past that point.  Moving it for
real needs a driver hook for argument shapes (or accepting that this one edge stays in the core).

## Consequence for Move 1

The eviction is still the right goal, but it is two pieces, not one: (a) the driver needs its own
deferred set (or the core needs to expose a "park this redex" hook), and (b) either a hook for
argument shapes or an explicit decision to leave that edge in the core.  Until then the core
retains `lin_op_needs_operand`, the blocked list, and `fold_arg`'s `_op` route — the parts that
were supposed to go away.

Reproduction: `test/scott_arith.lin` (stalls at `(eq 42 42)`) and `test/selfrecursion.lin`
(stalls after `24`); the direct matrix in `notes/knot-wip.md` stays correct throughout.
