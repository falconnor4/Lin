# Move 1 (EVICT): what the experiments actually showed

Baseline at HEAD `d02d753`: `test/run_tests.sh` green — 53 suites / 978 assertions;
`test/soundness_enum.py` green.  Core = `src/*.c` + `src/lin.h` = **2831 LOC**
(`src/*.inc` adds another 339, not counted by the stated gate).

## Experiment A: is the core complete without the fold machinery?

Patched `net_interact`'s LAM×APP case down to plain β (no `lin_fold_ffi`,
no `lin_fold_op`, no deferral, no `fold_arg`), keeping only the degenerate
identity shape.

**First attempt failed for the wrong reason, and that is worth recording:** I also
dropped the identity shape, and `((\x x) (\y y))` read back as `_`.  For `\x.x`
the compiler wires the binder port and the body port *to each other* (`ct` leaves
`self.1`/`self.2` cross-linked), so β must detect that case and link
argument↔result directly.  That is **β itself, not fold machinery**, and it stays
in the core.  With it restored, `test/basics.lin` passes completely — including
`42` for `((\x (add x x)) 21)` via the pure-Lin `_op` β-body fallback.

So: the `_op`/`_ffi` closures *do* have a working pure-β fallback.  Eviction is
viable in principle.

## The stall is NOT the fold — it is precompile freezing a too-shallow unrolling

Symptom: pure β stalls on `test/scott_arith.lin` at `(eq 42 42)` — the same point
the round-8/9 notes recorded — and `(num.eq 24 24)` hangs while
`(num.eq 23 23)` returns `true`.

Measurements (pure β):

| expr | steps | nodes | reduce time |
|---|---|---|---|
| `(eq 4 4)` | 781 | 3467 | 0.05 ms |
| `(eq 8 8)` | 1145 | 4523 | 0.09 ms |
| `(eq 16 16)` | 1701 | 6155 | 0.15 ms |
| `(eq 24 24)` | 4521 | 14507 | 0.4 ms |

Steps grow *linearly*; reduction is *sub-millisecond*.  So the hang is not in the
reducer and not in step count.

Bypassing the sentinel check (`LIN_NOSENT=1`) shows `(num.eq 24 24)` returning
`(\_rec (\_rec _rec))` — the **sentinel itself**.  The check is a *true positive*:
the k=24 chain really is exhausted.  `rec_k` starts at 24 and `(eq 24 24)` needs
25 levels.

Phase instrumentation then showed the actual defect:

```
[pc] cached num.eq (2388 nodes)          <-- frozen at k=24
[r0] after compile: 2539 nodes, 2 _rec nodes
[w] num._peq k=48 had_compiled=0
[r1] after compile: 2539 nodes, 2 _rec nodes   <-- IDENTICAL
[w] num._peq k=96 ...
[r2] after compile: 2539 nodes, 2 _rec nodes   <-- IDENTICAL
```

`widen_recursion()` rebuilds `defs[i].term` with the bigger `k` **but only for
defs where `rec && rec_body`**.  `num.eq` is *not* recursive — it merely *calls*
the recursive `num._peq` — so its precompiled net, which inlined the k=24
unrolling, is never invalidated.  Every widening round recompiles the byte-for-byte
same 2539-node net, the sentinel never clears, and `k` doubles until the
`build_bound_rec` term rebuild at k≈49152 explodes.  **That is the "hang".**

Confirmation: forcing `rec_k = 4096` initially makes `(num.eq 42 42)` return
`true` in pure β, with the fold machinery absent entirely.

## Why HEAD does not hit this: the decline is load-bearing

HEAD's `def_precompile` *declines* to cache a def when `lin_stuck_ffi_count > 0`,
and that counter is bumped by the in-core fold when it bails inside an open
free-var precompile.  `num.eq`'s body contains a `\_eq` `_op` closure, so at HEAD
`num.eq` is **never cached** — it stays textual, so `expand_defs` re-expands it
from `_peq`'s current `k` on every round and widening works.

Evicting the fold therefore *unmasks* the freeze: with nothing bumping the
counter, `num.eq` gets cached at k=24 and arithmetic past depth 24 hangs.

### Consequence for the landing order

Move 1 cannot be a bare deletion.  The `lin_stuck_ffi_count` decline must be
**relocated, not removed**: the driver must be able to say "this def is not
materialised", and the core must consult that generically.  That is exactly what
the Move 1 spec asks for (the decline moves *into* the driver), and it keeps
behaviour identical, so the suite stays green.

A second invalidation bug is also real and must be fixed before the core-only
fallback is genuinely complete: `widen_recursion` must invalidate the precompiled
cache of **every** def that may transitively reference a recursive body, not just
the recursive defs themselves.  (Naively clearing `expanded` for all defs instead
surfaced an `unbound variable '_peq'` in `num.eq`'s re-expansion — the unqualified
binder that `build_bound_rec` creates is `t->name` (`_peq`) while `qualify_free`
rewrote in-body references to the qualified `num._peq`.  Needs care; belongs with
Move 3/4, where the precompile-vs-textual decision is made AOT rather than by
try-and-fail.)

## Driver ABI gaps the WIP `std/drivers/fold.c` hit (still correct)

1. The **argument edge** (`fold_arg`: a saturated closure sitting in a β *argument*
   position, e.g. `succ (mul 2 2)`) is invisible to a driver, which only sees
   principal×principal redexes.  Needs a driver hook for argument shapes.
2. The **wait** is load-bearing: declining into β is not a substitute for parking a
   redex whose operands are not concrete yet.  The waiting policy must live in the
   driver, with the core providing only the drain point after a wave.

Both are resolved by the ABI extension designed for Move 1 (`arg_fold`, `drain`,
`pending`) plus the pre-emptor/strategy split, so that `driver_set "cpu"` /
`"simd"` does not silently drop the arithmetic pre-emptor the way `driver_clear`
would today.

## Finding 3: DESIGN.md's "don't wait at all" is falsified — the driver needs the wait

`DESIGN.md` (Move 1, item 2) proposes the driver's waiting policy as *"not to wait at
all: if it cannot fold, it declines and the core betas the closure, which is exactly the
pure-Lin body and therefore today's semantics"*.  That is false, and the counterexample is
already in the suite:

```
test/modules.lin:91   (div (mul 150 150) 100)      ; expect => 225
```

The outer `div` closure's operand slot holds the *still-unfolded* `_op` closure
`((\_mul <pure-body>) (_cl_cons 150 (_cl_cons 150 _cl_nil)))`.  Both redexes are in the
same wave, so at claim time the mul slot is present-but-not-decodable.  With "don't wait"
the driver declines, the core β-squashes the outer closure, and `_pdiv` receives that
*thunk* where a Scott numeral was expected — measured `=> 1`, not `225`.

So the deferral was load-bearing after all; the prior session's *conclusion* was right
even though its *evidence* was not (they blamed the `(eq 42 42)` hang on the missing wait,
which was really the recursion freeze below).  `drain`/`pending` are therefore not
ceremonial: the driver owns the parked set and the old `1<<15` patience bound, the core
supplies only the drain point after each wave plus a livelock guard.

## Finding 4: the recursion freeze, and the second bug underneath it

`widen_recursion` cleared `expanded` only for defs with `rec && rec_body`.  A def that
merely *calls* a recursive def (`num.eq` → `num._peq`) kept an expansion with the k=24
chain inlined, so the sentinel never cleared: widening doubled the bound forever,
re-expanding a larger chain every round (96 ms → 192 → 372 → … → 21.8 s) while emitting a
byte-identical 2646-node net.  Two further defects sat underneath it:

1. The two `build_bound_rec` call sites disagreed on the binder name.  `process_def` passed
   `t->name` (unqualified `_peq`) — which is what the body's self-references actually use,
   because `qualify_free` runs *before* the def is appended, so `lookup_raw("num._peq")` was
   still NULL and the self-reference was never rewritten — while `widen_recursion` passed
   `defs[i].name` (qualified `num._peq`).  Widening therefore always built a chain whose
   binders no longer matched the body, surfacing as `unbound variable '_peq'` the moment
   widening finally did re-expand.  `Def.rec_name` now carries the right name to both sites.
2. Widening must also drop *precompiled* nets.  With no driver loaded, nothing reports the
   open body as un-materialised, so a def like `num.eq` **is** baked; clearing only the term
   expansion then leaves widening with nothing to widen.

**Verified invariant — with no driver at all** (`std/drivers/arith.so` moved away), by plain
β plus correct widening: `(num.eq 42 42)` → `true`, `(num.eq 42 43)` → `false`,
`(num.lt 100 200)` → `true`, `(num.mul 6 7)` → `42`, `(num.div 100 5)` → `20`.  Nothing about
the core's correctness depends on a driver being present.

## Move 1 measured result

- Core **2831 → ~2700 LOC** (`src/*.c` + `src/lin.h`); ABI 2; no fold machinery.
- Startup with std **425 ms → 112 ms** (std load 421 → 108 ms; the Move 2 generalize fix,
  measured in this same tree).
- `test/scott_arith.lin`: hangs with the fold evicted → **passes in 777 ms**.
- `std/drivers/fold.c` (the WIP) is deleted: it referenced `lin_opfold_hook` /
  `lin_argfold_hook`, which never existed, and `std/drivers/arith.c` now owns the port.
- `std/drivers/gpu.c` dropped its `n->blocked` drain pass — the core holds no deferral
  state for it to drain.


## Two more defects the eviction exposed (both fixed)

### `net_print` sized its memo arrays from a node count that printing can grow

`print_port` reaches a LAM at port 0 and calls `net_read_int` (runtime_io.inc:71),
whose readback peek now goes through `lin_materialize` → a driver's `materialize`
→ `net_alloc_scott`.  Printing therefore **allocates nodes**, so `N->nn` grows
while printing.  `net_print` allocated `vis_print`/`viz_txt` from the old
`N->nn`, then used the *current* `N->nn` in its cleanup loop — so the loop ran
past the allocation, read garbage as `char *`, and called `free()` on it:

```
=> 49
=> 81free(): invalid pointer     (core dumped)
```

Caught with `-fsanitize=address`:

```
ERROR: AddressSanitizer: heap-buffer-overflow ... READ of size 8
    #0 net_print src/runtime_io.inc:101
0x... is located 0 bytes after 2630688-byte region
allocated by ... net_print src/runtime_io.inc:97
```

Fix: record the capacity (`vis_cap`) the arrays were allocated with, bounds-check
every `vis_print`/`viz_txt` access against it, and free exactly `vis_cap * 3`
entries.  A node allocated mid-print simply is not memoised (correct output, one
extra render).  This is a latent core bug, not a driver bug — it needed only a
driver that materialises during readback to fire.

### `drain` dropped a parked pair whose *shape* shifted, stranding a live redex

`drain` re-enqueued a parked pair only if it still passed the strict structural
`pair_live` test (mutual wiring *and* the LAM still carrying a DT_OP/DT_FFI
carrier).  Since `drain` is the **only** place a parked pair is ever put back,
dropping one is unrecoverable: the redex is neither folded (the driver stopped
seeing it) nor β-reduced (the core never saw it again), so it just sits in the
net and readback prints the closure still applied to its spine with its body
reduced — the `((\_eq true) spine)` / `((\_add 13) <spine>)` residual that
DESIGN.md records from the knot work.

Traced:

```
[park]  lam=6 app=5 slot=(nil) tries=-1
[park]  lam=2405 app=2404 slot=0x...c0 tries=0
[drain] slot=0x...c0 pairs=4
[park]  lam=6 app=5 slot=0x...c0 tries=2
[op]    lam=2405 app=2404 ... res=5891        <- only ONE fold happened
[drain] slot=(nil) pairs=-1                   <- (6,5) dropped, slot forgotten
=> ((\_eq true) (\c (\n ((c 1) ...))))        <- stranded
```

Fix: mirror the evicted core's blocked-list drain exactly — re-enqueue every pair
whose **nodes are still alive**, regardless of shape, and clear the list (so a
still-pending redex is re-parked in the next wave rather than duplicated); only a
consumed/destroyed node means there is nothing left to wait for.

Result: `booleans`, `let`, `math`, `modules`, `numbers`, `higher_order`,
`test_escapes_utf8`, `scott_arith` all pass — 240 assertions, previously 6 suites
red with several stopping early.
