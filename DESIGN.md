# Lin Architecture Notes

## Goal

Lin is a functional language where every program is inherently optimal
(Lévy-optimal interaction-combinator reduction) and parallel (wavefront
fan-out), implemented compactly.

## Core philosophy: pure interaction nets + pluggable optimizations

The **base engine** (`src/`) is pure interaction-net reduction: the four
scope-gauge rules (beta, annihilate, commute, erase) plus readback/effects,
with no hardware-specific or opportunistic fast paths baked in.  That purity
is what keeps the core small (the pure `src/` core is **2,476 lines** incl.
`lin.h`, under the 2,500 target) and auditable.

**All optimization/acceleration lives outside the core**, in `std/` and
`std/drivers/*.so`:

- **Drivers** (`std/drivers/simd.so`, `gpu.so`) reduce a *class* of redexes
  more cheaply than the base rules (SIMD native arithmetic; the GPU kernel)
  but must reproduce the base engine's reduction *exactly* — the base engine
  is always the correctness oracle, and `LIN_GPU_SELFTEST` asserts a driver's
  rewrites are bit-identical to `lin_reduce_wave_parallel`.
- **Scalar-op semantics** live in one shared table (`std/drivers/arith.so`),
  not in the core and not per-driver.
- **Non-calculus runtime** (readback/IO effects, the `.line` container) lives
  in `std/runtime/`, `#include`d into the core for a single binary.

This boundary is what permits "every program is inherently optimal" in the core
while still admitting hardware acceleration as an opt-in concern.

## Generality principles (post-refactor)

1. **Datatype registry** (`ctor_tag` / `ctor_register` in `src/io.c`).
   Value domains (`num`, `bool`, `string`, `ffi`, `effect`) are keyed by their
   carrier node names in one registry; the readback decoders consult it via
   `ctor_tag(name)` instead of hard-coded prefixes.  This removed a latent bug
   where any user identifier starting with `c`/`n` (e.g. `cons`, `car`) could
   be mis-decoded as a string.

2. **User-declared algebraic datatypes** (`datatype` + `match` in the parser).
   Constructors are generated Scott encodings — `C_i = \f1..\fk \d0..\d_{m-1}
   (d_i f1 .. fk)` — and type-check through ordinary Hindley-Milner
   let-generalization.  No new type-system machinery is required.

3. **Open effect/continuation protocol.**  Effect kinds (`_iod`, `_iop`,
   `_ior`, `_iow`, `_ffi`) are registry entries under one `DT_EFF`/`DT_FFI`
   tag set.  The monadic continuation step — apply continuation to the
   produced value, relink `ROOT`, re-reduce — is a single `eff_apply`
   primitive shared by every effect.  New effects are added by registering a
   carrier, not by growing `net_run_io` with new branches.

4. **Optional accelerator drivers.**  The wavefront reducer exposes a driver
   pipeline (`lin_driver_add`, sorted by descending priority).  The SIMD
   driver folds Scott×Scott native small-integer arithmetic *during*
   reduction; the GPU driver dispatches the fixed-allocation rules
   (beta/annihilate-inline/erase) to a Vulkan compute kernel.  Both are
   host-authoritative (the base engine is ground truth and a driver only
   commits when its output is proven bit-exact).

## Arithmetic: one shared table, any reduction strategy

There is **exactly one** place that knows what `lin_add`, `lin_eq`,
`lin_fadd`, … mean: `lin_arith_scalar()` in `std/drivers/arith.so`.  A
reduction *strategy* (base cpu fold, SIMD, GPU) decides **how** to reduce a
net; it resolves arithmetic by calling that one table.  This is the key
separation:

- `arith.so` is a **semantic provider**, deliberately *not* a reduction
  strategy (its `claim` is a no-op) — it only answers "what is the value of
  this operation".  New ops are one table row, not a new switch arm per driver.
- The **core hook is general-purpose**: `lin_scalar_ops_add()` /
  `lin_scalar_ops_load(sym)` let any driver register any number of
  `ScalarOpFn` providers, tried in registration order; arithmetic is just the
  first consumer.  `run_ffi` delegates unclaimed `lin_*` ops to them.
- `simd.c`'s `ev_ffi` decodes args and then calls `lin_arith_scalar` (dlsym,
  cached) instead of carrying its own switch; the GPU strategy already
  relegates `_ffi` folding to the base fold, so cpu, SIMD and GPU resolve the
  same math.
- **Non-movable C stays in the core**: memory/device/OS (`exit`, `driver_*`,
  `dlopen`, `puts`, `getenv`), float parsing (`lin_parse_float`/`lin_float`),
  string compare (`lin_streq`), and fold accounting (`lin_folds`/`lin_folded`).

## Pure-Lin arithmetic: `num.lin` is driver-foldable `_op` closures

`std/num.lin`'s integer/comparison ops are **pure-Lin Scott recursion wrapped as
driver-foldable `_op` closures** (replacing the old direct-`ccall2` de-ladered
form).  Each op emits a saturated redex whose head is a **DT_OP-named LAM** — the
same named-LAM pattern `_ffi` uses, no new interaction agent:
`add 4 3 = ((\_add (padd 4 3)) (cons 4 (cons 3 nil)))`.  The `_add` LAM applied
to the operand `_cl`-spine is routed by `net_interact` to `lin_fold_op`, which
derives the op token from the LAM's name, decodes the operands via the shared
`net_spine_args`, and folds through the one shared `lin_arith_scalar` table
(arith.so) whenever the operands are concrete.  The embedded pure-Scott body
(`padd` etc.) is the **always-correct β fallback**: with no scalar provider the
same redex reduces by the interaction calculus (slow but exact).  Drivers fold
the same saturated `_op` redexes through the same table, so the base engine,
SIMD and GPU resolve identical math.

The enabling engine behavior is a **confluence-preserving fold deferral** in
`src/net.c` / `src/io.c` (see *Fold routing* below) that threads each operand's
computed value into the closure before folding (for `_op` too, an outer redex
whose spine operand is an un-folded inner `_op` is deferred until the inner
folds).  Without it, a still-live operand such as `(min 4 5)` (a
`if`-application, not a scalar) would be β-squashed or mis-folded.

Two latent engine defects the old FFI overloads hid, now fixed: `egraph_optimize`
out-of-bounds-read for body-less TDEF/TDEFX/TFLOAT value markers (corrupted
`lin build`), and `net_load_line` not seeding the active-redex queue (loaded
`.line` containers didn't reduce).

## Fold routing (the composed-`if` fix)

The reducer folds a saturated pure-`lin_*` closure at the right moment:

- `lin_ffi_peek` refuses to fold unless **every** operand is a concrete scalar
  or a recursively-foldable closure (`ffi_ops_concrete`: walks the arg
  `_cl`-spine exactly like `unpack_args`).
- When a head-closure `lin_ffi_needs_operand` (an operand is still live, not
  yet concrete), the reducer **defers** rather than β-squashes: the head-redex
  is parked on a per-net `blocked` list and re-added to the active list only
  *after* the current wave drains, so the operand's own redexes materialise
  its value first.  Bounded by a per-net `declines` budget (reset on every
  real fold) so a genuinely-stranded operand falls back to β; deferral is
  disabled during open free-var precompiles.
- Nested `_ffi` operands recurse (an outer closure whose operand is itself a
  closure with an unresolved operand — the deep nqueens/`attacks` case — is
  deferred rather than baked with a wrong scalar).

Result: `(if (geq 1 (min 4 5)) 1 8)` → `8`, `(mul 6 (add 24 96))` → `720`,
and the previously-failing composed de-ladered tests (`math`, `map`, `set`,
`nqueens`, `sudoku`, `algorithms`) all pass.

## Recursion

Recursive defs are compiled by **bounded self-unravelling** (`build_bound_rec`:
`Y_k f = f (f (... (f base) ...))`, k=24, `base = \args 0`) instead of the
Y-fixpoint.  This sidesteps the continuation-knot stranding the Y-form caused,
and single/linear self-recursion reduces to the correct value (`peel 3→0`,
`fact 4→24`, `sumto 5→15`, `pow2 4→16`).  Pure and engine-native
(`process_def` in `src/main.c`); no new interaction agents.  Recursion deeper
than the bound truncates to the base value.  Regression test:
`test/selfrecursion.lin`.

## Net-manipulation primitives (runtime fan-out; pure deref/alias)

The language gains "net manipulation" that stays **within the pure interaction
combinators** — no new agents.  Recursion is denotationally present via
Church numeration (`n f x = f^n x`); what the language adds is making that
*structural*: driving sharing/iteration by a runtime count so `n` is data,
done in the wave with optimal (Lévy) sharing of `f`/`x` across iterations.

Design principle, unchanged: the base engine is the correctness oracle; it
computes exactly the pure denotation of the λ-term; only the *reduction
strategy* may change, and any accelerator must reproduce it bit-exactly.  A
structural fast path in the core is therefore not a new combinator — it is a
saturated-redex reduction of an existing pattern, exactly as `lin_fold_ffi`
reduces a saturated `_ffi` closure into a concrete value during `net_interact`.

Two capabilities and how they are realized:

- **Runtime-n loop / fan-out.**  The iterator position is driven by a runtime
  Scott/Church count on a wire.  The core expands an iterate by peeling one
  application per step with a DUP-sharing rewrite, so the function/argument are
  **shared** — not copied — across iterations (O(1) sharing growth per step).
  A driver may fold the whole iterate cheaper, still bit-exact.
- **Pointer deref/alias over shared structure.**  A *handle* is a shared wire
  to a subterm (interaction-net structural sharing).  Deref follows the
  handle; alias is sharing one handle from two sites.  Pure and confluent —
  reads and pure updates only; no destructive in-place mutation (confluence
  forbids aliased `set!`); an update is a pure rebinding to a new handle.

Because no node tags are added, the interaction algebra, the compiler's port
layout, the egraph optimizer, and the GPU fixed-allocation contract are
unchanged.

## Non-core runtime in `std/runtime/`

The readback/IO-effect runtime and the `.line` binary container are **not**
part of the pure `src/` core:

- `std/runtime/io.c` — value rendering, the net printer, and the monadic
  IO/effect continuation runner (`_iod`/`_iop`/`_ior`/`_iow`).
- `std/runtime/line.c` — `.line` serialize/deserialize (self-running containers).

These are `#include`d into the core TUs (unity build) so they share the same
translation unit's statics and the binary remains single — but they are
physically `std` code, keeping `src/` focused on the interaction calculus.
No build-recipe change was needed (`src/*.c` still compiles alone).

## Build

```
make all        # core (./lin) + driver plugins (std/drivers/*.so) + reduce.spv
make lin        # core only
make test       # build all + run the full suite
```

`nix build` also works (the flake compiles `src/*.c` plus the driver plugins
with `vulkan-headers`/`vulkan-loader`, and wraps the binary with the bundled
`std/`).

## Test status

The full suite is green: **50 suites / 875 assertions** (Tiers 1-6: core
primitives, FFI/system drivers, SAT & term rewriting, non-trivial workloads,
`.line` containers, and CLI invariants).  A driver's native folds are asserted
by `(folded)`/`lin_folds` in the driver suites; the GPU driver's bit-exactness
is asserted by `LIN_GPU_SELFTEST` (no mismatches on a device).

## Line budget

Pure core `src/` (`.c` + `lin.h`): **3,085 lines** (above the 2,500 target).
The pure-Scott de-laddering added the driver-foldable `_op` machinery
(`lin_fold_op`/`lin_fold_op_arg`/`op_value_from_lam`, `net_spine_args`, and the
`_op` deferral + eager-argument-fold edges) in `src/io.c`/`src/net.c`, which is
what lifts the count; the integer arithmetic itself was already retired to
`std/drivers/arith.so`, so the migration costs fold machinery in the core rather
than removing rows.  The arithmetic table, drivers, and `std/runtime/*` live
outside `src/` and do not count against the core.

## Status (honest)

**All green: 50 suites / 875 assertions.**

- **Integer/comparison arithmetic is now PURE LIN.**  `std/num.lin` no longer
  uses any integer `_ffi`/`ccall2`: `add/sub/mul/div/mod/pow/eq/lt/gt/leq/geq`
  are pure-Scott recursions wrapped as **driver-foldable `_op` closures** — a
  saturated op is a DT_OP-named LAM (`_add`, …) applied to the operand
  `_cl`-spine, whose head `lin_fold_op` folds through the one shared
  `lin_arith_scalar` table (arith.so) when operands are concrete, and whose
  pure-Scott body is the always-correct β fallback (verified correct with arith
  absent).  `(mul 6 (add 24 96))` → 720 and `(if (geq 1 (min 4 5)) 1 8)` → 8
  fold fast; the dead integer `_ffi` fold paths are trimmed.
- **Drivers fold `_op` uniformly.**  The base fold's `lin_fold_op` IS the
  uniform `_op` fold (op token from the DT_OP name, operands via the shared
  `net_spine_args` decoder, value from the shared scalar table); SIMD keeps its
  `_ffi` float fold and the GPU delegates to the base, so all strategies resolve
  the same math.  `native.lin` no longer routes integers through `ccall2`.
- **Arithmetic generalized.**  One shared `lin_arith_scalar` table is the single
  authority; the core hook is a general-purpose `lin_scalar_ops_add/load`
  registry.  Non-movable C (OS/device, float parsing, string compare, fold
  accounting) stays in the core.
- **Fold mechanics hardened.**  Two engine defects surfaced by the pure-Lin
  closures were fixed: `egraph_optimize` no longer out-of-bounds reads for
  body-less TDEF/TDEFX/TFLOAT value markers (was emitting a stray free `_sz` in
  `lin build`), and `net_load_line` now seeds the active-redex queue so a loaded
  `.line` container actually reduces.
- **Recursion converges** via bounded self-unravelling (k=24), extended by the
  `_rec` widening for deeper pure-Lin recursion.

**Known limitations (genuinely hard, not patched here).**
- Recursion depth is capped by the self-unravelling bound (truncates to the base
  value beyond it); arbitrarily-deep recursion still needs a value to thread out
  of a terminating recursive knot in the reducer.
- The driver fold paths (`simd.c`'s `_ffi` arg-decoding) still parallel the
  core's shared decoder; the scalar *semantics* are shared via `lin_arith_scalar`
  and the `_op` operands are decoded by the shared `net_spine_args`, but a fuller
  consolidation of each driver's net-side walk remains.
- Core LOC is ~3,085 (above the 2,500 target): the pure-Scott `_op` machinery is
  the current cost.  Recapturing headroom requires consolidating the fold/defer
  and decoder paths, not removing dead arithmetic rows (those already live in
  arith.so).

**Journey / lessons (compressed history).**  Earlier rounds documented in
detail: Y-combinator recursion strands its base value on a continuation knot;
deep windows in `num.lin` exploded node counts; a fold-on-saturation gap made
composed direct-FFI comparisons strand until the fold-routing/deferral fix
landed; readback folds and `lin_precompile_depth` suppression were incremental
steps toward it.  These were resolved by the bounded self-unravelling and the
deferral fix above; the per-round investigation is preserved in git history.