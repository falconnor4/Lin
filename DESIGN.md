# Lin Architecture Notes

## Goal

Lin is a functional language where every program is inherently optimal
(Lévy-optimal interaction-combinator reduction) and parallel (wavefront
fan-out), implemented compactly.

## Core philosophy: pure interaction nets + pluggable optimizations

The **base engine** (`src/`) is pure interaction-net reduction: the four
scope-gauge rules (beta, annihilate, commute, erase) plus readback/effects,
with no hardware-specific or opportunistic fast paths baked in.  That purity
is what keeps the core small (the pure `src/` core is **2,923 lines** incl.
`lin.h`, under the 3,000 target) and auditable.

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

## Canonical driver selftest (the driver correctness contract)

Every reduction driver — current (`cpu` fold, SIMD, GPU) or future — must
reproduce the base engine's reduction exactly.  That invariant is enforced by
one canonical, driver-agnostic selftest, not by per-driver test files:

- **Corpus: `std/selftest.lin`.**  A single module that loads `std.lin` and
  reduces a fixed set of pure probes covering each redex/capability class a
  driver claims (`_op` integer folds, saturated comparisons, float folds,
  composed/deferred operands, annihilate/erase identities, beta-heavy nesting).
  It activates **no** driver and carries **no** expected values: it just emits
  the readback tokens.  It is meaningful under cpu, SIMD, GPU and any future
  driver because every value follows from core confluence plus the one shared
  scalar-op table (`arith.so`).
- **Runner: `test/driver_selftest.sh`.**  Runs the corpus under the base CPU
  engine (golden), then under each driver in a `DRIVERS` registry array, and
  requires the driver's probe lines to equal the golden **value-for-value**.
  It also reports each driver's native fold count (`(folds)`), which is
  informational — folding is a driver's own optimization decision, so `folded`
  need **not** be true for a driver to pass.
- **The contract for a new driver is two lines of work, not a new test file:**
  1. ship its `std/drivers/<name>.lin` plugin, and
  2. add `<name>` to the `DRIVERS` array in `test/driver_selftest.sh`.
  The runner then validates it against the base engine exactly as it does SIMD
  and GPU.  No bespoke expected values, no driver-specific assertions to
  maintain, no drift.
- **Device reducers get a stronger, per-wave oracle.**  `std/drivers/selftest.h`
  is the shared, std-wide extraction of what was `gpu_selftest`: a device
  driver calls `lin_selftest_replay(...)` after committing a wave, and the
  harness clones the host net, replays the *same* redexes through the canonical
  `lin_reduce_wave_parallel`, and diffs `wire[]`/`dead[]` **bit-exactly**
  (env-gated, e.g. `LIN_GPU_SELFTEST=1`).  Host-native reducers (SIMD) have no
  separable device state to compare, so their oracle is the value-level corpus.
  The two layers compose: `std/selftest.lin` proves cross-driver value
  equality everywhere; `selftest.h` proves per-wave device-redux bit-exactness
  where a device actually ran.

## SIMD / GPU acceleration vs. the current engine

Both drivers predate the "arithmetic is pure Lin" migration, when scalar ops
were `_ffi`/`ccall2` closures the drivers folded natively.  After the migration
(`std/num.lin` `_op` closures, base-folded by `lin_fold_op`), each was left
with nothing of its old class to fold: SIMD's DT_FFI-only claim never matched
the `_op` closures (a silent no-op), and the GPU's beta kernel (which only
rewires wires) mishandled the `_op`/`_ffi` closures it claimed (a bit-exactness
mismatch plus segfault on a real device).  Their adaptation to the current
engine:

- **SIMD folds `_op` closures.**  `std/drivers/simd.c` now claims saturated
  pure-Lin `_op` redexes (DT_OP) alongside DT_FFI.  `claim` gates on an
  **operand-readiness predicate** (`simd_op_ready`: every operand concrete and
  the shared `lin_arith_scalar` table claims the op) so a driver never strands a
  claimed-but-unfoldable redex (a claimed redex is removed from the wave; the
  base engine DEFERS non-concrete operands, a driver cannot).  `reduce` folds
  via the shared `net_spine_args` decoder + `lin_arith_scalar` table, rewiring
  exactly like `lin_fold_op`.  The float `_ffi` arm is preserved but
  near-vestigial: floats already fold at readback in a couple of steps, so there
  is no reduction-time win to capture.
  *Fold-accounting note:* SIMD's native-fold count matches, not exceeds, the
  base engine's on the same programs (e.g. 71 vs 71 on `fact 6`), because the
  base's `lin_fold_op` already folds every saturated `_op` closure in O(1) via
  the one shared scalar table.  `simd_reduce` implements the **SIMD_WIDTH
  factorization**: it processes the claimed slice in batches of up to
  `SIMD_WIDTH` redexes, running a side-effect-free *eval* pass (decode operands
  + shared-table value) for the whole batch, then a sequential *apply* pass
  (net rewire) — so the independent value computations decouple from mutation
  and can be auto-vectorized.  It stays bit-exact (canonical selftest green),
  but rigorously no wall-clock win over the base on `_op` scalar folding: the
  base's O(1) fold already dominates and the surrounding interaction-net
  reduction, which neither SIMD nor batching accelerates, is the real cost.
- **GPU beta must not claim foldable closures.**  The GPU kernel's beta only
  rewires wires; it does not fold.  So `gpu_claim` rejects any LAM x APP whose
  head **or** applied argument is a saturated `_op`/`_ffi` closure — the base
  engine folds those (via `lin_fold_op`/`lin_fold_ffi` and the eager `fold_arg`
  inside beta).  Claiming them would beta-reduce on-device instead of folding,
  the exact per-wave differential mismatch observed.
- **GPU wave dispatch is two-phase.**  `gpu_reduce` interleaved host-fallback
  `net_interact` calls with GPU-slice collection, mutating the net so later
  reads saw stale wire structure and the differential replay diverged (a
  concurrency bug).  It now (1) collects the sector-disjoint GPU slice and the
  host-fallback list **without mutating the net**, (2) dispatches the GPU, (3)
  commits, then (4) host-falls-back.  On real AMD hardware `LIN_GPU_SELFTEST=1`
  the dispatched waves are **bit-exact OK** (previously a mismatch within two
  waves and a segfault).
- **GPU fallback must not strand deferred `_op`.**  GPU `gpu_reduce`'s
  host-fallback used `net_interact` directly, which parks `_op`/`_ffi` closures
  with non-concrete operands on `n->blocked`; only `net_reduce`'s main loop
  drains that, so a closure in a fallback redex was stranded (the composed-`if`
  probe `(if (geq 1 (min 4 5)) 1 8) -> ((_ 1) 8)` under gpu).  `gpu_reduce` now
  drains `n->blocked` after the fallback, so deferred closures are re-queued and
  resolve; the composed probe reduces to `8` and every dispatched wave stays
  bit-exact.
- **`run_ffi` guards mixed-type arguments.**  The core's `run_ffi` strcmp'd a
  `c_args[i]` as a char* even when the arg decoded as an INT/BOOL/FLOAT;
  a `_ffi` closure under an accelerator read back with a mismatched arg type
  (e.g. an int where a string was expected) segfaulted in `__strcmp`.  The
  string-taking FFIs (`lin_streq`, `puts`, `dlopen`, `getenv`,
  `lin_parse_float`) now guard on the argument kind, so a malformed closure
  yields a clean no-value instead of a crash.  This is a core robustness fix
  that all drivers benefit from and does not regress the host suite.
- **GPU verified bit-exact on a real device.**  With a correct std, the full
  canonical corpus reduces under GPU with **all 23 value probes matching the CPU
  golden and every dispatched wave `[GPU selftest] OK` (1602/1602)**, no crash
  (exit 0).  `test/driver_selftest.sh` reports `PASS gpu (23 probes equal; N
  native folds)` on the device.  The one earlier "long-run divergence" was **not
  a GPU bug but a std-load-path defect**: `resolve_path` (src/main.c) resolved a
  `(load "std/...")` to a coincidental `./std` in the process CWD before trying
  the configured `LIN_STD_DIR`, so a checkout run mixed a local std onto the
  configured one and stranded private defs (`num._padd` unbound).  Fixed: a
  `std/`-prefixed load now honors `LIN_STD_DIR` first.  The flake's packaged
  std loads cleanly and the GPU dispatches to hardware through the normal
  `nix run #.lin` / `result/bin/lin` path (all corpus values correct, real
  device dispatch).
- **Flake std loads cleanly.**  From a non-checkout CWD the flake binary
  (`./result/bin/lin`, store std) was already correct; the `resolve_path` fix
  (prefer `LIN_STD_DIR` for `std/...`) closes the checkout-CWD mixing case so
  `add 8 5 -> 13` holds even when `./std` exists beside an overridden
  `LIN_STD_DIR`.

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

## Sharing soundness: fan–fan commutation and the gauge discipline

Lin's DUP sharing was **unsound**: every fan carried the *empty* gauge, and a fan
annihilates only when gauges match, so two *independent* sharing points
annihilated against each other and merged their values.  Minimal witness on the
unmodified engine (plain `let`, no compiler fan-sharing involved):

```
(let ((f (\x (pair x x)))) (pair (f 1) (f 2)))   =>  (pair 1 2) (pair 1 2)     ; should be (1 1) (2 2)
(let ((f (\x (add x 1)))) (pair (f 1) (f 2)))    =>  (pair 3 3)                ; should be (2 3)
```

The suite documented the same defect as a "superposition collapse": it asserted
`(exists f_sat1) => false` for the satisfiable `f_sat1 = \x1 (x1 and x1)` and
labelled it a *false negative*, while asserting the correct `true` for the
explicitly-desugared form of the same formula.  Three changes make sharing sound:

1. **Fan–fan commutation (the missing rule).**  `net_interact`'s `DUP × DUP` case
   only annihilated equal-gauge fans and *silently dropped* mismatched pairs;
   there was no rule at all for two independent fans meeting, so a fan-shared
   body could never be reduced correctly.  It now implements Lafont's δ⋈δ
   commutation for differing gauges — each fan is copied by the other (a's
   auxiliaries get a δ_b each, b's get a δ_a each, cross-connected) — with each
   fan's copies keeping *that fan's own* gauge.  (The reference implementation
   has only three rules — LAM↔APP, DUP↔DUP on scope match, LAM/APP↔DUP — and
   leaves mismatched fans stuck.)
2. **A real gauge discipline.**  Every fan now carries a gauge identifying *its*
   sharing point — a compact unique marker — so fans for independent sharing
   points are never equal and the gauge only annihilates a fan against a copy of
   *itself*.  Structural nodes keep a uniform (empty) gauge: the commute modulates
   copies as `1·s_node·s_dup`, so uniform node gauges are what keep copies of the
   same fan matching.  Markers are compact (a counter that stays inside the 57-bit
   inline scope word) rather than nesting-path words, because a path word grows
   with depth and every scope operation on a spilled word allocates.
3. **Re-gauging on splice.**  A precompiled body's fans were labelled during its
   own precompile reduction, so splicing it verbatim gave every reference's copy
   identical labels and independent sharing points collided again.  `ct_splice`
   now re-gauges each clone at a fresh level.

Result: the witnesses above reduce correctly, and every `exists` case in
`test/sat.lin`, `test/sat_verify.lin` and `test/tseitin.lin` now agrees with the
explicit-assignment enumeration.  Three expectations that encoded the unsound
results were corrected: a Tseitin parity contradiction is unsatisfiable, so its
`exists` is `false` rather than `true`, and `sat.lin`'s clause set
(`~x1∨x3, ~x3∨x2, ~x2∨x1`, satisfied by all-true) is `true` rather than `false`.

`scope_from_bits` (`net.c`) rebuilds a heap-backed scope in **one** allocation;
the previous per-bit `scope_ext` loop allocated once per bit, which made
per-node re-gauging of large spliced bodies dominate compile time.  Remaining
cost: a large precompiled body is still cloned once per reference, and gauges
make that clone's scope work non-trivial — sharing one copy across references
(and making a shared body reduce per consumer) is the next step.

## Gauges as levels: the meet modulation (a large compile-time win)

A gauge is meant to be a Lamping *level*, and levels **meet**: two sharing points
that have crossed each other share the prefix of their histories, so their meet is
the level they genuinely have in common.  The paper's modulation
(`s₁ = 1·s_node·s_dup`) only ever *concatenates*, so words grow without bound: two
fans that meet inside a cycle commute again and again and the cycle never closes,
and later scope operations pay for words of ever-increasing length.

`scope_meet` (the longest common prefix) now supplies the meet, and the
`LAM/APP × DUP` commute modulates the copies through it:
`s₁ = 1·(s_node ⊓ s_dup)`, `s₂ = 2·(s_node ⊓ s_dup)`.  Copies therefore *converge*
towards the level the two histories share instead of diverging, which is what makes
repeat crossing settle.  Measured effect (all of it with the suite and the
soundness oracle green):

| program | before | after |
|---|---|---|
| `test/modules.lin` | 17.3 s | **2.3 s** |
| `test/numbers.lin` | 14.4 s | **4.9 s** |
| `test/string.lin` | 1.8 s | **0.6 s** |
| `test/selfrecursion.lin` | 3.6 s | 2.8 s |

The gain is mostly that words stay short: the expensive part of compiling had been
scope work on long words, and converging gauges also make more fans annihilate
instead of commuting (less duplicated work).

**A gauge must be a PATH, not a bare level.**  Relabelling fans by their binder
*depth* (so the meet is trivially the shallower level) is unsound: two sibling
binders at the same depth get the same label, their fans annihilate, and values
merge — with depth labels the oracle reports 5 mismatches (including the
`(let ((f (\x (pair x x)))) (pair (f 1) (f 2)))` witness, which correctly reduces to
`(1 1) (2 2)` only with path labels).  The paper's "binder paths as free-group word
invariants" is therefore load-bearing: the *path* (one generator per binder, one
per application child) distinguishes siblings, and the *meet* of two paths supplies
the level behaviour.  Path labels + meet keep every check green.

**Open soundness question.**  Annihilating two fans is only sound when equal gauges
really mean "the same sharing point", i.e. when the labels *are* levels.  Today a
fan's label is a unique marker, so the meet of two unrelated markers is empty and
unrelated fans can collapse to the same level.  The corpus above is green, but the
cyclic-knot experiment below produces exactly that failure (`_op` folds stop being
wired correctly, 5 suites red), so the discipline is not yet consistent.  The fix is
to label fans by their true level (the binder depth they duplicate at, which the
compiler already threads as its scope) so that the meet is the genuine LCA.

## Recursion

Recursive defs are compiled by **bounded self-unravelling** (`build_bound_rec`:
`Y_k f = f (f (... (f base) ...))`, k=24, `base = \args 0`) instead of the
Y-fixpoint.  This sidesteps the continuation-knot stranding the Y-form caused,
and single/linear self-recursion reduces to the correct value (`peel 3→0`,
`fact 4→24`, `sumto 5→15`, `pow2 4→16`).  Pure and engine-native
(`process_def` in `src/main.c`); no new interaction agents.  Recursion deeper
than the bound truncates to the base value.  Regression test:
`test/selfrecursion.lin`.

**Why the bound is still there (a cyclic knot was tried).**  The alternative — one
compiled body whose self-reference is fed by a fan (the def's lambda put on a DUP
whose one auxiliary is the public value and whose other auxiliary feeds every
occurrence of the def's own name) — *converges* once the meet modulation above is in
place, and gives the right values with **linear** steps and tiny nets
(`(rec n)` for n = 0,1,2,4,8,16: 410, 416, 426, 458, 570, 986 steps; 1.8–3.5 k
nodes) where the unrolled chain needs k copies of the body.  What it does *not* yet
do is reach the `_op` folds at all: with a knot anywhere in the program,
`(add 8 5)` reduces to `((\_add 13) <spine>)` instead of `13`, and 5 suites go red.
Instrumented, the `_op` closure's head-fold (`lin_fold_op`) and its eager-argument
fold (`lin_fold_op_arg`) are **never called** for `_add` (both counters stay 0),
while the non-knot build folds immediately (`lam=6 app=5 ar=0 aa=1242 body=43`), and
the knot's own unfolding does run (many `_padd` LAM×APP events; the stray `13` comes
from the pure-Scott β fallback).  A post-compile dump shows the pair *is* formed
(`_add node=6 principal=5(t1.p0)`, an APP) — so the redex exists and the fold simply
never gets to run on it: this is the pre-existing `_op`-fold operand-deferral bug
that a shared closure already exposed before the knot (a fold whose operands sit
behind a fan never decodes them, `lin_op_needs_operand` keeps answering "defer", and
the redex parks on the blocked list forever because unrelated folds keep resetting
the decline budget).  The knot just makes every `_op` closure shared.  Two fixes are
available: make the operand decoder fan-complete (it hops DUPs with `skip_dup`, so
the failure is a direction/shape detail), or materialise the fan before folding.  This is independent of the label scheme (unique markers, depth levels and
path labels all show it) and of whether recursion-referencing defs are precompiled;
the next diagnostic is to dump the compiled net for `(add 8 5)` in both builds and
compare what the `_add` LAM's principal port is wired to.  Before the meet existed the knot never became inert at all
(traced: LAM×APP and DUP×DUP redexes still firing at step 3000, node ids still
climbing) — the unrolled chain has no such problem because its leftover is inert
(unapplied lambdas) that the reachability GC reclaims, whereas a live cycle cannot
be dismantled because erasure is **passive**: `net_interact` has no ERA×DUP / ERA×LAM rule
(those pairs are dropped, "as in the reference") and erasure works by leaving ports
dangling.  A knot therefore needs either **active erasure** (ε×δ propagation — with
the caveat that the naive "erase both auxiliaries" rule is unsound when a fan
straddles an erase boundary) or a **level discipline** in which the cycle's fans
annihilate once and for all: today's unique-per-fan markers deliberately keep
unrelated fans from annihilating, which also stops the loop from closing.  Either
is a prerequisite for deleting the unrolling bound along with the `_rec` sentinel
and the widening machinery.  Two latent defects surfaced while doing this and are
part of the same work: a def in a namespace kept its self-reference *unqualified*
(`_padd` inside `num._padd`) because `qualify_free` ran before the def was
registered, and precompiling a def whose expansion mentions recursion is pointless
(there is no normal form to bake) yet burned the whole step limit.

## A2/A3: the knot, and why it is the same change as fan-sharing a def body

`def_precompile` bakes a **non-recursive** define into a reduced net (`d->compiled`)
and every reference clones it (`ct_splice`, one fresh re-gauged copy per reference),
while **recursive** defines (`d->rec`) take the textual path: `expand` copies the
body per reference and `build_bound_rec` wraps it in `k` unrollings whose innermost
base carries a `_rec` sentinel; if that sentinel survives reduction, `eval_form`
doubles `k` for every def and re-evaluates (16 rounds).  That is the machinery
behind the two pathologies we measured: nets oscillating 30,733 <-> 111,933 through
`widen_recursion`'s rounds (`(let ((g (mul 2))) (pair (g 3) (g 4)))`, and the shared
`_op` hangs generally), and the reason a *shared* closure's fold failure turns into
a blow-up rather than a slow path — the body being β-duplicated is the k-unrolled
one.

**The knot and "fan-share the body instead of copying it" are the same change.**
Compile the body **once**, with the def's own name bound to a placeholder port, then
wire that placeholder to the body's root: every self-reference is then a wire back
into the shared body (a self-referential net) and every *reference site* can be fed
from one spliced copy through a fan.  The compiler already has both halves of the
mechanism: `push_var` + `ERA` placeholders for a variable's later occurrences
(`ct`'s `TVAR`/`TLAM` cases), and `fan_lvl`/`dup_tree` for re-gauged sharing.  It
also gives mutual recursion for free (a cycle through two bodies is still just
wires), which today is not handled at all: `expand`'s guard stops at the cycle and
leaves a bare `TVAR`.

Budget: this **removes** `build_bound_rec` + `widen_recursion` + `net_has_reachable`
+ `REC_SENTINEL` + `eval_form`'s 16-round retry + the `rec_k`/`rec_body` fields
(~90 lines in `main.c`, measured) and adds a knot constructor plus a memoised splice
(~40 lines in `compile.c`), so the pure core goes *down*.  Core is 2,831 lines now.

**Knot attempt #1 (reverted).**  The construction above was implemented: in
`def_precompile`, a self-recursive define expands its body with its own name already
guarded, wraps it in `(\name body)`, compiles that, then links what the binder feeds
(the occurrence fan, or the single use) to the body's own root and re-points ROOT at
the body.  It builds, costs +33 lines (core 2,864), and leaves the working acceptance
cases alone (`(g 3)` -> 6, `(pair 8 15)`, `(pair 6 10)`) — but `test/selfrecursion.lin`
prints **nothing** where HEAD prints 24/120/15/16, so the knot's cyclic net does not
reduce (the same blocker class the first prototype hit).  Reverted.

**Where the hanging repros actually come from (new).**  None of the four hanging cases
involves self-recursion: they hang through the *non-recursive* `_op` wrappers (`mul`,
`add`).  `def_precompile` declines to bake any define whose open-body precompile hit a
suppressed fold — `op_value_from_lam` bumps `lin_stuck_ffi_count` whenever it is asked
to fold while `lin_precompile_depth > 0` (`src/io.c`), and the cache is declined when
that counter is non-zero (`src/main.c`).  So every `_op` wrapper stays **textual** and
is re-expanded per reference, and the shared case degenerates into the unrolled path
where the blow-up lives.  That is the concrete A2 lever: during an open-body precompile
a fold blocked by *free-variable* operands is not "stuck" — the pure-Lin beta body is
the semantics, and the fold simply happens later at run time when the operands are
concrete — so such a define can be baked (splicing the knot for its recursive parts),
which removes the unrolling that the hangs hide behind.

Consequence for sequencing: A2 and A3 have to land together.  A knot shares every
reference to the define through a fan, which is exactly the operand shape A2 must read;
and A2's lever (baking the `_op` wrappers) is what removes the unrolling the hangs hide
behind.  Acceptance for the pair: the four hanging repros, `test/selfrecursion.lin`,
the suite and the oracle.

Acceptance tests (all correct on HEAD, none of them terminating today):
`(let ((g (mul 2))) (pair (g 3) (g 4)))` -> (6, 8);
`(let ((g (\x (\y (mul x y))))) (pair (g 2 3) (g 4 5)))` -> (6, 20);
`(let ((g (mul 2))) (g 3))` -> 6 (works today);
`(let ((f (\x (\y (mul x y))))) (add (f 6 7) (f 3 4)))` -> 42 + 12;
plus the suite (53/978), the soundness oracle, and the sharing witnesses.

## The `_op` fold path: deferral is correctness-critical (measured)

A saturated pure-Lin `_op` closure (`((\_add <pure-body>) <_cl-spine>)`) is folded
to a scalar by reading its raw operands.  When an operand is not decodable yet the
reducer does **not** β-squash the redex: it parks the pair on a per-net blocked
list and re-examines it after each wave drains.  Two attempts to make that wait
*terminate* were implemented and measured on this tree — **both are unsound and
were reverted**:

| attempt | result |
|---|---|
| a fan-wrapped operand slot (`skipped == 2`) falls through to β instead of waiting | `test/modules.lin` returns **1** where the answer is **225** |
| deferral budget made net-lifetime (never reset by a fold, cap 4096) | same suite fails; a following suite hangs |

So the wait is not an optimisation that can be shortened: it is what keeps a
shared operand alive until it is concrete.  The fix has to make the shared operand
*readable* (fan-complete operand decoding — materialise or route through the fan),
never to skip the wait.

**A2's failing read, seen whole.**  A local-graph dump of the undecodable operand
slot in `(let ((g (mul 2))) (pair (g 3) (g 4)))` shows the slot resolving to a fan
whose principal faces an *auxiliary pin of an APP* and whose two auxiliary pins face
`_sz` (numeral) LAMs:

```
[SLOT-raw] 30750.0 tag=2 DUP   p0->30718.2 (APP arg pin)   p1->30770.0 (LAM '_sz')  p2->30774.0 (LAM '_sz')
```

`skip_dup` hops the principal and lands on that APP pin, which is not a value, so
the fold cannot read it; and reading *through* the auxes instead is unsound (that is
the shortcut that produced 225 -> 1).  So A2 needs the operand to become readable
*in the shared case* rather than a cleverer hop, which is why it is pursued together
with A3: with the unrolling gone the same program has no blow-up to hide behind.

Instrumented diagnosis of the shared-closure case
(`(let ((g (mul 2))) (pair (g 3) (g 4)))`):

- the failing pair is re-examined ~10³ times/s with `argc=0 skipped=1`, i.e. the
  operand slot resolves to a **DUP** (a fan) rather than a not-yet-reduced redex;
- the per-net `declines` budget never expires because any successful fold resets
  it, so the pair spins for ever (the pre-existing "shared `_op` closure hangs");
- the same pair is examined on **two different nets** (nn = 30,733 and 111,933):
  `eval_form`'s recursion-widening loop rebuilds the defs with a doubled
  unravelling bound whenever the `_rec` sentinel survives reduction.  Per-net
  bookkeeping therefore cannot carry state across waves (a persistent
  blocked-entry count was tried, observed losing its count, and reverted).

The hang is dominated by that recursion machinery rather than by the deferral:
single use (`(g 3)`) and two *separate* closures (`(let ((g (mul 2))) (let ((h
(mul 3))) (pair (g 4) (h 5))))` → `(pair 8 15)`) are both fine, and two nested
`_op` operands through a shared closure also work (`(pair 6 10)`).  This inverts
the earlier plan: the **knot (or another recursion mechanism) is the prerequisite**
for these cases, and fan-complete operand decoding comes after it.

## Type inference: order-dependence, and what fixing it costs

`generalize` (HM) used to scan **every** scheme in the live environment and treat
*all* its free vars as environment-free, including the scheme's own quantified
vars.  A scheme's quantified vars are bound by the scheme, so this
under-generalises every later definition against every earlier one — inference
results depend on the order defs are checked in.  It is sound (it rejects some
well-typed programs rather than accepting ill-typed ones) but it is what made the
parallel def loader produce "infinite type"/"unbound variable" errors, and it is
why a shared `_op` closure could infer differently from an unshared one.

Two fixes were measured on the std load (`(load "std/std.lin")`, type checking is
370 ms of the ~410 ms load), interleaved A/B, 3 runs each:

| build | std load |
|---|---|
| committed | 400-440 ms |
| incremental `efree` counters, *old* (over-)inclusive semantics | 508-518 ms |
| incremental `efree`, correct HM semantics (skip `s.q`) | 597-617 ms |

So the ~+100 ms is the maintenance scan (`fv` per push/pop, 593 def pushes at
load) and another ~+100 ms is the *semantics*: correct generalisation makes
schemes more polymorphic, and every use site then instantiates more type nodes.
Neither was landed: +50 % on every program's startup for a latent
(not currently observable in serial loading) incompleteness is a bad trade.

The next attempt should remove the scan rather than pay it: `env_find` already
falls back to `def_find`, so the 593 def schemes need not be pushed into `env` at
all (they contribute no *mono* free vars — a closed def's scheme has none once
`generalize` has run), leaving `efree` to track only local bindings, whose
schemes are one `TVR` and cost O(1).  That should leave only the semantic ~+100 ms
to argue about.

## Parallelism: measured, and where it does and does not pay

Reduction is **not** where Lin's time goes.  On the workloads in `test/` and
`benchmarks/` the reducer accounts for ~3% of a run (`test/nqueens.lin`: 29 ms of
849 ms, 38142 steps; `test/string.lin`: 6.8 ms of ~1600 ms, 4820 steps), and the
fixed cost of every run is loading `std`: ~410 ms, of which **~370 ms is type
checking** 593 defs (`process_def`), 10 ms is qualification/registration, and the
rest is parsing.

Two consequences, both measured:

- **The wave reducer's parallelism does not amortise.**  A wave is usually small
  (`test/string.lin`: 4621 waves under 64 redexes, 48 under 128, 326 under 256,
  5 under 512, **none** ≥ 512), and the multi-redex waves that do occur are cheap,
  so a fork/join per wave costs more than it saves.  Threads are therefore left
  off unless asked for (`-t` / `LIN_THREADS` / `OMP_NUM_THREADS`).  Measured on
  `test/numbers.lin`: 13.2 s with everything serial, 15.6 s with OpenMP's own
  default, and 13.4–14.9 s when the parallel threshold is raised to 2k–32k — i.e.
  no configuration beat serial.  (Note `omp_set_num_threads(...)` called at
  runtime also measured worse than leaving OpenMP's default alone, so the core
  does not force a thread count.)
- **Type checking does parallelise well, but not yet soundly enough to switch
  on.**  Type checking is 90% of the fixed cost and is independent per def, so
  defs were queued and checked in dependency-ordered batches across threads: it
  makes `std` load twice as fast (416 → 208 ms) and small programs 25–33% faster
  (`test/tsp.lin` 452 → 318 ms).  It was *not* landed, because batching only
  preserves the loader's exact semantics if a def's inferred scheme does not
  depend on which *unrelated* defs were registered before it — and it currently
  does: `generalize` counts a scheme's **quantified** type variables as free in
  the environment, so an extra earlier def makes a later scheme *less* general.
  Making that rule standard (only unquantified variables block generalization)
  removes the order dependence, but costs 18–28% on the def-heavy programs
  (`test/numbers.lin` 13.3 → 15.7 s, `test/selfrecursion.lin` 3.4 → 4.4 s), which
  outweighs the gain.  That latent order-dependence is worth fixing on its own
  terms (a def's type should not depend on unrelated defs), separately from
  parallelism.

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

The full suite is green: **53 suites / 978 assertions** (Tiers 1-6: core
primitives, FFI/system drivers, SAT & term rewriting, non-trivial workloads,
`.line` containers, and CLI invariants, plus the independent soundness oracle
below).  A driver's native folds are asserted
by `(folded)`/`lin_folds` in the driver suites; cross-driver correctness is
asserted by the canonical selftest (`test/driver_selftest.sh` validates every
driver against the base-CPU golden via `std/selftest.lin`); the GPU driver's
per-wave bit-exactness is asserted by `LIN_GPU_SELFTEST` through the shared
`std/drivers/selftest.h` harness (no mismatches on a device).

**Values are pinned to an independent oracle, not to the suite's own comments.**
`test/soundness_enum.py` (Tier 2.6, in both runners) evaluates the boolean
formulas of `test/sat.lin`, `test/sat_verify.lin` and `test/tseitin.lin` by
ordinary lambda evaluation — no nets, no fans, no sharing — and requires the
engine's readback to agree (35 evaluations, all comparison-free of the `; expect`
comments).  This exists because the suite once *asserted* the wrong values the
unsound fan sharing produced: `sat_verify.lin` labelled its own answer a
"superposition collapse false negative".  Editing an expectation can no longer
make an unsound engine pass, and the oracle fails loudly if its vocabulary stops
covering an expression rather than skipping it.

## Readback: render once, replay for the shared rest

`print_port` carried `vis_print[]` as a *cycle* guard (set on entry, cleared on
exit), so a DAG-shaped result was fully re-walked at every sharing point — the
printed size is exponential in the number of sharing points even though the net
is small.  (An earlier note blamed `benchmarks/bench_combinators.lin` for this;
that benchmark still does not complete even with the memo — >122 s on both builds
— so its cost is *not* printing and stays an open item.  The memo's evidence is
the synthetic repro below, where output is byte-identical.)

The printer now appends into a buffer and memoises the rendered text per
`(node, port)` (`viz_txt[]`, freed with the net), replaying it on later visits.
A render is memoised only if it emitted no `?` on the way in: a `?` means the
text was shaped by an in-progress ancestor (a real cycle), so that text is not
context-free and must not be replayed.  Output is byte-identical — measured on a
nested-sharing repro `(let ((f (\x (pair x x)))) (f (f … (f 1))))`:

| sharing depth | before | after | output |
|---|---|---|---|
| 12 | 726 ms | 420 ms | 53,240 B, byte-identical |
| 16 | >240 s (killed) | 793 ms | 851,960 B |

`f` is fan-shared (the landed sharing soundness work) and each `(pair x x)` shares
its `x`, so depth *n* is 2^n print work while the net stays O(n).

## Line budget

Pure core `src/` (`.c` + `lin.h`): **2,831 lines** (< **3,000 target**; the
non-core readback runtime in `src/runtime_io.inc` is std and not counted, and the
whole `.inc` set is 3,170).  The
pure-Scott de-laddering added the driver-foldable `_op` machinery
(`lin_fold_op`/`lin_fold_op_arg`/`op_value_from_lam`, `net_spine_args`, and the
`_op` deferral + eager-argument-fold edges) in `src/io.c`/`src/net.c`, which is
what lifts the count; the integer arithmetic itself was already retired to
`std/drivers/arith.so`, so the migration costs fold machinery in the core rather
than removing rows.  The fold machinery was then consolidated and generalised —
one shared `_cl`-spine walk (`decode_spine`), one shared `_ffi`-header dig
(`ffi_header`), a Scott-spine `scott_peel`, a fold-result `fold_link`, and a
shared beta `fold_arg` edge — and expository comments/blank lines were compressed
(3,085 → 2,923).  The arithmetic table, drivers, and `std/runtime/*` live outside
`src/` and do not count against the core.

## Status (honest)

**All green: 53 suites / 978 assertions.**

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
- Core LOC is ~2,923, under the **3,000 target**: the pure-Scott `_op` machinery
  is a deliberate cost, now consolidated (shared `decode_spine`/`ffi_header`/
  `scott_peel`/`fold_link`/`fold_arg` and compressed comments).  The driver
  fold paths (`simd.c`'s `_ffi` arg-decoding) still parallel the core's shared
  decoder; a fuller consolidation of each driver's net-side walk would reclaim a
  little more headroom.

**Journey / lessons (compressed history).**  Earlier rounds documented in
detail: Y-combinator recursion strands its base value on a continuation knot;
deep windows in `num.lin` exploded node counts; a fold-on-saturation gap made
composed direct-FFI comparisons strand until the fold-routing/deferral fix
landed; readback folds and `lin_precompile_depth` suppression were incremental
steps toward it.  These were resolved by the bounded self-unravelling and the
deferral fix above; the per-round investigation is preserved in git history.

## Standard library rework: `(export <ns>)`

The std modules carried a per-module boilerplate tail — `(namespace _) (open X)`
plus a hand-written `(define! y X.y …)` alias for every public name (~230 lines
total).  A new compiler form `(export <ns>)` re-exports a namespace's public
members into the current (root) scope in one form: `(namespace _) (export X)`.
Each export is routed through `process_def` (matching the old `(define y X.y)`
aliases exactly), `_`-prefixed members are treated as private and skipped, and
last-loaded-wins resolve bare-name collisions the way the old alias modules did.

The whole std was migrated to this template, with two idioms applied per module:
- **Global-safe public names**: members are named so `(export X)` exposes the
  exact bare names consumers use and nothing that collides across modules (e.g.
  `str_eq`/`streq`/`maybe_map`/`empty_queue`/`io_read`; never a naked `eq`,
  `length`, `head`, `empty`, …).  Qualified-only short names consumers still
  reach (e.g. `str.eq`, `stream.nth_c`, `io.print`) are bound as dotted aliases
  after the export so they resolve without re-exporting bare.
- **De-laddering**: hand-unrolled positional families (list `first..eighth`,
  string `length`/`concat`, map/set insert-ladders) were collapsed onto a single
  terminating recursion or shared internal `_`-helpers without changing public
  semantics.

A proper distinct `float` annotation type remains a compiler/type-checker task
(annotations only have builtin atoms `num`/`bool`/`a`/`(list a)`); `float.lin` is
reworked to the export template but its ops stay `num`-typed.  Suite: 53/978.