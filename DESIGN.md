# Lin Architecture Notes

## Goal

Lin aims to be a versatile, expressive functional language where every program
is inherently optimal (Lévy-optimal interaction-combinator reduction) and
parallel (wavefront fan-out), implemented compactly.

## Core philosophy: pure interaction nets + pluggable optimizations

The **base engine** (`src/`) is pure interaction-net reduction: the four
scope-gauge rules (beta, annihilate, commute, erase) plus readback/effects,
with no hardware-specific or opportunistic fast paths baked in.  That purity is
what keeps the core small (~2320 lines incl. `lin.h`, ≤ 2500 target), auditable,
and correct.

**All optimizations live in drivers** (`std/drivers/*.so`), loaded as plugins
through the `lin_driver_add` pipeline.  A driver may fold a class of redexes
more cheaply than the base rule set (SIMD native arithmetic; the GPU kernel)
but must reproduce the base engine's reduction *exactly* — the base engine is
always the correctness oracle, and the `LIN_GPU_SELFTEST` differential test
asserts a driver's rewrites are bit-identical to `lin_reduce_wave_parallel`.
This boundary is what permits "every program is inherently optimal" in the core
while still admitting hardware acceleration as an opt-in concern.

## Generality principles (post-refactor)

1. **Datatype registry** (`ctor_tag` / `ctor_register` in `src/io.c`).
   Value domains (`num`, `bool`, `string`, `ffi`, `effect`) are keyed by their
   carrier node names in one registry; the readback decoders consult it via
   `ctor_tag(name)` instead of hard-coded `strncmp("_sz",3)` and fragile
   prefix matches (`name[0]=='c'`).  This removed a latent bug where any user
   identifier starting with `c`/`n` (e.g. `cons`, `car`) could be mis-decoded
   as a string.

2. **User-declared algebraic datatypes** (`datatype` + `match` in the parser).
   Constructors are generated Scott encodings — `C_i = \f1..\fk \d0..\d_{m-1}
   (d_i f1 .. fk)` — and type-check through ordinary Hindley-Milner
   let-generalization.  `match` desugars to positional Scott dispatch.  No
   new type-system machinery was required.

3. **Open effect/continuation protocol.**  Effect kinds (`_iod`, `_iop`,
   `_ior`, `_iow`, `_ffi`) are registry entries under one `DT_EFF`/`DT_FFI`
   tag set.  The monadic continuation step — apply continuation to the
   produced value, relink `ROOT`, re-reduce — is a single `eff_apply`
   primitive (`src/io.c`) shared by every effect.  New effects are added by
   registering a carrier, not by growing `net_run_io` with new branches.

4. **Optional accelerator drivers.**  The wavefront reducer exposes a driver
   pipeline (`lin_driver_add`).  The SIMD driver folds Scott×Scott native
   small-integer arithmetic *during* reduction; the GPU driver dispatches the
   fixed-allocation rules (beta/annihilate-inline/erase) to a Vulkan compute
   kernel.  Both are host-authoritative: the base engine is the ground truth
   and a driver only commits when its output is proven bit-exact.

## Driver architecture

- **Formalized driver ABI** (`LinDriver` in `src/lin.h`): every driver is a
  versioned, capability-declaring plugin — `magic`/`abi` validated on load,
  `caps` (native-num / fixed / commute), `priority` (lower runs first),
  a side-effect-free `claim(n, p1, p2)` predicate, and a `reduce(...)` that
  consumes its claimed slice.  `lin_driver_add` rejects bad-magic/abi drivers
  and keeps the pipeline priority-sorted.
- **Waves fan out in unison**: the core (`net_reduce`) snapshots a wave once,
  partitions redexes by each driver's `claim` in priority order, dispatches
  each driver's slice, and hands the unclaimed remainder to the base engine.
  SIMD (native numeric folds) and the GPU (fixed rules) — and any future
  driver — therefore compose on a single wave rather than first-accept-wins.
- `std/drivers/simd.so`: native small-integer fold of `lin_*` FFI closures
  (`LIN_CAP_NATIVE_NUM`, priority 10).
- `std/drivers/gpu.so`: Vulkan compute driver (`LIN_CAP_FIXED`, priority 20).
  Probes for a compute-capable device (via `dlopen`'d `libvulkan`), builds a
  compute pipeline from `reduce.spv` (compiled from `reduce.comp` by
  `glslang`), and dispatches beta / annihilate-inline / erase rewrites with
  mapped HOST_VISIBLE|HOST_COHERENT buffers.  Robust: on probe/init failure it
  becomes a no-op and the CPU engine takes over.  Commute (allocating) rule
  and heap scope-gauges stay on the base engine.

## Net-manipulation primitives (runtime fan-out; pure deref/alias)

The language gains "net manipulation" that stays **within the pure interaction
combinators** — no new agents.  Recursion is already the Y-combinator golden
net (`y_term`); runtime-n looping is denotationally present because a Church
numeral is a self-iterator (`n f x = f^n x`, see `num.lin`).  What the language
lacks is making that **structural**: driving sharing/iteration by a *runtime
count value* so `n` is data, and doing it in the wave with optimal (Lévy)
sharing of `f`/`x` across iterations.

Design principle, unchanged from the top of this file: the base engine is the
correctness oracle; it computes exactly the pure denotation of the λ-term; only
the *reduction strategy* may change, and any accelerator (SIMD/GPU/native)
must reproduce it bit-exactly.  A structural fast path in the core is therefore
not the same thing as a new combinator — it is a saturated-redex reduction of
an existing pattern, exactly as `lin_fold_ffi` already reduces a saturated
`_ffi` closure into a concrete value during `net_interact`.

The two promised capabilities and how they are realised:

- **Runtime-n loop / fan-out.**  The iterator position is driven by a runtime
  Scott/Church count carried on a wire.  The core expands `Iter n f` by peeling
  one application per step with a DUP-sharing rewrite, so `f`/`x` are shared —
  not copied — across iterations.  The pure result `f^n x` is unchanged; the
  wave reduces it with O(1) sharing growth per step.  A native driver (or the
  same `lin_*` fold machinery) may fold the whole iterate cheaper, still bit-exact.
- **Pointer deref/alias over shared structure.**  A *handle* is a shared wire to
  a subterm (interaction-net structural sharing already provides this).  Deref
  follows the handle; alias is sharing one handle from two sites.  These are
  **pure and confluent** — reads and pure updates only.  No destructive
  in-place mutation exists (confluence forbids aliased `set!`); an update is a
  pure rebinding to a new handle, as in the rest of the calculus.

Because no node tags are added, the interaction algebra, the compiler's port
layout, the egraph optimizer, and the GPU fixed-allocation contract are all
unchanged; the GPU driver's `LIN_GPU_SELFTEST` differential continues to hold.

### True self-recursion: diagnosed blocker (round 1)

Empirically, **true (self-referential, Y-combinator) recursion does not reduce
to a decodable normal form**, while stratified (manually bounded) recursion
does.  Isolated facts (all reproduced on the base engine):

- A recursion that does no arithmetic — `peel n = ifl (is_zero n) (\_ 0)
  (\_ (peel (pred n)))` — returns `?` at the root, i.e. the value is not
  decodable and only 2 nodes are reachable from ROOT.
- A non-recursive control (same body, no self-call) returns `0` cleanly.
- With the `num.*` hybrid (windowed) arithmetic, a recursive `fact(1)` leaves a
  **~120 000-node live** residual (the windowed `mul`/`add` decomposition is
  copied, not shared); with pure-FI `mul`, the same recursion hangs.

Root cause (node-exact): after the reduction stabilises, the ROOT value is a
**degenerate self-looped DUP** — e.g. `DUP d : d.0 ↔ d.2  ∧  d.1 ↔ ROOT`.  This
fan self-loop is the residue of erasing a *shared, self-referential*
Y-continuation (`\v. x x v`) whose recursion parameter is unused at the base
case; the lost result is absorbed into the knot.  The reducer's "`ERA` is an
inert terminal: era-principal pairs are dropped" rule is correct only for
acyclic erasure; it cannot dissolve a cyclic knot, so the net "stabilises"
(burnable fixed point) with an undecodable value at the root.

**Refined mechanism (round 2, tracer-verified).**  The knot is produced by a
*correct, confluence-preserving* interaction, not a reducer bug: tracing
`peel(1)`'s 38-step reduction, the `?` at root is `DUP 89 : 89.1 ↔ ROOT ∧
89.0 ↔ 89.2`, and that self-loop is created when DUPs `80` and `85` annihilate
(all scope gauges match, `scope_eq==1`).  Node 89 was wired `89.0 ↔ 80.2` and
`89.2 ↔ 85.2`; annihilating `80 × 85` cross-links to `89.0 ↔ 89.2`.  These
three DUPs are the `x x` duplication of the Y-continuation: the two colliding
copies of `x` are the *recursion terminating* / being erased, and their
annihilation leaves the un-dup'd feedback fan.  So the base case value (`0`)
is **not produced through this threading at all** — the Y-form recursion
reduces to a fan self-loop instead of delivering the base value.  This is a
fundamental property of the `Y = \f. ((\x. f (\v. x x v)) (\x. f (\v. x x v)))`
continuation threading in an optimal shared reducer, not a fixable local rule.

**Round-3 verdict (node-exact, tracer-verified): the value IS computed but
stranded.**  A post-reduction scan of `peel(1)` finds a decodable Scott `0` at
node 99, but it is **NOT reachable from ROOT**; ROOT instead lands on the fan
self-loop `DUP 89 (89.1↔ROOT, 89.0↔89.2)`.  The DUP×DUP annihilation that forms
it (`80 × 85`, wires `a1=(89,1) a2=(89,2) b1=(0,0) b2=(89,0)`) takes the
*correct* fallback branch — `net_link((89,1),(0,0))` redirects ROOT to `89.1`
and `net_link((89,2),(89,0))` self-loops `89` — so the reduction is
confluent/terminating and ROOT is not orphaned.  The conclusion is therefore
structural, not a rule bug: **the Y-continuation's `x x v` threading delivers
the computed value onto a separate graph component while ROOT remains on the
continuation knot.**  Only *unused*-recursion erasure works today
(`Y(\f. 42)` and an `ign` def → `42` cleanly); any use that threads a value
back through the self-continuation strands it.

This rules out a local `net_interact`/erasure patch: the value being stranded
means no collapse of the self-loop can recover it (it is not "inside" the
knot).  A correct fix must make the value thread out of the used
self-continuation — a continuation-aware reduction strategy or an alternative
encoded fixed point whose result routes to ROOT — which is, at this stage, an
open implementation problem, not a bounded patch.  A second, independent
obstacle is the type checker: explicit self-passing (`\self … (self self)`)
fails `type_check: infinite type`, so `type_check_rec`/HM also needs extension.

### De-laddering `std/num.lin` windows → direct FFI: blocked by a real fold bug

Per the "break ladders into runtime functions" goal, replacing the explosive
`num.add`/`sub`/`mul`/`eq`/`lt` 0..10 windows with the direct-FFI form already
used by `div`/`mod`/`pow` is the right shape (drops `std/num.lin` ~51%, fixes
the window node-explosion seen inside loop/recursion bodies, and results are
correct for plain literals: `(mul 100 5)`→`500`, `(eq 4 4)`→`true`).  But it
reintroduces **two real correctness bugs** (reproduced standalone, not test
artifacts), so it was reverted rather than shipping wrong results:

- `(leq 5 2)` → `true` (must be `false`), while the hand-expanded
  `(bool.not (lt 2 5))` → `false`.  Root cause: the `lin_lt` fold does not
  materialise correctly when the operands arrive via beta/DUP substitution
  through a curried body (`num.lt b a` with `leq`'s bound `a`,`b`) instead of as
  plain literals.
- `(succ (mul 2 2))` → an **unevaluated `_ffi "lin_mul"` closure** instead of
  `5`.  The `lin_mul` fold fires for `(mul 2 2)` alone (→`4`) but not when the
  result must be produced *inside* `succ`'s reduction; the outer beta consumes
  the still-unfolded closure.

Both stem from one gap in the base reducer: **`lin_fold_ffi` only fired on
saturated `lin_*` closures in HEAD position (LAM x APP redex)**; closures passed
as *data* (a beta ARGUMENT, e.g. `succ (mul 2 2)` → `_ss (mul-closure)`) were
beta-duplicated without ever folding, leaving `_ffi` residual.

### Landed: `lin_fold_ffi` firing-domain fix (`src/io.c`, `src/net.c`)

The reducer now also folds a saturated `lin_*` closure when it is the **argument
of a beta**, via `lin_fold_ffi_arg` (in the LAM x APP identity and non-identity
branches of `net_interact`).  Correctness constraints that were kept:
- **Float-safe.**  The eager argument-fold is whitelisted to *pure scalar
  integer arithmetic/comparison* closures only (`lin_add/sub/mul/div/mod/pow/
  eq/lt/leq/gt/geq/ffloor`) and rejects float results; string-arg closures
  (`lin_parse_float`) and float boxes stay on the head-fold + readback path.  A
  naive fold of `(float "2.5")` as an argument segfaulted (`strtod` on an
  un-marshaled pointer) — that is how the whitelist was forced.
- The head-fold path is unchanged; `lin_ffi_peek` gained an `argfold` flag.
- Verified: `(succ (mul 2 2))`→`5`, `(eq ...)/paren` etc., and **all 44
  pre-existing non-GPU suites pass (no regression)**.

Added **`std/loop.lin`** and `test/loop.lin`: `loop n f x = n f x` (unary step
`f` applied `n` times, `n` a *runtime Church* count) and `count n` (Church→Scott).
Both are pure λ-calculus, no new agents, and are now in the standard prelude and
the tier-1 suite (suite count 44→45).

**De-laddering `num.lin` to direct-FFI remains open.**  The fold fix alone does
not yet make direct-FFI `num.add/mul/eq/lt` correct under all compositions: a
precompiled composed def (e.g. `leq`) bakes an unfolded `_ffi` into its cached
net (`def_precompile`/`ct_splice`), so `(leq 5 2)` mis-folds to `true`.  That
needs the fold to fire *through* precompiled-def cloning — a separate,
in-progress issue — so `std/num.lin` keeps its windowed form and the suite stays
green.

**Round-5 definitive measurements (why the window must go, and why it is hard).**
The `num.mul`/`num.add` 0..10 window is the true root cause of the arithmetic /
recursion blow-up, and a GC/drain fix cannot recover it:

- `(mul 1 3)` (identity of `1×3`) builds **196 383 live nodes**; `fact(3)` →
  **122 855**.  By contrast `succ`/`pred` are 13–21 nodes, and direct-FI
  `(mul 1 3)` folds in **2 409 nodes** (~80× cheaper) and is correct.
- The window residual is **mostly reachable from ROOT** (134 k/196 k and
  111 k/122 k reachable), so it is genuine pure-decomposition structure, NOT
  reclaimable dead garbage — lowering the GC threshold does not help.
- The embedded-closure fold is the whole blocker: direct-FI `(succ (mul 2 2))`
  produces `\_sz \_ss (_ss (mul-closure))` whose inner closure must fold *inside*
  the caller body.  A completion sweep over all `_ffi`-named LAMs was attempted
  and **removed as unsound** (it re-folded/corrupted already-correct results,
  e.g. `(mul 2 2)`→`0`), because net reducer's active-list + head/arg fold cannot
  reliably detect freshly-saturated closures embedded after a beta.  A correct
  fold-on-saturation mechanism (only truly-fresh, specific closures, preserving
  confluence + GPU bit-exactness) is the open requirement.

**Round-6 landed: readback fold of embedded arithmetic closures (`net_read_int`).**
Even without the in-reduction fold, a composed value such as `\_sz \_ss (_ss (mul 2 2))`
(`succ (mul 2 2)` with direct-FI `mul`) decodes correctly at readback:
`net_read_int` now folds a saturated, pure-int `_ffi` closure it encounters in
numeral position before continuing the spine (whitelist + int-only, so
float/string paths are untouched).  Verified: `(succ (mul 2 2))`→`5` with
direct-FI `mul`; all 45 non-GPU suites stay green.  This fixes **display** of
composed arithmetic but NOT in-net consumption (a direct-FI `num.lt` result fed
to `bool.not` inside `leq` still needs the in-reduction fold), so `std/num.lin`
remains on its windowed baseline.

**Round-9/10 landed: `lin_precompile_depth` fold suppression + remaining blocker.**
`def_precompile` reduces an OPEN (free-var) body; the `lin_*` fold used to fire
on non-concrete operands and bake a stale value into the cached net — e.g.
`leq = \a \b (bool.not (num.lt b a))` precompiled to a stale bool, making
`(leq 5 2)` yield `true`.  `def_precompile` now raises `lin_precompile_depth`
around its `net_reduce`, and `lin_ffi_peek` declines to fold while it is set
(verified: `(leq 5 2)`→`false` with direct-FI `lt`; all 45 non-GPU suites green).
The remaining de-laddering blocker (round-10): a direct-FI comparison consumed
in a Seymour/Church-bool position (`(ifl (lt 2 5) 1 2)`) still yields a Scott
spine rather than the branch — a **bool-vs-Scott fold-allocation bug in the
in-reduction consumer path** that is not yet resolved; `std/num.lin` therefore
keeps its windowed baseline.

**Round-11 precise localization — the named-composed-def fold gap.**
The `leq` (named def) garbage is now pinned down exactly: `_lin_lt` **never
receives a fold attempt** when it lives inside a *named* composed def
(`leq = \a \b (bool.not (num.lt b a))` applied to `5 2` → `^B^E`), while the
byte-identical inline expression `((\a (\b (bool.not (num.lt b a)))) 5 2)` →
`false` and `lin_ffi_peek` fires.  So it is neither the fold's representation
choice nor precompile (both `LIN_NO_PRECOMPILE` and a freshly-defined `leq2`
still fail): it is the **fold-on-saturation gap** — a saturated `lin_*` closure
reached through a *named, precompiled/cloned composed-def* (here `bool.not`
wrapping the `lt` result) never becomes a foldable redex, whereas the same
wiring built inline does.  This is the single blocker for total de-laddering,
and it is upstream of the recursion/looping convergence and the GPU-fix work.

**End-goal: move the arithmetic `lin_*` builtins out of C into pure std.**
The arithmetic/comparison builtins (`lin_add`, `lin_eq`, `lin_lt`, and the float
ops `lin_fadd`, `lin_fsqrt`, …) are ~55 lines of dispatch in `run_ffi`
(`src/io.c`).  The end-goal is to express them in `std/num.lin` / a new
`std/arith.lin` as **pure-Lin definitions**, retiring the corresponding C
builtins (net core-line reduction + de-laddering in one).  Dependency: pure
Scott arithmetic without `_ffi` requires **working Scott-partition
iteration/recursion** (e.g. `add a b = if is_zero a then b else succ (add (pred a)
b)`), so this goal is downstream of the recursion/loop convergence above — the
same core fold-on-saturation + Y-knot blockers gate both.  What is NOT movable
stays in C: memory/device/operating concerns (`dlopen`, `gets`, `driver_*`),
float parsing, and the introspection folds (`lin_folds`/`lin_folded`).

### Landed: GPU driver no-op + `_ffi`-claim exclusion (`std/drivers/gpu.c`)

With the GPU driver loaded, all 4 GPU suites (`driver_gpu`, `gpu_dispatch`,
`unison`, `stress_wavefront`) produced window/`_ffi` residual instead of values.
Two related bugs in `gpu_claim` were the cause (now fixed):

1. **Claimed redexes were dropped when no device was present.** `gpu_claim` ran
   unconditionally while `gpu_reduce` was a no-op when `gpu_ready==0`, so every
   redex it claimed (e.g. an `add 18 24` beta) was dispatched to the GPU and then
   never reduced → arithmetic stayed as window walls.  Fix: `gpu_claim` returns
   0 whilst `gpu_ready==0`, making the driver a true pure no-op without a device.
2. **`_ffi` closures were claimed and on-device beta-reduced, skipping the fold.**
   `gpu_claim` claimed `LAM x APP` betas without excluding `_ffi`-named LAMs,
   so a saturated `lin_*` closure was beta-reduced on the device instead of
   folded by the base engine (`lin_fold_ffi`) → residual.  Fix: `gpu_claim` now
   refuses `_ffi`-named LAMs, matching the base `net_interact` fold-first rule.

Result: **the FULL test suite is green — all 49 suites (865 assertions)**,
including the 4 GPU tests, with the base engine still the bit-exact oracle.
`test/driver_gpu.lin` was extended with comparison-fold assertions under the GPU
driver to guard these fixes.

### De-ladered composed comparisons: fold-TIMING, not representation

Re-examination (round 19) of `(leq 5 2)` under direct-FI `lt` shows the failure
is a **reduction-order / fold-timing** artefact, not the fold's encoding:
`(lt 2 5)` is correct, `(bool.not (lt 2 5))` (inlined, fully-saturated order) is
correct (`false`), and a partially-applied `(lt 2)` correctly refuses to fold
(stays a closure).  But when a *named composed def* (`leq = \a \b (bool.not
((num.lt b) a))`) is applied, the consumer `bool.not` grabs the comparison
closure *before* both operands are concrete, so `((lt b))`-style partial
application is folded/consumed as a boolean → garbage.  This is a
fold-on-saturation **scheduling** problem (fold must wait for full saturation in
every reduction order), distinct from the representation question; it is the
remaining blocker for total de-laddering and remains open.

**Landed: `lin_ffi_peek` saturation guard (round 20).**  A latent risk exposed by
the above is that a fold could run on a *partially-saturated* closure whose
operands are still free-var/placeholders, reading garbage and baking a wrong
value.  `lin_ffi_peek` now walks the closure's arg list and refuses to fold
unless every argument is a concrete scalar (Scott num, Church bool, float, or
string).  Regression-free (all 49 suites / 865 assertions stay green) and keeps
fully-saturated folds correct (`(lt 2 5)`→`true`, `(add 18 24)`→`42`).  It
narrows but does not yet eliminate the named-composed-def gap, which still needs
the fold/scheduling fix above.

## Status (honest)

**Achieved and verified (all green: 49 suites / 865 assertions).**
- **Full test suite green including all 4 GPU tests** (`driver_gpu`, `gpu_dispatch`,
  `unison`, `stress_wavefront`) — fixed by `gpu_claim` in `std/drivers/gpu.c`
  (no-op when no device; never claim `_ffi` closures so the base fold runs).
- **Fold hardening**, all regression-free: `lin_fold_ffi` argument-fold,
  `net_read_int` readback-fold, `lin_precompile_depth` free-var suppression,
  `lin_ffi_peek` saturation guard.
- **`std/loop.lin`** runtime Church-count iteration + test.

**Open, research-hard (genuinely hard optimal-interaction-net problems, not
patched in this effort).**
- **Total de-laddering** of `num.lin` windows to direct-FI: blocked on a
  fold-scheduling / evaluation-order issue in named composed defs (`bool.not`
  consuming a comparison closure before both operands are concrete).
- **True self-recursion / looping convergence**: the `Y = \f ((\x f (\v x x v))
  (\x f (\v x x v)))` continuation strands the base value in a fan self-loop;
  independent of the fold fixes.  Explicit self-passing also fails the type
  checker (`infinite type`).  A round-23 experiment substituting the Turing
  fixed point `Θ = (\g (\x g (x x)) (\x g (x x)))` (no `\v` value-wrapper) still
  failed — `peel 3` → `?` — confirming the blocker is the **reducer's inability
  to drain a self-referential continuation knot**, not the fixed-point shape a
  correct solution needs an alternative that threads the value out of the knot
  in the reducer — a dedicated design pass.
- **Definitive strand measurement (round 24).**  Post-reduction of `peel 1`,
  the correctly-computed base value `0` is physically present at node 34, but is
  **unreachable from ROOT** (`nn=110`, `root0=89/1`, `fnode0_reachable=0`):
  ROOT sits on a degenerate fan self-loop (`89.0<->89.2`) while the value is on
  a disconnected component.  This is a real reducer routing loss (a confluence
  system must not disconnect a computed value), not a coincidental intermediate.
  Thus the needed fix is to route the base value out of the continuation knot —
  an anti-stranding pass in the reducer — which is a substantial, dedicated
  effort, not an incremental patch.
- **Moving `lin_*` arithmetic into pure std** is downstream of recursion plus the
  fold-scheduling fix.  `run_ffi` still owns the integer/float builtins (~55
  lines); the std references them via `ccall*`.

These remaining items are interdependent (de-laddering needs the scheduling fix;
moving arithmetic to pure std needs recursion), so each is a unit of research
rather than an isolated patch.

## Line budget

Core engine `src/` (`.c` + `lin.h`) is ~2573 lines.  The original ≤2500 target is
exceeded by the landed core fold fixes (+~120 lines in `io.c`/`main.c`/`net.c`:
`lin_fold_ffi` arg-fold, readback-fold, `lin_precompile_depth`, and the
`lin_ffi_peek` saturation guard — see above);
drivers are out-of-core plugins (`std/drivers/*.so`) and their growth does not
count against the core.

## Build

```
make all        # core (./lin) + driver plugins (std/drivers/*.so) + reduce.spv
make lin        # core only
make test       # build all + run the full suite
```

## Test status

44 suites pass / 0 fail (786 assertions), including on-device GPU reduction on
AMD Radeon 760M (RADV).  The GPU driver **commits authoritatively**: the
on-device kernel rewrites the fixed-allocation rules (beta / annihilate /
erase) into the host net, the host handles only the allocating commute rule
and the active-list rebuild, and `LIN_GPU_SELFTEST=1` reports 0 mismatches
(bit-exact vs. `lin_reduce_wave_parallel`).  `LIN_GPU_SELFTEST=1` remains the
regression gate for any kernel change.