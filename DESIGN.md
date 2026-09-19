# Lin — Design

Lin is a functional language whose evaluation model *is* an interaction net. A program is
compiled to a net of agents and wires; running it is cut-elimination on that net; the
answer is a value read back out of the normal form. There is no intermediate abstract
machine, no runtime graph rewriting a heap of closures, and no garbage collector in the
usual sense — allocation and reclamation are consequences of the reduction rules.

Lin is an **AOT-compiled language**: `lin build` is the compilation model and the artifact is the
deliverable — a residual net plus the runtime that reduces it. The same runtime can evaluate a term
directly (`lin prog.lin`), which is that architecture driven without the build step: a development
convenience, not a second implementation. Every cost this document talks about is therefore measured
on the artifact — how many bytes ship, and how much work is left for the runtime.

That choice is what makes the two headline goals achievable at all:

- **Inherently optimal.** Sharing is a first-class net structure (fan nodes with a gauge
  discipline), so a shared sub-computation is reduced once and its result distributed.
- **Inherently parallel.** The rules are *local*: a redex is two principal ports meeting,
  and whether two redexes are independent is a structural property of the net, not the
  result of a dependence analysis.

Everything else in this document exists to keep those two properties honest: a core that
is complete by itself, and every opportunistic or hardware-specific concern pushed out of
it into drivers and the standard library.

---

## 1. Goals

**G1 — Optimality by construction.** Sharing is expressed in the net, so evaluating a
shared sub-term once is the *default* behaviour rather than an optimisation pass that has
to be trusted. Measured today for acyclic sharing: a computation shared between N uses
costs one execution, with a marginal ~177 steps per additional forced use (0.8% of the
computation). The open half of this goal is cyclic sharing — see §11.2.

**G2 — Parallelism by construction.** Independent redexes are contracted simultaneously
across threads. Confluence makes the *answer* independent of the schedule, so a scheduler
can only ever be a performance choice, never a semantic one.

**G3 — A small, auditable, portable core.** The core is the interaction calculus and
nothing else: **3,458 lines** across `src/` — core and runtime counted together, under one gate. It has
no knowledge of arithmetic, hardware, effects, or filesystem formats. That is what makes
the layering claim of §2 checkable by reading it.

**G4 — AOT-first.** `lin build` runs the whole pipeline — including partial evaluation of
the program — and ships a `.line` container holding the *residual* net. The artifact keeps
exactly the work the runtime genuinely must do (effects, IO, non-pure FFI) and nothing
else. Interpretation stays as the development path and shares the same front end, so there
is one semantics and two schedules.

**G5 — Verification before claims.** Values are pinned to an *independent* oracle (ordinary
lambda evaluation, no nets, no sharing, no fans), not to the test suite's own expectations.
Accelerators must reproduce the base engine's rewrites, not merely produce the same answer.

### The rule that keeps the layering honest

A driver may **pre-empt** a rule on a redex class. It may never **replace** a rule. A
program whose redexes no driver claims must still reduce to exactly the same value, by
plain β. Every architectural decision below is an instance of that one rule.

---

## 2. Layering

| layer | owns | invariant it must uphold |
|---|---|---|
| surface + AOT passes | program rewrites, def precompilation, net compilation, and the e-graph optimizer (`src/runtime_egraph.inc`, std rather than core) | the term handed to the compiler is semantically finished; every rewrite is meaning-preserving, and every optimization is optional — the pass may be absent and programs still compile and run |
| **calculus core** (`src/net.c`) | agents, wires, scopes, and the four rules: β, δ⋈δ, γ⋈δ, ε — nothing else | **complete and correct alone**; with no driver loaded, every program still reduces exactly |
| drivers (`std/drivers/*.so`) | arithmetic folding, wave dispatch to SIMD/GPU/threads, waiting policy, Lévy bracketing if it ever lands | never load-bearing for correctness; must be bit-exact against the base engine |
| std runtime (`src/runtime_*.inc`, `std/`) | readback, IO/effect continuations, the `.line` container, the language library | same as drivers: convenience, not correctness |

The dependency direction is one-way. The core may call a driver through the ABI (§5); no
driver may require the core to know what it is for. The one thing the core tells drivers
about itself is *context*, via two flags — `lin_precompile_depth` ("these operands are free
variables and will never become concrete") and `lin_build_depth` ("this reduction is
happening at build time, so nothing the program would observe at run time may be baked").
Both are statements about *when*, not about *what*.

---

## 3. The calculus core

### 3.1 Nets

A net is a graph of agents with wires between ports. Exactly four agent kinds exist:

| agent | symbol | ports |
|---|---|---|
| `LAM` | γ | binder (1), body (2), principal (0) |
| `APP` | γ | function (0), argument (2), principal (1) |
| `DUP` | δ | principal (0), two auxiliaries (1, 2) |
| `ERA` | ε | principal (0) |

`ROOT` is node 0, the observation point. A net is stored flat — `tag[]`, `wire[]`
(3 ports per node), `scope[]`, `name[]`, `dead[]` — so drivers can read and rewrite the
graph directly, and the wavefront scheduler can reason about node indices.

`name[]` is load-bearing rather than decorative: a node's *name* is its carrier tag, and
the value domains Lin supports are recognized by carrier name through one registry
(§7.3). This is why "add a value domain" is a registration, not a new agent.

### 3.2 Gauges: scopes as levels

Every fan carries a **scope**: the *level* of the sharing point it belongs to, held as an id
into the net's **level trie**. A level is a position in the term — the sequence of branches
taken from the root — and interning that sequence as a trie node makes the four operations the
calculus needs exact and cheap:

| operation | meaning | cost |
|---|---|---|
| `scope_eq` | the same sharing point | one integer comparison |
| `scope_meet` | the level two sharing points genuinely share | lowest common ancestor |
| `scope_within` | one sharing point encloses the other | walk up from the deeper level |
| `scope_app` / `scope_rebase` | one step deeper / a clone's levels under a new site | one intern |

Representation is therefore free of the word-length problem: one id per node and one edge per
*distinct path*, whether a path is 3 steps or 300. The previous representation was a bit word
inline (57 bits) spilling into a per-net table beyond that, and it cost the artifact dearly: a
built container was 3,659,765 bytes of which **97.1%** was 444,380 spilled gauge entries, where
the trie form ships 136,953 bytes with 9,508 levels. Level ids are **net-local**, which matters
at a splice — a clone's levels must be re-interned under the site that cloned it
(`scope_rebase`), where a bit word could simply be copied.

A gauge must be a **path**, not a bare binder depth: siblings at equal depth would get equal
labels, their fans would annihilate, and independent values would merge. Depth labels are
measurably unsound (5 oracle mismatches); paths are not. Paths also mean equal scopes *are*
"the same sharing point" — two sharing points sit at different positions, so they never share a
path, and no per-fan counter or fixed-width argument is needed for soundness.

Two fans annihilate only when their scopes are equal; when they differ they commute, and the
nested case is handled as §3.3 describes. The naive paper modulation concatenates
(`s₁ = 1·s_node·s_dup`), so a copy's name grows with every crossing; γ⋈δ **extends the meet**
instead, which keeps copies converging toward the level the two histories genuinely share.

### 3.3 The four rules

All four live in `net_interact` (`src/net.c`). That function is the entire semantics of the
language.

**β — `LAM × APP`.** Kill both nodes, link the binder's wire to the argument and the body's
wire to the result. Two degenerate shapes are detected first, and both are β itself rather
than fold machinery:

- the degenerate binder (`\x.x`, where the compiler cross-links the binder and body ports) is
  handled as a direct link; without it `((\x x) V)` strands `V` on a dead node;
- when two of the four wires are ports of the *same* fan (the fan sits between the binder and
  the argument, or between the body and the result) the fan already relates them, so that pair
  is not linked — linking it would wire a fan's principal to its own auxiliary, a pair no rule
  fires on, and the net would reach a "normal form" whose value cannot be read back. Before substituting, β
offers the argument to every driver's `arg_fold` hook (§5.3) — a saturated closure sitting
in an argument position is never a principal×principal redex, so β is the only place a
driver can reach it.

**δ⋈δ — two fans meet.** Three cases, and the case distinction *is* the duplication discipline:

- *Equal scopes* → **annihilate**: the two fans are copies of one sharing point, so their
  auxiliaries are cross-linked (with the identity-pairing cases handled explicitly) and both
  fans disappear. This is what makes a copy as cheap as the original.
- *Nested scopes* (one gauge a proper prefix of the other: the two sharing points enclose one
  another) → **share, do not duplicate**: the two fans are still copied by each other, but the
  deeper fan's copies take the *shallower* level. Nested sharing points are related, so the
  inner one belongs to the outer copies rather than being re-duplicated once per copy. This is
  the bracket-free rule that bounds duplication, and it is what makes a cyclic knot finite:
  measured on a knot, `(fact 0)` runs 2,000,000+ steps without a normal form under the plain
  commutation and **33,200 steps / 1,122 nodes** with the right value under this rule, with
  the suite and the oracle still green.
- *Incomparable scopes* → **commute** (Lafont's δ⋈δ): two genuinely independent sharing points
  met, so each fan is copied by the other — `δ_a`'s auxiliaries each get a `δ_b`, `δ_b`'s each
  get a `δ_a`, cross-connected — and each copy keeps *its own* fan's scope. Without this rule
  the only options would be annihilating unrelated fans (wrong value) or stranding the pair
  (no reduction), so a shared body could never be reduced.

**γ⋈δ — a fan meets a LAM or APP.** The fan duplicates the agent: two copies are allocated
at `scope_app(meet, 1)` and `scope_app(meet, 2)` (one level deeper than the meet), two fresh
fans carrying the *dup's* scope
fan out the agent's auxiliary wires, and the copies' principals go to the fan's auxiliaries.
The meet modulation (§3.2) is what keeps repeated crossings finite. The degenerate-binder
case links the two fresh fan principals to each other instead.

**ε — erasure is passive.** Pairs involving `ERA` are dropped; there is no ERA×DUP or
ERA×LAM propagation. Erasure works by leaving ports dangling and letting reachability
reclaim the nodes. This is the reference behaviour, and it has a sharp architectural
consequence (§11.2): **nothing in the core can actively dismantle a cycle.**

### 3.4 Sharing as the compiler introduces it

The compiler (`src/compile.c`) turns a binder used N times into a `DUP` fan tree
(`dup_tree`) whose gauge is the **path of the binder that owns it** — the sequence of branch
choices from the term root, built with `scope_app`. LAM and APP nodes carry their own path as
their scope too, so a fan crossing one of them meets at a real common level.

- A spliced precompiled define body (`ct_splice`) is **re-gauged** as it is cloned: each level
  inside the clone is re-interned under the level of the site that cloned it (`scope_rebase`).
  The body's fans were labelled during its own precompile reduction, so cloning it verbatim
  would give every reference's copies identical labels — two independent sharing points would
  annihilate into each other, and clones at different sites would not be distinguishable.
  Because level ids are net-local this rebasing is required even at the root level, where the
  old bit words happened to be copyable verbatim.

A path identifies a sharing point *and* its level, which is what the acyclic case needs for
soundness (verified) and what cyclic sharing needs to close a fan on its own copies (§11.2).

### 3.5 What the core deliberately does not have

**No brackets, no abstractors.** Lin has fans with gauges and the meet — enough to be
Lévy-optimal for acyclic sharing — but not the bracket machinery that lets a *cyclic* body
be shared. The consequence is architectural, not incidental: recursion cannot be a shared
cyclic body today, so it is unrolled at compile time (§8, §11.2).

---

## 4. The reduction engine

### 4.1 The wave loop

`net_reduce` (`src/net.c`):

1. `wave_snapshot` drains the active list into an immutable array of principal pairs and
   empties it. Each pair is re-validated as it is reached (both nodes still live, their wires
   still mutually facing), so a pair whose nodes an earlier redex already consumed is simply
   skipped rather than contracted twice.
2. Every loaded driver is asked to `claim` pairs, in ascending priority order; each gets a
   slice of the pairs it claimed, and the unclaimed remainder goes to the base engine.
3. Each driver `reduce`s its slice; `lin_reduce_wave_parallel` reduces the remainder, in
   parallel or serially depending on the wave's size and the thread setting.
4. The wave is fully drained, so every driver gets its `drain` point: retry what was parked
   because an operand was not concrete yet, and re-enqueue what is still expected.
5. If nothing changed and the active list is empty, the net is a normal form (or the step
   limit was hit) and reduction stops.

### 4.2 Independence and the wavefront scheduler

Two redexes may run concurrently when their read/write footprints are disjoint. The test is
structural and cheap: a pair's two principal nodes *and* the far ends of their four
auxiliary ports must all lie in the same 64-node sector (`node >> 6`). Pairs that pass are
grouped by sector and executed under `omp parallel for` with dynamic scheduling; pairs that
fail go to a serial fallback within the same wave. All dispatch buffers are grow-only
statics, so a wave allocates nothing and dispatch is O(pairs). γ⋈δ pairs are also routed to
the serial fallback: allocating a copy interns a level, and interning writes the net's shared
trie, which a threaded wave must not do concurrently.

**Policy: serial by default.** Threads are used only when asked (`-t`, `LIN_THREADS`,
`OMP_NUM_THREADS`), and parallelism engages only for waves of at least 512 port entries (256
redexes). This is a measured decision, not caution: waves are usually small and cheap
relative to a fork/join, so threading them costs more than it saves.

**The ceiling.** On `test/numbers.lin` the wall clock splits as:

| phase | share |
|---|---|
| type check | 1% |
| `expand_defs` (def inlining + precompilation) | **30%** |
| `compile` (term → net) | **36%** |
| `net_reduce` | **22%** |
| load / IO / print / unaccounted | ~11% |

So reduction is about a fifth of a run, and the front end about two thirds. A perfectly
parallel, infinitely fast reducer would buy at most ~17% of wall clock; the front end is
where both goals actually pay. (See §11.3 for the parallel experiments this table retired.)

### 4.3 Reclamation

Reclamation is reachability compaction from ROOT, run when the active list empties and the
node count has doubled past a high-water mark (`net_gc`). There is no incremental collector
and no stop-the-world pause in the usual sense: dead nodes are a by-product of the rules,
and the compact step is O(live net).

Because the `.line` container stores *every* node and *every* level, the AOT path compacts
before serialising (`net_gc`). Compaction is load-bearing for artifact size rather than
cosmetic: a program that merely *referenced* a recursive define at depth 0 — never recursing —
compacted to 3 live nodes and still shipped a 423,502-byte artifact, 99.98% of it gauge data
belonging to erased nodes. Levels cost one id per node and one trie edge per distinct path, so
what survives compaction is what the residual actually uses.

### 4.4 Accounting and livelock guards

Reduction steps are counted on the net; a driver that re-enqueues parked work without
progress is bounded by a stall counter in the wave loop, and a driver whose fold budget is
exhausted must release its redex to β rather than hold it forever (§5.3). Both guards exist
because a *driver* is where waiting policies live, and a bad policy must degrade to slower-
but-correct, never to divergence.

---

## 5. Driver ABI

Drivers are shared objects (`std/drivers/*.so`) exposing one `LinDriver` struct. The core
loads them, sorts them by priority, and hands them redexes. This ABI is the whole extension
surface of the engine.

| field | meaning |
|---|---|
| `magic`, `abi` | identity; a mismatch is rejected **loudly** (an older `.so` is smaller than the current struct, so reading new fields would run past its end) |
| `name`, `description` | what `(get_driver)` reports |
| `caps` | `LIN_CAP_NATIVE_NUM` (scalar folds), `LIN_CAP_FIXED` (β/annihilate/erase), `LIN_CAP_COMMUTE` (allocating γ⋈δ), `LIN_CAP_PREEMPT` (pre-pass) |
| `priority` | ascending; the wave partitions in this order |
| `claim(n, p1, p2)` | **pure** predicate: will this driver handle this redex? |
| `reduce(n, redexes, nred, limit, changed)` | consume a claimed slice |
| `arg_fold(n, arg, target)` | pre-empt a sub-term in a β *argument* position |
| `materialize(n, p, out)` | readback pre-pass: turn a foldable closure the reducer left behind into a value |
| `drain(n)` | the wave emptied; retry parked work, return how many pairs were re-enqueued |
| `pending(n)` | still holds un-materialised work for this net |

### 5.1 Strategies vs pre-emptors

A **strategy** (SIMD, GPU) reduces a redex *class* more cheaply than the base rules.
A **pre-emptor** (`LIN_CAP_PREEMPT`) claims classes the core would otherwise handle
anyway — native folds, guarded deferral — as a pre-pass, and composes with whichever
strategy is selected. `(set_driver "cpu"|"simd"|"gpu")` clears strategies but **keeps**
pre-emptors, so selecting a strategy never silently disables the fold pre-pass.

### 5.2 The contract every driver must honour

1. **`claim` never strands.** A claimed redex is removed from the wave; so claim returns 1
   only when the driver will either rewrite it now or hold it deliberately and give it back.
2. **The base engine is the oracle.** A driver's rewrite must be bit-exact against
   `lin_reduce_wave_parallel` on the same redex (§10.2).
3. **The waiting policy belongs to the driver.** The core supplies a drain point and a
   livelock guard, nothing more. A driver that cannot materialise a redex must eventually
   release it to β, which is always correct.
4. **`pending` is honest.** A reduction that ends with a driver still holding work has not
   reached a value, and the core acts on that: `def_precompile` refuses to bake such a net.
5. **Respect the two context flags.** Do not fold while `lin_precompile_depth > 0` (the
   operands are free variables that never become concrete), and do not bake anything
   observable while `lin_build_depth > 0` (a program must still be able to observe its own
   run).
6. **File two lines, not a test file, to add a driver:** ship `std/drivers/<name>.lin` and
   add `<name>` to the `DRIVERS` registry in `test/driver_selftest.sh` (§10.2).

### 5.3 The two edges the wave cannot reach

A principal×principal redex is the wave's unit, but two shapes are not one:

- a saturated closure in an **argument** position (`succ (mul 2 2)`) — reached through
  `arg_fold`, offered by β just before substitution;
- a foldable closure left embedded in a value spine at **readback** — reached through
  `materialize`.

Both hooks exist so that drivers need not invent a way to see those shapes; a driver that
implements neither simply leaves them to the core.

### 5.4 The drivers that exist

| driver | caps | what it does |
|---|---|---|
| `arith.so` | `NATIVE_NUM \| PREEMPT`, priority 5 | the fold pre-pass: claims saturated `_op`/`_ffi` closures and folds them through the shared scalar table, parking (and draining) the ones whose operands are not concrete yet. Also *is* the scalar table (§6). |
| `simd.so` | `NATIVE_NUM`, priority 10 | claims saturated `_op` redexes (readiness-gated) and folds them in batches of `SIMD_WIDTH` — an eval pass over the batch, then an apply pass — so value computation decouples from mutation. Bit-exact. |
| `gpu.so` | `FIXED`, priority 20 | dispatches the fixed-allocation rules (β, DUP×DUP with inline scopes, erase) to a Vulkan compute kernel over host-visible buffers; allocating commutes and heap-backed gauges are delegated to the base engine. Two-phase per wave: collect the sector-disjoint slice *without mutating the net*, dispatch, commit, then host-fall-back. Loader/device failure degrades to the base engine with one warning. |

An important consequence of the layering shows up here: since integer arithmetic became
pure Lin (§6), a driver's fold is only ever an *acceleration*. `simd.so` measured exactly the
same native-fold count as the base engine on the same programs — because the base fold is
already O(1) per saturated `_op` closure via the shared table. Its value is the batched
structure, not the count.

---

## 6. Scalar semantics: one table, any strategy

There is exactly **one** place that knows what `lin_add`, `lin_eq`, `lin_fadd`, … mean:
`lin_arith_scalar()` in `std/drivers/arith.so`. A reduction *strategy* decides *how* to
reduce a net; it resolves arithmetic by calling that one table.

- **`arith.so` is a semantic provider, not a strategy.** Its table answers "what is the
  value of this operation"; its `claim` is the pre-pass, not a reduction policy. New ops
  are new table rows, not a new switch arm in every driver.
- **The core hook is general-purpose.** `lin_scalar_ops_add()` / `lin_scalar_ops_load()`
  let any driver register any number of `ScalarOpFn` providers, tried in registration
  order; arithmetic is merely the first consumer. `run_ffi` delegates unclaimed `lin_*` ops
  to them.
- **Non-movable C stays in the core:** memory/device/OS (`exit`, `driver_*`, `dlopen`,
  `puts`, `getenv`), float parsing, string comparison, and fold accounting. These are not
  semantics that a strategy could vary; they are the host boundary.
- **Arithmetic is pure Lin first.** `std/num.lin`'s integer and comparison ops are pure
  Scott recursions wrapped as driver-foldable `_op` closures: `(add 4 3)` compiles to
  `((\_add <pure-body>) (cons 4 (cons 3 nil)))`, a `DT_OP`-named `LAM` applied to an operand
  spine. The embedded pure-Scott body is the **always-correct β fallback** — with no scalar
  provider at all, the same redex still reduces by the interaction calculus, slowly and
  exactly. The fold is an acceleration of a term that already means the right thing.

That last point is the cleanest illustration of G4: the arithmetic table can be deleted and
Lin still computes the right answers.

---

## 7. Language surface and types

### 7.1 Forms

S-expression syntax over curried lambda calculus. Reader forms: `(\x …)` / `(lambda …)`,
`(define …)`, `(define! …)` (typed, checked at definition), `(let ((x v) …) body)`,
`(namespace X)` / `(open X)` / `(export X)`, `(load "file.lin")`, `(datatype …)`,
`(match scrut (pat body) …)`, integer literals of arbitrary magnitude, floats, strings.
Macros are ordinary definitions — there is no separate macro layer.

`(export X)` re-exports a namespace's public members into the current scope in one form
(`_`-prefixed members are private, last-loader-wins on collisions). It replaced ~230 lines
of hand-written alias boilerplate in the standard library.

### 7.2 Hindley–Milner with nominal types

`src/type.c` is a textbook HM checker: unification with occurs check, let-generalization,
`Scheme` with up to 256 quantified variables, and nominal type constructors (`num`, `bool`,
`float`, `list`, plus user-declared ones) alongside arrows and type parameters.

One property is architectural rather than incidental: **a definition's type must not depend
on which unrelated definitions were registered before it.** Generalization therefore counts
only *unquantified* environment variables as free — a scheme's own quantified variables are
bound by the scheme. This matters for two reasons: it is the correct HM rule, and it is the
prerequisite for checking and compiling definitions concurrently (§11.3), where "which def
came first" is a schedule rather than a fact.

### 7.3 Data types

- **Built-ins** are Scott-encoded: numerals (the successor case receives the predecessor
  numeral, so `pred` is one application — O(1)), booleans, Church-list strings, floats (a
  boxed double), and Church numerals for pure iteration.
- **User ADTs** — `(datatype Name (Ctor field…) …)` introduces each constructor as a
  Scott-encoded function `C_i = \f1..\fk \d0..\d_{m-1} (d_i f1 … fk)`, and `(match scrut
  (pat body) …)` compiles to positional Scott dispatch. They type-check through ordinary
  let-generalization: no new type-system machinery and no new net agents.
- **The datatype registry** keys every value domain by its *carrier node names*
  (`_sz`/`_ss`, `_bt`/`_bf`, `_cl`/`_nl`, `_ffi`, `_fsz`, the `_op` LAMs, the effect
  continuations). Readback decoders and drivers consult `ctor_tag(name)` instead of
  pattern-matching identifiers, which is what makes a new value domain a registration
  rather than a change spread across the readback path.

---

## 8. The AOT pipeline

`lin build prog.lin -o prog` runs the whole pipeline once and writes a `.line` container;
`./prog` then reduces only what the compiler could not finish. `lin prog.lin` (interpret)
shares the identical front end.

| pass | what it decides | where |
|---|---|---|
| load + type check | the program is well typed before anything is rewritten | `load_file`, `type_check` |
| `expand_defs` | defs inlined; non-recursive defs **precompiled** (baked to a reduced net) where that is sound | `expand`, `def_precompile` |
| e-graph saturate + extract | β/η rewrites by equality saturation, then cheapest form; classes with several parents are bound with a `let` (a DUP fan) instead of being copied per parent | `egraph_optimize`, `src/runtime_egraph.inc` |
| compile | term → interaction net; each multi-use variable becomes a `DUP` fan tree | `compile`, `ct`, `dup_tree` |
| **AOT evaluation** | reduce the net at build time, stopping at effects | `do_build`, `net_reduce` |
| compact | drop reduction intermediates before serialising | `net_gc` |

The last three steps are what make this AOT rather than merely optimising. Partial
evaluation folds and β-reduces everything that does not need the runtime, and is *stuck*
exactly at an IO effect or a non-pure FFI closure — so the artifact contains precisely the
work that genuinely needs a runtime, with the effect continuation intact. Measured today on
the container tests (`LIN_PASSES=1`): `line_binary` compiles 8,238 nodes and finishes 3,842
of them at build time, shipping 3,832 live nodes in a ~105 KB container; `line_ffi` compiles
63,890 nodes, runs 114,909 build-time steps, and compacts 346,627 nodes to 3,397. Without
the compaction the artifact came out *twice* the size of the un-evaluated one despite being a
value, because the container stores every node the reduction ever allocated.

Two invariants constrain the passes:

- **Precompilation must not bake a lie.** A define is baked only if its open-body
  precompile finished (not truncated by the step limit) and no driver reports `pending` on
  the result. Otherwise the define stays textual and is expanded per reference. The signal
  is generic — "this net is not a value" — so no driver's policy leaks into the core.
- **Build-time answers must not become runtime facts.** `lin_build_depth` marks the AOT
  reduction so a driver will not fold a probe like `(lin_folds)` into the artifact.

**E-graph status, honestly.** The pass runs only on the AOT path, saturates β and η for four
rounds under a node cap, and extracts lowest-cost forms. It is a scaffold, not yet a
decision layer: `eg_extract` rebuilds a *tree*, so a class with two parents is emitted
twice — the sharing it discovers is thrown away; dedup is a linear scan, so insertion is
quadratic in the cap; and on the only two programs that exercise it the shipped artifact was
byte-identical with and without it (the compiled node count `LIN_PASSES=1` reports is where
its one measurable effect — 4.6% fewer nodes on `line_ffi` — shows up, without reaching the
artifact). What it is *supposed* to own — CSE, precompile-vs-textual choice, unrolling
strategy — is the subject of §11.3.

---

## 9. Runtime: effects, readback, containers

These live in `src/runtime_*.inc`, `#include`d into core translation units for a single
binary, but they are std code: the readback/IO runtime, the shared on-net decoder, and the
`.line` container. They share the core's statics (`N`, the wire accessors) rather than
duplicating them.

### 9.1 Effects as a protocol, not a switch

An effect is a continuation named by a registered carrier (`_iod` done, `_iop` print,
`_ior` read, `_iow` wait). The monadic step is one primitive — `eff_apply`: apply the
continuation to the produced value, relink ROOT, re-reduce. New effects are added by
registering a carrier plus, where the host is involved, one arm in the runner; the
continuation protocol itself never changes. `_ffi` is the general escape hatch: resolve a
symbol and call it.

This is also where the language's "wait for anything" facility lives (`io_wait`): a
selector string chooses stdin, a file descriptor, a subprocess (`!cmd`), a file, a timer,
or an FFI call — all funneling into the same continuation step.

### 9.2 Readback

Decoding is registry-driven (`ctor_tag`), so an identifier that happens to start with `c`
or `n` can never be mis-decoded as a string spine.

Printing renders into a buffer and **memoises the rendered text per (node, port)**, replaying
it on later visits. Without the memo, a DAG-shaped result is re-walked at every sharing point
and printed output becomes exponential in the number of sharing points while the net stays
linear. A render is memoised only if it emitted no `?` on the way in: a `?` means the text was
shaped by an in-progress ancestor (a real cycle), so it is not context-free and must not be
replayed. Output is byte-identical either way.

### 9.3 The `.line` container

A `.line` file is a shebang line (re-invoking the engine that produced it) followed by a
`LINE` magic, a versioned header `{version, nn, nlevels, nnamed}`, the node arrays (`tag`,
`dead`, `wire`, `scope` — the scope being a level id), the named nodes, and the level trie as
`(parent, branch)` edges in id order. Loading rebuilds the trie and its interning table (a
loaded net still reduces, so it must be able to intern new levels), and reconstructs the
active-redex queue from live principal pairs — the queue is not serialised, so without that a
loaded container would sit inert.

---

## 10. Verification

The architecture is only as good as the mechanism that catches it when it lies, so
verification is part of the design rather than a separate activity.

### 10.1 The independent oracle

`test/soundness_enum.py` evaluates the boolean formulas of the SAT/Tseitin suites by
ordinary lambda evaluation — no nets, no fans, no sharing, no engine — and requires the
engine's readback to agree, 35 evaluations. It exists because the suite once *asserted* the
wrong values that unsound fan sharing produced, and even labelled one of them a "false
negative". Editing an expectation can no longer make an unsound engine pass, and the oracle
fails loudly if its vocabulary stops covering an expression instead of silently skipping it.

### 10.2 The canonical driver contract

- **Corpus `std/selftest.lin`** activates no driver and carries no expected values; it just
  prints the readback of a fixed set of pure probes covering every redex/capability class a
  driver may claim.
- **Runner `test/driver_selftest.sh`** reduces the corpus under the base CPU engine (golden)
  and then under each driver in its `DRIVERS` registry, requiring value-for-value equality.
  Adding a driver is two lines of work, and no expected values to maintain.
- **Device reducers get a stronger oracle.** `std/drivers/selftest.h` lets a device driver
  replay *the same redexes* it just committed through the canonical host reducer and diff
  `wire[]`/`dead[]` bit-exactly (env-gated, `LIN_GPU_SELFTEST=1`). The two layers compose:
  the corpus proves cross-driver value equality, the replay proves per-wave device
  bit-exactness where a device actually ran.

### 10.3 The suite

`test/run_tests.sh` runs **53 suites / 978 assertions** in ~39 s across six tiers: core
primitives, FFI/system drivers, cross-driver selftest, the soundness oracle, constraint
satisfaction and rewriting, non-trivial workloads and confluence invariants, `.line`
containers, and CLI invariants. The Nix runner mirrors it for CI against committed content;
`make test` runs the working tree.

Useful observability knobs: `LIN_PASSES=1` (per-pass AOT stats), `LIN_TRACE=1` (per-step
rule trace), `LIN_STEPS` (step limit), `LIN_THREADS`/`-t`, `LIN_GPU_SELFTEST`.

---

## 11. Status and open problems

### 11.1 Landed

- The core is a complete four-rule calculus with no fold machinery in it: `net_interact`
  contains β plus the two commutation rules and passive erasure, and nothing else. The
  `_ffi`/`_op` fold, its saturation guard, its waiting policy and its decline signalling all
  live in `arith.so` as a pre-emptor.
- Arithmetic is pure Lin with a single shared scalar table behind it.
- Sharing is verified Lévy-optimal **for acyclic values**, with measured marginal cost.
- Fan–fan commutation and the gauge/meet discipline are in, and every sharing witness in the
  SAT/Tseitin suites agrees with the oracle.
- `lin build` runs the pipeline end to end and bakes a compacted residual.
- Definition types are order-independent.
- Gate: 55 suites / 991 assertions, oracle green, 3,458 lines across `src/`.

### 11.2 Open: cyclic sharing — the Lévy gap and the largest compiler cost

Recursion is the one place where Lin is not what it claims. A recursive define is compiled by
**bounded self-unravelling**: `build_bound_rec` emits `f (f (… (f base) …))` with k copies of
the body, tagged with a `_rec` sentinel; if the sentinel survives reduction the whole program
is recompiled with k doubled (up to 16 rounds). Multiplexed across nested recursive defines
this multiplies — k^depth — so k is the multiplier on the whole front end and it is now small
(k = 6, was 24): at k = 24 `(fact 1)` — one multiplication — compiled a 981,286-node net and
the suite ran in 48.7 s; at k = 6 the same suite runs in 23.6 s with the oracle green and
`(fact 1)` compiles 18,449 nodes. Depth is not guessed pessimistically; widening pays for it
only where it is needed. The runtime is still dominated by the unravelling rather than by the
depth needed (a depth-12 case costs ~50 s either way), which is why the knot below matters.

The fix is architectural and known: compile the body **once**, wire the define's own name to
a path back into that body, and share the body across reference sites through a fan — the
"knot". It is not landed because it does not reduce, and the mechanism is now measured rather
than assumed. A knot net is *not* divergent by construction: with the self-reference wired to
an `ERA` (the call never made) the same net becomes inert in **62 steps / 196 nodes**. What
diverges is duplication:

- With the knot live, a profile at a 200k-step cap shows the work is **γ⋈δ crossings**, not
  β: `peel 3` reaches 46,180 live `LAM` and 46,170 live `DUP` around just **18 `APP`**, with
  γ⋈δ = 117,950 against β = 35,899; `fact 0` shows γ⋈δ = 145,002 against **β = 24**. Fan
  crossings create two fans each, and δ⋈δ annihilations pair them off more slowly than they
  are created, so the fan population grows with the step count.
- It is not gauge naming. The same divergence appears under every arithmetic tried: the
  current meet-extension, the paper's `1·s_node·s_dup`, unique markers, identity+path levels,
  level-only paths, copies-at-the-fan's-level, twins-at-the-agent's-level, and the δ⋈δ
  variants (mutual copy, meet-collapse, level-lowering). The two that *do* cut the cycle
  (collapse the copies onto the meet) are measurably unsound: `test/let.lin`'s sharing probes
  return `2` for both components of `(pair (f 1) (f 2))`, i.e. two independent sharing points
  merged. A true δ⋈δ commutation needs four fans for the wiring to close, so fan duplication
  is structural, and the only escapes are to *block* the crossing or to drop the pair.
- It is not specific to recursion. The acyclic witness `(let ((g (mul 2))) (add (fst (pair
  (g 3) (g 4))) 0))` — sharing a partially-applied closure, no recursion anywhere — fails to
  terminate in reduction in every variant above (measured with printing disabled, so readback
  is excluded), and the reference implementation (`wave-opt-reduction/main.hs`, whose rule set
  has no unequal-fan rule at all) behaves the same way. That case is dominated by β instead
  (1.68M β at a 738k-step cap), i.e. by the eager unrolling of the shared closure's body — so
  it is the *unrolling* that makes ordinary closure sharing expensive, and the knot is what
  would fix it, which is blocked by the duplication result above.

So the prerequisite is **duplication control**, and the four rules do express it — as
arithmetic on the gauge words, with no bracket and no new agent. Since gauges are paths, two
fans' levels can be *nested* (one a prefix of the other) rather than merely equal or unrelated,
and the δ⋈δ case analysis now uses that: nested sharing points **share** the inner one between
the outer copies instead of re-duplicating it per copy (§3.3). With that rule the knot reaches
a normal form — `(fact 0)` 33,200 steps / 1,122 nodes with the right value, `(peel 1)` and
`(peel 2)` returning `0` — where the plain commutation ran 2,000,000+ steps without stopping.

Cyclic sharing is therefore no longer divergent, but it is not yet correct: `(peel 3)` and
`(peel 4)` reach a normal form (72 steps / 195 nodes) whose value does not read back (the
printer emits `?`), so the sharing over-merges at deeper re-entries. Until that is fixed the
knot is not landed and the unravelling below stays.

**Sharing at the net level is blocked by the fold driver, measured.** The e-graph's sharing was
expressed as a `let`, which is lexical and so has to be placed inside the binders its value depends
on; two attempts at that placement failed (11.3). A fan has no such problem -- it is a graph node
whose auxiliaries are consumers wherever they sit -- so sharing was tried in the compiler instead:
every compiled subterm of 8 nodes or more is wrapped in a fan whose auxiliaries are its uses, keyed
structurally with the *binder identity* of each variable, so only genuinely equal computations merge
and no scope question arises. It is sound and catastrophic on the AOT metric: `line_ffi` went from
119,854 B / 3,397 residual nodes to **8.9 MB / 427,348 nodes**, i.e. the build-time reduction stops
finishing and nearly all the work lands in the artifact. Reverted. The likely cause is the one already
in 4.4 -- a fold driver that parks a redex whose operands sit behind a fan and never releases it --
so **driver deferral comes before sharing**, not after.


**The unravelling bound is a hazard, not a tuning knob.** The AOT candidate search (§8) measured
k = 4 as the byte winner on every program it tried (`selfrecursion.lin` 21,608 B against 55,899 B at
k = 6), and it was wrong to take: at k = 4 `test/selfrecursion.lin` returns `0` for `(fact 3)` where
the answer is 6.  The unravelling ran out, the `_rec` sentinel was not detected, no widening fired,
and a wrong value was returned silently -- while the same bound at depth 8 widens correctly
(`(fact 8)` = 40320 at k = 4), so the hazard is shape-specific rather than a simple cliff.  Two
consequences: the bound stays at 6, and a build-time search may only range over axes where *every*
candidate is correct — the search infrastructure now reports the artifact's cost, and correctness is
checked by the suite and the oracle rather than by the search.  Until a cycle can be shared (§11.2)
the real fix is to delete the bound, not to tune it.

Active erasure (propagating ε through agents) was implemented as the alternative and measured
as paying nothing; it was reverted. It also carries a soundness caveat when a fan straddles
an erase boundary.

### 11.3 Open: make the front end the place decisions live

Both headline goals now pay *here*, not in the reducer (§4.2):

- **Share recurrence at the net level** rather than copying unrolled levels (§11.2) — attacks
  the measured 30%.
- **Give the e-graph real decisions to make — partially done, and now measured on the
  artifact.** The pass was rewritten this round: e-node lookup is hashed (it was a linear scan,
  i.e. quadratic in the node cap), the rules and extraction are reported under `LIN_PASSES`, an
  `LIN_NO_EGRAPH=1` / `LIN_EGSHARE=0` A/B pair exists, and extraction is sharing-aware — a class
  with several parents is bound with a `let`, which the compiler compiles into the same DUP fan a
  multi-use binder gets, instead of being emitted once per parent. Measured on the shipped
  metric: with the pass, `line_ffi` compiles 8,166 → 7,802 nodes and ships **122,149 → 119,854 B**
  (the earlier claim that the pass was artifact-neutral was measured before the artifact cost was
  reported at all); `line_binary` is unchanged at 136,937 B.
  Rules are now **data**: one table row per optimization, each switchable (`LIN_EGRULES=beta,eta`)
  and each reporting how often it fired, with the search budget as data too (`LIN_EGROUNDS`,
  `LIN_EGCAP`) and the cost model selectable (`LIN_EGCOST=tree|dag`).  That immediately produced
  attribution the pass never had: `line_ffi`'s 8,166 → 7,802 nodes and 122,149 → 119,854 bytes come
  from **beta** alone (13 unionations); disabling it (`LIN_EGRULES=eta`) reproduces the unoptimized
  8,166/122,149 exactly, and eta itself fires **zero** times on both container programs — it is
  carried but not yet earning its place.  The sharing-aware cost model (charging a shared child
  once, so the pass prefers forms whose repeated parts are already shared) is implemented but
  **hangs** in the current saturation, so it is an opt-in switch rather than the default; measured,
  not assumed.
  The *sharing* half of that is not yet realized: a binding is wrapped around the whole term, and
  hoisting a subterm out of the λ binders its free variables come from is unsound.  Extraction
  therefore verifies its own output (no free generated name) and `egraph_optimize` compile-checks
  the result, falling back to the plain tree extraction when the check fails — which is what
  happens on `line_ffi` today (`shared extraction rejected (unbound variable 'a')`). The next step
  is **scope-aware placement**: bind each shared class in the *frame* (a λ body, or the root) that
  encloses all of its uses, which is what makes sharing pay on real programs rather than only on
  closed subterms.  An attempt at it is recorded here because its failure mode is instructive:

  - Design: one traversal for both planning and emission (so a plan cannot disagree with what is
    emitted), a frame per λ body, a binding hosted by the frame of its *first* use, and a class
    used outside its host frame simply not shared.  A frame emits `let v1 = .. in let v2 = .. in
    body`, values ordered so a value referencing another binding is evaluated inside it; a
    within-frame binding cycle vetoes that one class and the pass retries, so one awkward value
    does not cost every other binding in the program.
  - Two bugs cost the attempt.  The frame's binding list was filled only by the planning pass, so
    emission wrapped nothing and every generated name came out free (the compile probe caught it,
    which is why the result was safe rather than wrong, but useless).  And a value emitted at a
    frame close can register *more* bindings in that same frame, so the list has to be drained to a
    fixpoint -- iterating it as it grows does not terminate.
  - With both fixed the emitted term still had out-of-scope names and then stopped terminating, so
    the work was reverted rather than landed half-debugged.  What made it expensive is that the two
    passes can silently disagree: the next attempt should assert that planning and emission visit
    the same class, binding and frame sequence, and should be tested on a shared value that
    mentions a λ-bound variable -- the shape flat root hoisting cannot express.
- **Parallelise definitions, not waves.** Defs are independent units of type checking and
  compilation, they are 66% of wall clock, and order-independent generalization is now in
  place — that is where the cores are. Parallel *reduction* measurements (a precise
  independence test doubled the parallel fraction from 28% to 53% and still left wall clock
  2% worse; per-pair work is ~140 ns and the allocating rules contend on one atomic node
  counter) are bounded by the ~17% ceiling §4.2 records, while threading defs is not.

### 11.4 Open: smaller items

- **Float typing is nominal but not enforced.** `float` is a registered nominal annotation
  and a float is a Scott numeral carrying an IEEE-754 bit pattern under the `_fsz`/`_fss`
  spine (so it never collides with integer numerals), but `std/float.lin`'s operations are
  declared `num`-typed and route through `_ffi` closures to libm. A distinct, checked float
  type is a type-system task, not a net-level one.
- **A shared float inside a spine does not read back.** `(let ((x (fmul (float "6") (float "7")))) (fadd x (float "1")))` folds to `43`, but the same shared float nested in a pair spine (`(pair x …)`) renders as the closure structure instead of a numeral: the readback decoders peel a fan at the top of a value, not one buried in a spine. Measured identical at `ddd1cd7`, i.e. pre-existing rather than a regression from the level representation, and `test/float_share.lin` leaves the shape unasserted until it is fixed.
- **Driver net-side decoding** is not fully consolidated: drivers reuse the shared
  `net_spine_args`/`net_ffi_args`/`net_dhop` walkers, but `simd.c` still parallels parts of
  the `_ffi` argument walk. A fuller consolidation would reclaim headroom against the LOC
  gate.
- **The interpreter-side surface is the whole remaining gap to 3,000.** The REPL and `-e`
  (`test/` never uses them), the GoI determinant benchmark (`src/goi.c` plus the `-b` report
  that prints it) and `do_goi` are ~200 lines of capability `lin build` makes optional, since
  the artifact is the deliverable. They are *not* dead weight — the suite's `-b`-independent
  paths and `test/` run through the same `eval_form` — so deleting them is a product decision
  about whether a source-level interpreter stays in the shipped binary, not a cleanup. Held
  pending that decision rather than removed to flatter the line count.

### 11.5 Standing policy

Land only what measurably pays. Three reverted attempts are the reference points, and each
was reverted *on numbers*: a term-level CSE (artifact 30× worse), a precise independence
scheduler (wall clock 2% worse for ~40 lines), and active erasure (paid nothing). A change
that adds lines without moving a measurement does not ship; the measurement is the
deliverable.

---

## 12. Building and layout

```
make all       # core (./lin) + driver plugins (std/drivers/*.so)
make lin       # core only
make test      # build everything, run the full suite against the working tree
nix build      # hermetic build: core + plugins + the Vulkan compute shader
               #   (reduce.spv is compiled from reduce.comp by glslangValidator)
nix flake check
```

`nix build` sees only **committed** content (flakes stage `src = ./`), so use `make test` for
day-to-day work and treat Nix as the CI/reproducibility path.

| path | contents |
|---|---|
| `src/net.c` | nets, scopes/gauges, the four rules, wave scheduler, GC, driver pipeline |
| `src/compile.c` | term → net, fan trees, define splicing; `.line` container (`runtime_line.inc`) and e-graph optimizer (`runtime_egraph.inc`) are std, included here |
| `src/io.c` | readback decoders, datatype registry, FFI runner, scalar-op hook (via `runtime_io.inc`, `runtime_decoder.inc`) |
| `src/main.c` | pipeline, defines/namespaces, recursion unrolling, CLI/REPL |
| `src/parse.c`, `src/type.c`, `src/goi.c` | reader, HM type checker, GoI determinant benchmark invariant |
| `std/*.lin` | the library, in Lin |
| `std/drivers/` | `arith.so` (scalar table + fold pre-pass), `simd.so`, `gpu.so` (+ `reduce.comp`), `selftest.h` |
| `test/` | suite, driver selftest, soundness oracle |
| `examples/`, `benchmarks/` | curated self-verifying programs, benchmark harness |

**Line budget.** `src/` is **3,458 lines** — every file counted, no `*.inc` anywhere — against a
3,500-line gate, so the gate is now met. Of those lines 3,012 are code, 192 are comment-only and 254
are blank: the comments are rule semantics and hazard records (why a guard exists, what a measured
alternative cost), which is what makes the core auditable rather than merely small. Earlier revisions
excluded `runtime_*.inc` files from the count; that was an accounting trick and it is gone — everything
that ships is counted. What the gate protects is the calculus — four rules and nothing else — and the
honest way to protect it is to count everything that ships.

The stretch target is **under 3,000**. A census of the tree says the remaining ~450 lines are live
capability, not slack: there are no dead functions (every `static` has a caller) and the last
duplicate mechanism — a second Scott-number allocator — was deleted at 3,458. What is left on the
interpreter side (REPL and `-e`, the GoI determinant benchmark, the `-b` report) is exactly the
capability `lin build` makes optional, since the artifact is the deliverable; deleting it is a
product decision recorded under §11.4, not a cleanup.
