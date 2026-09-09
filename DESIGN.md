# Lin Architecture Notes

## Goal

Lin aims to be a versatile, expressive functional language where every program
is inherently optimal (Lévy-optimal interaction-combinator reduction) and
parallel (wavefront fan-out), implemented compactly.

## Core philosophy: pure interaction nets + pluggable optimizations

The **base engine** (`src/`) is pure interaction-net reduction: the four
scope-gauge rules (beta, annihilate, commute, erase) plus readback/effects,
with no hardware-specific or opportunistic fast paths baked in.  That purity is
what keeps the core small (~2140 lines, ≤ 2222 target), auditable, and correct.

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

- `std/drivers/simd.so`: native small-integer fold of `lin_*` FFI closures
  (enabled by `std/drivers/native.lin`).  Its argument walk is a *restricted*
  evaluator (pure arithmetic only), deliberately separate from `run_ffi`
  (which fires side effects and must never run during reduction).
- `std/drivers/gpu.so`: Vulkan compute driver.  Probes for a compute-capable
  device (via `dlopen`'d `libvulkan`), builds a compute pipeline from
  `reduce.spv` (compiled from `reduce.comp` by `glslang`), and dispatches
  fixed-allocation redexes with mapped HOST_VISIBLE|HOST_COHERENT buffers.
  Robust: on any probe/init failure it becomes a no-op and the CPU engine
  takes over.  The commute (allocating) rule and heap scope-gauges stay host
  side.

## Line budget

Core engine `src/*.c` is ~2140 lines (≤ 2222 target); drivers are out-of-core
plugins, so growth there does not count against the core budget.

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