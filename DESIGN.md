# Lin Architecture Notes

## Goal

Lin aims to be a versatile, expressive functional language where every program
is inherently optimal (Lévy-optimal interaction-combinator reduction) and
parallel (wavefront fan-out), implemented compactly.

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
   small-integer arithmetic *during* reduction.  Its argument walk is a
   *restricted* evaluator (pure `lin_*` ops only) — deliberately separate from
   `run_ffi`, which also performs side-effecting calls and must not fire
   during reduction.

## Line budget

Core engine `src/*.c` is ~2140 lines (≤ 2222 target).  Accelerator drivers are
**loadable plugins** compiled separately to `std/drivers/*.so` (not part of the
core build): the core links with `-rdynamic`, and `set_driver`/`add_driver`
resolve a driver name through an open protocol — `dlsym` by exact name, by
`lin_<name>_driver`, or by `dlopen("<LIN_STD_DIR>/drivers/<name>.so")`.

The Vulkan GPU driver was removed outright: it was ~325 lines, non-portable
(hand-rolled Vulkan ABI wrapping a hard-coded SPIR-V blob), and triggered
undefined behaviour at `-O2` (segfault).  The SIMD driver survives as
`std/drivers/simd.so`, the reference plugin.

## Build

```
make all        # core (./lin) + driver plugins (std/drivers/*.so)
make lin        # core only
make test       # build all + run the full suite
```

## Test status

39 suites pass; 4 fail, all pre-existing environment limitations:
- `driver_gpu` / `stress_wavefront`: expect a Vulkan GPU (now a removed core
  driver; loadable plugins replace it).
- `.line` binary direct-exec: expects `#!/usr/bin/env lin` shebang to resolve
  `lin` on `PATH` (only the in-suite `LIN_BIN` invocation is exercised).
