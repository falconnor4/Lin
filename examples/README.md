# Examples

Each `.lin` file here is a complete program. Run one with:

```bash
./lin examples/pure-functional/scott_lists.lin
```

Programs that carry `; expect` comments are checked automatically:

```bash
bash examples/run_verifier.sh ./lin
```

The verifier runs every non-interactive example and compares its output with its
expectations. Interactive programs, which read from the terminal or open a
window, are listed but not run.

## Language

### `pure-functional/`

| File | Shows |
|------|-------|
| `scott_lists.lin` | Lists, indexing, equality, and folds written from scratch |
| `immutable_adt.lin` | A user `datatype` with `match`; trees updated without mutation |
| `functional_collections.lin` | Queues, streams, sets and maps from the standard library |

### `numeric-float/`

| File | Shows |
|------|-------|
| `float_math.lin` | Float arithmetic, interpolation, clamping, angle conversion |
| `recurse_arith.lin` | Recursive integer functions |
| `tiny_kernel.lin` | Small numeric kernels: a sum of squares, a geometric series |

### `optimization/`

| File | Shows |
|------|-------|
| `redundant_compute.lin` | A subterm written twice is computed once |
| `sharing_folds.lin` | How to observe that a driver folded a computation |
| `church_numerals.lin` | Church-encoded arithmetic, with sharing across iterations |
| `aot_vs_interpret.lin` | The same source run directly and as a built `.line` artifact |

### `logic-sat/`

| File | Shows |
|------|-------|
| `sat_solve.lin` | Finding and checking a satisfying assignment |
| `curry_howard.lin` | Proofs as programs: propositions that normalise to `true` |
| `tseitin.lin` | A Tseitin formula with its truth table and certificate |

## Systems

### `systems-ffi/`

| File | Shows |
|------|-------|
| `ffi_basics.lin` | Calling C: `puts`, `getenv`, `ccall`, `load_lib`, `system` |
| `driver_folds.lin` | Switching reduction drivers; results are identical across them |
| `interactive_repl.lin` | A read-eval-print loop built from I/O continuations (interactive) |

### `interactive/`

| File | Shows |
|------|-------|
| `driver_tour.lin` | Switching between the CPU, SIMD and GPU drivers at run time |
| `repl_calc.lin` | A calculator loop with no mutable state |
| `game_demo.lin` | A small turn-based game |

### `games/`

| File | Shows |
|------|-------|
| `tictactoe.lin` | A complete game with board printing and a computer opponent |

## Larger projects

| Directory | Contents |
|-----------|----------|
| [`bootstrap/`](bootstrap/README.md) | The Lin core written in Lin: parser, net compiler, reducer and readback |
| [`linden/`](linden/README.md) | A 3D wireframe renderer built as a driver loaded by path |
| [`faster_than_c/`](faster_than_c/README.md) | Early comparison programs, kept for reference; see [`bench/`](../bench/README.md) for the maintained benchmarks |
