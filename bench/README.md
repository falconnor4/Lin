# Lin against C

`bench/run.sh` (or `nix run .#bench`) runs each program here twice: as Lin, with the std and
all of its drivers, and as the C a programmer would write for the same algorithm, built with
`cc -O3 -march=native -ffp-contract=off`. Times are wall clock, best of three, and include Lin's whole process
(startup, prelude, and loading the function compiler's cached build). Outputs must match.

The rules, so the numbers mean something:

- **Same algorithm, natural code.** No memoisation or algorithmic help on the Lin side, no
  hand-written parallelism on the C side. If Lin is faster, it is because of what Lin does
  automatically.
- **Lin's speed comes from its drivers, never from changing the program.** `std/drivers/fn.c`
  compiles a recursive integer function to C *from its own net* and folds the call. Tree
  recursion and independent calls run on every core, and a loop folding an associative operation
  (wrapping `add`/`mul`, the bitwise ops, `max`/`min`) is split across threads. All of it is
  checked against the net's own reduction (`test/fn_compile.sh`).
- **`Lin -t 1` is reported too**, so the single-threaded comparison is visible.
- **Floating point is strict IEEE on both sides.** Lin's float semantics are fixed (no fused multiply-add),
  so the C is built with `-ffp-contract=off`; with contraction, `-march=native` C computes a *different*
  mandelbrot count, and two programs that disagree cannot be timed against each other.

| benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | what it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| collatz | 211 ms | 57 ms | 168 ms | 3.70x | a loop calling a helper loop; a max-reduction |
| fib | 148 ms | 58 ms | 162 ms | 2.55x | tree recursion |
| loop | 99 ms | 33 ms | 98 ms | 3.00x | a tail-recursive sum-reduction |
| mandel | 106 ms | 37 ms | 124 ms | 2.86x | floating point; three nested loops, the outer one a reduction |
| nqueens | 187 ms | 170 ms | 212 ms | 1.10x | bitmask backtracking, unbalanced tree |
| tak | 74 ms | 36 ms | 75 ms | 2.06x | calls whose arguments are calls |

Measured on a 4-core x86-64 container (gcc 15, nixpkgs). Re-run before quoting.

## Not covered yet

These are not in the table because Lin does not compile them yet, and the interaction-net
oracle alone is orders of magnitude slower than C on them:

- **floats on the oracle alone**: float operations are FFI calls with no pure-Lin fallback yet, so the
  net by itself mis-reduces some float programs; the function compiler computes them correctly
  (mandel above) but they do not yet meet "everything compiles to nets";
- **data structures** (binary-trees, list pipelines): constructors and pattern matches are not
  compiled yet, and that needs the DUP/ERA-derived ownership plan (no GC);
