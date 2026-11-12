# Benchmarks

Each benchmark is one algorithm written twice: in Lin (`name.lin`) and in the C a
programmer would naturally write for it (`name.c`).

```bash
bench/run.sh ./lin       # or: nix run .#bench
```

## Method

- **Same algorithm, natural code.** No memoisation or restructuring on the Lin
  side; no hand-written threads on the C side. Where Lin is faster, it is because
  of what Lin does without being asked.
- **C is built with `cc -O3 -march=native -ffp-contract=off`.** Lin's float
  arithmetic is strict IEEE, so the C is held to the same; with contraction
  enabled the two programs compute different answers and cannot be compared.
- **Times are wall clock for the whole process, best of three.** For Lin that
  includes start-up and reading the library. The first Lin run of each program
  compiles it and fills the caches, and is not timed, just as the C compile is
  not. On later runs an unchanged program runs its compiled code directly
  (see [the program cache](../docs/drivers.md#the-program-cache)).
- **Outputs must match**, or the row reports a mismatch instead of a time.
- **`Lin -t 1` is reported** so the single-threaded comparison is visible.

## Results

4-core x86-64, gcc 15. `C / Lin` above 1 means Lin is faster. `binarytrees` and `nbody` follow
the [Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/)
definitions at reduced sizes.

| Benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | What it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| binarytrees | 173 ms | 25 ms | 28 ms | 6.92× | Benchmarks Game *binary-trees*, depth 16: many trees built and checked |
| bintree | 33 ms | 5 ms | 5 ms | 6.60× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| seqs | 81 ms | 14 ms | 20 ms | 5.79× | `std/seq.lin`: map, filter and fold over a million-element list |
| collatz | 165 ms | 44 ms | 184 ms | 3.75× | A loop calling a helper loop; a max-reduction |
| mandel | 86 ms | 29 ms | 96 ms | 2.97× | Floats; three nested loops over a 1000 × 800 grid |
| loop | 72 ms | 27 ms | 74 ms | 2.67× | A tail-recursive sum over 100 million iterations |
| fib | 125 ms | 48 ms | 140 ms | 2.60× | Tree recursion: `fib 40` |
| tak | 72 ms | 35 ms | 81 ms | 2.06× | Calls whose arguments are calls |
| omap | 116 ms | 94 ms | 109 ms | 1.23× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| bst | 30 ms | 30 ms | 26 ms | 1.00× | A search tree: 200,000 inserts, then a weighted walk |
| nqueens | 156 ms | 161 ms | 179 ms | 0.97× | Bitmask backtracking for n = 14; an unbalanced search tree |
| words | 4 ms | 11 ms | 14 ms | 0.36× | Text: a 1M-character string built and its words counted |
| array | 7 ms | 30 ms | 28 ms | 0.23× | `std/array.lin`: 1M strided writes, then 1M reads |
| nbody | 14 ms | 482 ms | 487 ms | 0.03× | Benchmarks Game *n-body*: five bodies, 200,000 steps, in floats |

The machine these were measured on is shared and noisy; expect variation of
about 15% between runs. Re-run before quoting a number.

## Reading the results

**Parallelism.** The function compiler runs independent recursive calls on
separate threads (`fib`, `tak`, `bintree`, `nqueens`) and splits loops that fold
an associative operation (`loop`, `collatz`, `mandel`). With one thread
(`Lin -t 1`) these run at about the speed of the C.

**Memory.** `seqs` and `omap` are ahead on one thread too: compiled code
allocates from an arena, rebuilds structures in place when nothing else holds
them, and frees everything at once, where the C calls `malloc` and `free` per
node.

**Sharing.** In `binarytrees` and `bintree` the two subtrees of a node are the
same expression, `(make (sub d 1))` written twice. Lin evaluates a shared
expression once, so each level of a tree is built once and both children are the
same value; the C builds every node. This is the language's semantics rather
than an optimisation applied to these programs, and it is why Lin's time barely
depends on the tree's size. A version that forced the two subtrees to be
different values would measure allocation instead, as `bst` and `omap` do.

## Where Lin is behind

- **`nbody` (about 30× slower).** The program is a map over the list of bodies
  in which each body folds over that same list. The list is therefore shared
  while it is being mapped, so nothing can be updated in place, and each of the
  five million interactions allocates a new body. Compiled code has no way yet
  to free a structure that has become garbage while its unit is still running:
  it either reuses a block in place or keeps it until the call returns. Closing
  this needs the compiled counterpart of the net's eraser, dropping an owned
  value at its last use.
- **`array` (about 4× slower).** A Lin array is a 32-way trie, so an element is
  four dependent loads away where C does one indexed store. Updates are in place
  and run as a loop.
- **`words` (about 3× slower).** A Lin string is a linked list with a 16-byte
  cell per character; the C scans a byte buffer. Most of what remains is
  start-up: the C process takes about 2 ms to start here and Lin about 5 ms.

Flat memory is not something a pure net can express directly, so closing the
`array` gap fully would take a representation change in the function compiler
rather than a change to the library.

## Programs not yet in the suite

Two more Benchmarks Game programs were tried and are not included because they
do not yet run acceptably:

- **spectral-norm.** The function compiler compiles its pieces separately
  rather than as one unit, and declines one shape outright (a function argument
  whose body is a literal, such as `(\i 1.0)`), so most of the program runs by
  net reduction.
- **fannkuch-redux** has not been written.

## Without the function compiler

`LIN_FN_OFF=1` runs the same programs by net reduction alone. They produce the
same answers, far more slowly: the interaction-net reducer is the definition of
the language, and the function compiler is what makes it fast.
