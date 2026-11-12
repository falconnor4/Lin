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

4-core x86-64, gcc 15. `C / Lin` above 1 means Lin is faster. `binarytrees`, `nbody` and `spectralnorm`
follow the [Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/)
definitions at reduced sizes.

| Benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | What it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| binarytrees | 205 ms | 29 ms | 29 ms | 7.07× | Benchmarks Game *binary-trees*, depth 16: many trees built and checked |
| bintree | 48 ms | 7 ms | 6 ms | 6.86× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| seqs | 89 ms | 15 ms | 15 ms | 5.93× | `std/seq.lin`: map, filter and fold over a million-element list |
| collatz | 248 ms | 62 ms | 221 ms | 4.00× | A loop calling a helper loop; a max-reduction |
| mandel | 134 ms | 39 ms | 141 ms | 3.44× | Floats; three nested loops over a 1000 × 800 grid |
| fib | 170 ms | 54 ms | 183 ms | 3.15× | Tree recursion: `fib 40` |
| loop | 102 ms | 35 ms | 111 ms | 2.91× | A tail-recursive sum over 100 million iterations |
| tak | 107 ms | 45 ms | 100 ms | 2.38× | Calls whose arguments are calls |
| bst | 50 ms | 30 ms | 31 ms | 1.67× | A search tree: 200,000 inserts, then a weighted walk |
| omap | 128 ms | 79 ms | 113 ms | 1.62× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| spectralnorm | 61 ms | 43 ms | 117 ms | 1.42× | Benchmarks Game *spectral-norm*, n = 1000: ten power-method steps |
| nqueens | 218 ms | 177 ms | 234 ms | 1.23× | Bitmask backtracking for n = 14; an unbalanced search tree |
| words | 6 ms | 13 ms | 13 ms | 0.46× | Text: a 1M-character string built and its words counted |
| nbody | 18 ms | 50 ms | 55 ms | 0.36× | Benchmarks Game *n-body*: five bodies, 200,000 steps, in floats |
| array | 8 ms | 24 ms | 29 ms | 0.33× | `std/array.lin`: 1M strided writes, then 1M reads |

The machine these were measured on is shared and noisy; expect variation of
about 15% between runs. Re-run before quoting a number.

## Reading the results

**Parallelism.** The function compiler runs independent recursive calls on
separate threads (`fib`, `tak`, `bintree`, `nqueens`), splits loops that fold an
associative operation (`loop`, `collatz`, `mandel`), and maps a list in
stretches when each element takes a call to compute (`spectralnorm`, whose rows
are independent). With one thread (`Lin -t 1`) these run at about the speed of
the C.

**Memory.** `seqs`, `bst` and `omap` are ahead on one thread too: compiled code
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

- **`nbody` (about 3× slower).** The program is a map over the list of bodies
  in which each body folds over that same list, building a new list every step.
  Compiled code now starts each fold from a copy of the body and updates it in
  place, and drops the previous step's list once the new one is built, so the
  run uses a few blocks however long it is. What remains is the inner
  arithmetic: per interaction the C is still about three times faster, and why
  has not been measured (the likely cause is that Lin's loop writes each body's
  velocity back to memory at every interaction where the C keeps it in
  registers).
- **`array` (about 3× slower).** A Lin array is a 32-way trie, so an element is
  four dependent loads away where C does one indexed store. Updates are in place
  and run as a loop.
- **`words` (about 3× slower).** A Lin string is a linked list with a 16-byte
  cell per character; the C scans a byte buffer. Most of what remains is
  start-up: the C process takes about 2 ms to start here and Lin about 5 ms.

Flat memory is not something a pure net can express directly, so closing the
`array` gap fully would take a representation change in the function compiler
rather than a change to the library.

## Programs not yet in the suite

**fannkuch-redux**, **fasta**, **k-nucleotide** and the other Benchmarks Game
programs have not been written. Each of the three that were added found faults
in the compiler (see the commit history), so more are worth adding.

## Without the function compiler

`LIN_FN_OFF=1` runs the same programs by net reduction alone. They produce the
same answers, far more slowly: the interaction-net reducer is the definition of
the language, and the function compiler is what makes it fast.
