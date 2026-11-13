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

4-core x86-64, gcc 15. `C / Lin` above 1 means Lin is faster. Nine of the programs follow the
[Computer Language Benchmarks Game](https://benchmarksgame-team.pages.debian.net/benchmarksgame/)
definitions, at reduced sizes, and generate their own input so each is a single file.

| Benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | What it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| binarytrees | 200 ms | 35 ms | 27 ms | 5.71× | Benchmarks Game *binary-trees*, depth 16 |
| bintree | 34 ms | 6 ms | 7 ms | 5.67× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| seqs | 69 ms | 13 ms | 12 ms | 5.31× | `std/seq.lin`: map, filter and fold over a million-element list |
| collatz | 221 ms | 52 ms | 198 ms | 4.25× | A loop calling a helper loop; a max-reduction |
| loop | 91 ms | 26 ms | 102 ms | 3.50× | A tail-recursive sum over 100 million iterations |
| mandel | 123 ms | 38 ms | 125 ms | 3.24× | Floats; three nested loops over a 1000 × 800 grid |
| fib | 161 ms | 52 ms | 183 ms | 3.10× | Tree recursion: `fib 40` |
| tak | 89 ms | 34 ms | 91 ms | 2.62× | Calls whose arguments are calls |
| bst | 59 ms | 30 ms | 27 ms | 1.97× | A search tree: 200,000 inserts, then a weighted walk |
| spectralnorm | 54 ms | 34 ms | 72 ms | 1.59× | Benchmarks Game *spectral-norm*, n = 1000 |
| omap | 112 ms | 73 ms | 105 ms | 1.53× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| regexredux | 87 ms | 62 ms | 62 ms | 1.40× | Benchmarks Game *regex-redux*: nine patterns counted and five substitutions over 200,000 letters, with `std/regex.lin` |
| nqueens | 206 ms | 152 ms | 211 ms | 1.36× | Bitmask backtracking for n = 14; an unbalanced search tree |
| revcomp | 19 ms | 25 ms | 27 ms | 0.76× | Benchmarks Game *reverse-complement*: 1,000,000 letters reversed and complemented |
| knucleotide | 36 ms | 72 ms | 72 ms | 0.50× | Benchmarks Game *k-nucleotide*: fragment counts in 250,000 letters, with `std/hmap.lin` |
| fasta | 17 ms | 36 ms | 38 ms | 0.47× | Benchmarks Game *fasta*, n = 100,000: a repeated and two random sequences, checksummed |
| array | 8 ms | 20 ms | 25 ms | 0.40× | `std/array.lin`: 1M strided writes, then 1M reads |
| nbody | 18 ms | 51 ms | 53 ms | 0.35× | Benchmarks Game *n-body*: five bodies, 200,000 steps, in floats |
| words | 4 ms | 12 ms | 11 ms | 0.33× | Text: a 1M-character string built and its words counted |
| pidigits | 577 ms | 1812 ms | 1661 ms | 0.32× | Benchmarks Game *pidigits*: 2,000 digits of pi on `std/big.lin` |
| fannkuch | 20 ms | 115 ms | 119 ms | 0.17× | Benchmarks Game *fannkuch-redux*, n = 9: every permutation, by prefix reversals |

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

- **`fannkuch` (about 6×).** Permutations are lists rebuilt at every step; the
  C flips an array of nine bytes in place.
- **`array`, `words` and `fasta` (about 2–3×).** A persistent trie
  or linked list against flat C memory, and process start-up: the C starts in
  about 2 ms, Lin in about 5 ms.
- **`pidigits` (about 3×).** Arbitrary-precision numbers are persistent lists of
  limbs in `std/big.lin`; the C updates arrays in place.
- **`nbody` (about 3×).** Each step folds every body over the whole list; the
  inner arithmetic is about three times slower per interaction than the C's,
  and the cause has not been measured.
- **`knucleotide` and `revcomp` (about 1.3–2×).** List-based text against byte
  buffers and an open-addressing hash table.

Flat memory is not something a pure net can express directly, so closing these
gaps fully would take a representation change in the function compiler rather
than a change to the library.

## Programs not in the suite

**mandelbrot** in its Benchmarks Game form (bitmap output) is covered by `mandel`.
Every other Benchmarks Game program has a row above.

## Without the function compiler

`LIN_FN_OFF=1` runs the same programs by net reduction alone. They produce the
same answers, far more slowly: the interaction-net reducer is the definition of
the language, and the function compiler is what makes it fast.
