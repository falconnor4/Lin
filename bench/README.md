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
| seqs | 91 ms | 4 ms | 5 ms | 22.75× | `std/seq.lin`: map, filter and fold over a million-element list |
| binarytrees | 172 ms | 19 ms | 24 ms | 9.05× | Benchmarks Game *binary-trees*, depth 16 |
| bintree | 32 ms | 4 ms | 6 ms | 8.00× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| mandel | 97 ms | 26 ms | 88 ms | 3.73× | Floats; three nested loops over a 1000 × 800 grid |
| collatz | 202 ms | 56 ms | 190 ms | 3.61× | A loop calling a helper loop; a max-reduction |
| loop | 87 ms | 27 ms | 91 ms | 3.22× | A tail-recursive sum over 100 million iterations |
| tak | 76 ms | 32 ms | 84 ms | 2.38× | Calls whose arguments are calls |
| fib | 137 ms | 62 ms | 153 ms | 2.21× | Tree recursion: `fib 40` |
| spectralnorm | 54 ms | 35 ms | 65 ms | 1.54× | Benchmarks Game *spectral-norm*, n = 1000 |
| omap | 144 ms | 101 ms | 121 ms | 1.43× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| regexredux | 81 ms | 64 ms | 82 ms | 1.27× | Benchmarks Game *regex-redux*: nine patterns counted and five substitutions over 200,000 letters, with `std/regex.lin` |
| nqueens | 197 ms | 163 ms | 164 ms | 1.21× | Bitmask backtracking for n = 14; an unbalanced search tree |
| bst | 39 ms | 37 ms | 39 ms | 1.05× | A search tree: 200,000 inserts, then a weighted walk |
| fasta | 17 ms | 18 ms | 18 ms | 0.94× | Benchmarks Game *fasta*, n = 100,000: a repeated and two random sequences, checksummed |
| array | 10 ms | 11 ms | 12 ms | 0.91× | `std/array.lin`: 1M strided writes, then 1M reads |
| revcomp | 16 ms | 23 ms | 23 ms | 0.70× | Benchmarks Game *reverse-complement*: 1,000,000 letters reversed and complemented |
| nbody | 16 ms | 27 ms | 26 ms | 0.59× | Benchmarks Game *n-body*: five bodies, 200,000 steps, in floats |
| fannkuch | 16 ms | 28 ms | 75 ms | 0.57× | Benchmarks Game *fannkuch-redux*, n = 9: every permutation, by prefix reversals |
| knucleotide | 41 ms | 90 ms | 67 ms | 0.46× | Benchmarks Game *k-nucleotide*: fragment counts in 250,000 letters, with `std/hmap.lin` |
| pidigits | 493 ms | 1334 ms | 1211 ms | 0.37× | Benchmarks Game *pidigits*: 2,000 digits of pi on `std/big.lin` |
| words | 4 ms | 18 ms | 22 ms | 0.22× | Text: a 1M-character string built and its words counted |

The machine these were measured on is shared and noisy; expect variation of
about 15% between runs. Re-run before quoting a number.

## Reading the results

**Parallelism.** The function compiler runs independent recursive calls on
separate threads (`fib`, `tak`, `bintree`, `nqueens`), splits loops that fold an
associative operation (`loop`, `collatz`, `mandel`), maps a list in stretches
when each element takes a call to compute (`spectralnorm`), runs the independent
loops of one expression side by side (`knucleotide`'s seven maps, `regexredux`'s
nine counts), and computes the steps of a loop whose steps do not depend on one
another together (`fannkuch`'s permutations). With one thread (`Lin -t 1`) these
run at about the speed of the C or slower.

**Memory.** `seqs`, `bst` and `omap` are ahead on one thread too: compiled code
allocates from an arena, rebuilds structures in place when nothing else holds
them, and frees everything at once, where the C calls `malloc` and `free` per
node. In `seqs` and `revcomp` the intermediate lists are never built at all: a
loop that builds a list and the loop that takes it apart are fused into one.

**Sharing.** In `binarytrees` and `bintree` the two subtrees of a node are the
same expression, `(make (sub d 1))` written twice. Lin evaluates a shared
expression once, so each level of a tree is built once and both children are the
same value; the C builds every node. This is the language's semantics rather
than an optimisation applied to these programs, and it is why Lin's time barely
depends on the tree's size. A version that forced the two subtrees to be
different values would measure allocation instead, as `bst` and `omap` do.

## Where Lin is behind

- **`pidigits` (about 2.5×).** Arbitrary-precision numbers are lists of limbs in
  `std/big.lin`; the C updates arrays in place, and the step is sequential. With
  reference counting every block it builds is freed again (130.7M built, 130.7M
  freed): what remains is the compute on lists of limbs, and their counts.
- **`words` (about 4×), `knucleotide` (about 2×).** A list of characters, and a
  hash trie, against flat C memory: each cell carries a count word, and each
  step takes and releases counts. `words` is also short enough (4 ms) that
  process start matters.
- **`fannkuch` (about 2×).** Permutations are lists, and each prefix reversal
  builds a new one; the C flips nine bytes in place. Its permutations run in
  parallel, which is most of what closes the gap from 6×.
- **`nbody` (about 1.5×).** Five bodies are a list of records; the C's loop over
  an array of five structs is unrolled and vectorised. The steps are sequential,
  so there is no parallelism to use.
- **`array`, `fasta` are level** with the C. An array is one flat block in
  compiled code (`vec a`, see [owned vectors](../docs/drivers.md#owned-vectors)),
  set in place when nothing else holds it.

## Programs not in the suite

**mandelbrot** in its Benchmarks Game form (bitmap output) is covered by `mandel`.
Every other Benchmarks Game program has a row above.

## Without the function compiler

`LIN_FN_OFF=1` runs the same programs by net reduction alone. They produce the
same answers, far more slowly: the interaction-net reducer is the definition of
the language, and the function compiler is what makes it fast.
