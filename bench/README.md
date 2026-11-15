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
| seqs | 87 ms | 4 ms | 6 ms | 21.75× | `std/seq.lin`: map, filter and fold over a million-element list |
| binarytrees | 178 ms | 14 ms | 23 ms | 12.71× | Benchmarks Game *binary-trees*, depth 16 |
| bintree | 35 ms | 4 ms | 5 ms | 8.75× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| collatz | 218 ms | 49 ms | 193 ms | 4.45× | A loop calling a helper loop; a max-reduction |
| mandel | 120 ms | 30 ms | 119 ms | 4.00× | Floats; three nested loops over a 1000 × 800 grid |
| fib | 149 ms | 46 ms | 156 ms | 3.24× | Tree recursion: `fib 40` |
| loop | 90 ms | 29 ms | 94 ms | 3.10× | A tail-recursive sum over 100 million iterations |
| tak | 87 ms | 30 ms | 90 ms | 2.90× | Calls whose arguments are calls |
| spectralnorm | 54 ms | 27 ms | 70 ms | 2.00× | Benchmarks Game *spectral-norm*, n = 1000 |
| bst | 45 ms | 23 ms | 25 ms | 1.96× | A search tree: 200,000 inserts, then a weighted walk |
| regexredux | 78 ms | 42 ms | 59 ms | 1.86× | Benchmarks Game *regex-redux*: nine patterns counted and five substitutions over 200,000 letters, with `std/regex.lin` |
| omap | 106 ms | 69 ms | 99 ms | 1.54× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| nqueens | 193 ms | 147 ms | 202 ms | 1.31× | Bitmask backtracking for n = 14; an unbalanced search tree |
| revcomp | 21 ms | 16 ms | 17 ms | 1.31× | Benchmarks Game *reverse-complement*: 1,000,000 letters reversed and complemented |
| knucleotide | 32 ms | 31 ms | 40 ms | 1.03× | Benchmarks Game *k-nucleotide*: fragment counts in 250,000 letters, with `std/hmap.lin` |
| fasta | 16 ms | 16 ms | 19 ms | 1.00× | Benchmarks Game *fasta*, n = 100,000: a repeated and two random sequences, checksummed |
| nbody | 16 ms | 23 ms | 25 ms | 0.70× | Benchmarks Game *n-body*: five bodies, 200,000 steps, in floats |
| words | 5 ms | 9 ms | 12 ms | 0.56× | Text: a 1M-character string built and its words counted |
| fannkuch | 18 ms | 36 ms | 106 ms | 0.50× | Benchmarks Game *fannkuch-redux*, n = 9: every permutation, by prefix reversals |
| pidigits | 454 ms | 857 ms | 885 ms | 0.53× | Benchmarks Game *pidigits*: 2,000 digits of pi on `std/big.lin` |
| array | 7 ms | 19 ms | 25 ms | 0.37× | `std/array.lin`: 1M strided writes, then 1M reads |

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

- **`pidigits` (about 2×).** Arbitrary-precision numbers are lists of limbs in
  `std/big.lin`; the C updates arrays in place, and the step is sequential. Much
  of the gap was memory never freed: 1.9 GB against the C's 13 MB. Results now
  share no cells, and temporaries, locals and fields are freed once dead, which
  brings it to about 220 MB. What remains is mostly the compute on lists of
  limbs.
- **`array`, `words` (about 2–2.5×).** A persistent trie or a list of characters
  against flat C memory. `words` is also short enough (5 ms) that process start
  matters: Lin's is now within 1 ms of an empty C program's.
- **`fannkuch` (about 2×).** Permutations are lists, and each prefix reversal
  builds a new one; the C flips nine bytes in place. Its permutations run in
  parallel, which is most of what closes the gap from 6×. Reversing in place
  needs the ownership analysis to see that a list it reads and then hands on is
  still owned.
- **`nbody` (about 1.4×).** Five bodies are a list of records; the C's loop over
  an array of five structs is unrolled and vectorised. The steps are sequential,
  so there is no parallelism to use.
- **`fasta` is level** with the C.

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
