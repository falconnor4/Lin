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
  includes start-up, reading the library, type checking, and loading the
  compiled functions from the native-code cache. The first Lin run of each
  program fills that cache and is not timed, just as the C compile is not.
- **Outputs must match**, or the row reports a mismatch instead of a time.
- **`Lin -t 1` is reported** so the single-threaded comparison is visible.

## Results

4-core x86-64, gcc 15. `C / Lin` above 1 means Lin is faster.

| Benchmark | C -O3 | Lin | Lin -t 1 | C / Lin | What it exercises |
|-----------|-------|-----|----------|---------|-------------------|
| bintree | 33 ms | 8 ms | 7 ms | 4.12× | Constructors and `match`: a depth-20 tree (2M nodes) built and counted |
| seqs | 73 ms | 18 ms | 22 ms | 4.06× | `std/seq.lin`: map, filter and fold over a million-element list |
| collatz | 165 ms | 46 ms | 163 ms | 3.59× | A loop calling a helper loop; a max-reduction |
| loop | 92 ms | 26 ms | 93 ms | 3.54× | A tail-recursive sum over 100 million iterations |
| fib | 156 ms | 47 ms | 161 ms | 3.32× | Tree recursion: `fib 40` |
| tak | 70 ms | 26 ms | 63 ms | 2.69× | Calls whose arguments are calls |
| mandel | 85 ms | 38 ms | 112 ms | 2.24× | Floats; three nested loops over a 1000 × 800 grid |
| bst | 38 ms | 30 ms | 23 ms | 1.27× | A search tree: 200,000 inserts, then a weighted walk |
| nqueens | 196 ms | 160 ms | 205 ms | 1.23× | Bitmask backtracking for n = 14; an unbalanced search tree |
| omap | 123 ms | 117 ms | 155 ms | 1.05× | `std/omap.lin`, a red-black tree: 200,000 inserts and lookups |
| words | 5 ms | 15 ms | 13 ms | 0.33× | Text: a 1M-character string built and its words counted |
| array | 6 ms | 51 ms | 55 ms | 0.12× | `std/array.lin`: 1M strided writes, then 1M reads |

The machine these were measured on is shared and noisy; expect variation of
about 15% between runs. Re-run before quoting a number.

## Reading the results

**Where Lin is ahead, it is mostly parallelism.** The function compiler runs
independent recursive calls on separate threads (`fib`, `tak`, `bintree`,
`nqueens`) and splits loops that fold an associative operation (`loop`,
`collatz`, `mandel`). With one thread (`Lin -t 1`) these run at about the speed
of the C.

**`seqs`, `bst` and `bintree` are ahead on one thread too.** Lin's compiled code
allocates from an arena, rebuilds structures in place when nothing else holds
them, and frees everything at once; the C uses `malloc` and `free` per node.

## Where Lin is behind

`array` and `words` compare a persistent structure with flat mutable memory.

- **`array`.** A Lin array is a 32-way trie, so an element is four dependent
  loads away where C does one indexed store. Updates are in place and run as a
  loop, and the run itself takes about 20 ms. The rest is the front end: a
  program that uses the trie spends about 20 ms being parsed, checked and
  analysed before it runs, and the C's time has no compiler in it.
- **`words`.** A Lin string is a linked list with a 16-byte cell per character;
  the C scans a byte buffer. The run takes about 8 ms against 5 ms for the whole
  C process; the remainder is start-up.

Flat memory is not something a pure net can express directly, so closing the
`array` gap fully would take a representation change in the function compiler
rather than a change to the library.

## Without the function compiler

`LIN_FN_OFF=1` runs the same programs by net reduction alone. They produce the
same answers, far more slowly: the interaction-net reducer is the definition of
the language, and the function compiler is what makes it fast.
