<p align="center">
  <img src="docs/Lin.svg" alt="Lin" width="240">
</p>

**Lin** is a pure functional programming language whose programs are interaction nets.
A program is compiled to a graph of four kinds of node, and evaluation is graph
rewriting: there is no garbage collector, shared work is done once, and independent
work runs in parallel without the program asking for it.

```scheme
(datatype (Tree a) (leaf) (node (v a) (l Tree a) (r Tree a)))

(define insert (\x (\t (match t
  (leaf (node x leaf leaf))
  ((node v l r) (if (lt x v) (node v (insert x l) r) (node v l (insert x r))))))))

(insert 2 (insert 1 (insert 3 leaf)))
; => (node 3 (node 1 leaf (node 2 leaf leaf)) leaf)

(ssum (smap (\x (mul x x)) (srange 0 1000000)))
; => 333332833333500000
```

## Highlights

- **A small, pure core.** The engine (`src/`, about 5,300 lines of C99) knows lambda,
  application, duplication and erasure. Numbers, strings, floats and datatypes are
  all ordinary net structure built from those.
- **No garbage collector.** Memory is reclaimed by the calculus itself: a rewrite
  frees what it consumes, and erasers remove what nothing uses.
- **Parallel by construction.** Rewrites that do not overlap fire together across
  threads; compiled functions fork independent recursive calls and split
  associative loops.
- **Compiled where it counts.** A driver reads recursive functions out of their own
  nets and compiles them to native code, with in-place update of data nothing else
  holds. The net remains the authority: anything the compiler declines is reduced
  as a net, and the two always agree.
- **Typed.** Hindley–Milner inference with parametric algebraic datatypes and
  pattern matching. Values print by their type.
- **A standard library written in Lin.** Lists, sequences, persistent arrays,
  ordered maps, strings, floats, I/O and a C FFI, loaded on demand.

## Performance

Wall-clock time for the whole process, from source, against the same algorithm in C
built with `cc -O3 -march=native` (4 cores; see [`bench/`](bench/README.md) for the
method and the full table):

| Benchmark | C | Lin | Lin vs C |
|-----------|---|-----|----------|
| Map, filter and fold over a 1M-element list | 87 ms | 4 ms | 21.8× faster |
| Benchmarks Game binary-trees, depth 16 | 178 ms | 14 ms | 12.7× faster |
| Collatz, longest chain below one million | 218 ms | 49 ms | 4.4× faster |
| Mandelbrot, 1000 × 800, in floats | 120 ms | 30 ms | 4.0× faster |
| `fib 40`, tree recursion | 149 ms | 46 ms | 3.2× faster |
| Benchmarks Game spectral-norm, n = 1000 | 54 ms | 27 ms | 2.0× faster |
| Search tree, 200,000 inserts | 45 ms | 23 ms | 2.0× faster |
| Benchmarks Game regex-redux, against POSIX `regex.h` | 78 ms | 42 ms | 1.9× faster |
| Red-black map, 200,000 inserts and lookups | 106 ms | 69 ms | 1.5× faster |
| Benchmarks Game reverse-complement | 21 ms | 16 ms | 1.3× faster |
| Benchmarks Game k-nucleotide | 32 ms | 31 ms | level |
| Benchmarks Game fasta | 16 ms | 16 ms | level |
| Benchmarks Game n-body | 16 ms | 23 ms | 1.4× slower |
| Benchmarks Game fannkuch-redux, n = 9 | 18 ms | 36 ms | 2.0× slower |
| Words in a 1M-character string | 5 ms | 9 ms | 1.8× slower |
| Array, 1M strided writes and reads | 7 ms | 19 ms | 2.7× slower |
| Benchmarks Game pidigits, 2,000 digits | 557 ms | 1407 ms | 2.5× slower |

Lin is ahead on 14 of the 21 benchmarks and level with the C on two more: where it
runs work in parallel that the C runs on one core, where it shares a computation
the C repeats, where it never builds the intermediate lists a pipeline describes,
and where it updates data in place. It is behind on five, where a persistent
structure (a list, a trie, limbs of a big number) is compared with flat mutable
memory. The full table is in [`bench/`](bench/README.md).

## Quick start

Lin builds with any C99 compiler and `libffi`. With [Nix](https://nixos.org/):

```bash
nix build              # build ./result/bin/lin
nix flake check        # run the full test suite
nix develop            # a shell with the toolchain
```

Without Nix:

```bash
make all               # build ./lin and the drivers in std/drivers/
make test              # build, then run the full suite against the working tree
```

Run a program, evaluate an expression, or start the REPL:

```bash
./lin examples/pure-functional/scott_lists.lin
./lin -e '(mul 6 7)'
./lin
```

## Documentation

| Document | Contents |
|----------|----------|
| [Getting started](docs/getting-started.md) | Building, running programs, the REPL, command-line options |
| [Language reference](docs/language.md) | Syntax, definitions, types, datatypes, pattern matching, modules |
| [Standard library](docs/stdlib.md) | Every module and what it provides |
| [Architecture](docs/architecture.md) | Interaction nets, the core engine, memory, parallel reduction |
| [Drivers](docs/drivers.md) | The driver system and the function compiler |
| [Development](docs/development.md) | Repository layout, tests, conventions |
| [Benchmarks](bench/README.md) | Method and results against C |
| [Examples](examples/README.md) | A guided index of the example programs |

## Repository layout

```
src/            the core engine: parser, type checker, net compiler, reducer
std/            the standard library (Lin) and its drivers (C plugins)
test/           the test suite
bench/          benchmarks against C
examples/       example programs
docs/           documentation
```

## Status

Lin is under active development and its interfaces may change. The test suite
(84 suites, about 1,500 assertions) passes on Linux x86-64. Known gaps are listed
in the [language reference](docs/language.md#limitations) and the
[benchmarks](bench/README.md#where-lin-is-behind).

## License

MIT
