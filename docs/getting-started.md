# Getting started

## Requirements

- A C99 compiler (`cc`, gcc or clang)
- `libffi`, `pthreads`, `libdl`, `libm`
- Python 3, for some test suites
- Optional: a Vulkan loader, for the GPU driver

The function compiler invokes `cc` at run time, so a C compiler must be on `PATH`
when programs run, not only when Lin is built.

## Building

### With Nix

```bash
nix build              # ./result/bin/lin, with the standard library packaged beside it
nix flake check        # build and run the full test suite
nix run .#test         # run the test runner
nix run .#bench        # run the benchmarks against C
nix develop            # development shell: compiler, gdb, valgrind
```

Nix builds from committed files only. While editing, use the Makefile, which
builds from the working tree.

### With make

```bash
make all               # ./lin and std/drivers/*.so
make test              # build, then run the full suite
make clean
```

`make lin` builds the core alone; `make plugins` builds the drivers.

## Running programs

A Lin source file is a sequence of forms. Definitions define; every other
top-level expression is evaluated and its value printed after `=> `.

```scheme
; hello.lin
(define square (\x (mul x x)))
(square 12)
"hello"
```

```console
$ ./lin hello.lin
=> 144
=> "hello"
```

The standard library is available without any `load`: a library module is read
the first time a program names something in it.

### Command line

```
lin [options] [files...]
lin build <file.lin> [-o <file.line>]
```

| Option | Meaning |
|--------|---------|
| `-e`, `--eval <expr>` | Evaluate the forms in `<expr>` |
| `-t`, `--threads <n>` | Number of worker threads (default: all cores) |
| `-b`, `--bench` | After each result, print rewrite steps, node counts and time |
| `-v`, `--version` | Print the version |
| `-h`, `--help` | Print usage |

With no file and no `-e`, Lin starts the REPL.

### The REPL

```console
$ ./lin
lin 0.1 - interaction combinator language
commands: :type <expr>  :goi <expr>  :load <file>  :help  :q
lin> (define x 5)
lin> (mul x x)
=> 25
lin> :type smap
(t1 -> t2) -> Seq t1 -> Seq t2
```

(Type variables are numbered as they are created, so the numbers you see will differ.)

| Command | Meaning |
|---------|---------|
| `:type <expr>`, `:t` | Print the inferred type of an expression |
| `:load <file>`, `:l` | Load a source file |
| `:goi <expr>` | Print the net's Geometry of Interaction invariant before and after reduction |
| `:help` | A one-line syntax reminder |
| `:q` | Quit |

### Building an artifact

`lin build` evaluates everything that can be evaluated ahead of time and writes
the remaining net to a `.line` file, which runs directly:

```console
$ ./lin build fib.lin -o fib.line
$ ./lin fib.line
=> 832040
```

A `.line` file starts with a `#!` line naming the `lin` binary that built it, so
it can be made executable and run as a command.

## Environment variables

### Common

| Variable | Meaning |
|----------|---------|
| `LIN_THREADS` | Worker threads, as `-t` |
| `LIN_STD` | Path of the prelude to load (default `std/std.lin`) |
| `LIN_STD_DIR` | Directory holding the standard library (default `std`) |
| `LIN_EAGER_STD=1` | Load every library module up front instead of on demand |
| `LIN_NATIVE_CACHE` | Directory for compiled functions (default `~/.cache/lin/native`) |
| `LIN_NATIVE_CC` | C compiler the function compiler invokes (default `cc`) |

### Diagnostics

| Variable | Meaning |
|----------|---------|
| `LIN_FN_OFF=1` | Disable the function compiler; everything is reduced as a net |
| `LIN_FN_DEBUG=1` | Report each function-compiler decision and timing; `2` also prints the generated C |
| `LIN_NO_SHRINK=1` | Skip compile-time simplification of terms |
| `LIN_NO_EGRAPH=1` | Skip the e-graph optimiser |
| `LIN_STEPS=<n>` | Stop reduction after `n` rewrite steps |
| `LIN_LEAKCHECK=1` | With `-b`, report what the result still reaches |
| `LIN_TRACE=1` | Trace reduction |
| `LIN_WAVE_STATS=1` | Print parallel-reduction statistics at exit |

## Next steps

- [Language reference](language.md)
- [Standard library](stdlib.md)
- [Examples](../examples/README.md)
