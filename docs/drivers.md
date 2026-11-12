# Drivers

A driver is a shared library, loaded at run time, that takes over part of the
work of reducing or observing a net. Drivers are where Lin's performance comes
from, and they are deliberately outside the core: the core's rewrite rules define
what a program means, and a driver may only produce what those rules would have
produced.

- [The driver contract](#the-driver-contract)
- [Loading drivers](#loading-drivers)
- [The drivers](#the-drivers)
- [The function compiler](#the-function-compiler)
  - [The program cache](#the-program-cache)

## The driver contract

1. **Same answer.** A driver's result must equal the net's own reduction. The
   test suite runs programs with and without each driver and compares.
2. **Decline, never guess.** When a driver meets something it does not handle, it
   leaves the net untouched and the core reduces it.
3. **Structure only.** A driver recognises shapes in the net: node kinds, wiring,
   and the structural conventions described in
   [Architecture](architecture.md#data-as-net-structure). Nothing in a net is
   tagged for a driver's benefit.

Before rewriting, a driver *claims* a region of the net: a set of redexes and the
ports where the region meets the rest. The core validates the claim, which is what
allows a driver to work on its region while other reduction proceeds. The
interface is declared in [`src/lin.h`](../src/lin.h).

## Loading drivers

Drivers are loaded from Lin code. The prelude loads the three that ordinary
programs rely on (`arith`, `readback`, `fn`); the others are opt-in.

```scheme
(load "std/drivers/simd.lin")     ; load a driver by its loader module
```

| Function | Meaning |
|----------|---------|
| `(set_driver name)` | Make `name` the active reduction driver |
| `(add_driver name)` | Add a driver; the most recently added is consulted first |
| `clear_drivers` | Return to the core alone |
| `get_driver` | Name of the active driver |

A driver that is not part of the standard library can be loaded by path with
`load_lib` and then registered by name; `examples/linden/` does this.

## The drivers

| Driver | Source | Role |
|--------|--------|------|
| `arith` | `std/drivers/arith.c` | Computes a primitive operation (`add`, `fmul`, a comparison, ...) on evaluated operands in one step, instead of rewriting through its bit-level definition |
| `fn` | `std/drivers/fn.c` | The function compiler: compiles recursive functions to native code. See below |
| `readback` | `std/drivers/readback.c` | Turns a reduced net into a printed value according to its type, runs I/O effects, and dispatches FFI calls |
| `native` | `std/drivers/native.c` | Compiles a tree of arithmetic operations to one C expression |
| `simd` | `std/drivers/simd.c` | Evaluates arithmetic in batches |
| `gpu` | `std/drivers/gpu.c` | Fires rewrite rules on a GPU through Vulkan compute; falls back to the CPU when no device is available |
| `text` | `std/drivers/text.c` | Constant-time indexing into strings, for text-heavy programs |

The integer and float semantics shared by every driver, and by the code the
function compiler generates, are defined once in
[`std/runtime/i64.h`](../std/runtime/i64.h).

## The function compiler

`std/drivers/fn.c` is responsible for most of Lin's speed. When reduction
reaches a call to a recursive function, the driver reads the function *out of its
net*, translates it to C, compiles it with the system C compiler, and replaces
the call with its result.

### What it compiles

- Integer and float arithmetic, comparisons, and conditionals
- Calls among functions, including mutual recursion
- Datatypes: constructors and `match`
- Lists and strings
- Higher-order calls: a function passed as an argument is inlined into a copy of
  the callee specialised to it, and a local function that uses variables of an
  enclosing one is lifted to take them as parameters

A value already present in the net when the call is reached, such as a string
read from input or a structure built earlier, is passed into the compiled code
rather than rebuilt.

### What it declines

The compiled code is strict; Lin is lazy. The driver compiles only where the
difference cannot be observed, and otherwise leaves the call to the net:

- A value used in a way its inferred shape does not allow
- A structure that is infinite or outgrows memory or the stack while being built:
  the compiled call is abandoned and the net computes the call lazily
- Any shape of net it does not recognise

`LIN_FN_DEBUG=1` prints each decision and the reason for each decline.

### Memory in compiled code

Compiled code allocates from an arena that is released when the call returns.
There is no collector. The driver analyses ownership from the function's own
structure, which shows exactly where a value is shared:

- **In-place update.** A `match` on a value nothing else holds may build its
  result in the block it took apart. Inserting into a tree, mapping over a list
  and setting an array element all update in place when the old value is not used
  again, and copy when it is.
- **Reuse along every path.** A path that consumes a block either rebuilds in it
  or returns it to a free list, so a loop that builds and consumes cells runs in
  constant memory.
- **Unread fields are not computed.** A constructor field that no part of the
  program reads is never evaluated or stored, matching lazy semantics.

### Loops

- **Tail calls** are loops.
- **Destination passing.** A function that builds a cell around its own recursive
  call, such as `map`, `filter` and `append`, is compiled to build the cell first
  and pass the address of the unfinished field to the call. The recursion becomes
  a loop, so a list of any length is processed in constant stack.
- **Indexed fields.** Reading or replacing field `k` of a wide constructor, as the
  array trie does, is one indexed load or store.

### Parallelism

- **Independent calls.** When a function's result combines two or more recursive
  calls, as in `fib` or a tree traversal, they run on separate threads down to a
  depth chosen from the thread count.
- **Reductions.** A loop that folds an associative operation over a range
  (wrapping `add` or `mul`, the bitwise operations, `max` and `min`) is split
  into chunks that run on separate threads.

Both are checked to give the same answer at every thread count
(`test/fn_compile.sh`).

### Caching

Generated C is compiled once and cached by content hash under
`~/.cache/lin/native` (`LIN_NATIVE_CACHE` overrides the location). The first run
of a program pays for the C compiler; later runs load the cached library.

### The program cache

Compiling is not the only work that can be saved. When every top-level
expression of a program was answered by a single compiled call on constants, the
function compiler records which compiled unit answered each one and with which
arguments. The next run of the same program runs those units directly, without
parsing, type checking or analysing it again.

The cache never stores an answer: a cached run performs the whole computation.
An entry is keyed on the program's text, the library and drivers on disk, the
`lin` binary and the environment's `LIN_` settings, so changing any of them is a
different program. A program is not cached if it performs an effect or a foreign
call, loads another source file, or has an expression the compiler did not
answer with a single number or boolean. A run with a diagnostic setting
(`LIN_FN_DEBUG`, `LIN_TRACE`, and so on) is always made in full.

### Controls

| Variable | Effect |
|----------|--------|
| `LIN_FN_OFF=1` | Disable the function compiler |
| `LIN_FN_DEBUG=1` | Print decisions and timings; `2` also prints the generated C |
| `LIN_NATIVE_CC` | The C compiler to invoke (default `cc`) |
| `LIN_NATIVE_CACHE` | The cache directory |
| `LIN_NO_CACHE=1` | Do not use the program cache |
| `LIN_CACHE_DEBUG=1` | Report whether a run came from the program cache |

## Writing a driver

A driver is a C file that includes `src/lin.h`, exports a registration symbol,
and is compiled to a shared library. `std/drivers/text.c` is the smallest
complete example; `std/drivers/arith.c` shows a driver that folds redexes. The
driver ABI is versioned, and a driver built against a different version is
refused at load (`test/driver_abi.sh`).
