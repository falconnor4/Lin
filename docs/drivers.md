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
rather than rebuilt. A small one that is pure data (constructors and numbers,
such as a table of constants the program defines) is compiled into the unit as
a constant instead, so that the program cache can answer for the program.

### What it declines

The compiled code is strict; Lin is lazy. The driver compiles only where the
difference cannot be observed, and otherwise leaves the call to the net:

- A value used in a way its inferred shape does not allow
- A value whose shape cannot be worked out. Shapes follow each value's
  datatype parameters, so a list of lists of numbers is `list(list(num))` and
  compiles, though the cells of the inner and the outer lists hold different
  kinds of value. What a unit is handed from the net is known by how the unit
  uses it: an inner list's head added as a number makes the outer list's
  elements lists of numbers. A function called at two shapes (`nth` on a list
  of lists and on the lists in it) is given a version for each
- A structure that is infinite or outgrows memory or the stack while being built:
  the compiled call is abandoned and the net computes the call lazily
- Any shape of net it does not recognise

`LIN_FN_DEBUG=1` prints each decision and the reason for each decline.

### Recursive calls it declines

A recursive definition reaches the net as the Y combinator applied to the
function, `Y F`. Reduced as it stands, every call runs the combinator's own
machinery: its self-application is unfolded, and `F` is copied through layers of
the combinator's fans. When the driver declines a call, it rewrites it with the
equation the combinator computes, `Y v = v (Y v)`, using only the net's own node
kinds:

- `(Y v) args` becomes `(v₁ (Y' v₂)) args`, where `v₁` and `v₂` are the two
  sides of one new fan on `v`. Nothing of `v` is copied by the driver: the fan
  copies it as each call reaches it, so a call pays only for what it uses (an
  untaken branch is never copied), and whatever is reduced in front of the fan is
  reduced once and shared by every call. There is no walk over `v` and no limit
  on its size.
- `Y'` is a copy of the combinator (a fixed dozen nodes) on a new application,
  and the old pair is erased, so a demand root that named it goes with it.
- The fan's label is the call's own (`net_fresh_label`). Once the call's copy
  can no longer be observed, the core turns the call's fans into wires to the
  definition's side (see [the architecture](architecture.md)). Without that,
  every call would leave its fans waiting in the definition and the net would
  grow with every call.

Measured with the compiler off, against the combinator alone, on a counting loop:
the net stays at about 2,500 nodes however many calls are made (the combinator's
grows to 3.4 million after 12,800 calls), and 12,800 calls take 2.1 s instead of
98 s, with the time growing in proportion to the calls. The steps are the combinator's: the fan does the same copying, lazily. A
loop whose accumulator is never forced keeps every call's world alive, because
the unevaluated sums are still needed; that is the cost of laziness, not of the
rewrite. `LIN_Y_OFF=1` turns the rewrite off.

### Memory in compiled code

Compiled code has one memory system: every block carries a count, in the word
before it, and compiled code keeps the count exact, in the manner of Perceus.
There is no collector, and nothing is left to the arena the unit releases when
it returns except what the threads were handed (see below). What the compiler
works out from a function's structure is only where counts can be skipped; whether
a block is shared is the count's question, asked at run time.

- **Every value has an owner.** A call or constructor given something its giver
  still needs (a parameter used again, a field of a block that stays, a value
  used twice, a value the callee also reads as a captured variable) is given a
  new reference. Every owned parameter is released where its paths end, and a
  block is freed when its last reference goes.
- **Borrowing.** A parameter a function only reads (takes apart without
  rebuilding in it, reads the fields of, lends on) is borrowed: the caller takes
  no count for the call and the callee releases nothing. This is a fixpoint over
  the unit. A tail call that hands an owned value to a parameter keeps that
  parameter owned, so loops stay loops.
- **Traversed parameters stay borrowed.** A parameter the function recurses on
  through its parts (`(_addc xs ys 0)` passes a field of `b` to `b`) is borrowed
  even if one path hands it on whole to an owner, or hands it a fresh value in a
  tail call. Owned, every step would take a count of the rest and release the
  cell whenever the caller still holds the number. Borrowed, the one path that
  hands it on takes one count, once.
- **Moves.** The last use of a parameter takes its reference. Liveness follows
  the order the emitted code evaluates, including the values each region binds,
  where the emitter binds them. A field consumed once by what is stored back in
  its own slot of a block rebuilt in place is moved, decided at run time, so
  nested updates do not copy every level. A branch that takes apart a block it
  owns moves out the fields it uses once, if on every path it then rebuilds that
  block in place or drops it. A balanced-tree insertion then rebuilds its whole
  path in place. A block dropped after its fields moved out is simply freed.
- **In place by count.** A `match` on a value it consumes (an owned parameter no
  other function reads, or a call's result used once) builds its result in the
  block it took apart: inserting into a tree, mapping over a list and setting an
  array element. The rebuild first checks that the block's count is one, and
  copies it otherwise, so a value built fresh and used once is updated in place
  all the way down while one that is still shared is copied. A copy copies only
  the fields the rebuild keeps. Both forms of
  destination passing work, and drops on a path that ends in a cell with a hole
  run before the call that fills the hole, so the loop stays a loop.
- **Temporaries, locals and fields.** A value built only to be the argument of
  one call that just reads it is freed when that call returns. A value a function
  builds and only lends, and a field of a value it takes apart, are freed where
  each of their paths ends: a loop that computes each state from the last keeps
  one state, not all of them. A value computed inside one operand (a call's
  argument, an arm of a choice) is dropped inside it. One whose path ends where
  it is not in hand is kept in a variable of the function's frame, set wherever
  it is computed, so the drop can still name it.
- **Reads before a move.** A call handed a vector whole that also reads its
  length or an element in another argument moves it once: the reads happen
  before the call runs. A node a path has already evaluated is the same value
  wherever else that path names it.
- **Free lists by size class.** A freed block goes on a list for its size: one
  list per size under 8 words, and one per power of two above that, so the block
  a freed vector leaves serves the next of its class.
- **Unread fields are not computed.** A constructor field that no part of the
  program reads is never evaluated or stored, matching lazy semantics.
- **Threads.** A count is plain arithmetic while one thread alone can see the
  block. What forked tasks, parallel loops and reductions are handed is frozen
  first: never counted again and freed with the unit, so threads reading one
  structure never write to it. A list a parallel map splits among the threads is
  marked shared instead: its counts are negated and from then on atomic, and it
  is freed as it is consumed. A shared block held by a single reference becomes
  local again. A parameter that is read all the way down (no part of it is ever
  given a count) is handed to threads unmarked.

### Owned vectors

`std/array.lin`'s arrays have their own type, `vec a`, and their operations
(`array`, `alen`, `aget`, `aset`, `apush`) are `_op` heads like the arithmetic
operators. On the net, and in any driver that does not know them, their meaning
is a 32-way radix trie, written in Lin. The function compiler keeps a vector as
one flat block, `{length, capacity, elements}`:

- `aget` is a load and `alen` a word.
- `aset` writes in place when the vector's count is one, and copies otherwise.
  The old array is still there for whoever holds it, so the operation is
  persistent, but the copy is paid only when the old array is actually used again.
- `apush` grows the capacity by doubling.

Elements that are data are counted like fields. A vector that crosses between
the net and compiled code, as an argument, a result or a field of either, is
converted at the edge. Coming in, the trie it is on the net is walked into one
flat block. Going out, the block is built back as the trie, with `array`'s
depth and its slots past the length holding 0 (the operations never read them).
The unit keeps its flat vectors either way.

Blocks built and freed on one thread. What is not freed is what threads were
handed, frozen, and goes with the unit:

| Benchmark | Built | Freed |
|-----------|------:|------:|
| fannkuch | 12.2M | 12.2M |
| words | 1.9M | 1.9M |
| omap | 518K | 518K |
| knucleotide | 695K | 445K |
| pidigits | 58.9M | 58.9M |

Wall-clock run times in ms (best of five, cached), with the static ownership
analysis this replaced and with counts alone, in one session on a shared
4-core machine (expect ±20%):

| Benchmark | Lin | Lin `-t 1` |
|-----------|-----|------------|
| array | 8 / 9 | 9 / 10 |
| fannkuch | 25 / 23 | 75 / 68 |
| omap | 84 / 103 | 124 / 119 |
| pidigits | 1313 / 1385 | 1305 / 1339 |
| knucleotide | 63 / 76 | 78 / 81 |
| regexredux | 67 / 81 | 83 / 112 |
| bst | 31 / 31 | 28 / 30 |
| words | 16 / 17 | 16 / 16 |
| revcomp | 20 / 19 | 19 / 19 |
| nbody | 21 / 26 | 23 / 24 |
| fasta | 14 / 14 | 15 / 14 |
| binarytrees | 15 / 12 | 22 / 20 |
| spectralnorm | 27 / 34 | 76 / 63 |

What the counted programs still pay for is counts. The regex matcher's pattern
reaches it with a shape the compiler knows only as "data", so it is owned, and
every step takes and releases a count of a piece. `words` and `bst` pay for the
count word itself, which makes a two-word cell three.

### Loops

- **Tail calls** are loops.
- **Destination passing.** A function that builds a cell around its own recursive
  call, such as `map`, `filter` and `append`, is compiled to build the cell first
  and pass the address of the unfinished field to the call. The recursion becomes
  a loop, so a list of any length is processed in constant stack.
- **Indexed fields.** Reading or replacing field `k` of a wide constructor, as the
  array trie does, is one indexed load or store.
- **Fusion.** When the only use of a list one loop builds is another loop that
  takes it apart one cell per step, the two become one loop and the list is
  never built: `(sfoldl add 0 (sfilter even (smap square (srange 0 n))))` runs
  as a single loop over the integers. A cell field the consumer never reads is
  never computed. A consumer whose every step runs a loop of its own (a matrix
  row per cell) keeps its list, so its cells can still be mapped in parallel.

### Sharing

Compiled code computes a shared value once, as the net does.

- **One unit for the whole expression.** Before reduction starts, the compiler
  tries the entire expression the program observes as a single unit, so a value
  used by two calls in it is one node of the unit rather than work repeated in
  two separately compiled calls.
- **Captured values.** A function passed to `map` or `fold` may use a value
  from the enclosing scope. When that value is itself a computation, it is
  evaluated once and handed to the loop as a parameter, not re-evaluated at
  every step.
- **Equal expressions.** Within a unit, two occurrences of the same expression
  are the same node and are computed once.

### Parallelism

- **Independent calls.** When a function's result combines two or more recursive
  calls, as in `fib` or a tree traversal, they run on separate threads down to a
  depth chosen from the thread count.
- **Maps.** A loop that builds a list from a list, each element by a call, is
  split into stretches that run on separate threads; each builds its part of the
  result, and the parts are joined in order.
- **Reductions.** A loop that folds an associative operation over a range
  (wrapping `add` or `mul`, the bitwise operations, `max` and `min`) is split
  into chunks that run on separate threads.
- **Independent loops in one expression.** In the expression the program
  observes, operands that each run a loop run on separate threads; a value they
  share is computed once and handed to each. A loop the expression certainly
  needs starts as soon as the values it reads exist, alongside the loops bound
  before the expression is evaluated.
- **Independent steps.** A loop that folds into an accumulator the result of
  another loop that reads only the step's own state, such as
  `fannkuch`'s fold over the permutations under each rotation, computes every
  step's inner loop on worker threads and folds the results in order. The fold
  is the loop's own, so no associativity is assumed.

All are checked to give the same answer at every thread count
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
reading the standard library, parsing, type checking or analysing it again:
`lin` looks for the record before anything else and loads only the two drivers
a recall needs.

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
| `LIN_FN_NOFUSE=1` | Do not fuse loops (for comparison) |
| `LIN_Y_OFF=1` | Leave declined recursive calls to the Y combinator's own copying (for comparison) |
| `LIN_FN_POISON=1` | Fill freed blocks with an invalid address, so that memory read after it is freed fails instead of working by chance. The whole test suite and every benchmark pass under it |
| `LIN_FN_STATS=1` | Report the blocks each unit built and freed, per size |
| `LIN_FN_LEAKS=1` | Number every allocation site and report, when a unit ends, the sites whose blocks are still held, printing the code around each |
| `LIN_NATIVE_CC` | The C compiler to invoke (default `cc`) |
| `LIN_NATIVE_CACHE` | The cache directory |
| `LIN_NO_CACHE=1` | Do not use the program cache |
| `LIN_CACHE_DEBUG=1` | Report whether a run came from the program cache |

### Checking the compiler against the net

The net is the definition of the language and the function compiler is an
optimiser, so the two must never disagree. `test/fuzz_compile.py` generates
random programs from the shapes the compiler handles -- numeric loops, tree
recursion, lists built, mapped, filtered and folded, datatypes built and taken
apart, records rebuilt in loops, closures and partial application, shared values,
and nested, literal and wildcard patterns -- and requires each one to give the
net's answer compiled, on one thread, and with `LIN_FN_POISON`. One program in
six has a size past the parallel threshold; the net alone is too slow there, so
the compiled program on one thread (which runs no parallel code) is the
reference that the parallel and poisoned runs must match. A seeded slice runs in
the test suite; a long run is

```sh
python3 test/fuzz_compile.py ./lin 500 <seed>
```

### What the compiler leaves to the net

`test/coverage.py` runs programs (by default every `.lin` under `test`,
`examples` and `bench`) and reports, per top-level form, the reduction steps and
time the net still spent after the compiler had its turn, with the reasons the
compiler gave where it declined, ranked by time. It also lists the slowest files
with their wall time split into net, compiling and the rest (reading, checking,
expanding, the C compiler, readback), so a slow front end shows up as well:

```sh
python3 test/coverage.py ./lin [files or directories] [--min-steps N]
```

It is the list of what the compiler should learn next. At the time of writing
the remaining reasons are:

- data handed in from the net whose element shapes the unit's own use does not
  determine, and values left half-duplicated by an earlier form
  (`examples/linden`'s printing forms);
- superpositions: a value left half-duplicated in the net by an earlier form
  (`examples/games/tictactoe.lin`), which the compiler's evaluator does not read;
- `test/regex.lin`'s `Seq` arguments, whose shape is not known when the call is
  made.

## Writing a driver

A driver is a C file that includes `src/lin.h`, exports a registration symbol,
and is compiled to a shared library. `std/drivers/text.c` is the smallest
complete example; `std/drivers/arith.c` shows a driver that folds redexes. The
driver ABI is versioned, and a driver built against a different version is
refused at load (`test/driver_abi.sh`).
