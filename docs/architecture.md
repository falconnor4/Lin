# Architecture

Lin has two layers. The **core** (`src/`) turns source into an interaction net
and reduces it. **Drivers** (`std/drivers/`) are plugins that reduce parts of a
net faster by other means, and that read results back out. The core defines what
a program means; drivers only change how fast the answer arrives.

This page describes the core. Drivers have [their own page](drivers.md).

## From source to result

```
source text
   │  parse                      src/parse.c
   ▼
terms (lambda, application, let, definitions)
   │  type check                 src/type.c
   │  expand definitions, simplify, optimise
   ▼                             src/main.c, src/compile.c
one closed term per top-level expression
   │  compile                    src/compile.c
   ▼
interaction net
   │  reduce                     src/net.c   (+ drivers)
   ▼
reduced net
   │  read back by type          std/drivers/readback.c
   ▼
printed value
```

| File | Role |
|------|------|
| `src/parse.c` | Reader: S-expressions to terms; `datatype` and `match` to their encodings |
| `src/type.c` | Hindley–Milner inference with nominal datatypes |
| `src/main.c` | Driver of the pipeline: definitions, namespaces, lazy library loading, term simplification, the REPL, `lin build` |
| `src/compile.c` | Term to net; the e-graph optimiser; reading and writing `.line` artifacts |
| `src/net.c` | The net, the rewrite rules, erasure, parallel reduction, the driver interface |
| `src/io.c` | Driver loading, the constructor registry, dispatch to the readback driver |
| `src/goi.c` | A Geometry of Interaction invariant, used as a diagnostic |

## Interaction nets

A net is a graph of nodes with three ports each. One port is *principal*. Two
nodes whose principal ports are wired together form a *redex*, and a redex is the
only place a rewrite can happen.

| Node | Principal port | Other ports | Meaning |
|------|----------------|-------------|---------|
| `LAM` | the function's value | binder, body | A lambda |
| `APP` | the function applied | result, argument | An application |
| `DUP` | the value copied | two copies | Sharing: one value used twice |
| `ERA` | the value discarded | | An unused value |

A fifth tag, `ROOT`, marks where the result is observed. It takes part in no rule.

There are no other node kinds. In particular there is no node for a number, a
string or a constructor, and no node carries a name or a payload.

### Rules

| Redex | Rewrite |
|-------|---------|
| `LAM` × `APP` | Beta reduction: the argument is wired to the binder and the body to the result |
| `DUP` × `DUP`, same label | The two cancel, and their copies are wired pairwise |
| `DUP` × `DUP`, different labels | They pass through each other |
| `DUP` × `LAM` or `APP` | The node is copied, and the duplication moves to its other ports |
| `ERA` × any node | The node is removed, and erasers are placed on its other ports |

Every rule is local: it reads and writes only the two nodes of the redex and the
wires at their ports. That locality is what makes parallel reduction safe.

### Sharing and labels

A `DUP` node carries a *label*, a position in the program's scope structure, so
that two duplications that belong to the same act of sharing cancel when they
meet and unrelated ones pass through each other. Labels are interned in a trie:
comparing two labels is an integer comparison, however deeply nested the scopes.

Because a shared value is one piece of net, work done on it is done once for all
of its users. A redex and every copy that would arise from it are reduced in a
single step; `test/optimality.py` checks the step counts this implies.

A `let` binds one net that every use shares, including uses inside its own value.
A recursive definition is therefore a cycle in the net, not an unrolling.

### Demand

Reduction is driven by what the observed result needs. A redex fires only if the
result depends on it, so an unused argument, the branch of an `if` not taken, and
the tail of an infinite structure are never computed.

## Data as net structure

Everything a program manipulates is built from the four node kinds.

| Value | Encoding |
|-------|----------|
| Function | Lambda |
| Datatype value | Scott encoding: a constructor is a function that selects its own branch of a `match` |
| Boolean | A two-constructor datatype |
| Integer | A chain of bit cells, least significant first, ended by a sign terminal |
| Float | An integer holding the IEEE-754 bit pattern |
| List, string | Cells of head and tail; a string is a list of byte values |

Since no node is labelled, a few structural conventions let other components
recognise what a piece of net means:

- A primitive operation is a lambda whose binder is named `_op`, applied to an
  operation code. Its body is the operation's definition in pure Lin, so the net
  can always compute it by rewriting alone; a driver that recognises the shape may
  compute it directly instead.
- A constructor and a `match` branch each carry a marker that states which
  constructor of which datatype they are. The compiler front end records each
  datatype's constructors in a registry that drivers and the printer consult.

These conventions are what allow Lin to run with no standard library and no
drivers at all (`test/no_std.sh`): the meaning is always in the net.

## Memory

Lin has no garbage collector and no reference counts.

- A rewrite frees the two nodes it consumes.
- Where the compiler sees a value that is not used, it wires an `ERA` node to it.
  An eraser consumes whatever it reaches and passes erasure on, so unused
  structure is removed by the same kind of local rule as everything else.
- Freed node slots are reused at safe points only, so an index held by a reducer
  never comes to name a different node.

`LIN_LEAKCHECK=1 lin -b file.lin` reports what remains reachable from a result.

## Parallel reduction

Redexes whose neighbourhoods do not overlap cannot interfere, because rules are
local. The reducer repeatedly collects a set of such redexes, a *wave*, and fires
them together across worker threads, without locks on the net.

Drivers add parallelism of their own. The function compiler runs independent
recursive calls on separate threads and splits loops that fold an associative
operation; see [Drivers](drivers.md#parallelism).

Programs are pure, so the result is the same for any thread count. The test suite
runs programs at several widths and requires identical output.

## Compile-time simplification

Before a term becomes a net it passes through two optional stages:

- An **e-graph optimiser** (`src/compile.c`) that shares common subterms and
  applies rewrite rules. `LIN_NO_EGRAPH=1` disables it.
- **Shrinking** (`src/main.c`), which performs beta reductions that cannot
  duplicate work: a function applied to arguments it uses at most once is inlined.
  `LIN_NO_SHRINK=1` disables it.

Neither changes a program's meaning. Both exist to hand the reducer and the
drivers a smaller net.

## Library loading

The prelude registers every standard-library module without reading it. A
module whose top-level forms only define things is read the first time a program
names one of its definitions, so a program pays for the modules it uses and no
others. `LIN_EAGER_STD=1` reads everything at start-up.

## Artifacts

`lin build file.lin -o file.line` reduces everything that does not depend on
run-time input and writes the remaining net, together with the constructor
registry and the result's type, to a `.line` file. Running the artifact skips
parsing, checking and compilation. A program with no input reduces to its answer
at build time.

## Design rules

The core is kept small and uniform on purpose.

- **No new node kinds.** Anything that could be a node kind is an encoding
  instead.
- **Strategies live in drivers.** The core contains no fast path for arithmetic,
  strings or any particular program shape.
- **The net is the authority.** A driver must compute what the rules would have
  computed, and declines when it cannot.
- **No fixed limits.** A capacity is derived from the data or grows on demand;
  `test/no_caps.py` rejects new hard-coded ceilings.
