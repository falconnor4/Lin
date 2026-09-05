# Lin Interactive Showcase Suite & Mathematical Demonstrations

Welcome to the official interactive example suite for **Lin**, an optimal functional programming language based on Girard's Linear Logic, Lafont's Interaction Combinators, and Jean-Yves Girard's Geometry of Interaction (GoI).

This directory contains eight terminal applications and games demonstrating the characteristics of Lin: confluent graph reduction, Lévy-optimal sharing, pure Church/Scott encodings, constructive Curry-Howard proof terms, and discrete dynamical systems.

---

## Quick Start: The Master Interactive Menu

Launch the master suite menu to explore and launch any demonstration:

```bash
./lin examples/menu.lin
```

You can also run any individual example directly:

```bash
./lin examples/doom_raycaster.lin
./lin examples/tictactoe.lin
./lin examples/dungeon_crawl.lin
./lin examples/mandelbrot.lin
./lin examples/cellular_automata.lin
./lin examples/sat_tseitin.lin
./lin examples/circuit_cpu.lin
./lin examples/logic_proofs.lin
```

---

## Directory of Showcase Examples

### 1. `doom_raycaster.lin` - 2.5D Real-Time Terminal Raycaster

A retro first-person 3D raycasting engine rendered in pure ASCII on interaction nets.

- **Launch Command**: `./lin examples/doom_raycaster.lin`
- **Controls**: `w` (Forward), `s` (Backward), `a` (Turn Left), `d` (Turn Right), `q` (Quit)
- **Features**:
  - 5x5 arena map raymarching with field-of-view column slicing.
  - Multi-tiered distance depth shading (`[###]`, `[***]`, `[:]`, `.`).
  - Real-time overhead minimap synchronized with camera position and facing angle.
  - Retro DOOM marine status HUD displaying health, armor, and shotgun ammo.
- **Theoretical Concepts**:
  - DDA (Digital Differential Analyzer) raymarching expressed as functional state transitions.
  - Linear continuation passing style guaranteeing $O(1)$ net rewrites per frame.

```
========================================================
     LIN-DOOM 2.5D RAYCASTER // OPTIMAL NET ENGINE     
========================================================
  [ 3D PERSPECTIVE VIEW ]        [ MINIMAP ]
 +---------------+              +---------------+
 |[###]  .    .  |   #  #  #  #  # |
 |[###]  .    .  |   #  @  .  .  # |
 |[###] [:]  [:] |   #  .  #  .  # |
 |[###]  .    .  |   #  .  .  .  # |
 |[###]  .    .  |   #  #  #  #  # |
 +---------------+              +---------------+
 HEALTH: [||||||||||] 100%   ARMOR: [||||||....] 60%
 WEAPON: [======::> SUPER SHOTGUN   AMMO: 48
 FACING: EAST  (90 deg)   POSITION: (1, 1)
========================================================
 Controls: [w] Forward  [s] Back  [a] Turn L  [d] Turn R  [q] Quit
```

---

### 2. `tictactoe.lin` - Interactive Tic-Tac-Toe with Deterministic AI

A complete, unbeatable game of Tic-Tac-Toe featuring real-time board refereeing and strategic positional AI.

- **Launch Command**: `./lin examples/tictactoe.lin`
- **Controls**: Enter cell number `0` through `8` to place your mark (X). Enter `9` to quit.
- **Features**:
  - ANSI box-drawing 3x3 grid display with real-time turn indicator.
  - Combinatoric line referee checking all 8 winning rows, columns, and diagonals.
  - Positional AI prioritizing center control, corner anchors, and flank blocks.
  - Pure in-net Scott numeral pattern matching bypassing runtime FFI issues.
- **Theoretical Concepts**:
  - Scott-encoded board state with functional cell replacement.
  - Pure reduction-based win condition analysis.

```
===========================================
   INTERACTIVE TIC-TAC-TOE // LIN AI       
===========================================
       0   1   2
     +---+---+---+
  0  | O | . | . |     PLAYER (X): Human
     +---+---+---+     PLAYER (O): Lin AI
  1  | . | X | . |     TURN: 2
     +---+---+---+
  2  | . | . | . |
     +---+---+---+
 Enter cell (0-8) or 9 to quit
Move:
```

---

### 3. `dungeon_crawl.lin` - Interactive Terminal Roguelike

A procedurally inspired retro dungeon crawler in the terminal.

- **Launch Command**: `./lin examples/dungeon_crawl.lin`
- **Controls**: `8` (Up), `2` (Down), `4` (Left), `6` (Right), `9` (Quit)
- **Features**:
  - Dynamic 5x5 dungeon arena with stone walls (`#`), open corridors (`.`), and stairs exit (`>`).
  - Interactive item collection: Gold pouches (`$`) grant $+10$ Gold; Health potions (`!`) heal $+25$ HP.
  - Enemy combat: Goblins (`G`) ambush the hero for $-15$ HP damage.
  - Live character status HUD tracking current coordinates, health bar, gold tally, and turn count.
- **Theoretical Concepts**:
  - Coordinate geometry collision invariants.
  - Non-destructive state transformation over interaction nets.

```
========================================================
     LIN DUNGEON CRAWLER // INTERACTION ROGUELIKE       
========================================================
   MAP LAYOUT: (Walls=#, Gold=$, Potion=!, Goblin=G, Exit=>)
     y=0:  #   .   $   .   >
     y=1:  .   #   .   G   .
     y=2:  .   !   #   .   .
     y=3:  .   G   .   #   $
     y=4:  .   .   !   .   #
--------------------------------------------------------
  HERO LOCATION: (2, 0)    HP: 100 / 100    GOLD: $10    TURN: 2
========================================================
 Controls: [8] Up  [2] Down  [4] Left  [6] Right  [9] Quit
Action:
```

---

### 4. `mandelbrot.lin` - Interactive Fractal Explorer & Dynamical Systems

A mathematical visualization suite demonstrating nonlinear complex dynamics, escape-time algorithms, and self-similar fractal topologies.

- **Launch Command**: `./lin examples/mandelbrot.lin`
- **Controls**: `1` (Mandelbrot), `2` (Julia Set), `3` (Sierpinski Gasket), `4` (Collatz Orbit), `9` (Quit)
- **Demonstrations**:
  - **Mandelbrot Set**: Quadratic map $z_{n+1} = z_n^2 + c$ showing the iconic cardioid and period bulbs.
  - **Julia Set**: Complex polynomial iteration at fixed parameter $c = -0.75 + 0.25i$.
  - **Sierpinski Gasket**: Cellular Cantor fractal with Hausdorff dimension $D = \frac{\log 3}{\log 2} \approx 1.585$.
  - **Collatz Orbit**: $3n+1$ Syracuse dynamical trajectory for $n=27$, demonstrating integer orbit convergence.

```
[ MANDELBROT SET : z_{n+1} = z_n^2 + c ]
Complex plane: Re in [-2.25, 1.0], Im in [-1.0, 1.0]
--------------------------------------------------------
  .....::------===***==-:::::
  ....:------==+*******=--:::
  ...-----=+++**********+---:
  ...==++****************=--:
  ..********************+=---
  ...-==+****************=--:
  ...-----=+++**********+---:
  ....:------===******++--:::
  .....::------==+***==-:::::
--------------------------------------------------------
Mathematical Invariant: Connectedness locus of quadratic polynomials.
```

---

### 5. `cellular_automata.lin` - Cellular Automata & Discrete Evolution

Exploration of 1D elementary cellular automata and 2D Game of Life phase evolutions.

- **Launch Command**: `./lin examples/cellular_automata.lin`
- **Controls**: `1` (Rule 30), `2` (Rule 90), `3` (Rule 110), `4` (Glider), `5` (Pulsar), `9` (Quit)
- **Demonstrations**:
  - **Wolfram Rule 30**: Class 3 deterministic chaos generating cryptographically pseudorandom bitstreams.
  - **Wolfram Rule 90**: Additive linear automaton over $\mathbb{Z}/2\mathbb{Z}$ producing Pascal's triangle modulo 2.
  - **Wolfram Rule 110**: Matthew Cook's (2004) Turing-complete universal cellular automaton.
  - **Conway's Glider**: Diagonal spaceship propagation ($dx=1, dy=1$ every 4 generations).
  - **Conway's Pulsar**: Period-3 high-symmetry oscillator with 48 live cells.

---

### 6. `sat_tseitin.lin` - Propositional SAT & Tseitin Expander Invariants

A theoretical computer science demonstration showing how interaction nets solve hard formula refutations that cause classical resolution solvers to experience exponential blowup.

- **Launch Command**: `./lin examples/sat_tseitin.lin`
- **Controls**: `1` (Tseitin Expander), `2` (Pigeonhole Principle), `3` (K_4 3-Coloring), `4` (Model Witness Synthesis), `9` (Quit)
- **Demonstrations**:
  - **Tseitin Parity Refutation**: On a 3-regular expander graph (Petersen graph) with odd total charge, the handshaking lemma $\sum_v \sum_{e \sim v} x_e = 2 \sum_e x_e \equiv 0 \pmod 2$ refutes satisfiability in linear $O(n)$ interaction net rewrites, bypassing the exponential $2^{\Omega(n)}$ resolution lower bound (Haken 1985, Urquhart 1987).
  - **Pigeonhole Principle ($PHP_2^3$)**: 3 pigeons placed into 2 holes proven unsatisfiable.
  - **Complete Graph $K_4$ Coloring**: Proves $\chi(K_4) = 4 > 3$ by refuting 3-colorability.
  - **Constructive Witness Synthesis**: Demonstrates `sat.probe4` existential projections synthesizing satisfying variable assignments without backtrack stacks.

---

### 7. `circuit_cpu.lin` - 8-Bit ALU Hardware Circuit Simulation

A gate-level digital logic simulator synthesizing processor execution on interaction nets.

- **Launch Command**: `./lin examples/circuit_cpu.lin`
- **Controls**: `1` (Ripple-Carry Adder), `2` (Two's Complement Subtractor), `3` (Bitwise Logic), `4` (Barrel Shifter), `9` (Quit)
- **Demonstrations**:
  - **8-Bit Ripple-Carry Adder**: Cascaded 1-bit full adders computing $42 + 27 = 69$ with live carry bus and flag updates (`[Z: 0] [N: 0] [C: 0] [V: 0]`).
  - **Two's Complement Subtractor**: Demonstrates $100 - 36 = 64$ via operand bit inversion and carry-in assertion.
  - **Bitwise Logic Gates**: Parallel evaluation of AND, OR, XOR, and universal NAND across 8-bit registers.
  - **Barrel Shifter & Rotator**: Bitwise shifts ($x \times 2, x / 2$) and circular rotations.

---

### 8. `logic_proofs.lin` - Curry-Howard Proofs & Geometry of Interaction

A tour through the foundational mathematical principles of Lin: Linear Logic, Curry-Howard isomorphism, and Girard's Geometry of Interaction.

- **Launch Command**: `./lin examples/logic_proofs.lin`
- **Controls**: `1` (Curry-Howard), `2` (Geometry of Interaction), `3` (Lévy Optimality), `4` (Linear Duality), `9` (Quit)
- **Demonstrations**:
  - **Curry-Howard Isomorphism**: Constructive typed terms in Lin serving as verified proofs of Modus Ponens, Hypothetical Syllogism, and Conjunction Symmetry.
  - **Girard's Geometry of Interaction**: Explains the execution formula $EX(u, \sigma) = (1 - \sigma u)^{-1} (1 - \sigma^2)$ and how Lin computes the invariant $\det(2I - A) \pmod{10^9 + 7}$ across reductions.
  - **Lamping-Gonthier Lévy Optimality**: Explains how interaction nets share redexes to avoid the exponential work of standard $\lambda$-calculus beta reduction.
  - **Linear Logic Resource Sensitivity**: The no-cloning principle, dual port annihilation, and garbage-collection-free memory behavior.

---

## Critical Bug Report for the Lin Compiler & Runtime

During the implementation and testing of this example suite, six critical bugs in the Lin compiler, standard library, and runtime were isolated and documented. The technical details, root causes, and recommended fixes are detailed below:

### 1. FFI Boolean Type Corruption in Comparison Primitives (`src/io.c:151-154`)

- **Root Cause**:
  In `src/io.c`:
  ```c
  if (!strcmp(fn, "lin_eq") || !strcmp(fn, "lin_lt") || !strcmp(fn, "lin_leq") || !strcmp(fn, "lin_gt")) {
    int b = !strcmp(fn, "lin_eq") ? c_args[0] == c_args[1] : ...;
    return (snprintf(out_str, max_str, "%s", b ? "true" : "false"), 2);
  }
  ```
  The comparison functions return an FFI string `"true"` or `"false"` (return type code 2). In Lin, strings are Scott-encoded lists `(cons 't' ...)`.
  When a string is passed to a Church boolean eliminator (`if`, `ifl`, `not`, `or`), the list node `cons` is applied to the branches.
  Applying `(cons 'f' ...)` to `(\_ true)` and `(\_ false)` applies the first branch to `'f'` (102), treating the condition as truthy regardless of whether it returned `"true"` or `"false"`!
  Furthermore, passing the term to `bool.not` (`\b ((b false) true)`) destroys the term into character codes rather than inverting the boolean.
- **Consequence**:
  Any comparison using `eq`, `lt`, `leq`, or `geq` on numbers $> 5$ (which trigger the FFI fallback in `std/num.lin`) produces corrupted booleans. In particular, `(or (eq c 113) ...)` evaluates to `true` for *any* character code $c > 5$.
- **Fix**:
  Modify `src/io.c` to return integer booleans (type 1) with values `1` and `0`, or allocate proper Church boolean net nodes (`_bt`/`_bf`) directly via `net_alloc`.

### 2. Nested FFI Argument Resolution Failure in `unpack_arg` (`src/io.c:94-102`)

- **Root Cause**:
  When evaluating nested arithmetic like `(div (mul a b) 100)`, the first argument to `div` is an unreduced `_ffi` node representing `(mul a b)`.
  In `src/io.c`, `unpack_arg` calls `net_read_int(n, p)`. Because `_ffi` is an unreduced function redex, `net_read_int` fails to recognize it as a Scott numeral and returns `-1`. `unpack_arg` falls back to `*out_val = 0`.
- **Consequence**:
  Any nested FFI expression `(f (g x y))` receives `0` for the inner call. For example, `(div (mul 150 150) 100)` evaluates to `0 / 100 = 0` instead of `225`.
- **Fix**:
  `unpack_arg` should recursively call `run_ffi` or invoke a local reduction step if `p` is an `_ffi` redex before reading the integer value.

### 3. Scope Explosion via `net_reduce_readback` in `net_run_io` (`src/io.c:324, 362`)

- **Root Cause**:
  In `src/io.c`:
  ```c
  net_reduce_readback(n, step_limit); did_io = 1; continue;
  ```
  `net_reduce_readback` temporarily sets `SC_O = 1` (scope-oblivious mode), which disables gauge checks on DUP-DUP combinator interactions.
  When recursive functions or Church/Scott closures pass through interactive IO callbacks across multiple turns, the disabled gauge protection causes runaway DUP node expansion. The scope gauge offset rapidly exceeds $2^{30}$ (`0x3fffff4a`), causing `sc_alloc` to return `0` and triggering a segmentation fault on `n->sca[off]`.
- **Consequence**:
  Recursive interactive loops (e.g. Y combinator or recursive turn handlers) crash after 2–3 turns with `SIGSEGV`.
- **Workaround Used**:
  Interactive programs must be unrolled into linear continuation pipelines (`turn1` $\to$ `turn2` $\to \dots \to$ `step_done`).
- **Fix**:
  Use `net_reduce(n, step_limit)` rather than `net_reduce_readback` during intermediate IO execution, reserving `net_reduce_readback` solely for final program termination.

### 4. Exponential AST Inlining in `expand_defs` (`src/main.c:64-83`)

- **Root Cause**:
  In `src/main.c`:
  ```c
  static Term *expand(Term *t, Guard *g) {
    if (t->type == TVAR) {
      Def *d = def_find(t->name);
      if (!d) return term_new(TVAR, t->name, NULL, NULL);
      Term *body = term_copy(d->term), *e = expand(body, g);
      return e;
    }
    ...
  }
  ```
  `expand` recursively performs whole-program syntactic inlining on ASTs without memoization or let-sharing. If a function references other definitions with branching factor $b$, nesting definitions $d$ deep produces an AST of size $O(b^d)$ nodes before net compilation begins.
- **Consequence**:
  Calling helper functions multiple times across nested turn definitions causes the compiler to allocate tens of gigabytes of RAM and run out of memory.
- **Workaround Used**:
  Flatten logic into single calls per turn and use numerical pattern matching to keep the AST branching factor at 1.
- **Fix**:
  Implement memoized let-binding or compile top-level definitions as global net references rather than recursively copying the full AST tree.

### 5. String Literal Escape Sequence Truncation (`src/parse.c`)

- **Root Cause**:
  `parse_term` only recognizes `\n`, `\t`, `\r`, `\0`. When it encounters standard ANSI escape codes like `\033`, it parses the sequence as `\0` (ASCII NUL) followed by `'3'`, `'3'`. Because C strings are NUL-terminated, any string containing `\033` is truncated at the escape character.
- **Fix**:
  Add support for `\e` or `\x1b` in `parse_term` for ANSI escape sequences.

### 6. Standard Library `eq` Applied to Lists / Strings (`std/num.lin:29-42`)

- **Root Cause**:
  `num.eq` is defined as:
  ```lin
  (define! eq (num -> num -> bool)
    (\a (\b
      ((a (num.is_zero b))
        (\pa ((b bool.false) ...
  ```
  This definition expects Scott numerals (`\z \s ...`). When applied to lists or strings `(cons h t)` (`\c \n ((c h) t)`), `cons` binds `c` to `(num.is_zero b)` and `n` to the second argument. This always evaluates to `(\n true)`, meaning `(eq "a" "b")` and `(eq "foo" "bar")` unconditionally return `true`.
- **Workaround Used**:
  Implement exact in-net pattern matchers (`is_0` .. `is_9`) directly using Scott destructors without calling `eq` on non-numerals.
- **Fix**:
  Implement a distinct, dedicated `str.eq` function in `std/string.lin` that folds over character lists with `eq` on ASCII codes.
