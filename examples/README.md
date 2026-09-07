# Lin Interactive Showcase Suite & Mathematical Demonstrations

Welcome to the interactive demonstration and showcase suite for **Lin**, an optimal functional programming language based on Girard's Linear Logic, Yves Lafont's Interaction Combinators, and Jean-Yves Girard's Geometry of Interaction (GoI).

This directory contains ten terminal applications, simulations, and mathematical demonstrations illustrating the core properties of the Lin runtime: confluent graph reduction, Lévy-optimal sharing, pure Scott and Church data encodings, constructive Curry-Howard proof terms, and discrete dynamical systems.

---

## Quick Start: The Master Interactive Menu

Launch the master interactive menu to browse and execute the demonstration suite:

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
./lin examples/repl_calc.lin
./lin examples/life.lin
```

---

## Directory of Showcase Examples

### 1. `doom_raycaster.lin` - 2.5D Real-Time Terminal Raycaster

A first-person 3D raycasting engine rendered in pure ASCII over interaction nets.

- **Launch Command**: `./lin examples/doom_raycaster.lin`
- **Controls**: `w` (Forward), `s` (Backward), `a` (Turn Left), `d` (Turn Right), `q` (Quit)
- **Key Features**:
  - 5x5 arena map raymarching with field-of-view column slicing.
  - Multi-tiered distance depth shading (`[###]`, `[***]`, `[:]`, `.`).
  - Real-time overhead minimap synchronized with camera position and facing angle.
  - Classic marine status HUD displaying health, armor, and shotgun ammo.
- **Theoretical Foundations**:
  - Digital Differential Analyzer (DDA) raymarching expressed as functional state transitions.
  - Linear Continuation-Passing Style (CPS) guaranteeing deterministic net rewrites per frame.

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

A complete game of Tic-Tac-Toe featuring real-time board refereeing and strategic positional AI.

- **Launch Command**: `./lin examples/tictactoe.lin`
- **Controls**: Enter cell number `0` through `8` to place your mark (X). Enter `9` to quit.
- **Key Features**:
  - ANSI box-drawing 3x3 grid display with real-time turn indicator.
  - Combinatoric line referee checking all 8 winning rows, columns, and diagonals.
  - Positional AI prioritizing center control, corner anchors, and flank blocks.
  - Pure in-net Scott numeral pattern matching with constant-time evaluation.
- **Theoretical Foundations**:
  - Scott-encoded 9-cell board state with functional cell replacement.
  - Confluent reduction-based win condition analysis without mutable state.

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
- **Key Features**:
  - Dynamic 5x5 dungeon arena with stone walls (`#`), open corridors (`.`), and stairs exit (`>`).
  - Interactive item collection: Gold pouches (`$`) grant $+10$ Gold; Health potions (`!`) heal $+25$ HP.
  - Enemy combat: Goblins (`G`) ambush the hero for $-15$ HP damage.
  - Live character status HUD tracking current coordinates, health bar, gold tally, and turn count.
- **Theoretical Foundations**:
  - Coordinate geometry collision invariants.
  - Non-destructive persistent state transformation over interaction nets.

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
- **Key Demonstrations**:
  - **Mandelbrot Set**: Quadratic polynomial map $z_{n+1} = z_n^2 + c$ showing the iconic cardioid and period bulbs.
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
- **Key Demonstrations**:
  - **Wolfram Rule 30**: Class 3 deterministic chaos generating pseudorandom bit patterns.
  - **Wolfram Rule 90**: Additive linear automaton over $\mathbb{Z}/2\mathbb{Z}$ producing Pascal's triangle modulo 2.
  - **Wolfram Rule 110**: Matthew Cook's (2004) Turing-complete universal cellular automaton.
  - **Conway's Glider**: Diagonal spaceship propagation ($dx=1, dy=1$ every 4 generations).
  - **Conway's Pulsar**: Period-3 high-symmetry oscillator with 48 live cells.

---

### 6. `sat_tseitin.lin` - Propositional SAT & Tseitin Expander Invariants

A theoretical computer science demonstration showing how interaction nets evaluate hard formula refutations that cause classical resolution solvers to experience exponential blowup.

- **Launch Command**: `./lin examples/sat_tseitin.lin`
- **Controls**: `1` (Tseitin Expander), `2` (Pigeonhole Principle), `3` (K_4 3-Coloring), `4` (Model Witness Synthesis), `9` (Quit)
- **Key Demonstrations**:
  - **Tseitin Parity Refutation**: On a 3-regular expander graph (Petersen graph) with odd total charge, the handshaking lemma $\sum_v \sum_{e \sim v} x_e = 2 \sum_e x_e \equiv 0 \pmod 2$ refutes satisfiability in linear $O(n)$ interaction net rewrites, bypassing the exponential $2^{\Omega(n)}$ resolution lower bound (Haken 1985, Urquhart 1987).
  - **Pigeonhole Principle ($PHP_2^3$)**: 3 pigeons placed into 2 holes proven unsatisfiable.
  - **Complete Graph $K_4$ Coloring**: Proves $\chi(K_4) = 4 > 3$ by refuting 3-colorability.
  - **Constructive Witness Synthesis**: Demonstrates `sat.probe4` existential projections synthesizing satisfying variable assignments without backtrack stacks.

---

### 7. `circuit_cpu.lin` - 8-Bit ALU Hardware Circuit Simulation

A gate-level digital logic simulator synthesizing processor execution on interaction nets.

- **Launch Command**: `./lin examples/circuit_cpu.lin`
- **Controls**: `1` (Ripple-Carry Adder), `2` (Two's Complement Subtractor), `3` (Bitwise Logic), `4` (Barrel Shifter), `9` (Quit)
- **Key Demonstrations**:
  - **8-Bit Ripple-Carry Adder**: Cascaded 1-bit full adders computing $42 + 27 = 69$ with live carry bus and flag updates (`[Z: 0] [N: 0] [C: 0] [V: 0]`).
  - **Two's Complement Subtractor**: Demonstrates $100 - 36 = 64$ via operand bit inversion and carry-in assertion.
  - **Bitwise Logic Gates**: Parallel evaluation of AND, OR, XOR, and universal NAND across 8-bit registers.
  - **Barrel Shifter & Rotator**: Bitwise shifts ($x \times 2, x / 2$) and circular rotations.

---

### 8. `logic_proofs.lin` - Curry-Howard Proofs & Geometry of Interaction

A tour through the foundational mathematical principles of Lin: Linear Logic, Curry-Howard isomorphism, and Girard's Geometry of Interaction.

- **Launch Command**: `./lin examples/logic_proofs.lin`
- **Controls**: `1` (Curry-Howard), `2` (Geometry of Interaction), `3` (Lévy Optimality), `4` (Linear Duality), `9` (Quit)
- **Key Demonstrations**:
  - **Curry-Howard Isomorphism**: Constructive typed terms in Lin serving as verified proofs of Modus Ponens, Hypothetical Syllogism, and Conjunction Symmetry.
  - **Girard's Geometry of Interaction**: Explains the execution formula $EX(u, \sigma) = (1 - \sigma u)^{-1} (1 - \sigma^2)$ and how Lin computes the invariant $\det(2I - A) \pmod{10^9 + 7}$ across reductions.
  - **Lamping-Gonthier Lévy Optimality**: Explains how interaction nets share redexes to avoid the exponential duplication of standard $\lambda$-calculus beta reduction.
  - **Linear Logic Resource Sensitivity**: The no-cloning principle, dual port annihilation, and garbage-collection-free memory behavior.

---

### 9. `repl_calc.lin` - Interactive RPN Stack Calculator

A functional Reverse Polish Notation (RPN) stack calculator demonstrating pure list state transitions, stack combinators, and multi-turn interactive loops on interaction nets.

- **Launch Command**: `./lin examples/repl_calc.lin`
- **Controls**:
  - `1`: Push 1
  - `2`: Push 2
  - `3`: Push 5
  - `4`: Add (`+`)
  - `5`: Subtract (`-`)
  - `6`: Multiply (`*`)
  - `7`: Exponentiate (`^`)
  - `8`: Duplicate top (`dup`)
  - `9`: Pop / Drop top
  - `0`: Quit
- **Key Features**:
  - Pure Scott list stack representation with $O(1)$ push and pop.
  - Live inspection of stack depth and top elements.
  - Full arithmetic transformations via Scott numeral and FFI operations.

```
============================================================
      LIN INTERACTIVE RPN CALCULATOR // REPL ENGINE         
============================================================
  Stack Depth: 3
  Top Elements: [ 25, 10, 2 ]
------------------------------------------------------------
  [1] Push 1    [2] Push 2    [3] Push 5
  [4] Add (+)   [5] Sub (-)   [6] Mul (*)   [7] Pow (^)
  [8] Dup       [9] Drop      [0] Quit
============================================================
Operation:
```

---

### 10. `life.lin` - Conway's Game of Life Grid Simulator

A 2D toroidal cellular automata simulator with interactive generation advancement and canonical pattern exploration.

- **Launch Command**: `./lin examples/life.lin`
- **Controls**:
  - `1`: Glider (Diagonal spaceship, period 4)
  - `2`: Blinker (3-cell linear oscillator, period 2)
  - `3`: Beacon (Corner-touching block oscillator, period 2)
  - `4`: Toad (6-cell bar oscillator, period 2)
  - `0`: Exit Simulation
- **Key Features**:
  - 5x5 toroidal ASCII grid displays with alive cell markers (`O`) and dead markers (`.`).
  - Live population tracking and generation counter.
  - Discrete dynamical phase transitions modeled purely through linear graph reductions.

```
============================================================
       CONWAY'S GAME OF LIFE // TOROIDAL NET SIMULATOR      
============================================================
  Pattern: Glider (Spaceship) | Generation: 1 | Live Cells: 5
------------------------------------------------------------
    .  O  .  .  .
    .  .  O  .  .
    O  O  O  .  .
    .  .  .  .  .
    .  .  .  .  .
============================================================
Next Pattern: [1] Glider  [2] Blinker  [3] Beacon  [4] Toad  [0] Quit
Select:
```

---

## Architectural & Theoretical Foundations

### 1. Confluent Interaction Combinators & Graph Rewriting

Lin programs are compiled into symmetric interaction nets consisting of constructor nodes (e.g., application `@`, abstraction `\`, and duplication `dup`). Computation is performed through local graph rewrites (active pairs connected along their principal ports):

- **Commutation**: When two distinct symbols meet (e.g., duplication of an application), the nodes commute, duplicating the wire topology with zero global synchronization.
- **Annihilation**: When two identical symbols meet at their principal ports, they annihilate, fusing their auxiliary wires in $O(1)$ operations.
- **Confluence**: Reduction is strictly confluent (the Church-Rosser property holds intrinsically); any order of reduction yields the identical normal form.

### 2. Linear Continuation-Passing Style (CPS)

Because interaction nets are resource-conscious and linear (every port must connect to exactly one wire), interactive terminal applications are structured using Linear Continuation-Passing Style:

```lin
(define! turn (State -> a)
  (\state
    (render state
      (io_prompt "Action: " (\input
        (turn (transition state input)))))))
```

Each step consumes the previous state and yields a continuation wire to the next frame. Memory management is implicit: when an old frame is consumed by the transition function, all unreferenced nodes immediately annihilate, producing automatic, deterministic garbage collection without stop-the-world pauses.

### 3. Data Representation: Scott vs. Church Encodings

Lin leverages both Church and Scott encodings depending on performance requirements:

- **Scott Encodings**: Used for inductive data types such as numerals and lists where constant-time $O(1)$ destructors (pattern matching) are required. A Scott numeral $n$ matches on zero or successor:
  $$\text{Scott}(0) = \lambda z. \lambda s. z$$
  $$\text{Scott}(n+1) = \lambda z. \lambda s. s\ n$$
- **Church Encodings**: Used for functional folding and higher-order iteration where natural numbers act as $n$-fold function applicators:
  $$\text{Church}(n) = \lambda f. \lambda x. f^n(x)$$

### 4. Geometry of Interaction (GoI) Invariant Verification

During net reduction, Lin tracks the topological and algebraic invariants defined by Jean-Yves Girard:

$$EX(u, \sigma) = (1 - \sigma u)^{-1} (1 - \sigma^2)$$

The runtime verifies that the characteristic matrix determinant $\det(2I - A) \pmod{10^9 + 7}$ remains invariant under valid net reduction steps, providing formal verification of graph consistency.

---

## Compilation, Profiling & Standalone Execution

### Interpreted Mode

Run any program directly through the Lin runtime:

```bash
./lin path/to/program.lin
```

### Ahead-of-Time (AOT) Bytecode Compilation

Lin can compile source scripts directly into standalone executables packaged with a shebang header:

```bash
./lin build examples/life.lin -o ./life_sim
chmod +x ./life_sim
./life_sim
```

The resulting binary contains the pre-compiled interaction net bytecode and can be distributed or executed independently.

### Benchmark Profiling Mode

To profile graph reduction steps, memory allocation, and verify Geometry of Interaction matrix determinants, pass the `-b` flag:

```bash
./lin -b examples/mandelbrot.lin
```

The runtime will output:
- Total interaction net rewrite steps performed.
- Peak active node and wire counts.
- Time spent in compilation vs. graph reduction.
- GoI matrix determinant check.

---

## Verification & Test Suite

All interactive examples and standard library modules are validated through Lin's formal test harness:

```bash
# Run complete test suite across all 6 tiers (41 test suites, 760 checks)
nix run .#testRunner

# Verify Nix flake derivations and hermetic build checks
nix flake check
```
