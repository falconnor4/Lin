# Bootstrapped Lin Core Engine

A complete, mathematically pure, self-hosted implementation of the Lin interaction calculus core written entirely in Lin. This package serves as an executable formal specification and a drop-in replacement for the core evaluation engine.

---

## Architecture Overview

The bootstrapped core replicates the full compilation, reduction, and readback pipeline of Lin without relying on C-level runtime primitives or driver hooks:

```
S-Expression String / Tokens
         │
         ▼  (parse.lin)
    Term AST
         │
         ▼  (compile.lin)
  Interaction Net (LAM, APP, DUP, ERA, ROOT)
         │
         ▼  (reduce.lin + net.lin)
Normal Form Interaction Net
         │
         ▼  (readback.lin)
    Term AST / Church Value
```

### Module Breakdown

| Module | Responsibility |
|---|---|
| `types.lin` | Fundamental datatypes: 5 canonical IC node tags (`tag_lam`, `tag_app`, `tag_dup`, `tag_era`, `tag_root`), `Port`, `Node`, `NodeList`, `Redex`, `RedexList`, `Term` AST, and `Net`. |
| `net.lin` | Interaction net graph representation, in-place node table manipulation, wire linking, redex detection, and pure interaction rules ($\beta$-reduction, DUP annihilation, DUP commutation, DUP duplication, and erasure). |
| `reduce.lin` | Step-by-step redex scheduler and fuel-bounded/exhaustive net reduction driver (`net_reduce`). |
| `compile.lin` | AST $\to$ Interaction Net compiler. Handles lexical scoping, variable occurrence counting, automatic symmetric `DUP` fan-out trees, and port wiring. |
| `readback.lin` | Reconstructs normal-form AST terms by traversing net wires from the root port, detecting Church numerals, and verifying structural term equality. |
| `parse.lin` | Pure S-expression lexer and recursive descent parser transforming token streams and strings into `Term` ASTs. |
| `lin.lin` | Top-level entry points (`eval_term`, `eval_tokens`, `eval_str`, `eval_num`). |
| `test_bootstrap.lin` | Verification and validation test suite asserting correctness against mathematical oracle specifications. |

---

## Mathematical Interaction Calculus (5 Canonical Nodes)

The bootstrapped core adheres strictly to the symmetric Interaction Calculus with 5 canonical node types:

1. **`LAM`** (Abstraction): Principal port binds the function body; aux 0 is variable binder; aux 1 is the inner term.
2. **`APP`** (Application): Principal port connects to function; aux 0 is argument; aux 1 is continuation / return target.
3. **`DUP`** (Duplication / Sharing): Principal port connects to shared term; aux 0 and aux 1 are duplicate copies; tagged with lexical scope label.
4. **`ERA`** (Erasure / Garbage Collection): Principal port consumes unreferenced terms; annihilates binary nodes recursively.
5. **`ROOT`** (Global Anchor): Principal port holds the net output root.

### Reduction Rules Implemented

- **Beta Reduction (`LAM` $\bowtie$ `APP`)**:
  Wires caller argument into abstraction variable port, and function return port into abstraction body.
- **Duplication Annihilation (`DUP_s` $\bowtie$ `DUP_s`)**:
  When two duplicators of identical scope collide, they annihilate and link their respective ports ($0 \leftrightarrow 0, 1 \leftrightarrow 1$).
- **Duplication Commutation (`DUP_s` $\bowtie$ `DUP_t`, $s \ne t$)**:
  When duplicators of different scopes collide, they commute by duplicating each other.
- **Node Duplication (`DUP` $\bowtie$ Node)**:
  Duplicator clones `LAM` or `APP` nodes and distributes copies across duplicate wires.
- **Erasure Propagation (`ERA` $\bowtie$ Node)**:
  Erasure deletes binary nodes and creates fresh erasers on their auxiliary ports.

---

## Running the Verification Suite

Run the full verification suite directly with the Lin binary:

```bash
./lin examples/bootstrap/test_bootstrap.lin
```

### Verified Test Cases

The test suite validates:
1. **Identity Evaluation**: `((\x x) (\y y)) => (\v0 v0)` via full net compilation, reduction, and readback.
2. **Church Numeral 1 Readback**: `(\f (\x (f x))) => 1`.
3. **Church Numeral 2 Readback**: `(\f (\x (f (f x)))) => 2`.
4. **Token S-Expression Parsing**: `(\x x)` tokenized and parsed into verified AST.
5. **End-to-End Pipeline**: Token stream $\to$ AST $\to$ Net $\to$ Reduction $\to$ Readback $\to$ Term identity verification.

All tests execute concurrently and return `=> true`.
