# Language reference

Lin is a pure, lazily evaluated functional language with S-expression syntax.
Functions are curried lambdas, data is declared with `datatype`, and types are
inferred.

Every example on this page is a complete program; the value after `; =>` is what
it prints.

- [Lexical structure](#lexical-structure)
- [Expressions](#expressions)
- [Definitions](#definitions)
- [Numbers](#numbers)
- [Booleans](#booleans)
- [Strings and lists](#strings-and-lists)
- [Datatypes and pattern matching](#datatypes-and-pattern-matching)
- [Types](#types)
- [Evaluation](#evaluation)
- [Modules](#modules)
- [Input and output](#input-and-output)
- [Calling C](#calling-c)
- [How values print](#how-values-print)
- [Limitations](#limitations)

## Lexical structure

A program is a sequence of parenthesised forms. A `;` starts a comment that runs
to the end of the line.

| Token | Examples |
|-------|----------|
| Integer | `42`, `-5` |
| Float | `1.5`, `-0.25` |
| String | `"hello"`, `"tab\there"` |
| Name | `x`, `str_length`, `list.head` |

A name containing a dot is qualified by a namespace: `list.head` is `head` in the
namespace `list`.

## Expressions

### Lambda and application

`(\x body)` is a function of one argument. Functions of several arguments are
nested lambdas, and application is left-associative: `(f a b)` means `((f a) b)`.

```scheme
(define compose (\f (\g (\x (f (g x))))))
((compose (\x (mul x 2)) (\x (add x 1))) 5)
; => 12
```

### Conditionals

`(if c a b)` is a core form. `c` must be a boolean, and only the chosen branch is
evaluated.

```scheme
(if (lt -1 0) 1 2)
; => 1
```

### Local bindings

`(let ((name value) ...) body)` binds names in order; a later binding may use an
earlier one.

```scheme
(let ((x 2) (y (mul x 10))) (add x y))
; => 22
```

## Definitions

`(define name expr)` binds a name for the rest of the program. A definition may
refer to itself, and definitions may refer to each other.

```scheme
(define fact (\n (if (eq n 0) 1 (mul n (fact (sub n 1))))))
(fact 20)
; => 2432902008176640000

(define is_even (\n (if (eq n 0) true (is_odd (sub n 1)))))
(define is_odd (\n (if (eq n 0) false (is_even (sub n 1)))))
(is_even 10)
; => true
```

`(define! name type expr)` also states the definition's type. The stated type is
taken as given rather than checked against the body: it is how the standard
library gives nominal types such as `bool` and `num` to values that are, underneath,
plain lambdas. Ordinary programs should prefer `define` and let the type be
inferred.

```scheme
(define! inc (num -> num) (\x (add x 1)))
(inc 41)
; => 42
```

## Numbers

Integers are 64-bit two's complement and wrap on overflow. Division and remainder
by zero are zero.

```scheme
(sub 3 8)                     ; => -5
(add 9223372036854775807 1)   ; => -9223372036854775808
(div 7 0)                     ; => 0
```

| Operation | Functions |
|-----------|-----------|
| Arithmetic | `add` `sub` `mul` `div` `mod` `pow` |
| Comparison | `eq` `lt` `leq` `gt` `geq` |
| Bitwise | `band` `bor` `bxor` `shl` `shr` |

Floats are IEEE-754 doubles with their own operations. Integer and float
operations do not mix; convert with `i2f` and `f2i`.

```scheme
(fadd 1.5 2.25)         ; => 3.75
(fsqrt 2.0)             ; => 1.41421
(f2i (fmul 2.5 4.0))    ; => 10
```

| Operation | Functions |
|-----------|-----------|
| Arithmetic | `fadd` `fsub` `fmul` `fdiv` `fneg` `fabs` `fmin` `fmax` `fpow` |
| Comparison | `feq` `flt` `fleq` `fgt` `fgeq` |
| Functions | `fsqrt` `ffloor` `ffract` `fsign` `fsin` `fcos` `ftan` `fatan2` |
| Conversion | `i2f` `f2i` |
| Constants | `pi` `e` |

Float arithmetic is strict IEEE: no fused multiply-add, the same results on every
machine.

## Booleans

`true` and `false` have type `bool`. `not`, `and`, `or` and `xor` combine them;
comparisons produce them; `if` consumes them.

## Strings and lists

A list is built from `nil` and `cons`, and read with `head`, `tail` and `is_empty`.
A string literal is a list of character codes.

```scheme
(cons 1 (cons 2 (cons 3 nil)))    ; => [1 2 3]
(str_concat "foo" "bar")          ; => "foobar"
(str_length "hello")              ; => 5
(str_words "the quick brown fox")
; => (scons "the" (scons "quick" (scons "brown" (scons "fox" snil))))
```

String lengths and indices count bytes, so a non-ASCII character counts as more
than one.

For lists that programs compute with, prefer `Seq` from the standard library: it
is a declared datatype, so recursive functions over it are typed and compiled.
See [Standard library](stdlib.md#sequences).

## Datatypes and pattern matching

`datatype` declares a type by its constructors. A constructor with no fields is a
value; a constructor with fields is a function of them.

```scheme
(datatype Shape (circle (r num)) (rect (w num) (h num)) (unit))

(define area (\s (match s
  ((circle r) (mul 3 (mul r r)))
  ((rect w h) (mul w h))
  (unit 0))))

(area (rect 3 4))
; => 12
```

A field is written `(name type)`, or just `name` to leave its type to inference.
A datatype may take type parameters and may refer to itself:

```scheme
(datatype (Tree a) (leaf) (node (v a) (l Tree a) (r Tree a)))

(define size (\t (match t
  (leaf 0)
  ((node v l r) (add 1 (add (size l) (size r)))))))

(size (node 1 (node 2 leaf leaf) leaf))
; => 2
```

`(match value branch ...)` chooses a branch by constructor. A branch is
`(constructor body)` for a constructor without fields, or
`((constructor field ...) body)`, which binds the fields by position. Branches may
appear in any order. Every constructor of the type needs a branch.

## Types

Types are inferred by Hindley–Milner unification, and every top-level form is
checked before it runs.

```scheme
(add 1 true)
; error: type mismatch
```

| Type | Written |
|------|---------|
| Integer | `num` |
| Boolean | `bool` |
| Float | `float` |
| Function | `a -> b` |
| List | `list a` |
| Datatype | `Tree a`, `Maybe num`, ... |

Datatypes are nominal: two types with the same shape but different names are
different types. `:type` in the REPL prints the type of any expression.

## Evaluation

Lin is lazy: a value is computed when something needs it, and at most once however
many places use it. A program can therefore define more than it consumes.

```scheme
(shead 0 (smap (\x (add x 1)) (srange 0 1000000000000)))
; => 1
```

There is no mutation. Updating a structure produces a new one; when nothing else
holds the old one, compiled code performs the update in place, so persistence
costs nothing where it is not used.

Independent subcomputations may run on different threads. Because programs are
pure, the result never depends on the number of threads.

## Modules

A source file can place its definitions in a namespace, and other code can refer
to them by qualified name or open the namespace.

```scheme
(namespace geom)
(define area (\w (\h (mul w h))))
(namespace _)                ; back to the top level

(geom.area 3 4)              ; => 12

(export geom)                ; make the names available unqualified
(area 5 6)                   ; => 30
```

| Form | Meaning |
|------|---------|
| `(namespace n)` | Definitions that follow are named `n.name`; `(namespace _)` returns to the top level |
| `(export n)` | Make the names of `n` available unqualified. Names beginning with `_` are private and are not exported |
| `(open n)` | As `export`, for a namespace defined elsewhere |
| `(load "file.lin")` | Read another source file. A `std/` path names a library module |

The standard library needs no `load`. Each module is read the first time a
program uses one of its names.

## Input and output

A top-level expression's value is printed. Programs that interact with the world
describe their effects as a chain of continuations, built with `std/io.lin`:

```scheme
(io_print "What is your name? "
  (io_read (\name
    (io_print (str_concat "Hello, " name) io_done))))
```

| Function | Meaning |
|----------|---------|
| `(io_print s k)` | Write the string `s`, then continue with `k` |
| `(io_read k)` | Read a line from standard input and pass it to `k` |
| `(io_read_all k)` | Read all of standard input and pass it to `k` |
| `(io_file path k)` | Read the file at `path` and pass its contents to `k` |
| `(io_write_to dst s k)` | Write `s` to standard output (`dst` 1) or standard error (`dst` 2), then continue with `k` |
| `(io_wait source k)` | Wait for a result from a file descriptor, a command (`"!cmd"`), a file (`"file:path"`) or a timer (`"sleep:ms"`) |
| `io_done` | Finish |

## Calling C

`(ccall "name" args)` calls a C function by name with a list of arguments.
`load_lib` opens a shared library first if the function is not already loaded.

```scheme
(ccall "atoi" (cons "42" nil))
; => 42
```

See [`std/ffi.lin`](../std/ffi.lin) and
[`examples/systems-ffi/`](../examples/systems-ffi).

## How values print

A result is printed according to its type:

| Value | Printed as |
|-------|------------|
| Integer, float | `42`, `3.75` |
| Boolean | `true`, `false` |
| String | `"hello"` |
| List | `[1 2 3]`, `["a" "b"]` |
| Datatype value | Its constructors by name: `(node 1 leaf leaf)` |
| Function | A lambda term: `(\a a)` |

## Limitations

- A `match` that omits a constructor is not rejected; it evaluates to a function
  awaiting the missing branch.
- Patterns bind fields only: there are no nested patterns, literals in patterns,
  wildcards or guards.
- `define!` annotations are trusted, not checked.
- There are no type classes or traits: integer and float operations have
  different names, and a container's element operations are passed explicitly
  (see `omap_insert`).
- There are no records; a datatype's fields are positional.
- Type errors report the kind of error but not its location.
