# Standard library

The standard library lives in [`std/`](../std) and is written in Lin. Programs
need no `load` to use it: the prelude (`std/std.lin`) registers every module, and
a module is read the first time one of its names is used. Names are available
unqualified (`smap`) and qualified by module (`seq.smap`).

Arguments are listed in application order: `(str_take k s)` takes the first `k`
characters of `s`.

- [Core types](#core-types): [bool](#bool), [num](#num), [float](#float), [math](#math), [pair](#pair), [maybe](#maybe), [either](#either)
- [Collections](#collections): [list](#list), [sequences](#sequences), [array](#array), [omap](#omap), [hmap](#hmap), [map and set](#map-and-set), [queue](#queue), [stream](#stream), [tree](#tree)
- [Text](#text): [string](#string), [text](#text-driver)
- [System](#system): [io](#io), [ffi](#ffi)
- [Other modules](#other-modules)

## Core types

### bool

`std/bool.lin`

| Name | Meaning |
|------|---------|
| `true`, `false` | The booleans |
| `(not a)`, `(and a b)`, `(or a b)`, `(xor a b)` | Logical operations |

`if` is a core form and needs no library.

### num

`std/num.lin`. Integers are 64-bit and wrap on overflow.

| Name | Meaning |
|------|---------|
| `(add a b)`, `(sub a b)`, `(mul a b)` | Arithmetic |
| `(div a b)`, `(mod a b)` | Truncating division and remainder; zero when `b` is zero |
| `(pow a b)` | `a` to the power `b` |
| `(eq a b)`, `(lt a b)`, `(leq a b)`, `(gt a b)`, `(geq a b)` | Comparison |
| `(band a b)`, `(bor a b)`, `(bxor a b)`, `(shl a k)`, `(shr a k)` | Bitwise operations |
| `(succ n)`, `(pred n)`, `(is_zero n)` | Successor, predecessor, zero test |

The module defines these operations in pure Lin over the bit structure of a
number. The arithmetic driver computes the same functions natively; the two are
held equal by the test suite.

### float

`std/float.lin`. IEEE-754 doubles.

| Name | Meaning |
|------|---------|
| `(fadd a b)`, `(fsub a b)`, `(fmul a b)`, `(fdiv a b)` | Arithmetic |
| `(fneg a)`, `(fabs a)`, `(fsign a)`, `(fmin a b)`, `(fmax a b)`, `(fpow a b)` | |
| `(fsqrt a)`, `(ffloor a)`, `(ffract a)` | Square root, floor, fractional part |
| `(fsin a)`, `(fcos a)`, `(ftan a)`, `(fatan2 y x)` | Trigonometry |
| `(feq a b)`, `(flt a b)`, `(fleq a b)`, `(fgt a b)`, `(fgeq a b)` | Comparison |
| `(i2f n)`, `(f2i x)` | Integer to float; float to integer (floor) |
| `pi`, `e` | Constants |

`std/softfloat.lin` defines the same operations in pure Lin on the bit pattern,
and is what a float means when no driver is loaded.

### math

`std/math.lin`

| Name | Meaning |
|------|---------|
| `(min a b)`, `(max a b)`, `(clamp lo hi x)` | Integer bounds |
| `(sqr x)`, `(cube x)`, `(abs_diff a b)`, `(sign x)` | |
| `(fclamp lo hi x)`, `(lerp a b t)`, `(fsmoothstep e0 e1 x)` | Float interpolation |
| `(deg2rad d)`, `(rad2deg r)` | Angle conversion |

`std/vector.lin` adds 2D and 3D float vectors: `vec2`, `vec3`, component access
(`v3x`, ...), `v3add`, `v3sub`, `v3scale`, `v3dot`, `v3cross`, `v3len`, `v3norm`,
and rotations (`rotate_x`, `rotate_y`, `rotate_z`).

### pair

`std/pair.lin`

| Name | Meaning |
|------|---------|
| `(pair a b)` | A pair |
| `(fst p)`, `(snd p)`, `(swap p)` | Projections |
| `(pair_map f g p)` | Apply `f` to the first component and `g` to the second |
| `(curry f)`, `(uncurry f)` | Convert between a function of a pair and a function of two arguments |

### maybe

`std/maybe.lin`

```scheme
(datatype (Maybe a) (nothing) (just (v a)))
```

| Name | Meaning |
|------|---------|
| `(is_nothing m)`, `(is_just m)` | Tests |
| `(from_maybe d m)` | The value, or `d` for `nothing` |
| `(maybe_map f m)` | Apply `f` inside a `just` |
| `(maybe_bind m f)` | Chain a function returning a `Maybe` |
| `(maybe_or m alt)` | `m` if it is a `just`, otherwise `alt` |

### either

`std/either.lin`

```scheme
(datatype (Either a b) (left (l a)) (right (r b)))
```

| Name | Meaning |
|------|---------|
| `(is_left e)`, `(is_right e)` | Tests |
| `(either f g e)` | Apply `f` to a `left` value or `g` to a `right` value |
| `(either_map f e)`, `(either_bind e f)` | Map or chain over the `right` side |
| `(from_right d e)` | The `right` value, or `d` for a `left` |

## Collections

### list

`std/list.lin`. The built-in list: the encoding string literals use, printed as
`[1 2 3]`.

| Name | Meaning |
|------|---------|
| `nil`, `(cons h t)` | Constructors |
| `(head l)`, `(tail l)`, `(is_empty l)` | Destructors |
| `(nth i l)` | Element `i`, from zero |
| `(first l)` ... `(eighth l)` | Elements by position |
| `(list1 a)` ... `(list5 a b c d e)` | Lists of fixed length |
| `(list_eq a b)` | Equality of integer lists |

For computing with lists, use sequences.

### sequences

`std/seq.lin`. A list as a declared datatype. Functions over it are typed and
compiled; building functions run in constant stack, and a sequence nothing else
holds is transformed in place.

```scheme
(datatype (Seq a) (snil) (scons (h a) (t Seq a)))
```

```scheme
(ssum (sfilter (\x (eq (mod x 2) 0)) (smap (\x (mul x x)) (srange 0 10))))
; => 120
```

| Name | Meaning |
|------|---------|
| `snil`, `(scons h t)` | Constructors |
| `(sempty s)`, `(shead d s)`, `(stail s)` | Emptiness test; head, or `d` if empty; tail |
| `(srange lo hi)` | The integers from `lo` up to but not including `hi` |
| `(slength s)`, `(ssum s)`, `(snth i d s)` | Length; sum; element `i`, or `d` |
| `(smap f s)`, `(sfilter p s)` | Transform; keep elements satisfying `p` |
| `(sfoldl f z s)`, `(sfoldr f z s)` | Left fold `(f acc x)`; right fold `(f x acc)` |
| `(sany p s)`, `(sall p s)` | Whether any, or every, element satisfies `p` |
| `(sappend a b)`, `(sreverse s)` | Concatenate; reverse |
| `(stake k s)`, `(sdrop k s)` | First `k` elements; all but the first `k` |
| `(seq_of_list l)`, `(seq_to_list s)` | Convert from and to the built-in list |

### array

`std/array.lin`. A persistent array with logarithmic (base 32) access, stored as
a 32-way trie. `aset` returns a new array; when the old one is not used again,
the update happens in place.

```scheme
(aget (aset (array 10 0) 3 42) 3)
; => 42
```

| Name | Meaning |
|------|---------|
| `(array n x)` | An array of `n` copies of `x` |
| `aempty` | The empty array |
| `(alen a)` | Length |
| `(aget a i)`, `(aset a i x)` | Read and write element `i` |
| `(apush a x)` | Append one element |
| `(afold f z a)` | Left fold over the elements, `(f acc x)` |
| `(aof_seq s)`, `(ato_seq a)` | Convert from and to a sequence |

### omap

`std/omap.lin`. An ordered map: a red-black tree with logarithmic insert and
lookup, keys kept in order.

```scheme
(imap_get 2 0 (imap_insert 2 "two" omap_empty))
; => "two"
```

| Name | Meaning |
|------|---------|
| `omap_empty` | The empty map |
| `(imap_insert k v m)`, `(imap_get k d m)`, `(imap_has k m)` | Integer keys; `imap_get` returns `d` when `k` is absent |
| `(smap_insert k v m)`, `(smap_get k d m)`, `(smap_has k m)` | String keys |
| `(omap_insert cmp k v m)`, `(omap_get cmp k d m)`, `(omap_has cmp k m)` | Any key type, given a comparison: `(cmp a b)` is negative, zero or positive |
| `(omap_size m)` | Number of entries |
| `(omap_fold f z m)` | Fold in key order, `(f acc key value)` |
| `(omap_keys m)`, `(omap_values m)` | Keys or values, as sequences in key order |

### hmap

`std/hmap.lin`. A hash map from integer keys: a 32-way hash trie, so insert and
lookup take a handful of steps whatever the size. Persistent, and updated in
place when nothing else holds it. Keys are not kept in order.

```scheme
(hmap_get 7 0 (hmap_add 7 1 (hmap_add 7 1 hmap_empty)))
; => 2
```

| Name | Meaning |
|------|---------|
| `hmap_empty` | The empty map |
| `(hmap_insert k v m)` | `k` now maps to `v` |
| `(hmap_get k d m)`, `(hmap_has k m)` | The value at `k`, or `d`; membership |
| `(hmap_alter f d k m)` | The value at `k` becomes `(f old)`, where `old` is `d` when `k` is absent |
| `(hmap_add k n m)` | Add `n` to the count at `k` (absent counts as 0) |
| `(hmap_size m)` | Number of entries |
| `(hmap_fold f z m)` | Fold over the entries, `(f acc key value)`, in no particular order |

Use `omap` when keys must come out in order, `hmap` otherwise.

### map and set

`std/map.lin`, `std/set.lin`. Unbalanced binary search trees over integer keys.
Prefer `omap` for large or adversarial inputs.

| Name | Meaning |
|------|---------|
| `empty_map`, `(map_singleton k v)` | Construction |
| `(map_insert k v m)` | Insert or replace |
| `(map_get k m)` | A `Maybe` of the value |
| `(map_get_or d k m)`, `(map_has k m)` | Value or default; membership |
| `empty_set`, `(set_singleton x)`, `(set_insert x s)`, `(set_member x s)` | Sets |

### queue

`std/queue.lin`. A persistent FIFO queue with amortised constant-time
operations.

| Name | Meaning |
|------|---------|
| `empty_queue`, `(queue_singleton x)`, `(is_empty_queue q)` | |
| `(queue_push x q)` | Add at the back |
| `(queue_peek q)`, `(queue_pop q)` | Front element; the queue without it |

### stream

`std/stream.lin`. Lazy infinite sequences.

| Name | Meaning |
|------|---------|
| `(stream_create s0 next)` | A stream from a seed and a step function |
| `(nats_from n)`, `(repeat x)` | The integers from `n`; a constant stream |
| `(stream_head s)`, `(stream_tail s)` | First element; the rest |
| `(stream_nth0 s)` ... `(stream_nth3 s)` | Elements by position |
| `(stream_take1 s)` ... `(stream_take4 s)` | A prefix, as a list |

### tree

`std/tree.lin`. Binary trees with `leaf`, `node`, accessors (`tree_val`,
`tree_left`, `tree_right`), tests (`is_leaf`, `is_node`) and a fold (`c_fold`).
A program that declares its own `datatype` with constructors named `leaf` and
`node` uses its own.

## Text

### string

`std/string.lin`. A string is a list of byte values.

| Name | Meaning |
|------|---------|
| `(str_length s)`, `(str_is_empty s)` | |
| `(str_concat a b)`, `(str_reverse s)` | |
| `(str_take k s)`, `(str_drop k s)` | First `k` characters; all but the first `k` |
| `(str_eq a b)`, `(str_compare a b)` | Equality; ordering as a negative, zero or positive number |
| `(str_starts_with p s)`, `(str_index_of p s)` | Prefix test; position of `p` in `s`, or -1 |
| `(str_split c s)` | Split at each occurrence of the character code `c`; a sequence of strings |
| `(str_lines s)`, `(str_words s)` | Split at newlines; split at whitespace |
| `(str_join sep ss)` | Join a sequence of strings |
| `(str_of_num n)`, `(str_parse_int s)` | Convert between integers and decimal text |
| `(str_is_digit c)` | Whether a character code is a decimal digit |

### text driver

`std/text.lin` (load it explicitly: `(load "std/text.lin")`). Constant-time
access to a source string through a driver, for programs such as parsers that
index text heavily: `tlen`, `tget`, `tfind`, `tfindany`, `trun`, `tmatch`, `tsub`.

## System

### io

`std/io.lin`. Effects are described by chaining continuations; see
[Input and output](language.md#input-and-output).

| Name | Meaning |
|------|---------|
| `(io_print s k)` | Write `s` to standard output, then `k` |
| `(io_write_to dst s k)` | Write `s` to standard output (1) or standard error (2), then `k` |
| `(io_read k)`, `(io_read_all k)` | Pass a line, or all, of standard input to `k` |
| `(io_file path k)` | Pass a file's contents to `k` |
| `(io_prompt s k)` | Print `s`, then read a line |
| `(io_wait source k)` | Wait on a descriptor, `"!command"`, `"file:path"` or `"sleep:ms"` |
| `io_done` | Finish |
| `(puts s)`, `(putchar c)`, `(fopen path mode)`, `(fclose f)`, `(fgetc f)`, `(fputc c f)` | The C functions of the same names |

### ffi

`std/ffi.lin`

| Name | Meaning |
|------|---------|
| `(ccall name args)` | Call the C function `name` with a list of arguments |
| `(load_lib path)` | Open a shared library |
| `(getenv name)`, `(system command)`, `(exit code)` | The C functions of the same names |

## Other modules

| Module | Contents |
|--------|----------|
| `std/sat.lin` | Boolean formula combinators and witness search (`exists`, `forall`, `probe1` ... `probe5`, `verify1` ... `verify5`) |
| `std/loop.lin` | Iteration by a Church numeral (`loop`, `count`) |
| `std/drivers/*.lin` | Driver loaders; see [Drivers](drivers.md) |
