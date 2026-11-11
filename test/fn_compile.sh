#!/usr/bin/env bash
# ================================================================================
# The function compiler (std/drivers/fn.c) computes what the net computes.
# --------------------------------------------------------------------------------
# Each program runs twice: with the std (fn loaded, so a recursive integer function is
# compiled to C from its own net and the call folded) and with LIN_FN_OFF=1 (the same
# std, the compiler refusing every call), and the answers must be identical.  The
# compiled run must also have COMPILED (LIN_FN_DEBUG reports the fold), so a driver
# that silently declined everything cannot pass.
# usage: test/fn_compile.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
export LIN_NATIVE_CACHE="$TMP/cache"
pass=0; fail=0
prog() {   # name, program text, expected
  printf '%s\n' "$2" > "$TMP/$1.lin"
  a=$(timeout 300 "$LIN_BIN" "$TMP/$1.lin" 2>/dev/null)
  b=$(LIN_FN_OFF=1 timeout 300 "$LIN_BIN" "$TMP/$1.lin" 2>/dev/null)
  folded=$(LIN_FN_DEBUG=1 timeout 300 "$LIN_BIN" "$TMP/$1.lin" 2>&1 >/dev/null | grep -c "folded a call")
  if [ "$a" = "=> $3" ] && [ "$b" = "$a" ] && [ "$folded" -ge 1 ]; then pass=$((pass+1))
  else fail=$((fail+1)); echo "FAIL $1: compiled '$a', net '$b', want '=> $3', folds $folded"; fi
}
prog fib '(define fib (\n (if (lt n 2) n (add (fib (sub n 1)) (fib (sub n 2))))))
(fib 10)' 55
prog sumto '(define sumto (\n (\acc (if (is_zero n) acc (sumto (pred n) (add acc n))))))
(sumto 12 0)' 78
prog gcd '(define gcd (\a (\b (if (eq b 0) a (gcd b (mod a b))))))
(gcd 1071 462)' 21
prog neg '(define f (\n (if (lt n 0) (mul n -1) (sub 0 (f (sub 0 n))))))
(f 7)' -7
prog pow '(define p (\b (\e (if (eq e 0) 1 (mul b (p b (sub e 1)))))))
(p 3 5)' 243
prog wrap '(define w (\n (if (eq n 0) 9223372036854775807 (add (w (sub n 1)) 1))))
(w 1)' -9223372036854775808
prog ifl '(define c (\n (ifl (leq n 1) (\_ 0) (\_ (add 1 (c (ifl (eq (mod n 2) 0) (\_ (div n 2)) (\_ (add (mul 3 n) 1)))))))))
(c 6)' 8
prog calls '(define steps (\n (\acc (if (leq n 1) acc (steps (if (eq (mod n 2) 0) (div n 2) (add (mul 3 n) 1)) (add acc 1))))))
(define best (\i (\m (if (eq i 0) m (best (sub i 1) (if (gt (steps i 0) m) (steps i 0) m))))))
(best 7 0)' 16
# DATA: constructors and `match` compile too -- a datatype's values become words and blocks in C, a match a switch
prog bintree '(datatype Tree (leaf) (node l r))
(define make (\d (if (eq d 0) leaf (node (make (sub d 1)) (make (sub d 1))))))
(define check (\t (match t (leaf 1) ((node l r) (add 1 (add (check l) (check r)))))))
(check (make 6))' 127
prog bst '(datatype T (tip) (bin k l r))
(define ins (\x (\t (match t (tip (bin x tip tip)) ((bin k l r) (if (lt x k) (bin k (ins x l) r) (bin k l (ins x r))))))))
(define build (\i (\t (if (eq i 0) t (build (sub i 1) (ins (mod (mul i 37) 101) t))))))
(define walk (\t (\d (match t (tip 0) ((bin k l r) (add (mul k d) (add (walk l (add d 1)) (walk r (add d 1)))))))))
(walk (build 30 tip) 1)' 7600
# STRUCTURE RESULTS: a call whose value is data is built back into the net from the unit's arena, field kinds
# inferred (numbers, booleans, other datatypes) and shared blocks kept shared
prog dresult '(datatype L (ln) (lc h t))
(define upto (\n (if (eq n 0) ln (lc n (upto (sub n 1))))))
(upto 3)' '(lc 3 (lc 2 (lc 1 ln)))'
prog dmixed '(datatype (P a b) (pr (x a) (y b)))
(datatype (L a) (ln) (lc (h a) (t L a)))
(define pairs (\n (if (eq n 0) ln (lc (pr n (eq (mod n 2) 0)) (pairs (sub n 1))))))
(pairs 2)' '(lc (pr 2 true) (lc (pr 1 false) ln))'
prog dshared '(datatype T (lf) (nd l r))
(define full (\n (if (eq n 0) lf (let ((t (full (sub n 1)))) (nd t t)))))
(full 2)' '(nd (nd lf lf) (nd lf lf))'
prog dhigher '(datatype L (ln) (lc h t))
(define upto (\n (if (eq n 0) ln (lc n (upto (sub n 1))))))
(define lmap (\f (\s (match s (ln ln) ((lc h t) (lc (f h) (lmap f t)))))))
(lmap (\x (mul x 10)) (upto 3))' '(lc 30 (lc 20 (lc 10 ln)))'
# a closure capturing a parameter of the function that builds it: lifted into the specialised copy's parameters
prog lifted '(datatype L (ln) (lc h t))
(define upto (\n (if (eq n 0) ln (lc n (upto (sub n 1))))))
(define lmap (\f (\s (match s (ln ln) ((lc h t) (lc (f h) (lmap f t)))))))
(define lsum (\s (\a (match s (ln a) ((lc h t) (lsum t (add a h)))))))
(define go (\k (\acc (if (eq k 0) acc (go (sub k 1) (add acc (lsum (lmap (\x (mul x k)) (upto 10)) 0)))))))
(go 5 0)' 825
# STRINGS and other cell-encoded lists: the cell encoding is a datatype to the compiler (a block per cell)
prog strlen '(str_length "hello, world")' 12
prog strbuild '(define rep (\n (\acc (if (eq n 0) acc (rep (sub n 1) (cons 97 acc))))))
(str_length (str_concat (rep 30 nil) (rep 20 nil)))' 50
prog strmap '(define up (\s (if (str_is_empty s) s (cons (if (and (geq (head s) 97) (leq (head s) 122)) (sub (head s) 32) (head s)) (up (tail s))))))
(up "hello world")' '"HELLO WORLD"'
prog strint '(str_parse_int "90210")' 90210
# MEMORY: a block a match consumes and nothing else holds goes back to the allocator, so a loop that builds and
# consumes a list each round runs in the memory of one list (measured: 200M cells in 12 MB)
prog freed '(datatype L (ln) (lc h t))
(define upto (\n (if (eq n 0) ln (lc n (upto (sub n 1))))))
(define lsum (\s (\a (match s (ln a) ((lc h t) (lsum t (add a h)))))))
(define go (\k (\acc (if (eq k 0) acc (go (sub k 1) (add acc (lsum (upto 100) 0)))))))
(go 20 0)' 101000
# ...but a block stored twice (node t t) is shared, and is neither freed nor rebuilt in place
prog sharedfree '(datatype T (lf) (nd l r))
(define full (\n (if (eq n 0) lf (let ((t (full (sub n 1)))) (nd t t)))))
(define cnt (\t (match t (lf 1) ((nd l r) (add (cnt l) (cnt r))))))
(cnt (full 10))' 1024
# a function that may not look at its data argument (lazy in Lin, strict in C): still the net's answer
prog lazydata '(datatype S (snil) (scons h t))
(define upto (\n (if (eq n 0) snil (scons n (upto (sub n 1))))))
(define take_sum (\k (\s (if (eq k 0) 0 (match s (snil 0) ((scons h t) (add h (take_sum (sub k 1) t))))))))
(take_sum 5 (upto 100))' 490
# an INFINITE structure, of which a lazy program uses a part: the compiled unit's guard abandons the call and the
# net computes it -- the answer, not a hang
printf '%s\n' '(datatype S (snil) (scons h t))
(define from (\n (scons n (from (add n 1)))))
(define take_sum (\k (\s (if (eq k 0) 0 (match s (snil 0) ((scons h t) (add h (take_sum (sub k 1) t))))))))
(take_sum 5 (from 1))' > "$TMP/inf.lin"
got=$(timeout 120 "$LIN_BIN" "$TMP/inf.lin" 2>/dev/null); guard=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/inf.lin" 2>&1 >/dev/null | grep -c "guard fired")
if [ "$got" = "=> 15" ] && [ "$guard" -ge 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL infinite: got '$got', guard fired $guard time(s)"; fi

# FLOATS are checked against known values only: float operations are FFI calls with no pure-Lin fallback yet,
# so the net alone cannot be the reference for them (it mis-reduces an undispatched float closure).
progc() {
  printf '%s\n' "$2" > "$TMP/$1.lin"
  a=$(timeout 300 "$LIN_BIN" "$TMP/$1.lin" 2>/dev/null)
  folded=$(LIN_FN_DEBUG=1 timeout 300 "$LIN_BIN" "$TMP/$1.lin" 2>&1 >/dev/null | grep -c "folded a call")
  if [ "$a" = "=> $3" ] && [ "$folded" -ge 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $1: compiled '$a', want '=> $3', folds $folded"; fi
}
progc float '(define it (\cr (\ci (\zr (\zi (\k (if (eq k 0) 0 (if (flt 4.0 (fadd (fmul zr zr) (fmul zi zi))) k
  (it cr ci (fadd (fsub (fmul zr zr) (fmul zi zi)) cr) (fadd (fmul 2.0 (fmul zr zi)) ci) (sub k 1))))))))))
(it 0.3 0.6 0.0 0.0 8)' 0
progc floatres '(define h (\x (\k (if (eq k 0) x (h (fmul x 1.5) (sub k 1))))))
(ffloor (h 2.0 4))' 10
# Parallel compiled code (an operation whose two operands both recurse runs them on two threads) must answer
# exactly what one thread does, for every width.
printf '%s\n' '(define fib (\n (if (lt n 2) n (add (fib (sub n 1)) (fib (sub n 2))))))' '(fib 32)' > "$TMP/par.lin"
w1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/par.lin" 2>/dev/null)
for t in 2 3 8; do
  wt=$(timeout 120 "$LIN_BIN" -t $t "$TMP/par.lin" 2>/dev/null)
  if [ "$wt" = "=> 2178309" ] && [ "$wt" = "$w1" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL parallel -t $t: '$wt' vs -t 1 '$w1'"; fi
done
# Parallel REDUCTIONS (a loop folding an associative op, or a max written as a conditional) must answer what
# the sequential loop does at every width, and must have been recognised as reductions.
printf '%s\n' '(define go (\i (\acc (if (eq i 0) acc (go (sub i 1) (add acc (mod (mul i i) 7)))))))' '(go 100000 0)' > "$TMP/red.lin"
printf '%s\n' '(define st (\n (\a (if (leq n 1) a (st (if (eq (band n 1) 0) (shr n 1) (add (mul 3 n) 1)) (add a 1))))))' \
  '(define best (\i (\m (if (eq i 0) m (best (sub i 1) ((\s (if (gt s m) s m)) (st i 0)))))))' '(best 20000 0)' > "$TMP/max.lin"
for f in red max; do
  r1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/$f.lin" 2>/dev/null); r8=$(timeout 120 "$LIN_BIN" -t 8 "$TMP/$f.lin" 2>/dev/null)
  red=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" -t 8 "$TMP/$f.lin" 2>&1 >/dev/null | grep -c "parallel reduction")
  if [ -n "$r1" ] && [ "$r1" = "$r8" ] && [ "$red" -ge 1 ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL reduction $f: -t 1 '$r1' -t 8 '$r8' recognised $red"; fi
done
[ "$(timeout 120 "$LIN_BIN" "$TMP/red.lin" 2>/dev/null)" = "=> 200003" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL reduction value"; }
[ "$(timeout 120 "$LIN_BIN" "$TMP/max.lin" 2>/dev/null)" = "=> 278" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL max-reduction value"; }
sites=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/par.lin" 2>&1 >/dev/null | grep -c "1 parallel site")
[ "$sites" -ge 1 ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL the tree recursion was not compiled with a parallel site"; }
# ONE block given to several calls that each take it apart is not theirs to free: with the term left unshrunk
# the three selectors below share one list, and each must leave it whole for the next.
printf '%s\n' '(v3y (v3scale 2.0 (vec3 1.0 2.0 3.0)))' > "$TMP/shared.lin"
[ "$(LIN_NO_SHRINK=1 timeout 120 "$LIN_BIN" "$TMP/shared.lin" 2>/dev/null)" = "=> 4" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a shared block was consumed"; }
if [ "$fail" -eq 0 ]; then echo "fn_compile: OK ($pass checks: programs compiled from their nets equal the net's own answers, at every thread count)"; else echo "fn_compile: $fail of $((pass+fail)) failed"; fi
exit $fail
