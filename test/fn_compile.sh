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
# DESTINATION PASSING: a recursion that builds a cell around its own call is a loop, so a list far deeper than
# any stack is mapped, filtered and appended -- and the answers are what the short lists give.
printf '%s\n' '(ssum (sfilter (\x (eq (mod x 3) 0)) (smap (\x (add x 1)) (sappend (srange 0 3000000) (srange 0 3000000)))))' \
  '(slength (stake 2500000 (srange 0 3000000)))' '(ssum (smap (\x (mul x 2)) (srange 0 10)))' > "$TMP/dp.lin"
dp=$(timeout 120 "$LIN_BIN" "$TMP/dp.lin" 2>/dev/null | tr '\n' ' ')
[ "$dp" = "=> 3000003000000 => 2500000 => 90 " ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL destination passing: '$dp'"; }
dn=$(LIN_FN_DEBUG=2 timeout 120 "$LIN_BIN" "$TMP/dp.lin" 2>&1 >/dev/null | grep -c "_d(long \*dst")
[ "$dn" -ge 1 ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL no destination-passing form was written"; }
# A CAPTURED VARIABLE is held by the inner function for every step of its loop: in the n-body benchmark the list
# of bodies is read by each body's update while the map over that same list runs, so the map must not rebuild
# in it and the fold must not free it.  (It did both: bodies saw their neighbours' new positions, and the unit
# crashed.)  The answer after 1,000 steps is the one the C program gives.
sed 's/(run 200000 /(run 1000 /' "$ROOT/bench/nbody.lin" > "$TMP/cap.lin"
cap=$(timeout 120 "$LIN_BIN" "$TMP/cap.lin" 2>/dev/null)
[ "$cap" = "=> -169301064" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a captured list was taken apart: n-body after 1,000 steps is '$cap'"; }
# The same program states three more things the compiler must do, each named in its report: the fold over the
# bodies starts from a COPY of a body and rebuilds in it; the list a step was computed from is DROPPED once the
# step is built (the eraser, in compiled code); and the simulation the energy is read from is computed ONCE,
# though the energy's inner loop names it at every body.
LIN_FN_DEBUG=2 timeout 120 "$LIN_BIN" "$TMP/cap.lin" >/dev/null 2>"$TMP/cap.err"
for what in "is given a copy" "is dropped after its call" "is computed once"; do
  grep -q "$what" "$TMP/cap.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL n-body: no parameter '$what'"; }
done
# ...and dropping keeps a long run in a few blocks: thirty million steps of a two-body state allocate what one
# step does (kept, they would be gigabytes; the unit's memory guard must not fire).
printf '%s\n' '(datatype P (p (x num) (v num)))' \
  '(define nudge (\\b (\\o (match b ((p x v) (match o ((p ox ov) (p x (add v (sub ox x))))))))))' \
  '(define step (\\bs (smap (\\b (match (sfoldl nudge b bs) ((p x v) (p (add x v) v)))) bs)))' \
  '(define run (\\n (\\bs (if (eq n 0) bs (run (sub n 1) (step bs))))))' \
  '(define total (\\bs (sfoldl (\\a (\\b (match b ((p x v) (add a (band (add x v) 255)))))) 0 bs)))' \
  '(total (run 30000000 (scons (p 0 0) (scons (p 7 1) snil))))' > "$TMP/long.lin"
lg=$(LIN_FN_DEBUG=1 timeout 300 "$LIN_BIN" "$TMP/long.lin" 2>"$TMP/long.err")
[ -n "$lg" ] && ! grep -q "guard fired" "$TMP/long.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a long stepping loop did not stay in bounded memory: '$lg'"; }
# A FUNCTION WHOSE BODY IS A LITERAL is a function: `(\i 7)` is three lambdas deep, as a numeral's last cell is,
# and read as data it was passed in as a list and then applied.
printf '%s\n' '(ssum (smap (\i 7) (srange 0 5)))' > "$TMP/lit.lin"
lit=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/lit.lin" 2>"$TMP/lit.err")
[ "$lit" = "=> 35" ] && ! grep -q declined "$TMP/lit.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a literal-bodied function: '$lit'"; }
# TWO CLOSURES OF ONE LAMBDA with different captured values are two functions.  (After a speculative read failed,
# a function's number was given to another, and a remembered value still named the first: the four nested maps
# below became two, each defined by the other.)  And a captured value is COMPUTED ONCE, as the net shares it:
# the captured list is a parameter of the loop, not an expression evaluated at every step.
printf '%s\n' '(define row (\i (\u (\acc (match u (snil acc) ((scons h t) (row i t (add acc (mul i h)))))))))' \
  '(define av (\n (\u (smap (\i (row i u 0)) (srange 0 n)))))' '(define atav (\n (\u (av n (av n u)))))' \
  '(ssum (atav 3 (atav 3 (srange 0 3))))' > "$TMP/nest.lin"
nest=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/nest.lin" 2>"$TMP/nest.err")
[ "$nest" = "=> 243" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL nested closures of one lambda: '$nest'"; }
grep -q "computed once" "$TMP/nest.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a captured value was not made a parameter"; }
# A MAP IN PARALLEL: a loop that builds a list from a list, each cell by a call, does stretches of the list at
# once and joins them.  The list it builds must be the one a single thread builds -- same cells, same order --
# at every width, uneven splits included (a list of 1,003 over 3, 7 and 8 threads), and through a filter, which
# drops cells at the joins too.
printf '%s\n' '(define tri (\n (\a (if (eq n 0) a (tri (sub n 1) (add a n))))))' \
  '(define weigh (\s (\i (\a (match s (snil a) ((scons h t) (weigh t (add i 1) (add a (mul h i)))))))))' \
  '(weigh (smap (\x (tri (mod x 50) x)) (srange 0 1003)) 1 0)' \
  '(weigh (sfilter (\x (eq (mod (tri (mod x 7) 0) 2) 0)) (srange 0 1003)) 1 0)' > "$TMP/pm.lin"
pm1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/pm.lin" 2>/dev/null)
pmok=1; for t in 2 3 7 8; do [ "$(timeout 120 "$LIN_BIN" -t $t "$TMP/pm.lin" 2>/dev/null)" = "$pm1" ] || pmok=0; done
sed 's/(srange 0 1003)/(srange 0 40)/' "$TMP/pm.lin" > "$TMP/pms.lin"   # (the net's own answer, on a list it can walk in time)
pmn=$(LIN_FN_OFF=1 timeout 300 "$LIN_BIN" "$TMP/pms.lin" 2>/dev/null); pmc=$(timeout 120 "$LIN_BIN" -t 8 "$TMP/pms.lin" 2>/dev/null)
[ -n "$pm1" ] && [ "$pmok" = 1 ] && [ -n "$pmn" ] && [ "$pmc" = "$pmn" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL parallel map: -t 1 '$pm1' widths agree $pmok; short list compiled '$pmc' net '$pmn'"; }
pmd=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" -t 4 "$TMP/pm.lin" 2>&1 >/dev/null | grep -c "maps its list in parallel")
[ "$pmd" -ge 1 ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL no map was run in parallel"; }
# A FIELD DECLARED bool is a condition: taken out of a block and used by `if`, it is compiled, not left to the net.
printf '%s\n' '(datatype B (bb (n bool) (m num)))' \
  '(define h (\k (\a (if (eq k 0) a (h (sub k 1) (match a ((bb n m) (bb (not n) (add m 1)))))))))' \
  '(match (h 5 (bb true 0)) ((bb n m) (if n m 7)))' > "$TMP/bf.lin"
bf=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/bf.lin" 2>"$TMP/bf.err")
[ "$bf" = "=> 7" ] && ! grep -q declined "$TMP/bf.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a bool field: '$bf'"; }
# A FIELD ONLY PASSED ALONG has the shape its declared type says, so the value it holds can be read in.
printf '%s\n' '(datatype W (w (ac BigInt)))' \
  '(define t1 (\i (\st (if (eq i 0) 0 (t1 (sub i 1) (match st ((w ac) (w ac))))))))' '(t1 5 (w (bigint_of 3)))' > "$TMP/pa.lin"
pa=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/pa.lin" 2>"$TMP/pa.err")
[ "$pa" = "=> 0" ] && ! grep -q declined "$TMP/pa.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a field passed along: '$pa'"; }
# A PARAMETER ONLY LENT is dropped where its path ends -- and one handed to a function that owns it is not (it is
# that function's to free: big_mul hands its `a` to itself, and dropping it too freed it twice).
printf '%s\n' '(define fact (\n (\a (if (eq n 0) a (fact (sub n 1) (big_mul_small a n))))))' \
  '(big_to_string (big_mul (fact 20 (big_of 1)) (fact 25 (big_of 1))))' > "$TMP/bm.lin"
bm=$(timeout 120 "$LIN_BIN" "$TMP/bm.lin" 2>/dev/null)
[ "$bm" = '=> "37737254063669622951147441236213760000000000"' ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL big_mul: '$bm'"; }
sed 's/(digits 0 2000 1/(digits 0 600 1/' "$ROOT/bench/pidigits.lin" > "$TMP/pd.lin"
pd=$(LIN_FN_DEBUG=2 timeout 120 "$LIN_BIN" "$TMP/pd.lin" 2>"$TMP/pd.err")
[ "$pd" = "=> 127083" ] && grep -q "dropped where its paths end" "$TMP/pd.err" && ! grep -q "guard fired" "$TMP/pd.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL pidigits 600: '$pd'"; }
# REGULAR EXPRESSIONS compiled: a pattern built in the net is read in -- its Seqs of pieces and of ranges by
# the types it was declared at, as no single shape of `scons` can say -- and the matching loop runs as C.
# (A recursive predicate's result is a condition; a parameter-typed field may be taken apart as any datatype.)
printf '%s\n' '(define f (\r (\s (\n (if (eq n 0) 0 (add (re_count r s) (f r s (sub n 1))))))))' \
  '(f (regex "a[bc]+d|x[^a-c]y") "xxabcdyyabdaxbdxzy" 400)' > "$TMP/re.lin"
re=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/re.lin" 2>"$TMP/re.err")
[ "$re" = "=> 1200" ] && grep -q "folded a call" "$TMP/re.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a compiled regex loop: '$re'"; }
# A MATCH ON A CONDITIONAL with three or more arms, one of them a call of another recursive function: the branch
# is applied by one arm (a constructor takes it) before another takes the call apart -- still a branch.
printf '%s\n' '(datatype P (pp (a num) (r list num)))' \
  '(define sk (\s (\k (if (is_empty s) (pp k s) (if (eq (head s) 93) (pp k (tail s)) (sk (tail s) (add k 1)))))))' \
  '(define at (\s (if (eq (head s) 46) (pp 0 (tail s)) (if (eq (head s) 91) (sk (tail s) 0) (pp 1 (tail s))))))' \
  '(define cl (\s (\n (if (is_empty s) n (match (at s) ((pp a r) (cl r (add n a))))))))' '(cl "ab[d]x.[yy]z" 0)' > "$TMP/m3.lin"
m3=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/m3.lin" 2>"$TMP/m3.err")
[ "$m3" = "=> 7" ] && ! grep -q declined "$TMP/m3.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a match on a three-armed conditional: '$m3'"; }
# SUBSTITUTIONS chained: a pattern parsed, then a text rewritten around it, five times over -- one unit.
printf '%s\n' '(str_length (re_replace (regex "\\|[^|][^|]*\\|") "-" (re_replace (regex "<[^>]*>") "|" (re_replace (regex "a[NSt]|BY") "<2>" (re_replace (regex "aND|caN|Ha[DS]|WaS") "<3>" (re_replace (regex "tHa[Nt]") "<4>" "xtHaNtyaNDzHaDSaByBYk"))))))' > "$TMP/rs.lin"
rs=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/rs.lin" 2>"$TMP/rs.err")
[ "$rs" = "=> 5" ] && grep -q "folded a call" "$TMP/rs.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL chained substitutions: '$rs'"; }
# INDEPENDENT LOOPS IN ONE EXPRESSION run side by side: two sums over one list, the list built once and handed
# to both tasks.
printf '%s\n' '(define mk (\n (\a (if (eq n 0) a (mk (sub n 1) (scons n a))))))' \
  '(define sq (\s (\t (match s (snil t) ((scons h r) (sq r (add t (mul h h))))))))' \
  '(define cu (\s (\t (match s (snil t) ((scons h r) (cu r (add t (mul h (mul h h)))))))))' \
  '(let ((l (mk 1000 snil))) (add (sq l 0) (cu l 0)))' > "$TMP/pe.lin"
pe=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/pe.lin" 2>"$TMP/pe.err"); pe1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/pe.lin" 2>/dev/null)
[ "$pe" = "=> 250834083500" ] && [ "$pe1" = "$pe" ] && grep -q "[1-9][0-9]* parallel site" "$TMP/pe.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL independent loops in parallel: '$pe' '$pe1'"; }
# A LOOP STARTED EARLY: `cu` needs only the list, so it runs while `sq`'s result -- bound, being used twice -- is
# computed.
printf '%s\n' '(define mk (\n (\a (if (eq n 0) a (mk (sub n 1) (scons n a))))))' \
  '(define sq (\s (\t (match s (snil t) ((scons h r) (sq r (add t (mul h h))))))))' \
  '(define cu (\s (\t (match s (snil t) ((scons h r) (cu r (add t (mul h (mul h h)))))))))' \
  '(let ((l (mk 1000 snil))) (let ((a (sq l 0))) (add (add a a) (cu l 0))))' > "$TMP/pf.lin"
pf=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/pf.lin" 2>"$TMP/pf.err"); pf1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/pf.lin" 2>/dev/null)
[ "$pf" = "=> 251167917000" ] && [ "$pf1" = "$pf" ] && grep -q "[1-9][0-9]* parallel site" "$TMP/pf.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a loop started early: '$pf' '$pf1'"; }
# FUSION: a pipeline over a list two million long is one loop -- no list is built, and the filter's two arms,
# which step to the same next call, stay tail calls (bound first, they were a recursion two million deep).
printf '%s\n' '(sfoldl (\a (\x (add a x))) 0 (sfilter (\x (eq (mod x 2) 0)) (smap (\x (mul x x)) (srange 0 2000000))))' > "$TMP/fu.lin"
fu=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/fu.lin" 2>"$TMP/fu.err"); fu1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/fu.lin" 2>/dev/null)
[ "$fu" = "=> 1333331333334000000" ] && [ "$fu1" = "$fu" ] && [ "$(grep -c "fused" "$TMP/fu.err")" -ge 3 ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a fused pipeline: '$fu' '$fu1'"; }
# A producer whose list ends in another list (sappend): the consumer goes on with that list.
printf '%s\n' '(define up (\i (\n (\rest (if (eq i n) rest (scons i (up (add i 1) n rest)))))))' \
  '(define sm (\s (\a (match s (snil a) ((scons h t) (sm t (add a h)))))))' \
  '(sm (up 0 1000 (scons 5000 (scons 7 snil))) 0)' > "$TMP/fa.lin"
fa=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/fa.lin" 2>"$TMP/fa.err"); fan=$(LIN_FN_OFF=1 timeout 120 "$LIN_BIN" "$TMP/fa.lin" 2>/dev/null)
[ "$fa" = "=> 504507" ] && [ "$fan" = "$fa" ] && grep -q "fused" "$TMP/fa.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL fusion onto a list's own end: '$fa' net '$fan'"; }
# A LOOP WHOSE STEPS ARE INDEPENDENT: each step's inner loop reads only the step, so all of them run at once
# and are folded in order -- here with a fold that is not associative (a*3 + x), so order matters.
printf '%s\n' '(datatype P (pr (a num) (b num)))' \
  '(define work (\i (\n (\s (if (eq n 0) (pr s i) (work i (sub n 1) (add s (mod (mul i n) 7))))))))' \
  '(define go (\i (\n (\acc (if (eq i n) acc (go (add i 1) n (match acc ((pr a b) (match (work i 300 0) ((pr x y) (pr (add (mul a 3) x) (add b y))))))))))))' \
  '(match (go 0 12 (pr 0 0)) ((pr a b) (add (mod a 1000000007) b)))' > "$TMP/pl.lin"
pl=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/pl.lin" 2>"$TMP/pl.err"); pl1=$(timeout 120 "$LIN_BIN" -t 1 "$TMP/pl.lin" 2>/dev/null)
pln=$(LIN_FN_OFF=1 timeout 300 "$LIN_BIN" "$TMP/pl.lin" 2>/dev/null)
[ -n "$pl" ] && [ "$pl1" = "$pl" ] && [ "$pln" = "$pl" ] && grep -q "folds independent steps" "$TMP/pl.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL independent steps folded in order: '$pl' -t 1 '$pl1' net '$pln'"; }
# A NUMERIC unit whose loop folds an inner loop's result (mandel's shape) still compiles: the parallel fold of
# independent steps is a data unit's, and a numeric unit has its own parallel reduction.
printf '%s\n' '(define it (\a (\k (if (eq k 0) a (it (mod (add (mul a a) 7) 1009) (sub k 1))))))' \
  '(define cl (\y (\x (\acc (if (eq x 0) acc (cl y (sub x 1) (add acc (it (add x y) 20))))))))' \
  '(define rw (\y (\acc (if (eq y 0) acc (rw (sub y 1) (add acc (cl y 8 0)))))))' '(rw 5 0)' > "$TMP/nm.lin"
nm=$(LIN_FN_DEBUG=1 timeout 120 "$LIN_BIN" "$TMP/nm.lin" 2>"$TMP/nm.err"); nmn=$(LIN_FN_OFF=1 timeout 300 "$LIN_BIN" "$TMP/nm.lin" 2>/dev/null)
[ -n "$nm" ] && [ "$nm" = "$nmn" ] && grep -q "folded a call" "$TMP/nm.err" && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a numeric nested loop: '$nm' net '$nmn'"; }
# ...but a step that reads the accumulator only through a function it specialises -- a closure capturing it,
# lifted to a parameter -- is not independent: each step needs the one before.
printf '%s\n' '(define tot (\s (\a (match s (snil a) ((scons h t) (tot t (add a h)))))))' \
  '(define go (\k (\u (if (eq k 0) u (go (sub k 1) (smap (\x (add x (tot u 0))) (srange 0 3)))))))' \
  '(let ((r (go 6 (scons 1 (scons 1 (scons 1 snil)))))) (add (tot r 0) (mul 1000 (tot r 1))))' > "$TMP/pd2.lin"
pd2=$(timeout 120 "$LIN_BIN" "$TMP/pd2.lin" 2>/dev/null); pd2n=$(LIN_FN_OFF=1 timeout 300 "$LIN_BIN" "$TMP/pd2.lin" 2>/dev/null)
[ -n "$pd2" ] && [ "$pd2" = "$pd2n" ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL a step reading the accumulator through a closure: '$pd2' net '$pd2n'"; }
# ONE VALUE GIVEN TO TWO CALLS is owned by neither: each `fact` updates its accumulator in place, and the
# starting number they share must survive the first (it was freed under the second).
printf '%s\n' '(define fact (\n (\a (if (eq n 0) a (fact (sub n 1) (big_mul_small a n))))))' \
  '(let ((x (big_of 1))) (big_to_string (big_mul (fact 20 x) (fact 25 x))))' > "$TMP/sh2.lin"
sh2=$(timeout 120 "$LIN_BIN" "$TMP/sh2.lin" 2>/dev/null)
[ "$sh2" = '=> "37737254063669622951147441236213760000000000"' ] && pass=$((pass+1)) || { fail=$((fail+1)); echo "FAIL one value given to two owning calls: '$sh2'"; }
if [ "$fail" -eq 0 ]; then echo "fn_compile: OK ($pass checks: programs compiled from their nets equal the net's own answers, at every thread count)"; else echo "fn_compile: $fail of $((pass+fail)) failed"; fi
exit $fail
