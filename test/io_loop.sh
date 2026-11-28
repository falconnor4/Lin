#!/usr/bin/env bash
# Effects that loop (`io_loop s step`, `io_next`, `io_done`): the runner hands each turn a fresh copy of the step
# and forces the state as data between turns (std/drivers/readback.c).  The state is any value -- a number, a
# list of records, a record holding a list -- and the compiled units read it in every turn: each program must
# print the same compiled as on the net alone.  The record whose list starts empty is the case that once read the
# list's end as the number 0 (the terminal is both) and crashed the unit that walked it.
set -u
LIN_BIN="${1:-./lin}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
LEAF='(load "std/std.lin")
(datatype Leaf (leaf (x num) (y num) (v num)))
(define fall (\ls (match ls ((cons l r) (match l ((leaf x y v) (cons (leaf x (add y v) v) (fall r))))) (nil nil))))
(define hit (\px (\l (match l ((leaf x y v) (gt x px))))))
(define keep (\px (\ls (match ls ((cons l r) (if (hit px l) (keep px r) (cons l (keep px r)))) (nil nil)))))
(define ysum (\ls (match ls ((cons l r) (match l ((leaf x y v) (add y (ysum r))))) (nil 0))))
(define mk (\n (if (eq n 0) nil (cons (leaf n 0 1) (mk (sub n 1))))))'
WORLD='(datatype World (world (px num) (leaves list Leaf) (t num)))
(define score (\w (match w ((world px ls t) (ysum ls)))))'
n=0; fail=0
check() {   # name, program, expected output
  n=$((n+1)); printf '%s\n' "$2" > "$TMP/p$n.lin"
  for mode in compiled net; do
    if [ "$mode" = net ]; then got=$(LIN_FN_OFF=1 timeout 120 "$LIN_BIN" "$TMP/p$n.lin" 2>&1 | grep -v '^=>'); else got=$(timeout 120 "$LIN_BIN" "$TMP/p$n.lin" 2>&1 | grep -v '^=>'); fi
    if [ "$got" != "$3" ]; then echo "io_loop: $1 ($mode): got '$got', want '$3'"; fail=1; fi
  done
}
check "a counter" '(load "std/std.lin")
(io_loop 0 (\x (if (eq x 5) (io_print x io_done) (io_print x (io_next (add x 1))))))' '012345'
check "loops in sequence" '(load "std/std.lin")
(io_loop 0 (\x (if (eq x 4) (io_print x io_done) (io_next (add x 1)))))
(io_loop 0 (\x (io_print x (if (eq x 4) io_done (io_next (add x 1))))))' '401234'
check "a list of records" "$LEAF
(io_loop (cons (leaf 1 0 1) (cons (leaf 2 0 2) nil)) (\s (if (gt (ysum s) 30) (io_print (ysum s) io_done) (io_print (ysum s) (io_next (fall s))))))" '03691215182124273033'
check "fused walks of the state" "$LEAF
(io_loop (mk 6) (\s (if (gt (ysum s) 20) io_done (io_print (ysum s) (io_next (keep 3 (fall s)))))))" '0369121518'
check "a record holding a list" "$LEAF
$WORLD
(define step (\w (match w ((world px ls t) (world px (keep px (fall ls)) (add t 1))))))
(io_loop (world 3 (mk 6) 0) (\w (if (gt (score w) 20) io_done (io_print (score w) (io_next (step w))))))" '0369121518'
check "a record whose list starts empty" "$LEAF
$WORLD
(define step (\w (match w ((world px ls t) (world px (cons (leaf t 0 1) (keep px (fall ls))) (add t 1))))))
(io_loop (world 3 nil 0) (\w (if (gt (score w) 40) io_done (io_print (score w) (io_next (step w))))))" '001361014182226303438'
check "a game's world, stepped" '(load "std/std.lin")
(datatype Leaf (leaf (x num) (y num) (v num)))
(datatype World (world (px num) (leaves list Leaf) (score num) (lives num) (seed num) (t num)))
(define rnd (\s (mod (add (mul s 1103515245) 12345) 2147483648)))
(define fall (\ls (match ls ((cons l r) (match l ((leaf x y v) (cons (leaf x (add y v) v) (fall r))))) (nil nil))))
(define in_basket (\px (\l (match l ((leaf x y v) (and (gt y 104) (and (lt y 114) (and (gt (add x 4) px) (lt x (add px 24))))))))))
(define landed (\l (match l ((leaf x y v) (gt y 114)))))
(define caught (\px (\ls (match ls ((cons l r) (add (if (in_basket px l) 1 0) (caught px r))) (nil 0)))))
(define missed (\ls (match ls ((cons l r) (add (if (landed l) 1 0) (missed r))) (nil 0))))
(define still_falling (\px (\ls (match ls ((cons l r) (if (or (in_basket px l) (landed l)) (still_falling px r) (cons l (still_falling px r)))) (nil nil)))))
(define spawn (\t (\seed (\ls (if (eq (mod t 24) 0) (cons (leaf (mod (shr seed 8) 152) 0 (add 1 (mod (shr seed 16) 2))) ls) ls)))))
(define step (\w (match w ((world px ls score lives seed t)
  (let ((fl (fall ls))) (let ((got (caught px fl)) (lost (missed fl)))
    (world px (spawn t seed (still_falling px fl)) (add score got) (sub lives (if (gt lost lives) lives lost)) (rnd seed) (add t 1))))))))
(io_loop (world 68 nil 0 3 2024 0) (\w (match w ((world px ls score lives seed t)
  (if (gt t 150) (io_print score (io_print lives io_done)) (io_next (step w)))))))' '00'
[ "$fail" = 0 ] && echo "io_loop: OK ($n loops, from a counter to records holding lists, compiled and on the net)"
exit $fail
