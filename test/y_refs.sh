#!/usr/bin/env bash
# Recursive calls the function compiler declines are rewritten (std/drivers/fn.c, y_expand):
#   `(Y v) args` -> `(v1 (Y' v2)) args`, v1 and v2 the two sides of ONE fan on v with a label of the call's own
#   (net_fresh_label).  The fan copies lazily, so the steps are the knot's; what changes is what a call LEAVES:
#   the core retires the call's fans once its copy can no longer be observed, so the net stays the size of one
#   call instead of growing with every call.  With the compiler off every call goes this way, so these programs
#   check it against the Y knot (LIN_Y_OFF=1): the same answer always, and a net that does not grow.
set -u
LIN_BIN="${1:-./lin}"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
fail=0; pass=0
run() { LIN_FN_OFF=1 timeout 120 "$LIN_BIN" --bench -t 1 "$1" 2>&1; }
ans() { printf '%s\n' "$1" | grep -o '=> .*' | sed 's/\[bench\].*//' | head -1; }
nodes() { printf '%s\n' "$1" | grep -o '[0-9]* nodes' | head -1 | cut -d' ' -f1; }
# check <name> <program> <answer> <max percent of the knot's net size at the end, or - for answer only>
check() {
  printf '%s\n' "$2" > "$TMP/$1.lin"
  local y k; y=$(run "$TMP/$1.lin"); k=$(LIN_Y_OFF=1 run "$TMP/$1.lin")
  local ya kz; ya=$(ans "$y"); kz=$(ans "$k")
  if [ "$ya" != "=> $3" ] || [ "$kz" != "=> $3" ]; then
    echo "FAIL $1: expected '=> $3', rewritten '$ya', knot '$kz'"; fail=$((fail+1)); return
  fi
  if [ "$4" != - ]; then
    local ys ks; ys=$(nodes "$y"); ks=$(nodes "$k")
    if [ -z "$ys" ] || [ -z "$ks" ] || [ $((ys * 100)) -gt $((ks * $4)) ]; then
      echo "FAIL $1: a net of $ys nodes rewritten against the knot's $ks (bound $4%)"; fail=$((fail+1)); return
    fi
    echo "  $1: $ys nodes (knot $ks)"
  fi
  pass=$((pass+1))
}
# one self call per call: each call's fans retired once it is done, so the net stays the size of one call
check loop '(define go (\k (if (eq k 0) 0 (go (sub k 1))))) (go 2000)' 0 5
# two self calls (the self shared by the program's own fan)
check fib '(define fib (\k (if (lt k 2) k (add (fib (sub k 1)) (fib (sub k 2)))))) (fib 12)' 144 -
# two definitions sharing the form's operator meanings (values from outside the definition)
check shared '(define mk (\k (\a (if (eq k 0) a (mk (sub k 1) (scons k a)))))) (define s (\l (\acc (match l (snil acc) ((scons x r) (s r (add acc x))))))) (s (mk 30 snil) 0)' 465 -
# a function argument carried through the recursion
check higher '(define app (\f (\k (if (eq k 0) 0 (f (app f (sub k 1))))))) (app (\x (add x 2)) 10)' 20 -
# a recursive function used at two places, one of them unapplied (passed on)
check passed '(define dbl (\k (if (eq k 0) 0 (add 2 (dbl (sub k 1)))))) (define twice (\f (\x (f (f x))))) (twice dbl 3)' 12 -
# mutual recursion
check mutual '(define ev (\k (if (eq k 0) true (od (sub k 1))))) (define od (\k (if (eq k 0) false (ev (sub k 1))))) (if (ev 41) 1 0)' 0 -
# a lazy structure: the recursion is unbounded and only what is demanded is unfolded
check lazy '(define from (\k (scons k (from (add k 1))))) (define take (\n (\l (if (eq n 0) 0 (match l (snil 0) ((scons x r) (add x (take (sub n 1) r)))))))) (take 5 (from 1))' 15 -
if [ "$fail" -eq 0 ]; then
  echo "y_refs: OK ($pass programs: the rewritten calls give the knot's answers, and a finished call leaves nothing behind)"
else
  echo "y_refs: $fail problem(s)"; exit 1
fi
