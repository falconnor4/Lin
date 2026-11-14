#!/usr/bin/env bash
# ================================================================================
# The program cache runs compiled units again; it never remembers an answer.
# --------------------------------------------------------------------------------
# A program whose every expression was one compiled call on constants is, on its
# next run, answered by running those units without parsing or compiling it.  This
# suite pins what makes that sound:
#   * a cached run prints exactly what the first run printed;
#   * a change to the source is a different program (the old entry is not used);
#   * a program that reads the outside world is never cached;
#   * a program with an expression the compiler did not answer is never cached;
#   * LIN_NO_CACHE turns it off.
# (An expression that is more than one compiled call -- `(lt (fib 10) 100)` -- is likewise not recorded: the
#  structure case below stands for every program with an expression the cache has no unit for.)
# usage: test/program_cache.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
export LIN_NATIVE_CACHE="$TMP/cache"
pass=0; fail=0
ok() { pass=$((pass+1)); }
bad() { fail=$((fail+1)); echo "FAIL $1"; }
run() { LIN_CACHE_DEBUG=1 timeout 120 "$LIN_BIN" "$@" 2>"$TMP/err"; }
hit() { grep -q "run from compiled units" "$TMP/err"; }

printf '%s\n' '(define fib (\n (if (lt n 2) n (add (fib (sub n 1)) (fib (sub n 2))))))' '(fib 25)' '(define sq (\i (\a (if (eq i 0) a (sq (sub i 1) (add a (mul i i)))))))' '(sq 1000 0)' '(fib 12)' > "$TMP/p.lin"
a=$(run "$TMP/p.lin"); hit && bad "the first run cannot be a cached one"
b=$(run "$TMP/p.lin"); hit && ok || bad "the second run was not run from the cache"
want=$'=> 75025\n=> 333833500\n=> 144'
[ "$a" = "$want" ] && [ "$b" = "$want" ] && ok || bad "cached output differs: first '$a' second '$b'"
c=$(LIN_CACHE_DEBUG=1 timeout 120 "$LIN_BIN" -t 1 "$TMP/p.lin" 2>"$TMP/err"); hit && [ "$c" = "$want" ] && ok || bad "one thread: '$c'"

# the source changes: a different program
sed -i 's/(fib 25)/(fib 26)/' "$TMP/p.lin"
d=$(run "$TMP/p.lin"); hit && bad "a changed source was answered from the old entry"
[ "$(printf '%s\n' "$d" | head -1)" = "=> 121393" ] && ok || bad "changed source: '$d'"

# a small constant structure the program defines is compiled into the unit, so the program is cached too
printf '%s\n' '(datatype P (pt (x num) (y num)))' '(define ps (scons (pt 1 2) (scons (pt 3 4) snil)))' \
  '(define go (\n (\s (\acc (if (eq n 0) acc (go (sub n 1) s (add acc (sfoldl (\a (\p (match p ((pt x y) (add a (mul x y)))))) 0 s))))))))' \
  '(go 1000 ps 0)' > "$TMP/k.lin"
k1=$(run "$TMP/k.lin"); k2=$(run "$TMP/k.lin")
hit && [ "$k1" = "=> 14000" ] && [ "$k2" = "$k1" ] && ok || bad "a program with a constant structure: '$k1' '$k2'"

# the outside world: never cached
printf '%s\n' '(define f (\n (if (eq n 0) 0 (add n (f (sub n 1))))))' '(f (ccall "atoi" (cons (getenv "LIN_T_N") nil)))' > "$TMP/e.lin"
e1=$(LIN_T_N=10 run "$TMP/e.lin"); e2=$(LIN_T_N=20 run "$TMP/e.lin")
hit && bad "a program reading the environment was cached"
[ "$e1" = "=> 55" ] && [ "$e2" = "=> 210" ] && ok || bad "environment program: '$e1' '$e2'"

# an expression the compiler does not answer with a word: never cached
printf '%s\n' '(define g (\n (if (eq n 0) 1 (mul 2 (g (sub n 1))))))' '(g 10)' '(pair 1 2)' > "$TMP/s.lin"
s1=$(run "$TMP/s.lin"); s2=$(run "$TMP/s.lin")
hit && bad "a program with a structure result was cached"
[ "$s1" = "$s2" ] && [ "$(printf '%s\n' "$s1" | head -1)" = "=> 1024" ] && ok || bad "structure program: '$s1' '$s2'"

# off
printf '%s\n' '(define h (\n (if (eq n 0) 0 (add 1 (h (sub n 1))))))' '(h 500)' > "$TMP/o.lin"
run "$TMP/o.lin" >/dev/null; LIN_NO_CACHE=1 run "$TMP/o.lin" >/dev/null
hit && bad "LIN_NO_CACHE did not turn the cache off" || ok

if [ "$fail" -eq 0 ]; then echo "program_cache: OK ($pass checks: a cached run runs the compiled units again and prints the same)"; else echo "program_cache: $fail of $((pass+fail)) failed"; fi
exit $fail
