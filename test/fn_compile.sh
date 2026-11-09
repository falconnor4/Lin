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
if [ "$fail" -eq 0 ]; then echo "fn_compile: OK ($pass programs compiled from their nets, identical to the net's own answers)"; else echo "fn_compile: $fail of $((pass+fail)) failed"; fi
exit $fail
