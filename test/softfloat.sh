#!/usr/bin/env bash
# ================================================================================
# The pure soft float (std/softfloat.lin) is the hardware's IEEE-754, bit for bit.
# --------------------------------------------------------------------------------
# A float is a 64-bit pattern, and std/softfloat.lin is the PURE meaning of the float
# operations -- the net computes them with integer operations alone.  For each
# operation, a Lin loop draws operands from a 64-bit LCG in four shapes (raw bit
# patterns: NaNs, infinities, everything; values near 1; subnormal exponents; huge
# exponents), applies the soft-float operation and folds every result into a checksum
# (a NaN as one canonical NaN: which NaN an operation returns is unspecified).
# The same loop in C over std/runtime/i64.h's HARDWARE rows must give the same checksum.
# (The Lin loop runs through the function compiler, which compiles the soft float from
# its own net; test/fn_compile.sh holds that compiler to the net's own answers.)
# usage: test/softfloat.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
CC=$(command -v cc || command -v gcc || true)
[ -n "$CC" ] || { echo "softfloat: SKIPPED (no C compiler for the reference)"; exit 0; }
N=${SOFTFLOAT_N:-3000}
BIN2="add sub mul divz min max"; BOOL2="eq lt leq"; UN="sqrtz floor fract sign"
if [ -n "${SOFTFLOAT_OPS:-}" ]; then          # a subset, e.g. SOFTFLOAT_OPS="mul sqrtz"
  pick() { for o in $1; do case " $SOFTFLOAT_OPS " in *" $o "*) printf '%s ' "$o";; esac; done; }
  BIN2=$(pick "$BIN2"); BOOL2=$(pick "$BOOL2"); UN=$(pick "$UN"); OFI=$(pick ofint)
else OFI=ofint; fi
cat > "$TMP/ref.c" <<'C'
#define LIN_WANT_F64
#include <stdio.h>
#include <string.h>
#include <math.h>
#include RT
static long lcg(long x) { return lin_i64_add(lin_i64_mul(x, 6364136223846793005L), 1442695040888963407L); }
static long shape(long m, long x) {
  long keep = x & (long)0x800FFFFFFFFFFFFFUL;
  if (m == 1) return keep | ((1007 + ((x >> 52) & 31)) << 52);
  if (m == 2) return keep | (((x >> 52) & 31) << 52);
  if (m == 3) return keep | ((2016 + ((x >> 52) & 31)) << 52);
  return x;
}
static long divz(long a, long b) { return lin_f64_div(a, b); }
static long sqrtz(long a) { return lin_f64_sqrt(a); }
static long fsign(long a) { return lin_f64_sign(a); }
int main(int argc, char **argv) {
  const char *op = argv[1]; long n = atol(argv[2]), m = atol(argv[3]), x = 1, y = 2, acc = 0;
  for (; n > 0; n--) {
    long a = shape(m, x), b = shape(m, y), r = 0;
    if (!strcmp(op, "add")) r = lin_f64_add(a, b); else if (!strcmp(op, "sub")) r = lin_f64_sub(a, b);
    else if (!strcmp(op, "mul")) r = lin_f64_mul(a, b); else if (!strcmp(op, "divz")) r = divz(a, b);
    else if (!strcmp(op, "min")) r = lin_f64_min(a, b); else if (!strcmp(op, "max")) r = lin_f64_max(a, b);
    else if (!strcmp(op, "eq")) r = lin_f64_eq(a, b); else if (!strcmp(op, "lt")) r = lin_f64_lt(a, b);
    else if (!strcmp(op, "leq")) r = lin_f64_leq(a, b); else if (!strcmp(op, "sqrtz")) r = sqrtz(a);
    else if (!strcmp(op, "floor")) r = lin_f64_floor(a); else if (!strcmp(op, "fract")) r = lin_f64_fract(a);
    else if (!strcmp(op, "sign")) r = fsign(a); else if (!strcmp(op, "ofint")) r = lin_f64_of_int(x);
    if (strcmp(op, "eq") && strcmp(op, "lt") && strcmp(op, "leq") && (r & 0x7FFFFFFFFFFFFFFFL) > 0x7FF0000000000000L) r = 0x7FF8000000000000L;
    acc = lin_i64_add(lin_i64_mul(acc, 31), r);
    x = lcg(x); y = lcg(lin_i64_bxor(y, n));
  }
  printf("%ld\n", acc); return 0;
}
C
sed -i "s|#include RT|#include \"$ROOT/std/runtime/i64.h\"|" "$TMP/ref.c"
sed -i 's|#include <math.h>|#include <math.h>\n#include <stdlib.h>|' "$TMP/ref.c"
"$CC" -O1 -ffp-contract=off -o "$TMP/ref" "$TMP/ref.c" -lm || { echo "softfloat: FAIL (reference did not build)"; exit 1; }
{ echo '(load "std/softfloat.lin")'
  echo '(define cn (\r (if (num._isnan r) 9221120237041090560 r)))   ; a NaN result: its payload is unspecified'
  echo '(define lcg (\x (add (mul x 6364136223846793005) 1442695040888963407)))'
  echo '(define shape (\m (\x (if (eq m 1) (bor (band x -9218868437227405313) (shl (add 1007 (band (shr x 52) 31)) 52))
    (if (eq m 2) (bor (band x -9218868437227405313) (shl (band (shr x 52) 31) 52))
    (if (eq m 3) (bor (band x -9218868437227405313) (shl (add 2016 (band (shr x 52) 31)) 52)) x))))))'
  for f in $BIN2; do echo "(define T$f (\\n (\\m (\\x (\\y (\\acc (if (eq n 0) acc (T$f (sub n 1) m (lcg x) (lcg (bxor y n)) (add (mul acc 31) (cn (num._sf$f (shape m x) (shape m y))))))))))))"; done
  for f in $BOOL2; do echo "(define T$f (\\n (\\m (\\x (\\y (\\acc (if (eq n 0) acc (T$f (sub n 1) m (lcg x) (lcg (bxor y n)) (add (mul acc 31) (if (num._sf$f (shape m x) (shape m y)) 1 0))))))))))"; done
  for f in $UN; do echo "(define T$f (\\n (\\m (\\x (\\y (\\acc (if (eq n 0) acc (T$f (sub n 1) m (lcg x) (lcg (bxor y n)) (add (mul acc 31) (cn (num._sf$f (shape m x))))))))))))"; done
  echo "(define Tofint (\\n (\\m (\\x (\\y (\\acc (if (eq n 0) acc (Tofint (sub n 1) m (lcg x) (lcg (bxor y n)) (add (mul acc 31) (num._sfofint x))))))))))"
  for f in $BIN2 $BOOL2 $UN $OFI; do for m in 0 1 2 3; do echo "(T$f $N $m 1 2 0)"; done; done; } > "$TMP/t.lin"
got=$(timeout 900 "$LIN_BIN" "$TMP/t.lin" 2>/dev/null | sed -n 's/^=> //p')
want=$(for f in $BIN2 $BOOL2 $UN $OFI; do for m in 0 1 2 3; do "$TMP/ref" "$f" "$N" "$m"; done; done)
pass=0; fail=0; i=0
for f in $BIN2 $BOOL2 $UN $OFI; do for m in 0 1 2 3; do
  i=$((i+1)); g=$(printf '%s\n' "$got" | sed -n "${i}p"); w=$(printf '%s\n' "$want" | sed -n "${i}p")
  if [ -n "$g" ] && [ "$g" = "$w" ]; then pass=$((pass+1)); else fail=$((fail+1)); echo "FAIL $f shape $m: soft '$g' hardware '$w'"; fi
done; done
if [ "$fail" -eq 0 ]; then echo "softfloat: OK ($pass checksums over $N operand pairs each: the pure soft float is the hardware's IEEE-754)"; else echo "softfloat: $fail of $((pass+fail)) failed"; fi
exit $fail
