#!/bin/sh
# An FFI call is DYNAMIC: std/drivers/readback.c builds the call interface from the argument kinds with
# libffi, so the ARITY is a runtime count and nothing enumerates it.  Proven the only way that counts --
# a C function with TWELVE arguments, called through the FFI primitive with twelve.  The ladder this
# replaced silently passed 8 arguments whatever the count was, which is a wrong CALL, not a clipped value.
set -e
R=$(dirname "$0")/..
BIN=${1:-$R/lin}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cat > "$T/ffi12.c" <<'C'
long lin_ffi12(long a, long b, long c, long d, long e, long f,
               long g, long h, long i, long j, long k, long l) { return a+b+c+d+e+f+g+h+i+j+k+l; }
C
${CC:-cc} -O2 -fPIC -shared -o "$T/ffi12.so" "$T/ffi12.c"
# build the argument list by COUNTING, so the arity this test asserts is itself not a literal
ARGS=nil; i=12
while [ "$i" -ge 1 ]; do ARGS="(cons $i $ARGS)"; i=$((i-1)); done
{
  printf '(load_lib "%s")\n' "$T/ffi12.so"
  printf '(ffi.ffi "lin_ffi12" %s)\n' "$ARGS"
} > "$T/dyn.lin"
out=$("$BIN" "$T/dyn.lin" 2>&1 | tail -1)
[ "$out" = "=> 78" ] || { echo "ffi_arity: a 12-argument FFI call returned '$out', want '=> 78'"; exit 1; }
grep -q 'ffi_call' "$R/std/drivers/readback.c" || { echo "ffi_arity: readback does not call through libffi"; exit 1; }
if grep -q 'argc == 7\|FFI_ARMS' "$R/std/drivers/readback.c"; then echo "ffi_arity: readback still enumerates arity"; exit 1; fi
echo "ffi_arity: OK (a 12-argument C function through the FFI returns 78: arity is a runtime count, not a ladder)"
