#!/bin/sh
# The FFI call ladder in std/drivers/readback.c forwards ONE call per arity, so the arity the LANGUAGE can
# write must stay inside it: `ccallN` in std/ffi.lin, and any raw `ffi.ffi fn args` list a program builds.
# A call the ladder cannot forward is refused at run time, so the two counts are one property -- this pins
# them together, and pins that the refusal is there (the last arm used to pass 8 arguments whatever the
# count was, which is a wrong CALL, not a clipped value).
R=$(dirname "$0")/..
arms=$(sed -n 's/^#define FFI_ARMS \([0-9][0-9]*\).*/\1/p' "$R/std/drivers/readback.c" | head -1)
[ -n "$arms" ] || { echo "ffi_arity: readback has no FFI_ARMS"; exit 1; }
most=$(grep -rho 'ccall[0-9][0-9]*' "$R/std" --include=*.lin | sed 's/ccall//' | sort -n | tail -1)
[ -n "$most" ] || { echo "ffi_arity: no ccallN family in the std"; exit 1; }
[ "$most" -le "$arms" ] || { echo "ffi_arity: the std writes ccall$most but the ladder forwards only $arms"; exit 1; }
grep -q 'argc > FFI_ARMS' "$R/std/drivers/readback.c" || { echo "ffi_arity: the ladder does not refuse an arity it cannot forward"; exit 1; }
echo "ffi_arity: OK (the ladder forwards $arms arguments; the std's ccallN family tops out at $most, and anything larger is refused out loud)"
