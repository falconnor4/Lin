#!/usr/bin/env bash
# web/build.sh: Lin for the browser -- the engine, the std and its drivers, as one WebAssembly module.
#
#   web/build.sh [-o out-dir] [program.lin ...]
#
# Needs emcc (`nix shell nixpkgs#emscripten`) and, to compile programs' units ahead, the native ./lin
# built from this tree (`make all`).  Writes <out-dir>/lin.js, lin.wasm and lin.data (the std).
#
# THE FUNCTION COMPILER, AHEAD.  Natively, std/drivers/fn compiles a program's hot recursive functions to C
# and runs them, compiling as the program runs.  A page has no C compiler, so for each program named here the
# native engine runs it once with LIN_FN_EMIT_DIR set: every unit it compiles is also written out, under the
# key the browser's engine will compute for the same unit.  Those units are compiled with emcc and linked in;
# in the page the function compiler writes the same source, finds it by that key and runs it.  A unit not
# compiled ahead is computed by the net instead: the same answer, more slowly.  See web/README.md.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=web/dist; PROGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    -o) OUT=$2; shift 2 ;;
    *) PROGS+=("$1"); shift ;;
  esac
done
mkdir -p "$OUT"
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
UNITS=web/units_none.c; UOBJS=()
if [ ${#PROGS[@]} -gt 0 ]; then
  [ -x ./lin ] || { echo "web/build.sh: build the native engine first (make all)" >&2; exit 1; }
  mkdir -p "$TMP/units"
  for p in "${PROGS[@]}"; do
    echo "web/build.sh: compiling the units of $p ahead"
    LIN_FN_EMIT_DIR="$TMP/units" LIN_NO_CACHE=1 ./lin -t 1 "$p" > /dev/null
  done
  UNITS="$TMP/units.c"
  { echo '#include <stdint.h>'
    echo 'typedef int64_t (*Entry)(const int64_t *, int threads);'
    echo 'typedef struct { uint64_t h; Entry entry; int *aborted; void (*release)(void); } LinFnUnit;'
  } > "$UNITS"
  rows=""
  for c in "$TMP"/units/fn-*.c; do
    [ -e "$c" ] || continue
    h=$(basename "$c" .c); h=${h#fn-}
    # (each unit names its entry, abort flag and release alike: renamed apart, one per unit)
    emcc -O2 -std=gnu99 -w -c "$c" -o "$TMP/u-$h.o" -Dlin_fn_entry=lin_fn_entry_$h -Dlin_fn_aborted=lin_fn_aborted_$h -Dlin_fn_release=lin_fn_release_$h
    UOBJS+=("$TMP/u-$h.o")
    rel=0; grep -q 'lin_fn_release(void)' "$c" && rel="lin_fn_release_$h"
    echo "extern int64_t lin_fn_entry_$h(const int64_t *, int); extern int lin_fn_aborted_$h;" >> "$UNITS"
    [ "$rel" != 0 ] && echo "extern void lin_fn_release_$h(void);" >> "$UNITS"
    rows="$rows  { 0x$h, lin_fn_entry_$h, &lin_fn_aborted_$h, $rel },\n"
  done
  printf 'const LinFnUnit lin_fn_units[] = {\n%b  { 0, 0, 0, 0 }\n};\n' "$rows" >> "$UNITS"
  echo "web/build.sh: ${#UOBJS[@]} unit(s) compiled ahead"
fi
SRCS="src/*.c std/drivers/arith.c std/drivers/readback.c std/drivers/text.c std/drivers/simd.c std/drivers/fn.c web/plugins.c $UNITS"
# One thread (a page has no shared memory without special headers); a deep stack (the reducer and the
# parser recurse as deep as the program's data); memory that grows.
emcc -O2 -std=gnu99 -DLIN_STATIC -w $SRCS ${UOBJS[@]+"${UOBJS[@]}"} -o "$OUT/lin.js" \
  -sMODULARIZE=1 -sEXPORT_NAME=createLin -sINVOKE_RUN=0 -sEXIT_RUNTIME=0 \
  -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=256MB -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=64MB \
  -sEXPORTED_RUNTIME_METHODS=callMain,FS,ENV -sENVIRONMENT=web,node \
  --preload-file std@/std --exclude-file '*.so' --exclude-file '*.c' -lm
echo "web/build.sh: wrote $OUT/lin.js, lin.wasm, lin.data"
