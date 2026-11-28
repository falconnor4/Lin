#!/usr/bin/env bash
# ================================================================================
# The 3D Linden scene (examples/linden/three.lin): its shader is Lin, and wherever it runs the
# picture is the same.
# --------------------------------------------------------------------------------
# A few frames are rendered headless three ways and the final pictures must be IDENTICAL, bit for bit:
#   - as it runs by default: the per-pixel loop a GPU kernel when a Vulkan device is present (and
#     glslangValidator is found), else the CPU's threads;
#   - with LIN_GPU=0: the CPU's threads, always;
#   - with LIN_FN_NO_KT=1: the frame's unit with its constants written into the C (THE ENTRY'S
#     CONSTANTS, std/drivers/fn.c), one unit per frame.
# And the frame's unit must be compiled ONCE for the run, not once per frame: the frame counter and
# the camera reach the unit as a table it reads, so every frame is the same source.
# usage: test/linden_3d.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
FRAMES=4
if [ ! -f examples/linden/linden.so ]; then
  make -s examples/linden/linden.so >/dev/null 2>&1 || { echo "linden_3d: SKIP (examples/linden/linden.so cannot be built)"; exit 0; }
fi
render() {   # tag, env... -> $TMP/<tag>.ppm, the debug log in $TMP/<tag>.log
  local tag=$1; shift
  env "$@" LINDEN_HEADLESS=1 LINDEN_FRAMES=$FRAMES LINDEN_PPM="$TMP/$tag.ppm" LIN_NATIVE_CACHE="$TMP/cache-$tag" \
    LIN_FN_DEBUG=1 LIN_GPU_DEBUG=1 timeout 600 "$LIN_BIN" examples/linden/three.lin >"$TMP/$tag.log" 2>&1
}
fail=0
render dflt X=1
render cpu LIN_GPU=0
render nokt LIN_FN_NO_KT=1
for t in dflt cpu nokt; do
  [ -s "$TMP/$t.ppm" ] || { echo "FAIL: the $t run drew no picture"; tail -5 "$TMP/$t.log"; fail=1; }
done
if [ $fail = 0 ]; then
  cmp -s "$TMP/dflt.ppm" "$TMP/cpu.ppm" || { echo "FAIL: the default run's picture differs from the CPU threads'"; fail=1; }
  cmp -s "$TMP/dflt.ppm" "$TMP/nokt.ppm" || { echo "FAIL: the picture with the constants a table differs from the one with them compiled in"; fail=1; }
fi
grep -q "elements are a GPU kernel" "$TMP/dflt.log" || { echo "FAIL: the pixel loop was not written as a kernel"; fail=1; }
folds=$(grep -c "folded a call" "$TMP/dflt.log")
units=$(ls "$TMP/cache-dflt"/fn-*.so 2>/dev/null | wc -l)
[ "$folds" -ge "$FRAMES" ] || { echo "FAIL: $folds frames compiled, of $FRAMES"; fail=1; }
# (frame 0's camera has values that coincide -- a zero angle, a zero length -- so its table is shaped apart: two units;
#  and the scene is a constant, evaluated once before the first frame (main.c, def_precompile): a third, of its own)
[ "$units" -le 3 ] || { echo "FAIL: $units units compiled for $FRAMES frames: the frame is compiled again every frame"; fail=1; }
where="the CPU's threads (no Vulkan device)"
grep -q "kernels run on" "$TMP/dflt.log" && where="the GPU ($(sed -n 's/.*kernels run on \(.*\)/\1/p' "$TMP/dflt.log" | head -1))"
[ $fail = 0 ] || exit 1
echo "linden_3d: OK ($FRAMES frames identical on $where, on the CPU threads, and with the constants compiled in; $units units for the run)"
