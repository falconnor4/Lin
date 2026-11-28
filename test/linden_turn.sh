#!/usr/bin/env bash
# ================================================================================
# A game's frame, compiled whole (std/drivers/fn.c, A LOOP'S STEP): leaves.lin's turn -- draw the world, wait for
# the frame's keys, step the world -- is a turn that waits, compiled once as its parts and run each frame around
# the frame's own call.  The picture after many frames must be IDENTICAL, bit for bit, to the one the net draws
# with that compile switched off (LIN_STEP_WAIT_OFF), and the compiled run must really be the compiled turn.
# usage: test/linden_turn.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
FRAMES=90
if [ ! -f examples/linden/linden.so ]; then
  make -s examples/linden/linden.so >/dev/null 2>&1 || { echo "linden_turn: SKIP (examples/linden/linden.so cannot be built)"; exit 0; }
fi
render() {   # tag, game, frames, env... -> $TMP/<tag>.ppm, the debug log in $TMP/<tag>.log
  local tag=$1 game=$2 frames=$3; shift 3
  env "$@" LINDEN_HEADLESS=1 LINDEN_FRAMES=$frames LINDEN_PPM="$TMP/$tag.ppm" LIN_NATIVE_CACHE="$TMP/cache-$tag" \
    LIN_FN_DEBUG=1 timeout 600 "$LIN_BIN" examples/linden/$game.lin >"$TMP/$tag.log" 2>&1
}
fail=0
render turn leaves $FRAMES X=1
render net leaves $FRAMES LIN_STEP_WAIT_OFF=1
# wisps.lin: its world holds floats and a list of wisps, its picture a rendered view.  On the net its turns are
# too slow to run far, so the two agree over a couple of frames (walking and turning: LINDEN_KEYS), and the
# compiled turn then runs a long game of its own.
render wturn wisps 2 LINDEN_KEYS=6,6
render wnet wisps 2 LINDEN_KEYS=6,6 LIN_STEP_WAIT_OFF=1
render wlong wisps 240 LINDEN_KEYS=6,6,6,4,4,4,2,16,4100,4
for t in turn net wturn wnet wlong; do
  [ -s "$TMP/$t.ppm" ] || { echo "FAIL: the $t run drew no picture"; tail -5 "$TMP/$t.log"; fail=1; }
done
[ $fail = 0 ] && { cmp -s "$TMP/turn.ppm" "$TMP/net.ppm" || { echo "FAIL: the compiled turn's picture differs from the net's"; fail=1; }; }
[ $fail = 0 ] && { cmp -s "$TMP/wturn.ppm" "$TMP/wnet.ppm" || { echo "FAIL: wisps' compiled turn draws something else than the net"; fail=1; }; }
for t in turn wturn wlong; do
  grep -q "step: compiled as its parts" "$TMP/$t.log" || { echo "FAIL: the $t run's turn was not compiled"; grep "step:" "$TMP/$t.log"; fail=1; }
done
grep -q "step: compiled as its parts" "$TMP/net.log" && { echo "FAIL: LIN_STEP_WAIT_OFF still compiled the turn"; fail=1; }
[ $fail = 0 ] || exit 1
echo "linden_turn: OK ($FRAMES frames of leaves.lin and 2 of wisps.lin: the compiled turn draws what the net draws; 240 frames of wisps compiled)"
