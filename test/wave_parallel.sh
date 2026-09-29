#!/usr/bin/env bash
# ================================================================================
# The THREADED wave path.
# --------------------------------------------------------------------------------
# Under needed order a wave is only as wide as the program's DEMAND FRONTIER: `net_mark_demand`
# walks one path per root and stops at each redex it meets, because marking THROUGH one would
# demand an unbounded Y-knot unrolling.  A wave of one pair cannot use a second thread, so the
# OpenMP dispatcher in `lin_reduce_wave_parallel` needs a workload that really has several
# independent redexes live at once -- measured widest waves: nqueens 190, tseitin 121,
# stress_wavefront 22, queue 20.  (The "64-way wavefront" test is width 1: its wavefront is the
# PROGRAM's, not the reducer's.)
#
# So this suite widens the wave the only way a caller may: with MULTIPLE DEMAND ROOTS.  `lin_demand`
# is the ABI call by which a caller states that a port's weak head normal form is about to be
# observed, and `net_mark_demand` seeds from every root -- so a caller observing k independent
# results needs k redexes in one wave.  The probe driver below is that caller: it locates live,
# node-disjoint redexes of the net, declares each an ACTIVE redex pair (`lin_enqueue`) and declares
# its two principal ports OBSERVED (`lin_demand`).  It is a probe of the core's own ABI and nothing
# else -- no label, no driver name, no knowledge of what the program computes -- and it is compiled
# from a string here, into a scratch directory, so it can never become part of the shipped std.
#
# What is checked:
#   (a) WITHOUT a widening caller the width stays 1 and no thread is ever dispatched: the serial
#       behaviour must not have moved.  Checked with a driver-free prelude (no driver claims the
#       wave) at every thread count.
#   (b) WITH it the wave widens to >= 4, and the dispatcher runs at each thread count the widened
#       wave actually reaches: `par_batches > 0` exactly when `np >= 4*nth` -- the gate is the
#       measured fork/join cost (2.4 us at 4 threads) against a few hundred ns per interaction, so
#       the test pins BOTH directions: wide enough must dispatch, too narrow must not.
#   (c) every result is byte-identical to the same run at -t 1, and -- with the standard library
#       loaded, where the programs are run as they were written -- the widened run is
#       byte-identical to the un-widened one.  Interaction nets are confluent, so firing
#       independent redexes cannot change the answer; this is what pins that claim to a real wave
#       instead of to the argument.
#
# The driver-free prelude is used for the width and dispatch checks because a driver that CLAIMS
# redexes takes them out of the base engine's wave (the base engine then has nothing to thread).
# It is NOT used for an answer-identity check against the un-widened run for every program: a
# demand root states that a port IS observed, so a program that leaves a thunk there legitimately
# reduces further (measured: stress_wavefront.lin's driver-free run leaves its simd sections
# unreduced -- an empty prelude registers no fold pre-emptor, and the simd strategy then strands
# them -- while the same run with the std loaded prints the values its own `; expect` lines name).
# The assertion that always holds, and is the point of the suite, is checked for every program:
# every thread count agrees byte-for-byte with -t 1.
#
# usage: test/wave_parallel.sh [LIN_BIN] [LIN_STD_DIR]
# ================================================================================
set -e
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1

PROGS="test/queue.lin test/tseitin.lin test/stress_wavefront.lin test/nqueens.lin"
GATE=4                  # `np >= 4 * nth`, the rationalised dispatch gate in lin_reduce_wave_parallel
WANT=128                # demand roots the probe declares per wave
EMPTY=$(mktemp)         # a std with no drivers in it: the base engine is then the only reducer
pass=0; fail=0
bad() { fail=$((fail+1)); echo "FAIL $*"; }

# `width`/`batches`/`pairs` out of the [wave] report; empty when the run printed none.
field() { sed -n "s/.*$1=\([0-9]*\).*/\1/p"; }

# ---------------- the widening caller, built from a string into a scratch dir -------------------
# A preloaded plugin, like test/parallel_guard.py's probes: the constructor runs before main and
# registers the driver, so a program is widened without editing it.  `dlsym`, never a direct call:
# a preloaded object is relocated before the executable's own symbols are in scope.
PROBE_C=$(cat <<'EOF'
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <dlfcn.h>

/* A caller that observes SEVERAL ports at once.  Each wave it declares up to `want` live,
   node-disjoint redexes of the net: `lin_enqueue` says this is an active redex pair, `lin_demand`
   says its two principal ports are about to be observed.  Nothing else -- the core decides what may
   run at once (its exact partition), and nothing here knows what the program computes. */
static int want = 128, declared, scans;
static int live(const Net *n, int v) { return v >= 0 && v < n->nn && !n->dead[v]; }

/* The two core entry points are resolved at CALL time, like `lin_driver_add` above and for a second
   reason: the suite launches every run under `timeout`, so this object is preloaded into `timeout`
   FIRST, and `timeout` does not export `lin_enqueue`/`lin_demand`.  A toolchain that links with
   BIND_NOW -- `nix develop`'s does, the distro's cc does not -- then refuses the load outright and
   every probe run comes back empty (measured: 17 problems inside `nix develop`, a clean run outside
   it, with the same object); lazy binding only hides it.  Resolving by name leaves the object with
   no undefined core symbols, so it loads either way. */
static void (*wp_enqueue)(Net *, Port, Port);
static void (*wp_demand)(Net *, Port);
static int wp_resolve(void) {
  if (!wp_enqueue) wp_enqueue = (void (*)(Net *, Port, Port))dlsym(RTLD_DEFAULT, "lin_enqueue");
  if (!wp_demand) wp_demand = (void (*)(Net *, Port))dlsym(RTLD_DEFAULT, "lin_demand");
  return wp_enqueue && wp_demand;
}

static int wp_match(Net *n, void *st, LinView *view, LinClaim *out) {
  (void)st; (void)view; (void)out;
  int taken[256], nt = 0;
  if (!wp_resolve()) return 0;
  if (declared >= want || scans++ >= 64) return 0;
  for (int u = 1; u < n->nn && declared < want; u++) {
    int tu = n->tag[u];
    if (tu != LAM && tu != APP && tu != DUP) continue;
    int w = n->wire[u * 3].node;
    if (n->wire[u * 3].port != 0 || w <= u || !live(n, w)) continue;
    int tw = n->tag[w];
    if (!((tu == LAM && (tw == APP || tw == DUP)) || (tu != LAM && (tw == LAM || tw == DUP)))) continue;
    if (n->wire[w * 3].node != u || n->wire[w * 3].port != 0) continue;
    int clash = 0;
    for (int j = 0; j < nt; j++) if (taken[j] == u || taken[j] == w) clash = 1;
    if (clash) continue;
    taken[nt++] = u; taken[nt++] = w;
    wp_enqueue(n, (Port){u, 0}, (Port){w, 0});
    wp_demand(n, (Port){u, 0}); wp_demand(n, (Port){w, 0});
    declared++;
  }
  return 0;
}
static void wp_report(void) { fprintf(stderr, "[waveprobe] declared=%d of %d\n", declared, want); }
LinDriver lin_waveprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "waveprobe", .description = "a caller observing several independent redexes at once",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_MATCH,
  .match = wp_match,
};
__attribute__((constructor)) static void wp_init(void) {
  const char *e = getenv("LIN_WAVE_PROBE");
  if (e) want = atoi(e);
  void (*add)(LinDriver *) = (void (*)(LinDriver *))dlsym(RTLD_DEFAULT, "lin_driver_add");
  if (add) add(&lin_waveprobe_driver);
  atexit(wp_report);
}
EOF
)

CC=$(command -v cc || command -v gcc || true)
TMPD=$(mktemp -d)
trap 'rm -rf "$TMPD" "$EMPTY"; rm -f /tmp/wave_*.err /tmp/wave_*.out' EXIT
PROBE=""
if [ -n "$CC" ]; then
  echo "$PROBE_C" > "$TMPD/waveprobe.c"
  if ! "$CC" -O2 -w -std=c99 -fPIC -shared -I "$ROOT/src" -o "$TMPD/waveprobe.so" \
        "$TMPD/waveprobe.c" -ldl 2>"$TMPD/cc.log"; then
    echo "wave_parallel: SKIPPED -- the demand-root probe did not compile ($(head -1 "$TMPD/cc.log"))"
    echo "wave_parallel: the threaded path is NOT proven by this run"
    exit 0
  fi
  PROBE="$TMPD/waveprobe.so"
else
  echo "wave_parallel: SKIPPED -- no cc/gcc to build the demand-root probe"
  echo "wave_parallel: the threaded path is NOT proven by this run"
  exit 0
fi

wide8=0
for f in $PROGS; do
  [ -f "$f" ] || continue

  # ---- (c) the program's own std: neither a wide wave nor a thread may move the answer --------
  serial=$(timeout 300 "$LIN_BIN" -t 1 "$f" 2>/dev/null || true)
  if [ -z "$serial" ]; then bad "$f: no output at -t 1"; continue; fi
  for t in 2 4 8; do
    off=$(timeout 300 "$LIN_BIN" -t "$t" "$f" 2>/dev/null || true)
    [ "$off" = "$serial" ] || bad "$f -t $t: output differs from -t 1"
    on=$(LIN_WAVE_PROBE=$WANT LD_PRELOAD="$PROBE" timeout 300 "$LIN_BIN" -t "$t" "$f" 2>/dev/null || true)
    [ "$on" = "$serial" ] || bad "$f -t $t: a widened wave changed the answer (std loaded)"
  done

  # ---- (a) OFF: demand only -- width 1, threaded path never entered, at every thread count ----
  free=$(LIN_STD="$EMPTY" timeout 300 "$LIN_BIN" -t 1 "$f" 2>/dev/null || true)
  for t in 1 2 4 8; do
    off=$(LIN_STD="$EMPTY" LIN_WAVE_STATS=1 timeout 300 "$LIN_BIN" -t "$t" "$f" 2>/tmp/wave_off.err || true)
    [ "$off" = "$free" ] || { bad "$f -t $t (no caller): output differs from -t 1"; continue; }
    w=$(field max < /tmp/wave_off.err); b=$(field par_batches < /tmp/wave_off.err)
    [ "$w" = "1" ] || bad "$f -t $t (no caller): wave width $w, expected 1 -- demand-only must not widen a wave"
    [ "$b" = "0" ] || bad "$f -t $t (no caller): the threaded path ran ($b batches) with no widening caller"
  done

  # ---- (b) ON: the wave widens, and the dispatcher opens exactly at the gate -------------------
  LIN_WAVE_PROBE=$WANT LD_PRELOAD="$PROBE" LIN_STD="$EMPTY" LIN_WAVE_STATS=1 \
    timeout 300 "$LIN_BIN" -t 1 "$f" >/tmp/wave_on.out 2>/tmp/wave_on.err || true
  serial_w=$(field max < /tmp/wave_on.err); b1=$(field par_batches < /tmp/wave_on.err)
  [ "${serial_w:-0}" -ge 4 ] || bad "$f: the demand roots did not widen the wave (max width ${serial_w:-none}, expected >= 4)"
  [ "${b1:-0}" = "0" ] || bad "$f -t 1: the threaded path ran with ONE thread"

  for t in 2 4 8; do
    LIN_WAVE_PROBE=$WANT LD_PRELOAD="$PROBE" LIN_STD="$EMPTY" LIN_WAVE_STATS=1 \
      timeout 300 "$LIN_BIN" -t "$t" "$f" >/tmp/wave_t.out 2>/tmp/wave_t.err || true
    [ "$(cat /tmp/wave_t.out)" = "$(cat /tmp/wave_on.out)" ] ||
      { bad "$f -t $t: a widened wave differs from -t 1"; continue; }
    b=$(field par_batches < /tmp/wave_t.err); p=$(field par_pairs < /tmp/wave_t.err)
    if [ "${serial_w:-0}" -ge $((GATE * t)) ]; then
      if [ "${b:-0}" -lt 1 ] || [ "${p:-0}" -lt 1 ]; then
        bad "$f -t $t: a wave of $serial_w pairs must reach the dispatcher ($b batches, $p pairs)"
      else
        pass=$((pass+1))
        if [ "$t" = 8 ]; then wide8=1; fi
      fi
    elif [ "${b:-0}" != "0" ]; then
      bad "$f -t $t: the dispatcher ran on a wave of $serial_w pairs, below the measured gate (4*$t)"
    fi
  done
  pass=$((pass+1))
done

# The 8-thread case is a requirement of its own: it needs a wave of >= 32 pairs, which only a
# program with a wide demand frontier reaches (nqueens 190, tseitin 121 -- measured).
[ "$wide8" = 1 ] || bad "no program reached the gate at -t 8: the 8-thread dispatcher is unproven"

if [ "$fail" -eq 0 ]; then
  echo "wave_parallel: OK ($pass checks: no wave widens and no thread is dispatched without a caller that"
  echo "               declares demand roots; with $WANT demand roots the wave widens to >= 4, the dispatcher"
  echo "               opens exactly at np >= 4*nth (including -t 8), and every run at every thread count --"
  echo "               widened or not, with the standard library or without -- is byte-identical to -t 1)"
else
  echo "wave_parallel: $fail problem(s), $pass passed"
fi
exit $fail
