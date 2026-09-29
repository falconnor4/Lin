#!/usr/bin/env bash
# ============================================================================
# DEMAND CARRY: a build-time claim about what will be OBSERVED survives into the
# artifact, and the artifact runs wider for it -- with the producer gone.
# ----------------------------------------------------------------------------
# `net_save_line` does not serialize `act` (a load rebuilds it), and v7 writes the
# DEMAND ROOTS beside it, because they are the other half of the same scheduling
# state: with no roots an artifact re-derives ROOT alone and every wave can ever
# fire at most ONE pair.  This test pins the whole path:
#
#   1. a PASS (a driver with an `.aot` hook, compiled from a string into scratch,
#      never shipped) publishes demand roots on the net `lin build` hands it;
#   2. the artifact carries them in its own bytes;
#   3. run WITHOUT the pass present -- no LD_PRELOAD, no driver -- it still runs
#      wider than the control that was built without one.
#
# WHAT IT DOES NOT CLAIM: that this makes anything faster.  A blanket pass names
# roots on a pre-reduction net, most of which do not yield a coincident redex
# later, so the width it buys (measured: 4) does not reach `np >= 4 * nth`
# (16 at -t 4) and the threaded path is still not dispatched.  A width of one
# pair per root is the design: the walk stops at the first redex on each path so
# that a cycle reduces when demanded instead of unrolling.  What this pins is the
#   MECHANISM -- claim, carry, honour -- and that it changes the schedule and not the answer:
#   byte-identical output, and work that never rises (it may fall, when an earlier
#   schedule erases a subgraph before its redexes fire).
# ============================================================================
set -e
. "$(dirname "$0")/common.sh"
lin_test_env "${1:-}" "${2:-}" || exit 1

PROG=test/bench_runtime.lin
N=20
ANSWER=$(( N * (N + 1) / 2 ))
pass=0; fail=0
bad() { fail=$((fail+1)); echo "FAIL $*"; }
ok()  { pass=$((pass+1)); }

CC=$(command -v cc || command -v gcc || true)
TMPD=$(mktemp -d)
trap 'rm -rf "$TMPD"' EXIT
if [ -z "$CC" ]; then
  echo "demand_carry: SKIPPED -- no C compiler to build the pass probe"
  echo "demand_carry: the carried-demand path is NOT proven by this run"
  exit 0
fi

# ---------------- the producing pass, built from a string ----------------
cat >"$TMPD/pass.c" <<'EOF'
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <dlfcn.h>
/* A caller that will OBSERVE several ports, at BUILD time: it names live, node-disjoint redexes of the
   net the build hands it and states their principal ports are observed.  `lin_demand` is the whole
   mechanism -- the core decides what may run at once, and nothing here knows what the program means. */
static int declared;
static int live(const Net *n, int v) { return v >= 0 && v < n->nn && !n->dead[v]; }
static int rp_aot(Net *n, void *st, const Term *t, const Scheme *sch,
                  Port (*node_of)(void *, const Term *), void *ctx) {
  (void)st; (void)t; (void)sch; (void)node_of; (void)ctx;
  unsigned char *taken = calloc((size_t)n->nn, 1);   /* sized to the net, so there is no cap to get wrong */
  if (!taken) return 0;
  for (int u = 1; u < n->nn; u++) {
    int tu = n->tag[u];
    if (tu != LAM && tu != APP && tu != DUP) continue;
    int w = n->wire[u * 3].node;
    if (n->wire[u * 3].port != 0 || w <= u || !live(n, w)) continue;
    int tw = n->tag[w];
    if (!((tu == LAM && (tw == APP || tw == DUP)) || (tu != LAM && (tw == LAM || tw == DUP)))) continue;
    if (n->wire[w * 3].node != u || n->wire[w * 3].port != 0) continue;
    if (taken[u] || taken[w]) continue;
    taken[u] = 1; taken[w] = 1;
    lin_demand(n, (Port){u, 0}); lin_demand(n, (Port){w, 0});
    declared++;
  }
  free(taken);
  return declared > 0;
}
LinDriver lin_rootprobe_driver = {
  .magic = LIN_DRIVER_MAGIC, .abi = LIN_DRIVER_ABI, .net_size = (uint32_t)sizeof(Net),
  .size = (uint32_t)sizeof(LinDriver),
  .name = "rootprobe", .description = "a build-time pass publishing demand roots",
  .caps = LIN_CAP_PREEMPT, .priority = 1, .wants = LIN_WANT_AOT, .aot = rp_aot,
};
__attribute__((constructor)) static void rp_init(void) {
  void (*add)(LinDriver *) = (void (*)(LinDriver *))dlsym(RTLD_DEFAULT, "lin_driver_add");
  if (add) add(&lin_rootprobe_driver);
}
EOF
if ! "$CC" -O2 -w -std=c99 -fPIC -shared -I "$ROOT/src" -o "$TMPD/pass.so" "$TMPD/pass.c" -ldl 2>"$TMPD/cc.log"; then
  echo "demand_carry: SKIPPED -- the pass probe did not compile ($(head -1 "$TMPD/cc.log"))"
  echo "demand_carry: the carried-demand path is NOT proven by this run"
  exit 0
fi

# ---------------- build both artifacts: with the claim, and without it ----------------
LD_PRELOAD="$TMPD/pass.so" BENCH_N= "$LIN_BIN" build "$PROG" -o "$TMPD/carried" >"$TMPD/build1.log" 2>&1 \
  || bad "the build with the producing pass failed"
BENCH_N= "$LIN_BIN" build "$PROG" -o "$TMPD/control" >"$TMPD/build2.log" 2>&1 \
  || bad "the control build failed"

run() {  # run <artifact> <threads> -> "<output>|<max>|<fired>", all three read from the run itself
  BENCH_N=$N LIN_WAVE_STATS=1 timeout 300 "$1" -t "$2" >"$TMPD/out" 2>"$TMPD/err"
  local out fired max
  out=$(tail -1 "$TMPD/out")
  read -r fired max <<<"$(sed -n 's/.*fired=\([0-9]*\) max=\([0-9]*\).*/\1 \2/p' "$TMPD/err" | tail -1)"
  printf '%s|%s|%s' "$out" "${max:-0}" "${fired:-0}"
}

CAR1=$(run "$TMPD/carried" 1); CAR4=$(run "$TMPD/carried" 4)
CTL1=$(run "$TMPD/control" 1)

# The producer is now GONE: nothing below can have used it, so a run that is still wider proves the
# claim travelled in the artifact's own bytes rather than in a driver's live state.
rm -f "$TMPD/pass.so"

# ---------------- what is pinned ----------------
[ "${CAR1%%|*}" = "=> $ANSWER" ] && ok || bad "the carried artifact answered '${CAR1%%|*}' where the interpreter says '=> $ANSWER'"
[ "$CAR4" = "$CAR1" ] && ok || bad "the carried artifact is not thread-identical: -t 1 '$CAR1' vs -t 4 '$CAR4'"
[ "${CTL1%%|*}" = "=> $ANSWER" ] && ok || bad "the control artifact answered '${CTL1%%|*}' where the interpreter says '=> $ANSWER'"

CMAX=$(echo "$CAR1" | cut -d'|' -f2); MAX=$(echo "$CTL1" | cut -d'|' -f2)
[ "${CMAX:-0}" -gt "${MAX:-0}" ] && ok || bad "the carried claim did not widen the artifact (max ${CMAX:-?} vs control ${MAX:-?})"
[ "${MAX:-0}" = "1" ] && ok || bad "an artifact with no roots should fire one pair per wave, saw max=${MAX:-?}"
# The work may FALL (a schedule that fires earlier can erase a subgraph before its redexes fire) but it
# must never RISE: a claim that adds firings is a claim about work nobody asked for.
CF=$(echo "$CAR1" | cut -d'|' -f3); CT=$(echo "$CTL1" | cut -d'|' -f3)
[ "${CF:-0}" -le "${CT:-0}" ] && ok \
  || bad "the claim made the artifact do MORE work: fired $CF against the control's $CT"

[ -f "$TMPD/pass.so" ] && bad "the producer was not deleted before the runs" || ok

if [ "$fail" -eq 0 ]; then
  echo "demand_carry: OK ($pass checks: claim carried in the artifact, width ${MAX} -> ${CMAX}, thread-identical, work not increased)"
else
  echo "demand_carry: $fail problem(s)"
  exit 1
fi
