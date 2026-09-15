/* ============================================================================
 * Lin Standard Library: Canonical Driver Selftest (bit-exact differential)
 * ============================================================================
 * The canonical per-wave correctness oracle for DEVICE reducers — a shared,
 * reusable harness that any pd accelerator driver (GPU, NPU, remote device,
 * …) may call after it commits a wave of redexes.  It clones the host net,
 * replays the SAME redex list through the canonical concurrent host reducer
 * (`lin_reduce_wave_parallel`), and compares the committed `wire[]`/`dead[]`
 * against what the device wrote — bit-exactly.  This is the exact differential
 * that gpu.c's original `gpu_selftest` implemented; extracting it here makes
 * it a std-wide facility instead of a gpu-only blob, so a future device driver
 * gets the same oracle for free.
 *
 * The value-level contract (std/selftest.lin + test/driver_selftest.sh) is the
 * primary, portable correctness gate for ALL drivers; this header is the
 * stronger, per-wave, device-reduction depth on top of it (host-native reducers
 * like SIMD have no separate device state to compare, so value-equality from
 * the .lin corpus is their appropriate oracle).
 *
 * Usage (from a driver plugin's reduce step):
 *     static unsigned char dead_committed[MAXN];
 *     static Port wires_committed[MAXN*3];
 *     ... capture the device-committed wire[]/dead[] into those arrays ...
 *     lin_selftest_replay(n, redexes, nred,
 *                         wires_committed, dead_committed,
 *                         "GPU", "LIN_GPU_SELFTEST");
 * The routine only does work while the named env var is set; otherwise it is a
 * cheap no-op, so a driver may call it unconditionally.
 * ========================================================================== */
#include "../../src/lin.h"
#include <stdlib.h>
#include <stdio.h>

/* Accumulates a running tally across waves so a multi-wave reduction can report
   a summary, not just the first diff.  Not thread-safe; device drivers reduce
   waves on the host/host-side loop, so this matches the original gpu_selftest. */
static long dsh_selftest_runs = 0, dsh_selftest_mismatches = 0;

/* Replay `nred` fixed redexes (Port pairs in `redexes`, stride 2) on a host
   clone through the canonical wavefront reducer and diff the committed result
   (`wires`/`deads`, length `n->nn`, in the same layout net_reduce reads) against
   what the driver actually committed.  Env-gated on `env`.  Returns the number
   of mismatching nodes (0 == bit-exact). */
static inline int lin_selftest_replay(const Net *n, const Port *redexes, int nred,
                                      const Port *wires, const unsigned char *deads,
                                      const char *kind, const char *env) {
  if (!getenv(env)) return 0;
  dsh_selftest_runs++;

  /* Clone the host net and replay ONLY the same fixed redexes through the same
     concurrent wavefront reducer the base engine actually uses, so the oracle
     matches host reduction semantics (sequential net_interact would differ
     because concurrent reduction reorders). */
  Net *h = net_copy(n);
  Port *fp = malloc(sizeof(Port) * (size_t)nred * 2);
  if (!fp) { net_free(h); return 0; }
  for (int i = 0; i < nred; i++) { fp[i*2] = redexes[i*2]; fp[i*2+1] = redexes[i*2+1]; }
  int shadow = 0;
  lin_reduce_wave_parallel(h, fp, nred * 2, &shadow);
  free(fp);

  int bad = 0, didx = 0; long first = -1, firstp = -1;
  unsigned char gd8 = 0, hd8 = 0; Port gw0 = {-1,0}, hw0 = {-1,0};
  for (int i = 0; i < n->nn && !bad; i++) {
    if (deads[i] != h->dead[i]) {
      bad = 1; didx = 1; first = i; gd8 = deads[i]; hd8 = h->dead[i]; break;
    }
    for (int p = 0; p < 3; p++) {
      Port hw = h->wire[i*3+p], gw = wires[i*3+p];
      if (gw.node != hw.node || gw.port != hw.port) {
        bad = 1; first = i; firstp = p; gw0 = gw; hw0 = hw; break;
      }
    }
  }
  if (bad) {
    if (didx)
      fprintf(stderr, "[%s selftest] MISMATCH node %ld dead: driver=%u host=%u (replayed %d redexes)\n",
              kind, first, gd8, hd8, nred);
    else
      fprintf(stderr, "[%s selftest] MISMATCH node %ld port %ld: driver=(%d.%d) host=(%d.%d) (replayed %d redexes)\n",
              kind, first, firstp, gw0.node, gw0.port, hw0.node, hw0.port, nred);
  }
  dsh_selftest_mismatches += bad;
  net_free(h);
  /* Per-wave result is printed whenever the driver's selftest env is set, as
     the original gpu_selftest did. */
  fprintf(stderr, "[%s selftest] %s (run %ld, %ld/%ld waves mismatched)\n",
          kind, bad ? "MISMATCH" : "OK", dsh_selftest_runs,
          dsh_selftest_mismatches, dsh_selftest_runs);
  return bad;
}