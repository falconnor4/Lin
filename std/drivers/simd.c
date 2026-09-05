#include "../../src/lin.h"
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define SIMD_WIDTH 8
#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])

static int simd_reduce_wave(Net *n, long limit, int *changed) {
  int wave_cnt = n->atop;
  if (wave_cnt <= 0 || n->steps >= limit) return 0;

  Port *curr = malloc((size_t)wave_cnt * sizeof(Port));
  memcpy(curr, n->act, (size_t)wave_cnt * sizeof(Port));
  n->atop = 0;

  int batch_changed = 0;
  int np = wave_cnt / 2;
  if (getenv("LIN_SIMD_DEBUG"))
    fprintf(stderr, "[simd] vectorizing %d wavefront redexes (%d blocks)\n", np, (np + SIMD_WIDTH - 1) / SIMD_WIDTH);

  // Process in SIMD vector blocks of SIMD_WIDTH
  for (int b = 0; b < np; b += SIMD_WIDTH) {
    if (n->steps >= limit) {
      for (int j = b * 2; j < wave_cnt; j += 2) {
        if (n->atop + 2 > n->actcap)
          n->act = realloc(n->act, (size_t)(n->actcap = n->actcap ? n->actcap * 2 : 256) * sizeof(Port));
        n->act[n->atop++] = curr[j]; n->act[n->atop++] = curr[j + 1];
      }
      break;
    }

    int blk_len = (b + SIMD_WIDTH <= np) ? SIMD_WIDTH : (np - b);

    for (int k = 0; k < blk_len; k++) {
      int idx = (b + k) * 2;
      Port p1 = curr[idx], p2 = curr[idx + 1];
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node]) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port || p1.port || p2.port) continue;

      int u = p1.node, v = p2.node;
      int tu = n->tag[u], tv = n->tag[v];

      // Fast-path SIMD lane for Beta-reduction (LAM x APP)
      if ((tu == LAM && tv == APP) || (tu == APP && tv == LAM)) {
        int lam_node = (tu == LAM) ? u : v;
        int app_node = (tu == LAM) ? v : u;
        Port lv = WIRE(n, ((Port){lam_node, 1})), lb = WIRE(n, ((Port){lam_node, 2}));
        Port ar = WIRE(n, ((Port){app_node, 1})), aa = WIRE(n, ((Port){app_node, 2}));
        n->dead[lam_node] = 1; n->dead[app_node] = 1;
        if (lv.node == lam_node && lv.port == 2 && lb.node == lam_node && lb.port == 1) {
          net_link(n, aa, ar, 1);
        } else {
          net_link(n, lv, aa, 1);
          net_link(n, lb, ar, 1);
        }
        batch_changed++;
        n->steps++;
        continue;
      }

      // Confluent interaction lane
      if (net_interact(n, p1, p2)) batch_changed++;
      n->steps++;
    }
  }

  free(curr);
  *changed += batch_changed;
  return 1;
}

LinDriver lin_simd_driver = {"simd", simd_reduce_wave};
