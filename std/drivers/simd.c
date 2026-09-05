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
    fprintf(stderr, "[simd] executing %d wavefront redexes across %d vector blocks (SIMD-%d)\n",
            np, (np + SIMD_WIDTH - 1) / SIMD_WIDTH, SIMD_WIDTH);

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

    #pragma GCC ivdep
    for (int k = 0; k < blk_len; k++) {
      int idx = (b + k) * 2;
      Port p1 = curr[idx], p2 = curr[idx + 1];
      if (p1.node < 0 || p2.node < 0 || n->dead[p1.node] || n->dead[p2.node] || p1.port || p2.port) continue;
      if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
      if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port) continue;

      if (net_interact(n, p1, p2)) {
        batch_changed++;
        n->steps++;
      }
    }
  }

  free(curr);
  *changed += batch_changed;
  return 1;
}

LinDriver lin_simd_driver = {"simd", simd_reduce_wave};


