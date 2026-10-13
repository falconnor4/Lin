#include "lin.h"
#include <stdlib.h>

#define MOD 1000000007LL

static long long modpow(long long a, long long e) {
  long long r = 1;
  while (e) {
    if (e & 1) r = r * a % MOD;
    a = a * a % MOD;
    e >>= 1;
  }
  return r;
}

#define NXT(y) (n->wire[y].node < 0 ? -1 : n->wire[y].node * 3 + n->wire[y].port)
long long goi_det(Net *n) {
  int d = n->nn * 3;
  int *mark = calloc((size_t)d, sizeof *mark);
  long long det = 1; int tid = 0;
  for (int i = 0; i < d; i++) {
    if (mark[i]) continue;
    tid++;
    int k = 0, x = i;
    while (x >= 0 && mark[x] == 0) { mark[x] = tid; k++; x = NXT(x); }
    if (x >= 0 && mark[x] == tid) {                    /* this trail closes on itself: a cycle of length c */
      int c = 1; for (int y = NXT(x); y != x; y = NXT(y)) c++;
      for (int y = x; ; ) { mark[y] = -1; y = NXT(y); if (y == x) break; }
      det = det * modpow(2, k - c) % MOD * ((modpow(2, c) - 1 + MOD) % MOD) % MOD;
    } else {
      det = det * modpow(2, k) % MOD;                  /* a path, or a chain merging into a counted part */
    }
  }
  free(mark);
  return det;
}
