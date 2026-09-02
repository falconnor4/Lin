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

/* GoI invariant: det(2I - A) mod p over the node-port adjacency */
long long goi_det(Net *n) {
  if (n->nn > 400) return -1;
  int d = n->nn * 3;
  long long *m = calloc((size_t)d * d, sizeof(long long));
  for (int i = 0; i < d; i++) m[(size_t)i * d + i] = 2;
  for (int i = 0; i < n->nn; i++)
    for (int p = 0; p < 3; p++) {
      Port w = n->wire[i * 3 + p];
      if (w.node < 0) continue;
      size_t rc = (size_t)(i * 3 + p) * d + w.node * 3 + w.port;
      m[rc] = (m[rc] - 1 + MOD) % MOD;
    }
  for (int i = 0; i + 1 < n->atop; i += 2) {
    int r = n->act[i].node * 3 + n->act[i].port;
    int c = n->act[i + 1].node * 3 + n->act[i + 1].port;
    m[(size_t)r * d + c] = (m[(size_t)r * d + c] - 1 + MOD) % MOD;
    m[(size_t)c * d + r] = (m[(size_t)c * d + r] - 1 + MOD) % MOD;
  }
  long long det = 1;
  for (int i = 0; i < d; i++) {
    int piv = -1;
    for (int j = i; j < d; j++)
      if (m[(size_t)j * d + i]) {
        piv = j;
        break;
      }
    if (piv < 0) {
      free(m);
      return 0;
    }
    if (piv != i) {
      for (int k = 0; k < d; k++) {
        long long t = m[(size_t)i * d + k];
        m[(size_t)i * d + k] = m[(size_t)piv * d + k];
        m[(size_t)piv * d + k] = t;
      }
      det = (MOD - det) % MOD;
    }
    long long pv = m[(size_t)i * d + i];
    det = det * pv % MOD;
    long long inv = modpow(pv, MOD - 2);
    for (int j = i + 1; j < d; j++) {
      long long f = m[(size_t)j * d + i] * inv % MOD;
      if (!f) continue;
      for (int k = i; k < d; k++)
        m[(size_t)j * d + k] =
            (m[(size_t)j * d + k] - f * m[(size_t)i * d + k] % MOD + MOD) %
            MOD;
    }
  }
  free(m);
  return det;
}
