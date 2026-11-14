/* fannkuch-redux (Computer Language Benchmarks Game), n = 9: every permutation of 1..n in the benchmark's order;
   for each, how many prefix reversals bring 1 to the front.  The answer is checksum * 100 + the most flips. */
#include <stdio.h>
int main(void) {
  enum { N = 9 };
  int perm[N], perm1[N], count[N], r = N, maxflips = 0; long checksum = 0, permcount = 0;
  for (int i = 0; i < N; i++) perm1[i] = i;
  for (;;) {
    while (r != 1) { count[r - 1] = r; r--; }
    for (int i = 0; i < N; i++) perm[i] = perm1[i];
    int flips = 0, k;
    while ((k = perm[0]) != 0) {
      for (int i = 0, j = k; i < j; i++, j--) { int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
      flips++;
    }
    if (flips > maxflips) maxflips = flips;
    checksum += permcount % 2 == 0 ? flips : -flips;
    for (;;) {
      if (r == N) { printf("%ld\n", checksum * 100 + maxflips); return 0; }
      int p0 = perm1[0];
      for (int i = 0; i < r; i++) perm1[i] = perm1[i + 1];
      perm1[r] = p0;
      if (--count[r] > 0) break;
      r++;
    }
    permcount++;
  }
}
