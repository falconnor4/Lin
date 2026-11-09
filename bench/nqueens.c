#include <stdio.h>
static long place(long all, long cols, long d1, long d2, long avail) {
  if (avail == 0) return 0;
  long bit = avail & -avail, nc = cols | bit, n1 = (d1 | bit) << 1, n2 = (d2 | bit) >> 1;
  long here = nc == all ? 1 : place(all, nc, n1, n2, all & ~(nc | n1 | n2));
  return here + place(all, cols, d1, d2, avail ^ bit);
}
int main(void) { printf("%ld\n", place(16383, 0, 0, 0, 16383)); return 0; }
