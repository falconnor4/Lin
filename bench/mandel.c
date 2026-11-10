#include <stdio.h>
static long iter(double cr, double ci, double zr, double zi, long k) {
  for (; k != 0; k--) {
    if (4.0 < zr * zr + zi * zi) return k;
    double nr = zr * zr - zi * zi + cr; zi = 2.0 * (zr * zi) + ci; zr = nr;
  }
  return 0;
}
int main(void) {
  long acc = 0;
  for (long y = 800; y > 0; y--)
    for (long x = 1000; x > 0; x--) acc += iter(x * 0.003 - 2.0, y * 0.003 - 1.2, 0.0, 0.0, 200);
  printf("%ld\n", acc); return 0;
}
