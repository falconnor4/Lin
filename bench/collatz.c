#include <stdio.h>
static long steps(long n, long acc) { while (n > 1) { n = (n & 1) == 0 ? n >> 1 : 3 * n + 1; acc++; } return acc; }
int main(void) { long m = 0; for (long i = 999999; i > 0; i--) { long s = steps(i, 0); if (s > m) m = s; } printf("%ld\n", m); return 0; }
