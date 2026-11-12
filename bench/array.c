/* an array: a million random writes (i*7919 mod n), then a sum of every element by index */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  long n = 1000000, *a = calloc((size_t)n, sizeof *a), s = 0;
  for (long i = 0; i < n; i++) a[(i * 7919) % n] = i;
  for (long i = 0; i < n; i++) s += a[i];
  printf("%ld\n", s); free(a); return 0;
}
