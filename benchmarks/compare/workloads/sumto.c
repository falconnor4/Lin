/* The same program: sum 1..N by non-tail recursion. */
#include <stdio.h>
static long sumto(long n) { return n == 0 ? 0 : n + sumto(n - 1); }
int main(void) { printf("%ld\n", sumto(25)); return 0; }
