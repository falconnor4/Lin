/* The same program: tail-recursive accumulation. */
#include <stdio.h>
static long loopi(long i, long acc) { return i == 0 ? acc : loopi(i - 1, acc + i); }
int main(void) { printf("%ld\n", loopi(60, 0)); return 0; }
