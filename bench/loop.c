#include <stdio.h>
int main(void) { long acc = 0; for (long i = 100000000; i > 0; i--) acc += (i * i) % 7; printf("%ld\n", acc); return 0; }
