/* The same program: naive Fibonacci. */
#include <stdio.h>
static long fib(long n) { return n <= 1 ? n : fib(n - 1) + fib(n - 2); }
int main(void) { printf("%ld\n", fib(14)); return 0; }
