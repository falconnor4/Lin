/* reverse-complement (Computer Language Benchmarks Game): a DNA sequence of 1,000,000 letters, drawn by the
   benchmark's generator, is reversed and each letter replaced by its complement.  The answer is a checksum of
   the result, each letter with its position. */
#include <stdio.h>
#include <stdlib.h>
static char letter(long s) { return s < 42403 ? 'a' : s < 70117 ? 'c' : s < 97768 ? 'g' : 't'; }
static char comp(char c) { return c == 'a' ? 't' : c == 't' ? 'a' : c == 'c' ? 'g' : c == 'g' ? 'c' : c; }
int main(void) {
  long n = 1000000, seed = 42; char *s = malloc((size_t)n), *r = malloc((size_t)n);
  for (long i = 0; i < n; i++) { seed = (seed * 3877 + 29573) % 139968; s[i] = letter(seed); }
  for (long i = 0; i < n; i++) r[i] = comp(s[n - 1 - i]);
  long sum = 0;
  for (long pos = 0; pos < n; pos++) sum += (long)r[pos] * (pos % 97 + 1);
  printf("%ld\n", sum); free(s); free(r); return 0;
}
