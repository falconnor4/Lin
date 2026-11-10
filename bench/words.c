/* text: build a 1,000,000-character string of words (lengths 1..7, separated by one space), then count its words */
#include <stdio.h>
#include <stdlib.h>
int main(void) {
  long n = 1000000, w = 0; char *s = malloc((size_t)n + 1);
  for (long i = n; i > 0; i--) s[n - i] = (i % 8 == 0) ? ' ' : (char)('a' + i % 26);
  s[n] = 0;
  int in = 0;
  for (long i = 0; i < n; i++) { int sp = s[i] == ' ' || s[i] == '\n' || s[i] == '\t' || s[i] == '\r'; if (!sp && !in) w++; in = !sp; }
  printf("%ld\n", w); free(s); return 0;
}
