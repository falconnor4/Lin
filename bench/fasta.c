/* fasta (Computer Language Benchmarks Game), n = 100,000: a repeated sequence of 2n letters, then 3n and 5n
   letters drawn by the benchmark's random generator from two weighted alphabets.  Nothing is printed: the
   answer is a checksum of every letter with its position. */
#include <stdio.h>
#include <string.h>
typedef struct { long c; double p; } Freq;
static const char *alu = "GGCCGGGCGCGGTGGCTCACGCCTGTAATCCCAGCACTTTGGGAGGCCGAGGCGGGCGGATCACCTGAGGTCAGGAGTTCGAGACCAGCCTGGCCAACATGGTGAAACCCCGTCTCTACTAAAAATACAAAAATTAGCCGGGCGTGGTGGCGCGCGCCTGTAATCCCAGCTACTCGGGAGGCTGAGGCAGGAGAATCGCTTGAACCCGGGAGGCGGAGGTTGCAGTGAGCCGAGATCGCGCCACTGCACTCCAGCCTGGGCGACAGAGCGAGACTCCGTCTCAAAAA";
static Freq iub[] = { {'a', 0.27}, {'c', 0.12}, {'g', 0.12}, {'t', 0.27}, {'B', 0.02}, {'D', 0.02}, {'H', 0.02}, {'K', 0.02}, {'M', 0.02},
  {'N', 0.02}, {'R', 0.02}, {'S', 0.02}, {'V', 0.02}, {'W', 0.02}, {'Y', 0.02} };
static Freq homo[] = { {'a', 0.3029549426680}, {'c', 0.1979883004921}, {'g', 0.1975473066391}, {'t', 0.3015094502008} };
static long pick(const Freq *t, int nt, double r) { double acc = 0.0; for (int i = 0; i < nt; i++) { acc = acc + t[i].p; if (r < acc || i == nt - 1) return t[i].c; } return 0; }
static long mix(long sum, long pos, long c) { return sum + c * (pos % 97 + 1); }
static long repeat(const char *src, long k) { long sum = 0, len = (long)strlen(src); for (long pos = 0; pos < k; pos++) sum = mix(sum, pos, src[pos % len]); return sum; }
static long random_(const Freq *t, int nt, long k, long *seed) {
  long sum = 0, s = *seed;
  for (long pos = 0; pos < k; pos++) { s = (s * 3877 + 29573) % 139968; sum = mix(sum, pos, pick(t, nt, (double)s / 139968.0)); }
  *seed = s; return sum + s;
}
int main(void) {
  long n = 100000, seed = 42;
  long s1 = repeat(alu, 2 * n);
  long s2 = random_(iub, 15, 3 * n, &seed);
  long s3 = random_(homo, 4, 5 * n, &seed);
  printf("%ld\n", s1 + s2 + s3); return 0;
}
