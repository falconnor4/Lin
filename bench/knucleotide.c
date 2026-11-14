/* k-nucleotide (Computer Language Benchmarks Game): in a DNA sequence of 250,000 letters drawn by the
   benchmark's generator, count every fragment of length 1 and 2 and five given fragments, with a map from
   fragment to count.  The answer combines the number of distinct fragments of each length and the counts. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { long *key, *val; long cap, n; } Map;
static void put(Map *m, long k);
static void grow(Map *m) {
  Map o = *m; m->cap = o.cap ? o.cap * 2 : 64; m->n = 0;
  m->key = malloc((size_t)m->cap * sizeof(long)); m->val = calloc((size_t)m->cap, sizeof(long));
  for (long i = 0; i < m->cap; i++) m->key[i] = -1;
  for (long i = 0; i < o.cap; i++) if (o.key[i] >= 0) { long v = o.val[i]; put(m, o.key[i]); long h = (long)((unsigned long)o.key[i] * 0x9E3779B97F4A7C15UL >> 20) & (m->cap - 1); while (m->key[h] != o.key[i]) h = (h + 1) & (m->cap - 1); m->val[h] = v; }
  free(o.key); free(o.val);
}
static void put(Map *m, long k) {
  if ((m->n + 1) * 2 > m->cap) grow(m);
  long h = (long)((unsigned long)k * 0x9E3779B97F4A7C15UL >> 20) & (m->cap - 1);
  while (m->key[h] >= 0 && m->key[h] != k) h = (h + 1) & (m->cap - 1);
  if (m->key[h] < 0) { m->key[h] = k; m->n++; }
  m->val[h]++;
}
static long get(const Map *m, long k) {
  if (!m->cap) return 0;
  long h = (long)((unsigned long)k * 0x9E3779B97F4A7C15UL >> 20) & (m->cap - 1);
  while (m->key[h] >= 0 && m->key[h] != k) h = (h + 1) & (m->cap - 1);
  return m->key[h] < 0 ? 0 : m->val[h];
}
static Map frags(const char *s, long n, int k) {
  Map m = {0}; long mask = (1L << (2 * k)) - 1, code = 0;
  for (long i = 0; i < n; i++) { code = ((code * 4) + s[i]) & mask; if (i + 1 >= k) put(&m, code); }
  return m;
}
static long code(const char *g) { long c = 0; for (; *g; g++) c = c * 4 + (*g == 'A' ? 0 : *g == 'C' ? 1 : *g == 'G' ? 2 : 3); return c; }
static long hits(const char *s, long n, const char *g) { Map m = frags(s, n, (int)strlen(g)); long r = get(&m, code(g)); free(m.key); free(m.val); return r; }
int main(void) {
  long n = 250000, seed = 42; char *s = malloc((size_t)n);
  for (long i = 0; i < n; i++) { seed = (seed * 3877 + 29573) % 139968; s[i] = seed < 42403 ? 0 : seed < 70117 ? 1 : seed < 97768 ? 2 : 3; }
  Map m1 = frags(s, n, 1), m2 = frags(s, n, 2);
  long r = 1000000 * (m1.n + m2.n) + get(&m1, 0) + get(&m2, 15)
         + hits(s, n, "GGT") + hits(s, n, "GGTA") + hits(s, n, "GGTATT") + hits(s, n, "GGTATTTTAATT") + hits(s, n, "GGTATTTTAATTTATAGT");
  printf("%ld\n", r); return 0;
}
