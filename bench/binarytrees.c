/* binary-trees (Computer Language Benchmarks Game), max depth 16: the sum of every check */
#include <stdio.h>
#include <stdlib.h>
typedef struct T { struct T *l, *r; } T;
static T *make(int d) { T *t = malloc(sizeof *t); if (d == 0) { t->l = t->r = NULL; return t; } t->l = make(d - 1); t->r = make(d - 1); return t; }
static long check(T *t) { if (!t) return 0; long c = 1 + check(t->l) + check(t->r); free(t); return c; }
int main(void) {
  int mx = 16; long sum = check(make(mx + 1));
  T *longlived = make(mx);
  for (int d = 4; d <= mx; d += 2) { long it = 1L << (mx - d + 4), acc = 0; for (long i = 0; i < it; i++) acc += check(make(d)); sum += acc; }
  sum += check(longlived);
  printf("%ld\n", sum); return 0;
}
