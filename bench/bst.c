/* binary search tree: insert N keys (i * 37 mod 1009), then sum keys weighted by depth */
#include <stdio.h>
#include <stdlib.h>
typedef struct T { long k; struct T *l, *r; } T;
static T *ins(long x, T *t) {
  if (!t) { t = malloc(sizeof *t); t->k = x; t->l = t->r = NULL; return t; }
  if (x < t->k) t->l = ins(x, t->l); else t->r = ins(x, t->r);
  return t;
}
static long walk(T *t, long d) { return t ? t->k * d + walk(t->l, d + 1) + walk(t->r, d + 1) : 0; }
int main(void) { T *t = NULL; for (long i = 20; i > 0; i--) t = ins(i * 37 % 1009, t); printf("%ld\n", walk(t, 1)); return 0; }
