/* lists: the squares of 0..999,999, the even ones kept, summed (a linked list: map, filter, fold) */
#include <stdio.h>
#include <stdlib.h>
typedef struct L { long h; struct L *t; } L;
static L *cons(long h, L *t) { L *c = malloc(sizeof *c); c->h = h; c->t = t; return c; }
int main(void) {
  L *r = 0; for (long i = 999999; i >= 0; i--) r = cons(i, r);
  L *m = 0, **mp = &m; for (L *p = r; p; p = p->t) { *mp = cons(p->h * p->h, 0); mp = &(*mp)->t; }
  L *f = 0, **fp = &f; for (L *p = m; p; p = p->t) if (p->h % 2 == 0) { *fp = cons(p->h, 0); fp = &(*fp)->t; }
  long s = 0; for (L *p = f; p; p = p->t) s += p->h;
  printf("%ld\n", s); return 0;
}
