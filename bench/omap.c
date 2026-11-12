/* an ordered map (red-black tree, Okasaki's insert, mutable): 200,000 inserts, then a lookup of each */
#include <stdio.h>
#include <stdlib.h>
typedef struct N { int red; long k, v; struct N *l, *r; } N;
static N *mk(int red, N *l, long k, long v, N *r) { N *t = malloc(sizeof *t); t->red = red; t->l = l; t->k = k; t->v = v; t->r = r; return t; }
static int R(N *t) { return t && t->red; }
static N *bal(N *t) {   /* the four red-red shapes, rotated */
  if (t->red) return t;
  N *a, *b, *c, *x, *y, *z;
  if (R(t->l) && R(t->l->l)) { z = t; y = t->l; x = y->l; a = x->l; b = x->r; c = y->r; z->l = c; }
  else if (R(t->l) && R(t->l->r)) { z = t; x = t->l; y = x->r; a = x->l; b = y->l; c = y->r; z->l = c; }
  else if (R(t->r) && R(t->r->l)) { x = t; z = t->r; y = z->l; a = x->l; b = y->l; c = y->r; z->l = c; }
  else if (R(t->r) && R(t->r->r)) { x = t; y = t->r; z = y->r; a = x->l; b = y->l; c = z->l; }
  else return t;
  N *X = x, *Z = z;
  X->red = 0; X->l = a; X->r = b; Z->red = 0; Z->l = c;
  if (Z == t || Z == t->l) {} 
  y->red = 1; y->l = X; y->r = Z; return y;
}
static N *ins(N *t, long k, long v) {
  if (!t) return mk(1, 0, k, v, 0);
  if (k < t->k) t->l = ins(t->l, k, v); else if (k > t->k) t->r = ins(t->r, k, v); else { t->v = v; return t; }
  return bal(t);
}
static long get(N *t, long k) { while (t) { if (k < t->k) t = t->l; else if (k > t->k) t = t->r; else return t->v; } return 0; }
int main(void) {
  N *m = 0; long s = 0;
  for (long i = 200000; i > 0; i--) { m = ins(m, i * 7919 % 1000003, i); m->red = 0; }
  for (long i = 200000; i > 0; i--) s += get(m, i * 7919 % 1000003);
  printf("%ld\n", s); return 0;
}
