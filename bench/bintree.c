/* binary-trees: build a complete tree of depth 20 and count its nodes */
#include <stdio.h>
#include <stdlib.h>
typedef struct T { struct T *l, *r; } T;
static T *make(long d) { if (d == 0) return NULL; T *t = malloc(sizeof *t); t->l = make(d - 1); t->r = make(d - 1); return t; }
static long check(T *t) { if (!t) return 1; return 1 + check(t->l) + check(t->r); }
int main(void) { printf("%ld\n", check(make(20))); return 0; }
