#include "lin.h"
#include <stdlib.h>
#include <string.h>

static Net *N;

static Port wire(Port p) { return N->wire[p.node * 3 + p.port]; }

/* follow DUP principal chains to the value a port actually carries */
static Port dup_resolve(Port p) {
  for (int i = 0; i < 100000; i++) {
    if (p.node < 0 || p.node >= N->nn || N->tag[p.node] != DUP) return p;
    p = wire((Port){p.node, 0});
  }
  return p;
}

/* is there a live DUP reachable from the root?  if so the net is a shared
   croissant that must be expanded before structural readback */
static int live_dup_reachable(Net *n) {
  int *q = malloc(sizeof(int) * (size_t)(n->nn + 1));
  unsigned char *vis = calloc((size_t)n->nn, 1);
  int qh = 0, qt = 0;
  Port r = n->wire[0];
  if (r.node < 0) { free(q); free(vis); return 0; }
  q[qt++] = r.node;
  vis[r.node] = 1;
  while (qh < qt) {
    int i = q[qh++];
    if (n->tag[i] == DUP) { free(q); free(vis); return 1; }
    for (int p = 0; p < 3; p++) {
      Port w = n->wire[i * 3 + p];
      if (w.node < 0 || w.node >= n->nn || n->dead[w.node]) continue;
      if (!vis[w.node]) {
        vis[w.node] = 1;
        q[qt++] = w.node;
      }
    }
  }
  free(q);
  free(vis);
  return 0;
}

/* The std library Curry-encodes data with reserved binder names: numerals as
   \_cf. \_cx. ..., booleans as \_bt. \_bf. .... These names are the only type
   discipline a plain net exposes (church-0 and boolean-false are the very
   same lambda term).  We recognize an encoding only when its names match;
   anything else prints as a plain lambda. */

/* structural Church numeral: \_cf. \_cx. (_cf^k ...)  =>  k.  Runs on the
   structural (croissant-free) path only: the body is a chain of _cf-apps
   whose fun slot resolves to the head variable, ending at the inner variable
   (or an erased tail, which still counts as the same numeral). */
static long church_count(int node) {
  if (N->tag[node] != LAM) return -1;
  if (strcmp(N->name[node], "_cf")) return -1;
  Port bf = wire((Port){node, 2});
  if (bf.node < 0 || bf.port != 0 || N->tag[bf.node] != LAM) return -1;
  int inner = bf.node;
  if (strcmp(N->name[inner], "_cx")) return -1;
  Port cur = wire((Port){inner, 2});
  long count = 0;
  while (count < 100000000) {
    cur = dup_resolve(cur);
    if (cur.node == inner && cur.port == 1) return count;
    if (cur.node < 0) return count;            /* dangling tail: erased x */
    if (N->dead[cur.node] || N->tag[cur.node] == ERA) return count;
    if (N->tag[cur.node] != APP) return -1;
    Port fun = dup_resolve(wire((Port){cur.node, 0}));
    if (!(fun.node == node && fun.port == 1)) return -1;
    count++;
    cur = wire((Port){cur.node, 2});
  }
  return -1;
}

/* structural boolean: \_bt. \_bf. body, body resolving to _bt (true) or
   _bf (false) */
static int bool_detect(int node) {
  if (N->tag[node] != LAM) return -1;
  if (strcmp(N->name[node], "_bt")) return -1;
  Port bf = wire((Port){node, 2});
  if (bf.node < 0 || bf.port != 0 || N->tag[bf.node] != LAM) return -1;
  if (strcmp(N->name[bf.node], "_bf")) return -1;
  Port b = dup_resolve(wire((Port){bf.node, 2}));
  if (b.node == node && b.port == 1) return 1;
  if (b.node == bf.node && b.port == 1) return 0;
  return -1;
}

static void print_port(Port p, int depth) {
  if (depth > 100000 || p.node < 0 || p.node >= N->nn) {
    putchar('?');
    return;
  }
  if (N->dead[p.node]) {
    putchar('_');
    return;
  }
  switch (N->tag[p.node]) {
  case ROOT:
    print_port(wire(p), depth + 1);
    return;
  case ERA:
    putchar('_');
    return;
  case DUP:
    print_port(wire((Port){p.node, 0}), depth + 1);
    return;
  case APP:
    putchar('(');
    print_port(wire((Port){p.node, 0}), depth + 1);
    putchar(' ');
    print_port(wire((Port){p.node, 2}), depth + 1);
    putchar(')');
    return;
  case LAM:
    if (p.port == 1) { /* a variable occurrence */
      fputs(N->name[p.node], stdout);
      return;
    }
    if (p.port == 0) {
      long v = church_count(p.node);
      if (v >= 0) {
        printf("%ld", v);
        return;
      }
      int b = bool_detect(p.node);
      if (b >= 0) {
        fputs(b ? "true" : "false", stdout);
        return;
      }
      fputs("(\\", stdout);
      fputs(N->name[p.node], stdout);
      putchar(' ');
      print_port(wire((Port){p.node, 2}), depth + 1);
      putchar(')');
      return;
    }
    print_port(wire(p), depth + 1);
    return;
  }
}

/* readback: structural print of a fully reduced net.  Returns 1 when the
   head is a shared croissant (live DUP reachable from the root) whose value
   must be decoded from the expanded source term by the normal-order
   decoder; returns 0 when the net was printed directly. */
int net_print(Net *n) {
  N = n;
  if (live_dup_reachable(n)) return 1;
  print_port(wire((Port){0, 0}), 0);
  return 0;
}