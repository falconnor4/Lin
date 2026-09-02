#include "lin.h"
#include <stdlib.h>
#include <string.h>

static Net *N;

#define NONE ((Port){-1, -1})

static Port wire(Port p) { return N->wire[p.node * 3 + p.port]; }

static Port dup_resolve(Port p) {
  for (int i = 0; i < 1000; i++) {
    if (p.node < 0 || p.node >= N->nn || N->tag[p.node] != DUP) return p;
    p = wire((Port){p.node, 0});
  }
  return p;
}

/* structural Church numeral check: \_cf. \_cx. f (f (... (f x))) */
static long church_structural(int node) {
  if (N->tag[node] != LAM || strcmp(N->name[node], "_cf")) return -1;
  Port bf = wire((Port){node, 2});
  if (bf.node < 0 || bf.port != 0 || N->tag[bf.node] != LAM) return -1;
  if (strcmp(N->name[bf.node], "_cx") || bf.node == node) return -1;
  int inner = bf.node;
  Port cur = wire((Port){inner, 2});
  if (cur.node == inner && cur.port == 1) return 0;
  long count = 0;
  while (count < 100000) {
    cur = dup_resolve(cur);
    if (cur.node == inner && cur.port == 1) return count;
    if (cur.node < 0 || N->tag[cur.node] != APP) return -1;
    Port fun = dup_resolve(wire((Port){cur.node, 0}));
    if (!(fun.node == node && fun.port == 1)) return -1;
    count++;
    cur = wire((Port){cur.node, 2});
  }
  return -1;
}

static int bool_detect(int node) {
  if (N->tag[node] != LAM || strcmp(N->name[node], "_bt")) return -1;
  Port bf = wire((Port){node, 2});
  if (bf.node < 0 || bf.port != 0 || N->tag[bf.node] != LAM) return -1;
  if (strcmp(N->name[bf.node], "_bf")) return -1;
  Port b = dup_resolve(wire((Port){bf.node, 2}));
  if (b.node == node && b.port == 1) return 1;
  if (b.node == bf.node && b.port == 1) return 0;
  return -1;
}

/* count the number of applications a Church-number-shaped root performs
   when applied to f, then x.  chains  N f x  with  N possibly literal or
   (succ N)(add M N)(mul M N)(pow M N)  without reducing anything. */
static long iter_count(Port p, int fn, int xn, int depth);

static long chain_count(Port cur, int fn, int xn, int depth) {
  if (depth-- <= 0) return -1;
  cur = dup_resolve(cur);
  if (cur.node == xn && cur.port == 1) return 0;
  if (cur.node < 0 || N->tag[cur.node] != APP) return -1;
  long f = iter_count(wire((Port){cur.node, 0}), fn, xn, depth);
  long r = chain_count(wire((Port){cur.node, 2}), fn, xn, depth);
  if (f < 0 || r < 0) return -1;
  return f + r;
}

static long iter_count(Port p, int fn, int xn, int depth) {
  if (depth-- <= 0) return -1;
  p = dup_resolve(p);
  if (p.node < 0) return -1;
  if (p.node == fn && p.port == 1) return 1;
  if (N->tag[p.node] == LAM) {
    if (p.port != 0) return -1;
    return church_structural(p.node);
  }
  if (N->tag[p.node] == APP) {
    long k = iter_count(wire((Port){p.node, 0}), fn, xn, depth);
    if (k < 0) return -1;
    Port u = dup_resolve(wire((Port){p.node, 2}));
    long m;
    if (u.node >= 0 && u.node != fn && u.port == 0 &&
        N->tag[u.node] == LAM && (m = church_structural(u.node)) >= 0) {
      long r = 1;
      for (long i = 0; i < k; i++) r *= m;
      return r;
    }
    long c = iter_count(u, fn, xn, depth);
    if (c < 0) return -1;
    return c * k;
  }
  return -1;
}

/* detect a Church numeral '\_cf. \_cx. BODY' with BODY an iteration chain */
static long num_detect(int node) {
  if (N->tag[node] != LAM || strcmp(N->name[node], "_cf")) return -1;
  Port bf = wire((Port){node, 2});
  if (bf.node < 0 || bf.port != 0 || N->tag[bf.node] != LAM) return -1;
  if (strcmp(N->name[bf.node], "_cx") || bf.node == node) return -1;
  Port cx = wire((Port){bf.node, 2});
  if (cx.node == bf.node && cx.port == 1) return 0;
  return chain_count(cx, node, bf.node, 1000);
}

static void print_port(Port p, int depth) {
  if (depth > 10000 || p.node < 0 || p.node >= N->nn) {
    putchar('?');
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
  case APP: {
    Port f = wire((Port){p.node, 0});
    if (f.node < 0) {
      putchar('?');
      return;
    }
    /* (\x. x) E  =>  E : collapse identity applications in the readback
       (identity betas are always weak-firable but may sit under lambdas). */
    Port ff = dup_resolve(f);
    if (N->tag[ff.node] == LAM && !N->dead[ff.node] &&
        ff.node != p.node && ff.port == 0) {
      Port lv = wire((Port){ff.node, 1});
      Port lb = wire((Port){ff.node, 2});
      if ((lv.node == ff.node && lv.port == 2 &&
           lb.node == ff.node && lb.port == 1)) {
        Port ar = wire((Port){p.node, 2});
        if (ar.node >= 0) {
          print_port(ar, depth + 1);
          return;
        }
      }
    }
    putchar('(');
    print_port(f, depth + 1);
    putchar(' ');
    print_port(wire((Port){p.node, 2}), depth + 1);
    putchar(')');
    return;
  }
  case LAM: {
    if (p.port == 1) {
      fputs(N->name[p.node], stdout);
      return;
    }
    if (p.port == 0) {
      if (wire(p).node < 0) {
        putchar('?');
        return;
      }
      long v = num_detect(p.node);
      if (getenv("LIN_NUM")) fprintf(stderr, "NUM node %d name %s v %ld\n", p.node, N->name[p.node], v);
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
}

/* Read back the weak-head result.  A clean head lambda is printed
   structurally (under-lambda redexes stay untouched).  When optimal
   reduction leaves croissant residue (a numeral/boolean whose body is
   wrapped in live fan/identity-lambda scaffolding) the structural checks
   fail; return nonzero and let the caller fall back to term evaluation,
   which is semantically identical to the net's weak-head value. */
int net_print(Net *n) {
  N = n;
  Port hp = wire((Port){0, 0});
  if (hp.node >= 0 && hp.node < N->nn && !N->dead[hp.node] &&
      hp.port == 0 && N->tag[hp.node] == LAM) {
    const char *nm = N->name[hp.node];
    if (!strcmp(nm, "_cf") && num_detect(hp.node) < 0) return 1;
    if (!strcmp(nm, "_bt") && bool_detect(hp.node) < 0) return 1;
    print_port(hp, 0);
    return 0;
  }
  return 1;
}
