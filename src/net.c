#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WIRE(n, p) ((n)->wire[(p).node * 3 + (p).port])
#define NONE ((Port){-1, -1})

Scope scope_nil(void) { return (Scope){0, 0}; }

Scope scope_ext(Scope s, int bit) {
  if (s.len < MAXSCOPE) {
    s.bits = (s.bits << 1) | (bit & 1);
    s.len++;
  }
  return s;
}

/* [bit] ++ a ++ b  (paper: scope extension on commutation) */
static Scope scope_cat(int bit, Scope a, Scope b) {
  Scope r = scope_ext(scope_nil(), bit);
  for (int i = a.len - 1; i >= 0; i--) r = scope_ext(r, (a.bits >> i) & 1);
  for (int i = b.len - 1; i >= 0; i--) r = scope_ext(r, (b.bits >> i) & 1);
  return r;
}

int scope_eq(Scope a, Scope b) {
  return a.len == b.len && a.bits == b.bits;
}

void net_init(Net *n, int cap) {
  n->cap = cap;
  n->tag = malloc(cap);
  n->wire = malloc(cap * 3 * sizeof(Port));
  n->scope = malloc(cap * sizeof(Scope));
  n->name = malloc(cap * NAME);
  n->act = NULL; n->atop = 0; n->actcap = 0;
  n->mark = calloc(cap, sizeof(int));
  n->dead = calloc(cap, 1);
  n->nn = 0; n->gen = 0; n->steps = 0;
  net_alloc(n, ROOT, scope_nil(), "");
}

void net_free(Net *n) {
  free(n->tag); free(n->wire); free(n->scope);
  free(n->name); free(n->act); free(n->mark); free(n->dead);
}

Port net_alloc(Net *n, int tag, Scope sc, const char *name) {
  if (n->nn >= n->cap) {
    int nc = n->cap * 2;
    n->tag = realloc(n->tag, nc);
    n->wire = realloc(n->wire, nc * 3 * sizeof(Port));
    n->scope = realloc(n->scope, nc * sizeof(Scope));
    n->name = realloc(n->name, nc * NAME);
    n->mark = realloc(n->mark, nc * sizeof(int));
    n->dead = realloc(n->dead, nc);
    n->cap = nc;
  }
  int id = n->nn++;
  n->tag[id] = tag;
  n->scope[id] = sc;
  snprintf(n->name[id], NAME, "%s", name);
  for (int i = 0; i < 3; i++) n->wire[id * 3 + i] = NONE;
  return (Port){id, 0};
}

static void act_push(Net *n, Port a, Port b) {
  if (n->atop + 2 > n->actcap) {
    n->actcap = n->actcap ? n->actcap * 2 : 256;
    n->act = realloc(n->act, n->actcap * sizeof(Port));
  }
  n->act[n->atop++] = a;
  n->act[n->atop++] = b;
}

/* eliminate a croissant fan (DUP whose principal wire leads to a dead node).
   The duplication is inert once its producer died; join the two copy wires
   directly.  Only safe for the dead-principal case (live fans are semantics). */
static int croissant_kill(Net *n, int dnode) {
  Port p0 = (Port){dnode, 0};
  Port pr = WIRE(n, p0);
  if (pr.node >= 0 && pr.node < n->nn && !n->dead[pr.node]) return 0;
  Port pa = (Port){dnode, 1}, pb = (Port){dnode, 2};
  Port a = WIRE(n, pa), b = WIRE(n, pb);
  n->dead[dnode] = 1;
  if (a.node >= 0 && b.node >= 0) {
    if (a.node == b.node && a.port == b.port) return 1;
    net_link(n, a, b, 1);
  }
  return 1;
}

void net_link(Net *n, Port a, Port b, int enqueue) {
  if (a.node < 0 || b.node < 0) return;
  WIRE(n, a) = b;
  WIRE(n, b) = a;
  if (enqueue && a.port == 0 && b.port == 0) act_push(n, a, b);
}

static int interact(Net *n, Port p1, Port p2) {
  int t1 = n->tag[p1.node], t2 = n->tag[p2.node];
  if (t1 > t2) { Port t = p1; p1 = p2; p2 = t; int u = t1; t1 = t2; t2 = u; }
  int n1 = p1.node, n2 = p2.node;
  if (getenv("LIN_TRACE")) {
    static const char *tn[] = { "LAM", "APP", "DUP", "ERA", "ROOT" };
    fprintf(stderr, "step %ld: %s%d{%d,%llx} x %s%d{%d,%llx}\n", n->steps,
            tn[t1], n1, n->scope[n1].len, (unsigned long long)n->scope[n1].bits,
            tn[t2], n2, n->scope[n2].len, (unsigned long long)n->scope[n2].bits);
  }

  if (t1 == ERA || t2 == ERA) {
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    if (t1 == ERA && t2 == ERA) return 1;
    Port e1 = net_alloc(n, ERA, scope_nil(), "");
    Port e2 = net_alloc(n, ERA, scope_nil(), "");
    net_link(n, e1, WIRE(n, ((Port){n1, 1})), 1);
    net_link(n, e2, WIRE(n, ((Port){n1, 2})), 1);
    return 1;
  }

  if (t1 == LAM && t2 == APP) {
    Port lv = WIRE(n, ((Port){n1, 1})), lb = WIRE(n, ((Port){n1, 2}));
    Port ar = WIRE(n, ((Port){n2, 1})), aa = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    if (lv.node == n1 && lv.port == 2 && lb.node == n1 && lb.port == 1) {
      net_link(n, aa, ar, 1);
      return 1;
    }
    net_link(n, lv, aa, 1);
    net_link(n, lb, ar, 1);
    return 1;
  }

  if (t1 == DUP && t2 == DUP) {
    if (!scope_eq(n->scope[n1], n->scope[n2])) {
      if (getenv("LIN_TRACE"))
        fprintf(stderr, "  STUCK dup %d vs dup %d\n", n1, n2);
      return 0;
    }
    Port a1 = WIRE(n, ((Port){n1, 1})), a2 = WIRE(n, ((Port){n1, 2}));
    Port b1 = WIRE(n, ((Port){n2, 1})), b2 = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    net_link(n, a1, b1, 1);
    net_link(n, a2, b2, 1);
    return 1;
  }

  if ((t1 == LAM || t1 == APP) && t2 == DUP) {
    Scope sn = n->scope[n1], sd = n->scope[n2];
    Port nv = WIRE(n, ((Port){n1, 1})), nb = WIRE(n, ((Port){n1, 2}));
    Port da = WIRE(n, ((Port){n2, 1})), db = WIRE(n, ((Port){n2, 2}));
    n->dead[n1] = 1;
    n->dead[n2] = 1;
    char nm[NAME];
    snprintf(nm, NAME, "%s", n->name[n1]);
    int m1 = net_alloc(n, t1, scope_cat(1, sn, sd), nm).node;
    int m2 = net_alloc(n, t1, scope_cat(2, sn, sd), nm).node;
    int d1 = net_alloc(n, DUP, sd, "").node;
    int d2 = net_alloc(n, DUP, sd, "").node;
    net_link(n, (Port){d1, 1}, (Port){m1, 1}, 0);
    net_link(n, (Port){d1, 2}, (Port){m2, 1}, 0);
    net_link(n, (Port){d2, 1}, (Port){m1, 2}, 0);
    net_link(n, (Port){d2, 2}, (Port){m2, 2}, 0);
    net_link(n,(Port){d1, 0}, nv, 1);
    net_link(n,(Port){d2, 0}, nb, 1);
    net_link(n, (Port){m1, 0}, da, 1);
    net_link(n, (Port){m2, 0}, db, 1);
    return 1;
  }
  return 0;
}

static void reduce_worklist(Net *n, long limit, int *changed) {
  while (n->atop > 0 && n->steps < limit) {
    Port p2 = n->act[--n->atop];
    Port p1 = n->act[--n->atop];
    if (p1.node < 0 || p2.node < 0) continue;
    if (n->dead[p1.node] || n->dead[p2.node]) continue;
    if (WIRE(n, p1).node != p2.node || WIRE(n, p1).port != p2.port) continue;
    if (WIRE(n, p2).node != p1.node || WIRE(n, p2).port != p1.port) continue;
    if (p1.port != 0 || p2.port != 0) continue;
    if (interact(n, p1, p2)) *changed += 1;
    n->steps++;
  }
}

long net_reduce(Net *n, long limit) {
  int ch = 0;
  reduce_worklist(n, limit, &ch);
  return n->steps;
}

/* weak-head reduction: fire only redexes on the head spine (from ROOT),
   stop as soon as the head is a lambda.  Bodies under lambdas and redexes
   in argument positions are left untouched (weak / call-by-name). */
long net_reduce_whnf(Net *n, long limit) {
  while (n->steps < limit) {
    Port app = NONE, funf = NONE;
restart_nav:
    Port p = WIRE(n, ((Port){0, 0}));
    int guard = 0;
    while (p.node >= 0 && !n->dead[p.node] && guard++ < 100000) {
      int t = n->tag[p.node];
      if (p.port == 0) {
        if (t == LAM || t == ROOT || t == ERA) break; /* WHNF */
        if (t == DUP) {
          if (n->dead[p.node]) break;
          if (croissant_kill(n, p.node)) continue; /* inert fan: remove, re-nav */
        }
        if (t == APP) {             /* APP.0 reached: follow its result */
          Port w = WIRE(n, ((Port){p.node, 1}));
          if (w.node < 0) break;
          p = w;
          continue;
        }
        break;
      }
      if (t == LAM) {               /* var/body port: follow body */
        Port w = WIRE(n, ((Port){p.node, 2}));
        if (w.node < 0) break;
        p = w;
        continue;
      }
      if (t == APP && p.port == 1) {
        Port f = WIRE(n, ((Port){p.node, 0}));
        if (f.node < 0) break;
        int ft = n->tag[f.node];
        if (n->dead[f.node]) {
          /* substituted-through binder: beta already fired, so the far end of
             this port holds the value that was wired in its place */
          if (f.port != 0) {
            Port w = WIRE(n, f);
            if (w.node < 0) break;
            p = w;
            continue;
          }
          break;
        }
        if (f.port == 0 &&
            (ft == LAM || ft == DUP)) {      /* head redex */
          app = (Port){p.node, 0};
          funf = f;
          break;
        }
        if (ft == DUP && n->dead[f.node] == 0) {
          /* fan in function position (on one of its aux ports): */
          Port top = (Port){f.node, 0};
          Port cur = WIRE(n, top);
          int g2 = 0;
          while (cur.node >= 0 && g2++ < 1000) {
            if (n->dead[cur.node]) {
              croissant_kill(n, top.node);   /* inert fan blocking head spine */
              goto restart_nav;
            }
            if (n->tag[cur.node] == DUP) {
              if (cur.port == 0) {          /* two dups facing: annihilate */
                app = top; funf = cur;
                break;
              }
              top = (Port){cur.node, 0};    /* climb one level up the tree */
              cur = WIRE(n, top);
              continue;
            }
            if (n->tag[cur.node] == LAM && cur.port == 0) {
              app = top; funf = cur;
              break;
            }
            break;
          }
          if (app.node >= 0) break;          /* found a redex through the fan */
          if (!n->dead[top.node] &&
              croissant_kill(n, top.node)) goto restart_nav;
          break;                             /* fan head without redex: stop */
        }
        if (ft == ERA) {                    /* applied-to-erased: follow era wire */
          Port w = WIRE(n, ((Port){f.node, 1}));
          if (w.node < 0) break;
          p = w;
          continue;
        }
        if (ft == APP && f.port == 1) { p = f; continue; } /* descend fun chain */
        break;
      }
      break;
    }
    if (app.node < 0) break;                 /* no head redex: WHNF reached */
    interact(n, app, funf);
    n->steps++;
    n->atop = 0;                             /* WHNF only; drop pending work */
  }
  return n->steps;
}

Net *net_copy(const Net *n) {
  Net *c = malloc(sizeof(Net));
  c->cap = n->cap;
  c->tag = malloc(c->cap);
  c->wire = malloc(c->cap * 3 * sizeof(Port));
  c->scope = malloc(c->cap * sizeof(Scope));
  c->name = malloc(c->cap * NAME);
  c->act = NULL;
  c->actcap = 0;
  c->atop = 0;
  c->mark = calloc(c->cap, sizeof(int));
  c->dead = malloc(c->cap);
  memcpy(c->dead, n->dead, c->cap);
  c->nn = n->nn;
  c->gen = 0;
  c->steps = 0;
  memcpy(c->tag, n->tag, c->cap);
  memcpy(c->wire, n->wire, c->cap * 3 * sizeof(Port));
  memcpy(c->scope, n->scope, c->cap * sizeof(Scope));
  memcpy(c->name, n->name, c->cap * NAME);
  return c;
}

/* full reduction: also fire pairs inside lambdas, used by readback */
long net_reduce_full(Net *n, long limit) {
  for (int round = 0; round < 100000 && n->steps < limit; round++) {
    int changed = 0;
    n->atop = 0;
    for (int i = 0; i < n->nn; i++) {
      if (n->tag[i] == ROOT || n->dead[i]) continue;
      Port w = WIRE(n, ((Port){i, 0}));
      if (w.node < 0 || w.port != 0 || w.node <= i) continue;
      if (n->dead[w.node]) continue;
      act_push(n, (Port){i, 0}, w);
    }
    reduce_worklist(n, limit, &changed);
    if (getenv("LIN_DUMP")) {
      for (int i = 0; i < n->nn; i++) {
        if (n->dead[i]) continue;
        for (int pp = 0; pp < 3; pp++) {
          Port w = n->wire[i * 3 + pp];
          if (w.node < 0) continue;
          if (n->wire[w.node * 3 + w.port].node != i ||
              n->wire[w.node * 3 + w.port].port != pp) {
            fprintf(stderr, "ASYMMETRY %d.%d -> %d.%d back %d.%d\n", i, pp,
                    w.node, w.port, n->wire[w.node * 3 + w.port].node,
                    n->wire[w.node * 3 + w.port].port);
          }
        }
      }
    }
    if (changed == 0) break;
  }
  return n->steps;
}
