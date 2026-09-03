#define _GNU_SOURCE
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>

static Net *N;

static inline Port wire(Port p) {
  return N->wire[p.node * 3 + p.port];
}

/* --- Geometry of Interaction (GoI) Value Marshaling --- */

static long read_scott(Net *n, Port p) {
  N = n;
  long count = 0;
  Port cur = p;
  for (int step = 0; step < 1000000; step++) {
    while (cur.node >= 0 && cur.node < n->nn && !n->dead[cur.node] && n->tag[cur.node] == DUP)
      cur = wire((Port){cur.node, 0});
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node]) return -1;
    if (n->tag[cur.node] != LAM || strncmp(n->name[cur.node], "_sz", 3)) return -1;
    int sz = cur.node;
    Port ss_p = wire((Port){sz, 2});
    while (ss_p.node >= 0 && ss_p.node < n->nn && !n->dead[ss_p.node] && n->tag[ss_p.node] == DUP)
      ss_p = wire((Port){ss_p.node, 0});
    if (ss_p.node < 0 || ss_p.node >= n->nn || n->dead[ss_p.node]) return -1;
    if (n->tag[ss_p.node] != LAM || strncmp(n->name[ss_p.node], "_ss", 3)) return -1;
    int ss = ss_p.node;

    Port body = wire((Port){ss, 2});
    while (body.node >= 0 && body.node < n->nn && !n->dead[body.node] && n->tag[body.node] == DUP)
      body = wire((Port){body.node, 0});
    if (body.node < 0 || body.node >= n->nn || n->dead[body.node]) return -1;
    if (body.node == sz && body.port == 1) return count;
    if (n->tag[body.node] == APP) {
      Port fn = wire((Port){body.node, 0});
      while (fn.node >= 0 && fn.node < n->nn && !n->dead[fn.node] && n->tag[fn.node] == DUP)
        fn = wire((Port){fn.node, 0});
      if (fn.node == ss && fn.port == 1) {
        count++;
        cur = wire((Port){body.node, 2});
        continue;
      }
    }
    return -1;
  }
  return -1;
}

static long read_church(Net *n, Port p) {
  N = n;
  if (p.node < 0 || p.node >= n->nn || n->tag[p.node] != LAM) return -1;
  if (strncmp(n->name[p.node], "_cf", 3)) return -1;
  Port bf = wire((Port){p.node, 2});
  if (bf.node < 0 || bf.port != 0 || n->tag[bf.node] != LAM) return -1;
  int inner = bf.node;
  if (strncmp(n->name[inner], "_cx", 3)) return -1;

  Port cur = wire((Port){inner, 2});
  long count = 0;
  int stack[8192];
  int sp = 0;

  for (int step = 0; step < 10000000; step++) {
    if (cur.node < 0 || n->dead[cur.node]) return count;
    if (cur.node == inner && cur.port == 1) return count;
    int tag = n->tag[cur.node];
    if (tag == ERA) return count;
    if (tag == DUP) {
      if (cur.port == 1 || cur.port == 2) {
        if (sp >= 8192) return -1;
        stack[sp++] = cur.port;
        cur = wire((Port){cur.node, 0});
      } else if (cur.port == 0) {
        if (sp <= 0) return -1;
        cur = wire((Port){cur.node, stack[--sp]});
      }
    } else if (tag == APP) {
      if (cur.port == 1) {
        count++;
        cur = wire((Port){cur.node, 2});
      } else if (cur.port == 2) {
        cur = wire((Port){cur.node, 1});
      } else {
        return -1;
      }
    } else {
      return -1;
    }
  }
  return -1;
}

long net_read_int(Net *n, Port p) {
  long s = read_scott(n, p);
  if (s >= 0) return s;
  return read_church(n, p);
}


/* Extract Church boolean: _bt / _bf */
int net_read_bool(Net *n, Port p) {
  N = n;
  if (p.node < 0 || p.node >= n->nn || n->tag[p.node] != LAM) return -1;
  if (strncmp(n->name[p.node], "_bt", 3)) return -1;
  Port bf = wire((Port){p.node, 2});
  if (bf.node < 0 || bf.port != 0 || n->tag[bf.node] != LAM) return -1;
  if (strncmp(n->name[bf.node], "_bf", 3)) return -1;

  Port cur = wire((Port){bf.node, 2});
  for (int step = 0; step < 1000; step++) {
    if (cur.node < 0 || n->dead[cur.node]) return -1;
    if (cur.node == p.node && cur.port == 1) return 1;
    if (cur.node == bf.node && cur.port == 1) return 0;
    if (n->tag[cur.node] == DUP) {
      cur = wire((Port){cur.node, 0});
    } else {
      break;
    }
  }
  return -1;
}

/* Extract string from Lin list of characters: cons / nil or _cl / _nl */
int net_read_string(Net *n, Port p, char *buf, size_t max) {
  N = n;
  size_t len = 0;
  Port cur = p;

  for (int step = 0; step < 100000 && len + 1 < max; step++) {
    while (cur.node >= 0 && cur.node < n->nn && !n->dead[cur.node] && n->tag[cur.node] == DUP)
      cur = wire((Port){cur.node, 0});
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node]) break;
    if (n->tag[cur.node] != LAM) break;

    if (n->name[cur.node][0] != 'c' && strncmp(n->name[cur.node], "_cl", 3)) break;

    // Check if nil: \c. \n. true
    Port bn = wire((Port){cur.node, 2});
    while (bn.node >= 0 && bn.node < n->nn && !n->dead[bn.node] && n->tag[bn.node] == DUP)
      bn = wire((Port){bn.node, 0});
    if (bn.node < 0 || bn.port != 0 || n->tag[bn.node] != LAM) break;
    if (n->name[bn.node][0] != 'n' && strncmp(n->name[bn.node], "_nl", 3)) break;

    Port body = wire((Port){bn.node, 2});
    while (body.node >= 0 && body.node < n->nn && !n->dead[body.node] && n->tag[body.node] == DUP)
      body = wire((Port){body.node, 0});
    if (body.node < 0) break;

    // Nil check: body is true (LAM returning its first argument)
    if (n->tag[body.node] == LAM) {
      buf[len] = 0;
      return (int)len;
    }

    // Cons cell: body is APP ((c h) t)
    if (n->tag[body.node] == APP) {
      Port inner_app = wire((Port){body.node, 0});
      while (inner_app.node >= 0 && n->tag[inner_app.node] == DUP)
        inner_app = wire((Port){inner_app.node, 0});
      if (inner_app.node >= 0 && n->tag[inner_app.node] == APP) {
        Port ch_port = wire((Port){inner_app.node, 2});
        long ch = net_read_int(n, ch_port);
        if (ch >= 0 && ch < 256) {
          buf[len++] = (char)ch;
        }
      }
      cur = wire((Port){body.node, 2});
      continue;
    }
    break;
  }
  if (len > 0) {
    buf[len] = 0;
    return (int)len;
  }
  return -1;
}


/* Check if an unresolved DUP is reachable from root */
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

/* Check if root is an FFI invocation: \_ffi. \_ret. ((_ffi fn) arg) */
static int net_try_ffi(Net *n, Port p) {
  if (p.node < 0 || p.node >= n->nn || n->tag[p.node] != LAM) return 0;
  if (strcmp(n->name[p.node], "_ffi")) return 0;
  Port r = wire((Port){p.node, 2});
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM) return 0;
  if (strcmp(n->name[r.node], "_ret")) return 0;

  Port app2 = wire((Port){r.node, 2});
  if (app2.node < 0 || app2.port != 1 || n->tag[app2.node] != APP) return 0;
  Port app1 = wire((Port){app2.node, 0});
  if (app1.node < 0 || app1.port != 1 || n->tag[app1.node] != APP) return 0;

  char fn_name[256];
  if (net_read_string(n, wire((Port){app1.node, 2}), fn_name, sizeof(fn_name)) < 0)
    return 0;

  void *sym = dlsym(RTLD_DEFAULT, fn_name);
  if (!sym) {
    fprintf(stderr, "ffi: symbol '%s' not found\n", fn_name);
    return 0;
  }

  Port arg_p = wire((Port){app2.node, 2});
  char arg_str[4096];
  int is_str = (net_read_string(n, arg_p, arg_str, sizeof(arg_str)) >= 0);

  if (!strcmp(fn_name, "puts")) {
    int (*fn)(const char *) = (int (*)(const char *))sym;
    int res = fn(is_str ? arg_str : "");
    printf("%d", res);
    return 1;
  }
  if (!strcmp(fn_name, "putchar")) {
    long ch = net_read_int(n, arg_p);
    int (*fn)(int) = (int (*)(int))sym;
    int res = fn((int)ch);
    printf("%d", res);
    return 1;
  }
  if (!strcmp(fn_name, "exit")) {
    long code = net_read_int(n, arg_p);
    void (*fn)(int) = (void (*)(int))sym;
    fn((int)code);
    return 1;
  }
  if (!strcmp(fn_name, "getenv")) {
    char *(*fn)(const char *) = (char *(*)(const char *))sym;
    char *res = fn(is_str ? arg_str : "");
    fputs(res ? res : "(null)", stdout);
    return 1;
  }

  long arg_val = net_read_int(n, arg_p);
  if (arg_val >= 0) {
    long (*fn)(long) = (long (*)(long))sym;
    printf("%ld", fn(arg_val));
    return 1;
  } else {
    long (*fn)(void) = (long (*)(void))sym;
    printf("%ld", fn());
    return 1;
  }
}

/* Print a port representation to stdout */
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
    if (p.port == 0) print_port(wire((Port){p.node, 1}), depth + 1);
    else print_port(wire((Port){p.node, 0}), depth + 1);
    return;
  case APP:
    putchar('(');
    print_port(wire((Port){p.node, 0}), depth + 1);
    putchar(' ');
    print_port(wire((Port){p.node, 2}), depth + 1);
    putchar(')');
    return;
  case LAM:
    if (p.port == 1) {
      fputs(N->name[p.node], stdout);
      return;
    }
    if (p.port == 0) {
      long v = net_read_int(N, p);
      if (v >= 0) {
        printf("%ld", v);
        return;
      }
      int b = net_read_bool(N, p);
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

int net_print(Net *n) {
  N = n;
  Port r = wire((Port){0, 0});
  if (r.node >= 0 && r.node < n->nn && n->tag[r.node] == LAM) {
    if (net_try_ffi(n, r)) return 0;
    long v = net_read_int(n, r);
    if (v >= 0) {
      printf("%ld", v);
      return 0;
    }
    int b = net_read_bool(n, r);
    if (b >= 0) {
      fputs(b ? "true" : "false", stdout);
      return 0;
    }
  }
  if (live_dup_reachable(n)) return 1;
  print_port(r, 0);
  return 0;
}
