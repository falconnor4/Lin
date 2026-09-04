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

static inline Port dup_hop(Net *n, Port p) {
  for (int step = 0; step < n->nn && p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP; step++) {
    if (p.port == 0) p = n->wire[p.node * 3 + 1];
    else p = n->wire[p.node * 3 + 0];
  }
  return p;
}

static long read_scott(Net *n, Port p) {
  N = n;
  long count = 0;
  Port cur = p;
  for (int step = 0; step < n->nn; step++) {
    cur = dup_hop(n, cur);
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node]) return -1;
    if (n->tag[cur.node] != LAM || strncmp(n->name[cur.node], "_sz", 3)) return -1;
    int sz = cur.node;
    Port ss_p = dup_hop(n, wire((Port){sz, 2}));
    if (ss_p.node < 0 || ss_p.node >= n->nn || n->dead[ss_p.node]) return -1;
    if (n->tag[ss_p.node] != LAM || strncmp(n->name[ss_p.node], "_ss", 3)) return -1;
    int ss = ss_p.node;

    Port body = dup_hop(n, wire((Port){ss, 2}));
    if (body.node < 0 || body.node >= n->nn || n->dead[body.node]) return -1;
    if (body.node == sz && body.port == 1) return count;
    if (n->tag[body.node] == APP) {
      Port fn = dup_hop(n, wire((Port){body.node, 0}));
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

long net_read_int(Net *n, Port p) {
  return read_scott(n, p);
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
  for (int step = 0; step < n->nn; step++) {
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

  for (int step = 0; step < n->nn && len + 1 < max; step++) {
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

static int unpack_arg(Net *n, Port p, long *out_val, char *str_buf, size_t str_max) {
  while (p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP)
    p = wire((Port){p.node, 0});
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;

  /* 1. Boolean check: _bt */
  if (!strncmp(n->name[p.node], "_bt", 3)) {
    int b = net_read_bool(n, p);
    if (b >= 0) { *out_val = b; return 1; }
  }

  /* 2. String check: c or _cl */
  if (n->name[p.node][0] == 'c' || !strncmp(n->name[p.node], "_cl", 3)) {
    int len = net_read_string(n, p, str_buf, str_max);
    if (len >= 0) { *out_val = (long)(intptr_t)str_buf; return 1; }
  }

  /* 3. Number check / fallback */
  long v = net_read_int(n, p);
  if (v >= 0) { *out_val = v; return 1; }
  return 0;
}

static int unpack_args(Net *n, Port arg_p, long *args, char str_bufs[8][4096], int max_args) {
  /* Try unpacking arg_p as a list of arguments: (cons a1 (cons a2 ... nil)) */
  int argc = 0;
  Port cur = arg_p;
  while (cur.node >= 0 && cur.node < n->nn && !n->dead[cur.node] && n->tag[cur.node] == DUP)
    cur = wire((Port){cur.node, 0});

  if (cur.node >= 0 && cur.node < n->nn && n->tag[cur.node] == LAM &&
      (n->name[cur.node][0] == 'c' || !strncmp(n->name[cur.node], "_cl", 3))) {
    Port bn = wire((Port){cur.node, 2});
    while (bn.node >= 0 && bn.node < n->nn && !n->dead[bn.node] && n->tag[bn.node] == DUP)
      bn = wire((Port){bn.node, 0});
    if (bn.node >= 0 && bn.port == 0 && n->tag[bn.node] == LAM) {
      for (int step = 0; step < n->nn && argc < max_args; step++) {
        while (cur.node >= 0 && cur.node < n->nn && !n->dead[cur.node] && n->tag[cur.node] == DUP)
          cur = wire((Port){cur.node, 0});
        if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;

        Port inner = wire((Port){cur.node, 2});
        while (inner.node >= 0 && inner.node < n->nn && !n->dead[inner.node] && n->tag[inner.node] == DUP)
          inner = wire((Port){inner.node, 0});
        if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) break;

        Port body = wire((Port){inner.node, 2});
        while (body.node >= 0 && body.node < n->nn && !n->dead[body.node] && n->tag[body.node] == DUP)
          body = wire((Port){body.node, 0});
        if (body.node < 0) break;

        if (n->tag[body.node] == LAM) break; /* nil */

        if (n->tag[body.node] == APP) {
          Port inner_app = wire((Port){body.node, 0});
          while (inner_app.node >= 0 && n->tag[inner_app.node] == DUP)
            inner_app = wire((Port){inner_app.node, 0});
          if (inner_app.node >= 0 && n->tag[inner_app.node] == APP) {
            Port elem = wire((Port){inner_app.node, 2});
            unpack_arg(n, elem, &args[argc], str_bufs[argc], 4096);
            argc++;
          }
          cur = wire((Port){body.node, 2});
          continue;
        }
        break;
      }
      if (argc > 0) return argc;
    }
  }

  if (unpack_arg(n, arg_p, &args[0], str_bufs[0], 4096)) {
    return 1;
  }
  return 0;
}

/* Check if root is an FFI invocation: \_ffi. \_ret. ((_ffi fn) args) */
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

  Port arg_p = wire((Port){app2.node, 2});
  long c_args[8] = {0};
  char str_bufs[8][4096];
  int argc = unpack_args(n, arg_p, c_args, str_bufs, 8);


  fflush(stdout);

  if (!strcmp(fn_name, "lin_add")) { printf("%ld", c_args[0] + c_args[1]); return 1; }
  if (!strcmp(fn_name, "lin_sub")) { printf("%ld", c_args[0] >= c_args[1] ? c_args[0] - c_args[1] : 0); return 1; }
  if (!strcmp(fn_name, "lin_mul")) { printf("%ld", c_args[0] * c_args[1]); return 1; }
  if (!strcmp(fn_name, "lin_div")) { printf("%ld", c_args[1] ? c_args[0] / c_args[1] : 0); return 1; }
  if (!strcmp(fn_name, "lin_mod")) { printf("%ld", c_args[1] ? c_args[0] % c_args[1] : 0); return 1; }
  if (!strcmp(fn_name, "lin_eq"))  { fputs(c_args[0] == c_args[1] ? "true" : "false", stdout); return 1; }
  if (!strcmp(fn_name, "lin_lt"))  { fputs(c_args[0] < c_args[1] ? "true" : "false", stdout); return 1; }
  if (!strcmp(fn_name, "lin_leq")) { fputs(c_args[0] <= c_args[1] ? "true" : "false", stdout); return 1; }
  if (!strcmp(fn_name, "lin_gt"))  { fputs(c_args[0] > c_args[1] ? "true" : "false", stdout); return 1; }

  if (!strcmp(fn_name, "dlopen")) {
    void *h = dlopen(argc > 0 ? (const char *)c_args[0] : NULL, RTLD_NOW | RTLD_GLOBAL);
    if (!h) { fprintf(stderr, "ffi: dlopen failed: %s\n", dlerror()); return 0; }
    printf("%ld", (long)(intptr_t)h);
    return 1;
  }
  if (!strcmp(fn_name, "getenv")) {
    char *res = getenv(argc > 0 ? (const char *)c_args[0] : "");
    fputs(res ? res : "(null)", stdout);
    return 1;
  }
  if (!strcmp(fn_name, "exit")) { exit(argc > 0 ? (int)c_args[0] : 0); return 1; }
  if (!strcmp(fn_name, "puts")) { printf("%d", puts(argc > 0 ? (const char *)c_args[0] : "")); return 1; }

  void *sym = dlsym(RTLD_DEFAULT, fn_name);
  if (!sym) {
    fprintf(stderr, "ffi: symbol '%s' not found\n", fn_name);
    return 0;
  }

  long res = 0;
  switch (argc) {
  case 0: res = ((long (*)(void))sym)(); break;
  case 1: res = ((long (*)(long))sym)(c_args[0]); break;
  case 2: res = ((long (*)(long, long))sym)(c_args[0], c_args[1]); break;
  case 3: res = ((long (*)(long, long, long))sym)(c_args[0], c_args[1], c_args[2]); break;
  case 4: res = ((long (*)(long, long, long, long))sym)(c_args[0], c_args[1], c_args[2], c_args[3]); break;
  case 5: res = ((long (*)(long, long, long, long, long))sym)(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4]); break;
  case 6: res = ((long (*)(long, long, long, long, long, long))sym)(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5]); break;
  case 7: res = ((long (*)(long, long, long, long, long, long, long))sym)(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5], c_args[6]); break;
  case 8: res = ((long (*)(long, long, long, long, long, long, long, long))sym)(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5], c_args[6], c_args[7]); break;
  default:
    fprintf(stderr, "ffi: too many arguments (%d)\n", argc);
    return 0;
  }
  printf("%ld", res);
  return 1;
}

static unsigned char *vis_print = NULL;

/* Print a port representation to stdout */
static void print_port(Port p, int depth) {
  if (depth > N->nn || p.node < 0 || p.node >= N->nn) {
    putchar('?');
    return;
  }
  if (N->dead[p.node]) {
    putchar('_');
    return;
  }
  if (N->tag[p.node] == LAM && p.port == 1) {
    fputs(N->name[p.node], stdout);
    return;
  }
  if (vis_print && vis_print[p.node]) {
    putchar('?');
    return;
  }
  if (vis_print) vis_print[p.node] = 1;

  switch (N->tag[p.node]) {
  case ROOT:
    print_port(wire(p), depth + 1);
    break;
  case ERA:
    putchar('_');
    break;
  case DUP:
    if (p.port == 0) print_port(wire((Port){p.node, 1}), depth + 1);
    else print_port(wire((Port){p.node, 0}), depth + 1);
    break;
  case APP:
    putchar('(');
    print_port(wire((Port){p.node, 0}), depth + 1);
    putchar(' ');
    print_port(wire((Port){p.node, 2}), depth + 1);
    putchar(')');
    break;
  case LAM:
    if (p.port == 1) {
      fputs(N->name[p.node], stdout);
      break;
    }
    if (p.port == 0) {
      long v = net_read_int(N, p);
      if (v >= 0) {
        printf("%ld", v);
        break;
      }
      int b = net_read_bool(N, p);
      if (b >= 0) {
        fputs(b ? "true" : "false", stdout);
        break;
      }
      fputs("(\\", stdout);
      fputs(N->name[p.node], stdout);
      putchar(' ');
      print_port(wire((Port){p.node, 2}), depth + 1);
      putchar(')');
      break;
    }
    print_port(wire(p), depth + 1);
    break;
  }
  if (vis_print) vis_print[p.node] = 0;
}

int net_print(Net *n) {
  N = n;
  Port r = dup_hop(n, wire((Port){0, 0}));
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
  vis_print = calloc((size_t)(n->nn + 1), 1);
  print_port(r, 0);
  free(vis_print);
  vis_print = NULL;
  return 0;
}
