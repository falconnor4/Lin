#define _GNU_SOURCE
#include "lin.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
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

long net_read_int(Net *n, Port p) {
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

/* Extract Church boolean: _bt / _bf */
int net_read_bool(Net *n, Port p) {
  N = n;
  if (p.node < 0 || p.node >= n->nn || n->tag[p.node] != LAM || strncmp(n->name[p.node], "_bt", 3)) return -1;
  Port bf = wire((Port){p.node, 2});
  if (bf.node < 0 || bf.port != 0 || n->tag[bf.node] != LAM || strncmp(n->name[bf.node], "_bf", 3)) return -1;
  Port cur = wire((Port){bf.node, 2});
  for (int step = 0; step < n->nn; step++) {
    if (cur.node < 0 || n->dead[cur.node]) return -1;
    if (cur.node == p.node && cur.port == 1) return 1;
    if (cur.node == bf.node && cur.port == 1) return 0;
    if (n->tag[cur.node] == DUP) cur = wire((Port){cur.node, 0});
    else break;
  }
  return -1;
}

static inline Port skip_dup(Net *n, Port p) {
  while (p.node >= 0 && p.node < n->nn && !n->dead[p.node] && n->tag[p.node] == DUP)
    p = wire((Port){p.node, 0});
  return p;
}

int net_read_string(Net *n, Port p, char *buf, size_t max) {
  N = n;
  size_t len = 0;
  Port cur = p;
  for (int step = 0; step < n->nn && len + 1 < max; step++) {
    cur = skip_dup(n, cur);
    if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
    if (n->name[cur.node][0] != 'c' && strncmp(n->name[cur.node], "_cl", 3)) break;

    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node < 0 || bn.port != 0 || n->tag[bn.node] != LAM) break;
    if (n->name[bn.node][0] != 'n' && strncmp(n->name[bn.node], "_nl", 3)) break;

    Port body = skip_dup(n, wire((Port){bn.node, 2}));
    if (body.node < 0) break;
    if (n->tag[body.node] == LAM) { buf[len] = 0; return (int)len; }
    if (n->tag[body.node] == APP) {
      Port inner = skip_dup(n, wire((Port){body.node, 0}));
      if (inner.node >= 0 && n->tag[inner.node] == APP) {
        long ch = net_read_int(n, wire((Port){inner.node, 2}));
        if (ch >= 0 && ch < 256) buf[len++] = (char)ch;
      }
      cur = wire((Port){body.node, 2});
      continue;
    }
    break;
  }
  if (len > 0) { buf[len] = 0; return (int)len; }
  return -1;
}

static int unpack_arg(Net *n, Port p, long *out_val, char *str_buf, size_t str_max) {
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM) return 0;
  if (!strncmp(n->name[p.node], "_bt", 3)) {
    int b = net_read_bool(n, p);
    if (b >= 0) { *out_val = b; return 1; }
  }
  if (n->name[p.node][0] == 'c' || !strncmp(n->name[p.node], "_cl", 3)) {
    int len = net_read_string(n, p, str_buf, str_max);
    if (len >= 0) { *out_val = (long)(intptr_t)str_buf; return 1; }
  }
  long v = net_read_int(n, p);
  return v >= 0 ? (*out_val = v, 1) : 0;
}

static int unpack_args(Net *n, Port arg_p, long *args, char str_bufs[8][4096], int max_args) {
  int argc = 0;
  Port cur = skip_dup(n, arg_p);
  if (cur.node >= 0 && cur.node < n->nn && n->tag[cur.node] == LAM &&
      (n->name[cur.node][0] == 'c' || !strncmp(n->name[cur.node], "_cl", 3))) {
    Port bn = skip_dup(n, wire((Port){cur.node, 2}));
    if (bn.node >= 0 && bn.port == 0 && n->tag[bn.node] == LAM) {
      for (int step = 0; step < n->nn && argc < max_args; step++) {
        cur = skip_dup(n, cur);
        if (cur.node < 0 || cur.node >= n->nn || n->dead[cur.node] || n->tag[cur.node] != LAM) break;
        Port inner = skip_dup(n, wire((Port){cur.node, 2}));
        if (inner.node < 0 || inner.port != 0 || n->tag[inner.node] != LAM) break;
        Port body = skip_dup(n, wire((Port){inner.node, 2}));
        if (body.node < 0 || n->tag[body.node] == LAM) break;
        if (n->tag[body.node] == APP) {
          Port ia = skip_dup(n, wire((Port){body.node, 0}));
          if (ia.node >= 0 && n->tag[ia.node] == APP) {
            unpack_arg(n, wire((Port){ia.node, 2}), &args[argc], str_bufs[argc], 4096);
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
  return unpack_arg(n, arg_p, &args[0], str_bufs[0], 4096) ? 1 : 0;
}

/* Check if root is an FFI invocation: \_ffi. \_ret. ((_ffi fn) args) */
static int run_ffi(Net *n, Port p, long *out_int, char *out_str, size_t max_str) {
  p = skip_dup(n, p);
  if (p.node < 0 || p.node >= n->nn || n->dead[p.node] || n->tag[p.node] != LAM || strcmp(n->name[p.node], "_ffi")) return 0;
  Port r = skip_dup(n, wire((Port){p.node, 2}));
  if (r.node < 0 || r.port != 0 || n->tag[r.node] != LAM || strcmp(n->name[r.node], "_ret")) return 0;
  Port a2 = skip_dup(n, wire((Port){r.node, 2}));
  if (a2.node < 0 || a2.port != 1 || n->tag[a2.node] != APP) return 0;
  Port a1 = skip_dup(n, wire((Port){a2.node, 0}));
  if (a1.node < 0 || a1.port != 1 || n->tag[a1.node] != APP) return 0;

  char fn[256];
  if (net_read_string(n, wire((Port){a1.node, 2}), fn, sizeof(fn)) < 0) return 0;
  long c_args[8] = {0}; char sbufs[8][4096];
  int argc = unpack_args(n, wire((Port){a2.node, 2}), c_args, sbufs, 8);

  *out_int = 0; out_str[0] = 0;
  if (!strcmp(fn, "lin_add")) return (*out_int = c_args[0] + c_args[1], 1);
  if (!strcmp(fn, "lin_sub")) return (*out_int = c_args[0] >= c_args[1] ? c_args[0] - c_args[1] : 0, 1);
  if (!strcmp(fn, "lin_mul")) return (*out_int = c_args[0] * c_args[1], 1);
  if (!strcmp(fn, "lin_div")) return (*out_int = c_args[1] ? c_args[0] / c_args[1] : 0, 1);
  if (!strcmp(fn, "lin_mod")) return (*out_int = c_args[1] ? c_args[0] % c_args[1] : 0, 1);
  if (!strcmp(fn, "lin_eq") || !strcmp(fn, "lin_lt") || !strcmp(fn, "lin_leq") || !strcmp(fn, "lin_gt")) {
    int b = !strcmp(fn, "lin_eq") ? c_args[0] == c_args[1] : !strcmp(fn, "lin_lt") ? c_args[0] < c_args[1] : !strcmp(fn, "lin_leq") ? c_args[0] <= c_args[1] : c_args[0] > c_args[1];
    return (snprintf(out_str, max_str, "%s", b ? "true" : "false"), 2);
  }
  if (!strcmp(fn, "dlopen")) return (*out_int = (long)(intptr_t)dlopen(argc > 0 ? (char *)c_args[0] : NULL, RTLD_NOW | RTLD_GLOBAL), 1);
  if (!strcmp(fn, "getenv")) return (snprintf(out_str, max_str, "%s", getenv(argc > 0 ? (char *)c_args[0] : "") ?: "(null)"), 2);
  if (!strcmp(fn, "exit")) { exit(argc > 0 ? (int)c_args[0] : 0); return 1; }
  if (!strcmp(fn, "puts")) return (*out_int = puts(argc > 0 ? (char *)c_args[0] : ""), 1);

  fflush(stdout);
  void *sym = dlsym(RTLD_DEFAULT, fn);
  if (!sym) { fprintf(stderr, "ffi: symbol '%s' not found\n", fn); return 0; }
  long (*f)() = (long (*)())sym;
  *out_int = (argc <= 0) ? f() : (argc == 1) ? f(c_args[0]) : (argc == 2) ? f(c_args[0], c_args[1]) :
             (argc == 3) ? f(c_args[0], c_args[1], c_args[2]) : f(c_args[0], c_args[1], c_args[2], c_args[3], c_args[4], c_args[5], c_args[6], c_args[7]);
  return 1;
}

static int net_try_ffi(Net *n, Port p) {
  long v = 0; char s[4096] = {0};
  int r = run_ffi(n, p, &v, s, sizeof(s));
  if (r == 1) { printf("%ld", v); fflush(stdout); return 1; }
  if (r == 2) { fputs(s, stdout); fflush(stdout); return 1; }
  return 0;
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
      if (b >= 0) { fputs(b ? "true" : "false", stdout); break; }
      printf("(\\%s ", N->name[p.node]);
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
    char sbuf[4096];
    int slen = net_read_string(n, r, sbuf, sizeof(sbuf));
    if (slen >= 0) { printf("\"%s\"", sbuf); return 0; }
    long v = net_read_int(n, r);
    if (v >= 0) { printf("%ld", v); return 0; }
    int b = net_read_bool(n, r);
    if (b >= 0) { fputs(b ? "true" : "false", stdout); return 0; }
  }
  vis_print = calloc((size_t)(n->nn + 1), 1);
  print_port(r, 0);
  free(vis_print);
  vis_print = NULL;
  return 0;
}

static Port net_alloc_scott(Net *n, long k) {
  Scope sc = scope_nil(); Port cur = (Port){-1, -1};
  for (long i = 0; i <= k; i++) {
    Port sz = net_alloc(n, LAM, sc, "_sz"), ss = net_alloc(n, LAM, sc, "_ss");
    net_link(n, (Port){sz.node, 2}, (Port){ss.node, 0}, 0);
    if (i == 0) { net_link(n, (Port){ss.node, 2}, (Port){sz.node, 1}, 0); }
    else {
      Port app = net_alloc(n, APP, sc, "");
      net_link(n, (Port){app.node, 0}, (Port){ss.node, 1}, 0); net_link(n, (Port){app.node, 2}, cur, 0);
      net_link(n, (Port){ss.node, 2}, (Port){app.node, 1}, 0);
    }
    cur = (Port){sz.node, 0};
  }
  return cur;
}

static Port net_alloc_string(Net *n, const char *s) {
  Scope sc = scope_nil();
  Port c_nil = net_alloc(n, LAM, sc, "_cl"), n_nil = net_alloc(n, LAM, sc, "_nl");
  Port bt = net_alloc(n, LAM, sc, "_bt"), bf = net_alloc(n, LAM, sc, "_bf");
  net_link(n, (Port){c_nil.node, 2}, (Port){n_nil.node, 0}, 0); net_link(n, (Port){n_nil.node, 2}, (Port){bt.node, 0}, 0);
  net_link(n, (Port){bt.node, 2}, (Port){bf.node, 0}, 0);       net_link(n, (Port){bf.node, 2}, (Port){bt.node, 1}, 0);
  Port cur = (Port){c_nil.node, 0};
  for (long i = (long)strlen(s) - 1; i >= 0; i--) {
    Port ch = net_alloc_scott(n, (unsigned char)s[i]);
    Port c_lam = net_alloc(n, LAM, sc, "_cl"), n_lam = net_alloc(n, LAM, sc, "_nl");
    Port a1 = net_alloc(n, APP, sc, ""), a2 = net_alloc(n, APP, sc, "");
    net_link(n, (Port){c_lam.node, 2}, (Port){n_lam.node, 0}, 0);
    net_link(n, (Port){a1.node, 0}, (Port){c_lam.node, 1}, 0); net_link(n, (Port){a1.node, 2}, ch, 0);
    net_link(n, (Port){a2.node, 0}, (Port){a1.node, 1}, 0); net_link(n, (Port){a2.node, 2}, cur, 0);
    net_link(n, (Port){n_lam.node, 2}, (Port){a2.node, 1}, 0);
    cur = (Port){c_lam.node, 0};
  }
  return cur;
}

static void chomp(char *s) {
  size_t l = strlen(s);
  if (l > 0 && s[l - 1] == '\n') s[l - 1] = 0;
}
static void read_stream(FILE *f, char *buf, size_t sz, int is_pipe) {
  if (!f) return;
  size_t nr = fread(buf, 1, sz - 1, f);
  buf[nr] = 0; chomp(buf);
  if (is_pipe) pclose(f); else fclose(f);
}
static void read_stdin(char *buf, size_t sz) {
  if (!fgets(buf, (int)sz, stdin)) buf[0] = 0; else chomp(buf);
}

static inline int is_io_tag(const char *s) {
  return !strcmp(s, "_iod") || !strcmp(s, "_iop") || !strcmp(s, "_ior") || !strcmp(s, "_iow");
}

int net_run_io(Net *n, long step_limit) {
  N = n;
  int did_io = 0;
  for (;;) {
    Port r = dup_hop(n, wire((Port){0, 0}));
    if (r.node < 0 || r.node >= n->nn || n->dead[r.node] || n->tag[r.node] != LAM) break;
    if (!strcmp(n->name[r.node], "_iod")) return 1;
    if (!strcmp(n->name[r.node], "_iop")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      if (a0.node < 0 || n->tag[a0.node] != APP) break;
      Port a00 = dup_hop(n, wire((Port){a0.node, 0}));
      FILE *out_fp = stdout;
      Port msg_p = dup_hop(n, wire((Port){a0.node, 2}));
      if (a00.node >= 0 && n->tag[a00.node] == APP) {
        long dst_fd = net_read_int(n, dup_hop(n, wire((Port){a00.node, 2})));
        if (dst_fd == 2) out_fp = stderr;
      }
      if (!net_try_ffi(n, msg_p)) {
        char msg[4096];
        int slen = net_read_string(n, msg_p, msg, sizeof(msg));
        if (slen >= 0) fputs(msg, out_fp);
        else {
          long v = net_read_int(n, msg_p);
          if (v >= 0) fprintf(out_fp, "%ld", v);
          else { int b = net_read_bool(n, msg_p); fputs(b >= 0 ? (b ? "true" : "false") : "?", out_fp); }
        }
      }
      fflush(out_fp);
      Port next_p = wire((Port){body.node, 2});
      if (next_p.node >= 0 && next_p.node < n->nn && !n->dead[next_p.node] && n->tag[next_p.node] == LAM && !is_io_tag(n->name[next_p.node])) {
        Port app = net_alloc(n, APP, scope_nil(), ""), unit = net_alloc_scott(n, 0);
        net_link(n, (Port){app.node, 0}, next_p, 1); net_link(n, (Port){app.node, 2}, unit, 1);
        net_link(n, (Port){0, 0}, (Port){app.node, 1}, 1);
      } else net_link(n, (Port){0, 0}, next_p, 1);
      net_reduce_readback(n, step_limit);
      did_io = 1;
      continue;
    }
    if (!strcmp(n->name[r.node], "_ior") || !strcmp(n->name[r.node], "_iow")) {
      Port body = dup_hop(n, wire((Port){r.node, 2}));
      if (body.node < 0 || n->tag[body.node] != APP) break;
      Port a0 = dup_hop(n, wire((Port){body.node, 0}));
      Port cb = wire((Port){body.node, 2});
      Port src_p = (a0.node >= 0 && n->tag[a0.node] == APP) ? dup_hop(n, wire((Port){a0.node, 2})) : (Port){-1, -1};

      char in_buf[4096] = {0};
      long res_int = -1, ffi_int = 0;
      int is_int = 0;
      char ffi_str[4096] = {0};
      int ffi_res = (src_p.node >= 0) ? run_ffi(n, src_p, &ffi_int, ffi_str, sizeof(ffi_str)) : 0;
      if (ffi_res == 1) { res_int = ffi_int; is_int = 1; }
      else if (ffi_res == 2) snprintf(in_buf, sizeof(in_buf), "%s", ffi_str);
      else if (src_p.node < 0) read_stdin(in_buf, sizeof(in_buf));
      else {
        long fd = net_read_int(n, src_p);
        if (fd == 0) read_stdin(in_buf, sizeof(in_buf));
        else if (fd > 0) {
          ssize_t nr = read((int)fd, in_buf, sizeof(in_buf) - 1);
          if (nr > 0) { in_buf[nr] = 0; chomp(in_buf); }
        } else {
          char src[1024];
          if (net_read_string(n, src_p, src, sizeof(src)) >= 0) {
            if (!strcmp(src, "stdin") || !strcmp(src, "0")) read_stdin(in_buf, sizeof(in_buf));
            else if (src[0] == '!' || !strncmp(src, "cmd:", 4)) read_stream(popen(src[0] == '!' ? src + 1 : src + 4, "r"), in_buf, sizeof(in_buf), 1);
            else if (!strncmp(src, "sleep:", 6)) { res_int = strtol(src + 6, NULL, 10); if (res_int > 0) usleep((useconds_t)(res_int * 1000)); is_int = 1; }
            else read_stream(fopen(!strncmp(src, "file:", 5) ? src + 5 : src, "r"), in_buf, sizeof(in_buf), 0);
          }
        }
      }
      char *endptr = NULL;
      long val = (!is_int && in_buf[0]) ? strtol(in_buf, &endptr, 10) : -1;
      Port arg = is_int ? net_alloc_scott(n, res_int) :
                 (in_buf[0] && endptr && !*endptr && val >= 0) ? net_alloc_scott(n, val) :
                 net_alloc_string(n, in_buf);
      Port app = net_alloc(n, APP, scope_nil(), "");
      net_link(n, (Port){app.node, 0}, cb, 1);
      net_link(n, (Port){app.node, 2}, arg, 1);
      net_link(n, (Port){0, 0}, (Port){app.node, 1}, 1);
      net_reduce_readback(n, step_limit);
      did_io = 1;
      continue;
    }
    break;
  }
  return did_io;
}

