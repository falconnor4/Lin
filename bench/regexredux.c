/* regex-redux (Computer Language Benchmarks Game): a DNA sequence of 200,000 letters, drawn by the benchmark's
   generator from its IUB alphabet, is searched for nine variant patterns, then rewritten by five substitutions,
   with POSIX regular expressions.  The answer combines the nine counts and the rewritten length. */
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static char iub(long r) {
  static const long b[] = {37791, 54587, 71383, 109174, 111973, 114772, 117571, 120370, 123170, 125969, 128768, 131567, 134366, 137165};
  static const char c[] = "acgtBDHKMNRSVWY";
  for (int i = 0; i < 14; i++) if (r < b[i]) return c[i];
  return c[14];
}
static long count(const char *pat, const char *s) {
  regex_t re; regmatch_t m; long n = 0; regcomp(&re, pat, REG_EXTENDED);
  for (const char *p = s; !regexec(&re, p, 1, &m, 0); p += m.rm_eo) n++;
  regfree(&re); return n;
}
static char *subst(const char *pat, const char *rep, char *s) {
  regex_t re; regmatch_t m; regcomp(&re, pat, REG_EXTENDED);
  size_t cap = strlen(s) * 2 + 16, len = 0, rl = strlen(rep); char *out = malloc(cap); const char *p = s;
  while (!regexec(&re, p, 1, &m, 0)) {
    if (len + (size_t)m.rm_so + rl + 1 > cap) { cap = cap * 2 + rl; out = realloc(out, cap); }
    memcpy(out + len, p, (size_t)m.rm_so); len += (size_t)m.rm_so; memcpy(out + len, rep, rl); len += rl; p += m.rm_eo;
  }
  size_t tl = strlen(p); if (len + tl + 1 > cap) { cap = len + tl + 1; out = realloc(out, cap); }
  memcpy(out + len, p, tl + 1); regfree(&re); free(s); return out;
}
int main(void) {
  long n = 200000, seed = 42; char *s = malloc((size_t)n + 1);
  for (long i = 0; i < n; i++) { seed = (seed * 3877 + 29573) % 139968; s[i] = iub(seed); }
  s[n] = 0;
  static const char *vs[] = { "agggtaaa|tttaccct", "[cgt]gggtaaa|tttaccc[acg]", "a[act]ggtaaa|tttacc[agt]t", "ag[act]gtaaa|tttac[agt]ct",
    "agg[act]taaa|ttta[agt]cct", "aggg[acg]aaa|ttt[cgt]ccct", "agggt[cgt]aa|tt[acg]accct", "agggta[cgt]a|t[acg]taccct", "agggtaa[cgt]|[acg]ttaccct" };
  long acc = 0; for (int i = 0; i < 9; i++) acc += (i + 1) * count(vs[i], s);
  s = subst("tHa[Nt]", "<4>", s); s = subst("aND|caN|Ha[DS]|WaS", "<3>", s); s = subst("a[NSt]|BY", "<2>", s);
  s = subst("<[^>]*>", "|", s); s = subst("\\|[^|][^|]*\\|", "-", s);
  printf("%ld\n", acc + 1000000L * (long)strlen(s)); free(s); return 0;
}
