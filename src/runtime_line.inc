/* Lin `.line` binary container runtime (std — not core): #included into src/compile.c serializes/deserializes a reduced Net to a self-running .line executable (shebang re-invokes the producing engine) */
static char self_path[4096] = "lin";

void lin_set_self_path(const char *p) {
  if (!p || !*p) return;
  char *rp = realpath(p, NULL);
  snprintf(self_path, sizeof self_path, "%s", rp ? rp : p);
  free(rp);
}

int net_save_line(Net *n, const char *path) {
  FILE *f = fopen(path, "wb"); if (!f) return 0;
  fprintf(f, "#!%s\n", self_path); fwrite("LINE", 1, 4, f);
  uint32_t nnamed = 0; for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) nnamed++;
  uint32_t meta[4] = { 3, (uint32_t)n->nn, (uint32_t)n->nlv, nnamed };
  fwrite(meta, sizeof(uint32_t), 4, f);
  fwrite(n->tag, 1, (size_t)n->nn, f); fwrite(n->dead, 1, (size_t)n->nn, f);
  fwrite(n->wire, sizeof(Port) * 3, (size_t)n->nn, f);
  fwrite(n->scope, sizeof(Scope), (size_t)n->nn, f);
  for (int i = 0; i < n->nn; i++) if (n->name[i] && n->name[i][0]) {
    uint32_t id = i; uint8_t len = (uint8_t)strlen(n->name[i]);
    fwrite(&id, 4, 1, f); fwrite(&len, 1, 1, f); fwrite(n->name[i], 1, len, f);
  }
  /* the level trie: parents come before children by construction, so ids reload directly */
  if (n->nlv > 0) { fwrite(n->lv_parent + 1, sizeof(int), (size_t)n->nlv, f);
                    fwrite(n->lv_bit + 1, 1, (size_t)n->nlv, f); }
  fclose(f); chmod(path, 0755); return 1;
}

int net_load_line(Net *n, const char *path) {
  FILE *f = fopen(path, "rb"); if (!f) return 0;
  char buf[64];
  if (fgets(buf, sizeof buf, f) && buf[0] == '#' && buf[1] == '!') {} else fseek(f, 0, SEEK_SET);
  char magic[4]; uint32_t meta[4];
  if (fread(magic, 1, 4, f) != 4 || memcmp(magic, "LINE", 4) || fread(meta, 4, 4, f) != 4 || meta[0] != 3) {
    fclose(f); return 0;
  }
  int nn = (int)meta[1], nlv = (int)meta[2]; uint32_t nnamed = meta[3];
  net_init(n, nn + 16); n->nn = nn;

  if (fread(n->tag, 1, (size_t)nn, f) != (size_t)nn || fread(n->dead, 1, (size_t)nn, f) != (size_t)nn ||
      fread(n->wire, sizeof(Port) * 3, (size_t)nn, f) != (size_t)nn ||
      fread(n->scope, sizeof(Scope), (size_t)nn, f) != (size_t)nn) { fclose(f); net_free(n); return 0; }
  for (uint32_t k = 0; k < nnamed; k++) {
    uint32_t id = 0; uint8_t len = 0;
    if (fread(&id, 4, 1, f) != 1 || fread(&len, 1, 1, f) != 1) { fclose(f); net_free(n); return 0; }
    n->name[id] = malloc((size_t)len + 1);
    if (fread(n->name[id], 1, len, f) != len) { fclose(f); net_free(n); return 0; }
    n->name[id][len] = 0;
  }
  if (nlv > 0) {
    int *par = malloc((size_t)nlv * sizeof(int));
    unsigned char *bit = malloc((size_t)nlv);
    if (!par || !bit || fread(par, sizeof(int), (size_t)nlv, f) != (size_t)nlv ||
        fread(bit, 1, (size_t)nlv, f) != (size_t)nlv) { free(par); free(bit); fclose(f); net_free(n); return 0; }
    net_level_set(n, nlv, par, bit);
    free(par); free(bit);
  }
  fclose(f);
  /* seed the self-collecting activation queue: the active-redex list is not serialized, so a freshly loaded net has an empty queue; reconstruct all live principal pairs (including ROOT) so it actually reduces */
  for (int i = 0; i < n->nn; i++)
    if (n->wire[i * 3].port == 0 && n->wire[i * 3].node > i)
      lin_enqueue(n, (Port){i, 0}, n->wire[i * 3]);
  return 1;
}
