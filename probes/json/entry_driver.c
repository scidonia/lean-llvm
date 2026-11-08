/*
 * Row driver for the entry unit's installed object.
 *
 *   entry_driver [--corpus <file> ...] [--arms]
 *
 * The object is `kernel/json/entry.c` compiled with the measured compiler
 * line; this driver declares the ABI rather than including `entry.h`, so a
 * changed header cannot make the driver agree with itself.  A row is one
 * `(mask stream, blk0, nblk, k)` call under one kernel, printed as
 *
 *   <source>\t<label>\t<kernel>\t<count>\t<words>\t<multi>\t<sentinel>
 *
 * with `kernel` `p` for POS8 and `b` for B8, `count` the returned cursor `k'`,
 * `words` the first `k'` `i32` words as `0x` and exactly eight lowercase hex
 * digits each (comma-separated, `-` when `k'` is 0), `multi` 1 when a block of
 * the stream has more than eight set lanes, and `sentinel` the word at lane
 * `k'+8` — the first lane neither kernel writes.  The line is comparable,
 * line for line, with `leanllvm-json-entry`.
 *
 * Staging.  The mask stream is placed at **offset 1** of a heap buffer, so the
 * `uint64_t *` the ABI takes is misaligned: the model addresses bytes and has
 * no alignment, and the object is not asked to need one.  Every output buffer
 * is filled with `0xA5` before the call, so a lane the body does not write —
 * and the word at `k'+8` — reads back as `0xa5a5a5a5`, and a row whose cursor
 * starts at `k` begins with `k` sentinel words.  The buffer holds `k' + 8`
 * lanes plus slack for the lanes POS8 and B8 write past `k'`.
 *
 * `leanllvm_json_entry_table` is called once before the first row: the POS8
 * kernel reads the unit's own static table, which only the unit's initialiser
 * fills, and nothing else calls it.
 *
 * Rows: each corpus file as given, then, under `--arms`, the 64 single-lane
 * masks, the 256 masks that set group 0's byte to each value, 65536 splitmix64
 * masks seeded at 0x243F6A8885A308D3, the empty mask, the full mask, and the
 * 1025-mask long-loop stream built from the corpus masks concatenated in file
 * order and repeated.  Every arm starts at `blk0 = 0` and `k = 0`.  Each stream
 * contributes one row per kernel, POS8 first.
 *
 * This is test infrastructure: it calls the object and prints what the object
 * wrote.  It asserts nothing about the positions; the comparison against the
 * Lean body is what says the two agree.
 *
 * Exit status: 0 on success, 2 when an argument is missing or a file cannot be
 * read, so a setup fault is never read as a positions result.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                         uint64_t nblk, uint32_t *out,
                                         uint64_t k);
extern uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                       uint64_t nblk, uint32_t *out,
                                       uint64_t k);
extern void leanllvm_json_entry_table(uint32_t *dst);

#define SENTINEL 0xA5u
#define CORPUS_MAX 64
#define RANDOM_COUNT 65536
#define NBLK_COUNT 1025

static uint32_t table[256 * 8];

static void *xmalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (p == NULL) {
    fprintf(stderr, "entry_driver: out of memory\n");
    exit(2);
  }
  return p;
}

/* One mask stream as the caller hands it to the ABI: bytes at `+1`. */
typedef struct {
  uint8_t *bytes; /* 8 * n + 1; the stream starts at bytes + 1 */
  size_t n;
} stream;

static stream stream_new(const uint64_t *masks, size_t n) {
  stream s;
  s.bytes = xmalloc(8 * n + 1);
  s.n = n;
  s.bytes[0] = 0; /* the byte before the stream is not part of it */
  memcpy(s.bytes + 1, masks, 8 * n);
  return s;
}

static void stream_free(stream *s) {
  free(s->bytes);
  s->bytes = NULL;
}

static const uint64_t *stream_masks(const stream *s) {
  return (const uint64_t *)(const void *)(s->bytes + 1);
}

static int popcount64(uint64_t m) {
  return __builtin_popcountll(m);
}

/* Whether any mask of the stream has more than eight set lanes. */
static int stream_multi(const uint64_t *masks, size_t n) {
  for (size_t i = 0; i < n; i++) {
    if (popcount64(masks[i]) > 8) return 1;
  }
  return 0;
}

/* One row: stage the buffer, call the kernel, print what it wrote. */
static void row(const char *source, const char *label, char kernel,
                const stream *s, uint64_t blk0, uint64_t k) {
  /* `k'` cannot exceed `k + 64 * n`, and both kernels may write up to eight
   * lanes past it; nine lanes past `k'` are read. */
  size_t lanes = (size_t)k + 64 * s->n + 16;
  size_t bytes = 4 * lanes;
  uint32_t *out = xmalloc(bytes);
  memset(out, SENTINEL, bytes);

  uint64_t count;
  if (kernel == 'p') {
    count = leanllvm_json_entry_pos8(stream_masks(s), blk0, s->n, out, k);
  } else {
    count = leanllvm_json_entry_b8(stream_masks(s), blk0, s->n, out, k);
  }
  if (count + 8 >= lanes) {
    fprintf(stderr, "entry_driver: %s\t%s\t%c: count %llu outside the buffer\n",
            source, label, kernel, (unsigned long long)count);
    free(out);
    exit(2);
  }

  printf("%s\t%s\t%c\t%llu\t", source, label, kernel,
         (unsigned long long)count);
  if (count == 0) {
    fputs("-", stdout);
  } else {
    for (uint64_t i = 0; i < count; i++) {
      printf("%s0x%08x", i ? "," : "", out[i]);
    }
  }
  printf("\t%d\t0x%08x\n", stream_multi(stream_masks(s), s->n), out[count + 8]);

  free(out);
}

/* Both kernels over one stream: POS8 then B8. */
static void row_pair(const char *source, const char *label, const stream *s,
                     uint64_t blk0, uint64_t k) {
  row(source, label, 'p', s, blk0, k);
  row(source, label, 'b', s, blk0, k);
}

/* --- The corpus files: `blk0`, `k` and the masks a committed file carries. --- */

static int read_all(const char *path, char **text, size_t *len) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "entry_driver: cannot read '%s'\n", path);
    return 0;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fprintf(stderr, "entry_driver: cannot seek '%s'\n", path);
    fclose(f);
    return 0;
  }
  long size = ftell(f);
  if (size < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "entry_driver: cannot measure '%s'\n", path);
    fclose(f);
    return 0;
  }
  char *buf = xmalloc((size_t)size + 1);
  if (size > 0 && fread(buf, 1, (size_t)size, f) != (size_t)size) {
    fprintf(stderr, "entry_driver: short read on '%s'\n", path);
    free(buf);
    fclose(f);
    return 0;
  }
  buf[size] = '\0';
  fclose(f);
  *text = buf;
  *len = (size_t)size;
  return 1;
}

/* The unsigned decimal after `key` (`"blk0": 3`), or 0 when absent.  `key`
 * carries its own quotes, so `"k"` is not found inside another field. */
static int field_u64(const char *text, const char *key, uint64_t *v) {
  const char *p = strstr(text, key);
  if (p == NULL) return 0;
  p += strlen(key);
  while (*p == ' ' || *p == '\t' || *p == '\n' || *p == '\r' || *p == ':') p++;
  if (*p < '0' || *p > '9') return 0;
  uint64_t x = 0;
  while (*p >= '0' && *p <= '9') {
    x = x * 10 + (uint64_t)(*p - '0');
    p++;
  }
  *v = x;
  return 1;
}

/* The masks array: every `0x` and sixteen hex digits after the key. */
static uint64_t *corpus_masks(const char *text, size_t *count) {
  const char *p = strstr(text, "\"masks\"");
  if (p == NULL) return NULL;
  size_t cap = 8, n = 0;
  uint64_t *masks = xmalloc(cap * sizeof *masks);
  while ((p = strstr(p, "0x")) != NULL) {
    char hex[17];
    size_t i = 0;
    for (i = 0; i < 16; i++) {
      char c = p[2 + i];
      if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) break;
      hex[i] = c;
    }
    if (i != 16) {
      p += 2;
      continue;
    }
    hex[16] = '\0';
    if (n == cap) {
      cap *= 2;
      masks = realloc(masks, cap * sizeof *masks);
      if (masks == NULL) {
        fprintf(stderr, "entry_driver: out of memory\n");
        exit(2);
      }
    }
    masks[n++] = strtoull(hex, NULL, 16);
    p += 18;
  }
  *count = n;
  return masks;
}

static int emit_corpus(const char *path) {
  char *text = NULL;
  size_t len = 0;
  if (!read_all(path, &text, &len)) return 2;

  uint64_t blk0 = 0, k = 0, count = 0;
  if (!field_u64(text, "\"blk0\"", &blk0) || !field_u64(text, "\"k\"", &k)) {
    fprintf(stderr, "entry_driver: '%s' does not carry blk0 and k\n", path);
    free(text);
    return 2;
  }
  uint64_t *masks = corpus_masks(text, (size_t *)&count);
  free(text);
  if (masks == NULL || count == 0) {
    fprintf(stderr, "entry_driver: '%s' carries no masks\n", path);
    free(masks);
    return 2;
  }

  char label[64];
  snprintf(label, sizeof label, "blk0%llu/k%llu/masks%llu",
           (unsigned long long)blk0, (unsigned long long)k,
           (unsigned long long)count);
  stream s = stream_new(masks, (size_t)count);
  row_pair(path, label, &s, blk0, k);
  stream_free(&s);
  free(masks);
  return 0;
}

/* --- The generated arms. --- */

static void emit_lane_arm(void) {
  char label[16];
  for (int nn = 0; nn < 64; nn++) {
    uint64_t mask = UINT64_C(1) << nn;
    snprintf(label, sizeof label, "lane%02d", nn);
    stream s = stream_new(&mask, 1);
    row_pair("arm:lane", label, &s, 0, 0);
    stream_free(&s);
  }
}

static void emit_byte_arm(void) {
  char label[16];
  for (int hh = 0; hh < 256; hh++) {
    uint64_t mask = (uint64_t)hh;
    snprintf(label, sizeof label, "val%02x", hh);
    stream s = stream_new(&mask, 1);
    row_pair("arm:byte", label, &s, 0, 0);
    stream_free(&s);
  }
}

static uint64_t splitmix_next(uint64_t *x) {
  uint64_t z = (*x += UINT64_C(0x9E3779B97F4A7C15));
  z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
  return z ^ (z >> 31);
}

/* The mask `i`: one splitmix64 step from the fixed seed. */
static uint64_t random_mask(uint64_t i) {
  uint64_t x = UINT64_C(0x243F6A8885A308D3) +
               i * UINT64_C(0x9E3779B97F4A7C15);
  return splitmix_next(&x);
}

static void emit_random_arm(void) {
  char label[64];
  for (uint64_t i = 0; i < RANDOM_COUNT; i++) {
    uint64_t mask = random_mask(i);
    snprintf(label, sizeof label, "idx%llu/mask%016llx",
             (unsigned long long)i, (unsigned long long)mask);
    stream s = stream_new(&mask, 1);
    row_pair("arm:random", label, &s, 0, 0);
    stream_free(&s);
  }
}

static void emit_shape_arm(const char *source, const char *label,
                           uint64_t mask) {
  stream s = stream_new(&mask, 1);
  row_pair(source, label, &s, 0, 0);
  stream_free(&s);
}

/* The long-loop stream: the corpus masks concatenated in file order and
 * repeated to `NBLK_COUNT`. */
static void emit_nblk_arm(uint64_t *all, size_t n) {
  uint64_t *masks = xmalloc(NBLK_COUNT * sizeof *masks);
  if (n == 0) {
    fprintf(stderr, "entry_driver: the nblk arm has no corpus masks\n");
    free(masks);
    exit(2);
  }
  for (size_t i = 0; i < NBLK_COUNT; i++) masks[i] = all[i % n];
  stream s = stream_new(masks, NBLK_COUNT);
  row_pair("arm:nblk", "masks1025", &s, 0, 0);
  stream_free(&s);
  free(masks);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: entry_driver [--corpus <file> ...] [--arms]\n");
    return 2;
  }

  const char *corpus[CORPUS_MAX];
  int corpus_count = 0;
  int arms = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--corpus") == 0) {
      if (i + 1 >= argc) {
        fprintf(stderr, "entry_driver: missing path after --corpus\n");
        return 2;
      }
      if (corpus_count >= CORPUS_MAX) {
        fprintf(stderr, "entry_driver: too many corpus paths\n");
        return 2;
      }
      corpus[corpus_count++] = argv[++i];
    } else if (strcmp(argv[i], "--arms") == 0) {
      arms = 1;
    } else {
      fprintf(stderr, "entry_driver: unknown argument '%s'\n", argv[i]);
      return 2;
    }
  }

  if (corpus_count == 0 && !arms) {
    fprintf(stderr, "entry_driver: one of --corpus or --arms is required\n");
    return 2;
  }

  /* The POS8 body reads the unit's own static table; the only thing that fills
   * it is the unit's initialiser, reached through this call. */
  leanllvm_json_entry_table(table);

  /* The corpus masks, in the order the corpus files were given, for the
   * long-loop arm's stream. */
  uint64_t *all = NULL;
  size_t all_count = 0, all_cap = 0;

  for (int i = 0; i < corpus_count; i++) {
    int status = emit_corpus(corpus[i]);
    if (status != 0) {
      free(all);
      return status;
    }
    char *text = NULL;
    size_t len = 0;
    if (!read_all(corpus[i], &text, &len)) {
      free(all);
      return 2;
    }
    size_t n = 0;
    uint64_t *masks = corpus_masks(text, &n);
    free(text);
    if (masks == NULL || n == 0) {
      fprintf(stderr, "entry_driver: '%s' carries no masks\n", corpus[i]);
      free(masks);
      free(all);
      return 2;
    }
    if (all_count + n > all_cap) {
      all_cap = (all_count + n) * 2;
      all = realloc(all, all_cap * sizeof *all);
      if (all == NULL) {
        fprintf(stderr, "entry_driver: out of memory\n");
        free(masks);
        exit(2);
      }
    }
    memcpy(all + all_count, masks, n * sizeof *masks);
    all_count += n;
    free(masks);
  }

  if (arms) {
    emit_lane_arm();
    emit_byte_arm();
    emit_random_arm();
    emit_shape_arm("arm:empty", "empty", 0);
    emit_shape_arm("arm:full", "full", ~(uint64_t)0);
    emit_nblk_arm(all, all_count);
  }

  free(all);
  return 0;
}
