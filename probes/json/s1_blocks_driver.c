/*
 * Row driver for the contracted stage-1 block unit's installed object.
 *
 *   s1_blocks_driver --emit-block
 *   s1_blocks_driver [--corpus <path> ...] [--arms]
 *   s1_blocks_driver [--corpus <path> ...] [--arms] --ascii-expected
 *   s1_blocks_driver [--corpus <path> ...] [--arms] --utf8-expected
 *
 * The object is `kernel/json/s1_blocks.c` compiled with the measured compiler
 * line, with `kernel/json/escape.c` as the escape list it calls; this driver
 * declares the ABI rather than including `s1_blocks.h`, so a changed header
 * cannot make the driver agree with itself.  Every row stages a document padded
 * with zeroes to a whole number of blocks at **offset 4** of a buffer — a
 * misaligned pointer, with the three bytes before it zero (the UTF-8 DFA's
 * load-form carry) — fills an `ent` array of `8 * blocks` bytes and a
 * position-stream buffer with `0xA5`, stages `*nxp` at zero and the two
 * `xcarry` words at zero, calls `leanllvm_json_s1_blocks`, and prints
 *
 *   <source>\t<label>\t<arm>\t<blocks>\t<touched>\t<ent words…>
 *   \t<nxp>\t<xp bytes>\t<xcarry lo>\t<xcarry hi>\t<ret>
 *
 * with `arm` in {0, 2, 4, 6} (bit 1 the escape list, bit 2 the ungated UTF-8
 * gate), one `0x`-and-sixteen-hex-digit word per block, the count, carry and
 * return words the same way, and the first sixty-four `xp` bytes as one
 * hundred and twenty-eight lowercase hex digits.  The position-stream buffer is
 * larger than the sixty-four logged bytes so the escape list's eight-entry
 * batch reserve stays inside it in C; only the prefix is printed, and that
 * prefix is the whole region the Lean body stages.  `touched` is `1` when `xp`,
 * `nxp` and `xcarry` are still the staged bytes, so a list-free row reads `1`
 * and a list row whose block has an escape position reads `0`.  `ret` is the
 * object's two-bit word: bit 0 the ASCII probe (`1` when every document byte is
 * below `0x80`), bit 1 the UTF-8 stage's error word (`1` when the staged window
 * is not a valid prefix).  It is the last column so the `ent` words stay the
 * first `0x` fields.
 *
 * `--ascii-expected` prints one line per document instead of rows —
 * `<source>\t<label>\t<0|1>` — with the probe computed from the staged
 * document bytes rather than from the object, so the check can compare the
 * object's return with the document's actual high bits.  `--utf8-expected`
 * prints the same shape with `1` when a scalar reference validator rejects the
 * staged window, so the check can compare the object's bit 1 with a reader that
 * shares no code with the object.  The documents are selected and ordered
 * exactly as for the row streams.
 *
 * Rows, each document once per arm, arm ascending: the mixed block (`mixed`,
 * `len64`); each corpus file as one document, in the order given (a directory
 * contributes the files directly inside it, in name order); then, under
 * `--arms`, the byte sweep (every value at every lane position of a
 * sixty-four-byte document), the short arm (lengths 1…65 of a fixed splitmix64
 * stream), every four-byte sequence over the eight-symbol escape alphabet
 * `22 5C 2C 7B 01 20 61 0A`, and 512 splitmix64 documents seeded at
 * 0x243F6A8885A308D3 with length `1 + (37 * i) mod 128`.  The labels carry the
 * document's length as `len<n>`.
 *
 * This is test infrastructure: it calls the object and prints what the object
 * wrote.  It asserts nothing about the body; the comparison against
 * `leanllvm-json-s1-blocks` is what says the two agree.
 *
 * Exit status: 0 on success, 2 when an argument is missing or a file cannot be
 * read, so a setup fault is never read as a body result.
 */
#include <dirent.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

typedef struct {
  uint64_t esc_open, esc_ppar;
} s1b_carry;

extern uint64_t leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n,
                                        uint64_t *ent, uint32_t *xp,
                                        uint64_t *nxp, uint64_t *xcarry,
                                        uint64_t arm);

#define BLOCK_LEN 64
#define DOC_CAP 256
#define MAX_BLOCKS 4
#define XP_CAP 4096
#define XP_OBS 64
#define DOC_OFFSET 4 /* the document's offset in doc_buffer, with 3 zero bytes before */

/* The mixed block `leanllvm-json-s1-blocks --emit-block` writes; the two are
 * required to be the same 64 bytes by tests/json-s1-blocks/check.sh. */
static const uint8_t mixed_block[BLOCK_LEN] = {
  0x22, 0x6B, 0x5C, 0x22, 0x2C, 0x20, 0x31, 0x5D,
  0x0A, 0x09, 0x0D, 0x5C, 0x5C, 0x22, 0x3A, 0x78,
  0x22, 0x61, 0x22, 0x7B, 0x7D, 0x5B, 0x5D, 0x2C,
  0x20, 0x01, 0x1F, 0x7F, 0x22, 0x5C, 0x74, 0x22,
  0x5C, 0x6E, 0x22, 0x2C, 0x09, 0x5C, 0x22, 0x3A,
  0x64, 0x5B, 0x5D, 0x7B, 0x7D, 0x20, 0x0D, 0x30,
  0x22, 0x5C, 0x5C, 0x5C, 0x22, 0x2C, 0x76, 0x20,
  0x09, 0x0A, 0x22, 0x7A, 0x1F, 0x79, 0x5C, 0x22
};

/* The escape alphabet: unescaped quote, backslash, comma, brace, control,
 * space, ordinary content and newline. */
static const uint8_t alphabet[8] = { 0x22, 0x5C, 0x2C, 0x7B,
                                     0x01, 0x20, 0x61, 0x0A };

#define ALPHABET_COUNT 4096 /* 8^4 */
#define RANDOM_COUNT 512
#define SHORT_COUNT 65

#define GAMMA UINT64_C(0x9E3779B97F4A7C15)
#define RANDOM_SEED UINT64_C(0x243F6A8885A308D3)
#define SHORT_SEED UINT64_C(0x13198A2E03707344)

static _Alignas(64) uint8_t doc_buffer[DOC_CAP + DOC_OFFSET];
static _Alignas(8) uint64_t ent_array[MAX_BLOCKS];
static _Alignas(4) uint8_t xp_stream[XP_CAP];
static _Alignas(8) uint64_t nxp_word;
static _Alignas(8) uint64_t carry_words[2];

static uint64_t blocks_of(uint64_t n) { return (n + 63) / 64; }

static uint64_t splitmix_next(uint64_t *x) {
  uint64_t z = (*x += GAMMA);
  z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
  return z ^ (z >> 31);
}

/* `words` splitmix64 outputs, little-endian, at `out`. */
static void splitmix_bytes(uint64_t seed, size_t words, uint8_t *out) {
  uint64_t x = seed;
  for (size_t w = 0; w < words; w++) {
    uint64_t word = splitmix_next(&x);
    for (int k = 0; k < 8; k++) out[w * 8 + (size_t)k] = (uint8_t)(word >> (8 * k));
  }
}

static int xp_still_sentinel(void) {
  for (int i = 0; i < XP_OBS; i++) {
    if (xp_stream[i] != 0xA5) return 0;
  }
  return nxp_word == 0 && carry_words[0] == 0 && carry_words[1] == 0;
}

/* Whether every document byte is below 0x80, the unit's ASCII probe read from
 * the staged bytes rather than from the object's return.  Padding is zero and
 * below 0x80, so the document and the padded window agree. */
static int all_ascii(const uint8_t *bytes, uint64_t len) {
  for (uint64_t i = 0; i < len; i++) {
    if (bytes[i] >= 0x80) return 0;
  }
  return 1;
}

/* `--ascii-expected`: one line per document, the probe computed from the
 * document bytes, in the same order as the row streams. */
static int ascii_expected = 0;

/* `--utf8-expected`: one line per document, the UTF-8 error bit computed from
 * the staged window by a scalar reference reader.  It shares no code with the
 * object: the window is three zero bytes, the document, and zero padding to the
 * 64-byte boundary, and the answer is whether the window is a valid UTF-8
 * prefix (a trailing incomplete character is allowed, which is why the padding
 * is what rejects a truncated character inside the document). */
static int utf8_expected = 0;

static int utf8_prefix_window(const uint8_t *bytes, uint64_t len) {
  uint64_t blocks = blocks_of(len);
  uint64_t total = 3 + 64 * blocks;
  int need = 0;
  unsigned lo = 0x80, hi = 0xBF;
  for (uint64_t w = 0; w < total; w++) {
    unsigned c = (w < 3) ? 0 : (w - 3 < len ? bytes[w - 3] : 0);
    if (need) {
      if (c < lo || c > hi) return 0;
      need--;
      lo = 0x80;
      hi = 0xBF;
    } else if (c < 0x80) {
      /* ASCII */
    } else if (c >= 0xC2 && c <= 0xDF) {
      need = 1; lo = 0x80; hi = 0xBF;
    } else if (c == 0xE0) {
      need = 2; lo = 0xA0; hi = 0xBF;
    } else if ((c >= 0xE1 && c <= 0xEC) || (c >= 0xEE && c <= 0xEF)) {
      need = 2; lo = 0x80; hi = 0xBF;
    } else if (c == 0xED) {
      need = 2; lo = 0x80; hi = 0x9F;
    } else if (c == 0xF0) {
      need = 3; lo = 0x90; hi = 0xBF;
    } else if (c >= 0xF1 && c <= 0xF3) {
      need = 3; lo = 0x80; hi = 0xBF;
    } else if (c == 0xF4) {
      need = 3; lo = 0x80; hi = 0x8F;
    } else {
      return 0;
    }
  }
  return 1;
}

static void row(const char *source, const char *label, uint64_t len,
                const uint8_t *bytes, uint64_t arm) {
  uint64_t blocks = blocks_of(len);

  memset(doc_buffer, 0, DOC_CAP + DOC_OFFSET);
  if (len > 0) memcpy(doc_buffer + DOC_OFFSET, bytes, (size_t)len);

  if (ascii_expected) {
    printf("%s\t%s\t%d\n", source, label, all_ascii(bytes, len));
    return;
  }
  if (utf8_expected) {
    printf("%s\t%s\t%d\n", source, label,
           !utf8_prefix_window(bytes, len));
    return;
  }

  memset(ent_array, 0xA5, (size_t)(8 * blocks));
  memset(xp_stream, 0xA5, sizeof xp_stream);
  nxp_word = 0;
  carry_words[0] = 0;
  carry_words[1] = 0;

  uint64_t ret = leanllvm_json_s1_blocks(doc_buffer + DOC_OFFSET, len, ent_array,
                                         (uint32_t *)(void *)xp_stream,
                                         &nxp_word, carry_words, arm);

  int touched = xp_still_sentinel();

  printf("%s\t%s\t%llu\t%llu\t%d", source, label,
         (unsigned long long)arm, (unsigned long long)blocks, touched);
  for (uint64_t i = 0; i < blocks; i++) {
    printf("\t0x%016llx", (unsigned long long)ent_array[i]);
  }
  printf("\t0x%016llx\t", (unsigned long long)nxp_word);
  for (int i = 0; i < XP_OBS; i++) printf("%02x", xp_stream[i]);
  printf("\t0x%016llx\t0x%016llx\t0x%016llx\n",
         (unsigned long long)carry_words[0],
         (unsigned long long)carry_words[1],
         (unsigned long long)ret);
}

static int emit_document(const char *source, const char *label,
                         const uint8_t *bytes, uint64_t len) {
  if (ascii_expected || utf8_expected) {
    row(source, label, len, bytes, 0);
    return 0;
  }
  row(source, label, len, bytes, 0);
  row(source, label, len, bytes, 2);
  row(source, label, len, bytes, 4);
  row(source, label, len, bytes, 6);
  return 0;
}

static int emit_mixed(void) {
  return emit_document("mixed", "len64", mixed_block, BLOCK_LEN);
}

static int emit_corpus(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "s1_blocks_driver: cannot read '%s'\n", path);
    return 2;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fprintf(stderr, "s1_blocks_driver: cannot seek '%s'\n", path);
    fclose(f);
    return 2;
  }
  long size = ftell(f);
  if (size < 0 || (uint64_t)size > DOC_CAP || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "s1_blocks_driver: '%s' is too large or unseekable\n", path);
    fclose(f);
    return 2;
  }
  uint8_t *bytes = malloc(size > 0 ? (size_t)size : 1);
  if (bytes == NULL) {
    fprintf(stderr, "s1_blocks_driver: out of memory reading '%s'\n", path);
    fclose(f);
    return 2;
  }
  if (size > 0 && fread(bytes, 1, (size_t)size, f) != (size_t)size) {
    fprintf(stderr, "s1_blocks_driver: short read on '%s'\n", path);
    free(bytes);
    fclose(f);
    return 2;
  }
  fclose(f);

  char label[32];
  snprintf(label, sizeof label, "len%ld", size);
  int status = emit_document(path, label, bytes, (uint64_t)size);
  free(bytes);
  return status;
}

static int name_cmp(const void *a, const void *b) {
  return strcmp(*(const char *const *)a, *(const char *const *)b);
}

/* The regular files a path names: the file itself, or the files directly in a
 * directory, in name order.  Both arms must see one document per file. */
static int emit_path(const char *path) {
  struct stat st;
  if (stat(path, &st) != 0) {
    fprintf(stderr, "s1_blocks_driver: cannot stat '%s'\n", path);
    return 2;
  }
  if (!S_ISDIR(st.st_mode)) return emit_corpus(path);

  DIR *d = opendir(path);
  if (!d) {
    fprintf(stderr, "s1_blocks_driver: cannot read directory '%s'\n", path);
    return 2;
  }
  char *names[4096];
  size_t count = 0;
  struct dirent *e;
  while ((e = readdir(d)) != NULL) {
    if (strcmp(e->d_name, ".") == 0 || strcmp(e->d_name, "..") == 0) continue;
    if (count >= 4096) {
      fprintf(stderr, "s1_blocks_driver: too many entries in '%s'\n", path);
      closedir(d);
      return 2;
    }
    names[count] = strdup(e->d_name);
    if (!names[count]) {
      closedir(d);
      return 2;
    }
    count++;
  }
  closedir(d);

  qsort(names, count, sizeof names[0], name_cmp);

  int status = 0;
  for (size_t i = 0; i < count && status == 0; i++) {
    size_t n = strlen(path) + strlen(names[i]) + 2;
    char *child = malloc(n);
    if (!child) {
      status = 2;
      break;
    }
    snprintf(child, n, "%s/%s", path, names[i]);
    struct stat cs;
    if (stat(child, &cs) != 0) {
      fprintf(stderr, "s1_blocks_driver: cannot stat '%s'\n", child);
      status = 2;
    } else if (!S_ISDIR(cs.st_mode)) {
      status = emit_corpus(child);
    }
    free(child);
  }
  for (size_t i = 0; i < count; i++) free(names[i]);
  return status;
}

static void emit_byte_arm(void) {
  uint8_t block[BLOCK_LEN];
  char label[64];
  for (int pos = 0; pos < BLOCK_LEN; pos++) {
    for (int v = 0; v < 256; v++) {
      memset(block, 0x78, sizeof block);
      block[pos] = (uint8_t)v;
      snprintf(label, sizeof label, "pos%d/val%02x/len64", pos, v);
      emit_document("arm:byte", label, block, BLOCK_LEN);
    }
  }
}

static void emit_short_arm(void) {
  uint8_t stream[128];
  char label[32];
  splitmix_bytes(SHORT_SEED, 16, stream);
  for (int n = 1; n <= SHORT_COUNT; n++) {
    snprintf(label, sizeof label, "len%d", n);
    emit_document("arm:short", label, stream, (uint64_t)n);
  }
}

static void emit_alphabet_arm(void) {
  uint8_t seq[4];
  char label[64];
  for (int i = 0; i < ALPHABET_COUNT; i++) {
    seq[0] = alphabet[i % 8];
    seq[1] = alphabet[(i / 8) % 8];
    seq[2] = alphabet[(i / 64) % 8];
    seq[3] = alphabet[(i / 512) % 8];
    snprintf(label, sizeof label, "%02x%02x%02x%02x/len4",
             seq[0], seq[1], seq[2], seq[3]);
    emit_document("arm:alphabet", label, seq, 4);
  }
}

static void emit_random_arm(void) {
  uint8_t bytes[2 * BLOCK_LEN];
  char label[64];
  for (int i = 0; i < RANDOM_COUNT; i++) {
    uint64_t len = 1 + (37ULL * (uint64_t)i) % 128;
    uint64_t blocks = blocks_of(len);
    splitmix_bytes(RANDOM_SEED + (uint64_t)i * GAMMA, (size_t)(8 * blocks), bytes);
    snprintf(label, sizeof label, "idx%d/len%llu", i, (unsigned long long)len);
    emit_document("arm:random", label, bytes, len);
  }
}

static int emit_block(void) {
  if (fwrite(mixed_block, 1, BLOCK_LEN, stdout) != BLOCK_LEN) {
    fprintf(stderr, "s1_blocks_driver: cannot write the block\n");
    return 2;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr,
            "usage: s1_blocks_driver --emit-block\n"
            "       s1_blocks_driver [--corpus <path> ...] [--arms]\n"
            "       s1_blocks_driver [--corpus <path> ...] [--arms] --ascii-expected\n"
            "       s1_blocks_driver [--corpus <path> ...] [--arms] --utf8-expected\n");
    return 2;
  }
  if (argc == 2 && strcmp(argv[1], "--emit-block") == 0) {
    return emit_block();
  }

  const char *corpus[64];
  int corpus_count = 0;
  int arms = 0;

  for (int i = 1; i < argc; i++) {
    if (strcmp(argv[i], "--corpus") == 0) {
      if (i + 1 >= argc) {
        fprintf(stderr, "s1_blocks_driver: missing path after --corpus\n");
        return 2;
      }
      if (corpus_count >= 64) {
        fprintf(stderr, "s1_blocks_driver: too many corpus paths\n");
        return 2;
      }
      corpus[corpus_count++] = argv[++i];
    } else if (strcmp(argv[i], "--arms") == 0) {
      arms = 1;
    } else if (strcmp(argv[i], "--ascii-expected") == 0) {
      ascii_expected = 1;
    } else if (strcmp(argv[i], "--utf8-expected") == 0) {
      utf8_expected = 1;
    } else {
      fprintf(stderr, "s1_blocks_driver: unknown argument '%s'\n", argv[i]);
      return 2;
    }
  }

  if (corpus_count == 0 && !arms) {
    fprintf(stderr, "s1_blocks_driver: one of --corpus or --arms is required\n");
    return 2;
  }

  if (emit_mixed() != 0) return 2;
  for (int i = 0; i < corpus_count; i++) {
    int status = emit_path(corpus[i]);
    if (status != 0) return status;
  }
  if (arms) {
    emit_byte_arm();
    emit_short_arm();
    emit_alphabet_arm();
    emit_random_arm();
  }
  return 0;
}
