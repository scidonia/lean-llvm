/*
 * Row driver for the stage-1 mask kernel's installed object.
 *
 *   s1_masks_driver --emit-block
 *   s1_masks_driver [--corpus <file> ...] [--arms]
 *
 * The object is `kernel/json/s1_block.c` compiled with the measured compiler
 * line; this driver declares the ABI rather than including `s1_block.h`, so a
 * changed header cannot make the driver agree with itself.  Every row stages a
 * 64-byte block at **offset 1** of a 96-byte buffer — a misaligned pointer —
 * fills the 48-byte output slot with `0xA5`, sets the three carry words, calls
 * `leanllvm_json_s1_masks`, and prints
 *
 *   <source>\t<label>\t<open>\t<ppar>\t<inside>\t<comma>\t<quote>\t<delim>
 *   \t<in_string>\t<ws>\t<backslash>\t<ctl>\t<esc_open>\t<esc_ppar>
 *   \t<im_carry>
 *
 * with the nine words as `0x` and sixteen lowercase hex digits, so the output
 * is comparable line for line with `leanllvm-json-s1-masks`.  The carry state
 * is `4*open + 2*ppar + inside`; `comma` is `1` when any lane of the block is
 * `0x2C`, which is the row set a table byte for the comma class can move.
 *
 * Rows: the mixed block once per state; each corpus file's 64-byte windows,
 * offset ascending, once per state; then, under `--arms`, the byte sweep (every
 * value at every lane position), every 4-byte sequence over the sixteen-symbol
 * class alphabet at lanes 0-3 of a `0x78` block, and 4096 splitmix64 blocks
 * seeded at 0x243F6A8885A308D3 — each once per state.
 *
 * This is test infrastructure: it calls the object and prints what the object
 * wrote.  It asserts nothing about the classification; the comparison against
 * the Lean body is what says the two agree.
 *
 * Exit status: 0 on success, 2 when an argument is missing or a file cannot be
 * read, so a setup fault is never read as a classification result.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { uint64_t esc_open, esc_ppar, im_carry; } s1_carry;
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } s1_masks;

extern void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry,
                                   s1_masks *out);

#define BLOCK_LEN 64
#define BUFFER_LEN 96

/* The mixed block `leanllvm-json-s1-masks --emit-block` writes; the two are
 * required to be the same 64 bytes by tests/json-s1-masks/check.sh. */
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

/* The class alphabet: every byte class the six masks distinguish, one symbol
 * per class and per position on the class boundaries — the control bytes 0x00,
 * 0x09, 0x0A, 0x0D and 0x1F, the space 0x20, the quote 0x22, the comma 0x2C,
 * the colon 0x3A, the brackets 0x5B/0x5D and braces 0x7B/0x7D, the backslash
 * 0x5C, the ordinary byte 0x61, and 0x80, the first non-ASCII byte. */
static const uint8_t alphabet[16] = { 0x00, 0x09, 0x0A, 0x0D,
                                      0x1F, 0x20, 0x22, 0x2C,
                                      0x3A, 0x5B, 0x5C, 0x5D,
                                      0x7B, 0x7D, 0x61, 0x80 };

#define ALPHABET_COUNT 65536 /* 16^4 */
#define RANDOM_COUNT 4096

static _Alignas(64) uint8_t buffer[BUFFER_LEN];

/* Whether any lane of the block is `0x2C`, the byte the comma class's table
 * entry decides. */
static int has_comma(const uint8_t *block) {
  int found = 0;
  for (int i = 0; i < BLOCK_LEN; i++) {
    if (block[i] == 0x2C) found = 1;
  }
  return found;
}

static void row(const char *source, const char *label, int state,
                const uint8_t *block) {
  s1_carry carry;
  s1_masks out;

  memcpy(buffer + 1, block, BLOCK_LEN);
  memset(&out, 0xA5, sizeof out);
  carry.esc_open = (state & 4) ? 1u : 0u;
  carry.esc_ppar = (state & 2) ? 1u : 0u;
  carry.im_carry = (state & 1) ? ~(uint64_t)0 : (uint64_t)0;

  leanllvm_json_s1_masks(buffer + 1, &carry, &out);

  printf("%s\t%s\t%d\t%d\t%d\t%d"
         "\t0x%016llx\t0x%016llx\t0x%016llx"
         "\t0x%016llx\t0x%016llx\t0x%016llx"
         "\t0x%016llx\t0x%016llx\t0x%016llx\n",
         source, label, (state >> 2) & 1, (state >> 1) & 1, state & 1,
         has_comma(block),
         (unsigned long long)out.quote, (unsigned long long)out.delim,
         (unsigned long long)out.in_string, (unsigned long long)out.ws,
         (unsigned long long)out.backslash, (unsigned long long)out.ctl,
         (unsigned long long)carry.esc_open,
         (unsigned long long)carry.esc_ppar,
         (unsigned long long)carry.im_carry);
}

static int emit_mixed(void) {
  char label[16];
  for (int state = 0; state < 8; state++) {
    snprintf(label, sizeof label, "%d", state);
    row("mixed", label, state, mixed_block);
  }
  return 0;
}

static int emit_corpus(const char *path) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "s1_masks_driver: cannot read '%s'\n", path);
    return 2;
  }
  if (fseek(f, 0, SEEK_END) != 0) {
    fprintf(stderr, "s1_masks_driver: cannot seek '%s'\n", path);
    fclose(f);
    return 2;
  }
  long size = ftell(f);
  if (size < 0 || fseek(f, 0, SEEK_SET) != 0) {
    fprintf(stderr, "s1_masks_driver: cannot measure '%s'\n", path);
    fclose(f);
    return 2;
  }
  uint8_t *bytes = malloc(size > 0 ? (size_t)size : 1);
  if (bytes == NULL) {
    fprintf(stderr, "s1_masks_driver: out of memory reading '%s'\n", path);
    fclose(f);
    return 2;
  }
  if (size > 0 && fread(bytes, 1, (size_t)size, f) != (size_t)size) {
    fprintf(stderr, "s1_masks_driver: short read on '%s'\n", path);
    free(bytes);
    fclose(f);
    return 2;
  }
  fclose(f);

  char label[32];
  for (long off = 0; off + BLOCK_LEN <= size; off++) {
    snprintf(label, sizeof label, "%ld", off);
    for (int state = 0; state < 8; state++) {
      row(path, label, state, bytes + off);
    }
  }

  free(bytes);
  return 0;
}

static void emit_byte_arm(void) {
  uint8_t block[BLOCK_LEN];
  char label[64];
  for (int state = 0; state < 8; state++) {
    for (int pos = 0; pos < BLOCK_LEN; pos++) {
      for (int v = 0; v < 256; v++) {
        memset(block, 0x78, sizeof block);
        block[pos] = (uint8_t)v;
        snprintf(label, sizeof label, "pos%d/val%02x/carry%d", pos, v, state);
        row("arm:byte", label, state, block);
      }
    }
  }
}

static void emit_alphabet_arm(void) {
  uint8_t block[BLOCK_LEN];
  char label[64];
  for (int state = 0; state < 8; state++) {
    for (int i = 0; i < ALPHABET_COUNT; i++) {
      memset(block, 0x78, sizeof block);
      block[0] = alphabet[i % 16];
      block[1] = alphabet[(i / 16) % 16];
      block[2] = alphabet[(i / 256) % 16];
      block[3] = alphabet[(i / 4096) % 16];
      snprintf(label, sizeof label, "%02x%02x%02x%02x/carry%d",
               block[0], block[1], block[2], block[3], state);
      row("arm:alphabet", label, state, block);
    }
  }
}

static uint64_t splitmix_next(uint64_t *x) {
  uint64_t z = (*x += UINT64_C(0x9E3779B97F4A7C15));
  z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
  z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
  return z ^ (z >> 31);
}

static void emit_random_arm(void) {
  uint8_t block[BLOCK_LEN];
  char label[64];
  for (int state = 0; state < 8; state++) {
    for (int i = 0; i < RANDOM_COUNT; i++) {
      uint64_t x = UINT64_C(0x243F6A8885A308D3) +
                   (uint64_t)i * UINT64_C(0x9E3779B97F4A7C15);
      for (int w = 0; w < 8; w++) {
        uint64_t word = splitmix_next(&x);
        for (int k = 0; k < 8; k++) {
          block[w * 8 + k] = (uint8_t)((word >> (8 * k)) & 0xFF);
        }
      }
      snprintf(label, sizeof label, "idx%d/carry%d", i, state);
      row("arm:random", label, state, block);
    }
  }
}

static int emit_block(void) {
  if (fwrite(mixed_block, 1, BLOCK_LEN, stdout) != BLOCK_LEN) {
    fprintf(stderr, "s1_masks_driver: cannot write the block\n");
    return 2;
  }
  return 0;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: s1_masks_driver --emit-block\n"
                    "       s1_masks_driver [--corpus <file> ...] [--arms]\n");
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
        fprintf(stderr, "s1_masks_driver: missing path after --corpus\n");
        return 2;
      }
      if (corpus_count >= 64) {
        fprintf(stderr, "s1_masks_driver: too many corpus paths\n");
        return 2;
      }
      corpus[corpus_count++] = argv[++i];
    } else if (strcmp(argv[i], "--arms") == 0) {
      arms = 1;
    } else {
      fprintf(stderr, "s1_masks_driver: unknown argument '%s'\n", argv[i]);
      return 2;
    }
  }

  if (corpus_count == 0 && !arms) {
    fprintf(stderr, "s1_masks_driver: one of --corpus or --arms is required\n");
    return 2;
  }

  if (emit_mixed() != 0) return 2;
  for (int i = 0; i < corpus_count; i++) {
    int status = emit_corpus(corpus[i]);
    if (status != 0) return status;
  }
  if (arms) {
    emit_byte_arm();
    emit_alphabet_arm();
    emit_random_arm();
  }
  return 0;
}
