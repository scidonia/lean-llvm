/* gen.c -- the fixed-seed synthetic corpus generator for the stage-1 unit
   measurement.

   Three document shapes, each written to a requested size:

     dense    an array of small objects: many structural bytes per block,
              the shape the classification and entry units are fastest on.
     strings  an array of long ASCII strings carrying occasional `\n`, `\"`,
              `\\` and `\u00e9` escapes: few structural bytes per block.
     utf8     an array of strings of raw multi-byte UTF-8 (two-, three- and
              four-byte sequences) mixed with ASCII: the shape the UTF-8
              validity stage's DFA is exercised by.

   The stream is a splitmix64 sequence seeded at 0x243F6A8885A308D3 -- the
   seed the unit drivers' random arms use -- so the same shape, size and seed
   produce the same bytes on every run and on every host.  Elements are emitted
   until the remaining room is shorter than the longest element, the array is
   closed with `]`, and the file is padded with newlines to exactly the
   requested size, so the byte count is the requested one rather than
   approximately it.

     gen --shape <dense|strings|utf8> --size <bytes> --out <path> [--seed <hex>]

   Exit status: 0 on success, 2 on a bad argument or an unwritable output.
   This is corpus production, not a measurement: it asserts nothing about the
   units. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define DEFAULT_SEED 0x243F6A8885A308D3ull

static uint64_t rng_state;

static uint64_t splitmix64(void) {
  uint64_t z = (rng_state += 0x9E3779B97F4A7C15ull);
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
  return z ^ (z >> 31);
}

static unsigned pick(unsigned n) { return (unsigned)(splitmix64() % n); }

typedef struct {
  FILE *f;
  uint64_t written;
  int failed;
} sink;

static void put(sink *s, const char *p, size_t n) {
  if (s->failed) return;
  if (fwrite(p, 1, n, s->f) != n) { s->failed = 1; return; }
  s->written += n;
}

static void puts_(sink *s, const char *p) { put(s, p, strlen(p)); }

static void put_u64(sink *s, uint64_t v) {
  char buf[24];
  int n = snprintf(buf, sizeof buf, "%llu", (unsigned long long)v);
  if (n > 0) put(s, buf, (size_t)n);
}

/* ---------------------------------------------------------------- dense -- */
/* `[{"id":123,"k":"ab","ok":true,"v":null},...]`; the longest element is well
   under 96 bytes. */
static void emit_dense_element(sink *s) {
  static const char *const words[] = { "ab", "cd", "ef", "gh", "ij", "kl" };
  puts_(s, "{\"id\":");
  put_u64(s, splitmix64() & 0xFFFFu);
  puts_(s, ",\"k\":\"");
  puts_(s, words[pick(6)]);
  puts_(s, "\",\"ok\":");
  puts_(s, pick(2) ? "true" : "false");
  puts_(s, ",\"v\":");
  puts_(s, pick(2) ? "null" : "12");
  puts_(s, "}");
}

/* -------------------------------------------------------------- strings -- */
static void emit_string_literal(sink *s, unsigned long len) {
  puts_(s, "\"");
  unsigned long i = 0;
  while (i < len) {
    unsigned r = pick(100);
    if (r < 3) {
      /* An escape sequence: two source bytes or six. */
      static const char *const esc[] = { "\\n", "\\\"", "\\\\", "\\u00e9" };
      puts_(s, esc[pick(4)]);
      i += 4;
    } else if (r < 6) {
      puts_(s, " ");
      i += 2;
    } else {
      char c = (char)('a' + pick(26));
      put(s, &c, 1);
      i += 1;
    }
  }
  puts_(s, "\"");
}

/* ---------------------------------------------------------------- utf8 -- */
/* Valid UTF-8 sequences, so the whole document is a valid UTF-8 byte string:
   `é` (2 bytes), `€` (3 bytes), `😀` (4 bytes). */
static const char *const seq[] = {
  "\xC3\xA9", "\xE2\x82\xAC", "\xF0\x9F\x98\x80", "alpha", "beta", " ", "42",
};
static const unsigned seq_len[] = { 2, 3, 4, 5, 4, 1, 2 };

static void emit_utf8_element(sink *s) {
  static const char *const words[] = { "word", "text", "name", "value", "id" };
  puts_(s, "\"");
  puts_(s, words[pick(5)]);
  unsigned parts = 4 + pick(12);
  for (unsigned i = 0; i < parts; i++) {
    unsigned k = pick(7);
    put(s, seq[k], seq_len[k]);
  }
  puts_(s, "\"");
}

/* ---------------------------------------------------------------- driver -- */
typedef enum { SHAPE_DENSE, SHAPE_STRINGS, SHAPE_UTF8 } shape;

int main(int argc, char **argv) {
  shape sh;
  uint64_t want = 0;
  const char *out = NULL;
  uint64_t seed = DEFAULT_SEED;
  int have_shape = 0;

  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--shape") && i + 1 < argc) {
      const char *v = argv[++i];
      if (!strcmp(v, "dense")) sh = SHAPE_DENSE;
      else if (!strcmp(v, "strings")) sh = SHAPE_STRINGS;
      else if (!strcmp(v, "utf8")) sh = SHAPE_UTF8;
      else { fprintf(stderr, "gen: unknown shape %s\n", v); return 2; }
      have_shape = 1;
    } else if (!strcmp(argv[i], "--size") && i + 1 < argc) {
      want = strtoull(argv[++i], NULL, 10);
    } else if (!strcmp(argv[i], "--out") && i + 1 < argc) {
      out = argv[++i];
    } else if (!strcmp(argv[i], "--seed") && i + 1 < argc) {
      seed = strtoull(argv[++i], NULL, 0);
    } else {
      fprintf(stderr, "gen: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (!have_shape || want == 0 || out == NULL) {
    fprintf(stderr, "usage: gen --shape <dense|strings|utf8> --size <bytes> "
                    "--out <path> [--seed <hex>]\n");
    return 2;
  }

  FILE *f = fopen(out, "wb");
  if (f == NULL) { perror(out); return 2; }

  rng_state = seed;
  sink s = { f, 0, 0 };

  /* The largest element any shape emits, so the array can always be closed
     inside the budget: dense <= 64 bytes, a strings literal <= 242 (160
     counted characters at up to six source bytes each, plus quotes), utf8 <=
     96.  A comma and the closing bracket fit beside it. */
  const uint64_t reserve = 280;
  if (want < reserve + 2) {
    fprintf(stderr, "gen: size %llu is too small\n", (unsigned long long)want);
    fclose(f);
    remove(out);
    return 2;
  }

  puts_(&s, "[");
  int first = 1;
  while (s.written + reserve + 1 < want) {
    if (!first) puts_(&s, ",");
    switch (sh) {
      case SHAPE_DENSE: emit_dense_element(&s); break;
      case SHAPE_STRINGS: {
        /* Long strings for the low-structure shape. */
        emit_string_literal(&s, 40 + pick(120));
        break;
      }
      case SHAPE_UTF8: emit_utf8_element(&s); break;
    }
    first = 0;
    if (s.failed) break;
  }
  puts_(&s, "]");
  while (s.written < want) {
    char pad = '\n';
    put(&s, &pad, 1);
    if (s.failed) break;
  }

  if (fflush(f) != 0 || fclose(f) != 0) {
    fprintf(stderr, "gen: write failed: %s\n", out);
    remove(out);
    return 2;
  }
  if (s.failed) {
    fprintf(stderr, "gen: write failed: %s\n", out);
    remove(out);
    return 2;
  }
  if (s.written != want) {
    fprintf(stderr, "gen: wrote %llu bytes, wanted %llu\n",
            (unsigned long long)s.written, (unsigned long long)want);
    remove(out);
    return 2;
  }
  return 0;
}
