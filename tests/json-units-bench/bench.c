/* bench.c -- the measurement harness for the three proved stage-1 units.

   `bench.sh` compiles this against objects built from `kernel/json/` at the
   measured compiler line, the two bench-only mask copies in `bench-ablate.c`
   and the bench-only mask unit in `bench-fastesc.c`, and runs it once per CPU
   and trial.  Each document
   is read once, staged once, and then swept from the same warm buffer: every
   repetition re-runs the unit over bytes that were just read, so no repetition
   pays a first-touch page fault or a cold-cache fill of its own.

   Rows, one per unit (or per arm of a unit), each over the whole document:

     s1_masks      leanllvm_json_s1_masks once per complete 64-byte block
     s1_fastesc    the mask unit's copy in `bench-fastesc.c`, with the
                   escape/quote derivation computed without pext, pdep or clz;
                   it runs every block beside `s1_masks` and must return the
                   same six mask words and carry state before it is timed
     s1_noesc      the mask unit's copy in `bench-ablate.c` with the escape
                   correction and escape carry removed: a cost bound for that
                   derivation, not a classifier
     s1_noesc_noparity  the same copy with the in-string parity removed too
     entry_pos8    leanllvm_json_entry_pos8 once over the document's mask
                   stream, derived the way the entry route derives its corpus:
                   lane t of block i is set iff byte 64*i + t is one of the
                   eight structural bytes.  This is the unit's own stream, not
                   the pipeline's, and is kept for the route comparison
     entry_b8      leanllvm_json_entry_b8 over the same stream
     fused_pos8    the pipeline's own block loop: masks, the scalar word S,
                   the entry word, its tail clamp, and one pos8 call per block
                   with nblk = 1 and the cursor threaded between blocks
     fused_b8      the same loop with the b8 emitter
     split_ent_pos8  the same pipeline entry mask, but composed whole-document
                   into an array first and then emitted by one pos8 call: the
                   split shape on the fused row's own stream
     split_ent_b8  the same with the b8 emitter
     utf8_gated    leanllvm_json_utf8 with `ungated = 0`
     utf8_ungated  leanllvm_json_utf8 with `ungated = 1`

   The ABI is declared here rather than included, as the route drivers declare
   it, so a changed header cannot make the harness agree with itself.

   Instrument.  Wall time is CLOCK_MONOTONIC_RAW around one whole-document pass,
   reported in ns per document byte and as GB/s (one byte per ns is one GB/s).
   Cycles per byte are ns per byte times the core clock measured immediately
   before the row by a serial dependent-add chain (`add; dec; jne`, one
   iteration per cycle on this part), because the host's perf events are not
   available to an unprivileged process.  The chain measures the core's clock at
   the moment of the row, not during it; a frequency change inside the row
   (AVX2 licence downclocking, turbo decay) is therefore not in the divisor and
   is a stated limit of the instrument.  The invariant TSC frequency is
   measured too and printed, so a reader can convert a wall time to reference
   cycles independently of the calibration.

   Staging.  Every document and derived array is 64-byte aligned, and the UTF-8
   row's document starts 64-byte aligned with the three zero bytes its ABI
   requires immediately before it.  The units' loads are unaligned and take any
   address, so alignment is the caller's choice; one choice is made and
   recorded, rather than letting malloc placement differ between documents.

   Variance is reported per row: the median, the 10th and 90th percentile and
   the extremes of the per-repetition ns/byte, plus the relative spread
   `(p90 - p10) / median`.  The script repeats the whole binary as trials, so
   process-to-process variance is a second, visible layer.

   Gates held fixed across every row, because a row that did not reach the code
   is not a measurement: entry_pos8's and entry_b8's cursors must both equal the
   stream's total set lanes; the fused rows' final cursors must equal the total
   set lanes of the pipeline's entry mask composed independently here, which
   the entry unit must also return over that staged stream; the gated and
   ungated UTF-8 words must be equal; s1_fastesc must equal s1_masks in every
   mask word and in the carry state on every block of every document; and every
   timed pass's checksum must equal the warm-up pass's checksum.  A disagreement exits 3 (the instrument is not
   usable), never as a number.

     bench --doc <name>=<path> [--doc ...] [--reps <n>] [--samples]

   Exit status: 0 on success, 2 on a bad argument or unreadable document, 3 when
   a gate above fails.  `--samples` additionally prints every per-repetition
   ns/byte, for inspecting a row whose spread looks surprising. */
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(__x86_64__)
#include <cpuid.h>
#include <x86intrin.h>
#endif

/* The three ABIs, declared rather than included.  The unity build includes the
   unit sources before this file, so their headers have already defined the two
   stage-1 struct types and this file must not define them again. */
#ifndef BENCH_UNITY_STAGE1
typedef struct { uint64_t esc_open, esc_ppar, im_carry; } s1_carry;
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } s1_masks;
#endif

extern void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry,
                                   s1_masks *out);
/* Bench-only ablations of the mask unit (`bench-ablate.c`): cost bounds, not
   classifiers. */
extern void leanllvm_json_s1_masks_noesc(const uint8_t *p, s1_carry *carry,
                                         s1_masks *out);
extern void leanllvm_json_s1_masks_noesc_noparity(const uint8_t *p,
                                                  s1_carry *carry,
                                                  s1_masks *out);
/* The bench-only mask unit whose escape/quote derivation uses no gather,
   scatter or count-leading-zeros instruction (`bench-fastesc.c`). */
extern void leanllvm_json_s1_fastesc(const uint8_t *p, s1_carry *carry,
                                     s1_masks *out);
extern uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                         uint64_t nblk, uint32_t *out,
                                         uint64_t k);
extern uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                       uint64_t nblk, uint32_t *out,
                                       uint64_t k);
extern void leanllvm_json_entry_table(uint32_t *dst);
extern uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated);

#define MAX_DOCS 64
#define BLOCK 64

/* ------------------------------------------------------------------ time -- */
static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
    perror("clock_gettime");
    exit(2);
  }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static uint64_t rdtsc_now(void) {
#if defined(__x86_64__)
  return __rdtsc();
#else
  return now_ns();
#endif
}

/* The core clock, in cycles per nanosecond, by a serial dependent-add chain.
   One `add` per iteration is the loop-carried dependency and its latency is one
   cycle on this part, so `iterations / nanoseconds` is the core's GHz. */
static volatile uint64_t cal_sink;

static void serial_chain(uint64_t n) {
  uint64_t x = cal_sink;
#if defined(__x86_64__)
  __asm__ __volatile__("1:\n\t"
                       "addq $1, %0\n\t"
                       "decq %1\n\t"
                       "jne 1b\n\t"
                       : "+r"(x), "+r"(n)
                       :
                       : "cc");
#else
  while (n--) x += 1;
#endif
  cal_sink = x;
}

static double calibrate_ghz(void) {
  const uint64_t iterations = 1ull << 25;
  serial_chain(1ull << 20); /* warm the loop and the clock */
  uint64_t t0 = now_ns();
  serial_chain(iterations);
  uint64_t t1 = now_ns();
  uint64_t ns = t1 - t0;
  return ns ? (double)iterations / (double)ns : 0.0;
}

static double tsc_ghz(void) {
  uint64_t t0 = now_ns();
  uint64_t c0 = rdtsc_now();
  while (now_ns() - t0 < 15000000ull) {}
  uint64_t t1 = now_ns();
  uint64_t c1 = rdtsc_now();
  uint64_t ns = t1 - t0;
  return ns ? (double)(c1 - c0) / (double)ns : 0.0;
}

/* ------------------------------------------------------------------ docs -- */
typedef struct {
  char name[64];
  const char *path;
  uint8_t *buf;      /* document bytes, zero-padded to a block boundary */
  uint64_t n;        /* document length */
  uint64_t nb;       /* complete 64-byte blocks (n / 64) */
  uint8_t *u8;       /* allocation: prefix, document, zero padding */
  uint8_t *b;        /* the document's first byte inside u8, 64-aligned */
  uint64_t u8_blocks;
  uint64_t *ent;     /* nb mask words, structural bytes only (entry rows) */
  uint64_t *pent;    /* nblk words, the pipeline's own per-block entry mask */
  uint32_t *pos;     /* nb * 64 + 16 words of output slack */
  uint64_t structural;   /* total set lanes of ent */
  uint64_t pipeline_ent; /* total set lanes of pent, the gate's reference */
  uint64_t ascii_vectors;
  uint64_t vectors;
  uint64_t utf8_gated, utf8_ungated;
} doc;

static doc docs[MAX_DOCS];
static int ndocs;

static void die(int code, const char *what) {
  fprintf(stderr, "bench: %s\n", what);
  exit(code);
}

static void *xmalloc(size_t n) {
  void *p = malloc(n ? n : 1);
  if (p == NULL) die(2, "out of memory");
  return p;
}

/* Documents and their derived arrays are staged 64-byte aligned: the units'
   loads are unaligned and take any address, so alignment is the caller's
   choice, and aligning it keeps one document's malloc placement out of the
   comparison with another's. */
static void *xaligned(size_t n) {
  void *p = NULL;
  if (posix_memalign(&p, BLOCK, n ? n : BLOCK) != 0)
    die(2, "out of memory");
  return p;
}

static uint8_t *read_file(const char *path, uint64_t *n_out) {
  FILE *f = fopen(path, "rb");
  if (f == NULL) {
    fprintf(stderr, "bench: %s: %s\n", path, strerror(errno));
    exit(2);
  }
  if (fseek(f, 0, SEEK_END) != 0) die(2, "fseek failed");
  long end = ftell(f);
  if (end < 0) die(2, "ftell failed");
  rewind(f);
  uint64_t n = (uint64_t)end;
  uint8_t *buf = xaligned((size_t)n + 2 * BLOCK);
  if (n && fread(buf, 1, n, f) != n) die(2, "short read");
  if (fclose(f) != 0) die(2, "close failed");
  memset(buf + n, 0, 2 * BLOCK);
  *n_out = n;
  return buf;
}

static int is_structural(uint8_t b) {
  switch (b) {
    case '"': case '\\': case ':': case ',': case '{':
    case '}': case '[': case ']':
      return 1;
    default:
      return 0;
  }
}

static void stage_doc(doc *d) {
  d->nb = d->n / BLOCK;

  /* The mask stream, derived from the document's block bytes exactly as
     tests/json-entry/corpus derives its streams: lane t of block i is set iff
     byte 64*i + t is structural. */
  d->ent = xaligned((size_t)(d->nb ? d->nb : 1) * sizeof *d->ent);
  d->structural = 0;
  for (uint64_t i = 0; i < d->nb; i++) {
    uint64_t m = 0;
    for (unsigned t = 0; t < BLOCK; t++)
      if (is_structural(d->buf[i * BLOCK + t])) m |= 1ull << t;
    d->ent[i] = m;
    d->structural += (uint64_t)__builtin_popcountll(m);
  }

  /* The pipeline's own per-block entry mask, composed the way `pipeline.c`
     composes it.  The fused row builds it one word at a time on the stack; the
     split-on-the-same-stream rows and the gate stage it here. */
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  d->pent = xaligned((size_t)(nblk ? nblk : 1) * sizeof *d->pent);

  /* The entry unit's output buffer: the ABI asks for eight words of slack past
     the largest count the stream can reach. */
  d->pos = xaligned(((size_t)d->nb * BLOCK + 16) * sizeof *d->pos);

  /* The UTF-8 unit's staging: three zero bytes before the document and zero
     padding to the next block boundary, both of which its ABI requires.  The
     document's first byte is itself 64-byte aligned, so the staging choice is
     one alignment and not whatever malloc returned. */
  d->u8_blocks = (d->n + BLOCK - 1) / BLOCK;
  size_t u8_len = (size_t)d->u8_blocks * BLOCK;
  d->u8 = xaligned(u8_len + 2 * BLOCK);
  memset(d->u8, 0, u8_len + 2 * BLOCK);
  d->b = d->u8 + BLOCK;
  memcpy(d->b, d->buf, (size_t)d->n);

  /* The UTF-8 gate's own census: all-ASCII 32-byte vectors. */
  d->vectors = d->u8_blocks * 2;
  d->ascii_vectors = 0;
  for (uint64_t v = 0; v < d->vectors; v++) {
    int ascii = 1;
    for (unsigned i = 0; i < 32; i++)
      if (d->b[v * 32 + i] & 0x80) { ascii = 0; break; }
    if (ascii) d->ascii_vectors++;
  }
}

/* ---------------------------------------------------------------- passes -- */
/* Each pass returns a checksum of what the unit produced, so a timed pass that
   silently did less work than its warm-up is caught instead of timed.  The s1
   row's reference pass mixes every word; its timed pass touches one word per
   block so the accumulator is not what the row measures. */

static uint64_t mix(uint64_t h, uint64_t v) {
  return (h ^ v) * 0x100000001B3ull;
}

typedef void (*s1_kernel)(const uint8_t *, s1_carry *, s1_masks *);

/* The four mask rows reach their kernels through this table, loaded through a
   volatile pointer at the start of each pass.  The indirect call is one call
   per block in every build: at unity the plain `leanllvm_json_s1_masks` would
   inline into `pass_s1` and have its unread outputs deleted, which would make
   the baseline a shorter function than the ablations and the candidate it is
   compared with. */
static s1_kernel volatile s1_kernels[4];

static uint64_t pass_s1(const doc *d, int which, int full) {
  s1_kernel fn = s1_kernels[which];
  s1_carry carry = { 0, 0, 0 };
  s1_masks out;
  uint64_t h = 0x84222325CBF29CE4ull;
  for (uint64_t i = 0; i < d->nb; i++) {
    fn(d->buf + i * BLOCK, &carry, &out);
    if (full) {
      /* The reference pass mixes every word, once per block. */
      h = mix(h, out.quote);
      h = mix(h, out.delim);
      h = mix(h, out.in_string);
      h = mix(h, out.ws);
      h = mix(h, out.backslash);
      h = mix(h, out.ctl);
      h = mix(h, carry.esc_open);
      h = mix(h, carry.esc_ppar);
      h = mix(h, carry.im_carry);
    } else {
      /* Inside the timed loop only this one dependent step is charged to the
         row: the quote mask already carries the escape and in-string state, so
         a unit that skipped a block or diverged would change it.  Every other
         word is checked by the reference pass. */
      h ^= out.quote;
    }
  }
  return h;
}

/* The candidate's byte-identity gate: every one of the six mask words and the
   carry state must equal the kernel's on every block of the document.  A
   mismatch fails the run instead of producing a timing row. */
static void gate_fastesc(const doc *d) {
  s1_carry kc = { 0, 0, 0 }, fc = { 0, 0, 0 };
  s1_masks km, fm;
  for (uint64_t i = 0; i < d->nb; i++) {
    leanllvm_json_s1_masks(d->buf + i * BLOCK, &kc, &km);
    leanllvm_json_s1_fastesc(d->buf + i * BLOCK, &fc, &fm);
    const char *field = NULL;
    uint64_t k = 0, f = 0;
    if (km.quote != fm.quote) {
      field = "quote"; k = km.quote; f = fm.quote;
    } else if (km.delim != fm.delim) {
      field = "delim"; k = km.delim; f = fm.delim;
    } else if (km.in_string != fm.in_string) {
      field = "in_string"; k = km.in_string; f = fm.in_string;
    } else if (km.ws != fm.ws) {
      field = "ws"; k = km.ws; f = fm.ws;
    } else if (km.backslash != fm.backslash) {
      field = "backslash"; k = km.backslash; f = fm.backslash;
    } else if (km.ctl != fm.ctl) {
      field = "ctl"; k = km.ctl; f = fm.ctl;
    } else if (kc.esc_open != fc.esc_open) {
      field = "esc_open"; k = kc.esc_open; f = fc.esc_open;
    } else if (kc.esc_ppar != fc.esc_ppar) {
      field = "esc_ppar"; k = kc.esc_ppar; f = fc.esc_ppar;
    } else if (kc.im_carry != fc.im_carry) {
      field = "im_carry"; k = kc.im_carry; f = fc.im_carry;
    }
    if (field != NULL) {
      fprintf(stderr,
              "bench: %s: s1_fastesc %s %016" PRIx64
              ", s1_masks %016" PRIx64 " at block %" PRIu64
              " (byte %" PRIu64 ")\n",
              d->name, field, f, k, i, i * BLOCK);
      exit(3);
    }
  }
}

/* The ablated-mask rows.  `which` selects the copied kernel.  The reference
   pass mixes all six output words, so the printed checksum is a function of
   every mask the ablation still writes.  The timed pass touches one word per
   block, exactly as `pass_s1` does: the kernel is reached through the shared
   volatile pointer table, so no build can inline it and drop an output the
   caller does not read, and a six-word timed fold would cost more than the
   derivation it is meant to isolate. */
static uint64_t pass_ablate(const doc *d, int which, int full) {
  s1_kernel fn = s1_kernels[1 + which];
  s1_carry carry = { 0, 0, 0 };
  s1_masks out;
  uint64_t h = 0x84222325CBF29CE4ull;
  for (uint64_t i = 0; i < d->nb; i++) {
    fn(d->buf + i * BLOCK, &carry, &out);
    if (full) {
      h = mix(h, out.quote);
      h = mix(h, out.delim);
      h = mix(h, out.in_string);
      h = mix(h, out.ws);
      h = mix(h, out.backslash);
      h = mix(h, out.ctl);
    } else {
      h ^= out.quote;
    }
  }
  return h;
}

static uint64_t pass_entry(const doc *d, int pos8, uint64_t *k_out) {
  uint64_t k = pos8
    ? leanllvm_json_entry_pos8(d->ent, 0, d->nb, d->pos, 0)
    : leanllvm_json_entry_b8(d->ent, 0, d->nb, d->pos, 0);
  *k_out = k;
  uint64_t h = mix(0x84222325CBF29CE4ull, k);
  if (k > 0) {
    h = mix(h, d->pos[0]);
    h = mix(h, d->pos[k - 1]);
  }
  return h;
}

/* The pipeline's own per-block loop (`kernel/json/pipeline.c`): the mask unit
   over the block, the scalar word and its run starts, the entry word's
   composition, the tail clamp, and one emitter call with nblk = 1, with the
   cursor threaded from block to block.  The reference pass mixes every mask
   word and the final cursor; the timed pass touches one mask word per block and
   the cursor once, so the accumulator is not what the row measures.

   The document is swept to its last partial block, as the pipeline sweeps
   `(n + 63) >> 6`, and the clamp keeps lanes past the end out of the entry
   word.  `buf` is zero-padded by two blocks, so the last block is readable. */
static uint64_t pass_fused(const doc *d, int b8, int full, uint64_t *k_out) {
  s1_carry carry = { 0, 0, 0 };
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t k = 0;
  uint64_t entw[1];
  uint64_t h = 0x84222325CBF29CE4ull;
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  for (uint64_t i = 0; i < nblk; i++) {
    leanllvm_json_s1_masks(d->buf + (i << 6), &carry, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    entw[0] = ent;
    k = b8 ? leanllvm_json_entry_b8(entw, i, 1, d->pos, k)
           : leanllvm_json_entry_pos8(entw, i, 1, d->pos, k);
    if (full) {
      h = mix(h, m.quote);
      h = mix(h, m.delim);
      h = mix(h, m.in_string);
      h = mix(h, m.ws);
      h = mix(h, m.backslash);
      h = mix(h, m.ctl);
    } else {
      h ^= m.quote;
    }
  }
  *k_out = k;
  return mix(h, k);
}

/* The reference for the fused rows' gate: the pipeline's entry mask composed
   here, block by block, from the mask unit's own output, with this file's
   `S`/`prevS` and tail clamp rather than the fused pass's.  It stages the
   stream in `d->pent` and returns its total set lanes, which the fused rows'
   final cursor must reach.  It is not timed. */
static uint64_t derive_pipeline_ent(const doc *d) {
  s1_carry carry = { 0, 0, 0 };
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t total = 0;
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  for (uint64_t i = 0; i < nblk; i++) {
    leanllvm_json_s1_masks(d->buf + (i << 6), &carry, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    d->pent[i] = ent;
    total += (uint64_t)__builtin_popcountll(ent);
  }
  return total;
}

/* The split shape on the stream the fused rows use: one whole-document pass
   that runs the masks and composes the pipeline's entry mask into `d->pent`,
   then one entry call over that array.  Only the presence or absence of the
   per-block fusion differs from `pass_fused`.  The reference pass mixes every
   mask word and every `ent` word; the timed pass touches one mask word per
   block, so the accumulator is not what the row measures. */
static uint64_t pass_split_ent(const doc *d, int b8, int full,
                               uint64_t *k_out) {
  s1_carry carry = { 0, 0, 0 };
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t h = 0x84222325CBF29CE4ull;
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  for (uint64_t i = 0; i < nblk; i++) {
    leanllvm_json_s1_masks(d->buf + (i << 6), &carry, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    d->pent[i] = ent;
    if (full) {
      h = mix(h, m.quote);
      h = mix(h, m.delim);
      h = mix(h, m.in_string);
      h = mix(h, m.ws);
      h = mix(h, m.backslash);
      h = mix(h, m.ctl);
      h = mix(h, ent);
    } else {
      h ^= m.quote;
    }
  }
  uint64_t k = b8 ? leanllvm_json_entry_b8(d->pent, 0, nblk, d->pos, 0)
                  : leanllvm_json_entry_pos8(d->pent, 0, nblk, d->pos, 0);
  *k_out = k;
  return mix(h, k);
}

static uint64_t pass_utf8(const doc *d, int ungated) {
  /* The unit returns one word for the whole document, so the checksum carries
     the document's length and structural census beside the verdict: dense and
     strings documents share a zero verdict, and a row's checksum must still say
     which document it measured. */
  uint64_t h = mix(0x84222325CBF29CE4ull, d->n);
  h = mix(h, d->structural);
  return mix(h, leanllvm_json_utf8(d->b, d->n, ungated));
}

/* ------------------------------------------------------------------ rows -- */
static int cmp_u64(const void *a, const void *b) {
  uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

typedef struct {
  uint64_t min, p10, median, p90, max;
} summary;

static summary summarise(uint64_t *s, int reps) {
  summary out;
  qsort(s, (size_t)reps, sizeof *s, cmp_u64);
  out.min = s[0];
  out.max = s[reps - 1];
  out.p10 = s[(int)((double)(reps - 1) * 0.10)];
  out.median = s[(reps - 1) / 2];
  out.p90 = s[(int)((double)(reps - 1) * 0.90)];
  return out;
}

typedef uint64_t (*pass_fn)(void *ctx);

typedef struct {
  doc *d;
  const char *unit;
  pass_fn fn;
  uint64_t bytes;   /* document bytes the row is charged with */
  uint64_t touch;   /* bytes the unit reads */
} row;

/* The s1 row's context: which mask kernel, and whether this call is the
   reference pass. */
typedef struct {
  const doc *d;
  int which;
  int full;
} s1_ctx;

static uint64_t row_s1(void *ctx) {
  const s1_ctx *c = ctx;
  return pass_s1(c->d, c->which, c->full);
}

/* The ablated row's context: which copy, and whether this call is the
   reference pass. */
typedef struct {
  const doc *d;
  int which;
  int full;
} ablate_ctx;

static uint64_t row_ablate(void *ctx) {
  const ablate_ctx *c = ctx;
  return pass_ablate(c->d, c->which, c->full);
}

static uint64_t row_pos8(void *ctx) {
  uint64_t k;
  return pass_entry((const doc *)ctx, 1, &k);
}

static uint64_t row_b8(void *ctx) {
  uint64_t k;
  return pass_entry((const doc *)ctx, 0, &k);
}

/* The fused row's context: the emitter arm, and whether this call is the
   reference pass. */
typedef struct {
  const doc *d;
  int b8;
  int full;
} fused_ctx;

static uint64_t row_fused(void *ctx) {
  const fused_ctx *c = ctx;
  uint64_t k;
  return pass_fused(c->d, c->b8, c->full, &k);
}

static uint64_t row_split_ent(void *ctx) {
  const fused_ctx *c = ctx;
  uint64_t k;
  return pass_split_ent(c->d, c->b8, c->full, &k);
}

static uint64_t row_utf8_gated(void *ctx) {
  return pass_utf8((const doc *)ctx, 0);
}

static uint64_t row_utf8_ungated(void *ctx) {
  return pass_utf8((const doc *)ctx, 1);
}

/* `ctx_full` produces the reference checksum printed with the row; `ctx_cheap`
   is the context the timed loop and its warm-up both use, so the equality
   gate compares equal work rather than two different accumulators. */
static void run_row(const row *r, void *ctx_full, void *ctx_cheap, int reps,
                    int samples, int cpu) {
  uint64_t reference = r->fn(ctx_full);
  uint64_t cheap_reference = r->fn(ctx_cheap);
  uint64_t *s = xmalloc((size_t)reps * sizeof *s);
  double g1 = calibrate_ghz();
  double g2 = calibrate_ghz();
  double ghz = 0.5 * (g1 + g2);

  for (int i = 0; i < reps; i++) {
    uint64_t t0 = now_ns();
    uint64_t h = r->fn(ctx_cheap);
    uint64_t t1 = now_ns();
    if (h != cheap_reference) {
      fprintf(stderr,
              "bench: %s/%s: a timed pass produced checksum %016" PRIx64
              ", the warm-up pass %016" PRIx64 "\n",
              r->d->name, r->unit, h, cheap_reference);
      exit(3);
    }
    s[i] = t1 - t0;
  }
  summary m = summarise(s, reps);

  double median_ns_per_byte = (double)m.median / (double)r->bytes;
  double gbps = (double)r->bytes / (double)m.median;
  double cycles_per_byte = median_ns_per_byte * ghz;

  printf("row cpu=%d doc=%s unit=%s bytes=%" PRIu64 " touch=%" PRIu64
         " blocks=%" PRIu64 " reps=%d"
         " min_ns=%" PRIu64 " p10_ns=%" PRIu64 " median_ns=%" PRIu64
         " p90_ns=%" PRIu64 " max_ns=%" PRIu64
         " ns_per_byte=%.5f gbps=%.3f cycles_per_byte=%.4f"
         " core_ghz=%.3f calib_spread_pct=%.2f checksum=0x%016" PRIx64 "\n",
         cpu, r->d->name, r->unit, r->bytes, r->touch, r->d->nb, reps,
         m.min, m.p10, m.median, m.p90, m.max,
         median_ns_per_byte, gbps, cycles_per_byte,
         ghz, g1 > g2 ? 100.0 * (g1 - g2) / ghz : 100.0 * (g2 - g1) / ghz,
         reference);

  if (samples) {
    for (int i = 0; i < reps; i++)
      printf("sample cpu=%d doc=%s unit=%s rep=%d ns=%" PRIu64
             " gbps=%.3f\n",
             cpu, r->d->name, r->unit, i, s[i],
             (double)r->bytes / (double)s[i]);
  }
  free(s);
}

/* ------------------------------------------------------------------ main -- */
static unsigned cpuid_core_class(void) {
#if defined(__x86_64__)
  unsigned a = 0, b = 0, c = 0, d = 0;
  if (__get_cpuid(0x1A, &a, &b, &c, &d)) return (a >> 24) & 0xFFu;
#endif
  return 0;
}

static void add_doc(const char *spec) {
  if (ndocs >= MAX_DOCS) die(2, "too many documents");
  const char *eq = strchr(spec, '=');
  if (eq == NULL || eq == spec || eq[1] == '\0')
    die(2, "--doc wants <name>=<path>");
  doc *d = &docs[ndocs];
  memset(d, 0, sizeof *d);
  size_t name_len = (size_t)(eq - spec);
  if (name_len >= sizeof d->name) die(2, "document name too long");
  memcpy(d->name, spec, name_len);
  d->name[name_len] = '\0';
  d->path = eq + 1;
  ndocs++;
}

int main(int argc, char **argv) {
  int reps = 51;
  int samples = 0;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "--doc") && i + 1 < argc) {
      add_doc(argv[++i]);
    } else if (!strcmp(argv[i], "--reps") && i + 1 < argc) {
      reps = atoi(argv[++i]);
      if (reps < 5 || reps > 100000) die(2, "reps out of range");
    } else if (!strcmp(argv[i], "--samples")) {
      samples = 1;
    } else {
      fprintf(stderr, "bench: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (ndocs == 0) die(2, "no --doc given");

  /* POS8 reads the unit's own static table; only the unit's initialiser fills
     it, and nothing else calls that initialiser. */
  static uint32_t table[256 * 8];
  leanllvm_json_entry_table(table);

  /* One table entry per mask row, read back through a volatile pointer by each
     pass so the call stays indirect in every build. */
  s1_kernels[0] = leanllvm_json_s1_masks;
  s1_kernels[1] = leanllvm_json_s1_masks_noesc;
  s1_kernels[2] = leanllvm_json_s1_masks_noesc_noparity;
  s1_kernels[3] = leanllvm_json_s1_fastesc;

  int cpu = -1;
#if defined(__linux__)
  cpu = sched_getcpu();
#endif

  printf("instrument bench=1 reps=%d tsc_ghz=%.3f cpuid_1a=%02x cpu=%d\n",
         reps, tsc_ghz(), cpuid_core_class(), cpu);

  for (int i = 0; i < ndocs; i++) {
    doc *d = &docs[i];
    d->buf = read_file(d->path, &d->n);
    stage_doc(d);

    /* The candidate's byte-identity gate, before any timing: every mask word
       and the carry state must match the kernel's on every block. */
    gate_fastesc(d);

    /* The row gates, taken once per document before any timing. */
    uint64_t k8, kb;
    pass_entry(d, 1, &k8);
    pass_entry(d, 0, &kb);
    if (k8 != d->structural || kb != d->structural) {
      fprintf(stderr,
              "bench: %s: entry cursors pos8=%" PRIu64 " b8=%" PRIu64
              ", stream has %" PRIu64 " set lanes\n",
              d->name, k8, kb, d->structural);
      exit(3);
    }
    /* The fused rows' gate.  `derive_pipeline_ent` composes the pipeline's
       entry mask in this file's own loop and stages it; the entry unit over
       that stream must return its total, and the fused loop's final cursor must
       equal the same total.  A fused row that skipped a block, dropped the
       carry or clamped the last block differently fails here instead of being
       timed. */
    uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
    d->pipeline_ent = derive_pipeline_ent(d);
    uint64_t e8 = leanllvm_json_entry_pos8(d->pent, 0, nblk, d->pos, 0);
    uint64_t eb = leanllvm_json_entry_b8(d->pent, 0, nblk, d->pos, 0);
    if (e8 != d->pipeline_ent || eb != d->pipeline_ent) {
      fprintf(stderr,
              "bench: %s: pipeline-stream entry cursors pos8=%" PRIu64
              " b8=%" PRIu64 ", reference stream has %" PRIu64 " set lanes\n",
              d->name, e8, eb, d->pipeline_ent);
      exit(3);
    }
    uint64_t f8, fb;
    pass_fused(d, 0, 1, &f8);
    pass_fused(d, 1, 1, &fb);
    if (f8 != e8 || fb != eb) {
      fprintf(stderr,
              "bench: %s: fused cursors pos8=%" PRIu64 " b8=%" PRIu64
              ", pipeline-stream entry cursors pos8=%" PRIu64 " b8=%" PRIu64
              "\n",
              d->name, f8, fb, e8, eb);
      exit(3);
    }
    d->utf8_gated = leanllvm_json_utf8(d->b, d->n, 0);
    d->utf8_ungated = leanllvm_json_utf8(d->b, d->n, 1);
    if (d->utf8_gated != d->utf8_ungated) {
      fprintf(stderr, "bench: %s: gated UTF-8 word %" PRIu64
                      ", ungated %" PRIu64 "\n",
              d->name, d->utf8_gated, d->utf8_ungated);
      exit(3);
    }

    printf("doc name=%s bytes=%" PRIu64 " blocks=%" PRIu64
           " structural=%" PRIu64 " structural_per_block=%.2f"
           " pipeline_ent=%" PRIu64
           " vectors=%" PRIu64 " ascii_vectors=%" PRIu64
           " utf8_word=%" PRIu64 " entry_positions=%" PRIu64 "\n",
           d->name, d->n, d->nb, d->structural,
           d->nb ? (double)d->structural / (double)d->nb : 0.0,
           d->pipeline_ent,
           d->vectors, d->ascii_vectors, d->utf8_gated, d->structural);

    s1_ctx s1_full = { d, 0, 1 };
    s1_ctx s1_cheap = { d, 0, 0 };
    s1_ctx fe_full = { d, 3, 1 };
    s1_ctx fe_cheap = { d, 3, 0 };
    row r_s1 = { d, "s1_masks", row_s1, d->nb * BLOCK, d->nb * BLOCK };
    row r_fastesc = { d, "s1_fastesc", row_s1, d->nb * BLOCK,
                      d->nb * BLOCK };
    row r_noesc = { d, "s1_noesc", row_ablate, d->nb * BLOCK,
                    d->nb * BLOCK };
    row r_nopar = { d, "s1_noesc_noparity", row_ablate, d->nb * BLOCK,
                    d->nb * BLOCK };
    row r_pos8 = { d, "entry_pos8", row_pos8, d->nb * BLOCK, d->nb * 8 };
    row r_b8 = { d, "entry_b8", row_b8, d->nb * BLOCK, d->nb * 8 };
    row r_fp8 = { d, "fused_pos8", row_fused, d->nb * BLOCK, d->nb * BLOCK };
    row r_fb8 = { d, "fused_b8", row_fused, d->nb * BLOCK, d->nb * BLOCK };
    row r_sp8 = { d, "split_ent_pos8", row_split_ent, d->nb * BLOCK,
                  d->nb * BLOCK + d->nb * 8 };
    row r_sb8 = { d, "split_ent_b8", row_split_ent, d->nb * BLOCK,
                  d->nb * BLOCK + d->nb * 8 };
    row r_utf8_g = { d, "utf8_gated", row_utf8_gated, d->n,
                     d->u8_blocks * BLOCK };
    row r_utf8_u = { d, "utf8_ungated", row_utf8_ungated, d->n,
                     d->u8_blocks * BLOCK };

    fused_ctx fp8_full = { d, 0, 1 };
    fused_ctx fp8_cheap = { d, 0, 0 };
    fused_ctx fb8_full = { d, 1, 1 };
    fused_ctx fb8_cheap = { d, 1, 0 };
    ablate_ctx ab_noesc_full = { d, 0, 1 };
    ablate_ctx ab_noesc_cheap = { d, 0, 0 };
    ablate_ctx ab_nopar_full = { d, 1, 1 };
    ablate_ctx ab_nopar_cheap = { d, 1, 0 };

    if (d->nb > 0) {
      run_row(&r_s1, &s1_full, &s1_cheap, reps, samples, cpu);
      run_row(&r_fastesc, &fe_full, &fe_cheap, reps, samples, cpu);
      run_row(&r_noesc, &ab_noesc_full, &ab_noesc_cheap, reps, samples, cpu);
      run_row(&r_nopar, &ab_nopar_full, &ab_nopar_cheap, reps, samples, cpu);
      run_row(&r_pos8, d, d, reps, samples, cpu);
      run_row(&r_b8, d, d, reps, samples, cpu);
      run_row(&r_fp8, &fp8_full, &fp8_cheap, reps, samples, cpu);
      run_row(&r_fb8, &fb8_full, &fb8_cheap, reps, samples, cpu);
      run_row(&r_sp8, &fp8_full, &fp8_cheap, reps, samples, cpu);
      run_row(&r_sb8, &fb8_full, &fb8_cheap, reps, samples, cpu);
    }
    if (d->n > 0) {
      run_row(&r_utf8_g, d, d, reps, samples, cpu);
      run_row(&r_utf8_u, d, d, reps, samples, cpu);
    }
  }
  return 0;
}
