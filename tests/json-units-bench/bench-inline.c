/* bench-inline.c -- the fused masks-and-entry loop with the entry kernel
   inlined rather than called.

   `kernel/json/entry.c` wraps its block loop in `S1F_DEFINE_KERNEL`, which
   declares the kernel `static __attribute__((noinline))`.  Every fused row
   therefore pays one call per block: the classifier loop composes a block's
   `ent` word and calls a kernel that iterates once and emits.  LTO cannot
   remove that call and the unity build cannot inline the body, because the
   attribute forbids both.

   This file is the honest ablation of that attribute and nothing else.  The
   table, its initialiser, the two emitters and the block-loop macro are
   `entry.c`'s text with the attribute removed and `always_inline` added, under
   this file's names; the loops at the end are the pipeline's fused loop, block
   for block: the mask unit over the block, the scalar word `S`, the entry word
   `ent`, its tail clamp, and one call to the block-loop kernel with `nblk = 1`
   and the cursor threaded between blocks, exactly as `bench.c`'s `pass_fused`
   does.  With the attribute gone that call is the same body written where it
   is called, so a difference between a row of this file and `fused_*` is
   attributable to the call and not to the arithmetic.

   The classifier (`leanllvm_json_s1_masks`) is still called out of line here:
   it is the same call the fused rows make, so the ablation moves the entry
   call and nothing else.

   This is a benchmark candidate, not a kernel: `bench.c` runs it beside the
   `fused_*` and `split_ent_*` rows and, before timing it, compares its emitted
   position stream and final cursor against `leanllvm_json_entry_pos8`/`_b8`
   over the pipeline's staged `ent` stream on every corpus document.
   `kernel/json/` is not edited. */
#include "../../kernel/json/s1_block.h"

#include <immintrin.h>
#include <stdint.h>

/* ----------------------------------------------------------------- table -- */
/* POS8's table, copied from the unit: for each eight-bit mask, the offsets of
   its set bits in order, padded to eight entries. */
static uint32_t inl_pos8_tab[256][8] __attribute__((aligned(32)));
/* Set once, so a second initialisation is a load and a branch. */
static int inl_pos8_ready;

static void inl_pos8_init(void) {
    if (inl_pos8_ready) return;
    for (unsigned m = 0; m < 256; m++) {
        unsigned o = 0;
        for (unsigned t = 0; t < 8; t++)
            if ((m >> t) & 1) inl_pos8_tab[m][o++] = t;
        while (o < 8) inl_pos8_tab[m][o++] = 0;
    }
    inl_pos8_ready = 1;
}

/* ---------------------------------------------------------------- kernels -- */
static inline __attribute__((always_inline))
uint64_t inl_ke_pos8(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    for (int b = 0; b < 8; b++) {
        unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)inl_pos8_tab[x]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
        _mm256_storeu_si256((__m256i *)o, v);
        o += (uint64_t)__builtin_popcount(x);
    }
    return (uint64_t)__builtin_popcountll(m);
}

static inline __attribute__((always_inline))
uint64_t inl_ke_b8(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    if (!n) return 0;
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 8) return n;
    o += 8;
    uint64_t k = 8;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

/* The unit's `S1F_DEFINE_KERNEL` with the `noinline` removed: the body is
   written where the fused loop calls it. */
#define INL_DEFINE_KERNEL(NAME, BLOCK)                                        \
static inline __attribute__((always_inline)) uint64_t                         \
NAME(uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out, uint64_t k) {\
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        uint64_t m = ent[i];                                                  \
        if (!m) continue;                                                     \
        k += BLOCK(m, (uint32_t)((blk0 + i) << 6), out + k);                   \
    }                                                                         \
    return k;                                                                 \
}
INL_DEFINE_KERNEL(inl_k_pos8, inl_ke_pos8)
INL_DEFINE_KERNEL(inl_k_b8, inl_ke_b8)
#undef INL_DEFINE_KERNEL

/* The table's initialiser, as its own entry point.  The pass does not call it,
   so the timed loop's only call is the classifier's; `bench.c` calls this once
   per process, beside `leanllvm_json_entry_table`. */
void leanllvm_bench_inline_table(void) {
    inl_pos8_init();
}

/* `bench.c`'s accumulator, under this file's name so the pass can be its own
   translation unit: the row's checksum is the same function of the same words
   as the `fused_*` rows'. */
static inline uint64_t inl_mix(uint64_t h, uint64_t v) {
    return (h ^ v) * 0x100000001B3ull;
}

/* ----------------------------------------------------------- fused passes -- */
/* The pipeline's fused loop with one emitter, the entry call inlined.  `buf` is
   the document with two blocks of zero padding, as the fused rows stage it, so
   the last partial block is readable; `n` is the document length. */
#define INL_FUSED_PASS(NAME, KERNEL)                                          \
uint64_t NAME(const uint8_t *buf, uint64_t n, uint32_t *pos, int full,         \
              uint64_t *k_out) {                                              \
    s1_carry carry = { 0, 0, 0 };                                             \
    s1_masks m;                                                               \
    uint64_t prevS = 0;                                                       \
    uint64_t k = 0;                                                           \
    uint64_t entw[1];                                                         \
    uint64_t h = 0x84222325CBF29CE4ull;                                       \
    uint64_t nblk = (n + 63) / 64;                                            \
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        leanllvm_json_s1_masks(buf + (i << 6), &carry, &m);                    \
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);                \
        uint64_t ent = m.quote | (m.delim & ~m.in_string);                     \
        ent |= S & ~((S << 1) | prevS);                                       \
        prevS = S >> 63;                                                      \
        uint64_t lim = n - (i << 6);                                          \
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;                            \
        entw[0] = ent;                                                        \
        k = KERNEL(entw, i, 1, pos, k);                                       \
        if (full) {                                                           \
            h = inl_mix(h, m.quote);                                          \
            h = inl_mix(h, m.delim);                                          \
            h = inl_mix(h, m.in_string);                                      \
            h = inl_mix(h, m.ws);                                             \
            h = inl_mix(h, m.backslash);                                      \
            h = inl_mix(h, m.ctl);                                            \
        } else {                                                              \
            h ^= m.quote;                                                     \
        }                                                                     \
    }                                                                         \
    *k_out = k;                                                               \
    return inl_mix(h, k);                                                     \
}
INL_FUSED_PASS(leanllvm_bench_inline_pos8, inl_k_pos8)
INL_FUSED_PASS(leanllvm_bench_inline_b8, inl_k_b8)
#undef INL_FUSED_PASS
