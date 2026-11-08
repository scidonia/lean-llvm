/* entry.c -- the entry unit of the measured SIMD JSON pipeline: the `ent` word's
   two position emitters, and the table one of them reads.

   The table, its initialiser and the two kernels are the measured text of
   kernel/json/measured/xlist.h and kernel/json/measured/s1fuse.h, at the line
   ranges README.md's identity list records, with the arms the measured build did
   not take and the emitters this unit is not deleted (README.md's `entry`
   deletion list; `identity/source-identity.sh --unit entry` applies it and
   diffs).  Both kernels and both block loops keep their measured names,
   signatures, formatting and comments, so the token diff and the IR diff
   compare the measured functions rather than a re-spelling of them.

   What the measured header calls the entry emitter is a pipeline: the `ent`
   word is computed inline in three places (`s1f_ent_probe`, `s1f_build`,
   `s1f_build2`, none of which is a function over one block), a selector picks a
   kernel per document, and a dispatcher calls it per chunk.  This unit is the
   emitters and nothing else: the word is not computed here, no selector is
   here, and neither the escape list nor the inline emitter of `s1f_build` is
   here.  Both kernels are exported, because proving two emitters of one stream
   is the point and the choice between them is not this unit's to make.

   The two kernels write the same position stream -- the gate compares the
   streams byte for byte -- and differ only in how a block's entry mask becomes
   positions:

     pos8  one 32-byte store per mask byte through the byte table: eight stores
           per block whatever its mask holds, and no serial advance chain.
     b8    eight fixed tzcnt/blsr slots, then a scalar tail.

   `S1F_DEFINE_KERNEL` wraps a kernel into the block loop both share: one mask
   word per block, the base `(uint32_t)((blk0 + i) << 6)`, and the cursor `k`
   threaded through.  It is `noinline` so a caller's chunk costs one call and
   the kernel is a body of its own rather than inlined into every caller.

   The new text is the three functions at the end of this file: the two wrappers,
   which restate the block loop's parameters with `const` on `ent` and add no
   instruction, and `leanllvm_json_entry_table`, which fills a caller's 8 KiB
   from the unit's own table so a route can compare the table's content without
   a second model of it. */
#include "entry.h"

#include <immintrin.h>
#include <stdint.h>

/* ----------------------------------------------------------------- table -- */
/* POS8: for each eight-bit mask, the offsets of its set bits, in order, padded
   to eight entries.  A store of a whole row therefore writes the byte's
   positions contiguously at the cursor, and its slots past the popcount are
   overwritten by the next store (or never read). */
static uint32_t xl_pos8[256][8] __attribute__((aligned(32)));
/* Set once, so a second initialisation is a load and a branch rather than a
   refill of 8 KiB. */
static int xl_pos8_ready;

static void xl_pos8_init(void) {
    if (xl_pos8_ready) return;
    for (unsigned m = 0; m < 256; m++) {
        unsigned o = 0;
        for (unsigned t = 0; t < 8; t++)
            if ((m >> t) & 1) xl_pos8[m][o++] = t;
        while (o < 8) xl_pos8[m][o++] = 0;
    }
    xl_pos8_ready = 1;
}

/* ---------------------------------------------------------------- kernels -- */
static inline uint64_t s1f_ke_pos8(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    for (int b = 0; b < 8; b++) {
        unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
        _mm256_storeu_si256((__m256i *)o, v);
        o += (uint64_t)__builtin_popcount(x);
    }
    return (uint64_t)__builtin_popcountll(m);
}

static inline uint64_t s1f_ke_b8(uint64_t m, uint32_t base, uint32_t *o) {
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

#define S1F_DEFINE_KERNEL(NAME, BLOCK)                                        \
static __attribute__((noinline)) uint64_t                                     \
NAME(uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out, uint64_t k) {\
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        uint64_t m = ent[i];                                                  \
        if (!m) continue;                                                     \
        k += BLOCK(m, (uint32_t)((blk0 + i) << 6), out + k);                   \
    }                                                                         \
    return k;                                                                 \
}
S1F_DEFINE_KERNEL(s1f_k_pos8, s1f_ke_pos8)
S1F_DEFINE_KERNEL(s1f_k_b8, s1f_ke_b8)
#undef S1F_DEFINE_KERNEL

/* ------------------------------------------------------------------- ABI -- */
/* The block loop's parameters, hoisted.  `const` on `ent` is a qualifier and
   not an instruction: the kernel reads the mask word and never writes it, and
   the cast drops a `const` the body does not need to keep. */
uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                  uint64_t nblk, uint32_t *out, uint64_t k) {
    return s1f_k_pos8((uint64_t *)ent, blk0, nblk, out, k);
}

uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                uint64_t nblk, uint32_t *out, uint64_t k) {
    return s1f_k_b8((uint64_t *)ent, blk0, nblk, out, k);
}

void leanllvm_json_entry_table(uint32_t *dst) {
    xl_pos8_init();
    for (unsigned m = 0; m < 256; m++)
        for (unsigned t = 0; t < 8; t++) dst[m * 8 + t] = xl_pos8[m][t];
}
