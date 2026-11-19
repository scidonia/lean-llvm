/* entry_variants.c -- two further entry-emitter shapes beside the installed one.

   The installed unit (`kernel/json/entry.c`) emits a block's positions with one
   32-byte store per mask byte of the word, through its own POS8 table.  This
   file holds the two shapes the entry-opt experiment measures:

     skip    the installed shape with an empty mask byte's load and store
             skipped: `if (!x) continue;` in the eight-iteration loop.  Same
             table, same 32-byte group store, fewer groups written.
     sparse  no table and no group store: one 4-byte store per set lane, walked
             with `ctz`/`blsr`.  One store per position the stream holds.

   Both keep the installed kernel's external shape -- a `noinline` block loop
   over `nblk` mask words, the base `(uint32_t)((blk0 + i) << 6)` and the cursor
   threaded through -- so a caller can substitute one for the other and the
   difference measured is the emitter rather than the call.

   The table the `skip` shape reads is filled by the installed unit's own
   `leanllvm_json_entry_table`, so both kernels read the same bytes; the harness
   checks that table against the rule it is specified by.  Nothing here is
   production text: this translation unit is built only into the entry-opt
   harness.
*/
#include <immintrin.h>
#include <stdint.h>

#include "entry.h"

/* --------------------------------------------------------------- table -- */
/* Filled from the installed unit rather than derived a second time, so a
   difference between the two kernel's streams cannot come from two tables. */
static uint32_t eo_pos8[256][8] __attribute__((aligned(32)));
static int eo_pos8_ready;

void eo_table_init(void) {
    if (eo_pos8_ready) return;
    leanllvm_json_entry_table(&eo_pos8[0][0]);
    eo_pos8_ready = 1;
}

/* 1 when the installed unit's table is the rule it is specified by: row `m`
   holds the offsets of `m`'s set bits in order, padded to eight with zeros. */
int eo_table_check(void) {
    eo_table_init();
    for (unsigned m = 0; m < 256; m++) {
        unsigned o = 0;
        for (unsigned t = 0; t < 8; t++)
            if ((m >> t) & 1) {
                if (eo_pos8[m][o] != t) return 0;
                o++;
            }
        for (; o < 8; o++)
            if (eo_pos8[m][o] != 0) return 0;
    }
    return 1;
}

/* -------------------------------------------------------------- shapes -- */
/* skip: the installed group loop, an empty byte's group skipped.  A byte with
   no set lane contributes no position, so its load, add and store can only
   write lanes the stream does not read; skipping it leaves the lanes before
   the cursor and writes the same positions after it. */
static inline uint64_t eo_ke_pos8_skip(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    for (int b = 0; b < 8; b++) {
        unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
        if (!x) continue;
        __m256i v = _mm256_load_si256((const __m256i *)eo_pos8[x]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
        _mm256_storeu_si256((__m256i *)o, v);
        o += (uint64_t)__builtin_popcount(x);
    }
    return (uint64_t)__builtin_popcountll(m);
}

/* sparse: one store per set lane, in increasing lane order, which is the
   stream's rule.  The word's positions are visited through the mask itself, so
   the work is the popcount rather than eight groups. */
static inline uint64_t eo_ke_sparse(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t k = 0, c = m;
    while (c) {
        o[k++] = base + (uint32_t)__builtin_ctzll(c);
        c &= c - 1;
    }
    return k;
}

/* The installed block loop's text, with the emitter as the parameter: one mask
   word per block, `noinline` so a caller's chunk costs one call. */
#define EO_DEFINE_KERNEL(NAME, BLOCK)                                         \
static __attribute__((noinline)) uint64_t                                     \
NAME(const uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out,        \
     uint64_t k) {                                                           \
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        uint64_t m = ent[i];                                                  \
        if (!m) continue;                                                     \
        k += BLOCK(m, (uint32_t)((blk0 + i) << 6), out + k);                   \
    }                                                                         \
    return k;                                                                 \
}
EO_DEFINE_KERNEL(eo_k_pos8_skip, eo_ke_pos8_skip)
EO_DEFINE_KERNEL(eo_k_sparse, eo_ke_sparse)
#undef EO_DEFINE_KERNEL

/* ------------------------------------------------------------------ ABI -- */
/* The installed unit's signatures, so a caller substitutes one for the other
   with no change at the call site. */
uint64_t eo_entry_pos8_skip(const uint64_t *ent, uint64_t blk0, uint64_t nblk,
                            uint32_t *out, uint64_t k) {
    return eo_k_pos8_skip(ent, blk0, nblk, out, k);
}

uint64_t eo_entry_sparse(const uint64_t *ent, uint64_t blk0, uint64_t nblk,
                         uint32_t *out, uint64_t k) {
    return eo_k_sparse(ent, blk0, nblk, out, k);
}
