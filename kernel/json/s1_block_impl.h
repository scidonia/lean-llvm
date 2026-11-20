/* s1_block_impl.h -- the stage-1 classifier's text, shared by the two units
   that run it.

   This is the measured text of kernel/json/measured/s1fuse.h, at the line
   ranges README.md's identity list records, with the arms the measured build
   did not take deleted (README.md's deletion list; `identity/source-identity.sh`
   applies it and diffs).  Nothing else of the measured header is here: not the
   UTF-8 machinery, not the entry emitter, not the pipeline loop.

   `s1f_escaped` is the unit's own text, not the measured text: it derives the
   escape word with two carry-propagating sums, the boundary lane and the carry
   out of the top lane, and is proved the same function of the backslash word
   and the carry as the measured form (`LeanLLVM/Refinement/QuoteDerive.lean`,
   `fastEscape_eq_kernelEscape` and `fastPpar_eq_runParity`).  README.md records
   the substitution and its evidence; both identity arms name it as the one
   exclusion.

   The text is header-only because two units run it over one block at a time:
   `leanllvm_json_s1_masks` (s1_block.c), which publishes all six mask words,
   and `leanllvm_json_s1_blocks` (s1_blocks.c), which keeps the masks in
   registers and stores only the entry word.  `s1f_masks` keeps its measured
   name, its measured parameter type `S1F *` and its measured signature, so the
   token diff and the IR diff both compare the measured function rather than a
   re-spelling of it; `S1F` is the units' three-word carry, the same object as
   `s1_carry`. */
#ifndef LEANLLVM_KERNEL_JSON_S1_BLOCK_IMPL_H
#define LEANLLVM_KERNEL_JSON_S1_BLOCK_IMPL_H

#include <immintrin.h>
#include <stdint.h>

#include "s1_block.h"

/* The measured carry type, at the three fields this unit reads and writes
   (`esc_open` at +0, `esc_ppar` at +8, `im_carry` at +16).  The measured
   header's `prevS`, `bs_prevb` and `bs_prevs` belong to the entry and escape
   units and are not part of this one. */
typedef s1_carry S1F;

/* ------------------------------------------------------------ classifier -- */
static inline uint64_t s1f_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

/* The escape mask from the backslash mask and the incoming carry.  A run whose
   first lane is `s` and last lane is `e` escapes the lane after it exactly when
   `e + 1 - s` is odd, so adding the run's start bit to the backslash mask carries
   through the run and marks that lane; the sums are separated by the start's
   parity, because a carry stops on the non-backslash lane after a run.  A run
   that opens in the previous block has its start parity in `open & ppar`, which
   also gives lane zero's boundary escape.  The carry out of bit 63 of the
   odd-class sum is the outgoing run parity. */
static inline uint64_t s1f_escaped(uint64_t bs, uint64_t *open, uint64_t *ppar) {
    const uint64_t even_lanes = 0x5555555555555555ULL;
    uint64_t odd_open = *open & *ppar;
    uint64_t starts = bs & ~(bs << 1);
    uint64_t alt = even_lanes ^ odd_open;
    uint64_t even_class = starts & alt;
    uint64_t odd_class = starts ^ even_class;
    uint64_t notbs = ~bs;
    uint64_t sum_even = bs + even_class;
    uint64_t sum_odd = bs + odd_class;
    uint64_t esc = ((sum_even & notbs) & ~even_lanes) |
                   ((sum_odd & notbs) & even_lanes) |
                   (odd_open & (notbs & 1));
    *ppar = (uint64_t)(sum_odd < bs);
    *open = bs >> 63;
    return esc;
}

/* Structural and whitespace masks from one shuffle pair: each low nibble and
   each high nibble carries a bit set per class it can take part in, and the
   AND is non-zero exactly for the six structural bytes (bits 0-5) and the four
   whitespace bytes (bits 6-7).  Verified exhaustively against the byte sets. */
static const uint8_t s1f_lo_tab[32] __attribute__((aligned(32))) = {
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
};
static const uint8_t s1f_hi_tab[32] __attribute__((aligned(32))) = {
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static inline void s1f_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_hi_tab), hi));
    *sm = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *ws = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8((char)0xC0)), z));
}

static inline uint64_t s1f_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {
    uint32_t s0, s1, w0, w1;
    s1f_sw32(v0, &s0, &w0);
    s1f_sw32(v1, &s1, &w1);
    *ws_o = (uint64_t)w0 | ((uint64_t)w1 << 32);
    return (uint64_t)s0 | ((uint64_t)s1 << 32);
}

/* Block masks in ci2's sense: unescaped quotes, raw structurals, in-string.
   With S1F_XS the raw backslash mask and the control-byte mask come out too,
   for the escape-position list. */
static inline void s1f_masks(__m256i v0, __m256i v1, S1F *st,
                             uint64_t *qm_o, uint64_t *sm_o, uint64_t *im_o,
                             uint64_t *ws_o, uint64_t *bm_o, uint64_t *ctl_o) {
    __m256i q = _mm256_set1_epi8('"');
    __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    {
        const __m256i v19 = _mm256_set1_epi8(0x1F);
        *ctl_o = (uint64_t)(uint32_t)_mm256_movemask_epi8(
                     _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
                 ((uint64_t)(uint32_t)_mm256_movemask_epi8(
                     _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
    }
    *bm_o = bm;
    uint64_t sm = 0, ws = 0;
    sm = s1f_sm_ws(v0, v1, &ws);
    *ws_o = ws;
    qm &= ~s1f_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint64_t im = s1f_prefix_xor(qm) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *qm_o = qm;
    *sm_o = sm;
    *im_o = im;
}

#endif
