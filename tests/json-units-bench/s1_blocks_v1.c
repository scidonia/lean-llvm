/* s1_blocks_v1.c -- the block unit's first (probe-only) body, frozen for the
   benchmark.

   This is `kernel/json/s1_blocks.c` at revision 64c3efe, the ASCII-probe body
   the v2 unit replaces: no UTF-8 arm, no `u8k` state, the return word the ASCII
   probe alone.  It is bench-only and is not compiled into any route; the
   benchmark compiles it beside the current unit and calls the same ABI, so the
   two bodies are timed at one boundary.  The symbol is renamed so both objects
   can be linked into one driver.

   The text is otherwise the frozen source: see the v2 file for the semantics of
   the masks, the escape list and the clamp. */
#include "s1_blocks.h"

#include "escape.h"
#include "s1_block_impl.h"

static inline void s1b_sw32_dn(__m256i v, uint32_t *d, uint32_t *nn) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_hi_tab), hi));
    *d = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *nn = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(r, z));
}

static inline void s1b_masks(__m256i v0, __m256i v1, S1F *st,
                             uint64_t *q_o, uint64_t *d_o, uint64_t *im_o,
                             uint64_t *n_o, uint64_t *bm_o) {
    const __m256i q = _mm256_set1_epi8('"');
    const __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    uint64_t qq = qm & ~s1f_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint32_t d0, d1, n0, n1;
    s1b_sw32_dn(v0, &d0, &n0);
    s1b_sw32_dn(v1, &d1, &n1);
    *d_o = (uint64_t)d0 | ((uint64_t)d1 << 32);
    *n_o = (uint64_t)n0 | ((uint64_t)n1 << 32);
    uint64_t im = s1f_prefix_xor(qq) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *q_o = qq;
    *im_o = im;
    *bm_o = bm;
}

static inline uint64_t s1b_ctl(__m256i v0, __m256i v1) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    return (uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
           ((uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
}

uint64_t leanllvm_json_s1_blocks_v1(const uint8_t *b, uint64_t n, uint64_t *ent,
                                    uint32_t *xp, uint64_t *nxp,
                                    uint64_t *xcarry, uint64_t arm) {
    uint64_t nfull = n >> 6;
    uint64_t rem = n & 63;
    uint64_t prevS = 0;
    S1F st = {0, 0, 0};
    __m256i ascii = _mm256_setzero_si256();

    for (uint64_t i = 0; i < nfull; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        ascii = _mm256_or_si256(ascii, _mm256_or_si256(v0, v1));
        uint64_t q, d, im, nn, bm;
        s1b_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
        if (arm & 2)
            leanllvm_json_escape_list(bm, s1b_ctl(v0, v1), im, i, xp, nxp, xcarry);
    }
    if (rem) {
        const uint8_t *p = b + (nfull << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        ascii = _mm256_or_si256(ascii, _mm256_or_si256(v0, v1));
        uint64_t q, d, im, nn, bm;
        s1b_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
        if (arm & 2)
            leanllvm_json_escape_list(bm, s1b_ctl(v0, v1), im, nfull, xp, nxp,
                                      xcarry);
    }
    return (uint64_t)(_mm256_testz_si256(ascii, _mm256_set1_epi8((char)0x80)) != 0);
}
