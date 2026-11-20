/* s1_blocks.c -- the contracted stage-1 mask pass.

   One loop over the document's 64-byte blocks runs the classifier and reduces
   its masks to the block's entry word: the unescaped quote, the structural
   byte outside a string, and the run start carried from the previous block's
   top scalar lane.  The word is clamped past the document's end and stored at
   `ent[i]`; when the gate selects the escape list, the block's backslash,
   control and in-string words go to the escape unit by value and the list's
   carry is the caller's `xcarry`.

   Two shapes of the same body, both measured (`string-classifier-transcript.txt`):

   * the composition reads the two masks it needs and one complement: the
     classifier's delimiter word, its *neither* word (neither structural nor
     whitespace), and the whitespace word is never needed on its own.  The
     scalar word is `neither & ~quote & ~in_string`, the same complement the
     four-mask form builds, so dropping the whitespace word removes one mask
     from the block's arithmetic and nothing from its output;
   * the loop peels the final partial block, so the `lim < 64` test is not in
     the full-block loop.

   The control-byte word is only the escape list's input, so the list-free path
   does not compute it: the gate's arm computes it where the call is.

   The return word is the ASCII probe: the body ORs every loaded lane into one
   accumulator (two `vpor` per block) and tests its high bits once at the end;
   `1` means every document byte is below `0x80`, and an empty document is
   vacuously ASCII.

   The classifier carry lives in this body and starts at zero, so no caller
   stages it.  The mask words, the in-string carry and the previous block's
   scalar lane are registers; the unit has no stack and writes only `ent`, and
   `xp`/`*nxp`/`xcarry` when the gate selects the list.  The entry emitter is
   the caller's: it reads the `ent` array in one call over all blocks. */
#include "s1_blocks.h"

#include "escape.h"
#include "s1_block_impl.h"

/* Structural/whitespace classification, in the two outputs the composition
   reads: the delimiter word and the *neither* word — the lanes whose table
   entry is zero, so neither a structural byte nor a whitespace byte. */
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

/* The block's masks for the composition: unescaped quotes, the delimiter word,
   the in-string word and the neither word, plus the raw backslash word the
   escape list's gate passes by value. */
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

/* The raw control-byte word, computed only where the escape list is called. */
static inline uint64_t s1b_ctl(__m256i v0, __m256i v1) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    return (uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
           ((uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
}

uint64_t leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n, uint64_t *ent,
                                 uint32_t *xp, uint64_t *nxp, uint64_t *xcarry,
                                 uint64_t arm) {
    uint64_t nfull = n >> 6;            /* whole blocks, without the tail */
    uint64_t rem = n & 63;              /* tail bytes; zero on a block boundary */
    uint64_t prevS = 0;                 /* the previous block's top scalar lane */
    S1F st = {0, 0, 0};                 /* block-local classifier carry */
    __m256i ascii = _mm256_setzero_si256();  /* every byte the document holds */

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
    /* The ASCII probe: every byte below 0x80 is exactly no high bit in the
       document's OR.  `_mm256_testz_si256` answers `(ascii & highbits) == 0`,
       and an empty document is vacuously ASCII. */
    return (uint64_t)(_mm256_testz_si256(ascii, _mm256_set1_epi8((char)0x80)) != 0);
}
