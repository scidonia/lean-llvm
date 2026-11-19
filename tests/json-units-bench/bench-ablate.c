/* bench-ablate.c -- two bench-only ablations of the stage-1 mask unit.

   These are copies of `s1f_masks` from `kernel/json/s1_block.c` with one part
   of the block's derivation deleted, so the harness can charge that part
   separately.  They are cost bounds and not classifiers: an ablated mask word
   says nothing about a JSON document, and nothing outside `bench.c` may call
   them.

     leanllvm_json_s1_masks_noesc
       `s1f_escaped` is gone: the unescaped-quote correction is not applied and
       the two escape carry fields are left untouched.  The prefix xor and the
       in-string carry are still there, so the difference against `s1_masks` is
       the `pext`/`pdep`/`clz` work and the escape carry update.

     leanllvm_json_s1_masks_noesc_noparity
       As above, and the in-string word is the raw quote mask: no prefix xor,
       no in-string carry update.  The difference against `noesc` is the
       `clmul` parity.

   Everything else is kept as written in the kernel: the two unaligned loads,
   the byte compares, the two table shuffles, the mask extraction, and the
   writes of all six output words.  Only the derivation between the raw quote
   mask and the in-string word is ablated.

   Compiled at the measured compiler line by `bench.sh`, as its own object and
   at its own name, so `kernel/json/` is not edited and the kernel object keeps
   its measured bytes. */
#include "../../kernel/json/s1_block.h"

#include <immintrin.h>
#include <stdint.h>

/* `s1f_prefix_xor`, under this file's name.  The in-string derivation's parity
   step, kept whole. */
static inline uint64_t ab_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

/* The two tables and the shuffle pair, copied from the kernel so the ablated
   unit does the same non-derivation work. */
static const uint8_t ab_lo_tab[32] __attribute__((aligned(32))) = {
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
};
static const uint8_t ab_hi_tab[32] __attribute__((aligned(32))) = {
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static inline void ab_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)ab_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)ab_hi_tab), hi));
    *sm = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *ws = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8((char)0xC0)), z));
}

static inline uint64_t ab_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {
    uint32_t s0, s1, w0, w1;
    ab_sw32(v0, &s0, &w0);
    ab_sw32(v1, &s1, &w1);
    *ws_o = (uint64_t)w0 | ((uint64_t)w1 << 32);
    return (uint64_t)s0 | ((uint64_t)s1 << 32);
}

/* The no-escape masks: `s1f_masks` with `s1f_escaped` deleted.  The escape
   carry fields are neither read nor written; `im_carry` still is. */
static inline void ab_masks_noesc(__m256i v0, __m256i v1, s1_carry *st,
                                  uint64_t *qm_o, uint64_t *sm_o,
                                  uint64_t *im_o, uint64_t *ws_o,
                                  uint64_t *bm_o, uint64_t *ctl_o) {
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
    sm = ab_sm_ws(v0, v1, &ws);
    *ws_o = ws;
    /* `qm &= ~s1f_escaped(...)` is deleted; the raw quote mask stands. */
    uint64_t im = ab_prefix_xor(qm) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *qm_o = qm;
    *sm_o = sm;
    *im_o = im;
}

/* The no-escape, no-parity masks: also `im = qm`, with no `im_carry` read or
   write. */
static inline void ab_masks_noesc_noparity(__m256i v0, __m256i v1, s1_carry *st,
                                           uint64_t *qm_o, uint64_t *sm_o,
                                           uint64_t *im_o, uint64_t *ws_o,
                                           uint64_t *bm_o, uint64_t *ctl_o) {
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
    sm = ab_sm_ws(v0, v1, &ws);
    *ws_o = ws;
    /* No escape correction, no prefix xor, no in-string carry. */
    uint64_t im = qm;
    (void)st;
    *qm_o = qm;
    *sm_o = sm;
    *im_o = im;
}

/* The ABI of `s1_block.h`, under a bench-only name.  `noinline` keeps every
   call opaque: with the caller reading one output word per block in the timed
   pass, an inlined copy would let the compiler drop the outputs it does not
   read, and the row would time a shorter function than the one measured. */
__attribute__((noinline))
void leanllvm_json_s1_masks_noesc(const uint8_t *p, s1_carry *carry,
                                  s1_masks *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    uint64_t qm, sm, im, ws, bm, ctl;
    ab_masks_noesc(v0, v1, carry, &qm, &sm, &im, &ws, &bm, &ctl);
    out->quote = qm;
    out->delim = sm;
    out->in_string = im;
    out->ws = ws;
    out->backslash = bm;
    out->ctl = ctl;
}

__attribute__((noinline))
void leanllvm_json_s1_masks_noesc_noparity(const uint8_t *p, s1_carry *carry,
                                           s1_masks *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    uint64_t qm, sm, im, ws, bm, ctl;
    ab_masks_noesc_noparity(v0, v1, carry, &qm, &sm, &im, &ws, &bm, &ctl);
    out->quote = qm;
    out->delim = sm;
    out->in_string = im;
    out->ws = ws;
    out->backslash = bm;
    out->ctl = ctl;
}
