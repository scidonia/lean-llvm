/* bench-fastesc.c -- the stage-1 mask unit's escape/quote derivation with the
   bit-gather instructions removed.

   `s1f_masks` in `kernel/json/s1_block.c` derives the unescaped-quote mask from
   the raw quote and backslash masks with `_pext_u64`, `_pdep_u64` and
   `__builtin_clzll`:

     starts  = backslashes at the first lane of each run
     lasts   = backslashes at the last lane of each run
     alt     = even lanes, flipped at lane zero when the incoming run is odd
     esc     = pdep(~(pext(alt, starts) ^ pext(even, lasts)), lasts << 1)
                | (open & ~bs0 & ppar)
     ppar'   = top & (all-ones correction ^ clz(~bs) & 1)

   The quantities are the ones `LeanLLVM/Refinement/QuoteDerive.lean` pins:
   `kernelEscape_eq` says the escape mask is the parity mask on the lanes that
   are not backslashes, `kernelQuote64` says the unescaped quotes are the raw
   quotes without those lanes, and `ppn64` says the outgoing parity is the run
   parity at the block's end.  This file computes the same quantities with
   shifts, ands, xors, additions and one carry-less multiply, and no gather,
   scatter or count-leading-zeros instruction:

   * The parity of a backslash run is a property of its two ends: a run of odd
     length reaches an odd lane from an even start, or an even lane from an odd
     start.  So one addition of the run starts of one start-parity class to the
     backslash mask carries every such start through its run and clears a bit at
     the lane after the run's end; the carry stops on that non-backslash lane, so
     runs in different classes are added in separate sums and cannot interfere.
     Selecting the after-lane's own parity picks exactly the odd runs of that
     class.
   * A run that opens in the previous block is a continuation: its start parity
     is the incoming run parity (`open & ppar`) rather than lane zero's, so lane
     zero's start bit moves to that class, and a block whose lane zero is not a
     backslash escapes lane zero exactly when `open & ppar`.
   * The carry out of bit 63 of the odd-class sum is the outgoing run parity:
     the top run's start is odd exactly when its length is odd, which is
     `ppn64`'s `nextParity`.  This replaces the count-leading-zeros parity.
   * The in-string mask is the same carry-less prefix xor of the unescaped quote
     mask seeded by `im_carry`, as in the kernel.

   Everything else is kept as written in the kernel -- the two unaligned loads,
   the byte compares, the two table shuffles, the mask extraction and the writes
   of all six output words -- so a difference between this unit and the kernel is
   attributable to the escape/quote derivation alone.

   This is a benchmark candidate, not a kernel: it is called only by
   `tests/json-units-bench/bench.c`, which compares every mask word and the
   carry state against `leanllvm_json_s1_masks` on every block before timing it.
   `kernel/json/` is not edited. */
#include "../../kernel/json/s1_block.h"

#include <immintrin.h>
#include <stdint.h>

/* `s1f_prefix_xor`, under this file's name.  The all-ones carry-less product of
   the quote mask is its inclusive prefix xor (`Pclmul.lean`'s
   `clmul_allOnes_eq_fold`). */
static inline uint64_t fe_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

/* The two tables and the shuffle pair, copied from the kernel so the candidate
   does the same structural/whitespace work. */
static const uint8_t fe_lo_tab[32] __attribute__((aligned(32))) = {
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
};
static const uint8_t fe_hi_tab[32] __attribute__((aligned(32))) = {
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static inline void fe_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)fe_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)fe_hi_tab), hi));
    *sm = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *ws = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8((char)0xC0)), z));
}

static inline uint64_t fe_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {
    uint32_t s0, s1, w0, w1;
    fe_sw32(v0, &s0, &w0);
    fe_sw32(v1, &s1, &w1);
    *ws_o = (uint64_t)w0 | ((uint64_t)w1 << 32);
    return (uint64_t)s0 | ((uint64_t)s1 << 32);
}

/* The escape mask, from the backslash mask and the incoming carry.

   `escaped[i]` for a lane `i` that is not a backslash is the parity of the
   backslash run immediately before it; backslash lanes are not escape lanes
   (`kernelEscape_eq`).  A run whose first lane is `s` and last lane is `e` is
   escaped at `e + 1` exactly when `e + 1 - s` is odd, that is when `e + 1` and
   `s` have different parities.  Adding the run's start bit to the backslash
   mask carries it through the run's ones, clears them, and sets `e + 1`; the
   sum therefore marks every run of one start-parity class at its after-lane,
   and selecting the after-lanes of the other parity keeps that class's odd
   runs.  Two sums, one per start-parity class, cannot interfere: each class's
   carries stop on the non-backslash lane after a run, below the next run's
   start.

   The start-parity mask is the kernel's `%altc2`: the even lanes, flipped at
   lane zero when the previous block left an odd open run.  A run that opens in
   the previous block is a continuation, so its start parity is `open & ppar`
   rather than lane zero's, which is exactly that flip.  A non-backslash lane
   zero is escaped exactly in that case, which is the kernel's
   `boundaryEscape` term.

   The carry out of bit 63 of the odd-class sum is the top run's start parity,
   which is its length parity: the outgoing `ppar` (`ppn64`).  The outgoing
   `open` is bit 63. */
static inline uint64_t fe_escaped(uint64_t bs, uint64_t *open, uint64_t *ppar) {
    const uint64_t even_lanes = 0x5555555555555555ULL;
    uint64_t odd_open = *open & *ppar;      /* the incoming run's parity */
    uint64_t starts = bs & ~(bs << 1);
    uint64_t alt = even_lanes ^ odd_open;   /* `%altc2`: even lanes, flipped at 0 */
    uint64_t even_class = starts & alt;     /* runs whose start parity is zero */
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

/* Block masks: unescaped quotes, raw structurals, in-string, whitespace,
   backslash and control.  Identical to `s1f_masks` except that the quote mask
   is cleared through `fe_escaped`. */
static inline void fe_masks(__m256i v0, __m256i v1, s1_carry *st,
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
    sm = fe_sm_ws(v0, v1, &ws);
    *ws_o = ws;
    qm &= ~fe_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint64_t im = fe_prefix_xor(qm) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *qm_o = qm;
    *sm_o = sm;
    *im_o = im;
}

/* The ABI of `s1_block.h`, under a bench-only name.  `noinline` keeps the call
   opaque so a caller that reads one output word still charges the whole unit. */
__attribute__((noinline))
void leanllvm_json_s1_fastesc(const uint8_t *p, s1_carry *carry, s1_masks *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    uint64_t qm, sm, im, ws, bm, ctl;
    fe_masks(v0, v1, carry, &qm, &sm, &im, &ws, &bm, &ctl);
    out->quote = qm;
    out->delim = sm;
    out->in_string = im;
    out->ws = ws;
    out->backslash = bm;
    out->ctl = ctl;
}
