/* pipeline_fast.c -- the benchmark-only full-pipeline candidate.

   The candidate is `splitfast3_u8` from
   `tests/json-units-bench/bench-contract.c` assembled with the rest of the
   pipeline: its mask pass (`maskfast_u8`) writes one entry word per block into
   the caller's `ent`, the three-slot emitter turns those words into the entry
   stream, the fused UTF-8 word either refuses at the document's end or lets
   stage 2 walk the stream.  `pipeline_fast.h` states the ABI, the staging
   promises and the fields a harness compares; `pipeline.h` remains the
   default route's ABI and is not changed by this file.

   Two entries share that shape.  `leanllvm_json_pipeline_fast` is the
   list-free one and stays the measured `splitfast3_u8` candidate.
   `leanllvm_json_pipeline_fast_list` additionally builds the stage-1 escape
   list with the tree's `leanllvm_json_escape_list` call and hands its count to
   stage 2, so the list-driven decoder is measured against the list-free
   rescan; its escape carry is a local zeroed at the document's first block, so
   it needs no caller-staged carry and keeps the same ABI.

   This file carries no bench harness, no clock and no arm selector, and it
   includes no `LeanLLVM/Refinement` machinery: it is a prototype of the
   candidate's shape, gated by the harness over the corpus rather than by a
   theorem. */
#include "pipeline_fast.h"

#include <immintrin.h>
#include <stdint.h>

#include "entry.h"
#include "escape.h"
#include "measured/u8kl.h"
#include "pipeline_fast_plain.h"
#include "s1_block_impl.h"
#include "stage2.h"

/* ------------------------------------------------------------ classifier --
   The composition reads two classification words: the structural (delimiter)
   word and the *neither* word, the lanes whose table entry is zero, so neither
   a structural byte nor a whitespace byte.  `s1_block_impl.h`'s `s1f_sw32`
   returns the delimiter and whitespace words; the whitespace word is what the
   composition never reads on its own, so this returns the neither word
   instead.  One `movemask` per word either way. */
static inline void pf_sw32_dn(__m256i v, uint32_t *d, uint32_t *n) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_hi_tab), hi));
    *d = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *n = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(r, z));
}

/* The block's masks for the composition: unescaped quotes, the delimiter
   word, the in-string word and the neither word, plus the raw backslash word
   the escape list's arm passes by value.  The raw word is the one
   `s1f_escaped` already consumes, so returning it costs the list-free arm
   nothing. */
static inline __attribute__((always_inline))
void pf_masks(__m256i v0, __m256i v1, S1F *st,
              uint64_t *q_o, uint64_t *d_o, uint64_t *im_o, uint64_t *n_o,
              uint64_t *bs_o) {
    const __m256i q = _mm256_set1_epi8('"');
    const __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    uint64_t qq = qm & ~s1f_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint32_t d0, d1, n0, n1;
    pf_sw32_dn(v0, &d0, &n0);
    pf_sw32_dn(v1, &d1, &n1);
    *d_o = (uint64_t)d0 | ((uint64_t)d1 << 32);
    *n_o = (uint64_t)n0 | ((uint64_t)n1 << 32);
    uint64_t im = s1f_prefix_xor(qq) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *q_o = qq;
    *im_o = im;
    *bs_o = bm;
}

/* The raw control-byte word, computed only where the escape list is called. */
static inline uint64_t pf_ctl(__m256i v0, __m256i v1) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    return (uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
           ((uint64_t)(uint32_t)_mm256_movemask_epi8(
               _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
}

/* ----------------------------------------------------------------- UTF-8 --
   `measured/u8kl.h`'s load form is the gate: `kl_err_vec_ld` over the two
   vectors the classifier already loaded, and `kl_tail_byte` after the loop.
   The header is included rather than copied, so its tables have one source --
   the one `utf8.c`'s identity arm pins -- and this file carries no second copy
   to drift. */

/* ------------------------------------------------------------- mask pass --
   One pass over the document: the entry word per block into `ent`, the
   optional escape list into `xp`/`*nxp`, and the fused UTF-8 error word out.
   The full-block loop and the peeled partial block are `maskfast_u8`'s, so the
   `lim < 64` clamp is not in the loop.  The gate is
   `leanllvm_json_utf8`'s: a block pays the DFA when it or its predecessor
   carries a high bit, and the document-end tail byte is checked outside the
   loop.

   The list arm is a compile-time selection rather than a loop-carried branch,
   as the bench's four pass bodies are: leaving it inside the loop costs the
   list-free body the list path's registers.  The list body computes the
   block's control-byte word (the only input the list-free classifier does not
   already form) and calls the tree's escape list with the candidate's own
   carry, which is zero at the document's first block. */
#define PF_MASK_PASS(NAME, LIST)                                             \
static uint64_t NAME(const uint8_t *b, uint64_t n, uint64_t *ent,            \
                     uint32_t *xp, uint64_t *nxp, uint64_t *xc) {            \
    S1F st = { 0, 0, 0 };                                                    \
    uint64_t prevS = 0;                                                      \
    uint64_t nfull = n >> 6, rem = n & 63;                                   \
    __m256i u8k = _mm256_setzero_si256();                                    \
    const __m256i high = _mm256_set1_epi8((char)0x80);                       \
    int prev_ascii = 1;                                                      \
    (void)xp;                                                                \
    (void)nxp;                                                               \
    (void)xc;                                                                \
    for (uint64_t i = 0; i < nfull; i++) {                                   \
        const uint8_t *p = b + (i << 6);                                     \
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);   \
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32)); \
        uint64_t q, d, im, nn, bm;                                           \
        pf_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);                        \
        uint64_t S = nn & ~q & ~im;                                          \
        uint64_t e = q | (d & ~im);                                          \
        e |= S & ~((S << 1) | prevS);                                        \
        prevS = S >> 63;                                                     \
        ent[i] = e;                                                          \
        if (LIST)                                                            \
            leanllvm_json_escape_list(bm, pf_ctl(v0, v1), im, i, xp, nxp,    \
                                      xc);                                   \
        int ascii = _mm256_testz_si256(_mm256_or_si256(v0, v1), high);       \
        if (!(ascii && prev_ascii))                                          \
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));            \
        prev_ascii = ascii;                                                  \
    }                                                                        \
    if (rem) {                                                               \
        const uint8_t *p = b + (nfull << 6);                                 \
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);   \
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32)); \
        uint64_t q, d, im, nn, bm;                                           \
        pf_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);                        \
        uint64_t S = nn & ~q & ~im;                                          \
        uint64_t e = q | (d & ~im);                                          \
        e |= S & ~((S << 1) | prevS);                                        \
        ent[nfull] = e & ((1ULL << rem) - 1ULL);                             \
        if (LIST)                                                            \
            leanllvm_json_escape_list(bm, pf_ctl(v0, v1), im, nfull, xp,     \
                                      nxp, xc);                              \
        int ascii = _mm256_testz_si256(_mm256_or_si256(v0, v1), high);       \
        if (!(ascii && prev_ascii))                                          \
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));            \
    }                                                                        \
    uint64_t err = (uint64_t)!_mm256_testz_si256(u8k, u8k);                  \
    if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);              \
    return err;                                                              \
}

PF_MASK_PASS(pf_mask_core, 0)
PF_MASK_PASS(pf_mask_list, 1)
#undef PF_MASK_PASS

/* ---------------------------------------------------------------- entry -- */
uint64_t leanllvm_json_pipeline_fast(const uint8_t *b, uint64_t n,
                                     uint64_t *ent,
                                     uint32_t *ep, uint64_t epcap,
                                     uint64_t *nk,
                                     uint32_t *xp, uint64_t xpcap,
                                     uint64_t *nxp,
                                     uint8_t *dst, uint64_t dstcap,
                                     uint64_t *ndst,
                                     uint8_t *ev, uint64_t evcap,
                                     uint64_t *nev,
                                     uint64_t *err) {
    uint64_t nblk = (n + 63) >> 6;
    uint64_t u8 = pf_mask_core(b, n, ent, xp, nxp, 0);
    uint64_t k;

    (void)epcap;
    (void)xpcap;

    k = leanllvm_json_entry_b3(ent, 0, nblk, ep, *nk);
    *nk = k;

    /* The document-level verdict keeps the default's rule and its order: the
       entry stream is written first, and an invalid document is refused at
       its end, because the UTF-8 stage reports that the document is invalid
       and not where. */
    if (u8 != 0) {
        *err = n;
        return 0;
    }

    /* Stage 2 owns the remaining refusals.  The candidate has no escape-list
       arm, so `xp`/`*nxp` are the caller's and pass through unchanged. */
    return leanllvm_json_stage2(b, n, ep, k, xp, *nxp,
                                dst, dstcap, ndst, ev, evcap, nev, err);
}

/* The list arm of the same shape: the mask pass appends the document's escape
   positions to `xp`/`*nxp`, and stage 2 takes its list-driven decoder.  The
   carry is the pass's own, zero at the first block, so the caller stages no
   escape-list scratch. */
uint64_t leanllvm_json_pipeline_fast_list(const uint8_t *b, uint64_t n,
                                          uint64_t *ent,
                                          uint32_t *ep, uint64_t epcap,
                                          uint64_t *nk,
                                          uint32_t *xp, uint64_t xpcap,
                                          uint64_t *nxp,
                                          uint8_t *dst, uint64_t dstcap,
                                          uint64_t *ndst,
                                          uint8_t *ev, uint64_t evcap,
                                          uint64_t *nev,
                                          uint64_t *err) {
    uint64_t nblk = (n + 63) >> 6;
    uint64_t xc[2] = { 0, 0 };
    uint64_t u8 = pf_mask_list(b, n, ent, xp, nxp, xc);
    uint64_t k;

    (void)epcap;
    (void)xpcap;

    k = leanllvm_json_entry_b3(ent, 0, nblk, ep, *nk);
    *nk = k;

    if (u8 != 0) {
        *err = n;
        return 0;
    }

    return leanllvm_json_stage2(b, n, ep, k, xp, *nxp,
                                dst, dstcap, ndst, ev, evcap, nev, err);
}

/* ---------------------------------------------------------- the selector --
   The document's class from a bounded prefix: one high-bit sweep and one
   backslash sweep over the first 128 bytes, in the classifier's own loads and
   idiom.  Both sweeps stop at 128 bytes, so the cost is independent of the
   document's length.  The prefix separates the measured corpus: the first
   backslash of a strings document is at offset 74-115 and the first high byte
   of a UTF-8 document at offset 7-28. */
enum { PF_CLASS_DENSE = 0, PF_CLASS_STRINGS = 1, PF_CLASS_UTF8 = 2 };

static int pf_class(const uint8_t *b, uint64_t n) {
    const __m256i high = _mm256_set1_epi8((char)0x80);
    const __m256i bs = _mm256_set1_epi8('\\');
    __m256i x0, x1, any;
    uint32_t bm;

    if (n == 0) return PF_CLASS_DENSE;
    x0 = _mm256_loadu_si256((const __m256i *)(const void *)b);
    x1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + 32));
    any = _mm256_or_si256(x0, x1);
    bm = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(x0, bs)) |
         (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(x1, bs));
    if (n > 64) {
        __m256i y0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + 64));
        __m256i y1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + 96));
        any = _mm256_or_si256(any, _mm256_or_si256(y0, y1));
        bm |= (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(y0, bs)) |
              (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(y1, bs));
    }
    if (!_mm256_testz_si256(any, high)) return PF_CLASS_UTF8;
    return bm != 0 ? PF_CLASS_STRINGS : PF_CLASS_DENSE;
}

/* The per-document choice the C ranking measured: pos8 on dense documents, the
   fused entry on UTF-8 and on strings at or below 64 KiB, and the escape-list
   entry on larger strings.  The chosen entry is called with the caller's
   arguments unchanged, so the best entry's output is that entry's. */
uint64_t leanllvm_json_pipeline_fast_best(const uint8_t *b, uint64_t n,
                                          uint64_t *ent,
                                          uint32_t *ep, uint64_t epcap,
                                          uint64_t *nk,
                                          uint32_t *xp, uint64_t xpcap,
                                          uint64_t *nxp,
                                          uint8_t *dst, uint64_t dstcap,
                                          uint64_t *ndst,
                                          uint8_t *ev, uint64_t evcap,
                                          uint64_t *nev,
                                          uint64_t *err) {
    int cls = pf_class(b, n);

    if (cls == PF_CLASS_DENSE)
        return leanllvm_json_pipeline_fast_plain_pos8(
            b, n, ent, ep, epcap, nk, xp, xpcap, nxp, dst, dstcap, ndst, ev,
            evcap, nev, err);
    if (cls == PF_CLASS_STRINGS && n > 65536)
        return leanllvm_json_pipeline_fast_list(
            b, n, ent, ep, epcap, nk, xp, xpcap, nxp, dst, dstcap, ndst, ev,
            evcap, nev, err);
    return leanllvm_json_pipeline_fast(
        b, n, ent, ep, epcap, nk, xp, xpcap, nxp, dst, dstcap, ndst, ev, evcap,
        nev, err);
}
