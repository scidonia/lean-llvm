/* utf8.c -- the UTF-8 validity unit of the measured SIMD JSON pipeline: the
   Keiser-Lemire `pshufb` table DFA, and the stage that runs it over a document.

   The tables, the load-form error vector and the tail test are the measured
   text of kernel/json/measured/u8kl.h, at the entities README.md's identity
   list names, with the permutation form the measured build does not select
   deleted (README.md's `utf8` deletion list; `identity/source-identity.sh
   --unit utf8` applies it and diffs tokens).  The stage's statements are the
   measured text of measured/s1fuse.h:1833-1841 and :1911-1912, at the
   `S1F_UTF8=7`, `S1F_KL_DOC=1` arm, with the one rename the ABI records: the
   document-level static `s1f_u8_ungated` becomes the parameter `ungated`.

   The stage is not a measured function.  In the measured header it is a run of
   statements inside `s1f_build2`'s block loop, which `S1F_TWOPHASE=1` selects,
   and the loop carries the whole pipeline: the block's masks, the entry and
   escape expansion, the output cursor.  This unit is the UTF-8 stage and
   nothing else -- it reads the document's bytes and returns one word -- so the
   loop here is the stage's own and the rest of the pipeline is not present.
   The loop's header and the declarations it needs are the new text; the marked
   region below is the measured statements, unchanged.

   Two copies of the stage exist in the measured header, `s1f_build2`'s and the
   unselected `s1f_build`'s, and the identity list names both ranges; the token
   arm asserts they are one text, which is what makes choosing either harmless.

   The DFA accumulates one error vector over the document.  Per 32-byte vector,
   with the previous bytes carried by the load form:

     p1,p2,p3 = the vector shifted right 1,2,3 bytes, read as three unaligned
                loads at `p-1`, `p-2`, `p-3` in the caller's window

     sc   = T1[lo(p1)] & T2[hi(p1)] & T3[hi(v)]
            bit 7 set = "this position's continuation status matches what the
            byte one back asks for"; the other seven bits are the structural
            error classes (overlong 2/3/4, surrogate, too large, lone
            continuation).

     must = 0x80 & ((p2 -sat 0x60) | (p3 -sat 0x70))
            the positions a 3- or 4-byte lead requires a continuation at.

     err  = sc ^ must, any non-zero byte being an error.

   The tables fold to literal vector operands in the emission, so this unit has
   no table parameter and no table global: `kl_t1`, `kl_t2` and `kl_t3` are
   read where they are defined, and each 32-byte vector's three `pshufb` calls
   carry their lanes.

   The tail rule is the stage's document-end rule and not the document's: a
   `C0`, `C1` or `F5..FF` at the last scanned position is reported at the
   position after it, which a full 64-byte block does not evaluate, so
   `kl_tail_byte` restores it.  Every other document-end rule falls out of the
   loop: with zero padding the position past the last document byte is scanned
   and a truncated final character is rejected, and with `n % 64 == 0` that
   position does not exist and a truncated `C2-F4` tail is accepted.  Which of
   the two the caller gets is the caller's staging rule; README.md records it as
   a limit and utf8.h states it as a consequence. */
#include "utf8.h"

#include <immintrin.h>
#include <stdint.h>

/* ---------------------------------------------------------------- tables -- */
/* T1 indexes the low nibble of the byte one position back, T2 its high nibble,
   and T3 the high nibble of the current byte; their conjunction is the
   position's structural word. */
static const uint8_t kl_t1[32] __attribute__((aligned(32))) = {
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
};
static const uint8_t kl_t2[32] __attribute__((aligned(32))) = {
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
};
static const uint8_t kl_t3[32] __attribute__((aligned(32))) = {
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
};

/* ---- load-based shifts -------------------------------------------------
   p1/p2/p3 come from three unaligned loads instead of vperm2i128+vpalignr.
   vpalignr and vpshufb share one execution port, so the loads are free where
   the shifts are not; this keeps the shuffle count at three per vector. */
static inline __m256i kl_err32_ld(__m256i v, const uint8_t *p) {
    const __m256i m4  = _mm256_set1_epi8(0x0F);
    const __m256i b80 = _mm256_set1_epi8((char)0x80);
    __m256i p1 = _mm256_loadu_si256((const __m256i *)(p - 1));
    __m256i p2 = _mm256_loadu_si256((const __m256i *)(p - 2));
    __m256i p3 = _mm256_loadu_si256((const __m256i *)(p - 3));
    __m256i sc = _mm256_and_si256(
        _mm256_and_si256(
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)kl_t1),
                _mm256_and_si256(p1, m4)),
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)kl_t2),
                _mm256_and_si256(_mm256_srli_epi16(p1, 4), m4))),
        _mm256_shuffle_epi8(
            _mm256_load_si256((const __m256i *)kl_t3),
            _mm256_and_si256(_mm256_srli_epi16(v, 4), m4)));
    __m256i must = _mm256_and_si256(
        _mm256_or_si256(
            _mm256_subs_epu8(p2, _mm256_set1_epi8(0x60)),
            _mm256_subs_epu8(p3, _mm256_set1_epi8(0x70))),
        b80);
    return _mm256_xor_si256(sc, must);
}

static inline __m256i kl_err_vec_ld(__m256i v0, __m256i v1, const uint8_t *p) {
    return _mm256_or_si256(kl_err32_ld(v0, p), kl_err32_ld(v1, p + 32));
}

/* a C0/C1/F5..FF at the last scanned position is reported one position later,
   i.e. outside the loop.  Call with the last scanned byte. */
static inline int kl_tail_byte(uint8_t b) {
    return (b & 0xFE) == 0xC0 || b >= 0xF5;
}

/* ------------------------------------------------------------------ stage -- */

/* The document is `b .. b+n-1`, `n < 2^63`, and the caller stages three zero
   bytes before it and zero padding to the 64-byte boundary after it; the block
   count is derived from `n` alone, so `n` is the length of the byte string this
   body scans and there is no second count to disagree with it.  `ungated`
   selects the stage's two block paths and the returned word is its error word:
   zero exactly when the staged window is valid. */
uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated)
{
    uint64_t nb = (n + 63) / 64;
    uint64_t err = 0;
    int prev_ascii = 1;
    const __m256i high = _mm256_set1_epi8((char)0x80);
    __m256i u8k = _mm256_setzero_si256();
    for (uint64_t bi = 0; bi < nb; bi++) {
        const uint8_t *p = b + (bi << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
/* begin: copied stage statements */
        if (ungated) {
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
        } else {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii))
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            prev_ascii = ascii;
        }
/* end: copied stage statements */
    }
/* begin: copied stage statements */
    err |= (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);
/* end: copied stage statements */
    return err;
}
