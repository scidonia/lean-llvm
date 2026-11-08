/* u8kl.h -- Keiser-Lemire vectorised UTF-8 validation (scratch, spike 47).

   Per 32-byte vector, with the previous vector carried:

     p1,p2,p3 = the vector shifted right 1,2,3 bytes (the previous vector
                supplies the carry; zeros at the document start, which is the
                same convention the old probe uses for p-1..p-3)

     sc   = T1[lo(p1)] & T2[hi(p1)] & T3[hi(v)]
            high bit set = "this position's continuation status matches what
            the byte one back asks for"; any other non-zero bit is a
            structural error (overlong 2/3/4, surrogate, too large, lone
            continuation).  T1 depends on the low nibble of p1, T2 on its high
            nibble, T3 on the high nibble of the current byte.

     must = 0x80 & ((p2 - 0x60) | (p3 - 0x70))
            p2 >= 0xE0 marks the 2nd continuation of a 3/4-byte sequence,
            p3 >= 0xF0 its 3rd; the saturating subtract leaves bit 7 set
            exactly for those bytes and the AND keeps only that bit.

     err  = sc ^ must   (any non-zero byte is an error)

   The tables are the published ones (verified exhaustively here, which also
   pins the exact tail behaviour against this harness's scalar reference).

   Tail: a C0/C1/F5..FF byte is reported at the position *after* it, so a bad
   byte at the last scanned position of a document escapes the block loop.
   kl_tail() restores it; every other document-end rule (a lead whose
   continuations would start past the last byte is not evaluated) falls out
   of the block loop exactly as it does for the old probe.
*/
#ifndef U8KL_H
#define U8KL_H

#include <immintrin.h>
#include <stdint.h>

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

typedef struct {
    __m256i prev;       /* previous 32-byte vector (its tail is p1..p3's carry) */
} KLCARRY;

static inline void kl_carry_init(KLCARRY *c) {
    c->prev = _mm256_setzero_si256();
}

/* error vector of one vector's worth of positions; `mm` is the per-vector
   permute already made by the caller */
static inline __m256i kl_err32(__m256i v, __m256i mm, const KLCARRY *c) {
    const __m256i m4  = _mm256_set1_epi8(0x0F);
    const __m256i b80 = _mm256_set1_epi8((char)0x80);
    __m256i p1 = _mm256_alignr_epi8(v, mm, 15);
    __m256i p2 = _mm256_alignr_epi8(v, mm, 14);
    __m256i p3 = _mm256_alignr_epi8(v, mm, 13);
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
    (void)c;
    return _mm256_xor_si256(sc, must);
}

static inline __m256i kl_err_vec(__m256i v0, __m256i v1, const KLCARRY *c) {
    __m256i m0 = _mm256_permute2x128_si256(c->prev, v0, 0x21);
    __m256i m1 = _mm256_permute2x128_si256(v0, v1, 0x21);
    return _mm256_or_si256(kl_err32(v0, m0, c), kl_err32(v1, m1, c));
}

static inline int kl_block_vec(__m256i v0, __m256i v1, KLCARRY *c) {
    __m256i e = kl_err_vec(v0, v1, c);
    c->prev = v1;
    return (int)!_mm256_testz_si256(e, e);
}

static inline int kl_block(const uint8_t *p, KLCARRY *c) {
    return kl_block_vec(_mm256_loadu_si256((const __m256i *)p),
                        _mm256_loadu_si256((const __m256i *)(p + 32)), c);
}

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

static inline int kl_block_ld(const uint8_t *p) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
    __m256i e = kl_err_vec_ld(v0, v1, p);
    return (int)!_mm256_testz_si256(e, e);
}

/* a C0/C1/F5..FF at the last scanned position is reported one position later,
   i.e. outside the loop.  Call with the last scanned byte. */
static inline int kl_tail_byte(uint8_t b) {
    return (b & 0xFE) == 0xC0 || b >= 0xF5;
}

/* carry state for a scan that starts at an arbitrary offset: the 32 bytes
   before `p` (the harness pads the buffer, so a plain load is in bounds) */
static inline void kl_carry_prefix(KLCARRY *c, const uint8_t *p) {
    c->prev = _mm256_loadu_si256((const __m256i *)(p - 32));
}

#endif /* U8KL_H */
