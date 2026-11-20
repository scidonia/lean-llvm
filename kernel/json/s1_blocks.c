/* s1_blocks.c -- the contracted stage-1 mask pass, with the UTF-8 stage fused.

   One loop over the document's 64-byte blocks runs the classifier and reduces
   its masks to the block's entry word: the unescaped quote, the structural
   byte outside a string, and the run start carried from the previous block's
   top scalar lane.  The word is clamped past the document's end and stored at
   `ent[i]`; when the gate selects the escape list, the block's backslash,
   control and in-string words go to the escape unit by value and the list's
   carry is the caller's `xcarry`.

   The same loop carries the UTF-8 stage's state: the Keiser-Lemire error
   vector `u8k` and the previous block's ASCII answer.  The block's two vectors
   are the ones the classifier already loaded, and the three bytes before the
   block (`p - 3`) are the DFA's load-form carry, which the caller stages as
   zero before the document.  When `arm & 4` is clear the stage is gated: a
   block whose predecessor was ASCII and which is itself ASCII skips the DFA,
   because the error vector `klErrBlk` is zero there (the `JsonUtf8Fused`
   `utf8Skip_eq_zero`).  When `arm & 4` is set the DFA runs on every block,
   which is `utf8.h`'s `ungated` path; the verdict is the same either way.

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

   The return word carries both document-level answers:

   * bit 0 is the ASCII probe: the body ORs every loaded lane into one
     accumulator (two `vpor` per block) and tests its high bits once at the end;
     `1` means every document byte is below `0x80`, and an empty document is
     vacuously ASCII.  It is the v1 word, unchanged.
   * bit 1 is the UTF-8 stage's error word: `1` means the staged window is not
     a valid prefix, and `0` means it is (`utf8WinPrefix` at the window the
     three zero prefix bytes, the document and its zero padding form).  It is
     `leanllvm_json_utf8`'s word, computed in this loop at the block's own
     loads, so the pipeline reads it here and the separate UTF-8 call
     disappears.
   * bits 2 and above are zero.

   `r & 2 == 0` is therefore the verdict, `r & 1` the ASCII class, and the
   pipeline consumes those two bits.  The arm word's bit 2 selects the UTF-8
   gate (`0` gated, `1` ungated) as `utf8.h` does; bits at and above 3 are
   reserved and ignored.

   The classifier carry lives in this body and starts at zero, so no caller
   stages it.  The mask words, the in-string carry, the previous block's
   scalar lane and the UTF-8 state are registers; the unit has no stack and
   writes only `ent`, and `xp`/`*nxp`/`xcarry` when the gate selects the list.
   The entry emitter is the caller's: it reads the `ent` array in one call over
   all blocks. */
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

/* The UTF-8 stage's three 32-byte tables and its load-form error vector.  The
   text is `utf8.c`'s (`measured/u8kl.h`), carried here because the stage runs
   inside this loop rather than at a call: the two vectors and the three bytes
   before the block are already in the block's window.  The table bytes and the
   `sc`/`must` arithmetic are the unit's, which `JsonUtf8IR`/`JsonUtf8Spec`
   define, and `tests/json-utf8/check.sh` ties these constants to the header's
   bytes. */
static const uint8_t s1b_kl_t1[32] __attribute__((aligned(32))) = {
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
};
static const uint8_t s1b_kl_t2[32] __attribute__((aligned(32))) = {
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
};
static const uint8_t s1b_kl_t3[32] __attribute__((aligned(32))) = {
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
};

static inline __m256i s1b_kl_err32(__m256i v, const uint8_t *p) {
    const __m256i m4 = _mm256_set1_epi8(0x0F);
    const __m256i b80 = _mm256_set1_epi8((char)0x80);
    __m256i p1 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 1));
    __m256i p2 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 2));
    __m256i p3 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 3));
    __m256i sc = _mm256_and_si256(
        _mm256_and_si256(
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)s1b_kl_t1),
                _mm256_and_si256(p1, m4)),
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)s1b_kl_t2),
                _mm256_and_si256(_mm256_srli_epi16(p1, 4), m4))),
        _mm256_shuffle_epi8(
            _mm256_load_si256((const __m256i *)s1b_kl_t3),
            _mm256_and_si256(_mm256_srli_epi16(v, 4), m4)));
    __m256i must = _mm256_and_si256(
        _mm256_or_si256(
            _mm256_subs_epu8(p2, _mm256_set1_epi8(0x60)),
            _mm256_subs_epu8(p3, _mm256_set1_epi8(0x70))),
        b80);
    return _mm256_xor_si256(sc, must);
}

static inline __m256i s1b_kl_err_vec(__m256i v0, __m256i v1, const uint8_t *p) {
    return _mm256_or_si256(s1b_kl_err32(v0, p), s1b_kl_err32(v1, p + 32));
}

/* The stage's document-end rule: a `C0`, `C1` or `F5..FF` at the last scanned
   position is restored, because the full block does not evaluate the position
   after it. */
static inline int s1b_kl_tail_byte(uint8_t b) {
    return (b & 0xFE) == 0xC0 || b >= 0xF5;
}

uint64_t leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n, uint64_t *ent,
                                 uint32_t *xp, uint64_t *nxp, uint64_t *xcarry,
                                 uint64_t arm) {
    uint64_t nfull = n >> 6;            /* whole blocks, without the tail */
    uint64_t rem = n & 63;              /* tail bytes; zero on a block boundary */
    uint64_t prevS = 0;                 /* the previous block's top scalar lane */
    S1F st = {0, 0, 0};                 /* block-local classifier carry */
    __m256i ascii = _mm256_setzero_si256();  /* every byte the document holds */
    __m256i u8k = _mm256_setzero_si256();    /* the accumulated UTF-8 error vector */
    int prev_ascii = 1;                 /* the preheader's `%prev_ascii = 1` */
    int ungated = (arm & 4) != 0;       /* bit 2: run the DFA on every block */
    const __m256i high = _mm256_set1_epi8((char)0x80);

    for (uint64_t i = 0; i < nfull; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        __m256i any = _mm256_or_si256(v0, v1);
        int blk_ascii = _mm256_testz_si256(any, high);
        ascii = _mm256_or_si256(ascii, any);
        uint64_t q, d, im, nn, bm;
        s1b_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
        if (ungated || !(blk_ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, s1b_kl_err_vec(v0, v1, p));
        prev_ascii = blk_ascii;
        if (arm & 2)
            leanllvm_json_escape_list(bm, s1b_ctl(v0, v1), im, i, xp, nxp, xcarry);
    }
    if (rem) {
        const uint8_t *p = b + (nfull << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        __m256i any = _mm256_or_si256(v0, v1);
        int blk_ascii = _mm256_testz_si256(any, high);
        ascii = _mm256_or_si256(ascii, any);
        uint64_t q, d, im, nn, bm;
        s1b_masks(v0, v1, &st, &q, &d, &im, &nn, &bm);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
        if (ungated || !(blk_ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, s1b_kl_err_vec(v0, v1, p));
        prev_ascii = blk_ascii;
        if (arm & 2)
            leanllvm_json_escape_list(bm, s1b_ctl(v0, v1), im, nfull, xp, nxp,
                                      xcarry);
    }
    /* The stage's document-end rule, then the two words the caller reads:
       the ASCII probe in bit 0 and the UTF-8 error in bit 1. */
    uint64_t err = (uint64_t)(_mm256_testz_si256(u8k, u8k) == 0);
    if (n != 0 && (n & 63) == 0)
        err |= (uint64_t)s1b_kl_tail_byte(b[n - 1]);
    uint64_t ascii_word =
        (uint64_t)(_mm256_testz_si256(ascii, high) != 0);
    return ascii_word | (err << 1);
}
