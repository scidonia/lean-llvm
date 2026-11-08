/* escape.c -- the escape-position list and the list-driven escape expander:
   the two measured stages M4 states as one unit.

   The list is `xlist.h`'s `xl_lanes` and `xl_emit` at the measured `XL_EMIT=1`
   (`s1fuse.h:70-71`, selected by `S1F_XS=5`): the per-block gate in front of
   spike 38's eight-entry batch.  `xl_lanes`'s masks are the classifier's
   words, so the unit takes them through its ABI and does not recompute what
   the mask unit produces.  The expander is `usdec.h`'s `us_dec_x` with its
   kernels, at the measured `US_EMIT4=1` arm and the defaults the header gives
   every other switch; `UJ_UNESC` and `uj_enc_word` are `uj.c`'s, which is the
   measured chain's include and the only definition site.

   The arms the measured configuration does not take are deleted rather than
   kept behind a macro: this is the measured text, not a transcription of two
   configurations.  README.md's `escape-delete:` rows are the deletions the
   token arm applies to the measured side; the unit carries their result, so
   the two sides' tokens are the selected text.  What remains is exactly the
   code the measured build compiles.

   The two ABI functions at the end are the unit's only new definitions.  The
   rest of the new text is the decoder's `US_XP_DIAG` default, the includes,
   and the two attribute selectors the deleted conditional blocks left outside
   the extracted spans (the inline `us_esc_u` and the `noinline` `us_dec_x`).
   The ABI functions hoist the measured signatures without bundling
   parameters, renaming a token inside the bodies, or adding a result channel.
   `us_dec_x` keeps its measured name and signature, so the emitted-code arm
   lifts it by name from both sides. */
#include "escape.h"

#include <immintrin.h>
#include <stdint.h>
#include <string.h>

/* --------------------------------------------------- escape-position list -- */
/* `s1f_lanes_im` (`s1fuse.h:218`), the mask unit's caller of this function,
   is not copied by this unit: its `SP_MODES`/`S1F_XS_NOIM` early-return
   selector stays in the measured header and is outside this unit's deletion
   list. */
static inline uint64_t xl_lanes(uint64_t bs, uint64_t ctl, uint64_t im,
                                uint64_t *pb, uint64_t *ps) {
    uint64_t prevb = *pb, prevs = *ps;
    uint64_t starts = bs & ~((bs << 1) | prevb);
    uint64_t e = starts;
    if ((bs & 1) & prevb)
        e |= prevs ? (bs & 2) : 1;
    {
        uint64_t cont = bs & (bs << 1);
        e |= (e << 2) & cont;
        e |= (e << 2) & cont;
        /* A run longer than five backslashes finishes here.  Only enter when
           the step would add a bit that is not already in `e`: the bare
           `(e << 2) & cont` is non-zero on every run of three, all of whose
           lanes the two straight-line steps have already produced. */
        if (__builtin_expect((((e << 2) & cont) & ~e) != 0, 0)) {
            uint64_t old;
            do {
                old = e;
                e |= (e << 2) & cont;
            } while (e != old);
        }
    }
    *pb = bs >> 63;
    *ps = (e >> 63) & (bs >> 63);
    return (ctl | e) & im;
}

/* One fixed batch of eight positions (the mask may hold more; the caller's
   tail handles that).  Returns the number of real entries. */
static inline unsigned xl_batch(uint64_t esc, uint32_t base, uint32_t *o) {
    uint64_t c = esc | 0x8000000000000000ULL;   /* keeps ctz defined */
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    {
        unsigned n = (unsigned)__builtin_popcountll(esc);
        return n > 8 ? 8 : n;
    }
}

/* Append the escape positions of one 64-byte block.  With XL_EMIT=0 this is
   spike 38's shape: one straight-line batch of eight, then (only for a block
   that holds more than eight lanes) further batches of eight. */
static inline void xl_emit_batch(uint64_t esc, uint32_t base, uint32_t *out,
                                 uint64_t *k) {
    uint32_t *o = out + *k;
    unsigned n = xl_batch(esc, base, o);
    *k += n;
    if (__builtin_expect(__builtin_popcountll(esc) > 8, 0)) {
        uint64_t c = esc;
        for (unsigned t = 0; t < 8; t++) c &= c - 1;
        o += 8;
        while (c) {
            unsigned b = xl_batch(c, base, o);
            o += b;
            *k += b;
            for (unsigned t = 0; t < 8; t++) c &= c - 1;
        }
    }
}

static inline void xl_emit(uint64_t esc, uint32_t base, uint32_t *out,
                           uint64_t *k) {
    if (!esc) return;                       /* per-block gate */
    xl_emit_batch(esc, base, out, k);
}

/* ------------------------------------------------ list-driven expander -- */
/* `UJ_UNESC`, the simple-escape map, and `uj_enc_word`, the branch-free
   encoder, are `uj.c`'s definitions; the measured chain supplies them through
   `p16.c:57` and the unit carries the copies the identity list names. */
static const int8_t UJ_UNESC[256] = {
    [0 ... 255] = -1,
    ['"'] = '"', ['\\'] = '\\', ['/'] = '/', ['b'] = 8,
    ['f'] = 12, ['n'] = 10, ['r'] = 13, ['t'] = 9
};

/* Encode cp (any value including a lone surrogate) into a 4-byte word and set
   its length.  The four forms are computed and selected with conditional
   moves.  No branches: the four forms are computed and selected with
   conditional moves. */
static inline __attribute__((always_inline)) uint32_t
uj_enc_word(uint32_t cp, int *lenp) {
    uint32_t v2 = (0xC0u | (cp >> 6)) | ((0x80u | (cp & 0x3F)) << 8);
    uint32_t v3 = (0xE0u | (cp >> 12)) |
                  ((0x80u | ((cp >> 6) & 0x3F)) << 8) |
                  ((0x80u | (cp & 0x3F)) << 16);
    uint32_t v4 = (0xF0u | (cp >> 18)) |
                  ((0x80u | ((cp >> 12) & 0x3F)) << 8) |
                  ((0x80u | ((cp >> 6) & 0x3F)) << 16) |
                  ((0x80u | (cp & 0x3F)) << 24);
    int g2 = cp >= 0x80u, g3 = cp >= 0x800u, g4 = cp >= 0x10000u;
    uint32_t v = cp;
    v = g2 ? v2 : v;
    v = g3 ? v3 : v;
    v = g4 ? v4 : v;
    *lenp = 1 + g2 + g3 + g4;
    return v;
}

/* Four hex digits validated and combined with one 16-byte load: the digit
   value is the low nibble plus nine for a letter, and the class test is
   (byte-'0' <= 9) | ((byte|0x20)-'a' <= 5).  Only the first four lanes
   decide the result; the rest of the vector is read past the digits and
   ignored. */
static inline __attribute__((always_inline)) int
us_hex4_pshufb(const uint8_t *q, uint32_t *out) {
    __m128i v = _mm_loadu_si128((const __m128i *)q);
    __m128i d = _mm_sub_epi8(v, _mm_set1_epi8('0'));
    __m128i a = _mm_sub_epi8(_mm_or_si128(v, _mm_set1_epi8(0x20)),
                             _mm_set1_epi8('a'));
    __m128i isd = _mm_cmpeq_epi8(_mm_subs_epu8(d, _mm_set1_epi8(9)),
                                 _mm_setzero_si128());
    __m128i isa = _mm_cmpeq_epi8(_mm_subs_epu8(a, _mm_set1_epi8(5)),
                                 _mm_setzero_si128());
    if (((unsigned)_mm_movemask_epi8(_mm_or_si128(isd, isa)) & 0x0Fu) != 0x0Fu)
        return 0;
    __m128i lo = _mm_and_si128(v, _mm_set1_epi8(0x0F));
    __m128i val = _mm_add_epi8(lo, _mm_and_si128(isa, _mm_set1_epi8(9)));
    __m128i m1 = _mm_maddubs_epi16(val, _mm_set1_epi16(0x0110));   /* hi*16+lo */
    __m128i m2 = _mm_madd_epi16(m1, _mm_set1_epi32(0x00010100));   /* <<8, +  */
    *out = (uint32_t)_mm_cvtsi128_si32(m2) & 0xFFFF;
    return 1;
}

static inline __attribute__((always_inline)) int
us_hex4(const uint8_t *q, uint32_t *out) {
    return us_hex4_pshufb(q, out);
}

/* ---- escape step ---------------------------------------------------------
   p[i] is a backslash, i < n.  On success writes the decoded bytes at dst[j],
   advances *jp and sets *advp to the number of input bytes consumed.  On
   failure sets *err = i (the reference's offset) and returns 0. */
static inline __attribute__((always_inline)) void
us_emit(uint32_t cp, uint8_t *dst, uint64_t *jp) {
    int len;
    uint32_t w = uj_enc_word(cp, &len);
    memcpy(dst + *jp, &w, 4);
    *jp += (uint64_t)len;
}

static inline __attribute__((always_inline)) int
us_esc_u(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
         uint64_t *advp, uint64_t *err) {
    if (i + 6 > n) { *err = i; return 0; }
    uint32_t cp;
    if (!us_hex4(p + i + 2, &cp)) { *err = i; return 0; }
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        uint32_t lo;
        if (us_hex4(p + i + 8, &lo) && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
        }
    }
    us_emit(cp, dst, jp);
    *advp = adv;
    return 1;
}

static inline __attribute__((always_inline)) int
us_esc(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
       uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    unsigned c1 = p[i + 1];
    int8_t sv = UJ_UNESC[c1];
    if (sv >= 0) {
        dst[*jp] = (uint8_t)sv;
        *jp += 1;
        *advp = 2;
        return 1;
    }
    if (c1 != 'u') { *err = i; return 0; }
    return us_esc_u(p, n, i, dst, jp, advp, err);
}

/* run store: whole vectors, over-writing up to 31 bytes past the run (the
   caller's slack and the next store make that harmless).  len <= win <= 64.

   US_RUN2 stores both vectors always: the second store's load address is
   selected instead of branching on len, so the single data-dependent branch in
   the run copy disappears (the load is always inside the vector just read). */
static inline __attribute__((always_inline)) void
us_run(const uint8_t *p, uint8_t *dst, uint64_t len) {
    _mm256_storeu_si256((__m256i *)dst, _mm256_loadu_si256((const __m256i *)p));
    if (len > 32)
        _mm256_storeu_si256((__m256i *)(dst + 32),
                            _mm256_loadu_si256((const __m256i *)(p + 32)));
}

/* copy a run of any length: exact 64-byte chunks while more than a window is
   left, then the vector store that over-writes forward */
static inline __attribute__((always_inline)) void
us_run_long(const uint8_t *p, uint8_t *dst, uint64_t len) {
    uint64_t k = 0;
    while (len - k > 64) {
        _mm256_storeu_si256((__m256i *)(dst + k),
                            _mm256_loadu_si256((const __m256i *)(p + k)));
        _mm256_storeu_si256((__m256i *)(dst + k + 32),
                            _mm256_loadu_si256((const __m256i *)(p + k + 32)));
        k += 64;
    }
    us_run(p + k, dst + k, len - k);
}

/* The measured default of the decoder's diagnostic switch (`usdec.h:821-822`).
   The kept arm tests it, so its value is part of the configuration rather than
   a reading of the header: 0 is the branch the measured build compiles. */
#ifndef US_XP_DIAG
#define US_XP_DIAG 0
#endif

#define US_FAIL ((size_t)-1)

/* out of line in every build: the floor probe must pay the same call as the
   real consumer, otherwise the DIAG=6 binary inlines the copy and the
   consumption figure prices a call that the real path still pays */
__attribute__((noinline)) static size_t
us_dec_x(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
         const uint32_t *xp, uint64_t *xj, uint64_t nxp, uint64_t pos0) {
    uint64_t k = *xj, i = 0, j = 0;
    uint64_t endp = pos0 + n;
    while (k < nxp && (uint64_t)xp[k] < pos0) k++;
    while (k < nxp) {
        uint64_t q = (uint64_t)xp[k];
        if (q >= endp) break;
        k++;
        {
            uint64_t b = q - pos0;
            us_run_long(p + i, dst + j, b - i);
            j += b - i;
            if (US_XP_DIAG != 1 && p[b] < 0x20) {
                *err = (size_t)b; *xj = k; return US_FAIL;
            }
            {
                uint64_t adv;
                if (!us_esc(p, n, b, dst, &j, &adv, err)) {
                    *xj = k;
                    return US_FAIL;
                }
                i = b + adv;
                /* A decoded escape consumes at most one further position: the
                   second `\u` of a surrogate pair, which is exactly the
                   adv == 12 case.  The companion of `\\` never reaches the
                   list. */
                k += (adv == 12);
            }
        }
    }
    us_run_long(p + i, dst + j, n - i);
    *xj = k;
    return (size_t)(j + (n - i));
}

/* ------------------------------------------------------------------- ABI -- */
void leanllvm_json_escape_list(uint64_t bs, uint64_t ctl, uint64_t im,
                               uint64_t blk0, uint32_t *xp,
                               uint64_t *xn, uint64_t *carry) {
    uint64_t esc = xl_lanes(bs, ctl, im, &carry[0], &carry[1]);
    xl_emit(esc, (uint32_t)(blk0 << 6), xp, xn);
}

uint64_t leanllvm_json_escape_expand(const uint8_t *b, uint64_t n, uint8_t *dst,
                                     uint64_t *err, const uint32_t *xp,
                                     uint64_t *xj, uint64_t nxp, uint64_t pos0) {
    return (uint64_t)us_dec_x(b, n, dst, (size_t *)err, xp, xj, nxp, pos0);
}
