/* uj.c -- fused JSON string validate + unescape (scratch experiment).
   Nothing here belongs to the repository.

   One pass over a string body whose closing quote is already known:
     * 32 bytes at a time are copied to the destination while a single mask
       test rejects control bytes (< 0x20) and locates backslashes;
     * an escape is decoded by an out-of-line helper that returns the up to
       four encoded bytes, so the copy loop stays small and its entry does not
       spill callee-saved registers;
     * the last 32 (and then 8) bytes are covered by an overlapping vector
       load whenever no escape has shifted the output, which removes the
       byte-at-a-time tail for every string that is not tiny;
     * an optional byte checksum over the output is accumulated in the same
       pass (a vector accumulator, reduced once at the end).

   Escapes produce at most 4 bytes from 6 (or 12 for a surrogate pair), so the
   output is never longer than the input: the caller provides `n` bytes plus 32
   bytes of slack, because a copy may store a whole 32-byte vector past the
   output position (those bytes are later overwritten or lie beyond the
   returned length).

   Error offsets and surrogate handling match p6.c's str_process byte for byte
   (a lone surrogate is encoded as the 3-byte WTF-8 form of its code point). */
#include <stdint.h>
#include <string.h>
#include <immintrin.h>

#define UJ_FAIL ((size_t)-1)

static const int8_t UJ_UNESC[256] = {
    [0 ... 255] = -1,
    ['"'] = '"', ['\\'] = '\\', ['/'] = '/', ['b'] = 8,
    ['f'] = 12, ['n'] = 10, ['r'] = 13, ['t'] = 9
};

/* one load instead of a three-way compare chain per hex digit */
static const int8_t UJ_HEX[256] = {
    [0 ... 255] = -1,
    ['0'] = 0, ['1'] = 1, ['2'] = 2, ['3'] = 3, ['4'] = 4,
    ['5'] = 5, ['6'] = 6, ['7'] = 7, ['8'] = 8, ['9'] = 9,
    ['a'] = 10, ['b'] = 11, ['c'] = 12, ['d'] = 13, ['e'] = 14, ['f'] = 15,
    ['A'] = 10, ['B'] = 11, ['C'] = 12, ['D'] = 13, ['E'] = 14, ['F'] = 15
};

static inline int uj_hv(uint8_t c) { return UJ_HEX[c]; }

/* Encode cp (any value including a lone surrogate) into tmp[0..4); returns the
   length.  Identical to p6.c's put_utf8. */
static inline uint32_t uj_enc(uint8_t *tmp, uint32_t cp) {
    if (cp < 0x80) { tmp[0] = (uint8_t)cp; return 1; }
    if (cp < 0x800) {
        tmp[0] = (uint8_t)(0xC0 | (cp >> 6));
        tmp[1] = (uint8_t)(0x80 | (cp & 0x3F));
        return 2;
    }
    if (cp < 0x10000) {
        tmp[0] = (uint8_t)(0xE0 | (cp >> 12));
        tmp[1] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        tmp[2] = (uint8_t)(0x80 | (cp & 0x3F));
        return 3;
    }
    tmp[0] = (uint8_t)(0xF0 | (cp >> 18));
    tmp[1] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
    tmp[2] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
    tmp[3] = (uint8_t)(0x80 | (cp & 0x3F));
    return 4;
}

/* Decode the escape whose backslash is at p[*ip].  Writes the encoded bytes to
   enc[0..4) (always four bytes; only *elen of them belong to the output) and
   advances *ip past the escape.  Returns 0 on an invalid escape with *err set
   to the backslash offset, like str_process.  Out of line on purpose: it keeps
   the copy loop small and its caller's entry cheap. */
static __attribute__((noinline)) int
uj_esc(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *enc, uint32_t *elen,
       size_t *err) {
    uint64_t i = *ip;
    if (i + 1 >= n) { *err = (size_t)i; return 0; }
    uint8_t e = p[i + 1];
    int8_t uv = UJ_UNESC[e];
    if (uv >= 0) {
        enc[0] = (uint8_t)uv;
        *elen = 1;
        *ip = i + 2;
        return 1;
    }
    if (e != 'u') { *err = (size_t)i; return 0; }
    if (i + 6 > n) { *err = (size_t)i; return 0; }
    int h0 = uj_hv(p[i + 2]), h1 = uj_hv(p[i + 3]);
    int h2 = uj_hv(p[i + 4]), h3 = uj_hv(p[i + 5]);
    if (h0 < 0 || h1 < 0 || h2 < 0 || h3 < 0) { *err = (size_t)i; return 0; }
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    i += 6;
    if (cp >= 0xD800 && cp <= 0xDBFF && i + 6 <= n &&
        p[i] == '\\' && p[i + 1] == 'u') {
        int g0 = uj_hv(p[i + 2]), g1 = uj_hv(p[i + 3]);
        int g2 = uj_hv(p[i + 4]), g3 = uj_hv(p[i + 5]);
        if (g0 >= 0 && g1 >= 0 && g2 >= 0 && g3 >= 0) {
            uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                          ((uint32_t)g2 << 4) | (uint32_t)g3;
            if (lo >= 0xDC00 && lo <= 0xDFFF) {
                cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                i += 6;
            }
        }
    }
    *elen = uj_enc(enc, cp);
    *ip = i;
    return 1;
}

/* ---- escape step used by the copy loops -----------------------------------
   UJ_ESC_MODE 0: out-of-line uj_esc for everything (spike-12 behaviour)
   UJ_ESC_MODE 1: simple escapes decoded in line (one byte stored, no call)
   UJ_ESC_MODE 2: branch-free classifier and encoder for every escape
*/
#ifndef UJ_ESC_MODE
#define UJ_ESC_MODE 2
#endif

/* UTF-8 encoding of cp as a word whose low `len` bytes are the sequence in
   memory order; the bytes above len are zero, so a 4-byte store and a plain
   byte sum are both correct.  No branches: the four forms are computed and
   selected with conditional moves. */
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

static inline __attribute__((always_inline)) int
uj_esc_simple(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst,
              uint64_t *jp, uint64_t *acc, size_t *err) {
    uint64_t i = *ip;
    int8_t sv = (i + 1 < n) ? UJ_UNESC[p[i + 1]] : -1;
    if (sv >= 0) {
        if (dst) dst[*jp] = (uint8_t)sv;
        if (acc) *acc += (uint64_t)(uint8_t)sv;
        *jp += 1;
        *ip = i + 2;
        return 1;
    }
    uint8_t enc[8];
    uint32_t elen;
    if (!uj_esc(p, n, &i, enc, &elen, err)) return 0;
    if (dst) memcpy(dst + *jp, enc, 4);
    if (acc) for (uint32_t k = 0; k < elen; k++) *acc += enc[k];
    *jp += elen;
    *ip = i;
    return 1;
}

/* No data-dependent branch: the escape class, its validity, the code point and
   the 1..4-byte encoding are all computed for both classes and selected with
   conditional moves.  Needs 12 readable bytes past the backslash (the longest
   escape is a surrogate pair) and falls back otherwise. */
static inline __attribute__((always_inline)) int
uj_esc_bf(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst,
          uint64_t *jp, uint64_t *acc, size_t *err) {
    uint64_t i = *ip;
    if (i + 12 > n) return uj_esc_simple(p, n, ip, dst, jp, acc, err);
    uint64_t w; memcpy(&w, p + i, 8);
    unsigned e1 = (unsigned)((w >> 8) & 0xFFu);
    int8_t sv = UJ_UNESC[e1];
    int h0 = UJ_HEX[(w >> 16) & 0xFF], h1 = UJ_HEX[(w >> 24) & 0xFF];
    int h2 = UJ_HEX[(w >> 32) & 0xFF], h3 = UJ_HEX[(w >> 40) & 0xFF];
    int isU = (e1 == 'u');
    int hexok = (h0 | h1 | h2 | h3) >= 0;          /* all in [-1,15] */
    uint32_t cpU = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                   ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint32_t cp = (uint32_t)sv;
    if (isU) cp = cpU;
    if (!(isU ? hexok : sv >= 0)) { *err = (size_t)i; return 0; }
    uint64_t adv = isU ? 6 : 2;
    if (isU && (cp - 0xD800u) < 0x400u) {
        uint64_t w2; memcpy(&w2, p + i + 6, 8);
        unsigned e2v = (unsigned)((w2 >> 8) & 0xFFu);
        int g0 = UJ_HEX[(w2 >> 16) & 0xFF], g1 = UJ_HEX[(w2 >> 24) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 32) & 0xFF], g3 = UJ_HEX[(w2 >> 40) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((w2 & 0xFFu) == '\\' && e2v == 'u' && (g0 | g1 | g2 | g3) >= 0 &&
            (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv += 6;
        }
    }
    int len;
    uint32_t v = uj_enc_word(cp, &len);
    if (dst) memcpy(dst + *jp, &v, 4);
    if (acc) *acc += (v & 0xFF) + ((v >> 8) & 0xFF) + ((v >> 16) & 0xFF) +
                      ((v >> 24) & 0xFF);
    *jp += (uint64_t)len;
    *ip = i + adv;
    return 1;
}

/* Mode 3: simple escapes in line (one byte, no call) and the \u form decoded
   with the same branch-free encoder, so a document that mixes \" with \uXXXX
   does not mispredict the class on every escape. */
static inline __attribute__((always_inline)) int
uj_esc_u(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst,
         uint64_t *jp, uint64_t *acc, size_t *err) {
    uint64_t i = *ip;
    int8_t sv = (i + 1 < n) ? UJ_UNESC[p[i + 1]] : -1;
    if (sv >= 0) {
        if (dst) dst[*jp] = (uint8_t)sv;
        if (acc) *acc += (uint64_t)(uint8_t)sv;
        *jp += 1;
        *ip = i + 2;
        return 1;
    }
    if (i + 1 >= n || p[i + 1] != 'u') return uj_esc_simple(p, n, ip, dst, jp, acc, err);
    if (i + 6 > n) { *err = (size_t)i; return 0; }
    int h0 = uj_hv(p[i + 2]), h1 = uj_hv(p[i + 3]);
    int h2 = uj_hv(p[i + 4]), h3 = uj_hv(p[i + 5]);
    if ((h0 | h1 | h2 | h3) < 0) { *err = (size_t)i; return 0; }
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        int g0 = uj_hv(p[i + 8]), g1 = uj_hv(p[i + 9]);
        int g2 = uj_hv(p[i + 10]), g3 = uj_hv(p[i + 11]);
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv += 6;
        }
    }
    int len;
    uint32_t v = uj_enc_word(cp, &len);
    if (dst) memcpy(dst + *jp, &v, 4);
    if (acc) *acc += (v & 0xFF) + ((v >> 8) & 0xFF) + ((v >> 16) & 0xFF) +
                      ((v >> 24) & 0xFF);
    *jp += (uint64_t)len;
    *ip = i + adv;
    return 1;
}


/* Mode 4's class table: one u64 per byte that can follow a backslash.
     bits  0..31 : the simple class's output word (decoded byte in byte 0)
     bits 32..39 : the simple class's output length
     bits 40..47 : the advance (2 for a simple escape, 6 for \u)
     bit  48     : set for \u       (selected with a mask, not a branch)
     bit  49     : set for an invalid escape */
#define UJ_LEN1  (1ULL << 32)
#define UJ_ADV2  (2ULL << 40)
#define UJ_ADV6  (6ULL << 40)
#define UJ_ISU   (1ULL << 48)
#define UJ_BADESC (1ULL << 49)
static const uint64_t UJ_ESC4[256] = {
    [0 ... 255] = UJ_BADESC,
    ['"'] = 0x22 | UJ_LEN1 | UJ_ADV2,
    ['\\'] = 0x5C | UJ_LEN1 | UJ_ADV2,
    ['/'] = 0x2F | UJ_LEN1 | UJ_ADV2,
    ['b'] = 0x08 | UJ_LEN1 | UJ_ADV2,
    ['f'] = 0x0C | UJ_LEN1 | UJ_ADV2,
    ['n'] = 0x0A | UJ_LEN1 | UJ_ADV2,
    ['r'] = 0x0D | UJ_LEN1 | UJ_ADV2,
    ['t'] = 0x09 | UJ_LEN1 | UJ_ADV2,
    ['u'] = UJ_ISU | UJ_ADV6,
};

/* Mode 4: table-driven escape expansion.  Both classes are computed, the
   table selects the simple one, and the escape always ends with a single
   8-byte store, so the store shape and the advance do not depend on which
   class the escape turned out to be.  Needs 12 readable bytes past the
   backslash (a surrogate pair is the longest escape) and falls back at the
   end of the body, where the out-of-line decoder keeps the byte-exact
   behaviour. */
static inline __attribute__((always_inline)) int
uj_esc_tab(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst,
           uint64_t *jp, uint64_t *acc, size_t *err) {
    uint64_t i = *ip;
    if (i + 12 > n) return uj_esc_simple(p, n, ip, dst, jp, acc, err);
    uint64_t w; memcpy(&w, p + i + 1, 8);            /* c1 c2 c3 c4 c5 c6 c7 c8 */
    unsigned c1 = (unsigned)(w & 0xFFu);
    uint64_t t = UJ_ESC4[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cpU = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                   ((uint32_t)h2 << 4) | (uint32_t)h3;
    int ulen;
    uint32_t uw = uj_enc_word(cpU, &ulen);           /* computed for every escape */
    uint64_t isu = t & UJ_ISU;
    uint32_t word = isu ? uw : (uint32_t)t;
    uint64_t len = isu ? (uint64_t)ulen : ((t >> 32) & 0xFFu);
    uint64_t adv = isu ? 6u : ((t >> 40) & 0xFFu);
    if (t & UJ_BADESC) { *err = (size_t)i; return 0; }
    if (isu && ((h0 | h1 | h2 | h3) < 0)) { *err = (size_t)i; return 0; }
    /* a high surrogate is a value test, not a class test */
    if (isu && (cpU - 0xD800u) < 0x400u && i + 12 <= n) {
        uint64_t w2; memcpy(&w2, p + i + 6, 8);
        int g0 = UJ_HEX[(w2 >> 16) & 0xFF], g1 = UJ_HEX[(w2 >> 24) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 32) & 0xFF], g3 = UJ_HEX[(w2 >> 40) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((w2 & 0xFFu) == '\\' && ((w2 >> 8) & 0xFFu) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cpU = 0x10000u + ((cpU - 0xD800u) << 10) + (lo - 0xDC00u);
            uw = uj_enc_word(cpU, &ulen);
            word = uw;
            len = (uint64_t)ulen;
            adv += 6;
        }
    }
    if (dst) {
        uint64_t out = (uint64_t)word;               /* one 8-byte store */
        memcpy(dst + *jp, &out, 8);
    }
    if (acc) *acc += (word & 0xFF) + ((word >> 8) & 0xFF) +
                     ((word >> 16) & 0xFF) + ((word >> 24) & 0xFF);
    *jp += len;
    *ip = i + adv;
    return 1;
}

static inline __attribute__((always_inline)) int
uj_esc_step(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst,
            uint64_t *jp, uint64_t *acc, size_t *err) {
#if UJ_ESC_MODE == 4
    return uj_esc_tab(p, n, ip, dst, jp, acc, err);
#elif UJ_ESC_MODE == 3
    return uj_esc_u(p, n, ip, dst, jp, acc, err);
#elif UJ_ESC_MODE == 2
    return uj_esc_bf(p, n, ip, dst, jp, acc, err);
#elif UJ_ESC_MODE == 1
    return uj_esc_simple(p, n, ip, dst, jp, acc, err);
#else
    uint8_t enc[8];
    uint32_t elen;
    if (!uj_esc(p, n, ip, enc, &elen, err)) return 0;
    if (dst) memcpy(dst + *jp, enc, 4);
    if (acc) for (uint32_t k = 0; k < elen; k++) *acc += enc[k];
    *jp += elen;
    return 1;
#endif
}

static inline __m256i uj_add32(__m256i accv, __m256i v) {
    return _mm256_add_epi64(accv, _mm256_sad_epu8(v, _mm256_setzero_si256()));
}

static inline uint64_t uj_hsum256(__m256i v) {
    __m128i lo = _mm256_castsi256_si128(v);
    __m128i hi = _mm256_extracti128_si256(v, 1);
    __m128i s = _mm_add_epi64(lo, hi);
    return (uint64_t)_mm_cvtsi128_si64(s) + (uint64_t)_mm_extract_epi64(s, 1);
}

static inline int uj_mask(__m256i v, __m256i vbs, __m256i v19) {
    __m256i ctl = _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v);
    __m256i bsl = _mm256_cmpeq_epi8(v, vbs);
    return _mm256_movemask_epi8(_mm256_or_si256(ctl, bsl));
}

/* Bytes below index n are 0xFF, the rest 0x00 (n <= 32).  Used to keep the
   checksum limited to the bytes that are really part of the body when a
   32-byte store covers a shorter string. */
static inline __m256i uj_keep(unsigned n) {
    const __m256i idx = _mm256_setr_epi8(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
                                         12, 13, 14, 15, 16, 17, 18, 19, 20, 21,
                                         22, 23, 24, 25, 26, 27, 28, 29, 30, 31);
    return _mm256_cmpgt_epi8(_mm256_set1_epi8((char)n), idx);
}

/* Short strings (n < 32) are the majority and the generic path spends most of
   its time on length-dependent branches.  One masked 32-byte load decides
   "clean" in a handful of instructions; an escaping body walks the same
   window.  Requires 32 readable bytes at p (the caller's input is padded for
   the stage-1 block reads anyway). */
#ifndef UJ_SHORT
#define UJ_SHORT 1
#endif
#if UJ_SHORT
static __attribute__((always_inline)) inline size_t
uj_short(const uint8_t *p, uint64_t n, uint8_t *dst, uint64_t *acc,
         size_t *err, const int want_acc, __m256i av,
         const __m256i vbs, const __m256i v19) {
    uint64_t i = 0, j = 0;
    unsigned keep = (n >= 32) ? 0xFFFFFFFFu : ((1u << n) - 1u);
    __m256i v = _mm256_loadu_si256((const __m256i *)(p));
    unsigned m = (unsigned)uj_mask(v, vbs, v19) & keep;
    if (!m) {
        if (dst) _mm256_storeu_si256((__m256i *)(dst), v);
        if (want_acc) av = uj_add32(av, _mm256_and_si256(v, uj_keep((unsigned)n)));
        j = n;
        goto done;
    }
    for (;;) {
        unsigned b = (unsigned)__builtin_ctz(m);
        if (b) {
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc) av = uj_add32(av, _mm256_and_si256(v, uj_keep(b)));
            i += b; j += b;
        }
        if (p[i] < 0x20) { *err = (size_t)i; return UJ_FAIL; }
        if (!uj_esc_step(p, n, &i, dst, &j, want_acc ? acc : NULL, err))
            return UJ_FAIL;
        if (i >= n) break;
        v = _mm256_loadu_si256((const __m256i *)(p + i));
        m = (unsigned)uj_mask(v, vbs, v19) &
            ((n - i >= 32) ? 0xFFFFFFFFu : ((1u << (n - i)) - 1u));
        if (!m) {
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc)
                av = uj_add32(av, _mm256_and_si256(v, uj_keep((unsigned)(n - i))));
            j += n - i;
            i = n;
            break;
        }
    }
done:
    if (want_acc) *acc += uj_hsum256(av);
    return (size_t)j;
}
#endif

static __attribute__((always_inline)) inline size_t
uj_core(const uint8_t *p, uint64_t n, uint8_t *dst, uint64_t *acc,
        size_t *err, const int want_acc) {
    uint64_t i = 0, j = 0;
    __m256i av = _mm256_setzero_si256();
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);

#ifndef UJ_SHORT
#define UJ_SHORT 1
#endif
#if UJ_SHORT
    if (n < 32) return uj_short(p, n, dst, acc, err, want_acc, av, vbs, v19);
#endif

    while (i + 32 <= n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        int m = uj_mask(v, vbs, v19);
        if (m == 0) {
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc) av = uj_add32(av, v);
            i += 32; j += 32;
            continue;
        }
        int b = __builtin_ctz((unsigned)m);
        if (b) {
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc) av = uj_add32(av, v);
            i += (uint64_t)b; j += (uint64_t)b;
        }
        if (p[i] < 0x20) { *err = (size_t)i; return UJ_FAIL; }
        if (!uj_esc_step(p, n, &i, dst, &j, want_acc ? acc : NULL, err))
            return UJ_FAIL;
    }
    if (i < n) {
        /* An overlapping vector covers the tail when no escape has shifted the
           output (then dst[0..j) == p[0..i) and the overlap re-writes identical
           bytes).  Otherwise the chunks below finish the string. */
        if (n >= 32 && j == i) {
            __m256i v = _mm256_loadu_si256((const __m256i *)(p + n - 32));
            int m = uj_mask(v, vbs, v19);
            if (m == 0) {
                if (dst) _mm256_storeu_si256((__m256i *)(dst + n - 32), v);
                if (want_acc) av = uj_add32(av, v);
                i = n; j = n;
            }
        }
        while (i + 8 <= n) {
            uint64_t w;
            memcpy(&w, p + i, 8);
            uint64_t x = w ^ 0x5C5C5C5C5C5C5C5CULL;
            uint64_t bs = (x - 0x0101010101010101ULL) & ~x & 0x8080808080808080ULL;
            uint64_t lt = (w - 0x2020202020202020ULL) & ~w & 0x8080808080808080ULL;
            uint64_t mm = bs | lt;
            if (!mm) {
                if (dst) memcpy(dst + j, &w, 8);
                if (want_acc) av = uj_add32(av, _mm256_set1_epi64x((long long)w));
                i += 8; j += 8;
                continue;
            }
            uint64_t b = (uint64_t)(__builtin_ctzll(mm) >> 3);
            if (b) {
                if (dst) memcpy(dst + j, p + i, b);
                if (want_acc) {
                    uint64_t s = 0;
                    for (uint64_t k = 0; k < b; k++) s += p[i + k];
                    *acc += s;
                }
                i += b; j += b;
            }
            if (p[i] < 0x20) { *err = (size_t)i; return UJ_FAIL; }
            if (!uj_esc_step(p, n, &i, dst, &j, want_acc ? acc : NULL, err))
                return UJ_FAIL;
        }
        /* the last fewer-than-eight bytes, re-read with an overlapping load */
        if (i < n && j == i && n >= 8) {
            uint64_t w;
            memcpy(&w, p + n - 8, 8);
            uint64_t x = w ^ 0x5C5C5C5C5C5C5C5CULL;
            uint64_t bs = (x - 0x0101010101010101ULL) & ~x & 0x8080808080808080ULL;
            uint64_t lt = (w - 0x2020202020202020ULL) & ~w & 0x8080808080808080ULL;
            if (!(bs | lt)) {
                if (dst) memcpy(dst + n - 8, &w, 8);
                if (want_acc) av = uj_add32(av, _mm256_set1_epi64x((long long)w));
                i = n; j = n;
            }
        }
        while (i < n) {
            uint8_t c = p[i];
            if (c < 0x20) { *err = (size_t)i; return UJ_FAIL; }
            if (c == '\\') {
                if (!uj_esc_step(p, n, &i, dst, &j, want_acc ? acc : NULL, err))
                    return UJ_FAIL;
                continue;
            }
            if (dst) dst[j] = c;
            if (want_acc) av = uj_add32(av, _mm256_set1_epi8((char)c));
            i++; j++;
        }
    }
    if (want_acc) *acc += uj_hsum256(av);
    return (size_t)j;
}

/* dst must hold n bytes plus 32 bytes of slack. */
size_t uj_decode(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err) {
    return uj_core(p, n, dst, NULL, err, 0);
}

/* Same, accumulating a byte checksum of the decoded output into *acc. */
size_t uj_decode_acc(const uint8_t *p, uint64_t n, uint8_t *dst, uint64_t *acc,
                     size_t *err) {
    return uj_core(p, n, dst, acc, err, 1);
}

/* Decode two consecutive string bodies with one call: the walk knows both
   spans from the index stream, so the second body follows the first.  Both are
   written to dst (the second at dst + first length).  Returns the combined
   length, or UJ_FAIL with *which = 0/1 and *err an offset inside that body. */
size_t uj_decode_acc2(const uint8_t *p1, uint64_t n1, const uint8_t *p2,
                      uint64_t n2, uint8_t *dst, uint64_t *acc, size_t *err,
                      int *which) {
    size_t e = 0;
    size_t o1 = uj_core(p1, n1, dst, acc, &e, 1);
    if (o1 == UJ_FAIL) { *err = e; *which = 0; return UJ_FAIL; }
    size_t o2 = uj_core(p2, n2, dst + o1, acc, &e, 1);
    if (o2 == UJ_FAIL) { *err = e; *which = 1; return UJ_FAIL; }
    *which = 0;
    return o1 + o2;
}
