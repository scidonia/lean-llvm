/* zf.c -- one fused pass over a JSON string body.  Scratch experiment;
   nothing here belongs to the repository.

   The shipped OFF path validates a body with z_scan (a SIMD window that finds
   the first control byte or backslash) and then, when that first special is a
   backslash, restarts a second traversal from offset 0 in wm_escape_ok, which
   re-enters z_scan after every escape.  The shipped FULL path likewise scans
   the body once to classify it and then hands the whole body to ze_decode /
   uj_decode, which scans it again.

   This kernel does the whole body in one traversal and uses it for both
   contracts:
     * control bytes below 0x20 are rejected at their own offset;
     * every escape is validated (simple set, \u hex, surrogate pairing);
     * an invalid escape is reported at its backslash, an invalid low surrogate
       leaves the second \u to fail at its own backslash;
     * with ZF_COPY the decoded bytes are written in the same traversal, so a
       materialising consumer pays no second pass.  Runs between escapes are
       copied as whole vectors; the bytes past the run are rewritten by the
       next store or lie past the returned length, which is why dst needs
       32 bytes of slack.
   The scan window is ZF_W bytes (32 or 64), loaded once and consumed as one
   mask, so an escape costs its expansion instead of a reload and a re-mask.

   Accept/reject, error offset, decoded length and decoded bytes are identical
   to ze_decode/uj_decode; zb.c checks that differentially. */
#ifndef ZF_H
#define ZF_H

#include <immintrin.h>

/* Validate the escape whose backslash is at p[i].  *advp is the number of
   input bytes consumed.  Returns 0 with *err = i for every malformed form. */
static inline __attribute__((always_inline)) int
zf_esc_val(const uint8_t *p, uint64_t n, uint64_t i, uint64_t *advp,
           uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint8_t c1 = p[i + 1];
    if (UJ_UNESC[c1] >= 0) { *advp = 2; return 1; }
    if (c1 != 'u' || i + 6 > n) { *err = i; return 0; }
    int h0 = UJ_HEX[p[i + 2]], h1 = UJ_HEX[p[i + 3]];
    int h2 = UJ_HEX[p[i + 4]], h3 = UJ_HEX[p[i + 5]];
    if ((h0 | h1 | h2 | h3) < 0) { *err = i; return 0; }
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        int g0 = UJ_HEX[p[i + 8]], g1 = UJ_HEX[p[i + 9]];
        int g2 = UJ_HEX[p[i + 10]], g3 = UJ_HEX[p[i + 11]];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) adv = 12;
    }
    *advp = adv;
    return 1;
}

/* Same, writing the decoded bytes at dst[*jp].  Writes one 8-byte word for
   the \u form, so dst needs 8 bytes of room past the output cursor. */
static inline __attribute__((always_inline)) int
zf_esc_cp(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
          uint64_t *jp, uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint8_t c1 = p[i + 1];
    int8_t sv = UJ_UNESC[c1];
    if (sv >= 0) {
        dst[*jp] = (uint8_t)sv;
        *jp += 1;
        *advp = 2;
        return 1;
    }
    if (c1 != 'u' || i + 6 > n) { *err = i; return 0; }
    int h0 = UJ_HEX[p[i + 2]], h1 = UJ_HEX[p[i + 3]];
    int h2 = UJ_HEX[p[i + 4]], h3 = UJ_HEX[p[i + 5]];
    if ((h0 | h1 | h2 | h3) < 0) { *err = i; return 0; }
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        int g0 = UJ_HEX[p[i + 8]], g1 = UJ_HEX[p[i + 9]];
        int g2 = UJ_HEX[p[i + 10]], g3 = UJ_HEX[p[i + 11]];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
        }
    }
    int len;
    uint32_t word = uj_enc_word(cp, &len);
    {
        uint64_t w = (uint64_t)word;
        memcpy(dst + *jp, &w, 8);
    }
    *jp += (uint64_t)len;
    *advp = adv;
    return 1;
}

/* Same validation, counting the decoded length instead of writing.  Used by
   the length-only consumer: a body with escapes needs its decoded length, but
   not the bytes. */
static inline __attribute__((always_inline)) int
zf_esc_cnt(const uint8_t *p, uint64_t n, uint64_t i, uint64_t *jp,
           uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint8_t c1 = p[i + 1];
    int8_t sv = UJ_UNESC[c1];
    if (sv >= 0) { *jp += 1; *advp = 2; return 1; }
    if (c1 != 'u' || i + 6 > n) { *err = i; return 0; }
    int h0 = UJ_HEX[p[i + 2]], h1 = UJ_HEX[p[i + 3]];
    int h2 = UJ_HEX[p[i + 4]], h3 = UJ_HEX[p[i + 5]];
    if ((h0 | h1 | h2 | h3) < 0) { *err = i; return 0; }
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        int g0 = UJ_HEX[p[i + 8]], g1 = UJ_HEX[p[i + 9]];
        int g2 = UJ_HEX[p[i + 10]], g3 = UJ_HEX[p[i + 11]];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
        }
    }
    int len;
    (void)uj_enc_word(cp, &len);
    *jp += (uint64_t)len;
    *advp = adv;
    return 1;
}

/* ---- branch-free escape steps -------------------------------------------
   The escape class in a mixed document is unpredictable (canonical carries
   \\u, \\\\, \\t, \\/, \\n and \\" in near-equal numbers), so the class test, the
   hex test and the encoding are all computed for both classes and selected
   with conditional moves.  The surrogate-pair step is a value test on the
   first code point, so it leaves the common path as one predicted branch.
   Both read at most 8 bytes from p+i+1; the pair step reads p+i+4..p+i+11 and
   is taken only when i+12 <= n, so nothing past the body decides a result.
   The short tail falls back to the byte-exact branchy step. */

static inline __attribute__((always_inline)) int
zf_esc_bf_val(const uint8_t *p, uint64_t n, uint64_t i, uint64_t *advp,
              uint64_t *err) {
    if (i + 9 > n) return zf_esc_val(p, n, i, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);                    /* c1 c2 c3 c4 c5 c6 c7 c8 */
    unsigned c1 = (unsigned)(w & 0xFFu);
    int isu = (c1 == 'u');
    int8_t sv = UJ_UNESC[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int bad = isu ? ((h0 | h1 | h2 | h3) < 0) : (sv < 0);
    uint64_t adv = isu ? 6u : 2u;
    if (isu && (cp - 0xD800u) < 0x400u && i + 12 <= n) {
        uint64_t w2;                             /* p[i+4] .. p[i+11] */
        memcpy(&w2, p + i + 4, 8);
        int g0 = UJ_HEX[(w2 >> 32) & 0xFF], g1 = UJ_HEX[(w2 >> 40) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 48) & 0xFF], g3 = UJ_HEX[(w2 >> 56) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if (((w2 >> 16) & 0xFF) == '\\' && ((w2 >> 24) & 0xFF) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u)
            adv = 12;
    }
    if (bad) { *err = i; return 0; }
    *advp = adv;
    return 1;
}

/* The same for the materialising pass: the encoded word and its length are
   both computed, only the selected one is stored. */
static inline __attribute__((always_inline)) int
zf_esc_bf_cp(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
             uint64_t *jp, uint64_t *advp, uint64_t *err) {
    if (i + 9 > n) return zf_esc_cp(p, n, i, dst, jp, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);
    unsigned c1 = (unsigned)(w & 0xFFu);
    int isu = (c1 == 'u');
    int8_t sv = UJ_UNESC[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int bad = isu ? ((h0 | h1 | h2 | h3) < 0) : (sv < 0);
    uint64_t adv = isu ? 6u : 2u;
    int len;
    uint32_t word = uj_enc_word(cp, &len);       /* computed for both classes */
    uint32_t out = isu ? word : (uint32_t)(uint8_t)sv;
    uint64_t olen = isu ? (uint64_t)len : 1u;
    if (isu && (cp - 0xD800u) < 0x400u && i + 12 <= n) {
        uint64_t w2;
        memcpy(&w2, p + i + 4, 8);
        int g0 = UJ_HEX[(w2 >> 32) & 0xFF], g1 = UJ_HEX[(w2 >> 40) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 48) & 0xFF], g3 = UJ_HEX[(w2 >> 56) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | ((uint32_t)g3);
        if (((w2 >> 16) & 0xFF) == '\\' && ((w2 >> 24) & 0xFF) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
            word = uj_enc_word(cp, &len);
            out = word;
            olen = (uint64_t)len;
        }
    }
    if (bad) { *err = i; return 0; }
    {
        uint64_t ow = (uint64_t)out;
        memcpy(dst + *jp, &ow, 8);
    }
    *jp += olen;
    *advp = adv;
    return 1;
}

/* The same for the counting pass: the encoded length is computed, nothing is
   stored. */
static inline __attribute__((always_inline)) int
zf_esc_bf_cnt(const uint8_t *p, uint64_t n, uint64_t i, uint64_t *jp,
              uint64_t *advp, uint64_t *err) {
    if (i + 9 > n) return zf_esc_cnt(p, n, i, jp, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);
    unsigned c1 = (unsigned)(w & 0xFFu);
    int isu = (c1 == 'u');
    int8_t sv = UJ_UNESC[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int bad = isu ? ((h0 | h1 | h2 | h3) < 0) : (sv < 0);
    uint64_t adv = isu ? 6u : 2u;
    int len;
    (void)uj_enc_word(cp, &len);
    uint64_t olen = isu ? (uint64_t)len : 1u;
    if (isu && (cp - 0xD800u) < 0x400u && i + 12 <= n) {
        uint64_t w2;
        memcpy(&w2, p + i + 4, 8);
        int g0 = UJ_HEX[(w2 >> 32) & 0xFF], g1 = UJ_HEX[(w2 >> 40) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 48) & 0xFF], g3 = UJ_HEX[(w2 >> 56) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if (((w2 >> 16) & 0xFF) == '\\' && ((w2 >> 24) & 0xFF) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
            (void)uj_enc_word(cp, &len);
            olen = (uint64_t)len;
        }
    }
    if (bad) { *err = i; return 0; }
    *jp += olen;
    *advp = adv;
    return 1;
}

/* ------------------------------------------------ bulk body validation ----
   The serial pass pays one dependent load per escape (class byte, four hex
   digits, then the class/hex tables), which on cold corpus data is the whole
   cost.  This pass decides accept/reject for a body with vector work only:
   no per-escape branch and no per-escape scalar load.

   Conditions, and why they are exactly the reference's rejections:
     * a byte below 0x20 anywhere rejects.  An escape cannot hide one: every
       byte an escape consumes is either a class character or a hex digit, all
       >= 0x20, so a control byte always makes the escape invalid as well.
     * a backslash must be followed by one of " \ / b f n r t u.
     * a \u must be followed by four hex digits.
   Surrogate pairing is deliberately absent: no pairing outcome rejects a
   document (a lone surrogate is encoded as WTF-8), and an invalid low
   surrogate's own \u fails the hex rule at its own backslash.

   The error *offset* is not this pass's job.  A rejecting body is localized by
   the serial step (zf_val64), which reports the reference's first offset; that
   happens once per rejected document, never on the accepted path. */
static inline __attribute__((always_inline)) __m256i
zf_class_tab_lo(void) {
    /* for each low nibble, the set of allowed high nibbles as a bitmask */
    return _mm256_broadcastsi128_si256(_mm_setr_epi8(
        /*0*/ 0, 0, (char)0xC4, 0, (char)0x80, (char)0x80, (char)0x40, 0,
        /*8*/ 0, 0, 0, 0, (char)0x20, 0, (char)0x40, (char)0x04));
}
static inline __attribute__((always_inline)) __m256i
zf_class_tab_hi(void) {
    return _mm256_broadcastsi128_si256(_mm_setr_epi8(
        1, 2, 4, 8, 16, 32, 64, (char)128, 0, 0, 0, 0, 0, 0, 0, 0));
}

/* Mask of positions whose byte is one of " \ / b f n r t u (1 = ok). */
static inline __attribute__((always_inline)) unsigned
zf_mask_class_ok(__m256i v) {
    const __m256i vf = _mm256_set1_epi8(0x0F);
    __m256i lo = _mm256_and_si256(v, vf);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), vf);
    __m256i t = _mm256_shuffle_epi8(zf_class_tab_lo(), lo);
    __m256i b = _mm256_shuffle_epi8(zf_class_tab_hi(), hi);
    __m256i z = _mm256_and_si256(t, b);      /* zero exactly when not in the set */
    unsigned notok = (unsigned)_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(z, _mm256_setzero_si256()));
    return ~notok;
}

/* byte is a hex digit */
static inline __attribute__((always_inline)) unsigned
zf_mask_hex(__m256i v) {
    const __m256i v9 = _mm256_set1_epi8(9);
    const __m256i v5 = _mm256_set1_epi8(5);
    __m256i d = _mm256_sub_epi8(v, _mm256_set1_epi8('0'));
    unsigned dig = (unsigned)_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_min_epu8(d, v9), d));
    __m256i l = _mm256_or_si256(v, _mm256_set1_epi8(0x20));
    __m256i e = _mm256_sub_epi8(l, _mm256_set1_epi8('a'));
    unsigned let = (unsigned)_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_min_epu8(e, v5), e));
    return dig | let;
}

/* 1 = valid, 0 = invalid, -1 = undecided.
   The position-wise check is exact when no two backslashes are adjacent: then
   every backslash is an escape start and none is a class character.  A body
   with an adjacent pair (`\\`, or a longer run) needs the run parity to tell a
   start from a consumed class character, which is the serial step's job; the
   caller runs it for -1 exactly as it does for 0.
   A control byte is bad whatever the parity, so it decides immediately.
   p must be readable 64 bytes past the body. */
static inline __attribute__((always_inline)) int
zf_bulk_ok(const uint8_t *p, uint64_t n) {
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    const __m256i vu = _mm256_set1_epi8('u');
    uint64_t i = 0;
    unsigned anyadj = 0, carry = 0, badesc = 0;
    while (i < n) {
        uint64_t rem = n - i;
        uint64_t win = rem < 32 ? rem : 32;
        __m256i va = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned keep = (win == 32) ? 0xFFFFFFFFu : ((1u << win) - 1u);
        unsigned ctl = (unsigned)_mm256_movemask_epi8(
                           _mm256_cmpeq_epi8(_mm256_min_epu8(va, v19), va)) & keep;
        if (ctl) return 0;
        unsigned bs = (unsigned)_mm256_movemask_epi8(
                          _mm256_cmpeq_epi8(va, vbs)) & keep;
        if (bs & ((bs << 1) | carry)) anyadj = 1;
        carry = (bs >> 31) & 1u;
        if (bs) {
            /* bit j: the byte after position i+j is a legal escape character,
               a position at or past n is not */
            unsigned climit = (rem - 1 >= 32) ? 0xFFFFFFFFu
                                              : ((1u << (rem - 1)) - 1u);
            __m256i vb = _mm256_loadu_si256((const __m256i *)(p + i + 1));
            unsigned clsok = zf_mask_class_ok(vb) & climit;
            unsigned u = (unsigned)_mm256_movemask_epi8(
                             _mm256_cmpeq_epi8(vb, vu)) & climit;
            uint64_t hm = (uint64_t)zf_mask_hex(
                _mm256_loadu_si256((const __m256i *)(p + i + 2)));
            if (rem >= 34)
                hm |= (uint64_t)zf_mask_hex(
                          _mm256_loadu_si256((const __m256i *)(p + i + 34))) << 32;
            uint64_t hkeep = (rem >= 66) ? ~0ULL
                            : (rem >= 2 ? ((1ULL << (rem - 2)) - 1ULL) : 0ULL);
            hm &= hkeep;
            uint64_t hex4 = hm & (hm >> 1) & (hm >> 2) & (hm >> 3);
            badesc |= bs & ~clsok;
            badesc |= (bs & u) & ~(unsigned)hex4;
        }
        i += win;
    }
    if (anyadj) return -1;
    return badesc ? 0 : 1;
}

/* Trusting decode step: the body has already passed zf_bulk_ok, so this only
   materialises bytes.  Same output contract (WTF-8 for a lone surrogate, one
   escape consumed at a time), no validity branch.  Falls back to the checking
   step near the end of the body, where the wide load would run past it. */
static inline __attribute__((always_inline)) int
zf_esc_cp_t(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
            uint64_t *jp, uint64_t *advp, uint64_t *err) {
    if (i + 12 > n) return zf_esc_cp(p, n, i, dst, jp, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);
    unsigned c1 = (unsigned)(w & 0xFFu);
    int isu = (c1 == 'u');
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    uint64_t adv = isu ? 6u : 2u;
    int len;
    uint32_t word = uj_enc_word(cp, &len);
    uint32_t out = isu ? word : (uint32_t)(uint8_t)UJ_UNESC[c1];
    uint64_t olen = isu ? (uint64_t)len : 1u;
    if (isu && (cp - 0xD800u) < 0x400u && i + 12 <= n) {
        uint64_t w2;
        memcpy(&w2, p + i + 4, 8);
        int g0 = UJ_HEX[(w2 >> 32) & 0xFF], g1 = UJ_HEX[(w2 >> 40) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 48) & 0xFF], g3 = UJ_HEX[(w2 >> 56) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | ((uint32_t)g3);
        if (((w2 >> 16) & 0xFF) == '\\' && ((w2 >> 24) & 0xFF) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
            word = uj_enc_word(cp, &len);
            out = word;
            olen = (uint64_t)len;
        }
    }
    {
        uint64_t ow = (uint64_t)out;
        memcpy(dst + *jp, &ow, 8);
    }
    *jp += olen;
    *advp = adv;
    return 1;
}

/* Copy len bytes (1..64) with whole-vector stores; over-writes up to 32 bytes
   past dst+len, which the caller's slack and the output cursor make harmless. */
static inline __attribute__((always_inline)) void
zf_run(const uint8_t *p, uint64_t len, uint8_t *dst) {
    _mm256_storeu_si256((__m256i *)dst,
                        _mm256_loadu_si256((const __m256i *)p));
    if (len > 32)
        _mm256_storeu_si256((__m256i *)(dst + 32),
                            _mm256_loadu_si256((const __m256i *)(p + 32)));
}

/* Copy len bytes (any length) with vector stores plus at most one overlapping
   tail vector; writes at most len + 31 bytes, so the same slack rule holds.
   Used for the clean prefix before a body's first escape, which can be longer
   than one window. */
static inline __attribute__((always_inline)) void
zf_copy(const uint8_t *p, uint64_t len, uint8_t *dst) {
    if (len < 32) {
        _mm256_storeu_si256((__m256i *)dst,
                            _mm256_loadu_si256((const __m256i *)p));
        return;
    }
    uint64_t q = 0;
    for (; q + 32 <= len; q += 32)
        _mm256_storeu_si256((__m256i *)(dst + q),
                            _mm256_loadu_si256((const __m256i *)(p + q)));
    if (q < len)
        _mm256_storeu_si256((__m256i *)(dst + len - 32),
                            _mm256_loadu_si256((const __m256i *)(p + len - 32)));
}

/* Two passes with the same source: validate-only and materialise.  Each is
   generated for a 32-byte and a 64-byte window so the short-body tier can be
   chosen by measurement.
   ZF_FAST_SET selects the empty-mask shortcut of the 64-byte kernels:
     0 off, 1 test the first 32-byte chunk of every body, 2 test only a body
     that fits one chunk. */
#ifndef ZF_FAST_SET
#define ZF_FAST_SET 1
#endif
#ifdef ZF_COUNT
static uint64_t zf_win_count, zf_esc_count;
#endif
#define ZF_NAME zf_val32
#define ZF_ESC 0
#define ZF_COPY 0
#define ZF_W 32
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

#define ZF_NAME zf_val64
#define ZF_ESC 0
#define ZF_COPY 0
#define ZF_W 64
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

/* the same validate-only kernel with the empty-mask first-chunk exit */
#define ZF_NAME zf_val64f
#define ZF_ESC 0
#define ZF_COPY 0
#define ZF_W 64
#define ZF_FAST 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC
#undef ZF_FAST

#define ZF_NAME zf_span32
#define ZF_ESC 0
#define ZF_COPY 2
#define ZF_W 32
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

#define ZF_NAME zf_span64
#define ZF_ESC 0
#define ZF_COPY 2
#define ZF_W 64
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

/* the same span kernel with the empty-mask first-chunk exit */
#define ZF_NAME zf_span64f
#define ZF_ESC 0
#define ZF_COPY 2
#define ZF_W 64
#define ZF_FAST 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC
#undef ZF_FAST

/* attribution only: every body materialised, no span form */
#define ZF_NAME zf_cp64
#define ZF_ESC 0
#define ZF_COPY 1
#define ZF_W 64
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

/* the same four passes with the branch-free escape step */
#define ZF_NAME zf_val32b
#define ZF_COPY 0
#define ZF_W 32
#define ZF_ESC 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

#define ZF_NAME zf_val64b
#define ZF_COPY 0
#define ZF_W 64
#define ZF_ESC 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

#define ZF_NAME zf_span32b
#define ZF_COPY 2
#define ZF_W 32
#define ZF_ESC 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

#define ZF_NAME zf_span64b
#define ZF_COPY 2
#define ZF_W 64
#define ZF_ESC 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC

/* copy with the validity branch removed: only usable on a body zf_bulk_ok
   accepted, which is what the combined row exercises */
#define ZF_NAME zf_span_t
#define ZF_COPY 2
#define ZF_W 64
#undef ZF_NOVAL
#define ZF_NOVAL 1
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_NOVAL

/* generated only for the diagnostic: same source, plus window/escape counters */
#ifdef ZF_COUNT
#define ZF_NAME zf_val64c
#define ZF_COPY 0
#define ZF_W 64
#define ZF_ESC 0
#include "zf_impl.inc"
#undef ZF_NAME
#undef ZF_COPY
#undef ZF_W
#undef ZF_ESC
#endif

#endif /* ZF_H */
