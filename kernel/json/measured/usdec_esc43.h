/* usdec_esc43.h -- table-driven escape expansion for the per-body list
   decoder, and three shapes of the \u step.  Scratch; nothing here belongs to
   the repository.

   The existing escape step (usdec.h, US_ESC=0) is:
       sv = UJ_UNESC[c1]; if (sv >= 0) { dst[j] = sv; j += 1; adv = 2; }
       else if (c1 != 'u') fail; else us_esc_u(...)
   i.e. one byte stored per simple escape, a kind branch, and a \u step that
   packs four hex digits and encodes the code point.

   Here:
     us_emit4     the UTF-8 word stored with one 4-byte unaligned store
     us_esc_u2    the \u step with the 4-byte store (otherwise as shipped)
     US_ESC43     a 256-entry table: one entry per byte that may follow a
                  backslash, holding the output byte, its length, and the
                  class (\u / invalid) in flag bits
     us_esc_t     table class test, single 4-byte store for a simple escape
     us_esc_bf    branch-free: both classes computed, one 8-byte store, table
                  selects the simple class; hex pack runs for every escape
*/

#ifndef USDEC_ESC43_H
#define USDEC_ESC43_H

/* ---- one 4-byte store for the encoded word -------------------------------- */
static inline __attribute__((always_inline)) void
us_emit4(uint32_t cp, uint8_t *dst, uint64_t *jp) {
    int len;
    uint32_t w = uj_enc_word(cp, &len);
    memcpy(dst + *jp, &w, 4);
    *jp += (uint64_t)len;
}

/* ---- the \u step, 4-byte store ------------------------------------------ */
#ifndef US_ESC43_UNI
#define US_ESC43_UNI 0
#endif
#if US_ESC43_UNI
static __attribute__((noinline)) int
#else
static inline __attribute__((always_inline)) int
#endif
us_esc_u2(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
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
    us_emit4(cp, dst, jp);
    *advp = adv;
    return 1;
}


/* the rewritten \u step, kept out of line: the hot loop holds only the
   simple-escape path and a call */
static __attribute__((noinline)) int
us_esc_u2_ni(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
             uint64_t *jp, uint64_t *advp, uint64_t *err) {
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
    us_emit4(cp, dst, jp);
    *advp = adv;
    return 1;
}

/* shipped simple path, \u out of line (US_ESC=2's shape) */
static inline __attribute__((always_inline)) int
us_esc_sni(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
           uint64_t *jp, uint64_t *advp, uint64_t *err) {
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
    return us_esc_u2_ni(p, n, i, dst, jp, advp, err);
}

/* the shipped escape step with only its \u helper replaced: simple escapes
   keep the current one-byte store, so this isolates the \u change */
static inline __attribute__((always_inline)) int
us_esc_u2only(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
              uint64_t *jp, uint64_t *advp, uint64_t *err) {
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
    return us_esc_u2(p, n, i, dst, jp, advp, err);
}

/* ---- the kind table ------------------------------------------------------
   bits 0..7   the decoded byte of a simple escape
   bits 8..15  its output length (1)
   bit 16      the escape is \u
   bit 17      the escape is invalid (bad class)
   Byte 0 is a valid output byte for no escape, so 0 is an unambiguous "not a
   simple escape" as well. */
#define US_E_LEN1 (1u << 8)
#define US_E_U    (1u << 16)
#define US_E_BAD  (1u << 17)

static const uint32_t US_ESC43[256] = {
    [0 ... 255] = US_E_BAD,
    ['"'] = 0x22 | US_E_LEN1,
    ['\\'] = 0x5C | US_E_LEN1,
    ['/'] = 0x2F | US_E_LEN1,
    ['b'] = 0x08 | US_E_LEN1,
    ['f'] = 0x0C | US_E_LEN1,
    ['n'] = 0x0A | US_E_LEN1,
    ['r'] = 0x0D | US_E_LEN1,
    ['t'] = 0x09 | US_E_LEN1,
    ['u'] = US_E_U,
};

/* table-driven, class branch kept: the simple escape is one lookup and one
   4-byte store; \u goes to the rewritten step */
static inline __attribute__((always_inline)) int
us_esc_t(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
         uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint32_t t = US_ESC43[p[i + 1]];
    if (t & US_E_U) return us_esc_u2(p, n, i, dst, jp, advp, err);
    if (t & US_E_BAD) { *err = i; return 0; }
    uint32_t w = t & 0xFFu;
    memcpy(dst + *jp, &w, 4);
    *jp += 1;
    *advp = 2;
    return 1;
}

/* table class test, simple escapes one 4-byte store, \u out of line */
static inline __attribute__((always_inline)) int
us_esc_tni(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
           uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint32_t t = US_ESC43[p[i + 1]];
    if (t & US_E_U) return us_esc_u2_ni(p, n, i, dst, jp, advp, err);
    if (t & US_E_BAD) { *err = i; return 0; }
    uint32_t w = t & 0xFFu;
    memcpy(dst + *jp, &w, 4);
    *jp += 1;
    *advp = 2;
    return 1;
}

/* four hex digits from four table loads, no early return */
static inline __attribute__((always_inline)) int
us_hex4_val(const uint8_t *q, uint32_t *out) {
    int h0 = UJ_HEX[q[0]], h1 = UJ_HEX[q[1]];
    int h2 = UJ_HEX[q[2]], h3 = UJ_HEX[q[3]];
    if ((h0 | h1 | h2 | h3) < 0) return 0;
    *out = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
           ((uint32_t)h2 << 4) | (uint32_t)h3;
    return 1;
}

/* branch-free between the classes: the hex pack and the encoding run for every
   escape and the table's word/len/advance are cmov'ed in.  One 8-byte store
   covers both classes, so the store shape does not depend on the kind.  Needs
   12 readable bytes past the backslash, falling back to the branchy form at
   the end of a body. */
static inline __attribute__((always_inline)) int
us_esc_tail(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
            uint64_t *jp, uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint32_t t = US_ESC43[p[i + 1]];
    if (t & US_E_U) return us_esc_u2(p, n, i, dst, jp, advp, err);
    if (t & US_E_BAD) { *err = i; return 0; }
    uint32_t w = t & 0xFFu;
    memcpy(dst + *jp, &w, 4);
    *jp += 1;
    *advp = 2;
    return 1;
}

static inline __attribute__((always_inline)) int
us_esc_bf(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
          uint64_t *advp, uint64_t *err) {
    if (i + 12 > n) return us_esc_tail(p, n, i, dst, jp, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);                    /* c1 c2 c3 c4 c5 c6 c7 c8 */
    unsigned c1 = (unsigned)(w & 0xFFu);
    uint32_t t = US_ESC43[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int len;
    uint32_t uw = uj_enc_word(cp, &len);         /* computed for every escape */
    uint32_t isu = t & US_E_U;
    uint32_t word = isu ? uw : (t & 0xFFu);
    uint64_t outlen = isu ? (uint64_t)len : 1;
    uint64_t adv = isu ? 6u : 2u;
    if (t & US_E_BAD) { *err = i; return 0; }
    if (isu && ((h0 | h1 | h2 | h3) < 0)) { *err = i; return 0; }
    if (isu && (cp - 0xD800u) < 0x400u) {
        uint64_t w2;
        memcpy(&w2, p + i + 6, 8);
        int g0 = UJ_HEX[(w2 >> 16) & 0xFF], g1 = UJ_HEX[(w2 >> 24) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 32) & 0xFF], g3 = UJ_HEX[(w2 >> 40) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((w2 & 0xFFu) == '\\' && ((w2 >> 8) & 0xFFu) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            uw = uj_enc_word(cp, &len);
            word = uw;
            outlen = (uint64_t)len;
            adv = 12;
        }
    }
    {
        uint64_t out = (uint64_t)word;
        memcpy(dst + *jp, &out, 8);
    }
    *jp += outlen;
    *advp = adv;
    return 1;
}

/* branch-free table with the scalar hex pack and a 4-byte store: both classes
   are computed, but the pack is four table loads instead of the 16-byte
   pshufb/maddubs chain, and the tail fallback is the branchy form. */
static inline __attribute__((always_inline)) int
us_esc_bfs(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
           uint64_t *advp, uint64_t *err) {
    if (i + 12 > n) return us_esc_tail(p, n, i, dst, jp, advp, err);
    uint64_t w;
    memcpy(&w, p + i + 1, 8);
    unsigned c1 = (unsigned)(w & 0xFFu);
    uint32_t t = US_ESC43[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int len;
    uint32_t uw = uj_enc_word(cp, &len);
    uint32_t isu = t & US_E_U;
    uint32_t word = isu ? uw : (t & 0xFFu);
    uint64_t outlen = isu ? (uint64_t)len : 1;
    uint64_t adv = isu ? 6u : 2u;
    if (t & US_E_BAD) { *err = i; return 0; }
    if (isu && ((h0 | h1 | h2 | h3) < 0)) { *err = i; return 0; }
    if (isu && (cp - 0xD800u) < 0x400u) {
        uint64_t w2;
        memcpy(&w2, p + i + 6, 8);
        int g0 = UJ_HEX[(w2 >> 16) & 0xFF], g1 = UJ_HEX[(w2 >> 24) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 32) & 0xFF], g3 = UJ_HEX[(w2 >> 40) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((w2 & 0xFFu) == '\\' && ((w2 >> 8) & 0xFFu) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            uw = uj_enc_word(cp, &len);
            word = uw;
            outlen = (uint64_t)len;
            adv = 12;
        }
    }
    memcpy(dst + *jp, &word, 4);
    *jp += outlen;
    *advp = adv;
    return 1;
}

#endif /* USDEC_ESC43_H */
