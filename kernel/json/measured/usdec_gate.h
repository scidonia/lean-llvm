/* usdec_gate.h -- two shapes of the per-body list decoder in one build, so a
   document-level decision can pick one at run time.  Scratch.

     us_dec_x_out  the shipped shape: out of line, `\u` inlined (exactly
                   us_dec_x compiled with US_ESC=0).
     us_dec_x_inl  the shape measured 3-5 ns/block faster on canonical: the
                   decoder inlined into the consumer, its `\u` step kept out of
                   line so the inlined copy stays small.

   Both are the same source (usdec_x_body.inc) with the escape step
   substituted; nothing else differs.  Only the list consumer's call site
   changes (s2port.h). */
#ifndef USDEC_GATE_H
#define USDEC_GATE_H

/* The out-of-line `\u` step of the inlined shape.  A copy of usdec.h's
   us_esc_u with the noinline attribute, so the out-of-line shape keeps its
   own (always-inlined) copy under US_ESC=0 and the two shapes do not share
   code whose placement would change the measurement. */
static __attribute__((noinline)) int
us_esc_u_ni(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
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
    us_emit(cp, dst, jp);
    *advp = adv;
    return 1;
}

/* simple escapes inline, `\u` out of line: US_ESC=2's shape, locally */
static inline __attribute__((always_inline)) int
us_esc_si(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
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
    return us_esc_u_ni(p, n, i, dst, jp, advp, err);
}

/* shape O: out of line, `\u` inlined (the current form) */
#define USDEC_NAME us_dec_x_out
#define USDEC_ATTR __attribute__((noinline)) static
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ATTR
#undef USDEC_ESCFN

/* shape J: inlined with `\u` inlined as well (US_XP_INLINE=1, US_ESC=0).
   The largest inlined copy; kept because the `in` build measured it best on
   the escape-heavy files when the decoder's `\u` block is hot. */
#define USDEC_NAME us_dec_x_inl2
#define USDEC_ATTR static inline __attribute__((always_inline))
#define USDEC_ESCFN us_esc
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ATTR
#undef USDEC_ESCFN

/* shape I: inlined, `\u` out of line */
#define USDEC_NAME us_dec_x_inl
#define USDEC_ATTR static inline __attribute__((always_inline))
#define USDEC_ESCFN us_esc_si
#include "usdec_x_body.inc"
#undef USDEC_NAME
#undef USDEC_ATTR
#undef USDEC_ESCFN

#endif /* USDEC_GATE_H */
