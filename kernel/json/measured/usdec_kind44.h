/* usdec_kind44.h -- escape steps that consume the carried kind.  Scratch.

   The shipped step decides the class from the body itself:
       sv = UJ_UNESC[p[i+1]];  if (sv >= 0) simple; else if (p[i+1] != 'u') fail;
                               else \u
   so the branch that separates a simple escape from `\u` is a function of the
   input bytes and changes inside a body.

   Here the class arrives as one bit from stage 1.  The simple form is one
   US_ESC43 look-up (the decoded byte, its length, and the invalid flag in the
   same entry) and one 4-byte store; the `\u` form is us_esc_u2, whose encoded
   word is stored with us_emit4's single 4-byte store.  The validity test that
   remains in the simple form is never taken on a carried simple escape, so it
   is a branch whose direction is fixed per class rather than per body byte.

   Three dispatch shapes, all on the same carried bit:
       *_if    if (kind) u; else simple;
       *_jmp   computed goto through a two-entry label table
       *_sw    switch (kind & 1) */
#ifndef USDEC_KIND44_H
#define USDEC_KIND44_H

#include "usdec_esc43.h"   /* US_ESC43, us_esc_u2, us_emit4 */

/* simple escape, class already known: one table entry, one 4-byte store.
   The U/BAD test is the error path for an invalid escape and the safety net
   for a record that disagrees with the bytes; neither is taken on the simple
   path the record names. */
/* K44_STRICT removes the "record disagrees with the bytes" fallback, so a
   gate built with it proves the carried bit is the one driving the path: a
   wrong record turns into wrong output instead of a silent recovery. */
#ifndef K44_STRICT
#define K44_STRICT 0
#endif

static inline __attribute__((always_inline)) int
us_esc_k_simple(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
                uint64_t *jp, uint64_t *advp, uint64_t *err) {
    if (i + 1 >= n) { *err = i; return 0; }
    uint32_t t = US_ESC43[p[i + 1]];
#if K44_STRICT
    if (__builtin_expect(t & US_E_BAD, 0)) {
        *err = i;
        return 0;
    }
    {
        uint32_t w = t & 0xFFu;
        memcpy(dst + *jp, &w, 4);
    }
#else
    if (__builtin_expect(t & (US_E_U | US_E_BAD), 0)) {
        if (t & US_E_U) return us_esc_u2(p, n, i, dst, jp, advp, err);
        *err = i;
        return 0;
    }
    {
        uint32_t w = t & 0xFFu;
        memcpy(dst + *jp, &w, 4);
    }
#endif
    *jp += 1;
    *advp = 2;
    return 1;
}

static inline __attribute__((always_inline)) int
us_esc_k_if(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
            uint64_t *jp, uint64_t *advp, uint64_t *err, unsigned kind) {
    if (kind) return us_esc_u2(p, n, i, dst, jp, advp, err);
    return us_esc_k_simple(p, n, i, dst, jp, advp, err);
}

static inline __attribute__((always_inline)) int
us_esc_k_jmp(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
             uint64_t *jp, uint64_t *advp, uint64_t *err, unsigned kind) {
    static const void *const tab[2] = { &&ks, &&ku };
    goto *tab[kind & 1];
ks:
    return us_esc_k_simple(p, n, i, dst, jp, advp, err);
ku:
    return us_esc_u2(p, n, i, dst, jp, advp, err);
}

static inline __attribute__((always_inline)) int
us_esc_k_sw(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst,
            uint64_t *jp, uint64_t *advp, uint64_t *err, unsigned kind) {
    switch (kind & 1u) {
    case 1:
        return us_esc_u2(p, n, i, dst, jp, advp, err);
    default:
        return us_esc_k_simple(p, n, i, dst, jp, advp, err);
    }
}

#endif /* USDEC_KIND44_H */
