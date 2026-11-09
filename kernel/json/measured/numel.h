/* numel.h -- exact decimal -> double for mantissas up to 19 digits and
   decimal exponents in [-22,22] (the range the mul/div fast path cannot cover
   once the mantissa exceeds 2^53).

   One 128-bit multiply of the normalised mantissa by the 128-bit normalised
   significand of 10^q, then round to nearest even on the 53-bit slice.  The
   low half of the product (and, for q < 0, the truncated significand) is the
   only information lost; when the slice lands within one unit of the rounding
   point the function reports "cannot decide" and the caller falls back to
   strtod.  A mantissa that fits in 15 digits never reaches this code. */
#ifndef NUMEL_H
#define NUMEL_H

#include <stdint.h>
#include <string.h>
#include <stddef.h>

#include "epow_table.h"

/* value = w * 10^q with w < 10^19 and |q| <= 22.
   Returns 1 and writes the correctly rounded double, or 0 when the caller
   must use the slow path (ambiguity, subnormal or overflow). */
__attribute__((always_inline)) static inline int num_el(uint64_t w, int64_t q, double *out) {
    if (q < EPOW_MIN || q > EPOW_MAX) return 0;
    if (w == 0) { *out = 0.0; return 1; }
    const EPow *t = &EPOW[q - EPOW_MIN];
    int lz = __builtin_clzll(w);
    uint64_t W = w << lz;
    unsigned __int128 u = (unsigned __int128)W * t->hi;
    unsigned __int128 v = (unsigned __int128)W * t->lo;
    uint64_t dlo = (uint64_t)v;                       /* dropped low bits */
    uint64_t ulo = (uint64_t)u;
    uint64_t Rlo = ulo + (uint64_t)(v >> 64);
    uint64_t Rhi = (uint64_t)(u >> 64) + (Rlo < ulo);
    int s = 126 + (int)(Rhi >> 63) - 52;              /* 74 or 75 */
    uint64_t m = Rhi >> (s - 64);
    /* The remainder is wider than 64 bits: compare it with half of the last
       place as (high part, low part) against (hh, 0). */
    uint64_t hp = Rhi & ((1ULL << (s - 64)) - 1);
    uint64_t hh = 1ULL << (s - 64 - 1);
    int cmp;                     /* remainder - half: -1 below, 0 equal, 1 above */
    if (hp > hh || (hp == hh && Rlo != 0)) cmp = 1;
    else if (hp == hh) cmp = 0;
    else cmp = -1;
    int up;
    if (q >= 0) {                        /* significand exact: ties resolvable */
        if (cmp > 0) up = 1;
        else if (cmp == 0) up = dlo ? 1 : (int)(m & 1);
        else up = 0;
    } else {
        /* one unit of the dropped product, plus the truncated significand */
        if ((cmp == 0 && Rlo <= 1) || (hp + 1 == hh && Rlo == ~(uint64_t)0))
            return 0;
        up = cmp > 0;
    }
    if (up) {
        m++;
        if (m == (1ULL << 53)) { m >>= 1; s++; }
    }
    int eu = s + 64 + t->e - lz + 52;
    if (eu > 1023 || eu < -1022) return 0;
    uint64_t bits = ((uint64_t)(eu + 1023) << 52) | (m & ((1ULL << 52) - 1));
    double d;
    memcpy(&d, &bits, 8);
    *out = d;
    return 1;
}

#endif
