/* numf.h -- tiered JSON number scan + conversion to double.

   Tier 1: mantissa <= 15 digits, |eff| <= 22.  (double)mant * / POW10[eff]
           with both operands exact doubles below 2^53, so the single IEEE
           operation is the correctly rounded value of the decimal.
   Tier 2: mantissa <= 19 digits, |eff| <= EPOW_MAX.  A 128-bit multiply by the
           normalised significand of 10^eff (numel_el.h); the mantissa no longer
           fits 2^53, so a divide would round twice.
   Tier 3: everything else (longer mantissa, wider exponent, subnormal,
           overflow, or tier 2's ambiguity): NUMF_SLOW, i.e. num_scan, which
           validates the grammar when that has not happened yet and converts
           with strtod.

   The caller must define NUMF_SLOW(p, n, out, err) before including. */
#ifndef NUMF_EL1_H
#define NUMF_EL1_H

#include "numel.h"
#include "numel_el.h"

static uint64_t g_nume1_el, g_nume1_slow;      /* tier counters (diagnostics) */

static const double NUMF_EL1_POW10[23] = {
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22
};

static const uint64_t NUMF_EL1_P10[20] = {
    1ULL, 10ULL, 100ULL, 1000ULL, 10000ULL, 100000ULL, 1000000ULL,
    10000000ULL, 100000000ULL, 1000000000ULL, 10000000000ULL,
    100000000000ULL, 1000000000000ULL, 10000000000000ULL,
    100000000000000ULL, 1000000000000000ULL, 10000000000000000ULL,
    100000000000000000ULL, 1000000000000000000ULL, 10000000000000000000ULL
};

/* Eight ASCII digits at p -> value.  Returns 1 when all eight are digits.
   maddubs/madd turn the eight bytes into 10000*a + b in two instructions, so a
   17-digit mantissa needs two of these instead of seventeen 3-cycle multiplies
   in one dependency chain. */
#ifndef NUMF_SIMD
#define NUMF_SIMD 1
#endif
#include <immintrin.h>
__attribute__((always_inline)) static inline int num_d8_el1(const uint8_t *p, uint32_t *val) {
    uint64_t w;
    memcpy(&w, p, 8);
    __m128i v = _mm_cvtsi64_si128((long long)w);
    __m128i d = _mm_sub_epi8(v, _mm_set1_epi8('0'));
    int ok = _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_min_epu8(d, _mm_set1_epi8(9)), d));
    if ((ok & 0xFF) != 0xFF) return 0;
    __m128i t = _mm_maddubs_epi16(d, _mm_set1_epi16(0x010A));   /* bytes 10,1 */
    __m128i q = _mm_madd_epi16(t, _mm_set1_epi32(100 | (1 << 16)));
    *val = (uint32_t)_mm_cvtsi128_si32(q) * 10000u +
           (uint32_t)_mm_extract_epi32(q, 1);
    return 1;
}

/* RFC 8259 number grammar with in-place conversion.  Returns 1 on success;
   0 with *err = first offending index inside p. */
__attribute__((always_inline)) static inline int num_fast_el1(const uint8_t *p, uint64_t n, double *out, size_t *err) {
    uint64_t i = 0;
    int neg = 0;
    if (i < n && p[i] == '-') { neg = 1; i++; }
    if (i >= n) { *err = (size_t)i; return 0; }
    uint64_t ip = 0, fr = 0, idig = 0, fdig = 0;
    if (p[i] == '0') {
        idig = 1; i++;
    } else if (p[i] >= '1' && p[i] <= '9') {
        ip = (uint64_t)(p[i] - '0'); idig = 1; i++;
#if NUMF_SIMD
        while (i + 8 <= n && idig + 8 <= 19) {
            uint32_t v8;
            if (!num_d8_el1(p + i, &v8)) break;
            ip = ip * 100000000ULL + v8; idig += 8; i += 8;
        }
#endif
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (idig < 19) ip = ip * 10 + (uint64_t)(p[i] - '0');
            idig++; i++;
        }
    } else { *err = (size_t)i; return 0; }
    if (i < n && p[i] == '.') {
        i++;
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
#if NUMF_SIMD
        while (i + 8 <= n && fdig + 8 <= 19) {
            uint32_t v8;
            if (!num_d8_el1(p + i, &v8)) break;
            fr = fr * 100000000ULL + v8; fdig += 8; i += 8;
        }
#endif
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (fdig < 19) fr = fr * 10 + (uint64_t)(p[i] - '0');
            fdig++; i++;
        }
    }
    int64_t exp10 = 0;
    if (i < n && (p[i] == 'e' || p[i] == 'E')) {
        i++;
        int esign = 0;
        if (i < n && (p[i] == '+' || p[i] == '-')) { esign = (p[i] == '-'); i++; }
        if (i >= n || p[i] < '0' || p[i] > '9') { *err = (size_t)i; return 0; }
        /* saturate instead of counting digits: leading zeros must not stop the
           accumulation ("1e00005" is 1e5), and any value past 100000 leaves the
           fast range, so the slow path will re-read the token exactly */
        while (i < n && p[i] >= '0' && p[i] <= '9') {
            if (exp10 < 100000) exp10 = exp10 * 10 + (int64_t)(p[i] - '0');
            i++;
        }
        if (esign) exp10 = -exp10;
    }
    if (i != n) { *err = (size_t)i; return 0; }
    int64_t eff = exp10 - (int64_t)fdig;
    uint64_t nd = idig + fdig;
    if (nd <= 19 && eff >= EPOW_MIN && eff <= EPOW_MAX) {
        uint64_t mant = ip * NUMF_EL1_P10[fdig] + fr;
        if (nd <= 15 && eff >= -22 && eff <= 22) {
            /* both operands exact doubles: one IEEE operation is the result */
            double d = (eff >= 0) ? (double)mant * NUMF_EL1_POW10[eff]
                                  : (double)mant / NUMF_EL1_POW10[-eff];
            *out = neg ? -d : d;
            return 1;
        }
        double d;
        if (num_el_el1(mant, eff, &d)) {
            g_nume1_el++;
            *out = neg ? -d : d;
            return 1;
        }
    }
    double d;
    g_nume1_slow++;
    if (!NUMF_SLOW(p, n, &d, err)) return 0;
    *out = d;
    return 1;
}

#endif
