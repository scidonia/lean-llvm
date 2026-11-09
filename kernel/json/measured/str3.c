/* str3.c -- string-body decode paths selected by the stage-1 escape mask.
   Scratch; not part of the repository.

   Three kernels, all with the same destination/error contract as uj_decode:
     uj3_plain   the body holds no escape at all (the mask says so): a masked
                 32-byte copy loop, no backslash test and no escape ladder.
     uj3_simple  escapes are present but none is \u: the same masked copy but
                 the escape byte is decoded in line with a table lookup.  A \u
                 that the classifier missed still falls back to uj_esc, so the
                 kernel is correct for any body.
     path 3      the body holds \u: the existing uj_decode / uj_decode_acc call.

   dst must hold n bytes plus 32 bytes of slack, and p must be readable 32
   bytes past its body (the input is padded for the stage-1 block loads). */
#ifndef STR3_H
#define STR3_H

/* Control bytes only (byte <= 0x1F). */
static inline __attribute__((always_inline)) unsigned
uj3_ctl_mask(__m256i v, __m256i v19) {
    return (unsigned)_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v));
}

/* keep the low k bytes (k < 32) of a vector in a byte-sum accumulator */
static inline __attribute__((always_inline)) __m256i
uj3_keep(unsigned k) {
    return uj_keep(k);
}

__attribute__((always_inline)) static inline size_t
uj3_plain(const uint8_t *p, uint64_t n, uint8_t *dst, uint64_t *acc,
          int want_acc, size_t *err) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    __m256i av = _mm256_setzero_si256();
    uint64_t i = 0;
    if (!n) return 0;
    while (n - i >= 32) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = uj3_ctl_mask(v, v19);
        if (m) { *err = i + (uint64_t)__builtin_ctz(m); return UJ_FAIL; }
        if (dst) _mm256_storeu_si256((__m256i *)(dst + i), v);
        if (want_acc) av = uj_add32(av, v);
        i += 32;
    }
    if (i < n) {
        unsigned k = (unsigned)(n - i);
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = uj3_ctl_mask(v, v19) & ((1u << k) - 1u);
        if (m) { *err = i + (uint64_t)__builtin_ctz(m); return UJ_FAIL; }
        if (dst) _mm256_storeu_si256((__m256i *)(dst + i), v);
        if (want_acc) av = uj_add32(av, _mm256_and_si256(v, uj3_keep(k)));
        i = n;
    }
    if (want_acc) *acc += uj_hsum256(av);
    return (size_t)n;
}

__attribute__((always_inline)) static inline size_t
uj3_simple(const uint8_t *p, uint64_t n, uint8_t *dst, uint64_t *acc,
           int want_acc, size_t *err) {
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    __m256i av = _mm256_setzero_si256();
    uint64_t i = 0, j = 0, esc_sum = 0;
    if (!n) {
        if (want_acc) *acc += 0;
        return 0;
    }
    for (;;) {
        uint64_t left = n - i;
        unsigned keep = (left >= 32) ? 0xFFFFFFFFu : ((1u << (unsigned)left) - 1u);
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = uj_mask(v, vbs, v19) & keep;
        if (!m) {
            unsigned take = (left >= 32) ? 32u : (unsigned)left;
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc)
                av = uj_add32(av, take == 32 ? v
                                            : _mm256_and_si256(v, uj3_keep(take)));
            i += take; j += take;
            if (i >= n) break;
            continue;
        }
        unsigned b = (unsigned)__builtin_ctz(m);
        if (b) {
            if (dst) _mm256_storeu_si256((__m256i *)(dst + j), v);
            if (want_acc) av = uj_add32(av, _mm256_and_si256(v, uj3_keep(b)));
            i += b; j += b;
        }
        if (p[i] < 0x20) { *err = i; return UJ_FAIL; }
        /* backslash */
        int8_t sv = (i + 1 < n) ? UJ_UNESC[p[i + 1]] : -1;
        if (sv >= 0) {
            if (dst) dst[j] = (uint8_t)sv;
            esc_sum += (uint64_t)(uint8_t)sv;
            i += 2; j += 1;
        } else {
            uint8_t enc[8];
            uint32_t elen = 0;
            if (!uj_esc(p, n, &i, enc, &elen, err)) return UJ_FAIL;
            if (dst) memcpy(dst + j, enc, 4);
            for (uint32_t k = 0; k < elen; k++) esc_sum += enc[k];
            j += elen;
        }
        if (i >= n) break;
    }
    if (want_acc) *acc += uj_hsum256(av) + esc_sum;
    return (size_t)j;
}

#endif
