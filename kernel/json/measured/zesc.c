/* zesc.c -- chunked escape materialisation.  Scratch experiment.
   Nothing here belongs to the repository.

   The baseline kernel (uj.c) reloads and re-masks a 32-byte window after every
   escape.  On a body whose escapes are close together that is one load plus
   one five-instruction mask per escape, and the window never advances when the
   escape is at offset 0 of it.  This kernel loads a 64-byte block once, derives
   one 64-bit backslash/control mask for the block, and consumes that mask:
   each escape costs its expansion only, and the run before it is copied with
   a plain 32-byte store (over-writing past the run is correct: every byte at
   or beyond the output cursor is rewritten by the next run or the next escape,
   and the caller guarantees 32 bytes of slack).

   The escape expansion keeps the baseline's byte-exact error offsets and the
   WTF-8 encoding of a lone surrogate; simple escapes are decoded inline, the
   \u form goes through the branch-free encoder. */
#ifndef ZESC_H
#define ZESC_H

#include <immintrin.h>

static const int8_t ZE_UNESC[256] = {
    [0 ... 255] = -1,
    ['"'] = '"', ['\\'] = '\\', ['/'] = '/', ['b'] = 8,
    ['f'] = 12, ['n'] = 10, ['r'] = 13, ['t'] = 9
};

static inline __m256i ze_maskv(__m256i v, __m256i vbs, __m256i v19) {
    __m256i ctl = _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v);
    __m256i bs = _mm256_cmpeq_epi8(v, vbs);
    return _mm256_or_si256(ctl, bs);
}

/* 64-bit mask of backslash-or-control bytes in the 64-byte block at p.
   The two 32-byte halves are kept so the run copy can reuse them. */
static inline __attribute__((always_inline)) uint64_t
ze_block_mask(const uint8_t *p, __m256i *v0, __m256i *v1) {
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    *v0 = _mm256_loadu_si256((const __m256i *)p);
    *v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
    uint64_t m0 = (uint32_t)_mm256_movemask_epi8(ze_maskv(*v0, vbs, v19));
    uint64_t m1 = (uint32_t)_mm256_movemask_epi8(ze_maskv(*v1, vbs, v19));
    return m0 | (m1 << 32);
}

/* copy len bytes (0 < len <= 64) from p to dst; over-writes up to 32 bytes
   past dst+len, which the caller's slack and the output cursor make harmless */
static inline __attribute__((always_inline)) void
ze_run(const uint8_t *p, uint64_t len, uint8_t *dst) {
    _mm256_storeu_si256((__m256i *)dst,
                        _mm256_loadu_si256((const __m256i *)p));
    if (len > 32)
        _mm256_storeu_si256((__m256i *)(dst + 32),
                            _mm256_loadu_si256((const __m256i *)(p + 32)));
}

/* Decode one escape at p[i] into dst+j.  Returns 0 on an invalid escape with
   *err set to the backslash offset, exactly like str_process. */
static inline __attribute__((always_inline)) int
ze_esc(const uint8_t *p, uint64_t n, uint64_t *ip, uint8_t *dst, uint64_t *jp,
       size_t *err) {
    uint64_t i = *ip;
    if (i + 1 >= n) { *err = (size_t)i; return 0; }
    uint8_t c1 = p[i + 1];
    int8_t sv = ZE_UNESC[c1];
    if (sv >= 0) {
        dst[*jp] = (uint8_t)sv;
        (*jp)++;
        *ip = i + 2;
        return 1;
    }
    if (c1 != 'u' || i + 6 > n) { *err = (size_t)i; return 0; }
    int h0 = UJ_HEX[p[i + 2]], h1 = UJ_HEX[p[i + 3]];
    int h2 = UJ_HEX[p[i + 4]], h3 = UJ_HEX[p[i + 5]];
    if ((h0 | h1 | h2 | h3) < 0) { *err = (size_t)i; return 0; }
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
            adv += 6;
        }
    }
    int len;
    uint32_t v = uj_enc_word(cp, &len);
    {
        uint64_t w = (uint64_t)v;
        memcpy(dst + *jp, &w, 8);
    }
    *jp += (uint64_t)len;
    *ip = i + adv;
    return 1;
}

/* dst must hold n + 32 bytes.  Returns the decoded length, UJ_FAIL on error. */
size_t ze_decode(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err) {
    uint64_t i = 0, j = 0;
    while (i + 64 <= n) {
        __m256i v0, v1;
        uint64_t m = ze_block_mask(p + i, &v0, &v1);
        (void)v0; (void)v1;
        uint64_t cur = 0;
        while (m) {
            unsigned bpos = (unsigned)__builtin_ctzll(m);
            if (bpos > cur) {
                ze_run(p + i + cur, bpos - cur, dst + j);
                j += bpos - cur;
            }
            uint64_t at = i + bpos;
            if (p[at] < 0x20) { *err = (size_t)at; return UJ_FAIL; }
            uint64_t idx = at;
            if (!ze_esc(p, n, &idx, dst, &j, err)) return UJ_FAIL;
            cur = idx - i;
            if (cur >= 64) break;
            m &= ~((1ULL << cur) - 1ULL);
        }
        if (cur < 64) {
            ze_run(p + i + cur, 64 - cur, dst + j);
            j += 64 - cur;
            i += 64;
        } else {
            i += cur;
        }
    }
    /* tail: one 32-byte window masked to the remaining body, so a short body
       is one load, one mask and one store whether or not it ends in an escape */
    while (i < n) {
        uint64_t rem = n - i;
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = (unsigned)_mm256_movemask_epi8(
            ze_maskv(v, _mm256_set1_epi8('\\'), _mm256_set1_epi8(0x1F)));
        if (rem < 32) m &= (1u << (unsigned)rem) - 1u;
        if (!m) {
            _mm256_storeu_si256((__m256i *)(dst + j), v);
            uint64_t adv = rem < 32 ? rem : 32;
            j += adv; i += adv;
            continue;
        }
        unsigned b = (unsigned)__builtin_ctz(m);
        if (b) {
            _mm256_storeu_si256((__m256i *)(dst + j), v);
            i += b; j += b;
        }
        if (p[i] < 0x20) { *err = (size_t)i; return UJ_FAIL; }
        uint64_t idx = i;
        if (!ze_esc(p, n, &idx, dst, &j, err)) return UJ_FAIL;
        i = idx;
    }
    return (size_t)j;
}

#endif /* ZESC_H */
