/* zf_impl.inc -- the fused string-body pass, generated once per
   (ZF_COPY, ZF_W) combination by zf.c.

   Reads a window of ZF_W bytes (or the remaining body), derives one mask of
   control-byte-or-backslash positions and consumes that mask: the clean run
   before a special is copied as whole vectors, a control byte fails at its own
   offset, a backslash goes through the escape helper (which fails at the
   backslash).  No second traversal, and no reload after an escape that stays
   inside the window.

   ZF_COPY 0  validate only; writes nothing, *outn = n (the span length).
   ZF_COPY 1  materialise every body: *outn = decoded length.
   ZF_COPY 2  materialise lazily: *escaped reports which form the body needs;
              a body with no escape is never written, and the clean prefix
              before the first escape is copied in one go at that point.

   Requires: ZF_NAME, ZF_COPY (0/1/2), ZF_W (32/64).
   dst needs n + 32 bytes when a body may be materialised.  Returns 1 with
   *outn (and *escaped) set, or 0 with *err = body-relative offset of the
   first offending byte. */
#ifndef ZF_ESC
#define ZF_ESC 0
#endif
#ifndef ZF_NOVAL
#define ZF_NOVAL 0
#endif
#ifndef ZF_FAST
#define ZF_FAST 0
#endif
#if ZF_FAST && ZF_COPY == 1
#error "ZF_FAST skips the first chunk, so it cannot be used when every byte is copied"
#endif

static inline __attribute__((always_inline)) int
ZF_NAME(const uint8_t *p, uint64_t n, uint8_t *dst, int *escaped,
        uint64_t *outn, uint64_t *err) {
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    uint64_t i = 0, j = 0;
    int esc = 0;
#if ZF_FAST
    /* Empty-mask exit for a body that starts clean.  The common short plain
       body is one 32-byte load, one mask and one test: the 64-byte window,
       its tail mask and the escape ladder are not entered at all.  When the
       first chunk is clean but the body continues, the loop starts at 32; it
       reads absolute offsets from p, so nothing else changes.  A first chunk
       that holds a control byte or a backslash starts at 0 as before. */
#if ZF_FAST == 2
    /* Short-body form: only a body that fits one 32-byte chunk takes the
       exit, so a longer body pays no extra load and the window loop still
       starts at 0. */
    if (n && n <= 32) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        uint64_t m0 = (uint64_t)(uint32_t)_mm256_movemask_epi8(
            _mm256_or_si256(_mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0),
                            _mm256_cmpeq_epi8(v0, vbs)));
        if (n < 32) m0 &= (1ULL << n) - 1ULL;
        if (!m0) i = n;
    }
#else
    if (n) {
        uint64_t w0 = n < 32 ? n : 32;
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        uint64_t m0 = (uint64_t)(uint32_t)_mm256_movemask_epi8(
            _mm256_or_si256(_mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0),
                            _mm256_cmpeq_epi8(v0, vbs)));
        if (w0 < 32) m0 &= (1ULL << w0) - 1ULL;
        if (!m0) i = w0;
    }
#endif
#endif
    while (i < n) {
#ifdef ZF_COUNT
        zf_win_count++;
#endif
        uint64_t rem = n - i;
        uint64_t win = rem < ZF_W ? rem : ZF_W;
#if ZF_W == 64
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + i));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + i + 32));
        uint64_t m =
            (uint64_t)(uint32_t)_mm256_movemask_epi8(
                _mm256_or_si256(
                    _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0),
                    _mm256_cmpeq_epi8(v0, vbs))) |
            ((uint64_t)(uint32_t)_mm256_movemask_epi8(
                 _mm256_or_si256(
                     _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1),
                     _mm256_cmpeq_epi8(v1, vbs))) << 32);
#else
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + i));
        uint64_t m = (uint64_t)(uint32_t)_mm256_movemask_epi8(
            _mm256_or_si256(_mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0),
                            _mm256_cmpeq_epi8(v0, vbs)));
#endif
        if (win < ZF_W) m &= (1ULL << win) - 1ULL;
        uint64_t cur = 0;
        while (m) {
            unsigned b = (unsigned)__builtin_ctzll(m);
#if ZF_COPY == 0
            (void)b; (void)cur; (void)j;
#elif ZF_COPY == 1
            if (b > cur) { zf_run(p + i + cur, b - cur, dst + j); j += b - cur; }
#elif ZF_COPY == 2
            if (esc && b > cur) {
                zf_run(p + i + cur, b - cur, dst + j);
                j += b - cur;
            }
#else
            if (esc && b > cur) j += b - cur;       /* length only */
#endif
            uint64_t at = i + b;
#ifdef ZF_COUNT
            zf_esc_count++;
#endif
            if (p[at] < 0x20) { *err = at; return 0; }
#if ZF_COPY == 2
            if (!esc) {
                /* first escape in this body: the clean prefix becomes output.
                   It can be longer than the window, so it is copied with the
                   length-agnostic loop. */
                if (at) zf_copy(p, at, dst);
                j = at;
                esc = 1;
            }
#elif ZF_COPY == 3
            if (!esc) { j = at; esc = 1; }
#endif
            uint64_t adv;
#if ZF_NOVAL
            if (!zf_esc_cp_t(p, n, at, dst, &j, &adv, err)) return 0;
#elif ZF_ESC
#if ZF_COPY == 0
            if (!zf_esc_bf_val(p, n, at, &adv, err)) return 0;
#elif ZF_COPY == 2
            if (!zf_esc_bf_cp(p, n, at, dst, &j, &adv, err)) return 0;
#else
            if (!zf_esc_bf_cnt(p, n, at, &j, &adv, err)) return 0;
#endif
#else
#if ZF_COPY == 0
            if (!zf_esc_val(p, n, at, &adv, err)) return 0;
#elif ZF_COPY == 2
            if (!zf_esc_cp(p, n, at, dst, &j, &adv, err)) return 0;
#else
            if (!zf_esc_cnt(p, n, at, &j, &adv, err)) return 0;
#endif
#endif
            cur = b + adv;
            if (cur >= win) break;      /* escape crossed the window */
            m &= ~((1ULL << cur) - 1ULL);
        }
        if (cur < win) {
#if ZF_COPY == 1
            zf_run(p + i + cur, win - cur, dst + j); j += win - cur;
#elif ZF_COPY == 2
            if (esc) { zf_run(p + i + cur, win - cur, dst + j); j += win - cur; }
#elif ZF_COPY == 3
            if (esc) j += win - cur;                /* length only */
#endif
            i += win;
        } else {
            i += cur;
        }
    }
#if ZF_COPY == 0
    (void)dst; (void)j;
    *escaped = 0;
    *outn = n;
#elif ZF_COPY == 1
    (void)esc;
    *escaped = 1;
    *outn = j;
#else
#if ZF_COPY == 3
    (void)dst;
#endif
    *escaped = esc;
    *outn = esc ? j : n;
#endif
    return 1;
}
