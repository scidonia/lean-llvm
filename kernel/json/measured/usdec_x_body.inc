/* usdec_x_body.inc -- one copy of the per-body list decoder (the body of
   us_dec_x), parameterised so a build can hold two shapes of it and pick one
   per document.  Scratch; included from usdec_gate.h.

   USDEC_NAME   the function name
   USDEC_ATTR   its linkage/attribute prefix
   USDEC_ESCFN  the escape step (us_esc for the out-of-line shape,
                us_esc_si for the shape whose `\u` stays out of line) */
USDEC_ATTR size_t
USDEC_NAME(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
           const uint32_t *xp, uint64_t *xj, uint64_t nxp, uint64_t pos0) {
    uint64_t k = *xj, i = 0, j = 0;
    uint64_t endp = pos0 + n;
#if US_XP_DIAG == 6
    /* floor probe: the body is copied and no position is looked at */
    (void)k; (void)endp;
    us_run(p, dst, n);
    *err = 0;
    return (size_t)n;
#endif
    while (k < nxp && (uint64_t)xp[k] < pos0) k++;
    while (k < nxp) {
        uint64_t q = (uint64_t)xp[k];
        if (q >= endp) break;
        k++;
        {
            uint64_t b = q - pos0;
#ifdef US_XP_TRACE
            us_xp_visited[us_xp_nvis++] = (uint32_t)q;
#endif
#if US_XP_DIAG != 2 && US_XP_DIAG != 3
            us_run_long(p + i, dst + j, b - i);
#endif
            j += b - i;
#if US_XP_DIAG == 3
            i = b + 1;
#else
            if (US_XP_DIAG != 1 && p[b] < 0x20) {
                *err = (size_t)b; *xj = k; return US_FAIL;
            }
            {
                uint64_t adv;
#if US_XP_DIAG == 1
                adv = 2;
#else
                if (!USDEC_ESCFN(p, n, b, dst, &j, &adv, err)) {
                    *xj = k;
                    return US_FAIL;
                }
#endif
                i = b + adv;
                /* A decoded escape consumes at most one further position: the
                   second `\u` of a surrogate pair, which is exactly the
                   adv == 12 case. */
                k += (adv == 12);
            }
#endif
        }
    }
#if US_XP_DIAG != 2 && US_XP_DIAG != 3
    us_run_long(p + i, dst + j, n - i);
#endif
    *xj = k;
    return (size_t)(j + (n - i));
}
