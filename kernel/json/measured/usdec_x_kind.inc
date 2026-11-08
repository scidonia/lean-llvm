/* usdec_x_kind.inc -- the per-body list decoder reading the carried kind.
   Scratch.

   Same walk as usdec_x_body.inc, one difference: the escape class comes from
   stage 1's per-block kind record (`uk`, one word per 64-byte document block),
   loaded from the escape position before the run copy, so the class does not
   wait on the body byte.

   USDEC_NAME   the function name
   USDEC_ATTR   its linkage/attribute prefix
   USDEC_ESCFN  the escape step: us_esc_k_if, us_esc_k_jmp or us_esc_k_sw */
USDEC_ATTR size_t
USDEC_NAME(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
           const uint32_t *xp, uint64_t *xj, uint64_t nxp, uint64_t pos0,
           const uint64_t *uk) {
    uint64_t k = *xj, i = 0, j = 0;
    uint64_t endp = pos0 + n;
    while (k < nxp && (uint64_t)xp[k] < pos0) k++;
    while (k < nxp) {
        uint64_t q = (uint64_t)xp[k];
        if (q >= endp) break;
        k++;
        {
            uint64_t b = q - pos0;
            /* the class is a function of the position alone: read it before
               the copy so its load overlaps the run store */
            unsigned kind = (unsigned)((uk[q >> 6] >> (q & 63)) & 1);
#ifdef US_XP_TRACE
            us_xp_visited[us_xp_nvis++] = (uint32_t)q;
#endif
            us_run_long(p + i, dst + j, b - i);
            j += b - i;
            if (p[b] < 0x20) {
                *err = (size_t)b; *xj = k; return US_FAIL;
            }
            {
                uint64_t adv;
                if (!USDEC_ESCFN(p, n, b, dst, &j, &adv, err, kind)) {
                    *xj = k;
                    return US_FAIL;
                }
                i = b + adv;
                /* A decoded escape consumes at most one further position:
                   the second `\u` of a surrogate pair (adv == 12). */
                k += (adv == 12);
            }
        }
    }
    us_run_long(p + i, dst + j, n - i);
    *xj = k;
    return (size_t)(j + (n - i));
}
