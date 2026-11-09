/* str3body.inc -- string body dispatch by the stage-1 escape-class mask.
   Scratch; not part of the repository.

   od_str_class answers two questions about the body [pos, endpos) from the
   stage-1 escape masks alone -- no input byte is re-read:
     has_esc  the body contains a backslash (so it needs unescaping)
     has_u    the body contains a \u escape
   The body is then sent to uj3_plain, uj3_simple or the existing \u kernel.
   od_string_body_e is always inlined into the walk, so paths 1 and 2 have no
   call boundary. */

#ifdef PATH_COUNT
static uint64_t g_path_n[3];
#endif

/* Block class: bit0 = the block holds an escape, bit1 = it holds a \u.
   The byte array is input/64 and stays in L1; the 64-bit mask is only read
   for a body whose block class says \u. */
__attribute__((always_inline)) static inline int
od_str_path(const OdCur *c, uint64_t pos, uint64_t endpos) {
    const uint64_t *esc = c->esc;
    uint64_t b0 = pos >> 6, b1 = (endpos - 1) >> 6;
    unsigned lo = (unsigned)(pos & 63);
    uint64_t w = esc[b0];
    if (b0 == b1) {
        unsigned k = (unsigned)(endpos - pos);
        uint64_t x = w >> lo;
        if (k < 64u - lo) x &= (1ULL << k) - 1;
        return (x == 0) ? 0 : (((x & (x >> 1)) != 0) ? 2 : 1);
    }
    uint64_t x = w >> lo;
    int he = x != 0;
    int hu = (x & (x >> 1)) != 0;
    uint64_t last = x >> (63 - lo);
    for (uint64_t b = b0 + 1; b <= b1; b++) {
        w = esc[b];
        if (b == b1) {
            unsigned hi = (unsigned)((endpos - 1) & 63);
            if (hi < 63) w &= (1ULL << (hi + 1)) - 1;
        }
        he |= w != 0;
        hu |= (w & ((w << 1) | last)) != 0;
        last = w >> 63;
    }
    return !he ? 0 : (hu ? 2 : 1);
}

/* path 0 plain, 1 ladder, 2 full kernel; class byte first, mask only when
   the body's blocks say \u and the cursor is exact */
__attribute__((always_inline)) static inline int
od_str_dispatch(const OdCur *c, uint64_t pos, uint64_t len) {
#ifdef ABL_FORCE_FULL
    return 2;                     /* named ablation: ignore the mask */
#endif
    if (!len) return 0;
    uint64_t b0 = pos >> 6, b1 = (pos + len - 1) >> 6;
    unsigned cl = c->cls[b0];
    for (uint64_t b = b0 + 1; b <= b1; b++) cl |= c->cls[b];
    if (cl == 0) return 0;
    if (cl == 1 || c->twoway) return 1;
    return c->exact ? od_str_path(c, pos, pos + len) : 2;
}

__attribute__((always_inline)) static inline int
od_string_body_e(OdCur *c, const uint8_t *p, uint64_t len, int raw, Out *o,
                 uint64_t *acc) {
#ifdef SKIP_STR
    if (!o) { *acc = touch_u64(*acc, len); return 1; }
#endif
    uint64_t pos = (uint64_t)(p - c->b);

    if (!o) {
        if (raw && c->trusting) { *acc = touch_bytes(p, len, *acc); return 1; }
        if (raw) {
            uint64_t ctrl = 0;
            int bs = plain_scan_acc(p, len, acc, &ctrl);
            if (bs < 0) return od_fail(c, pos + ctrl, "string");
            return 1;
        }
        int path = od_str_dispatch(c, pos, len);
        out_reserve(&g_sbuf, (size_t)len + 32);
        size_t ei = 0;
        uint64_t sacc = 0;
        size_t outn;
        if (path == 0) outn = uj3_plain(p, len, g_sbuf.b, &sacc, 1, &ei);
        else if (path == 1) outn = uj3_simple(p, len, g_sbuf.b, &sacc, 1, &ei);
        else outn = uj_decode_acc(p, len, g_sbuf.b, &sacc, &ei);
        if (outn == (size_t)-1) return od_fail(c, pos + ei, "string");
        g_sbuf.len = outn;
        *acc += sacc;
        return 1;
    }
    if (o->hash) {
        int path = od_str_dispatch(c, pos, len);
        out_reserve(&g_sbuf, (size_t)len + 32);
        size_t ei = 0;
        size_t outn;
        if (path == 0) outn = uj3_plain(p, len, g_sbuf.b, NULL, 0, &ei);
        else if (path == 1) outn = uj3_simple(p, len, g_sbuf.b, NULL, 0, &ei);
        else outn = uj_decode(p, len, g_sbuf.b, &ei);
        if (outn == (size_t)-1) return od_fail(c, pos + ei, "string");
        out_u32(o, (uint32_t)outn);
        out_raw(o, g_sbuf.b, outn);
        return 1;
    }
    int path = od_str_dispatch(c, pos, len);
    out_reserve(o, (size_t)len + 4 + 32);
    uint8_t *d = o->b + o->len;
    size_t ei = 0;
    size_t outn;
    if (path == 0) outn = uj3_plain(p, len, d + 4, NULL, 0, &ei);
    else if (path == 1) outn = uj3_simple(p, len, d + 4, NULL, 0, &ei);
    else outn = uj_decode(p, len, d + 4, &ei);
    if (outn == (size_t)-1) return od_fail(c, pos + ei, "string");
    uint32_t v = (uint32_t)outn;
    d[0] = (uint8_t)v; d[1] = (uint8_t)(v >> 8);
    d[2] = (uint8_t)(v >> 16); d[3] = (uint8_t)(v >> 24);
    o->len += 4 + outn;
    return 1;
}
