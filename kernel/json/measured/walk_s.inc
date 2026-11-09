/* walk_s.inc -- the index-stream tokenizer with the SIMD whitespace skip.
   Scratch; not part of the repository.

   od_step is the shipped tokenizer (byte loop over whitespace).  This is the
   same tokenizer with od_ws_skip substituted, so the gap-skip change can be
   priced without switching to masks at the same time. */
/* same scalar classification as the shipped od_step (branch chain), so the
   gap-skip comparison changes one thing only */
/* the visited counter is gate bookkeeping only; NO_VISITED drops the
   per-token increment for throughput builds */
#ifndef NO_VISITED
#define NO_VISITED 0
#endif
#if NO_VISITED
#define VINC(c) ((void)0)
#else
#define VINC(c) ((c)->visited++)
#endif

static inline int od_scalar_kind_chain(uint8_t ch) {
    if (ch == '-' || (ch >= '0' && ch <= '9')) return K_NUM;
    if (ch == 't') return K_TRUE;
    if (ch == 'f') return K_FALSE;
    if (ch == 'n') return K_NULL;
    return 0;
}
#define SCALAR_KIND od_scalar_kind_chain

__attribute__((always_inline)) static inline int od_step_s(OdCur *c, OdTok *t, int need_kind) {
    const uint8_t *b = c->b;
    uint64_t n = c->n;
    uint64_t p = od_ws_skip(b, c->cur, n);
    if (c->k >= c->nix) {
        if (p >= n) { c->cur = p; return OD_END; }
        uint64_t ee = p;
        while (ee < n && !is_delim(b[ee])) ee++;
        /* A delimiter at p is not a scalar and cannot consume itself.  The
           walk rejects it at p; advancing one byte only guarantees progress
           (without this, a trailing delimiter after the last index entry makes
           every walker loop forever). */
        if (ee == p) ee = p + 1;
        t->pos = p; t->end = ee; t->gap = 0;
        t->kind = need_kind ? SCALAR_KIND(b[p]) : 0;
        c->cur = ee;
        VINC(c);
        return OD_SCALAR;
    }
    uint64_t ip = IXP(c->ix[c->k]);
    if (ip == p) {
        uint8_t ch = b[p];
        if (ch == '"') {
            if (c->k + 1 >= c->nix) { od_fail(c, n, "unterminated"); return OD_ERR; }
            uint64_t cp = c->ix[c->k + 1];
#ifdef NO_CLOSE_CHECK
            if (cp >= n) { od_fail(c, n, "unterminated"); return OD_ERR; }
#else
            if (cp >= n || b[cp] != '"') { od_fail(c, n, "unterminated"); return OD_ERR; }
#endif
            if (cp <= p) { od_fail(c, p, "quote order"); return OD_ERR; }
            t->pos = p; t->end = cp;
            t->kind = need_kind ? K_STR : 0;
            c->cur = cp + 1;
            c->k += 2;
            VINC(c);
            return OD_STR;
        }
        t->pos = p; t->end = p + 1; t->kind = need_kind ? KINDT[ch] : 0;
        c->cur = p + 1;
        c->k += 1;
        VINC(c);
        return OD_STRUCT;
    }
    uint64_t ee = p;
    t->gap = 1;
    if (ip > p && !is_ws(b[ip - 1])) {
        ee = ip;
    } else {
        ee = od_ws_find(b, ee, ip);
    }
    t->pos = p; t->end = ee;
    t->kind = need_kind ? SCALAR_KIND(b[p]) : 0;
    c->cur = ee;
    VINC(c);
    return OD_SCALAR;
}

#define WNAME od_walk_s
#define WSTEP od_step_s
#define WGAPRE od_gap_recover
#include "walk_body.inc"
