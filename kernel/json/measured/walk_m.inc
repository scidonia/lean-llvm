/* walk_m.inc -- masks-direct tokenizer and walk.
   Scratch; not part of the repository.

   The index stream is gone: token positions come from the per-block candidate
   mask, iterated with ctz.  The block cursor (bb, bit) always names the next
   unconsumed candidate bit, so a token is "taken" by advancing it and a scalar
   is returned without advancing (the following token stays pending).

   MASK_SWAR=1 skips whitespace 16 bytes at a time with SSE2 compares instead
   of a byte loop; MASK_SWAR=0 is the byte loop, for the ablation. */

#ifndef MASK_SWAR
#define MASK_SWAR 1
#endif

/* first byte >= p that is not JSON whitespace */
__attribute__((always_inline)) static inline uint64_t od_ws_skip(const uint8_t *b,
        uint64_t p, uint64_t n) {
    if (p >= n) return p;
    if (!is_ws(b[p])) return p;             /* minified input: nothing to do */
#if MASK_SWAR == 2
    while (p + 32 <= n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(b + p));
        __m256i w = _mm256_or_si256(
            _mm256_or_si256(_mm256_cmpeq_epi8(v, _mm256_set1_epi8(' ')),
                            _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\t'))),
            _mm256_or_si256(_mm256_cmpeq_epi8(v, _mm256_set1_epi8('\n')),
                            _mm256_cmpeq_epi8(v, _mm256_set1_epi8('\r'))));
        uint32_t m = (uint32_t)_mm256_movemask_epi8(w);
        if (m != 0xFFFFFFFFu) return p + (uint64_t)__builtin_ctz(~m);
        p += 32;
    }
#elif MASK_SWAR == 1
    while (p + 16 <= n) {
        __m128i v = _mm_loadu_si128((const __m128i *)(b + p));
        __m128i w = _mm_or_si128(
            _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8(' ')),
                         _mm_cmpeq_epi8(v, _mm_set1_epi8('\t'))),
            _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('\n')),
                         _mm_cmpeq_epi8(v, _mm_set1_epi8('\r'))));
        uint32_t m = (uint32_t)_mm_movemask_epi8(w);
        if (m != 0xFFFFu) return p + (uint64_t)__builtin_ctz(~m);
        p += 16;
    }
#endif
    while (p < n && is_ws(b[p])) p++;
    return p;
}

/* first whitespace byte in [p, lim), or lim.  p is known non-whitespace. */
__attribute__((always_inline)) static inline uint64_t od_ws_find(const uint8_t *b,
        uint64_t p, uint64_t lim) {
#if MASK_SWAR
    while (p + 16 <= lim) {
        __m128i v = _mm_loadu_si128((const __m128i *)(b + p));
        __m128i w = _mm_or_si128(
            _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8(' ')),
                         _mm_cmpeq_epi8(v, _mm_set1_epi8('\t'))),
            _mm_or_si128(_mm_cmpeq_epi8(v, _mm_set1_epi8('\n')),
                         _mm_cmpeq_epi8(v, _mm_set1_epi8('\r'))));
        uint32_t m = (uint32_t)_mm_movemask_epi8(w);
        if (m) return p + (uint64_t)__builtin_ctz(m);
        p += 16;
    }
#endif
    while (p < lim && !is_ws(b[p])) p++;
    return p;
}

/* next unconsumed candidate position, or UINT64_MAX.  The remaining bits of
   the current block live in the cursor, so a token costs one ctz and one
   clear rather than a fresh word load. */
__attribute__((always_inline)) static inline uint64_t od_peek(OdCur *c,
        uint64_t *pbb, uint64_t *pbit) {
    while (c->bits == 0) {
        if (c->bb >= c->nb) return UINT64_MAX;
        uint64_t bits = c->cand[c->bb];
        if (c->bb + 1 == c->nb && (c->n & 63))  /* never read the padding */
            bits &= ~0ULL >> (64 - (c->n & 63));
        c->bits = bits;
        if (!bits) c->bb++;                     /* block with no tokens */
    }
    uint64_t o = (uint64_t)__builtin_ctzll(c->bits);
    *pbb = c->bb;
    *pbit = o;
    return (c->bb << 6) + o;
}

__attribute__((always_inline)) static inline void od_take(OdCur *c,
        uint64_t bb, uint64_t bit) {
    (void)bb; (void)bit;
    c->bits &= c->bits - 1;
    if (!c->bits) c->bb++;                      /* next peek loads the next block */
}

#ifndef SCALAR_TABLE
#define SCALAR_TABLE 0
#endif

/* one load, no branch tree: every byte maps to its token kind.  Used only by
   the SCALAR_TABLE ablation; the default is the shipped branch chain. */
static const int8_t ODKIND[256] = {
    ['0' ... '9'] = K_NUM, ['-'] = K_NUM,
    ['t'] = K_TRUE, ['f'] = K_FALSE, ['n'] = K_NULL,
    [','] = K_COMMA, [':'] = K_COLON, ['{'] = K_OBJ, ['}'] = K_OBJ_END,
    ['['] = K_ARR, [']'] = K_ARR_END
};

__attribute__((always_inline)) static inline int od_scalar_kind(uint8_t ch) {
#if SCALAR_TABLE
    return ODKIND[ch];
#else
    if (ch == '-' || (ch >= '0' && ch <= '9')) return K_NUM;
    if (ch == 't') return K_TRUE;
    if (ch == 'f') return K_FALSE;
    if (ch == 'n') return K_NULL;
    return 0;
#endif
}

/* The masks-direct tokenizer.  Same contract as od_step: locate the next
   token, leave c->cur after it, advance the mask cursor only when a token is
   consumed. */
__attribute__((always_inline)) static inline int od_step_m(OdCur *c, OdTok *t, int need_kind) {
    const uint8_t *b = c->b;
    uint64_t n = c->n;
    uint64_t p = c->cur;
    uint64_t q = od_ws_skip(b, p, n);
    uint64_t pbb, pbit;
    uint64_t ip = od_peek(c, &pbb, &pbit);
    if (ip == UINT64_MAX) {
        if (q >= n) { c->cur = q; return OD_END; }
        /* no candidate left: the remainder is a top-level scalar (or junk) */
        uint64_t ee = q;
        while (ee < n && !is_delim(b[ee])) ee++;
        t->pos = q; t->end = ee; t->gap = 0;
        t->kind = need_kind ? od_scalar_kind(b[q]) : 0;
        c->cur = ee;
        c->visited++;
        return OD_SCALAR;
    }
    if (ip == q) {
        uint8_t ch = b[q];
        if (ch == '"') {                        /* string: the pair's close is next */
            od_take(c, pbb, pbit);
            uint64_t cbb, cbit;
            uint64_t cp = od_peek(c, &cbb, &cbit);
#ifdef NO_CLOSE_CHECK
            if (cp == UINT64_MAX || cp >= n) { od_fail(c, n, "unterminated"); return OD_ERR; }
#else
            if (cp == UINT64_MAX || cp >= n || b[cp] != '"') {
                od_fail(c, n, "unterminated"); return OD_ERR;
            }
#endif
            if (cp <= q) { od_fail(c, q, "quote order"); return OD_ERR; }
            t->pos = q; t->end = cp; t->gap = 0;
            t->kind = need_kind ? K_STR : 0;
            c->cur = cp + 1;
            od_take(c, cbb, cbit);
            c->visited++;
            return OD_STR;
        }
        t->pos = q; t->end = q + 1; t->gap = 0;
        t->kind = need_kind ? KINDT[ch] : 0;
        c->cur = q + 1;
        od_take(c, pbb, pbit);
        c->visited++;
        return OD_STRUCT;
    }
    /* a scalar occupies the gap [q, ip) */
    uint64_t ee = q;
    t->gap = 1;
    if (ip > q && !is_ws(b[ip - 1])) {
        ee = ip;
    } else {
        ee = od_ws_find(b, ee, ip);
    }
    t->pos = q; t->end = ee;
    t->kind = need_kind ? od_scalar_kind(b[q]) : 0;
    c->cur = ee;
    c->visited++;
    return OD_SCALAR;
}

/* same recovery as od_gap_recover, reading the pending candidate as the bound */
static void od_gap_recover_m(OdCur *c, const OdTok *t) {
    const uint8_t *b = c->b;
    uint64_t pbb, pbit;
    uint64_t ip = od_peek(c, &pbb, &pbit);
    if (ip == UINT64_MAX) ip = c->n;
    uint64_t ee = t->pos;
    while (ee < ip && !is_ws(b[ee])) ee++;
    if (ee == ip) return;
    OdTok t2 = *t;
    t2.end = ee;
    uint8_t ch = b[t2.pos];
    if (ch == '-' || (ch >= '0' && ch <= '9')) {
        double d; size_t ei;
        if (!num_fast(b + t2.pos, t2.end - t2.pos, &d, &ei)) {
            err_set(c->e, t2.pos + ei, "number");
            return;
        }
    } else {
        const char *lit; uint32_t ln;
        if (ch == 't') { lit = "true"; ln = 4; }
        else if (ch == 'f') { lit = "false"; ln = 5; }
        else if (ch == 'n') { lit = "null"; ln = 4; }
        else { err_set(c->e, t2.pos, "scalar"); return; }
        size_t ei;
        if (!lit_check(b + t2.pos, t2.end - t2.pos, lit, ln, &ei)) {
            err_set(c->e, t2.pos + ei, "literal");
            return;
        }
    }
    uint64_t s2 = ee;
    while (s2 < ip && is_ws(b[s2])) s2++;
    err_set(c->e, s2, "extra token");
}

/* od_walk over masks.  Body identical to od_walk except the tokenizer and the
   recovery helper. */
__attribute__((always_inline)) static inline uint64_t od_walk_m(OdCur *c, int level, int validate, int raw, Out *o) {
    uint64_t acc = 0;
    OdTok t;
    for (;;) {
        int r = od_step_m(c, &t, level >= LV_DECIDE);
        if (r == OD_ERR) return 0;
        if (r == OD_END) break;
        if (level == LV_FIND) { acc += t.pos; continue; }
        if (level == LV_DECIDE) { acc = acc * 3 + t.kind + t.pos; continue; }

        if (r == OD_STRUCT) {
            uint32_t kind = t.kind;
            if (validate) {
                switch (kind) {
                case K_COMMA: {
                    if (c->sp == 0) return od_fail(c, t.pos, "comma");
                    uint32_t ti = c->sp - 1;
                    if (c->ctype[ti] == C_OBJ) {
                        if (c->cst[ti] != 3) return od_fail(c, t.pos, "comma");
                        c->cst[ti] = 4;
                    } else {
                        if (c->cst[ti] != 1) return od_fail(c, t.pos, "comma");
                        c->cst[ti] = 2;
                    }
                    break;
                }
                case K_COLON: {
                    if (c->sp == 0) return od_fail(c, t.pos, "colon");
                    uint32_t ti = c->sp - 1;
                    if (c->ctype[ti] != C_OBJ || c->cst[ti] != 1)
                        return od_fail(c, t.pos, "colon");
                    c->cst[ti] = 2;
                    break;
                }
                case K_OBJ: case K_ARR: {
                    if (!od_value_pos(c))
                        return od_fail(c, t.pos, "container where no value is allowed");
                    if (c->sp >= MAXD) return od_fail(c, t.pos, "nesting limit");
                    c->ctype[c->sp] = (kind == K_OBJ) ? C_OBJ : C_ARR;
                    c->cst[c->sp] = 0;
                    c->sp++;
                    break;
                }
                case K_OBJ_END: case K_ARR_END: {
                    if (c->sp == 0) return od_fail(c, t.pos, "close");
                    uint32_t ti = c->sp - 1;
                    uint8_t want = (kind == K_OBJ_END) ? C_OBJ : C_ARR;
                    if (c->ctype[ti] != want) return od_fail(c, t.pos, "bracket type");
                    uint8_t st = c->cst[ti];
                    int ok = (want == C_OBJ) ? (st == 3 || st == 0)
                                             : (st == 1 || st == 0);
                    if (!ok) return od_fail(c, t.pos, "trailing comma");
                    c->sp--;
                    od_after_value(c);
                    break;
                }
                default:
                    return od_fail(c, t.pos, "kind");
                }
            }
            if (o) {
                if (kind == K_OBJ) out_tag(o, T_OBJ);
                else if (kind == K_OBJ_END) out_tag(o, T_OBJ_END);
                else if (kind == K_ARR) out_tag(o, T_ARR);
                else if (kind == K_ARR_END) out_tag(o, T_ARR_END);
            } else {
                acc = touch_u64(acc, kind);
            }
            continue;
        }

        if (r == OD_SCALAR) {
            if (validate) {
                if (!od_value_pos(c))
                    return od_fail(c, t.pos, "scalar where no value is allowed");
                if (!od_scalar_value(c, &t, o, &acc)) {
                    if (t.gap) od_gap_recover_m(c, &t);
                    return 0;
                }
                od_after_value(c);
            } else {
                if (!od_scalar_value(c, &t, o, &acc)) {
                    if (t.gap) od_gap_recover_m(c, &t);
                    return 0;
                }
            }
            continue;
        }

        /* OD_STR */
        int key = 0;
        if (validate) {
            int val = od_value_pos(c);
            if (c->sp > 0 && c->ctype[c->sp - 1] == C_OBJ) {
                uint8_t st = c->cst[c->sp - 1];
                if (st == 0 || st == 4) key = 1;
            }
            if (!key && !val)
                return od_fail(c, t.pos, "string where no value is allowed");
        }
        if (o) out_tag(o, key ? T_KEY : T_STR);
        else acc = touch_u64(acc, key ? T_KEY : T_STR);
        if (!od_string_body(c, c->b + t.pos + 1, t.end - t.pos - 1, raw, o, &acc))
            return 0;
        if (validate) {
            if (key) c->cst[c->sp - 1] = 1;
            else od_after_value(c);
        }
    }
    if (validate) {
        if (c->sp != 0) return od_fail(c, c->n, "unclosed container");
        if (!c->root_done) return od_fail(c, c->n, "no value");
    }
    c->e->ok = 1;
    c->e->off = 0;
    c->e->msg = "ok";
    return acc;
}
