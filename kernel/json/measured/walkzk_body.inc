/* walkzk_body.inc -- od_walk_z with the token kind read from the packed index
   entry (emit24.c) instead of the input byte and the kind table.  Scratch. */

__attribute__((always_inline)) static inline int od_step_sk(OdCur *c, OdTok *t, int need_kind) {
    const uint8_t *b = c->b;
    uint64_t n = c->n;
    uint64_t p = od_ws_skip(b, c->cur, n);
    if (c->k >= c->nix) {
        if (p >= n) { c->cur = p; return OD_END; }
        uint64_t ee = p;
        while (ee < n && !is_delim(b[ee])) ee++;
        t->pos = p; t->end = ee; t->gap = 0;
        t->kind = need_kind ? SCALAR_KIND(b[p]) : 0;
        c->cur = ee;
        c->visited++;
        return OD_SCALAR;
    }
    uint32_t ent = c->ix[c->k];
    uint64_t ip = (uint64_t)(ent >> E24_SHIFT);
    uint32_t kind = ent & 31u;
    if (ip == p) {
        if (kind == K_STR) {
            if (c->k + 1 >= c->nix) { od_fail(c, n, "unterminated"); return OD_ERR; }
            uint64_t cp = (uint64_t)(c->ix[c->k + 1] >> E24_SHIFT);
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
            c->visited++;
            return OD_STR;
        }
        t->pos = p; t->end = p + 1; t->kind = need_kind ? kind : 0;
        c->cur = p + 1;
        c->k += 1;
        c->visited++;
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
    c->visited++;
    return OD_SCALAR;
}

__attribute__((always_inline)) static inline uint64_t
od_walk_zk(OdCur *c, int level, int validate, ZOut *z) {
    uint64_t acc = 0;
    OdTok t;
    for (;;) {
        int r = od_step_sk(c, &t, level >= LV_DECIDE);
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
#if Z_TAG_ID
            /* K_OBJ..K_ARR_END are T_OBJ..T_ARR_END, so the tag is the kind */
            if (z) { if (kind <= K_ARR_END) out_tag(&z->ev, (uint8_t)kind); }
            else acc = touch_u64(acc, kind);
#else
            if (z) {
                if (kind == K_OBJ) out_tag(&z->ev, T_OBJ);
                else if (kind == K_OBJ_END) out_tag(&z->ev, T_OBJ_END);
                else if (kind == K_ARR) out_tag(&z->ev, T_ARR);
                else if (kind == K_ARR_END) out_tag(&z->ev, T_ARR_END);
            } else {
                acc = touch_u64(acc, kind);
            }
#endif
            continue;
        }

        if (r == OD_SCALAR) {
            if (validate) {
                if (!od_value_pos(c))
                    return od_fail(c, t.pos, "scalar where no value is allowed");
                if (!od_scalar_value(c, &t, z ? &z->ev : NULL, &acc)) {
                    if (t.gap) od_gap_recover(c, &t);
                    return 0;
                }
                od_after_value(c);
            } else {
                if (!od_scalar_value(c, &t, z ? &z->ev : NULL, &acc)) {
                    if (t.gap) od_gap_recover(c, &t);
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
        if (z) {
            if (!od_string_body_z(c, z, c->b + t.pos + 1,
                                  t.end - t.pos - 1, key)) return 0;
        } else {
            acc = touch_u64(acc, key ? T_KEY : T_STR);
        }
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

