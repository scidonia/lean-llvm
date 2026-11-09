/* walk_body.inc -- od_walk's body, parameterized by the tokenizer.
   Scratch; not part of the repository.

   Define WNAME, WSTEP and WGAPRE before including this file.  WSTR selects
   the string-body handler and defaults to od_string_body.  It exists so the
   same grammar and value code is compiled against each tokenizer, which is what
   makes the index/masks and byte-loop/SIMD gap-skip comparisons like-for-like. */
#ifndef WSTR
#define WSTR od_string_body
#endif
__attribute__((always_inline)) static inline uint64_t WNAME(OdCur *c, int level, int validate, int raw, Out *o) {
    uint64_t acc = 0;
    OdTok t;
    for (;;) {
        int r = WSTEP(c, &t, level >= LV_DECIDE);
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
            if (o) { if (kind <= K_ARR_END) out_tag(o, (uint8_t)kind); }
            else acc = touch_u64(acc, kind);
#else
            if (o) {
                if (kind == K_OBJ) out_tag(o, T_OBJ);
                else if (kind == K_OBJ_END) out_tag(o, T_OBJ_END);
                else if (kind == K_ARR) out_tag(o, T_ARR);
                else if (kind == K_ARR_END) out_tag(o, T_ARR_END);
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
                if (!od_scalar_value(c, &t, o, &acc)) {
                    if (t.gap) WGAPRE(c, &t);
                    return 0;
                }
                od_after_value(c);
            } else {
                if (!od_scalar_value(c, &t, o, &acc)) {
                    if (t.gap) WGAPRE(c, &t);
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
        if (!WSTR(c, c->b + t.pos + 1, t.end - t.pos - 1, raw, o, &acc))
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
#undef WNAME
#undef WSTEP
#undef WGAPRE
#undef WSTR
