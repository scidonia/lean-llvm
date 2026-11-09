/* walkz_body.inc -- od_walk_s grammar with zero-copy string bodies.
   Scratch; not part of the repository.

   Identical tokenizer and grammar to walk_body.inc's od_walk_s; only the
   string handler and its sink differ.  z == NULL keeps the accumulate-only
   form used by the find/decide levels. */

#ifndef WALKZ_BODY
#define WALKZ_BODY od_string_body_z
#endif
/* PF_NEXT: prefetch the input lines of the next PF_NEXT index entries before
   the current string body is processed.  The entry after a string pair is the
   delimiter; the one after it is usually the next string's opening quote, so
   this is the next body's first line with a body of lead time. */
#ifndef PF_NEXT
#define PF_NEXT 0
#endif

__attribute__((always_inline)) static inline uint64_t
od_walk_z(OdCur *c, int level, int validate, ZOut *z) {
    uint64_t acc = 0;
    OdTok t;
    for (;;) {
        int r = od_step_s(c, &t, level >= LV_DECIDE);
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
#if PF_NEXT > 0
        {
            uint64_t kk = c->k;
            uint64_t kk_end = kk + PF_NEXT;
            if (kk_end > c->nix) kk_end = c->nix;
            for (; kk < kk_end; kk++)
                __builtin_prefetch(c->b + IXP(c->ix[kk]), 0, 0);
        }
#endif
        if (z) {
            if (!WALKZ_BODY(c, z, c->b + t.pos + 1,
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

/* The stage-1 class prefilter form: a body whose blocks are all clean skips
   the backslash compare (control bytes are still located).  Not part of the
   second (fused) instantiation, which only needs the plain walk. */
#ifndef WALKZ_ONLY_MAIN
__attribute__((always_inline)) static inline uint64_t
od_walk_z_cls(OdCur *c, int level, int validate, ZOut *z,
              const uint8_t *cls, uint64_t nb) {
    uint64_t acc = 0;
    OdTok t;
    for (;;) {
        int r = od_step_s(c, &t, level >= LV_DECIDE);
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
            if (!od_value_pos(c))
                return od_fail(c, t.pos, "scalar where no value is allowed");
            if (!od_scalar_value(c, &t, z ? &z->ev : NULL, &acc)) {
                if (t.gap) od_gap_recover(c, &t);
                return 0;
            }
            od_after_value(c);
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
        uint64_t pos = t.pos + 1;
        uint64_t len = t.end - pos;
        int clean = 1;
        if (len) {
            uint64_t b0 = pos >> 6, b1 = (pos + len - 1) >> 6;
            unsigned cl = 0;
            for (uint64_t b = b0; b <= b1 && b < nb; b++) cl |= cls[b];
            clean = (cl == 0);
        }
        if (z) {
            if (!od_string_body_z_cls(c, z, c->b + pos, len, key, clean)) return 0;
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
#endif /* WALKZ_ONLY_MAIN */
