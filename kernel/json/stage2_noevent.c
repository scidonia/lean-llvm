/* stage2_noevent.c -- the no-event stage 2: the certified walk's validation and
   body work, with the event record and the arena replaced by the consumer's
   reading accumulated directly.

   The helper text is the certified unit's own: `stage2.c` is included under a
   rename of its entry point, so `s2_string_body`, `num_fast_el1`,
   `od_scalar_value`, `od_gap_recover`, `is_ws`, the tag constants, `US_SLACK`
   and the refusal record are that file's text, byte for byte.  `lit_check` is
   in the unit too, because the renamed certified entry calls it, but this
   walk's literal path is the one helper the unit adds, `ne_lit`, below.  The
   include also defines the renamed certified entry, which this unit never
   calls; it is the second global `stage2_noevent.h` records.

   The walk below is the same per-entry dispatch, written as the explicit
   state machine the certified walk's value-position and after-value rules
   unfold to.  Each refusal is the certified walk's, at the same offset: the
   structural rules, the number and literal rules, the string-body rules and the
   end-of-stream rules.  A string body is decoded through
   `s2_string_body` into the caller's scratch and consumed before the next
   body, because the fold's arena sum is order-independent over disjoint
   bodies and the encoded record's offset is the running decoded extent, which
   this unit maintains as `alen`.

   The three accumulations, and where the fold makes them:

     arena  the sum of every decoded escaped body's bytes.  The certified
            consumer sums `dst[0..*ndst)`, and `dst` holds exactly those bytes
            in document order, so the per-body sum here is that same sum.
     terms  for every event, the tag byte and the record's `len` and `payload`
            words: a structural token contributes its tag alone; a scalar its
            tag; a number `T_NUM` and the value's eight IEEE bytes; a plain
            string or key its tag, the span's length and the span record
            `(offset | 1 << 63)`; an escaped string or key its tag, the decoded
            length and the decoded body's arena offset.
     tokens one per event, which is also the build-mode consumer's `values`.

   `sum` is `arena + terms`, a `uint64_t`; the consumer's exact mathematical sum
   is that word when the sum is below `2 ^ 64` (`stage2_noevent.h`). */
#include "stage2_noevent.h"

#define leanllvm_json_stage2 leanllvm_json_stage2_noevent_lib
#include "stage2.c"
#undef leanllvm_json_stage2


/* The literal check, with the literal packed into an integer rather than
   addressed through a string.  The emitted body then carries the byte
   comparisons and no reference to a module global; the fragment the records
   are stated over has no global representation, and a pointer to a literal
   would be exactly that.  Its rule is the certified `lit_check`'s
   (`kernel/json/stage2.c`): `m = min(n, ln)`, the first differing byte under
   `m`, and `m` when the lengths differ.  That this helper returns that verdict
   and that offset is the refinement obligation the body's proof carries and
   what the differential exercises; the code below does not establish it. */
#define NE_LIT_TRUE  0x65757274ULL            /* "true"  */
#define NE_LIT_FALSE 0x65736C6166ULL          /* "false" */
#define NE_LIT_NULL  0x6C6C756EULL            /* "null"  */

static inline int ne_lit(const uint8_t *q, uint64_t n, uint64_t lit,
                         uint32_t ln, size_t *ei) {
    for (uint32_t i = 0; i < ln; i++) {
        if (i >= n) { *ei = (size_t)i; return 0; }
        if (q[i] != (uint8_t)(lit >> (8 * i))) { *ei = (size_t)i; return 0; }
    }
    if (n != ln) { *ei = (size_t)ln; return 0; }
    return 1;
}

uint64_t leanllvm_json_stage2_noevent(const uint8_t *b, uint64_t n,
                                      const uint32_t *ep, uint64_t nep,
                                      const uint32_t *xp, uint64_t nxp,
                                      uint8_t *scratch, uint64_t scratchcap,
                                      uint64_t *tokens_out,
                                      uint64_t *values_out,
                                      uint64_t *sum_out,
                                      uint64_t *err) {
    uint64_t tokens = 0, terms = 0, arena = 0, alen = 0, k = 0, xj = 0;
    uint8_t stk[MAXD];
    uint32_t sp = 0;
    uint8_t frame = 0;
    uint32_t p = 0;
    Err e;
    OdCur c;
    e.ok = 1;
    e.off = 0;
    e.msg = "ok";
    memset(&c, 0, sizeof c);
    c.b = b;
    c.n = n;
    c.ix = ep;
    c.nix = nep;
    c.e = &e;

    /* A structural or literal event: its record is the tag alone. */
#define NE_TAG(t) do { tokens++; terms += (uint64_t)(t); } while (0)
    /* A key or string event: its record is the tag, the length and the payload
       word the certified walk writes. */
#define NE_REF(t, ol, rf)                                                     \
    do {                                                                      \
        tokens++;                                                             \
        terms += (uint64_t)(t) + (uint64_t)(ol) + (uint64_t)(rf);             \
    } while (0)
    /* Refusal: the reading slots are zero (the declared semantics), and `*err`
       is the offset the walk recorded. */
#define NE_REFUSE()                                                           \
    do {                                                                      \
        *tokens_out = 0;                                                      \
        *values_out = 0;                                                      \
        *sum_out = 0;                                                         \
        *err = e.off;                                                         \
        return 0;                                                             \
    } while (0)

value:
    /* A value position: with the entry stream exhausted the walk reaches its
       end-of-stream rule, which reports the document's length. */
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k++];
    if (b[p] == '{') {
        if (sp >= MAXD) { e.off = p; NE_REFUSE(); }
        if (sp) stk[sp - 1] = frame;
        frame = 0;
        sp++;
        NE_TAG(T_OBJ);
        goto obj_first;
    }
    if (b[p] == '[') {
        if (sp >= MAXD) { e.off = p; NE_REFUSE(); }
        if (sp) stk[sp - 1] = frame;
        frame = 1;
        sp++;
        NE_TAG(T_ARR);
        goto arr_first;
    }
    if (b[p] == '"') goto string_value;
    goto scalar;

obj_first:
    /* An object's first member: `}` closes it, a key opens it, and every other
       byte is a refusal at its own position. */
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k];
    if (b[p] == '}') { k++; NE_TAG(T_OBJ_END); goto close_obj; }
    if (b[p] != '"') { e.off = p; NE_REFUSE(); }
    k++;
    goto key_body;

obj_key:
    /* After a member's comma the next entry is a key. */
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k];
    if (b[p] != '"') { e.off = p; NE_REFUSE(); }
    k++;
key_body:
    {
        uint32_t close;
        uint64_t len, ol, rf;
        size_t outn;
        int form;
        if (k >= nep) { e.off = p; NE_REFUSE(); }
        close = ep[k++];
        c.k = k;
        if (close >= n) { e.off = p; NE_REFUSE(); }
        len = (uint64_t)close - p - 1;
        if (len + US_SLACK > scratchcap) __builtin_trap();
        outn = 0;
        form = s2_string_body(&c, b + p + 1, len, scratch, &outn, xp, &xj,
                              nxp, NULL, NULL);
        if (!form) NE_REFUSE();
        if (form == 1) {
            NE_REF(T_KEY, len, (uint64_t)(p + 1) | (1ULL << 63));
        } else {
            /* One body's bytes, summed in order; vectorising this loop would
               put vector operations in the emitted body, which the model has
               none of, so the loop is the plain scalar form. */
#pragma clang loop vectorize(disable) interleave(disable)
            for (size_t i = 0; i < outn; i++) arena += scratch[i];
            ol = (uint64_t)outn;
            rf = alen;
            alen += ol;
            NE_REF(T_KEY, ol, rf);
        }
    }
    goto expect_colon;

string_value:
    {
        uint32_t close;
        uint64_t len, ol, rf;
        size_t outn;
        int form;
        if (k >= nep) { e.off = p; NE_REFUSE(); }
        close = ep[k++];
        c.k = k;
        if (close >= n) { e.off = p; NE_REFUSE(); }
        len = (uint64_t)close - p - 1;
        if (len + US_SLACK > scratchcap) __builtin_trap();
        outn = 0;
        form = s2_string_body(&c, b + p + 1, len, scratch, &outn, xp, &xj,
                              nxp, NULL, NULL);
        if (!form) NE_REFUSE();
        if (form == 1) {
            NE_REF(T_STR, len, (uint64_t)(p + 1) | (1ULL << 63));
        } else {
            /* One body's bytes, summed in order; vectorising this loop would
               put vector operations in the emitted body, which the model has
               none of, so the loop is the plain scalar form. */
#pragma clang loop vectorize(disable) interleave(disable)
            for (size_t i = 0; i < outn; i++) arena += scratch[i];
            ol = (uint64_t)outn;
            rf = alen;
            alen += ol;
            NE_REF(T_STR, ol, rf);
        }
    }
    goto after_value;

expect_colon:
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k++];
    if (b[p] != ':') { e.off = p; NE_REFUSE(); }
    goto value;

arr_first:
    /* An array's first value: `]` closes it, everything else is a value. */
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k];
    if (b[p] == ']') { k++; NE_TAG(T_ARR_END); goto close_arr; }
    goto value;

close_obj:
    sp--;
    if (sp) frame = stk[sp - 1];
    goto after_value;
close_arr:
    sp--;
    if (sp) frame = stk[sp - 1];
    goto after_value;

after_value:
    if (sp == 0) {
        /* The root value is complete: any further entry is a refusal at that
           entry's position, and an exhausted stream accepts. */
        if (k < nep) { e.off = (uint64_t)ep[k]; NE_REFUSE(); }
        goto accept;
    }
    if (k >= nep) { e.off = n; NE_REFUSE(); }
    p = ep[k++];
    if (frame == 0) {
        if (b[p] == '}') { NE_TAG(T_OBJ_END); goto close_obj; }
        if (b[p] != ',') { e.off = p; NE_REFUSE(); }
        goto obj_key;
    }
    if (b[p] == ']') { NE_TAG(T_ARR_END); goto close_arr; }
    if (b[p] != ',') { e.off = p; NE_REFUSE(); }
    goto value;

scalar:
    {
        uint64_t ip = (k < nep) ? (uint64_t)ep[k] : n;
        uint64_t ee = p;
        OdTok tok;
        tok.pos = p;
        tok.gap = 1;
        if (ip > p && !is_ws(b[ip - 1])) ee = ip;
        else while (ee < ip && !is_ws(b[ee])) ee++;
        tok.end = ee;
        c.k = k;
        uint8_t c0 = b[p];
        if (c0 == '-' || (c0 >= '0' && c0 <= '9')) {
            double d;
            size_t ei = 0;
            if (!num_fast_el1(b + p, ee - p, &d, &ei)) {
                e.off = p + ei;
                od_gap_recover(&c, &tok);
                NE_REFUSE();
            }
            tokens++;
            terms += (uint64_t)T_NUM + dbits(d);
        } else {
            uint64_t lit;
            uint32_t ln;
            uint8_t tag;
            if (c0 == 't')      { lit = NE_LIT_TRUE;  ln = 4; tag = T_TRUE;  }
            else if (c0 == 'f') { lit = NE_LIT_FALSE; ln = 5; tag = T_FALSE; }
            else if (c0 == 'n') { lit = NE_LIT_NULL;  ln = 4; tag = T_NULL;  }
            else {
                e.off = p;
                od_gap_recover(&c, &tok);
                NE_REFUSE();
            }
            size_t ei = 0;
            if (!ne_lit(b + p, ee - p, lit, ln, &ei)) {
                e.off = p + ei;
                od_gap_recover(&c, &tok);
                NE_REFUSE();
            }
            tokens++;
            terms += (uint64_t)tag;
        }
        /* Anything between the scalar's first-whitespace end and the next entry
           is a second token in the same gap; the certified walk reaches it as
           another scalar and refuses it at that byte. */
        if (ee < ip) {
            uint64_t q = ee;
            while (q < ip && is_ws(b[q])) q++;
            if (q < ip) { e.off = q; NE_REFUSE(); }
        }
    }
    goto after_value;

accept:
    *tokens_out = tokens;
    *values_out = tokens;
    *sum_out = arena + terms;
    return 1;
}
