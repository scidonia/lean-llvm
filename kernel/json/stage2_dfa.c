/* stage2_dfa.c -- a spike of a different stage-2 dispatch and value-rule
   design: a table-driven automaton over a dense eight-symbol alphabet.

   Bench-only.  This unit is a comparison candidate and a proof fixture: the
   certified `kernel/json/stage2.c` remains the default, this file does not
   replace it, and nothing in the route links it.  Its emitted body is pinned
   by the capture at `probes/install/ir/pipeline/stage2-dfa.candidate.ll`.

   ## Why this design, and what it is not

   The certified walk's per-entry work is a `switch` on the entry's byte, and
   inside each case a chain of value-rule branches: `s2_value_pos` (a scope
   stack load and two comparisons), the key test, the bracket-type and
   trailing-comma tests, the comma and colon state tests.  Measured on the
   hetero corpus, that walk is 80.6% of the stage-2 call while string bodies
   are 17.5% and event writes 4.9%, and a rewrite that kept this walk and only
   moved its bookkeeping (register cursors, one-byte stack, hoisted record
   checks) was slower on all 148 documents.  So the question this file asks is
   narrower: can the *rules* themselves, expressed as data, be cheaper than the
   branch chain?

   Here the byte classifies into one of eight symbols (three structural pairs,
   comma, colon, quote, scalar), one table load yields `(action, next state)`,
   and the value rules are entries in that table rather than branches.  The
   automaton has ten states: the document root and end, and for each container
   the four phases the certified walk keeps in its two `ctype`/`cst` arrays --
   with the first-element and after-comma phases distinct, because that is
   exactly the empty-container versus trailing-comma distinction.

   What is deliberately *not* changed, so the spike prices the dispatch alone:

     - the string body's classification and decode are the certified unit's
       (`s2_string_body`, i.e. the escape unit's list and list-free entries);
     - the scalar token's grammar, conversion and refusal offsets are the
       certified unit's (`od_scalar_value`, `od_gap_recover`);
     - the event encoding and the record stores are the certified unit's
       (`out_tag`, `out_u64`, and the same `out_reserve` + tag + 4 + 8 byte
       writes), including the arena reserve and the escape-list cursor.

   The whole certified translation unit is included, with its entry renamed so
   this file can reach those helpers in the same TU; the included walk is then
   dead code in this object and the tree's `stage2.o` remains the reference the
   gate compares against.

   ## What the gate must hold

   `leanllvm_json_stage2_dfa` has `leanllvm_json_stage2`'s ABI.  On every
   document the harness stages, its verdict, `*err` on refusal, `*ndst` and
   `dst[0..*ndst)`, and `*nev` and `ev[0..*nev)` must equal the certified
   walk's byte for byte.  A single difference is a failure and no timing is
   read.

   ## The tradeoff

   A faster prototype is not shippable: this walk has no contract object and no
   refinement theorem, so it cannot replace the certified unit -- which is the
   default and is what the route's proof covers -- without its own proof of the
   same statement. */
#define leanllvm_json_stage2 leanllvm_json_stage2_include_unused
#include "stage2.c"
#undef leanllvm_json_stage2

/* ------------------------------------------------------------- the design -- */
#define SD_MAXD 520

enum {
    SD_ROOT = 0,      /* expecting the document's single root value */
    SD_ROOT_END,      /* root done; nothing more is legal */
    SD_OBJ_FIRST,     /* after '{': a key or '}' */
    SD_OBJ_KEY,       /* after ',': a key, and not '}' (trailing comma) */
    SD_OBJ_COLON,     /* after a key: ':' */
    SD_OBJ_VAL,       /* after ':': a value */
    SD_OBJ_COMMA,     /* after a value: ',' or '}' */
    SD_ARR_FIRST,     /* after '[': a value or ']' */
    SD_ARR_VAL,       /* after ',': a value, and not ']' (trailing comma) */
    SD_ARR_COMMA      /* after a value: ',' or ']' */
};

enum {
    A_NONE = 0,       /* comma or colon: state change only */
    A_OPEN_OBJ,
    A_OPEN_ARR,
    A_CLOSE_OBJ,
    A_CLOSE_ARR,
    A_QUOTE,          /* a key or a string, decided by the previous state */
    A_SCALAR,
    A_ERR             /* the entry is not legal in this state */
};

/* Symbols: 0 '{', 1 '[', 2 '}', 3 ']', 4 ',', 5 ':', 6 '"', 7 scalar start. */
static const uint8_t sd_cls[256] = {
    [0 ... 255] = 7,
    ['{'] = 0, ['['] = 1, ['}'] = 2, [']'] = 3,
    [','] = 4, [':'] = 5, ['"'] = 6
};

#define SD_T(a, n) ((uint8_t)(((a) << 4) | (n)))
/* sd_tr[state][symbol] = (action << 4) | next state; a close's next state is
   the stack's restore value and the field is unused. */
static const uint8_t sd_tr[10][8] = {
    /* SD_ROOT */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ROOT_END), SD_T(A_SCALAR, SD_ROOT_END) },
    /* SD_ROOT_END */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0) },
    /* SD_OBJ_FIRST: key or '}' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_OBJ, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_QUOTE, SD_OBJ_COLON),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_KEY: key only */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_QUOTE, SD_OBJ_COLON),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_COLON: ':' only */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0), SD_T(A_NONE, SD_OBJ_VAL), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
    /* SD_OBJ_VAL: a value */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_OBJ_COMMA), SD_T(A_SCALAR, SD_OBJ_COMMA) },
    /* SD_OBJ_COMMA: ',' or '}' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_OBJ, 0), SD_T(A_ERR, 0),
      SD_T(A_NONE, SD_OBJ_KEY), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
    /* SD_ARR_FIRST: a value or ']' */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_CLOSE_ARR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ARR_COMMA), SD_T(A_SCALAR, SD_ARR_COMMA) },
    /* SD_ARR_VAL: a value only */
    { SD_T(A_OPEN_OBJ, SD_OBJ_FIRST), SD_T(A_OPEN_ARR, SD_ARR_FIRST),
      SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_QUOTE, SD_ARR_COMMA), SD_T(A_SCALAR, SD_ARR_COMMA) },
    /* SD_ARR_COMMA: ',' or ']' */
    { SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_ERR, 0), SD_T(A_CLOSE_ARR, 0),
      SD_T(A_NONE, SD_ARR_VAL), SD_T(A_ERR, 0), SD_T(A_ERR, 0),
      SD_T(A_ERR, 0) },
};

/* The state a parent frame resumes in once its child closes: the frame is
   either an object expecting a value (after ':') or an array expecting one
   (after '[' or ','). */
static const uint8_t sd_restore[10] = {
    [SD_OBJ_VAL] = SD_OBJ_COMMA,
    [SD_ARR_FIRST] = SD_ARR_COMMA,
    [SD_ARR_VAL] = SD_ARR_COMMA
};

__attribute__((always_inline)) static inline uint64_t
sd_walk(S2 *s, ZOut *z, Err *e) {
    const uint8_t *b = s->b;
    uint64_t n = s->n, nsp = s->nsp;
    const uint32_t *ep = s->ep;
    const uint32_t *xp = s->xp;
    uint64_t nxp = s->nxp;
    uint8_t stk[SD_MAXD];
    uint32_t sp = 0, state = SD_ROOT;
    uint64_t k = 0, xj = 0, acc = 0;
    OdCur c;
    memset(&c, 0, sizeof c);
    c.b = b;
    c.n = n;
    c.ix = ep;
    c.nix = nsp;
    c.e = e;

    while (k < nsp) {
        uint32_t p = ep[k++];
        unsigned sym = sd_cls[b[p]];
        unsigned prev = state;
        unsigned t = sd_tr[state][sym];
        unsigned act = t >> 4;
        state = t & 15u;
        if (__builtin_expect(act == A_ERR, 0)) { e->off = p; return 0; }
        switch (act) {
        case A_NONE:
            break;
        case A_OPEN_OBJ:
        case A_OPEN_ARR: {
            if (sp >= SD_MAXD) { e->off = p; return 0; }
            if (sp) stk[sp - 1] = sd_restore[prev];
            sp++;
            out_tag(&z->ev, (act == A_OPEN_OBJ) ? T_OBJ : T_ARR);
            break;
        }
        case A_CLOSE_OBJ:
        case A_CLOSE_ARR: {
            sp--;
            state = sp ? stk[sp - 1] : SD_ROOT_END;
            out_tag(&z->ev, (act == A_CLOSE_OBJ) ? T_OBJ_END : T_ARR_END);
            break;
        }
        case A_QUOTE: {
            /* A quotation's closing entry is the next one. */
            if (k >= nsp) { e->off = p; return 0; }
            uint32_t close = ep[k++];
            c.k = k;
            if (close >= n) { e->off = p; return 0; }
            int key = (prev == SD_OBJ_FIRST || prev == SD_OBJ_KEY);
            uint64_t len = (uint64_t)close - p - 1;
            size_t outn = 0;
            z_arena_reserve(z, (size_t)len + US_SLACK);
            uint8_t *dst = z->ar + z->alen;
            int form = s2_string_body(&c, b + p + 1, len, dst, &outn,
                                      xp, &xj, nxp, s->em, s->uk);
            if (!form) return 0;
            uint32_t ol;
            uint64_t rec;
            if (form == 1) {
                ol = (uint32_t)len;
                rec = (uint64_t)(p + 1) | (1ULL << 63);
            } else {
                ol = (uint32_t)outn;
                rec = z->alen;
                z->alen += outn;
            }
            out_reserve(&z->ev, 13);
            uint8_t *r = z->ev.b + z->ev.len;
            r[0] = (uint8_t)(key ? T_KEY : T_STR);
            memcpy(r + 1, &ol, 4);
            memcpy(r + 5, &rec, 8);
            z->ev.len += 13;
            break;
        }
        case A_SCALAR: {
            uint64_t ip = (k < nsp) ? (uint64_t)ep[k] : n;
            uint64_t ee = p;
            OdTok tok;
            tok.pos = p;
            tok.gap = 1;
            if (ip > p && !is_ws(b[ip - 1])) ee = ip;
            else while (ee < ip && !is_ws(b[ee])) ee++;
            tok.end = ee;
            {
                uint8_t c0 = b[p];
                if (c0 == '-' || (c0 >= '0' && c0 <= '9')) tok.kind = K_NUM;
                else if (c0 == 't') tok.kind = K_TRUE;
                else if (c0 == 'f') tok.kind = K_FALSE;
                else if (c0 == 'n') tok.kind = K_NULL;
                else tok.kind = 0;
            }
            if (!od_scalar_value(&c, &tok, &z->ev, &acc)) {
                if (tok.gap) od_gap_recover(&c, &tok);
                return 0;
            }
            if (ee < ip) {
                uint64_t q = ee;
                while (q < ip && is_ws(b[q])) q++;
                if (q < ip) { e->off = q; return 0; }
            }
            break;
        }
        default:
            e->off = p;                     /* unreachable: A_* is exhaustive */
            return 0;
        }
    }
    if (sp != 0) { e->off = n; return 0; }              /* unclosed container */
    if (state != SD_ROOT_END) { e->off = n; return 0; } /* no value */
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    return acc + 1;
}

/* ------------------------------------------------------------------- ABI -- */
uint64_t leanllvm_json_stage2_dfa(const uint8_t *b, uint64_t n,
                                  const uint32_t *ep, uint64_t nep,
                                  const uint32_t *xp, uint64_t nxp,
                                  uint8_t *dst, uint64_t dstcap,
                                  uint64_t *ndst,
                                  uint8_t *ev, uint64_t evcap,
                                  uint64_t *nev,
                                  uint64_t *err) {
    S2 s;
    ZOut z;
    Err e;

    s2_init(&s, b, n, (n + 63) >> 6, NULL, 0, NULL, (uint32_t *)ep);
    s.nsp = nep;
    s.xp = xp;
    s.nxp = nxp;

    z_init(&z);
    z.ar = dst;
    z.alen = (size_t)*ndst;
    z.acap = (size_t)dstcap;
    z.ev.b = ev;
    z.ev.len = (size_t)*nev;
    z.ev.cap = (size_t)evcap;

    e.ok = 1;
    e.off = 0;
    e.msg = "ok";

    uint64_t r = sd_walk(&s, &z, &e);
    *ndst = (uint64_t)z.alen;
    *nev = (uint64_t)z.ev.len;
    if (!r) *err = e.off;
    return r ? 1 : 0;
}
