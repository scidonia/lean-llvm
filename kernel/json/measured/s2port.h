/* s2port.h -- simdjson-shaped stage 2 over this tree's stage-1 stream.
   Scratch experiment; nothing here belongs to the repository.

   Stage 1 (`ci2` + `scan_cand_gated`) already produces the filtered
   structural index: quote characters (open and close) plus `{}[],:` outside
   strings.  simdjson's stage 2 expects one more thing from stage 1: an entry
   for the first byte of every scalar.  `s2_build` adds those entries by
   walking the gaps between index entries and skipping whitespace only; it does
   not scan scalar bodies.  The result `ep` is a single position stream in
   document order, which is what simdjson's loop consumes.

   The loop below is their shape: one pass over the position stream, a switch
   on the byte at each position, and a scope stack (container type + state per
   depth).  There is no cursor byte pointer, no per-token `od_step`, and no
   rescan of the input between index entries.

   Flags:
     S2_VAL  grammar validation with the reference's first-error offsets
     S2_STR  string-body validation with the reference's offsets
     S2_EV   typed value materialisation (the FULL event stream, into ZOut)

   With no flags the loop is the consuming form: every value is read, numbers
   converted and literals checked (exactly what the trusting consume path
   does), strings are summed, and no grammar or string-body check runs. */
#ifndef S2PORT_H
#define S2PORT_H

/* the unescaper the escaped-body form calls (SIMD, one pass) */
#include "usdec.h"
#include "dens.h"

/* S2_DEC_GATE: which shape of the per-body list decoder the escaped-body path
   calls.
     0  the shipped one: out of line (`us_dec_x`, `\u` inlined)
     1  the inlined shape (`\u` out of line), always
     2  the document class picks: SPARSE inlined, PLAIN and HEAVY out of line
     3  the document class picks, with HEAVY inlined too (the two-class rule,
        kept as a measurement arm) */
#ifndef S2_DEC_GATE
#define S2_DEC_GATE 0
#endif
#if S2_DEC_GATE || defined(SP_MODES)
#include "usdec_gate.h"
#endif
#if defined(SP_MODES)
#include "modes.h"
#endif
#if defined(SP43_MODES)
#include "modes43.h"
#include "usdec_esc43.h"
#include "usdec_variants43.h"
#endif
#if defined(SP44_MODES)
#include "modes44.h"
#include "usdec_kind44.h"
#include "usdec_variants44.h"
#endif

#define S2_VAL 1u
#define S2_STR 2u
#define S2_EV  4u

/* S2_XP=1: string bodies are decoded from the stage-1 escape-position list
   (s->xp) instead of scanning each body for its first special and its window
   mask.  Falls back to the scanning form when no list is attached. */
#ifndef S2_XP
#define S2_XP 0
#endif

/* S2_XM=1: string bodies are decoded from the stage-1 per-block escape
   masks (s->em): the body's byte range selects its lanes, so no
   per-body cursor and no per-position range test runs. */
#ifndef S2_XM
#define S2_XM 0
#endif

typedef struct {
    const uint8_t *b;
    uint64_t n, nb;
    const uint32_t *ix;      /* raw stage-1 index */
    uint64_t nix;
    const uint64_t *im;      /* in-string / quote-open bit per position */
    uint32_t *ep;            /* derived entry stream (positions) */
    uint64_t nsp;
    uint64_t visited;
    const uint32_t *xp;      /* stage-1 escape positions (document order) */
    uint64_t nxp;
    const uint64_t *em;      /* stage-1 escape mask per 64-byte block */
    uint64_t nem;
    const uint64_t *uk;      /* stage-1 escape-kind bit per block */
    uint64_t nuk;
} S2;

__attribute__((always_inline)) static inline void
s2_init(S2 *s, const uint8_t *b, uint64_t n, uint64_t nb,
        const uint32_t *ix, uint64_t nix, const uint64_t *im, uint32_t *ep) {
    s->b = b; s->n = n; s->nb = nb; s->ix = ix; s->nix = nix;
    s->im = im; s->ep = ep; s->nsp = 0; s->visited = 0;
    s->xp = NULL; s->nxp = 0;
    s->em = NULL; s->nem = 0;
    s->uk = NULL; s->nuk = 0;
}

/* Build the entry stream: keep the stage-1 positions, insert the first byte of
   every scalar gap, and leave each string's closing quote immediately after
   its opening quote (the parser consumes that one entry without a byte load).
   An opening quote with no closing quote becomes [open, n]; the parser fails
   at n only if it reaches it, so an earlier error keeps its own offset. */
static void s2_build(S2 *s) {
#ifdef S2_BUILD_COPY
    /* attribution only: the copy of the stage-1 stream, without scalar starts */
    for (uint64_t i = 0; i < s->nix; i++) s->ep[i] = s->ix[i];
    s->nsp = s->nix;
    return;
#endif
    const uint8_t *b = s->b;
    const uint32_t *ix = s->ix;
    const uint64_t *im = s->im;
    uint64_t n = s->n, nix = s->nix;
    uint32_t *ep = s->ep;
    uint64_t m = 0, q = 0;
    uint64_t first = nix ? (uint64_t)ix[0] : n;
    while (q < first && is_ws(b[q])) q++;
    if (q < first) ep[m++] = (uint32_t)q;
    for (uint64_t i = 0; i < nix; i++) {
        uint32_t p = ix[i];
        /* The in-string mask is 1 at an opening quote and at every body byte,
           0 at a structural character outside strings and at a closing quote.
           Every stage-1 entry is one of those, so this bit classifies it
           without loading the input byte. */
        if (im[p >> 6] & (1ULL << (p & 63))) {
            ep[m++] = p;                                        /* opening quote */
            if (i + 1 >= nix) { ep[m++] = (uint32_t)n; break; }
            uint32_t close = ix[i + 1];
            if (close >= n) { ep[m++] = (uint32_t)n; break; }  /* unterminated */
            ep[m++] = close;
            uint64_t nxt = (i + 2 < nix) ? (uint64_t)ix[i + 2] : n;
            q = (uint64_t)close + 1;
            while (q < nxt && is_ws(b[q])) q++;
            if (q < nxt) ep[m++] = (uint32_t)q;
            i++;
            continue;
        }
        ep[m++] = p;
        uint64_t nxt = (i + 1 < nix) ? (uint64_t)ix[i + 1] : n;
        q = (uint64_t)p + 1;
        if (q < nxt && nxt != q) {
            while (q < nxt && is_ws(b[q])) q++;
            if (q < nxt) ep[m++] = (uint32_t)q;
        }
    }
    s->nsp = m;
}

/* Value-position test, same states as the reference walk. */
__attribute__((always_inline)) static inline int s2_value_pos(uint32_t sp, int root_done,
                                                              const uint8_t *ct,
                                                              const uint8_t *cs) {
    if (sp == 0) return !root_done;
    uint32_t t = sp - 1;
    if (ct[t] == C_OBJ) return cs[t] == 2;
    return cs[t] == 0 || cs[t] == 2;
}

__attribute__((always_inline)) static inline void s2_after_value(uint32_t *sp, int *root_done,
                                                                 uint8_t *ct, uint8_t *cs) {
    if (*sp == 0) { *root_done = 1; return; }
    uint32_t t = *sp - 1;
    cs[t] = (ct[t] == C_OBJ) ? 3 : 1;
}

/* Timing probe: skip the byte-wise decoder for escaped bodies, keeping the
   z_scan half.  With S2_NO_DECODE=1 the walk no longer validates escape
   sequences, so the event stream / offsets differ on those documents; it is
   built only to price the decoder. */
#ifndef S2_NO_DECODE
#define S2_NO_DECODE 0
#endif

/* S2_FASTDISP: comma and colon handled before the switch.
   S2_NOBOUNDS: drop the per-string stream-bounds test. */
#ifndef S2_FASTDISP
#define S2_FASTDISP 0
#endif
#ifndef S2_NOBOUNDS
#define S2_NOBOUNDS 0
#endif

/* String body: the validation half of od_string_body_z, without the event
   record.

   Two forms, and between them one pass over the body:
     no escape   z_scan found nothing to decode, so the body is its own
                 materialisation -- no copy is made at all (form (a));
     escape      z_scan stopped at the first backslash.  Everything before it
                 is already known clean and its decoded bytes are the input
                 bytes, so they are copied and the SIMD unescaper starts at
                 the backslash itself (form (b)).  Nothing before that offset
                 is traversed twice.
   The error offset is the reference's: a control byte at its own offset, a
   malformed escape at its backslash. */
__attribute__((always_inline)) static inline int s2_string_body(OdCur *c, const uint8_t *p,
                                                               uint64_t len, uint8_t *dst,
                                                               size_t *outn,
                                                               const uint32_t *xp,
                                                               uint64_t *xj, uint64_t nxp,
                                                               const uint64_t *em,
                                                               const uint64_t *uk) {
#if S2_XM
    /* The stage-1 masks name every special byte of this body by block: the
       body's range alone classifies it, and the mask consumer starts at once. */
    if (em) {
        uint64_t pos0 = (uint64_t)(p - c->b);
        if (!us_mask_any(em, pos0, len)) { *outn = (size_t)len; return 1; }
        size_t ei = 0;
        size_t on = us_dec_m(p, len, dst, &ei, em, pos0);
        if (on == (size_t)-1) {
            od_fail(c, pos0 + ei, "string");
            return 0;
        }
        *outn = on;                                         /* form (b) */
        return 2;
    }
#endif
#if S2_XP
    /* The stage-1 list already names every special byte of this body: no scan
       is needed to classify it, and the unescaper starts at once. */
    if (xp) {
        uint64_t pos0 = (uint64_t)(p - c->b);
        while (*xj < nxp && (uint64_t)xp[*xj] < pos0) (*xj)++;
        if (!(*xj < nxp && (uint64_t)xp[*xj] < pos0 + len)) {
            *outn = (size_t)len;                            /* form (a) */
            return 1;
        }
        size_t ei = 0;
#if defined(SP44_MODES)
        /* runtime arm: the same object code in every arm */
        {
            uint64_t xj0 = *xj;
            size_t on;
            int dec = uk ? sp44_dec : 0;
            if (dec == 1)
                on = us_dec_x_kif44(p, len, dst, &ei, xp, xj, nxp, pos0, uk);
            else if (dec == 2)
                on = us_dec_x_kjmp44(p, len, dst, &ei, xp, xj, nxp, pos0, uk);
            else if (dec == 3)
                on = us_dec_x_ksw44(p, len, dst, &ei, xp, xj, nxp, pos0, uk);
            else if (dec == 4)
                on = us_dec_x_dup44(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (dec == 5)
                on = us_dec_x_dup2_44(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (dec == 6)
                on = us_dec_x_kifdup44(p, len, dst, &ei, xp, xj, nxp, pos0, uk);
            else if (dec == 7)
                on = us_dec_x_kifdup2_44(p, len, dst, &ei, xp, xj, nxp, pos0, uk);
            else
                on = us_dec_x(p, len, dst, &ei, xp, xj, nxp, pos0);
            sp44_calls++;
            sp44_escapes += *xj - xj0;
            sp44_outbytes += (on == (size_t)-1) ? 0 : on;
            if (on == (size_t)-1) { od_fail(c, pos0 + ei, "string"); return 0; }
            *outn = on;
            return 2;
        }
#elif defined(SP43_MODES)
        /* runtime arm: the same object code in every arm */
        {
            uint64_t xj0 = *xj;
            size_t on;
            if (sp43_esc == 1)
                on = us_dec_x_tab43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 2)
                on = us_dec_x_bf43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 3)
                on = us_dec_x_u2_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 4)
                on = us_dec_x_dup43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 5)
                on = us_dec_x_p6_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 6)
                on = us_dec_x_dup2_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 7)
                on = us_dec_x_dup3_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 8)
                on = us_dec_x_p1_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 9)
                on = us_dec_x_p2_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 10)
                on = us_dec_x_p3_43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 11)
                on = us_dec_x_sni43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 12)
                on = us_dec_x_tni43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else if (sp43_esc == 13)
                on = us_dec_x_bfs43(p, len, dst, &ei, xp, xj, nxp, pos0);
            else
                on = us_dec_x(p, len, dst, &ei, xp, xj, nxp, pos0);
            sp43_calls++;
            sp43_escapes += *xj - xj0;
            sp43_outbytes += (on == (size_t)-1) ? 0 : on;
            if (on == (size_t)-1) { od_fail(c, pos0 + ei, "string"); return 0; }
            *outn = on;
            return 2;
        }
#elif defined(SP_MODES)
        /* runtime arm: the same object code in every mode */
        int use_inl = (sp_dec == 1) ||
                      (sp_dec == 2 && dens_doc_class == DENS_SPARSE) ||
                      (sp_dec == 3 && dens_doc_class != DENS_PLAIN) ||
                      (sp_dec == 5 && dens_doc_class == DENS_SPARSE);
        int use_inl2 = (sp_dec == 4 && dens_doc_class != DENS_PLAIN) ||
                       (sp_dec == 5 && dens_doc_class == DENS_HEAVY);
        if (use_inl) {
            size_t on = us_dec_x_inl(p, len, dst, &ei, xp, xj, nxp, pos0);
            if (on == (size_t)-1) { od_fail(c, pos0 + ei, "string"); return 0; }
            *outn = on;
            return 2;
        } else if (use_inl2) {
            size_t on = us_dec_x_inl2(p, len, dst, &ei, xp, xj, nxp, pos0);
            if (on == (size_t)-1) { od_fail(c, pos0 + ei, "string"); return 0; }
            *outn = on;
            return 2;
        } else {
            size_t on = us_dec_x_out(p, len, dst, &ei, xp, xj, nxp, pos0);
            if (on == (size_t)-1) { od_fail(c, pos0 + ei, "string"); return 0; }
            *outn = on;
            return 2;
        }
#elif S2_DEC_GATE == 1
        size_t on = us_dec_x_inl(p, len, dst, &ei, xp, xj, nxp, pos0);
#elif S2_DEC_GATE == 2
        size_t on = (dens_doc_class == DENS_SPARSE)
                        ? us_dec_x_inl(p, len, dst, &ei, xp, xj, nxp, pos0)
                        : us_dec_x_out(p, len, dst, &ei, xp, xj, nxp, pos0);
#elif S2_DEC_GATE == 3
        size_t on = (dens_doc_class == DENS_PLAIN)
                        ? us_dec_x_out(p, len, dst, &ei, xp, xj, nxp, pos0)
                        : us_dec_x_inl(p, len, dst, &ei, xp, xj, nxp, pos0);
#elif S2_DEC_GATE == 4
        /* PLAIN out of line, everything else inlined with `\u` inlined */
        size_t on = (dens_doc_class == DENS_PLAIN)
                        ? us_dec_x_out(p, len, dst, &ei, xp, xj, nxp, pos0)
                        : us_dec_x_inl2(p, len, dst, &ei, xp, xj, nxp, pos0);
#elif S2_DEC_GATE == 5
        /* PLAIN out of line, SPARSE inlined with `\u` out of line, HEAVY
           inlined with `\u` inlined */
        size_t on = (dens_doc_class == DENS_PLAIN)
                        ? us_dec_x_out(p, len, dst, &ei, xp, xj, nxp, pos0)
                        : (dens_doc_class == DENS_HEAVY)
                              ? us_dec_x_inl2(p, len, dst, &ei, xp, xj, nxp, pos0)
                              : us_dec_x_inl(p, len, dst, &ei, xp, xj, nxp, pos0);
#else
        size_t on = us_dec_x(p, len, dst, &ei, xp, xj, nxp, pos0);
#endif
#if !defined(SP_MODES) && !defined(SP43_MODES) && !defined(SP44_MODES)
        if (on == (size_t)-1) {
            od_fail(c, pos0 + ei, "string");
            return 0;
        }
        *outn = on;                                         /* form (b) */
        return 2;
#endif
    }
#endif
#if US_FUSED
    {
        size_t ei = 0;
        int form = us_body(p, len, dst, outn, &ei);
        if (!form) od_fail(c, (uint64_t)(p - c->b) + ei, "string");
        return form;
    }
#endif
    int is_bs = 0;
    uint64_t off = z_scan(p, len, &is_bs);
    if (off == Z_NONE) { *outn = (size_t)len; return 1; }   /* form (a): a span */
    if (!is_bs) {
        od_fail(c, (uint64_t)(p - c->b) + off, "string");
        return 0;
    }
#if S2_NO_DECODE
    /* timing probe only: the escape sequence is not validated, so the event
       stream and the offsets are not the reference's */
    *outn = (size_t)len;
    return 2;
#endif
    if (off) {
        uint64_t k = 0;
        do {
            _mm256_storeu_si256((__m256i *)(dst + k),
                                _mm256_loadu_si256((const __m256i *)(p + k)));
            k += 32;
        } while (k < off);
    }
    size_t ei = 0;
    size_t on = us_dec(p + off, len - off, dst + off, &ei);
    if (on == (size_t)-1) {
        od_fail(c, (uint64_t)(p - c->b) + off + ei, "string");
        return 0;
    }
    *outn = (size_t)off + on;                               /* form (b) */
    return 2;
}

/* The P2 form: validate an escaped body into the shared scratch buffer. */
__attribute__((always_inline)) static inline int s2_string_check(OdCur *c, const uint8_t *p,
                                                                 uint64_t len) {
    size_t outn = 0;
    out_reserve(&g_sbuf, (size_t)len + US_SLACK);
    int form = s2_string_body(c, p, len, g_sbuf.b, &outn, NULL, NULL, 0, NULL, NULL);
    if (form == 2) g_sbuf.len = outn;
    return form;
}

/* Consuming string: sum the body bytes, no validation. */
__attribute__((always_inline)) static inline void s2_string_touch(const uint8_t *p, uint64_t len,
                                                                 uint64_t *acc) {
    *acc = touch_bytes(p, len, *acc);
}

/* flags is a compile-time constant at every call site; always_inline lets the
   compiler drop the branches the mode does not need, which is how the four
   measurements below are built from one source. */
__attribute__((always_inline)) static inline uint64_t
s2_walk(S2 *s, unsigned flags, ZOut *z, Err *e) {
    const uint8_t *b = s->b;
    uint64_t n = s->n;
    const uint32_t *ep = s->ep;
    uint64_t nsp = s->nsp;
    OdCur c;
    memset(&c, 0, sizeof c);
    c.b = b; c.n = n; c.ix = ep; c.nix = nsp; c.e = e;

    uint8_t ctype[MAXD], cst[MAXD];
    uint32_t sp = 0;
    int root_done = 0;
    uint64_t acc = 0, visited = 0;
    uint64_t k = 0;
#if S2_XP
    uint64_t xj = 0;
    const uint32_t *xp = s->xp;
    uint64_t nxp = s->nxp;
#endif

#ifdef S2_LOOP_ONLY
    while (k < nsp) {
        uint32_t p = ep[k++];
        acc ^= b[p];
        visited++;
    }
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    s->visited = visited;
    return acc + 1;
#elif defined(S2_LOOP_NOSW)
    /* probe: the same entry walk with the dispatch removed but the quote
       pairing and scalar gap scan kept, to price the switch */
    while (k < nsp) {
        uint32_t p = ep[k++];
        uint8_t ch = b[p];
        visited++;
        acc ^= ch;
        if (ch == '"') { k++; }
        else if (ch != ',' && ch != ':' && ch != '{' && ch != '[' &&
                 ch != '}' && ch != ']') {
#if S2_NOBOUNDS
            uint64_t ip = (uint64_t)ep[k];      /* ep[nsp] == n */
#else
            uint64_t ip = (k < nsp) ? (uint64_t)ep[k] : n;
#endif
            uint64_t ee = p;
            if (ip > p && !is_ws(b[ip - 1])) ee = ip;
            else while (ee < ip && !is_ws(b[ee])) ee++;
            acc ^= ee;
        }
    }
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    s->visited = visited;
    return acc + 1;
#else
#if S2_NOBOUNDS
    /* The stage-1 stream puts every closing quote immediately after its
       opening quote; an unterminated last string leaves the stream at the
       quote.  One sentinel `n` makes the close test the only test. */
    ((uint32_t *)s->ep)[nsp] = (uint32_t)n;
#endif
    while (k < nsp) {
        uint32_t p = ep[k++];
        uint8_t ch = b[p];
        c.k = k;
        visited++;
#if S2_FASTDISP
        /* The two most frequent tokens (40% of visited entries on canonical)
           leave the switch entirely; the rest keep their jump table. */
        if (ch == ',') {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "comma"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] == C_OBJ) {
                    if (cst[t] != 3) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 4;
                } else {
                    if (cst[t] != 1) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 2;
                }
            }
            continue;
        }
        if (ch == ':') {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "colon"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] != C_OBJ || cst[t] != 1)
                    return od_fail(&c, p, "colon"), 0;
                cst[t] = 2;
            }
            continue;
        }
#endif
        switch (ch) {
        case '{':
        case '[': {
            if (flags & S2_VAL) {
                if (!s2_value_pos(sp, root_done, ctype, cst))
                    return od_fail(&c, p, "container where no value is allowed"), 0;
                if (sp >= MAXD) return od_fail(&c, p, "nesting limit"), 0;
                ctype[sp] = (ch == '{') ? C_OBJ : C_ARR;
                cst[sp] = 0;
                sp++;
            }
            if (flags & S2_EV) out_tag(&z->ev, (ch == '{') ? T_OBJ : T_ARR);
            else acc = touch_u64(acc, (ch == '{') ? K_OBJ : K_ARR);
            break;
        }
        case '}':
        case ']': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "close"), 0;
                uint32_t t = sp - 1;
                uint8_t want = (ch == '}') ? C_OBJ : C_ARR;
                if (ctype[t] != want) return od_fail(&c, p, "bracket type"), 0;
                uint8_t st = cst[t];
                int ok = (want == C_OBJ) ? (st == 3 || st == 0) : (st == 1 || st == 0);
                if (!ok) return od_fail(&c, p, "trailing comma"), 0;
                sp--;
                s2_after_value(&sp, &root_done, ctype, cst);
            }
            if (flags & S2_EV) out_tag(&z->ev, (ch == '}') ? T_OBJ_END : T_ARR_END);
            else acc = touch_u64(acc, (ch == '}') ? K_OBJ_END : K_ARR_END);
            break;
        }
        case ',': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "comma"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] == C_OBJ) {
                    if (cst[t] != 3) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 4;
                } else {
                    if (cst[t] != 1) return od_fail(&c, p, "comma"), 0;
                    cst[t] = 2;
                }
            }
            (void)ch;
            break;
        }
        case ':': {
            if (flags & S2_VAL) {
                if (sp == 0) return od_fail(&c, p, "colon"), 0;
                uint32_t t = sp - 1;
                if (ctype[t] != C_OBJ || cst[t] != 1) return od_fail(&c, p, "colon"), 0;
                cst[t] = 2;
            }
            (void)ch;
            break;
        }
        case '"': {
#if !S2_NOBOUNDS
            if (k >= nsp) return od_fail(&c, n, "unterminated"), 0;
#endif
            uint32_t close = ep[k++];
            c.k = k;
            if (close >= n) return od_fail(&c, n, "unterminated"), 0;
            int key = 0;
            if (flags & S2_VAL) {
                int val = s2_value_pos(sp, root_done, ctype, cst);
                if (sp > 0 && ctype[sp - 1] == C_OBJ) {
                    uint8_t st = cst[sp - 1];
                    if (st == 0 || st == 4) key = 1;
                }
                if (!key && !val) return od_fail(&c, p, "string where no value is allowed"), 0;
            }
            uint64_t len = (uint64_t)close - p - 1;
            if (flags & (S2_STR | S2_EV)) {
                /* one body pass for both forms: with S2_EV the decoded bytes
                   go straight to the event arena, otherwise to the scratch */
                size_t outn = 0;
                uint8_t *dst;
                if (flags & S2_EV) {
                    z_arena_reserve(z, (size_t)len + US_SLACK);
                    dst = z->ar + z->alen;
                } else {
                    out_reserve(&g_sbuf, (size_t)len + US_SLACK);
                    dst = g_sbuf.b;
                }
#if S2_XP
                int form = s2_string_body(&c, b + p + 1, len, dst, &outn,
                                          xp, &xj, nxp, s->em, s->uk);
#else
                int form = s2_string_body(&c, b + p + 1, len, dst, &outn,
                                          NULL, NULL, 0, s->em, s->uk);
#endif
                if (!form) return 0;
                if (flags & S2_EV) {
                    uint32_t ol;
                    uint64_t rec;
                    if (form == 1) {          /* plain: a span into the input */
                        ol = (uint32_t)len;
                        rec = (uint64_t)(p + 1) | (1ULL << 63);
                    } else {                  /* escaped: bytes in the arena */
                        ol = (uint32_t)outn;
                        rec = z->alen;
                        z->alen += outn;
                    }
                    out_reserve(&z->ev, 13);
                    uint8_t *e = z->ev.b + z->ev.len;
                    e[0] = (uint8_t)(key ? T_KEY : T_STR);
                    memcpy(e + 1, &ol, 4);
                    memcpy(e + 5, &rec, 8);
                    z->ev.len += 13;
                } else {
                    if (form == 2) g_sbuf.len = outn;
                    acc = touch_u64(acc, len);
                }
            } else {
                s2_string_touch(b + p + 1, len, &acc);
            }
            if (flags & S2_VAL) {
                if (key) cst[sp - 1] = 1;
                else s2_after_value(&sp, &root_done, ctype, cst);
            }
            break;
        }
        default: {
            /* A scalar gap.  Its text ends at the first whitespace, exactly as
               the reference cursor's gap scan does; the next entry position is
               the delimiter that follows. */
#if S2_NOBOUNDS
            uint64_t ip = (uint64_t)ep[k];      /* ep[nsp] == n */
#else
            uint64_t ip = (k < nsp) ? (uint64_t)ep[k] : n;
#endif
            uint64_t ee = p;
            OdTok t;
            t.pos = p;
            t.gap = 1;
            if (ip > p && !is_ws(b[ip - 1])) {
                ee = ip;
            } else {
                while (ee < ip && !is_ws(b[ee])) ee++;
            }
            t.end = ee;
            {
                uint8_t c0 = b[p];
                if (c0 == '-' || (c0 >= '0' && c0 <= '9')) t.kind = K_NUM;
                else if (c0 == 't') t.kind = K_TRUE;
                else if (c0 == 'f') t.kind = K_FALSE;
                else if (c0 == 'n') t.kind = K_NULL;
                else t.kind = 0;
            }
            if (flags & S2_VAL) {
                if (!s2_value_pos(sp, root_done, ctype, cst))
                    return od_fail(&c, p, "scalar where no value is allowed"), 0;
            }
            if (flags & S2_EV) {
                if (!od_scalar_value(&c, &t, &z->ev, &acc)) {
                    if (t.gap) od_gap_recover(&c, &t);
                    return 0;
                }
            } else {
                if (!od_scalar_value(&c, &t, NULL, &acc)) {
                    if (t.gap) od_gap_recover(&c, &t);
                    return 0;
                }
            }
            if (flags & S2_VAL) s2_after_value(&sp, &root_done, ctype, cst);
            /* Anything between the scalar's first-whitespace end and the next
               entry is a second token in the same gap; the reference reaches
               it as another scalar and rejects it at that byte. */
            if (ee < ip) {
                uint64_t q = ee;
                while (q < ip && is_ws(b[q])) q++;
                if (q < ip) return od_fail(&c, q, "extra token"), 0;
            }
            break;
        }
        }
    }
#endif
    if (flags & S2_VAL) {
        if (sp != 0) return od_fail(&c, n, "unclosed container"), 0;
        if (!root_done) return od_fail(&c, n, "no value"), 0;
    }
    e->ok = 1;
    e->off = 0;
    e->msg = "ok";
    s->visited = visited;
    return acc + 1;
}

#endif /* S2PORT_H */
