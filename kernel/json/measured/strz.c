/* strz.c -- zero-copy string bodies.
   Scratch experiment; nothing here belongs to the repository.

   A string body with no backslash needs no decoding: its decoded bytes are
   exactly the input bytes.  This module emits a *span* (input offset, length)
   into the event stream instead of copying the bytes.  The "no backslash" test
   is a SIMD compare over the bytes of the span itself -- no stage-1 side array
   is read.  The same compare locates a control byte (< 0x20), which JSON
   rejects.  A body that does contain a backslash is materialised into an
   arena that is reused across strings and runs, and the record points into
   that arena.

   Event stream (expanded by z_expand to the flat reference stream):
     non-string token : tag byte, plus 8 bytes after T_NUM
     string           : tag byte, u32 out length, u64 payload
                        payload bit 63 = 1: plain span, low bits = input offset
                        payload bit 63 = 0: escaped, low bits = arena offset

   Requires AVX2.  p must be readable 32 bytes past its body (the input is
   padded for the stage-1 block reads; a 32-byte load is used for the tail). */
#ifndef STRZ_H
#define STRZ_H

#include <immintrin.h>

#ifdef ZF_GATE
/* Per-document choice between the serial kernels and the empty-mask
   shortcut, made once from a sample of the document. */
extern int zf_fast_gate;
#endif

#ifndef Z_ESC24
#define Z_ESC24 0
#endif

typedef struct {
    Out ev;                 /* event stream (hash = 0) */
    uint8_t *ar;            /* arena for escaped bodies */
    size_t alen, acap;
} ZOut;

#ifdef Z_STATS
uint64_t z_st_nstr, z_st_nplain, z_st_nesc, z_st_nctl;
uint64_t z_st_plain_bytes, z_st_esc_bytes, z_st_esc_out;
#endif

static void z_init(ZOut *z) {
    memset(z, 0, sizeof *z);
    out_init(&z->ev, 0);
}

static void z_free(ZOut *z) {
    out_free(&z->ev);
    free(z->ar);
    z->ar = NULL;
    z->alen = z->acap = 0;
}

/* keep the buffers, drop the contents: the arena is reused across strings and
   across whole runs, never reallocated per string */
static void z_reset(ZOut *z) {
    z->ev.len = 0;
    z->alen = 0;
}

static void z_arena_reserve(ZOut *z, size_t need) {
    if (z->alen + need <= z->acap) return;
    size_t nc = z->acap ? z->acap : 4096;
    while (nc < z->alen + need) nc <<= 1;
    uint8_t *nb = (uint8_t *)realloc(z->ar, nc);
    if (!nb) { fprintf(stderr, "oom\n"); exit(2); }
    z->ar = nb;
    z->acap = nc;
}

#define Z_NONE UINT64_MAX

/* First byte of the body that is either a backslash or a control byte.
   Returns Z_NONE when the body is plain.  *is_bs distinguishes the two. */
__attribute__((always_inline)) static inline uint64_t
z_scan(const uint8_t *p, uint64_t n, int *is_bs) {
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    uint64_t i = 0;
    while (i + 32 <= n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        __m256i ctl = _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v);
        __m256i bs = _mm256_cmpeq_epi8(v, vbs);
        unsigned m = (unsigned)_mm256_movemask_epi8(_mm256_or_si256(ctl, bs));
        if (m) {
            unsigned b = (unsigned)__builtin_ctz(m);
            *is_bs = (p[i + b] == '\\');
            return i + b;
        }
        i += 32;
    }
    if (i < n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        __m256i ctl = _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v);
        __m256i bs = _mm256_cmpeq_epi8(v, vbs);
        unsigned m = (unsigned)_mm256_movemask_epi8(_mm256_or_si256(ctl, bs));
        m &= (1u << (unsigned)(n - i)) - 1u;
        if (m) {
            unsigned b = (unsigned)__builtin_ctz(m);
            *is_bs = (p[i + b] == '\\');
            return i + b;
        }
    }
    return Z_NONE;
}

/* Control bytes only: used by the stage-1 class prefilter variant, which has
   already been told the body holds no backslash. */
__attribute__((always_inline)) static inline uint64_t
z_scan_ctl(const uint8_t *p, uint64_t n) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    uint64_t i = 0;
    while (i + 32 <= n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = (unsigned)_mm256_movemask_epi8(
            _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v));
        if (m) return i + (unsigned)__builtin_ctz(m);
        i += 32;
    }
    if (i < n) {
        __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
        unsigned m = (unsigned)_mm256_movemask_epi8(
            _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v));
        m &= (1u << (unsigned)(n - i)) - 1u;
        if (m) return i + (unsigned)__builtin_ctz(m);
    }
    return Z_NONE;
}

#ifndef Z_INLINE
#define Z_INLINE 0
#endif
#if Z_INLINE
#define ZBODY __attribute__((always_inline)) static inline
#else
#define ZBODY static
#endif

/* Emit one string.  key selects T_KEY/T_STR.  Returns 1 on success; on a
   malformed body sets the error at exactly the offset the reference reports
   (a control byte, or whatever uj_decode rejects for an escaped body). */
ZBODY int od_string_body_z(OdCur *c, ZOut *z, const uint8_t *p, uint64_t len,
                           int key) {
    uint64_t pos = (uint64_t)(p - c->b);
#ifdef SKIP_STR_FULL
    /* budget ablation only: keep the event shape, drop the body work */
    {
        uint32_t ol = (uint32_t)len;
        uint64_t rec = pos | (1ULL << 63);
        out_reserve(&z->ev, 13);
        uint8_t *e = z->ev.b + z->ev.len;
        e[0] = (uint8_t)(key ? T_KEY : T_STR);
        memcpy(e + 1, &ol, 4);
        memcpy(e + 5, &rec, 8);
        z->ev.len += 13;
        return 1;
    }
#endif
    int is_bs = 0;
    uint64_t off = z_scan(p, len, &is_bs);
    int plain = (off == Z_NONE);
    uint64_t roff;

    if (plain) {
        roff = pos;
    } else if (!is_bs) {
#ifdef Z_STATS
        z_st_nctl++;
#endif
        return od_fail(c, pos + off, "string");
    } else {
        /* materialise only escaped bodies, appended to the reused arena */
        z_arena_reserve(z, (size_t)len + 32);
        size_t ei = 0;
#if Z_ESC24
        size_t on = ze_decode(p, len, z->ar + z->alen, &ei);
#else
        size_t on = uj_decode(p, len, z->ar + z->alen, &ei);
#endif
        if (on == (size_t)-1) return od_fail(c, pos + ei, "string");
        roff = z->alen;
        z->alen += on;
        uint32_t ol = (uint32_t)on;
        uint64_t rec = roff;
        out_reserve(&z->ev, 13);
        uint8_t *e = z->ev.b + z->ev.len;
        e[0] = (uint8_t)(key ? T_KEY : T_STR);
        memcpy(e + 1, &ol, 4);
        memcpy(e + 5, &rec, 8);
        z->ev.len += 13;
#ifdef Z_STATS
        z_st_nstr++; z_st_nesc++; z_st_esc_bytes += len; z_st_esc_out += on;
#endif
        return 1;
    }

    uint32_t ol = (uint32_t)len;
    uint64_t rec = roff | (1ULL << 63);
    out_reserve(&z->ev, 13);
    uint8_t *e = z->ev.b + z->ev.len;
    e[0] = (uint8_t)(key ? T_KEY : T_STR);
    memcpy(e + 1, &ol, 4);
    memcpy(e + 5, &rec, 8);
    z->ev.len += 13;
#ifdef Z_STATS
    z_st_nstr++; z_st_nplain++; z_st_plain_bytes += len;
#endif
    return 1;
}

/* Same, with the stage-1 per-block backslash flag folded in: when the class
   bytes of every block the body touches are clean, the backslash compare is
   dropped and only control bytes are located. */
ZBODY int od_string_body_z_cls(OdCur *c, ZOut *z, const uint8_t *p, uint64_t len,
                               int key, int known_clean) {
    if (!known_clean) return od_string_body_z(c, z, p, len, key);
    uint64_t pos = (uint64_t)(p - c->b);
    uint64_t off = z_scan_ctl(p, len);
    if (off != Z_NONE) {
#ifdef Z_STATS
        z_st_nctl++;
#endif
        return od_fail(c, pos + off, "string");
    }
    uint32_t ol = (uint32_t)len;
    uint64_t rec = pos | (1ULL << 63);
    out_reserve(&z->ev, 13);
    uint8_t *e = z->ev.b + z->ev.len;
    e[0] = (uint8_t)(key ? T_KEY : T_STR);
    memcpy(e + 1, &ol, 4);
    memcpy(e + 5, &rec, 8);
    z->ev.len += 13;
#ifdef Z_STATS
    z_st_nstr++; z_st_nplain++; z_st_plain_bytes += len;
#endif
    return 1;
}

/* The same record, emitted from one fused traversal instead of the shipped
   two (z_scan to classify, then ze_decode to materialise).
     - a definite bulk accept means the body is valid: a plain body emits a
       span and is never written, an escaped body is decoded by the trusting
       copy step in the same pass;
     - anything else (an adjacent backslash pair, or a real violation) goes
       through the serial validator, which is what produces the reference's
       first-error offset; the body is then decoded exactly as before.
   Offsets and decoded bytes are the reference's, verified by the differential
   in zb.c and by the walk gate. */
ZBODY int od_string_body_f(OdCur *c, ZOut *z, const uint8_t *p, uint64_t len,
                           int key) {
    uint64_t pos = (uint64_t)(p - c->b);
    z_arena_reserve(z, (size_t)len + 32);
    int esc = 0;
    uint64_t outn = 0, err = 0;
#ifdef ZF_GATE
    int ok = zf_fast_gate
                 ? zf_span64f(p, len, z->ar + z->alen, &esc, &outn, &err)
                 : zf_span64(p, len, z->ar + z->alen, &esc, &outn, &err);
#else
    int ok = zf_span64(p, len, z->ar + z->alen, &esc, &outn, &err);
#endif
    if (!ok)
        return od_fail(c, pos + err, "string");
    uint32_t ol = (uint32_t)outn;
    uint64_t rec = esc ? z->alen : pos;
    if (esc) z->alen += outn;
    out_reserve(&z->ev, 13);
    uint8_t *e = z->ev.b + z->ev.len;
    e[0] = (uint8_t)(key ? T_KEY : T_STR);
    memcpy(e + 1, &ol, 4);
    if (!esc) rec |= 1ULL << 63;
    memcpy(e + 5, &rec, 8);
    z->ev.len += 13;
    return 1;
}

/* Expand the event stream to the flat reference encoding.  `input` is the
   document the spans point into. */
static void z_expand(const ZOut *z, const uint8_t *input, Out *flat) {
    const uint8_t *e = z->ev.b;
    size_t i = 0, n = z->ev.len;
    while (i < n) {
        uint8_t tag = e[i];
        if (tag == T_KEY || tag == T_STR) {
            uint32_t len;
            uint64_t rec;
            memcpy(&len, e + i + 1, 4);
            memcpy(&rec, e + i + 5, 8);
            out_tag(flat, tag);
            out_u32(flat, len);
            if (rec >> 63)
                out_raw(flat, input + (rec & ~(1ULL << 63)), len);
            else
                out_raw(flat, z->ar + rec, len);
            i += 13;
        } else if (tag == T_NUM) {
            out_raw(flat, e + i, 9);
            i += 9;
        } else {
            out_raw(flat, e + i, 1);
            i += 1;
        }
    }
}

#endif /* STRZ_H */
