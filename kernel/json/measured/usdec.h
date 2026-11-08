/* usdec.h -- one-pass SIMD JSON string-body unescaper.  Scratch experiment;
   nothing here belongs to the repository.

   Contract: identical accept/reject, identical error offset (body-relative),
   identical output bytes and length to uj_decode().  Requires 32 readable
   bytes at p and 32 bytes of slack at dst past the last output byte (the run
   store writes a whole vector).

   Shape: a window is loaded once, one mask of *control-byte-or-backslash*
   positions is derived, and that mask is consumed.  The run before a special
   is written with one vector store, a control byte fails at its own offset,
   and a backslash goes through the escape step.  An escape that stays inside
   the window costs no reload and no re-mask: `cur` advances and the consumed
   bits are cleared.

   Every store is a whole vector that over-writes forward.  That is what makes
   the run copy unconditional: a zero-length run costs the same store as a ten
   byte run, so the inner loop has no data-dependent branch on the run length.
   (Spike 35 measured that branch as worth 177 -> 508 ns/body on the same
   escapes at even versus random spacing, with the escape work unchanged.)

   Classification carries all four classes the format asks for (control,
   backslash, quote, hex digit) in one class byte per input byte:
     class = LO[byte & 0x0F] & HI[byte >> 4]
   so one shuffle pair answers every class question at once.  US_CLS=1 reads
   the control and backslash masks out of that class byte; US_CLS=0 (the
   default, measured faster when only those two classes are needed) uses two
   compares.  The hex class is used where it pays: validating and combining a
   \\uXXXX escape's four digits (US_HEX=1).

   Error offsets are the reference's: the first bad byte in offset order, a
   control byte at its own offset and a malformed escape at its backslash. */
#ifndef USDEC_H
#define USDEC_H

#include <immintrin.h>

#ifndef US_CLS
#define US_CLS 0          /* 0 compares, 1 pshufb class byte */
#endif
#ifndef US_HEX
#define US_HEX 1          /* 0 scalar hex table, 1 pshufb 4-digit */
#endif
#ifndef US_W
#define US_W 64           /* window: 32 or 64 bytes */
#endif
#ifndef US_ENC
#define US_ENC 0          /* 0 branch-free encoder, 1 branchy encoder */
#endif
#ifndef US_EMIT4
#define US_EMIT4 0        /* 1: the encoded \u word stored with one 4-byte
                             store (the word is at most four bytes) instead of
                             the 8-byte store; spike-43 measured it <= 2
                             ns/block better on canonical and never worse */
#endif
#ifndef US_ESC
#define US_ESC 0          /* 0 simple inline + \u inline, 1 branch-free,
                             2 simple inline + \u out of line */
#endif
#ifndef US_DIAG
/* Timing probes only (wrong output): 1 stops after the window scan, 2 decodes
   every escape as a simple one and skips the \u path, 3 keeps the mask loop
   but skips the escape step, 4 keeps the escape step but skips the run stores,
   5 keeps only the loop and the mask bookkeeping. */
#define US_DIAG 0
#endif
#ifndef US_FUSED
#define US_FUSED 0        /* 0 z_scan then unescape from the backslash,
                             1 one fused body pass for both forms */
#endif
#ifndef US_SLOTS
/* 0: the variable-trip `while (m)` loop.  K>=1: K predicated fixed slots per
   window, then the variable loop for anything left.  US_SLOTS=1 is the same
   work as 0 with the predicated slot body, which separates the cost of the
   predication itself from the cost of a fixed trip count. */
#define US_SLOTS 0
#endif
#ifndef US_RUN2
#define US_RUN2 0         /* 1: both run vectors stored unconditionally */
#endif
#ifndef US_INLINE
/* 1: the unescaper is inlined into the caller instead of called.  Its
   prologue materialises twelve vector constants and pushes six registers on
   every escaped body; across bodies those are loop-invariant. */
#define US_INLINE 0
#endif
#ifndef US_CHAIN
/* 1: the mask update no longer waits for the escape's decoded length.  The
   common escape consumes two input bytes, so the bits below b+2 are cleared
   from the tzcnt result itself, and only a longer escape (\u, and then only a
   surrogate pair needs 12) recomputes the clear mask from the real advance.
   The loop-exit test is folded into the same mask, so the variable-trip loop
   has one data-dependent branch fewer per escape. */
#define US_CHAIN 0
#endif
#ifndef US_STATS
/* 1: count calls, windows, mask-loop entries, escapes by kind and the
   per-window popcount/escape histograms; printed at exit on stderr. */
#define US_STATS 0
#endif
#ifndef US_EXP
/* Bulk extraction of the window's escape positions, tested against the
   variable tzcnt loop (US_EXP=0):
     1  tzcnt chain into a per-window stack buffer, then a consume loop whose
        positions are data, so nothing between two escapes waits on the
        previous escape's decoded length
     2  POS8 table expansion into the same buffer: one 8-lane store per mask
        byte, the lanes are the bit positions of that byte
     3  a list (US_EXP_SRC 1 or 2) consumed in batches of US_EXP_K positions:
        every position of a batch is decoded before any of them is committed
     4  the positions packed one per byte of one register (up to eight; a
        denser window falls back to the tzcnt list), shifted out in the
        consume loop
   The consume loop still reports the reference's first error in offset order:
   a position already consumed by the previous escape is skipped before its
   validity is looked at. */
#define US_EXP 0
#endif
#ifndef US_EXP_SRC
#define US_EXP_SRC 1      /* extraction used by US_EXP=3: 1 tzcnt, 2 POS8 */
#endif
#ifndef US_EXP_K
#define US_EXP_K 4        /* positions decoded per batch (US_EXP=3) */
#endif

#if US_STATS
#include <stdio.h>
static uint64_t us_st_calls, us_st_bodybytes, us_st_windows, us_st_escwin;
static uint64_t us_st_escbytes, us_st_esc, us_st_kind[3];
static uint64_t us_st_pc[65], us_st_epw[65], us_st_chunks;
static uint64_t us_st_runlen[65];
static void __attribute__((destructor)) us_stats_dump(void) {
    fprintf(stderr, "USTAT calls=%llu bodybytes=%llu windows=%llu escwin=%llu escbytes=%llu\n",
            (unsigned long long)us_st_calls, (unsigned long long)us_st_bodybytes,
            (unsigned long long)us_st_windows, (unsigned long long)us_st_escwin,
            (unsigned long long)us_st_escbytes);
    fprintf(stderr, "USTAT esc=%llu simple=%llu u6=%llu pair12=%llu chunks=%llu\n",
            (unsigned long long)us_st_esc, (unsigned long long)us_st_kind[0],
            (unsigned long long)us_st_kind[1], (unsigned long long)us_st_kind[2],
            (unsigned long long)us_st_chunks);
    for (int k = 0; k < 65; k++)
        if (us_st_pc[k])
            fprintf(stderr, "USTAT pc %d %llu\n", k, (unsigned long long)us_st_pc[k]);
    for (int k = 0; k < 65; k++)
        if (us_st_epw[k])
            fprintf(stderr, "USTAT epw %d %llu\n", k, (unsigned long long)us_st_epw[k]);
    for (int k = 0; k < 65; k++)
        if (us_st_runlen[k])
            fprintf(stderr, "USTAT run %d %llu\n", k, (unsigned long long)us_st_runlen[k]);
}
#define US_ST(x) do { x; } while (0)
#else
#define US_ST(x) do { } while (0)
#endif

#define US_CTLB 1u
#define US_BSB  2u
#define US_QB   4u
#define US_HEXB 8u

/* Low-nibble contribution and high-nibble contribution of each class.  The
   AND of the two is non-zero for exactly the classified bytes. */
static const uint8_t US_LO[16] = {
    /* 0x?0 */ US_CTLB | US_HEXB,             /* '0'..'9' */
    /* 0x?1 */ US_CTLB | US_HEXB,             /* '1','A'..'F','a'..'f' */
    /* 0x?2 */ US_CTLB | US_HEXB | US_QB,     /* '2', '"' */
    /* 0x?3 */ US_CTLB | US_HEXB,
    /* 0x?4 */ US_CTLB | US_HEXB,
    /* 0x?5 */ US_CTLB | US_HEXB,
    /* 0x?6 */ US_CTLB | US_HEXB,
    /* 0x?7 */ US_CTLB,
    /* 0x?8 */ US_CTLB,
    /* 0x?9 */ US_CTLB,
    /* 0x?A */ US_CTLB,
    /* 0x?B */ US_CTLB,
    /* 0x?C */ US_CTLB | US_BSB,
    /* 0x?D */ US_CTLB,
    /* 0x?E */ US_CTLB,
    /* 0x?F */ US_CTLB,
};
static const uint8_t US_HI[16] = {
    /* 0x0? */ US_CTLB,
    /* 0x1? */ US_CTLB,
    /* 0x2? */ US_QB,
    /* 0x3? */ US_HEXB,
    /* 0x4? */ US_HEXB,
    /* 0x5? */ US_BSB,
    /* 0x6? */ US_HEXB,
    /* 0x7? */ 0,
    /* 0x8? */ 0, /* 0x9? */ 0, /* 0xA? */ 0, /* 0xB? */ 0,
    /* 0xC? */ 0, /* 0xD? */ 0, /* 0xE? */ 0, /* 0xF? */ 0,
};

/* class byte per input byte */
static inline __attribute__((always_inline)) __m256i
us_class(__m256i v) {
    __m256i lot = _mm256_setr_epi8(
        US_LO[0],US_LO[1],US_LO[2],US_LO[3],US_LO[4],US_LO[5],US_LO[6],US_LO[7],
        US_LO[8],US_LO[9],US_LO[10],US_LO[11],US_LO[12],US_LO[13],US_LO[14],US_LO[15],
        US_LO[0],US_LO[1],US_LO[2],US_LO[3],US_LO[4],US_LO[5],US_LO[6],US_LO[7],
        US_LO[8],US_LO[9],US_LO[10],US_LO[11],US_LO[12],US_LO[13],US_LO[14],US_LO[15]);
    __m256i hit = _mm256_setr_epi8(
        US_HI[0],US_HI[1],US_HI[2],US_HI[3],US_HI[4],US_HI[5],US_HI[6],US_HI[7],
        US_HI[8],US_HI[9],US_HI[10],US_HI[11],US_HI[12],US_HI[13],US_HI[14],US_HI[15],
        US_HI[0],US_HI[1],US_HI[2],US_HI[3],US_HI[4],US_HI[5],US_HI[6],US_HI[7],
        US_HI[8],US_HI[9],US_HI[10],US_HI[11],US_HI[12],US_HI[13],US_HI[14],US_HI[15]);
    __m256i ln = _mm256_and_si256(v, _mm256_set1_epi8(0x0F));
    __m256i hn = _mm256_and_si256(_mm256_srli_epi16(v, 4), _mm256_set1_epi8(0x0F));
    return _mm256_and_si256(_mm256_shuffle_epi8(lot, ln),
                            _mm256_shuffle_epi8(hit, hn));
}

/* pull class bit b of every byte into that byte's sign bit, then movemask.
   Bits above b can only land in the low bits of the next byte, never in a
   sign bit, so the extraction is exact. */
static inline __attribute__((always_inline)) unsigned
us_cmask(__m256i cls, int bit) {
    return (unsigned)_mm256_movemask_epi8(_mm256_slli_epi16(cls, 7 - bit));
}

/* combined control-or-backslash mask of a 32-byte vector */
static inline __attribute__((always_inline)) unsigned
us_special32(__m256i v) {
#if US_CLS
    __m256i cls = us_class(v);
    return us_cmask(cls, 0) | us_cmask(cls, 1);
#else
    const __m256i vbs = _mm256_set1_epi8('\\');
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    __m256i ctl = _mm256_cmpeq_epi8(_mm256_min_epu8(v, v19), v);
    __m256i bs = _mm256_cmpeq_epi8(v, vbs);
    return (unsigned)_mm256_movemask_epi8(_mm256_or_si256(ctl, bs));
#endif
}

/* ---- hex digits ---------------------------------------------------------- */

static inline __attribute__((always_inline)) int
us_hex4_scalar(const uint8_t *q, uint32_t *out) {
    int h0 = UJ_HEX[q[0]], h1 = UJ_HEX[q[1]];
    int h2 = UJ_HEX[q[2]], h3 = UJ_HEX[q[3]];
    if ((h0 | h1 | h2 | h3) < 0) return 0;
    *out = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
           ((uint32_t)h2 << 4) | (uint32_t)h3;
    return 1;
}

/* Four hex digits validated and combined with one 16-byte load: the digit
   value is the low nibble plus nine for a letter, and the class test is
   (byte-'0' <= 9) | ((byte|0x20)-'a' <= 5).  Only the first four lanes
   decide the result; the rest of the vector is read past the digits and
   ignored. */
static inline __attribute__((always_inline)) int
us_hex4_pshufb(const uint8_t *q, uint32_t *out) {
    __m128i v = _mm_loadu_si128((const __m128i *)q);
    __m128i d = _mm_sub_epi8(v, _mm_set1_epi8('0'));
    __m128i a = _mm_sub_epi8(_mm_or_si128(v, _mm_set1_epi8(0x20)),
                             _mm_set1_epi8('a'));
    __m128i isd = _mm_cmpeq_epi8(_mm_subs_epu8(d, _mm_set1_epi8(9)),
                                 _mm_setzero_si128());
    __m128i isa = _mm_cmpeq_epi8(_mm_subs_epu8(a, _mm_set1_epi8(5)),
                                 _mm_setzero_si128());
    if (((unsigned)_mm_movemask_epi8(_mm_or_si128(isd, isa)) & 0x0Fu) != 0x0Fu)
        return 0;
    __m128i lo = _mm_and_si128(v, _mm_set1_epi8(0x0F));
    __m128i val = _mm_add_epi8(lo, _mm_and_si128(isa, _mm_set1_epi8(9)));
    __m128i m1 = _mm_maddubs_epi16(val, _mm_set1_epi16(0x0110));   /* hi*16+lo */
    __m128i m2 = _mm_madd_epi16(m1, _mm_set1_epi32(0x00010100));   /* <<8, +  */
    *out = (uint32_t)_mm_cvtsi128_si32(m2) & 0xFFFF;
    return 1;
}

static inline __attribute__((always_inline)) int
us_hex4(const uint8_t *q, uint32_t *out) {
#if US_HEX
    return us_hex4_pshufb(q, out);
#else
    return us_hex4_scalar(q, out);
#endif
}

/* ---- escape step ---------------------------------------------------------
   p[i] is a backslash, i < n.  On success writes the decoded bytes at dst[j],
   advances *jp and sets *advp to the number of input bytes consumed.  On
   failure sets *err = i (the reference's offset) and returns 0. */
static inline __attribute__((always_inline)) void
us_emit(uint32_t cp, uint8_t *dst, uint64_t *jp) {
#if US_EMIT4
    int len;
    uint32_t w = uj_enc_word(cp, &len);
    memcpy(dst + *jp, &w, 4);
    *jp += (uint64_t)len;
#elif US_ENC
    uint8_t tmp[4];
    uint32_t len = uj_enc(tmp, cp);
    memcpy(dst + *jp, tmp, 4);
    *jp += len;
#else
    int len;
    uint32_t w = uj_enc_word(cp, &len);
    uint64_t word = (uint64_t)w;
    memcpy(dst + *jp, &word, 8);
    *jp += (uint64_t)len;
#endif
}

#if US_ESC == 2
static __attribute__((noinline)) int
#else
static inline __attribute__((always_inline)) int
#endif
us_esc_u(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
         uint64_t *advp, uint64_t *err) {
    if (i + 6 > n) { *err = i; return 0; }
    uint32_t cp;
    if (!us_hex4(p + i + 2, &cp)) { *err = i; return 0; }
    uint64_t adv = 6;
    if ((cp - 0xD800u) < 0x400u && i + 12 <= n && p[i + 6] == '\\' &&
        p[i + 7] == 'u') {
        uint32_t lo;
        if (us_hex4(p + i + 8, &lo) && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
        }
    }
    us_emit(cp, dst, jp);
    *advp = adv;
    return 1;
}

static inline __attribute__((always_inline)) int
us_esc(const uint8_t *p, uint64_t n, uint64_t i, uint8_t *dst, uint64_t *jp,
       uint64_t *advp, uint64_t *err) {
#if US_ESC == 1
    if (i + 12 > n) {
        if (i + 1 >= n) { *err = i; return 0; }
        unsigned c1 = p[i + 1];
        int8_t sv = UJ_UNESC[c1];
        if (sv >= 0) { dst[*jp] = (uint8_t)sv; *jp += 1; *advp = 2; return 1; }
        if (c1 != 'u') { *err = i; return 0; }
        return us_esc_u(p, n, i, dst, jp, advp, err);
    }
    /* branch-free: the class, the validity and the encoding are all computed
       and selected with conditional moves */
    uint64_t w;
    memcpy(&w, p + i + 1, 8);
    unsigned c1 = (unsigned)(w & 0xFFu);
    int isu = (c1 == 'u');
    int8_t sv = UJ_UNESC[c1];
    int h0 = UJ_HEX[(w >> 8) & 0xFF], h1 = UJ_HEX[(w >> 16) & 0xFF];
    int h2 = UJ_HEX[(w >> 24) & 0xFF], h3 = UJ_HEX[(w >> 32) & 0xFF];
    uint32_t cp = ((uint32_t)h0 << 12) | ((uint32_t)h1 << 8) |
                  ((uint32_t)h2 << 4) | (uint32_t)h3;
    int bad = isu ? ((h0 | h1 | h2 | h3) < 0) : (sv < 0);
    uint64_t adv = isu ? 6u : 2u;
    if (isu && (cp - 0xD800u) < 0x400u) {
        uint64_t w2;
        memcpy(&w2, p + i + 6, 8);
        int g0 = UJ_HEX[(w2 >> 16) & 0xFF], g1 = UJ_HEX[(w2 >> 24) & 0xFF];
        int g2 = UJ_HEX[(w2 >> 32) & 0xFF], g3 = UJ_HEX[(w2 >> 40) & 0xFF];
        uint32_t lo = ((uint32_t)g0 << 12) | ((uint32_t)g1 << 8) |
                      ((uint32_t)g2 << 4) | (uint32_t)g3;
        if ((w2 & 0xFFu) == '\\' && ((w2 >> 8) & 0xFFu) == 'u' &&
            (g0 | g1 | g2 | g3) >= 0 && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            adv = 12;
        }
    }
    if (bad) { *err = i; return 0; }
    if (isu) { us_emit(cp, dst, jp); *advp = adv; return 1; }
    dst[*jp] = (uint8_t)sv;
    *jp += 1;
    *advp = 2;
    return 1;
#else
    if (i + 1 >= n) { *err = i; return 0; }
    unsigned c1 = p[i + 1];
    int8_t sv = UJ_UNESC[c1];
    if (sv >= 0) {
        dst[*jp] = (uint8_t)sv;
        *jp += 1;
        *advp = 2;
        return 1;
    }
    if (c1 != 'u') { *err = i; return 0; }
    return us_esc_u(p, n, i, dst, jp, advp, err);
#endif
}

/* run store: whole vectors, over-writing up to 31 bytes past the run (the
   caller's slack and the next store make that harmless).  len <= win <= 64.

   US_RUN2 stores both vectors always: the second store's load address is
   selected instead of branching on len, so the single data-dependent branch in
   the run copy disappears (the load is always inside the vector just read). */
static inline __attribute__((always_inline)) void
us_run(const uint8_t *p, uint8_t *dst, uint64_t len) {
    _mm256_storeu_si256((__m256i *)dst, _mm256_loadu_si256((const __m256i *)p));
#if US_W == 64
#if US_RUN2
    _mm256_storeu_si256((__m256i *)(dst + 32),
                        _mm256_loadu_si256((const __m256i *)(p + (len > 32 ? 32 : 0))));
#else
    if (len > 32)
        _mm256_storeu_si256((__m256i *)(dst + 32),
                            _mm256_loadu_si256((const __m256i *)(p + 32)));
#endif
#else
    (void)len;
#endif
}

/* One escape decoded out of the window order: the value and the two lengths
   are functions of the position alone, so a batch of these can be issued
   before any of them is committed.  Same accept/reject and same error offset
   as us_esc, with the control-byte and backslash cases both folded in. */
typedef struct {
    uint64_t word;            /* decoded bytes, one 64-bit word (8 of slack) */
    uint8_t ok, outlen, inlen;
} USX;

static inline __attribute__((always_inline)) USX
us_xdec(const uint8_t *p, uint64_t n, uint64_t at) {
    USX d;
    if (p[at] < 0x20) { d.ok = 0; return d; }        /* control byte */
    if (at + 1 >= n) { d.ok = 0; return d; }
    unsigned c1 = p[at + 1];
    int8_t sv = UJ_UNESC[c1];
    if (sv >= 0) {
        d.word = (uint8_t)sv; d.outlen = 1; d.inlen = 2; d.ok = 1;
        return d;
    }
    if (c1 != 'u') { d.ok = 0; return d; }
    if (at + 6 > n) { d.ok = 0; return d; }
    uint32_t cp;
    if (!us_hex4(p + at + 2, &cp)) { d.ok = 0; return d; }
    uint64_t inlen = 6;
    if ((cp - 0xD800u) < 0x400u && at + 12 <= n && p[at + 6] == '\\' &&
        p[at + 7] == 'u') {
        uint32_t lo;
        if (us_hex4(p + at + 8, &lo) && (lo - 0xDC00u) < 0x400u) {
            cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
            inlen = 12;
        }
    }
    int len;
    uint32_t w = uj_enc_word(cp, &len);
    d.word = w; d.outlen = (uint8_t)len; d.inlen = (uint8_t)inlen; d.ok = 1;
    return d;
}
/* ---- bulk position extraction (US_EXP) ---------------------------------- */
#if US_EXP
#include "us_pos8.inc"
static volatile unsigned us_xsink;

/* positions of the set bits of the window mask, in increasing order, into a
   stack buffer; returns their count.  win <= 64, so a position is one byte. */
static inline __attribute__((always_inline)) unsigned
us_xlist_tzcnt(uint64_t m, uint8_t *pos) {
    unsigned k = 0;
    do {
        pos[k++] = (uint8_t)__builtin_ctzll(m);
        m &= m - 1;
    } while (m);
    return k;
}

/* One 8-lane store per non-empty mask byte: the row is that byte's set-bit
   positions, in order, padded; the byte's chunk offset is added to every lane
   in the same 64-bit add (8*ch + 7 <= 63, so no lane carries).  The chunk
   mask picks the bytes that hold anything, so a sparse window touches only
   the rows it needs. */
static inline __attribute__((always_inline)) unsigned
us_xlist_pos8(uint64_t m, uint8_t *pos) {
    uint64_t t = m | (m >> 1);
    t |= t >> 2;
    t |= t >> 4;
    uint64_t cm = _pext_u64(t, 0x0101010101010101ULL);
    unsigned k = 0;
    while (cm) {
        unsigned ch = (unsigned)__builtin_ctzll(cm);
        cm &= cm - 1;
        unsigned x = (unsigned)((m >> (8 * ch)) & 0xFFu);
        uint64_t row;
        memcpy(&row, US_POS8B[x], 8);
        row += 0x0808080808080808ULL * (uint64_t)ch;
        memcpy(pos + k, &row, 8);
        k += (unsigned)__builtin_popcount(x);
    }
    return k;
}

#endif /* US_EXP */

#define US_FAIL ((size_t)-1)

#if US_RUN2
#define US_SLACK 64
#else
#define US_SLACK 32
#endif

/* ---- predicated fixed slots ----------------------------------------------
   US_SLOTS=K consumes the window's special mask with K straight-line slots.
   Nothing about a slot depends on whether it holds a special:

     * the bit position is `min(tzcnt(m), win)`, so an empty slot reads the
       window end rather than branching on `m == 0`;
     * the run is stored unconditionally (a zero-length run is the same store);
     * the escape step runs with its destination selected to a sink, and its
       failure is discarded, when the slot is empty.

   So the trip count of the chain is a constant.  Bits left after K slots (a
   window with more than K escapes) fall through to the same variable loop the
   US_SLOTS=0 build uses. */
static uint8_t us_sink[64] __attribute__((aligned(32)));
/* an empty slot's escape step runs on this instead of on document bytes: the
   path it takes is then the same one every time (`\\` then `x`, not a valid
   escape), so it cannot branch on whatever byte happens to sit at the window
   end.  16 bytes so the bounds check reads inside the buffer. */
static const uint8_t us_dummy[16] = {
    '\\', 'x', 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
};

/* One predicated slot over the locals of the window loop: no state struct, so
   the compiler keeps i/j/cur/m in registers. */
#define US_SLOT()                                                              \
    do {                                                                       \
        uint64_t _m = m;                                                       \
        unsigned _has = (_m != 0);                                             \
        unsigned _b = (unsigned)_tzcnt_u64(_m);                                \
        if (_b > (unsigned)win) _b = (unsigned)win;                            \
        uint64_t _run = ((uint64_t)_b > cur) ? (uint64_t)_b - cur : 0;         \
        us_run(p + i + cur, dst + j, _run);                                    \
        j += _run;                                                             \
        uint64_t _jt = _has ? j : 0;                                           \
        const uint8_t *_q = _has ? p : us_dummy;                               \
        uint64_t _qi = _has ? i + _b : 0;                                      \
        uint64_t _adv = 2, _eo = _qi;                                          \
        int _ok = us_esc(_q, _has ? n : 16, _qi, _has ? dst : us_sink, &_jt,   \
                         &_adv, &_eo);                                         \
        if (__builtin_expect(_has & ((_q[_qi] < 0x20) | !_ok), 0)) {           \
            *err = (size_t)(i + _b);                                           \
            return US_FAIL;                                                    \
        }                                                                      \
        j = _has ? _jt : j;                                                    \
        uint64_t _c = _has ? (uint64_t)_b + _adv                               \
                           : (((uint64_t)_b > cur) ? (uint64_t)_b : cur);      \
        m = (_has && _c < win)                                                 \
                ? (_m & ~(((uint64_t)1 << (_c & 63)) - 1))                     \
                : 0;                                                           \
        cur = _c;                                                              \
    } while (0)

/* Decode a body of n bytes at p into dst.  Returns the decoded length, or
   US_FAIL with *err = body-relative offset of the offending byte. */
static size_t us_dec_kernel(const uint8_t *p, uint64_t n, uint8_t *dst,
                            size_t *err) {
    uint64_t i = 0, j = 0;
    US_ST(us_st_calls++; us_st_bodybytes += n);
    while (i < n) {
        uint64_t rem = n - i;
        uint64_t win, m;
#if US_W == 64
        if (rem >= 64) {
            __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + i));
            __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + i + 32));
            m = (uint64_t)us_special32(v0) | ((uint64_t)us_special32(v1) << 32);
            if (!m) {
                _mm256_storeu_si256((__m256i *)(dst + j), v0);
                _mm256_storeu_si256((__m256i *)(dst + j + 32), v1);
                j += 64; i += 64;
                continue;
            }
            win = 64;
        } else
#endif
        {
            __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
            win = (rem < 32) ? rem : 32;
            m = (uint64_t)us_special32(v);
            if (win < 32) m &= ((uint64_t)1 << win) - 1;
            if (!m) {
                _mm256_storeu_si256((__m256i *)(dst + j), v);
                j += win; i += win;
                continue;
            }
        }
        {
#if US_DIAG == 1
            {   /* scan-only probe */
                uint64_t take = win;
                _mm256_storeu_si256((__m256i *)(dst + j),
                                    _mm256_loadu_si256((const __m256i *)(p + i)));
                j += take; i += take;
                continue;
            }
#endif
            uint64_t cur = 0;
#if US_STATS
            uint64_t _nw = 0;
            us_st_windows++;
            us_st_escwin++;
            us_st_pc[__builtin_popcountll(m)]++;
            for (int _k = 0; _k < 8; _k++)
                if (m & (0xFFULL << (8 * _k))) us_st_chunks++;
#endif
#if US_DIAG == 6
            {   /* probe: the mask is computed, its consumption is not; copy the
                   whole window, so q2 - q2d6 prices the mask machinery and
                   q2d6 - q2d1 the tzcnt loop */
                us_run(p + i, dst + j, win);
                j += win;
                i += win;
                continue;
            }
#endif
#if US_SLOTS >= 1
            {
#if US_SLOTS >= 2
                US_SLOT();
#endif
#if US_SLOTS >= 3
                US_SLOT();
#endif
#if US_SLOTS >= 4
                US_SLOT();
#endif
            }
#endif
#if US_EXP == 6
            {   /* probe: extract the list and drop it, then run the baseline
                   loop; prices the extraction alone */
                uint8_t xp[80];
                unsigned nk = us_xlist_tzcnt(m, xp);
                us_xsink = nk;
            }
#endif
#if US_EXP == 0 || US_EXP == 6
            while (m) {
                unsigned b = (unsigned)__builtin_ctzll(m);
                /* unconditional: a zero-length run costs the same store as a
                   long one, so the run length is not a branch */
#if US_DIAG == 4 || US_DIAG == 5
                (void)us_run;              /* probe: no run stores */
#else
                us_run(p + i + cur, dst + j, (uint64_t)b - cur);
#endif
                j += (uint64_t)b - cur;
                uint64_t at = i + b;
                US_ST(us_st_esc++; _nw++;
                     us_st_runlen[(uint64_t)b - cur < 64 ? (uint64_t)b - cur : 64]++);
                if (p[at] < 0x20) { *err = (size_t)at; return US_FAIL; }
                uint64_t adv;
#if US_DIAG == 3 || US_DIAG == 5
                adv = 2;                   /* probe: no escape step */
#elif US_DIAG == 2
                {   /* simple-escape-only probe: never the \u path */
                    int8_t sv = (at + 1 < n) ? UJ_UNESC[p[at + 1]] : -1;
                    dst[j] = (uint8_t)(sv < 0 ? 0xF0 : sv);
                    j += 1;
                    adv = 2;
                }
#else
                if (!us_esc(p, n, at, dst, &j, &adv, err)) return US_FAIL;
#endif
                US_ST(us_st_kind[adv == 2 ? 0 : (adv == 6 ? 1 : 2)]++);
#if US_CHAIN
                {
                    uint64_t nb2 = (uint64_t)b + 2;
                    cur = nb2;
                    /* nb2 < win <= 64, so the shift below is in range */
                    uint64_t keep = (nb2 < win) ? ~(((uint64_t)1 << nb2) - 1) : 0;
                    if (__builtin_expect(adv != 2, 0)) {
                        uint64_t nc = (uint64_t)b + adv;
                        keep = (nc < win) ? ~(((uint64_t)1 << nc) - 1) : 0;
                        cur = nc;
                    }
                    m &= keep;
                }
#else
                cur = (uint64_t)b + adv;
                if (cur >= win) break;
                m &= ~(((uint64_t)1 << cur) - 1);
#endif
            }
#elif US_EXP == 4
            /* register-resident list: the window's positions packed one per
               byte of one 64-bit register (a window with more than eight
               positions falls back to the stack buffer).  The consume loop
               shifts the next position out instead of loading it, and nothing
               between two escapes waits on the previous escape's length. */
            {
            uint8_t xp[80];
            unsigned nk;
            uint64_t q = 0;
            if (__builtin_popcountll(m) <= 8) {
                uint64_t mm = m;
                unsigned t = 0;
                do {
                    q |= (uint64_t)__builtin_ctzll(mm) << (8 * t);
                    mm &= mm - 1;
                    t++;
                } while (mm);
                nk = t;
                for (unsigned t2 = 0; t2 < nk; t2++) {
                    unsigned b = (unsigned)(q & 0xFFu);
                    q >>= 8;
                    if ((uint64_t)b < cur) continue;
                    us_run(p + i + cur, dst + j, (uint64_t)b - cur);
                    j += (uint64_t)b - cur;
                    uint64_t at = i + b;
                    if (p[at] < 0x20) { *err = (size_t)at; return US_FAIL; }
                    uint64_t adv;
                    if (!us_esc(p, n, at, dst, &j, &adv, err)) return US_FAIL;
                    cur = (uint64_t)b + adv;
                }
                goto us_exp_done;
            }
            nk = us_xlist_tzcnt(m, xp);
            for (unsigned t2 = 0; t2 < nk; t2++) {
                unsigned b = xp[t2];
                if ((uint64_t)b < cur) continue;
                us_run(p + i + cur, dst + j, (uint64_t)b - cur);
                j += (uint64_t)b - cur;
                uint64_t at = i + b;
                if (p[at] < 0x20) { *err = (size_t)at; return US_FAIL; }
                uint64_t adv;
                if (!us_esc(p, n, at, dst, &j, &adv, err)) return US_FAIL;
                cur = (uint64_t)b + adv;
            }
us_exp_done:;
            }
#else
            /* bulk extraction: the window's positions become data, so the
               consume loop carries no tzcnt/mask chain between two escapes and
               an escape's loads start as soon as its position is read. */
            uint8_t xp[80];
            unsigned nk;
#if US_EXP == 2 || (US_EXP == 3 && US_EXP_SRC == 2)
            nk = us_xlist_pos8(m, xp);
#else
            nk = us_xlist_tzcnt(m, xp);
#endif
#if US_EXP == 3
            for (unsigned t = 0; t < nk; t += US_EXP_K) {
                USX d[US_EXP_K];
                unsigned nq = nk - t;
                if (nq > US_EXP_K) nq = US_EXP_K;
                /* decode phase: every position of the batch is independent */
                for (unsigned q = 0; q < nq; q++)
                    d[q] = us_xdec(p, n, i + xp[t + q]);
                /* commit phase: only the write cursor and the input cursor
                   are serial */
                for (unsigned q = 0; q < nq; q++) {
                    unsigned b = xp[t + q];
                    if ((uint64_t)b < cur) continue;
                    us_run(p + i + cur, dst + j, (uint64_t)b - cur);
                    j += (uint64_t)b - cur;
                    if (!d[q].ok) { *err = (size_t)(i + b); return US_FAIL; }
                    memcpy(dst + j, &d[q].word, 8);
                    j += d[q].outlen;
                    cur = (uint64_t)b + d[q].inlen;
                }
            }
#else
            for (unsigned t = 0; t < nk; t++) {
                unsigned b = xp[t];
                /* a position the previous escape consumed (`\\`, or the `\u`
                   of a low surrogate) is not an escape */
                if ((uint64_t)b < cur) continue;
                us_run(p + i + cur, dst + j, (uint64_t)b - cur);
                j += (uint64_t)b - cur;
                uint64_t at = i + b;
                if (p[at] < 0x20) { *err = (size_t)at; return US_FAIL; }
                uint64_t adv;
                if (!us_esc(p, n, at, dst, &j, &adv, err)) return US_FAIL;
                cur = (uint64_t)b + adv;
            }
#endif
#endif /* US_EXP */
            /* both sides of "did the last escape cross the window?" are the
               same store: a zero length run writes the same vector, and those
               bytes are re-written by the next window's first store (or lie
               past the returned length). */
            uint64_t nxt = (cur < win) ? win : cur;
            uint64_t len = nxt - cur;
#if US_DIAG != 4 && US_DIAG != 5
            us_run(p + i + cur, dst + j, len);
#endif
            US_ST(us_st_epw[_nw]++);
            j += len;
            i += nxt;
        }
    }
    return (size_t)j;
}

#if US_INLINE
static inline __attribute__((always_inline)) size_t
#else
__attribute__((noinline)) static size_t
#endif
us_dec(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err) {
    return us_dec_kernel(p, n, dst, err);
}

/* ---- consuming the stage-1 escape-position list ---------------------------

   `xp` holds document offsets, in increasing order, of every byte inside a
   string that is a control byte or the first backslash of a run.  Stage 1
   builds it in its classify loop (xlist.h), so the body pass does no window
   mask, no tzcnt chain and no per-position test for the companion backslash of
   `\\`: the copy between two positions is a straight sequence.  The only
   position a decoded escape can still consume is the second `\` of a
   surrogate pair, and that is one loop after the escape, not a test per
   position.

   `*xj` is the caller's cursor and advances monotonically across bodies in
   document order; `pos0` is the body's document offset. */
#ifndef US_XP_DIAG
#define US_XP_DIAG 0
#endif

/* US_XP_TRACE: the gate records the documents offsets the consumer visits, to
   compare them, element for element, with the window mask loop's. */
#ifdef US_XP_TRACE
extern uint32_t *us_xp_visited;
extern uint64_t us_xp_nvis;
#endif

/* copy a run of any length: exact 64-byte chunks while more than a window is
   left, then the vector store that over-writes forward */
static inline __attribute__((always_inline)) void
us_run_long(const uint8_t *p, uint8_t *dst, uint64_t len) {
    uint64_t k = 0;
    while (len - k > 64) {
        _mm256_storeu_si256((__m256i *)(dst + k),
                            _mm256_loadu_si256((const __m256i *)(p + k)));
        _mm256_storeu_si256((__m256i *)(dst + k + 32),
                            _mm256_loadu_si256((const __m256i *)(p + k + 32)));
        k += 64;
    }
    us_run(p + k, dst + k, len - k);
}

/* out of line in every build: the floor probe must pay the same call as the
   real consumer, otherwise the DIAG=6 binary inlines the copy and the
   consumption figure prices a call that the real path still pays */
#ifndef US_XP_INLINE
#define US_XP_INLINE 0
#endif
#if US_XP_INLINE
__attribute__((always_inline)) static inline size_t
#else
__attribute__((noinline)) static size_t
#endif
us_dec_x(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
         const uint32_t *xp, uint64_t *xj, uint64_t nxp, uint64_t pos0) {
    uint64_t k = *xj, i = 0, j = 0;
    uint64_t endp = pos0 + n;
#if US_XP_DIAG == 6
    /* floor probe: the body is copied and no position is looked at */
    (void)k; (void)endp;
    us_run(p, dst, n);
    *err = 0;
    return (size_t)n;
#endif
    while (k < nxp && (uint64_t)xp[k] < pos0) k++;
    while (k < nxp) {
        uint64_t q = (uint64_t)xp[k];
        if (q >= endp) break;
        k++;
        {
            uint64_t b = q - pos0;
#ifdef US_XP_TRACE
            us_xp_visited[us_xp_nvis++] = (uint32_t)q;
#endif
#if US_XP_DIAG != 2 && US_XP_DIAG != 3
            us_run_long(p + i, dst + j, b - i);
#endif
            j += b - i;
#if US_XP_DIAG == 3
            i = b + 1;
#else
            if (US_XP_DIAG != 1 && p[b] < 0x20) {
                *err = (size_t)b; *xj = k; return US_FAIL;
            }
            {
                uint64_t adv;
#if US_XP_DIAG == 1
                adv = 2;
#else
                if (!us_esc(p, n, b, dst, &j, &adv, err)) {
                    *xj = k;
                    return US_FAIL;
                }
#endif
                i = b + adv;
                /* A decoded escape consumes at most one further position: the
                   second `\u` of a surrogate pair, which is exactly the
                   adv == 12 case.  The companion of `\\` never reaches the
                   list. */
                k += (adv == 12);
            }
#endif
        }
    }
#if US_XP_DIAG != 2 && US_XP_DIAG != 3
    us_run_long(p + i, dst + j, n - i);
#endif
    *xj = k;
    if (US_XP_DIAG == 2 || US_XP_DIAG == 3) return (size_t)n;
    return (size_t)(j + (n - i));
}

/* ---- consuming the stage-1 per-block escape masks ------------------------

   `em` holds one 64-bit escape mask per document block: bit k set means byte
   64*blk+k inside a string is a control byte or the first backslash of a run,
   exactly the set the compacted list holds.

   The body's byte range alone selects the lanes: the first block's mask is
   shifted down to the body start, the last block's is cut at the body end, and
   the blocks between are walked whole.  No per-body cursor and no per-position
   range test is needed.  A position consumed by the previous escape (the
   second `\u` of a surrogate pair) is skipped because it lies below the input
   cursor; the companion of `\\` is not in the mask at all. */

/* Does the body [pos0, pos0+len) hold any escape lane?  The common case is a
   body inside one block, which is one load and one shift/mask. */
static inline __attribute__((always_inline)) int
us_mask_any(const uint64_t *em, uint64_t pos0, uint64_t len) {
    if (!len) return 0;
    uint64_t endp = pos0 + len;
    uint64_t b0 = pos0 >> 6, b1 = (endp - 1) >> 6;
    unsigned lo = (unsigned)(pos0 & 63);
    unsigned hi = (unsigned)((endp - 1) & 63);
    if (b0 == b1) {
        unsigned span = hi - lo + 1;              /* 1..64 */
        uint64_t m = em[b0] >> lo;
        return (m & (span >= 64 ? ~0ULL : ((uint64_t)1 << span) - 1)) != 0;
    }
    if ((em[b0] >> lo) != 0) return 1;
    for (uint64_t b = b0 + 1; b < b1; b++)
        if (em[b]) return 1;
    return (em[b1] & (hi == 63 ? ~0ULL : ((uint64_t)1 << (hi + 1)) - 1)) != 0;
}

/* Decode a body from the masks.  The caller has already established through
   us_mask_any that at least one lane is in range.

   US_XM_DIAG probes (wrong output, timing only):
     6  copy the body, look at no lane (the floor both consumers share)
     3  walk the lanes, no run store and no escape step
     1  walk the lanes and the run stores, no escape step
     2  walk the lanes and the escape step, no run stores */
#ifndef US_XM_DIAG
#define US_XM_DIAG 0
#endif

static inline __attribute__((always_inline)) size_t
us_dec_m_fused(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
               const uint64_t *em, uint64_t pos0) {
    uint64_t j = 0, cur = pos0;
#if US_XM_DIAG == 6
    (void)em; (void)pos0;
    us_run(p, dst, n);
    *err = 0;
    return (size_t)n;
#endif
    if (!n) return 0;
    {
        uint64_t endp = pos0 + n;
        uint64_t b0 = pos0 >> 6, b1 = (endp - 1) >> 6;
        uint64_t lo = ~(uint64_t)0 << (pos0 & 63);
        unsigned last = (unsigned)((endp - 1) & 63);
        uint64_t hi = last == 63 ? ~(uint64_t)0 : ((uint64_t)1 << (last + 1)) - 1;
        uint64_t b = b0, base = b0 << 6;
        uint64_t m = em[b] & lo;
        if (b == b1) m &= hi;
        for (;;) {
            while (m) {
                unsigned bl = (unsigned)__builtin_ctzll(m);
                uint64_t q;
                m &= m - 1;
                q = base + bl;
                /* a lane the previous escape consumed is not an escape */
#ifndef US_XM_NOSKIP
                if (q < cur) continue;
#endif
#ifdef US_XP_TRACE
                us_xp_visited[us_xp_nvis++] = (uint32_t)q;
#endif
                {
                    uint64_t bi = q - pos0;
                    uint64_t ii = cur - pos0;
#if US_XM_DIAG != 2 && US_XM_DIAG != 3
                    us_run_long(p + ii, dst + j, bi - ii);
#endif
                    j += bi - ii;
#if US_XM_DIAG == 3
                    cur = q + 1;
#else
                    if (US_XM_DIAG != 1 && p[bi] < 0x20) {
                        *err = (size_t)bi;
                        return (size_t)-1;
                    }
                    {
                        uint64_t adv;
#if US_XM_DIAG == 1
                        adv = 2;
#else
                        if (!us_esc(p, n, bi, dst, &j, &adv, err))
                            return (size_t)-1;
#endif
                        cur = q + adv;
                    }
#endif
                }
            }
            if (b == b1) break;
            base += 64;
            b++;
            m = em[b];
            if (b == b1) m &= hi;
        }
        {
            uint64_t ii = cur - pos0;
#if US_XM_DIAG != 2 && US_XM_DIAG != 3
            us_run_long(p + ii, dst + j, n - ii);
#endif
            if (US_XM_DIAG == 2 || US_XM_DIAG == 3)
                return (size_t)n;
            return (size_t)(j + (n - ii));
        }
    }
}

/* Split form (US_XM_SPLIT): the mask walk becomes a position extractor and
   the expansion runs through the list consumer's loop unchanged, so the two
   phases do not share a register set.  A body with more than US_XM_CAP lanes
   falls back to the fused walk (which every body still uses when the build
   keeps US_XM_SPLIT=0). */
#ifndef US_XM_SPLIT
#define US_XM_SPLIT 0
#endif
#ifndef US_XM_CAP
#define US_XM_CAP 768
#endif
/* US_XM_BATCH=K: in the split consumer, decode K lanes ahead (independent)
   before the commit loop copies the runs and writes the decoded words.  That
   separates the escape expansion from the run copy, which the fused loop
   interleaves per escape. */
#ifndef US_XM_BATCH
#define US_XM_BATCH 0
#endif

#if US_XM_SPLIT
static inline __attribute__((always_inline)) size_t
us_dec_m_split(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
               const uint64_t *em, uint64_t pos0) {
    uint32_t pos[US_XM_CAP];
    uint64_t endp = pos0 + n;
    uint64_t b0 = pos0 >> 6, b1 = (endp - 1) >> 6;
    unsigned last = (unsigned)((endp - 1) & 63);
    uint64_t hi = last == 63 ? ~(uint64_t)0 : ((uint64_t)1 << (last + 1)) - 1;
    uint64_t lo = ~(uint64_t)0 << (pos0 & 63);
    unsigned np = 0;
    for (uint64_t b = b0; b <= b1; b++) {
        uint64_t m = em[b];
        uint64_t base = (b << 6) - pos0;
        if (b == b0) m &= lo;
        if (b == b1) m &= hi;
        while (m) {
            pos[np++] = (uint32_t)(base + (unsigned)__builtin_ctzll(m));
            m &= m - 1;
            if (np == US_XM_CAP)
                return us_dec_m_fused(p, n, dst, err, em, pos0);
        }
    }
#if US_XM_BATCH
    {
        uint64_t i = 0, j = 0;
        unsigned t = 0;
        while (t < np) {
            USX d[US_XM_BATCH];
            unsigned nq = np - t;
            if (nq > US_XM_BATCH) nq = US_XM_BATCH;
            for (unsigned q = 0; q < nq; q++)
                d[q] = us_xdec(p, n, pos[t + q]);
            for (unsigned q = 0; q < nq; q++) {
                uint64_t b = pos[t + q];
                if (b < i) continue;               /* consumed by the previous */
                us_run_long(p + i, dst + j, b - i);
                j += b - i;
                if (!d[q].ok) { *err = (size_t)b; return US_FAIL; }
                memcpy(dst + j, &d[q].word, 8);
                j += d[q].outlen;
                i = b + d[q].inlen;
            }
            t += nq;
        }
        us_run_long(p + i, dst + j, n - i);
        return (size_t)(j + (n - i));
    }
#else
    {
        uint64_t xj = 0;
        return us_dec_x(p, n, dst, err, pos, &xj, np, 0);
    }
#endif
}
#endif

#ifndef US_XM_INLINE
#define US_XM_INLINE 0
#endif
#if US_XM_INLINE
#define US_XM_FN static inline __attribute__((always_inline))
#else
#define US_XM_FN __attribute__((noinline)) static
#endif

US_XM_FN size_t
us_dec_m(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *err,
         const uint64_t *em, uint64_t pos0) {
#if US_XM_DIAG == 6
    (void)em; (void)pos0;
    us_run(p, dst, n);
    *err = 0;
    return (size_t)n;
#endif
#if US_XM_SPLIT
    return us_dec_m_split(p, n, dst, err, em, pos0);
#else
    return us_dec_m_fused(p, n, dst, err, em, pos0);
#endif
}

/* Fused body pass (US_FUSED): one traversal for both forms, so an escaped
   body is not classified by z_scan and then decoded from the backslash in a
   second entry.  Measured better than the split form when escapes are dense
   and worse when they are not, because every plain body then pays a call.
   Returns 1 with *outn = n when the body holds no escape and nothing was
   written (the caller emits a span), 2 with *outn = decoded length when it
   does, 0 with *err = body-relative offset on rejection. */
static int us_body_kernel(const uint8_t *p, uint64_t n, uint8_t *dst,
                          size_t *outn, size_t *err) {
    uint64_t i = 0, j = 0;
    int esc = 0;
    while (i < n) {
        uint64_t rem = n - i;
        uint64_t win, m;
#if US_W == 64
        if (rem >= 64) {
            __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + i));
            __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + i + 32));
            m = (uint64_t)us_special32(v0) | ((uint64_t)us_special32(v1) << 32);
            if (!m) {
                if (esc) {
                    _mm256_storeu_si256((__m256i *)(dst + j), v0);
                    _mm256_storeu_si256((__m256i *)(dst + j + 32), v1);
                    j += 64;
                }
                i += 64;
                continue;
            }
            win = 64;
        } else
#endif
        {
            __m256i v = _mm256_loadu_si256((const __m256i *)(p + i));
            win = (rem < 32) ? rem : 32;
            m = (uint64_t)us_special32(v);
            if (win < 32) m &= ((uint64_t)1 << win) - 1;
            if (!m) {
                if (esc) {
                    _mm256_storeu_si256((__m256i *)(dst + j), v);
                    j += win;
                }
                i += win;
                continue;
            }
        }
        {
            uint64_t cur = 0;
            while (m) {
                unsigned b = (unsigned)__builtin_ctzll(m);
                if (!esc) {
                    /* first escape: everything before it is already clean and
                       its decoded bytes are the input bytes */
                    uint64_t end = i + b, k = 0;
                    while (k + 32 <= end) {
                        _mm256_storeu_si256((__m256i *)(dst + k),
                                            _mm256_loadu_si256((const __m256i *)(p + k)));
                        k += 32;
                    }
                    if (k < end) us_run(p + k, dst + k, end - k);
                    j = end;
                    esc = 1;
                    cur = b;
                } else {
                    us_run(p + i + cur, dst + j, (uint64_t)b - cur);
                    j += (uint64_t)b - cur;
                }
                uint64_t at = i + b;
                if (p[at] < 0x20) { *err = (size_t)at; return 0; }
                uint64_t adv;
                if (!us_esc(p, n, at, dst, &j, &adv, err)) return 0;
                cur = (uint64_t)b + adv;
                if (cur >= win) break;
                m &= ~(((uint64_t)1 << cur) - 1);
            }
            {
                uint64_t nxt = (cur < win) ? win : cur;
                if (esc) {
                    uint64_t len = nxt - cur;
                    us_run(p + i + cur, dst + j, len);
                    j += len;
                }
                i += nxt;
            }
        }
    }
    *outn = esc ? (size_t)j : (size_t)n;
    return esc ? 2 : 1;
}

__attribute__((noinline)) static int
us_body(const uint8_t *p, uint64_t n, uint8_t *dst, size_t *outn, size_t *err) {
    return us_body_kernel(p, n, dst, outn, err);
}

#endif /* USDEC_H */
