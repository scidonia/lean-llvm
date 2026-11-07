/* xlist.h -- escape-position list shared by the fused stage-1 builder and the
   gates.  Scratch; not repository code.

   A position is recorded for every byte inside a string that is either a
   control byte or the first backslash of a run: the escapes the unescaper's
   window mask would visit, with the companion backslash of `\\` already
   removed, so the consumer needs no per-position skip test.

   XL_EMIT selects how the positions of one block are appended:

     0  spike 38: one straight-line eight-entry batch of tzcnt/blsr steps and
        stores run on every block, more batches when the mask holds more than
        eight lanes;
     1  the same batch, but a block whose escape mask is empty appends nothing
        and executes no batch;
     2  the batch is gone: the mask is expanded one non-empty mask byte at a
        time through the 256x8 POS8 table, one 32-byte store per byte.  A block
        with an empty mask appends nothing (the same per-block gate). */
#ifndef XLIST_H
#define XLIST_H

#include <immintrin.h>
#include <stdint.h>

#ifndef XL_EMIT
#define XL_EMIT 0
#endif

/* POS8: for each eight-bit mask, the offsets of its set bits, in order, padded
   to eight entries.  A store of a whole row therefore writes the byte's
   positions contiguously at the cursor, and its slots past the popcount are
   overwritten by the next store (or never read). */
static uint32_t xl_pos8[256][8] __attribute__((aligned(32)));
/* The same rows with the mask byte's own offset (8*byte) already added, so a
   block's eight stores need no per-group broadcast: one broadcast of the block
   base is added to every row.  64 KB, and only the groups a block actually
   uses are touched. */
static uint32_t xl_pos8b[8][256][8] __attribute__((aligned(32)));
static int xl_pos8_ready;

static void xl_pos8_init(void) {
    if (xl_pos8_ready) return;
    for (unsigned m = 0; m < 256; m++) {
        unsigned o = 0;
        for (unsigned t = 0; t < 8; t++)
            if ((m >> t) & 1) xl_pos8[m][o++] = t;
        while (o < 8) xl_pos8[m][o++] = 0;
    }
    for (unsigned b = 0; b < 8; b++)
        for (unsigned m = 0; m < 256; m++)
            for (unsigned t = 0; t < 8; t++)
                xl_pos8b[b][m][t] = xl_pos8[m][t] + 8 * b;
    xl_pos8_ready = 1;
}

/* prefix xor of the 64 block bits: bit i = parity of bits 0..i */
static inline uint64_t xl_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

/* The bytes of this block that start an escape: a control byte, or a
   backslash at an even offset inside its run (the first of `\\`, `\\\`, ...),
   restricted to bytes inside a string.

   `*pb` is 1 when the previous block's last byte is a backslash and `*ps` is 1
   when that backslash starts an escape, so a run that crosses a block boundary
   keeps its phase: the run start lies outside this block and the first byte
   here is seeded as its odd or its even member.

   Inside the block the even offsets propagate one step of two at a time,
   guarded by `cont` (a position whose predecessor is also a backslash), which
   is what keeps a step from jumping over a non-backslash byte into the next
   run.  Two straight-line steps cover runs up to five; a longer run finishes in
   a loop that is entered almost never. */
static inline uint64_t xl_lanes(uint64_t bs, uint64_t ctl, uint64_t im,
                                uint64_t *pb, uint64_t *ps) {
    uint64_t prevb = *pb, prevs = *ps;
    uint64_t starts = bs & ~((bs << 1) | prevb);
    uint64_t e = starts;
    if ((bs & 1) & prevb)
        e |= prevs ? (bs & 2) : 1;
    {
        uint64_t cont = bs & (bs << 1);
        e |= (e << 2) & cont;
        e |= (e << 2) & cont;
        /* A run longer than five backslashes finishes here.  Only enter when
           the step would add a bit that is not already in `e`: the bare
           `(e << 2) & cont` is non-zero on every run of three, all of whose
           lanes the two straight-line steps have already produced. */
        if (__builtin_expect((((e << 2) & cont) & ~e) != 0, 0)) {
            uint64_t old;
            do {
                old = e;
                e |= (e << 2) & cont;
            } while (e != old);
        }
    }
    *pb = bs >> 63;
    *ps = (e >> 63) & (bs >> 63);
    return (ctl | e) & im;
}

/* One fixed batch of eight positions (the mask may hold more; the caller's
   tail handles that).  Returns the number of real entries. */
static inline unsigned xl_batch(uint64_t esc, uint32_t base, uint32_t *o) {
    uint64_t c = esc | 0x8000000000000000ULL;   /* keeps ctz defined */
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    {
        unsigned n = (unsigned)__builtin_popcountll(esc);
        return n > 8 ? 8 : n;
    }
}

/* Append the escape positions of one 64-byte block.  With XL_EMIT=0 this is
   spike 38's shape: one straight-line batch of eight, then (only for a block
   that holds more than eight lanes) further batches of eight. */
static inline void xl_emit_batch(uint64_t esc, uint32_t base, uint32_t *out,
                                 uint64_t *k) {
    uint32_t *o = out + *k;
    unsigned n = xl_batch(esc, base, o);
    *k += n;
    if (__builtin_expect(__builtin_popcountll(esc) > 8, 0)) {
        uint64_t c = esc;
        for (unsigned t = 0; t < 8; t++) c &= c - 1;
        o += 8;
        while (c) {
            unsigned b = xl_batch(c, base, o);
            o += b;
            *k += b;
            for (unsigned t = 0; t < 8; t++) c &= c - 1;
        }
    }
}

/* POS8 expansion: one store per non-empty mask byte, at that byte's exact
   cursor.  `nb` holds one bit per non-empty byte, so the loop makes exactly
   that many passes and skips empty bytes for free.  The byte is non-empty
   exactly when (low seven bits + 0x7F) | byte has its top bit set, and the
   addition cannot carry out of a byte because the low bits are at most 0x7F. */
static inline void xl_emit_pos8(uint64_t esc, uint32_t base, uint32_t *out,
                                uint64_t *k) {
    uint32_t *o = out + *k;
    uint64_t kk = *k;
    uint64_t nzh = ((esc & 0x7F7F7F7F7F7F7F7FULL) + 0x7F7F7F7F7F7F7F7FULL) | esc;
    unsigned nb = (unsigned)_pext_u64(nzh, 0x8080808080808080ULL);
    do {
        unsigned b = (unsigned)__builtin_ctz(nb);
        unsigned m = (unsigned)((esc >> (b * 8)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[m]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (b << 3))));
        _mm256_storeu_si256((__m256i *)o, v);
        unsigned n = (unsigned)__builtin_popcount(m);
        o += n;
        kk += n;
        nb &= nb - 1;
    } while (nb);
    *k = kk;
}

/* The caller initialises the table once (xl_pos8_init); nothing here touches it
   unless the block has a lane, and a lane store is then a single load. */
/* Fixed-trip POS8: eight stores, one per mask byte, with the eight cursor
   offsets computed as independent prefix popcounts of the same mask.  There is
   no loop and no data-dependent branch, so a block's cost does not depend on
   how its lanes fall: an empty byte's store lands on the next byte's cursor and
   is overwritten before it can be read. */
static inline void xl_emit_pos8x(uint64_t esc, uint32_t base, uint32_t *out,
                                 uint64_t *k) {
    uint32_t *o = out + *k;
    uint64_t c0 = (uint64_t)__builtin_popcountll(esc & 0x00000000000000FFULL);
    uint64_t c1 = c0 + (uint64_t)__builtin_popcountll(esc & 0x000000000000FF00ULL);
    uint64_t c2 = c1 + (uint64_t)__builtin_popcountll(esc & 0x0000000000FF0000ULL);
    uint64_t c3 = c2 + (uint64_t)__builtin_popcountll(esc & 0x00000000FF000000ULL);
    uint64_t c4 = c3 + (uint64_t)__builtin_popcountll(esc & 0x000000FF00000000ULL);
    uint64_t c5 = c4 + (uint64_t)__builtin_popcountll(esc & 0x0000FF0000000000ULL);
    uint64_t c6 = c5 + (uint64_t)__builtin_popcountll(esc & 0x00FF000000000000ULL);
    uint64_t c7 = c6 + (uint64_t)__builtin_popcountll(esc & 0xFF00000000000000ULL);
#define XL_P8B(B, KOFF)                                                       \
    {                                                                         \
        unsigned m = (unsigned)((esc >> (8 * (B))) & 0xFFu);                  \
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[m]);           \
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + 8 * (B))));    \
        _mm256_storeu_si256((__m256i *)(o + (KOFF)), v);                      \
    }
    XL_P8B(0, 0)
    XL_P8B(1, c0)
    XL_P8B(2, c1)
    XL_P8B(3, c2)
    XL_P8B(4, c3)
    XL_P8B(5, c4)
    XL_P8B(6, c5)
    XL_P8B(7, c6)
#undef XL_P8B
    *k += c7;
}

/* Scalar: one position at a time, used as a cheap shape for sparse blocks and
   as the tail of the two-lane form. */
static inline void xl_emit_scalar(uint64_t esc, uint32_t base, uint32_t *out,
                                  uint64_t *k) {
    uint32_t *o = out + *k;
    while (esc) {
        *o++ = base + (uint32_t)__builtin_ctzll(esc);
        esc &= esc - 1;
    }
    *k = (uint64_t)(o - out);
}

/* Two fixed lanes, then the scalar tail only for a block that holds more.  The
   second store of a one-lane block lands one past the cursor and is
   overwritten by the next block's first store (never read).  The branch is
   biased the same way for the whole document: files with about a lane per
   block stay on the fast side, backslash-dense files on the slow side. */
static inline void xl_emit_two(uint64_t esc, uint32_t base, uint32_t *out,
                               uint64_t *k) {
    uint32_t *o = out + *k;
    uint64_t c = esc;
    o[0] = base + (uint32_t)__builtin_ctzll(c | 0x8000000000000000ULL);
    c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c | 0x8000000000000000ULL);
    c &= c - 1;
    unsigned pc = (unsigned)__builtin_popcountll(esc);
    if (__builtin_expect(pc > 2, 0)) {
        uint32_t *p = o + 2;
        uint64_t kk = *k + 2;
        while (c) { *p++ = base + (uint32_t)__builtin_ctzll(c); kk++; c &= c - 1; }
        *k = kk;
        return;
    }
    *k += pc;
}

/* Fixed-trip POS8 with the byte offset baked into the table: the block base is
   broadcast once and every group's row is one load, one add and one store. */
static inline void xl_emit_pos8b(uint64_t esc, uint32_t base, uint32_t *out,
                                 uint64_t *k) {
    uint32_t *o = out + *k;
    __m256i bv = _mm256_set1_epi32((int)base);
    uint64_t c0 = (uint64_t)__builtin_popcountll(esc & 0x00000000000000FFULL);
    uint64_t c1 = c0 + (uint64_t)__builtin_popcountll(esc & 0x000000000000FF00ULL);
    uint64_t c2 = c1 + (uint64_t)__builtin_popcountll(esc & 0x0000000000FF0000ULL);
    uint64_t c3 = c2 + (uint64_t)__builtin_popcountll(esc & 0x00000000FF000000ULL);
    uint64_t c4 = c3 + (uint64_t)__builtin_popcountll(esc & 0x000000FF00000000ULL);
    uint64_t c5 = c4 + (uint64_t)__builtin_popcountll(esc & 0x0000FF0000000000ULL);
    uint64_t c6 = c5 + (uint64_t)__builtin_popcountll(esc & 0x00FF000000000000ULL);
    uint64_t c7 = c6 + (uint64_t)__builtin_popcountll(esc & 0xFF00000000000000ULL);
#define XL_P8T(B, KOFF)                                                       \
    {                                                                         \
        unsigned m = (unsigned)((esc >> (8 * (B))) & 0xFFu);                  \
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8b[B][m]);       \
        v = _mm256_add_epi32(v, bv);                                          \
        _mm256_storeu_si256((__m256i *)(o + (KOFF)), v);                      \
    }
    XL_P8T(0, 0)
    XL_P8T(1, c0)
    XL_P8T(2, c1)
    XL_P8T(3, c2)
    XL_P8T(4, c3)
    XL_P8T(5, c4)
    XL_P8T(6, c5)
    XL_P8T(7, c6)
#undef XL_P8T
    *k += c7;
}

/* Expand a chunk of per-block escape masks into positions.  The masks are
   written by the classify loop (one store per block, no emitter in that loop),
   and this loop has no vector work, so the emitter's registers and the
   classify loop's registers never compete.  The shape is chosen once per
   chunk from the chunk's own density: a chunk that carries about a lane per
   block or more uses the fixed-trip POS8 stores, a sparser chunk the two-lane
   form, so neither choice switches back and forth inside the chunk. */
static void xl_expand_masks(const uint64_t *m, uint64_t blk0, uint64_t nblk,
                            uint32_t *out, uint64_t *nk) {
    uint64_t tot = 0;
    for (uint64_t i = 0; i < nblk; i++)
        tot += (uint64_t)__builtin_popcountll(m[i]);
    int dense = tot >= nblk;
    uint64_t k = *nk;
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t esc = m[i];
        if (!esc) continue;
        uint32_t base = (uint32_t)((blk0 + i) << 6);
        if (dense) xl_emit_pos8x(esc, base, out, &k);
        else xl_emit_two(esc, base, out, &k);
    }
    *nk = k;
}

static inline void xl_emit(uint64_t esc, uint32_t base, uint32_t *out,
                           uint64_t *k) {
    if (XL_EMIT == 0) { xl_emit_batch(esc, base, out, k); return; }
    if (!esc) return;                       /* per-block gate */
#if XL_EMIT == 2
    xl_emit_pos8(esc, base, out, k);
#elif XL_EMIT == 3
    xl_emit_pos8x(esc, base, out, k);
#elif XL_EMIT == 4
    xl_emit_scalar(esc, base, out, k);
#elif XL_EMIT == 5
    xl_emit_two(esc, base, out, k);
#elif XL_EMIT == 6
    xl_emit_pos8b(esc, base, out, k);
#else
    xl_emit_batch(esc, base, out, k);
#endif
}

#ifdef XL_STATS
static uint64_t xl_st_blocks, xl_st_lanes, xl_st_batches, xl_st_tail;
#endif

/* Gate-side builder: the same lane extraction and the same emitter as stage 1,
   over a standalone buffer whose bytes are all treated as inside a string
   (which is what a string body is). */
static inline void xl_build_body(const uint8_t *p, uint64_t n, uint32_t *out,
                                 uint64_t *nk) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    const __m256i vbs = _mm256_set1_epi8('\\');
    uint64_t pb = 0, ps = 0;
    xl_pos8_init();
    for (uint64_t bi = 0; bi * 64 < (n ? n : 1); bi++) {
        uint64_t o = bi << 6;
        uint64_t lim = n - o;
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + o));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + o + 32));
        uint64_t ctl = (uint64_t)(unsigned)_mm256_movemask_epi8(
                           _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
                       ((uint64_t)(unsigned)_mm256_movemask_epi8(
                           _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
        uint64_t bs = (uint64_t)(unsigned)_mm256_movemask_epi8(
                          _mm256_cmpeq_epi8(v0, vbs)) |
                      ((uint64_t)(unsigned)_mm256_movemask_epi8(
                          _mm256_cmpeq_epi8(v1, vbs)) << 32);
        uint64_t esc = xl_lanes(bs, ctl, ~0ULL, &pb, &ps);
        if (lim < 64) esc &= ((uint64_t)1 << lim) - 1;
        xl_emit(esc, (uint32_t)o, out, nk);
    }
}

/* Gate-side mask builder: the same lane extraction as xl_build_body, but the
   result of each block is one mask word instead of a compacted position list.
   The buffer is the body's own block grid, so a body at document offset zero
   can be consumed directly by the mask consumer. */
static inline void xl_build_masks_body(const uint8_t *p, uint64_t n,
                                       uint64_t *out) {
    const __m256i v19 = _mm256_set1_epi8(0x1F);
    const __m256i vbs = _mm256_set1_epi8('\\');
    uint64_t pb = 0, ps = 0;
    for (uint64_t bi = 0; bi * 64 < (n ? n : 1); bi++) {
        uint64_t o = bi << 6;
        uint64_t lim = n - o;
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(p + o));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + o + 32));
        uint64_t ctl = (uint64_t)(unsigned)_mm256_movemask_epi8(
                           _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
                       ((uint64_t)(unsigned)_mm256_movemask_epi8(
                           _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
        uint64_t bs = (uint64_t)(unsigned)_mm256_movemask_epi8(
                          _mm256_cmpeq_epi8(v0, vbs)) |
                      ((uint64_t)(unsigned)_mm256_movemask_epi8(
                          _mm256_cmpeq_epi8(v1, vbs)) << 32);
        uint64_t esc = xl_lanes(bs, ctl, ~0ULL, &pb, &ps);
        if (lim < 64) esc &= ((uint64_t)1 << lim) - 1;
        out[bi] = esc;
    }
}

#endif /* XLIST_H */
