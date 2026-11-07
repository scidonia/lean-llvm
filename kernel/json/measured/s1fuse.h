/* s1fuse.h -- one-pass stage 1: classify a 64-byte block and emit its entry
   positions inside the same loop.  Scratch experiment; not repository code.

   The entry stream is what the simdjson-shaped stage 2 consumes:

     S   = ~(im | qm | sm | ws)          bytes of a scalar run
     stm = S & ~((S << 1) | carry)       scalars start where a run starts
     ent = qm | (sm & ~im) | stm         quotes, structurals outside strings,
                                         and every scalar start

   S1F_GRAIN=1 drops stm and leaves the structural characters alone, which is
   the "index of structural characters only" granularity.

   Position expansion, S1F_EXPAND:
     0  tzcnt/blsr over the 64-bit block mask (one store per entry)
     1  POS8 table, one 8-lane store per non-empty mask byte
     2  POS8 table, one 8-lane store per mask byte (the batch32 shape)
   S1F_EMIT=0 prices the classify half alone.

   S1F_UTF8=1 runs the UTF-8 probe inside the same block loop (the probe is
   utf8f.c's kernel, duplicated here so the two can be compared in one build).

   The classifier is the block body of `ci2` in this tree's stage-1 kernel
   (same comparisons, same escape resolution, same clmul prefix xor).
*/
#ifndef S1FUSE_H
#define S1FUSE_H

#include <immintrin.h>
#include <stdint.h>
/* S1F_KL_DOC is read by dens.h's probe, which supplies its input, so the
   value has to be visible before the include; the rest of its wiring and its
   commentary are below. */
#ifndef S1F_KL_DOC
#define S1F_KL_DOC 0
#endif
#include "dens.h"
#if defined(SP_MODES)
#include "modes.h"
#endif
/* The entry-emitter kernel of the current document (dens.h's DENS_K_*); the
   probe sets it once per build, the modes binary may force it. */
static int s1f_kern = DENS_K_B8;

#if defined(SP45_MODES)
#include "modes45.h"
#endif

/* S1F_ENT_PROBE=1 measures the document's entry density on a bounded block
   sample (s1f_ent_probe) and picks s1f_kern from it. */
#ifndef S1F_ENT_PROBE
#define S1F_ENT_PROBE 0
#endif

/* S1F_XS=1 additionally appends the block's escape positions (control bytes
   and escape-start backslashes inside strings) to the shared list while the
   classify loop runs; see xlist.h for the shape.

   XS=5 and XS=6 keep the same list but change the emitter: 5 puts the
   per-block gate in front of spike 38's eight-entry batch, 6 replaces the batch
   with one POS8 store per non-empty mask byte, 7 with eight fixed POS8 stores,
   9 with a scalar walk, 10 with two fixed lanes and a scalar tail, and 11 with
   eight fixed POS8 stores whose table already holds the byte offset.  XS=8
   computes the control-byte mask and nothing else (a price probe for that mask
   alone). */
#ifndef S1F_XS
#define S1F_XS 0
#endif

#if S1F_XS == 5
#define XL_EMIT 1
#elif S1F_XS == 6
#define XL_EMIT 2
#elif S1F_XS == 7
#define XL_EMIT 3
#elif S1F_XS == 9
#define XL_EMIT 4
#elif S1F_XS == 10
#define XL_EMIT 5
#elif S1F_XS == 11
#define XL_EMIT 6
#elif S1F_XS == 12
#define XL_EMIT 3
#elif S1F_XS == 14
#define XL_EMIT 1
#elif S1F_XS == 15
/* both list shapes in one build, chosen per process (SP_MODES only) */
#define XL_EMIT 1
#endif

/* S1F_XS=13 records one escape mask per block and builds no position list:
   the consumer reads the masks (see usdec.h's us_dec_m). */
#if S1F_XS == 13
#define S1F_MASKS 1
#else
#define S1F_MASKS 0
#endif
#include "xlist.h"

#ifndef S1F_EXPAND
#define S1F_EXPAND 1
#endif
#ifndef S1F_GRAIN
#define S1F_GRAIN 0
#endif
#ifndef S1F_EMIT
#define S1F_EMIT 1
#endif
#ifndef S1F_UTF8
#define S1F_UTF8 0
#endif
/* S1F_UTF8=3: the fold -- the block's lead/continuation masks come from a
   pshufb class of each byte's high nibble, well-formedness is checked with
   64-bit shifts and compares, and the boundary state lives in a dword (the
   owed continuation bits plus the previous block's last byte). */
#if S1F_UTF8 == 3 || S1F_UTF8 == 4 || S1F_UTF8 == 5 || S1F_UTF8 == 6
#include "u8fold.h"
#endif
/* S1F_UTF8=7: the Keiser-Lemire table DFA.  Three pshufb per 32-byte vector
   carry the whole check (continuation structure + the four restricted leads
   + C0/C1/F5..FF), the boundary state is the bytes the three p-1/p-2/p-3 loads
   already see, and the error vectors accumulate: one vptest per document. */
#if S1F_UTF8 == 7 || S1F_UTF8 == 8
#include "u8kl.h"
#endif
/* S1F_KL_GATE=1 skips the DFA on a block that is all-ASCII when the block
   before it is too: no lead can reach into it and any pending continuation
   would already have errored in the previous block.  Without the gate the
   DFA runs on every block, which is what the 87%-non-ASCII file wants and
   what the ASCII-only files do not. */
#ifndef S1F_KL_GATE
#define S1F_KL_GATE 1
#endif
/* S1F_KL_DOC=1: the DFA's ASCII gate is decided once per document instead of
   being compiled in.  dens_probe samples adjacent block pairs spread over the
   document and dens_pick_u8 turns the share of blocks the gate would skip
   into the arm: a document whose blocks are mostly ASCII runs the gated DFA
   (the gate skips ~all of them), one whose blocks mostly carry a high byte
   runs the ungated DFA (no test at all).  Wrong readings cost time, never a
   verdict: each arm validates every position by itself.

   The two arms sit in one loop behind a branch on a document-constant int, so
   neither arm's code buys the other's placement.  S1F_U8_MODES (the
   measurement binary) adds SP48=1/2 to force gated/ungated for the same
   document; the shipped build compiles it out. */
#if S1F_KL_DOC && !S1F_KL_GATE
#error "S1F_KL_DOC decides between the gated and ungated arms; it needs S1F_KL_GATE"
#endif
#if S1F_KL_DOC && S1F_UTF8 != 7 && S1F_UTF8 != 8
#error "S1F_KL_DOC selects between the S1F_UTF8=7 arms"
#endif
static int s1f_u8_ungated;      /* 1: no per-block ASCII test on this document */
#if defined(S1F_U8_MODES)
static int s1f_u8_mode;         /* SP48: 0 auto, 1 gated, 2 ungated */
#endif
static inline void s1f_u8_decide(void) {
#if S1F_KL_DOC
    int un = dens_u8_ungated;
#if defined(S1F_U8_MODES)
    if (s1f_u8_mode == 1) un = 0;
    else if (s1f_u8_mode == 2) un = 1;
#endif
    s1f_u8_ungated = un;
#endif
}
#ifndef S1F_BATCH
#define S1F_BATCH 4
#endif
#ifndef S1F_CHUNK
#define S1F_CHUNK 1024          /* blocks of masks held in L1 between passes */
#endif

/* S1F_XS_DYN=1: a PLAIN document builds no escape-position list at all (no
   lane extraction, no emission) and the consumer is handed NULL, so it
   classifies each body itself.  The classification is one hoisted check per
   document, decided in dens.h. */
#ifndef S1F_XS_DYN
#define S1F_XS_DYN 0
#endif

/* S1F_DENS: read the document's escape-density class (dens.h) once per build.
   Implied by the consumer's gate (S2_DEC_GATE), by S1F_XS_DYN, and by
   S1F_KL_DOC (whose probe reading comes from the same sample). */
#ifndef S1F_DENS
#if defined(S2_DEC_GATE) && S2_DEC_GATE
#define S1F_DENS 1
#elif S1F_XS_DYN
#define S1F_DENS 1
#elif S1F_KL_DOC
#define S1F_DENS 1
#else
#define S1F_DENS 0
#endif
#endif

/* S1F_XS_NOIM=1: skip lane extraction on a block whose in-string mask is zero.
   No lane can be in such a block (the lane mask is intersected with it), and
   a backslash run crossing it cannot reach a string: a block that opens a
   string has a non-zero in-string mask at the opening quote, and a block
   inside a string has a non-zero mask throughout. */
#ifndef S1F_XS_NOIM
#define S1F_XS_NOIM 0
#endif

/* S1F_XS=15 (both list shapes in one build) with S1F_FOLD_HEAVY=1: a HEAVY
   document folds the list into the expansion pass, everything else emits it
   from the classify loop.  Measured: the fold wins on the two backslash-dense
   files and on wl_dense, and costs about 1 ns/block on canonical. */
#ifndef S1F_FOLD_HEAVY
#define S1F_FOLD_HEAVY 0
#endif

static int s1f_xs_on = 1;   /* S1F_XS_DYN: build the list on this document */

/* xl_lanes with the per-block in-string gate: a block with no in-string byte
   carries no lane and cannot hand a string-side run phase to the next block,
   so only the plain cross-block phase is updated. */
static inline uint64_t s1f_lanes_im(uint64_t bm, uint64_t ctl, uint64_t im,
                                    uint64_t *pb, uint64_t *ps) {
#if defined(SP_MODES)
    if (!im && sp_noim) {
        *pb = bm >> 63;
        *ps = 0;
        return 0;
    }
#elif S1F_XS_NOIM
    if (!im) {
        *pb = bm >> 63;
        *ps = 0;
        return 0;
    }
#endif
    return xl_lanes(bm, ctl, im, pb, ps);
}

/* --------------------------------------------------------------- tables ---- */
/* The POS8 table lives in xlist.h: the entry emitter and the escape-position
   emitter index the same 256 rows. */
#if S1F_UTF8 == 4
/* Both UTF-8 arms in one binary, chosen per process: SP46=0 runs the separate
   scan, SP46=1 the fold.  One binary means one code placement, so the paired
   delta is the algorithm's. */
static int s1f_u8_fold;
#endif
#if S1F_UTF8 == 8
/* SP47=0 the separate scan, 1 the table DFA, 2 no UTF-8 at all. */
static int s1f_u8_kl;
#endif
static void s1f_init(void) {
    xl_pos8_init();
    dens_core_init();               /* the cached core-class read, once */
#if S1F_UTF8 == 4
    {
        const char *e = getenv("SP46");
        s1f_u8_fold = e ? atoi(e) : 0;
    }
#endif
#if S1F_UTF8 == 8
    {
        const char *e = getenv("SP47");
        s1f_u8_kl = e ? atoi(e) : 0;
    }
#endif
#if defined(S1F_U8_MODES)
    {
        const char *e = getenv("SP48");
        s1f_u8_mode = e ? atoi(e) : 0;
    }
#endif
}

typedef struct { uint64_t esc_open, esc_ppar, im_carry, prevS,
                 bs_prevb, bs_prevs; } S1F;

/* Escape-position stream produced by S1F_XS, in document order.  `s1f_xcap`
   entries are allocated, so a fixed eight-entry batch at the end of the
   document cannot run past the buffer; only `s1f_xn` entries are real. */
static uint32_t *s1f_xp;
static uint64_t s1f_xn, s1f_xcap;
/* S1F_XS=13: one escape mask per block, resident for the whole document. */
#if S1F_MASKS
static uint64_t *s1f_em;
static uint64_t s1f_emn, s1f_emcap;
#endif
#if defined(SP44_MODES)
/* the carried escape kind: one bit per document byte, one word per block.
   NULL when the arm does not ask for it, so the classify loop's only extra
   work is one predictable store test. */
#include "kind44.h"
static uint64_t *s1f_uk;
static uint64_t s1f_ukn, s1f_ukcap;
static void s1f_uk_reserve(uint64_t nb) {
    if (nb <= s1f_ukcap) return;
    free(s1f_uk);
    s1f_ukcap = nb + 64;
    s1f_uk = (uint64_t *)malloc(s1f_ukcap * 8);
    if (!s1f_uk) { fprintf(stderr, "oom\n"); exit(2); }
}
#endif
/* S1F_XS=12 records one escape mask per block in this chunk buffer and expands
   the chunk in a separate loop; 1024 masks are 8 KB, which stays in L1. */
#ifndef S1F_ESC_CHUNK
#define S1F_ESC_CHUNK 1024
#endif
#if S1F_XS == 12
static uint64_t s1f_escm[S1F_ESC_CHUNK];
#endif
#if S1F_XS == 14 || S1F_XS == 15
/* the entry mask and the escape mask of one block, interleaved per block so
   the expansion loop reads both from one cache line */
static uint64_t s1f_e2[2 * S1F_CHUNK];
#endif
#if S1F_XS == 2 || S1F_XS == 8
static volatile uint64_t s1f_xsink;
#endif
#ifdef S1F_XS_STATS
uint64_t s1f_xhist[9];   /* lanes per block: 0,1,2,3,4,5,6,7,8+ */
uint64_t s1f_xbhist[9];  /* non-empty mask bytes per block: 0..8+ */
uint64_t s1f_xbatches, s1f_xlanes_total, s1f_xblocks, s1f_nim0;
#endif

#if S1F_MASKS
static void s1f_em_reserve(uint64_t nb) {
    if (nb <= s1f_emcap) return;
    free(s1f_em);
    s1f_emcap = nb + 64;
    s1f_em = (uint64_t *)malloc(s1f_emcap * 8);
    if (!s1f_em) { fprintf(stderr, "oom\n"); exit(2); }
}
#endif

static void s1f_x_reserve(uint64_t n) {
    if (n + 16 <= s1f_xcap) return;
    free(s1f_xp);
    s1f_xcap = n + 4096 + 16;
    s1f_xp = (uint32_t *)malloc(s1f_xcap * 4);
    if (!s1f_xp) { fprintf(stderr, "oom\n"); exit(2); }
}

#ifdef S1F_STATS
uint64_t s1f_hist[7];
#endif

/* ------------------------------------------------------------ classifier -- */
static inline uint64_t s1f_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

static inline uint64_t s1f_escaped(uint64_t bs, uint64_t *open, uint64_t *ppar) {
    const uint64_t even_slots = 0x5555555555555555ULL;
    uint64_t bs1 = bs << 1;
    uint64_t starts = bs & ~(bs1 | *open);
    uint64_t bs0 = bs & 1;
    starts |= bs0 & *open;
    uint64_t lasts = bs & ~(bs >> 1);
    uint64_t after = lasts << 1;
    uint64_t alt = even_slots ^ (*open & *ppar);
    uint64_t dd = _pext_u64(alt, starts) ^ _pext_u64(even_slots, lasts);
    uint64_t esc = _pdep_u64(~dd, after) | (*open & ~bs0 & *ppar);
    uint64_t top = bs >> 63;
    uint64_t lzp = ((bs == ~0ULL) ? 64u : (unsigned)__builtin_clzll(~bs)) & 1u;
    uint64_t pp = (((bs == ~0ULL) && *open) ? *ppar : 0) ^ lzp;
    *ppar = top & pp;
    *open = top;
    return esc;
}

static inline __m256i s1f_structural(__m256i v) {
    __m256i r = _mm256_cmpeq_epi8(v, _mm256_set1_epi8(','));
    r = _mm256_or_si256(r, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(':')));
    r = _mm256_or_si256(r, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('{')));
    r = _mm256_or_si256(r, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('}')));
    r = _mm256_or_si256(r, _mm256_cmpeq_epi8(v, _mm256_set1_epi8('[')));
    r = _mm256_or_si256(r, _mm256_cmpeq_epi8(v, _mm256_set1_epi8(']')));
    return r;
}

/* Structural and whitespace masks from one shuffle pair: each low nibble and
   each high nibble carries a bit set per class it can take part in, and the
   AND is non-zero exactly for the six structural bytes (bits 0-5) and the four
   whitespace bytes (bits 6-7).  Verified exhaustively against the byte sets. */
#ifndef S1F_CTAB
#define S1F_CTAB 1
#endif

static const uint8_t s1f_lo_tab[32] __attribute__((aligned(32))) = {
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
};
static const uint8_t s1f_hi_tab[32] __attribute__((aligned(32))) = {
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static inline void s1f_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)s1f_hi_tab), hi));
    *sm = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *ws = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8((char)0xC0)), z));
}

static inline uint64_t s1f_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {
    uint32_t s0, s1, w0, w1;
    s1f_sw32(v0, &s0, &w0);
    s1f_sw32(v1, &s1, &w1);
    *ws_o = (uint64_t)w0 | ((uint64_t)w1 << 32);
    return (uint64_t)s0 | ((uint64_t)s1 << 32);
}

/* Block masks in ci2's sense: unescaped quotes, raw structurals, in-string.
   With S1F_XS the raw backslash mask and the control-byte mask come out too,
   for the escape-position list. */
static inline void s1f_masks(__m256i v0, __m256i v1, S1F *st,
                             uint64_t *qm_o, uint64_t *sm_o, uint64_t *im_o,
                             uint64_t *ws_o, uint64_t *bm_o, uint64_t *ctl_o) {
    __m256i q = _mm256_set1_epi8('"');
    __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
#if S1F_XS
    {
        const __m256i v19 = _mm256_set1_epi8(0x1F);
        *ctl_o = (uint64_t)(uint32_t)_mm256_movemask_epi8(
                     _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
                 ((uint64_t)(uint32_t)_mm256_movemask_epi8(
                     _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
    }
    *bm_o = bm;
#else
    (void)bm_o; (void)ctl_o;
#endif
#if S1F_CTAB
    uint64_t sm = 0, ws = 0;
    sm = s1f_sm_ws(v0, v1, &ws);
    *ws_o = ws;
#else
    uint64_t sm = (uint64_t)(uint32_t)_mm256_movemask_epi8(s1f_structural(v0)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(s1f_structural(v1)) << 32);
    *ws_o = 0;
#endif
    qm &= ~s1f_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint64_t im = s1f_prefix_xor(qm) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *qm_o = qm;
    *sm_o = sm;
    *im_o = im;
}

/* whitespace (' ', '\t', '\n', '\r') by a two-nibble lookup */
static inline uint32_t s1f_ws32(__m256i x) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(x, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(x, 4), m4);
    static const uint8_t W8[32] = {
        4,0,0,0,0,0,0,0,0,1,1,0,0,1,0,0,
        4,0,0,0,0,0,0,0,0,1,1,0,0,1,0,0
    };
    static const uint8_t B8[32] = {
        1,2,4,8,16,32,64,128,0,0,0,0,0,0,0,0,
        1,2,4,8,16,32,64,128,0,0,0,0,0,0,0,0
    };
    __m256i t = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_loadu_si256((const __m256i *)W8), lo),
        _mm256_shuffle_epi8(_mm256_loadu_si256((const __m256i *)B8), hi));
    return (uint32_t)~_mm256_movemask_epi8(_mm256_cmpeq_epi8(t, z));
}

/* ----------------------------------------------------------- entry probe -- */
/* S1F_ENT_WIN blocks at the head of the document, classified with the same
   masks the timed pass builds (quotes, structurals outside strings, one entry
   per scalar run start).  The state is exact because the run starts at the
   document's first block; sampling windows further in was tried first and is
   wrong for long-string documents -- a window that starts inside a string has
   no quote to resynchronise it, so the whole window reads as scalar bytes and
   wl_longstr's 1.3 entries/block read as 24.

   The prefix reading is what the kernel choice gets:
     file        first 64 blocks  whole document
     canonical        6.84            6.28
     citm             7.87            6.03
     dense           26.38           26.43
     twitter          7.92            7.43
     canada           9.88            9.51
     longstr          1.31            1.33
     escdense         7.36            7.03
   A 1024-block chunk varies by at most 0.9 entries/block within a document
   (eprobe.c), so the head reads the document. */
#ifndef S1F_ENT_WIN
#define S1F_ENT_WIN 64
#endif
#if S1F_ENT_PROBE
static uint64_t s1f_ep_blocks, s1f_ep_hits;

static void s1f_ent_probe(const uint8_t *b, uint64_t n) {
    uint64_t nb = (n + 63) / 64;
    uint64_t nbw = nb < (uint64_t)S1F_ENT_WIN ? nb : (uint64_t)S1F_ENT_WIN;
    uint64_t hits = 0;
    S1F st = {0, 0, 0, 0};
    for (uint64_t bi = 0; bi < nbw; bi++) {
        const uint8_t *p = b + (bi << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
        uint64_t qm, sm, im, wsm = 0, bm = 0, ctl = 0;
        s1f_masks(v0, v1, &st, &qm, &sm, &im, &wsm, &bm, &ctl);
        uint64_t ent = qm | (sm & ~im);
#if S1F_GRAIN == 0
        {
#if S1F_CTAB
            uint64_t ws = wsm;
#else
            uint64_t ws = (uint64_t)s1f_ws32(v0) |
                          ((uint64_t)s1f_ws32(v1) << 32);
#endif
            uint64_t S = ~(im | qm | sm | ws);
            uint64_t stm = S & ~((S << 1) | st.prevS);
            st.prevS = S >> 63;
            ent |= stm;
        }
#endif
        uint64_t lim = n - (bi << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
        hits += (uint64_t)__builtin_popcountll(ent);
    }
    s1f_ep_blocks = nbw;
    s1f_ep_hits = hits;
}
#endif /* S1F_ENT_PROBE */

/* --------------------------------------------------------------- emitter -- */
#ifndef S1F_NOINL
#define S1F_NOINL 0
#endif
#if S1F_NOINL
__attribute__((noinline)) static void s1f_emit(uint64_t ent, uint32_t base,
                                                uint32_t *out, uint64_t *nk) {
#else
static inline void s1f_emit(uint64_t ent, uint32_t base, uint32_t *out,
                            uint64_t *nk) {
#endif
#if S1F_EMIT == 0
    (void)ent; (void)base; (void)out; (void)nk;
#elif S1F_EXPAND == 0
    uint64_t k = *nk;
    while (ent) {
        out[k++] = base + (uint32_t)__builtin_ctzll(ent);
        ent &= ent - 1;
    }
    *nk = k;
#elif S1F_EXPAND == 1
    uint64_t k = *nk;
    while (ent) {
        unsigned bit = (unsigned)__builtin_ctzll(ent);
        unsigned byte = bit >> 3;
        unsigned m = (unsigned)((ent >> (byte * 8)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[m]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + byte * 8)));
        _mm256_storeu_si256((__m256i *)(out + k), v);
        k += (uint64_t)__builtin_popcount(m);
        ent &= ~((uint64_t)0xFFu << (byte * 8));
    }
    *nk = k;
#elif S1F_EXPAND == 3
    /* batches of eight: fixed-offset stores, one blsr chain, count-accurate
       advance.  A batch overwrites the previous batch's overflow slots. */
    uint64_t k = *nk;
    uint32_t *o = out + k;
    uint64_t n = (uint64_t)__builtin_popcountll(ent);
    while (ent) {
        uint64_t c0 = ent;
        o[0] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[1] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[2] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[3] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[4] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[5] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[6] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        o[7] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        unsigned m = (n > 8) ? 8u : (unsigned)n;
        o += m;
        k += m;
        n -= m;
        ent = c0;
    }
    *nk = k;
#elif S1F_EXPAND == 4
    /* diagnostic: the eight stores only, no index computation */
    uint64_t k = *nk;
    uint32_t b0 = base;
    out[0] = b0; out[1] = b0; out[2] = b0; out[3] = b0;
    out[4] = b0; out[5] = b0; out[6] = b0; out[7] = b0;
    *nk = k + (uint64_t)__builtin_popcountll(ent);
#elif S1F_EXPAND == 5
    /* diagnostic: the eight tzcnt/blsr steps, one store */
    uint64_t c0 = ent;
    unsigned v = 0;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    v ^= (unsigned)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[0] = base + v;
    *nk = *nk + (uint64_t)__builtin_popcountll(ent);
#elif S1F_EXPAND == 6
    /* diagnostic: one unconditional batch, no loop */
    uint64_t k = *nk;
    uint64_t c0 = ent;
    out[0] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[1] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[2] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[3] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[4] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[5] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[6] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    out[7] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
    {
        unsigned n = (unsigned)__builtin_popcountll(ent);
        *nk = k + (n > 8 ? 8u : n);
    }
#elif S1F_EXPAND == 7
    /* diagnostic: batch of eight with the loop replaced by a taken-once test */
    uint64_t k = *nk;
    uint64_t n = (uint64_t)__builtin_popcountll(ent);
    uint64_t c = ent;
    for (;;) {
        uint64_t c0 = c;
        out[0] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[1] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[2] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[3] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[4] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[5] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[6] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        out[7] = base + (uint32_t)__builtin_ctzll(c0); c0 &= c0 - 1;
        if (n <= 8) { k += n; break; }
        out += 8; k += 8; n -= 8; c = c0;
    }
    *nk = k;
#elif S1F_EXPAND == 8
    /* S1F_BATCH unconditional batches of eight, then a rare scalar tail */
    uint64_t k = *nk;
    uint64_t n = (uint64_t)__builtin_popcountll(ent);
    uint64_t c = ent;
    uint32_t *oo = out + k;
    for (int q = 0; q < S1F_BATCH; q++) {
        oo[8 * q + 0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    }
    if (n <= (uint64_t)(8 * S1F_BATCH)) {
        *nk = k + n;
    } else {
        uint64_t m = (uint64_t)(8 * S1F_BATCH);
        uint32_t *o = out + k + m;
        uint64_t kk = k + m;
        while (c) {
            o[0] = base + (uint32_t)__builtin_ctzll(c);
            o++;
            kk++;
            c &= c - 1;
        }
        *nk = kk;
    }
#elif S1F_EXPAND == 10
    /* fixed batch of four, then a scalar tail */
    uint64_t k = *nk;
    uint64_t n = (uint64_t)__builtin_popcountll(ent);
    uint64_t c = ent;
    uint32_t *o = out + k;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 4) {
        *nk = k + n;
    } else {
        o += 4; k += 4;
        while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
        *nk = k;
    }
#else
    uint64_t k = *nk;
    for (int c = 0; c < 8; c++) {
        unsigned m = (unsigned)((ent >> (8 * c)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[m]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * c))));
        _mm256_storeu_si256((__m256i *)(out + k), v);
        k += (uint64_t)__builtin_popcount(m);
    }
    *nk = k;
#endif
}

/* ----------------------------------------------------------- UTF-8 probe -- */
#if S1F_UTF8
static inline __m256i s1f_uge(__m256i x, uint8_t lo) {
    return _mm256_cmpeq_epi8(_mm256_max_epu8(x, _mm256_set1_epi8((char)lo)), x);
}

static inline __m256i s1f_uchunk(const uint8_t *p) {
    __m256i x  = _mm256_loadu_si256((const __m256i *)p);
    __m256i p1 = _mm256_loadu_si256((const __m256i *)(p - 1));
    __m256i p2 = _mm256_loadu_si256((const __m256i *)(p - 2));
    __m256i p3 = _mm256_loadu_si256((const __m256i *)(p - 3));
    __m256i need = _mm256_or_si256(
        _mm256_or_si256(s1f_uge(p1, 0xC0), s1f_uge(p2, 0xE0)), s1f_uge(p3, 0xF0));
    __m256i cont = _mm256_cmpeq_epi8(_mm256_and_si256(x, _mm256_set1_epi8((char)0xC0)),
                                     _mm256_set1_epi8((char)0x80));
    __m256i e = _mm256_xor_si256(cont, need);
    __m256i bad = _mm256_or_si256(
        _mm256_cmpeq_epi8(_mm256_and_si256(x, _mm256_set1_epi8((char)0xFE)),
                          _mm256_set1_epi8((char)0xC0)),
        s1f_uge(x, 0xF5));
    __m256i mE0 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xE0));
    __m256i mED = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xED));
    __m256i mF0 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xF0));
    __m256i mF4 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xF4));
    __m256i lo = _mm256_or_si256(_mm256_and_si256(mE0, _mm256_set1_epi8((char)0xA0)),
                                 _mm256_and_si256(mF0, _mm256_set1_epi8((char)0x90)));
    __m256i hi = _mm256_or_si256(_mm256_and_si256(mED, _mm256_set1_epi8((char)0x9F)),
                                 _mm256_and_si256(mF4, _mm256_set1_epi8((char)0x8F)));
    __m256i rng = _mm256_or_si256(
        _mm256_subs_epu8(lo, x),
        _mm256_and_si256(_mm256_or_si256(mED, mF4), _mm256_subs_epu8(x, hi)));
    return _mm256_or_si256(_mm256_or_si256(e, bad), rng);
}
#endif

/* S1F_UTF8=2: the same kernel on the vector the classifier already loaded,
   plus the block's pending-continuation state.  A block with no high bit and
   no continuation owed by the previous block cannot contain any UTF-8
   structure, so it is skipped; a block with no high bit that does owe one is
   an error at once.  `pend` is derived from the previous block's last three
   bytes (the only ones that can reach into this block). */
#if S1F_UTF8 == 2
static inline __m256i s1f_uchunk_x(const uint8_t *p, __m256i x) {
    __m256i p1 = _mm256_loadu_si256((const __m256i *)(p - 1));
    __m256i p2 = _mm256_loadu_si256((const __m256i *)(p - 2));
    __m256i p3 = _mm256_loadu_si256((const __m256i *)(p - 3));
    __m256i need = _mm256_or_si256(
        _mm256_or_si256(s1f_uge(p1, 0xC0), s1f_uge(p2, 0xE0)), s1f_uge(p3, 0xF0));
    __m256i cont = _mm256_cmpeq_epi8(_mm256_and_si256(x, _mm256_set1_epi8((char)0xC0)),
                                     _mm256_set1_epi8((char)0x80));
    __m256i e = _mm256_xor_si256(cont, need);
    __m256i bad = _mm256_or_si256(
        _mm256_cmpeq_epi8(_mm256_and_si256(x, _mm256_set1_epi8((char)0xFE)),
                          _mm256_set1_epi8((char)0xC0)),
        s1f_uge(x, 0xF5));
    __m256i mE0 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xE0));
    __m256i mED = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xED));
    __m256i mF0 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xF0));
    __m256i mF4 = _mm256_cmpeq_epi8(p1, _mm256_set1_epi8((char)0xF4));
    __m256i lo = _mm256_or_si256(_mm256_and_si256(mE0, _mm256_set1_epi8((char)0xA0)),
                                 _mm256_and_si256(mF0, _mm256_set1_epi8((char)0x90)));
    __m256i hi = _mm256_or_si256(_mm256_and_si256(mED, _mm256_set1_epi8((char)0x9F)),
                                 _mm256_and_si256(mF4, _mm256_set1_epi8((char)0x8F)));
    __m256i rng = _mm256_or_si256(
        _mm256_subs_epu8(lo, x),
        _mm256_and_si256(_mm256_or_si256(mED, mF4), _mm256_subs_epu8(x, hi)));
    return _mm256_or_si256(_mm256_or_si256(e, bad), rng);
}

/* continuation bytes the next block owes because of this block's last three
   bytes; 0 when this block ends cleanly or is the document's last block */
static inline unsigned s1f_pend(const uint8_t *b, uint64_t n, uint64_t bi) {
    uint64_t start = bi << 6;
    uint64_t end = start + 64;
    if (end > n) end = n;
    if (end == n) return 0;
    unsigned pend = 0;
    uint64_t lo = end > 3 ? end - 3 : 0;
    for (uint64_t q = lo; q < end; q++) {
        unsigned c = b[q];
        unsigned len = (c >= 0xF0) ? 4 : (c >= 0xE0) ? 3 : (c >= 0xC0) ? 2 : 1;
        for (unsigned r = 1; r < len; r++) {
            uint64_t pos = q + r;
            if (pos >= end) pend |= 1u << (unsigned)(pos - end);
        }
    }
    return pend;
}
#endif

/* --------------------------------------------------------------- builder -- */
static uint64_t s1f_build(const uint8_t *b, uint64_t n, uint32_t *out,
                          uint64_t *uerr) {
    s1f_init();
#if defined(SP_MODES)
    dens_probe(b, n);
    s1f_xs_on = sp_list;
    if (sp_gate) s1f_xs_on &= (dens_doc_class != DENS_PLAIN);
#elif S1F_DENS
    dens_probe(b, n);               /* one document-level decision per build */
#endif
#if S1F_KL_DOC
    s1f_u8_decide();                /* gated or ungated DFA for this document */
#endif
#if S1F_ENT_PROBE
    s1f_ent_probe(b, n);
    dens_pick_kernel(s1f_ep_hits, s1f_ep_blocks);
    s1f_kern = dens_ent_kernel;
#if defined(SP45_MODES)
    if (sp45_kern >= 0) s1f_kern = sp45_kern;
#endif
#endif
#if S1F_XS_DYN && !defined(SP_MODES)
    s1f_xs_on = (dens_doc_class != DENS_PLAIN);
#endif
#if S1F_XS && !S1F_MASKS
    s1f_x_reserve(n);
    uint32_t *xpo = s1f_xp;
    uint64_t xk = 0;
#endif
    S1F st = {0, 0, 0, 0};
    uint64_t nb = (n + 63) / 64;
#if S1F_MASKS
    s1f_em_reserve(nb ? nb : 1);
    s1f_emn = nb ? nb : 1;
#endif
    uint64_t nk = 0, err = 0;
#if S1F_UTF8 == 3 || S1F_UTF8 == 4
    U8CARRY u8c;
    u8_carry_init(&u8c);
#endif
#if S1F_UTF8 == 5
    U8VCARRY u8v;
    u8v_carry_init(&u8v);
#endif
#if S1F_UTF8 == 6
    uint32_t u8s_need = 0;
    __m256i u8s_prev = _mm256_setzero_si256();
    (void)u8s_prev;
#endif
#if S1F_UTF8 && S1F_UTF8 != 3 && !(S1F_UTF8 == 7 && !S1F_KL_GATE)
    int prev_ascii = 1;
#endif
#if S1F_UTF8 && S1F_UTF8 != 3 && !(S1F_UTF8 == 7 && !S1F_KL_GATE)
    const __m256i high = _mm256_set1_epi8((char)0x80);
#endif
#if S1F_UTF8 == 2
    unsigned pend = 0;
#endif
#if S1F_UTF8 == 7 || S1F_UTF8 == 8
    __m256i u8k = _mm256_setzero_si256();
#endif
    for (uint64_t bi = 0; bi < nb; bi++) {
        const uint8_t *p = b + (bi << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
        uint64_t qm, sm, im, wsm = 0, bm = 0, ctl = 0;
        s1f_masks(v0, v1, &st, &qm, &sm, &im, &wsm, &bm, &ctl);
        uint64_t ent = qm | (sm & ~im);
#if S1F_GRAIN == 0
        {
#if S1F_CTAB
            uint64_t ws = wsm;
#else
            uint64_t ws = (uint64_t)s1f_ws32(v0) |
                          ((uint64_t)s1f_ws32(v1) << 32);
#endif
            uint64_t S = ~(im | qm | sm | ws);
            uint64_t stm = S & ~((S << 1) | st.prevS);
            st.prevS = S >> 63;
            ent |= stm;
        }
#endif
#ifdef S1F_STATS
        { unsigned pc = (unsigned)__builtin_popcountll(ent);
          s1f_hist[pc == 0 ? 0 : pc <= 8 ? 1 : pc <= 16 ? 2 : pc <= 24 ? 3
                           : pc <= 32 ? 4 : pc <= 48 ? 5 : 6]++; }
#endif
        uint64_t lim = n - (bi << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
#if S1F_XS
#if defined(SP_MODES) || S1F_XS_DYN
        if (s1f_xs_on)
#else
        if (1)
#endif
        {
#if S1F_XS == 2
            s1f_xsink ^= xl_lanes(bm, ctl, im, &st.bs_prevb, &st.bs_prevs);
#elif S1F_XS == 8
            s1f_xsink ^= ctl;
#else
            uint64_t esc = (S1F_XS == 4)
                               ? 0
                               : (S1F_XS == 3)
                                     ? (ctl | bm)
                                     : s1f_lanes_im(bm, ctl, im,
                                                    &st.bs_prevb,
                                                    &st.bs_prevs);
            if (lim < 64) esc &= (1ULL << lim) - 1ULL;
#ifdef S1F_XS_STATS
            { unsigned pc = (unsigned)__builtin_popcountll(esc);
              uint64_t nzh = ((esc & 0x7F7F7F7F7F7F7F7FULL) +
                              0x7F7F7F7F7F7F7F7FULL) | esc;
              unsigned nb = (unsigned)__builtin_popcountll(
                  _pext_u64(nzh, 0x8080808080808080ULL));
              s1f_xhist[pc > 8 ? 8 : pc]++;
              s1f_xbhist[nb > 8 ? 8 : nb]++;
              s1f_xlanes_total += pc; s1f_xblocks++;
              s1f_xbatches += pc ? (pc + 7) / 8 : 0; }
#endif
#if S1F_XS == 12
            /* record the mask; the expansion runs in a separate tight loop */
            s1f_escm[bi & (S1F_ESC_CHUNK - 1)] = esc;
            if ((bi & (S1F_ESC_CHUNK - 1)) == S1F_ESC_CHUNK - 1)
                xl_expand_masks(s1f_escm, bi + 1 - S1F_ESC_CHUNK,
                                S1F_ESC_CHUNK, xpo, &xk);
#elif S1F_MASKS
            s1f_em[bi] = esc;      /* one store per block, no emission */
#else
            xl_emit(esc, (uint32_t)(bi << 6), xpo, &xk);
#endif
#endif
        }
#endif
#if S1F_EMIT == 0
        nk ^= ent;                       /* keep the classify live */
#endif
        s1f_emit(ent, (uint32_t)(bi << 6), out, &nk);
#if S1F_UTF8 == 4
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (s1f_u8_fold == 1) {
                if (!ascii || u8c.need) {
                    err |= (uint64_t)u8_fold_vec(v0, v1, &u8c);
                } else {
                    u8c.prev = v1;
                }
            } else if (s1f_u8_fold == 2) {
                /* no UTF-8 arm at all: the price floor */
            } else if (!(ascii && prev_ascii)) {
                __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                err |= (uint64_t)!_mm256_testz_si256(u, u);
            }
            if (!s1f_u8_fold) prev_ascii = ascii;
        }
#elif S1F_UTF8 == 5
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii)) {
                err |= (uint64_t)u8_foldv_vec(v0, v1, &u8v);
            } else {
                u8v.prev = v1;
            }
            prev_ascii = ascii;
        }
#elif S1F_UTF8 == 6
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!ascii || u8s_need) {
                err |= (uint64_t)u8_fold6_vec(v0, v1, &u8s_need);
            } else {
                u8s_prev = v1;
            }
        }
#elif S1F_UTF8 == 3
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!ascii || u8c.need) {
                err |= (uint64_t)u8_fold_vec(v0, v1, &u8c);
            } else {
                /* nothing owed and no high bit: the block cannot carry a
                   lead, a continuation or a range violation */
                u8c.prev = v1;
            }
        }
#elif S1F_UTF8 == 7
#if S1F_KL_DOC
        if (s1f_u8_ungated) {
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
        } else {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii))
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            prev_ascii = ascii;
        }
#elif S1F_KL_GATE
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii))
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            prev_ascii = ascii;
        }
#else
        u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
#endif
#elif S1F_UTF8 == 8
        if (s1f_u8_kl == 1) {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii))
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            prev_ascii = ascii;
        } else if (s1f_u8_kl == 3) {
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
        } else if (s1f_u8_kl == 0) {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii)) {
                __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                err |= (uint64_t)!_mm256_testz_si256(u, u);
            }
            prev_ascii = ascii;
        }
#elif S1F_UTF8 == 2
        {
            uint64_t hm = (uint64_t)(uint32_t)_mm256_movemask_epi8(v0) |
                          ((uint64_t)(uint32_t)_mm256_movemask_epi8(v1) << 32);
            if (!hm) {
                err |= pend;
                pend = 0;
            } else {
                __m256i u = _mm256_or_si256(s1f_uchunk_x(p, v0),
                                                s1f_uchunk_x(p + 32, v1));
                err |= (uint64_t)!_mm256_testz_si256(u, u);
                pend = s1f_pend(b, n, bi);
            }
        }
#elif S1F_UTF8
        {
            __m256i any = _mm256_or_si256(v0, v1);
            int ascii = _mm256_testz_si256(any, high);
            if (!(ascii && prev_ascii)) {
                __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                err |= (uint64_t)!_mm256_testz_si256(u, u);
            }
            prev_ascii = ascii;
        }
#endif
    }
#if S1F_XS == 12
    {
        uint64_t done = nb & ~(uint64_t)(S1F_ESC_CHUNK - 1);
        if (nb > done) xl_expand_masks(s1f_escm, done, nb - done, xpo, &xk);
    }
#endif
#if S1F_UTF8 == 7
    /* the block loop does not evaluate the position after its last one; a
       C0/C1/F5..FF there is reported one position later, so take it here */
    err |= (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);
#elif S1F_UTF8 == 8
    if (s1f_u8_kl == 1 || s1f_u8_kl == 3) {
        err |= (uint64_t)!_mm256_testz_si256(u8k, u8k);
        if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);
    }
#endif
#if S1F_UTF8
    *uerr = err;
#else
    (void)uerr;
#endif
#if S1F_XS && !S1F_MASKS
    s1f_xn = xk;
#endif
#ifdef S1F_UTF8_LIVE
    return nk ^ (err << 32);
#else
    return nk;
#endif
}

#endif /* S1FUSE_H */

/* -------------------------------------------------- two-phase stage 1 ------
   The classify loop writes one entry mask per block; a second tight loop over
   that mask buffer expands them.  The mask buffer is consumed a chunk at a
   time, so it stays in L1.  This keeps the vector loop free of the emitter's
   register pressure; the expansion loop has no vector work.

   S1F_EXP2: 0 = tzcnt/blsr loop, 1 = eight-entry batches, 2 = POS8 per byte. */
#ifndef S1F_TWOPHASE
#define S1F_TWOPHASE 0
#endif
#ifndef S1F_EXP2
#define S1F_EXP2 1
#endif
#ifndef S1F_CHUNK
#define S1F_CHUNK 1024
#endif

static uint64_t *s1f_ent;
static uint64_t s1f_entcap;

static void s1f_ent_reserve(uint64_t nb) {
    if (nb <= s1f_entcap) return;
    free(s1f_ent);
    s1f_entcap = nb + 4096;
    s1f_ent = (uint64_t *)malloc(s1f_entcap * 8);
    if (!s1f_ent) { fprintf(stderr, "oom\n"); exit(2); }
}

#ifndef S1F_DENSE_THR
#define S1F_DENSE_THR 12      /* entries per block above which POS8 is used */
#endif
#ifndef S1F_BATCH2
#define S1F_BATCH2 1          /* fixed batches of eight in the sparse kernel */
#endif

/* POS8 per mask byte with the eight store offsets as prefix popcounts: one
   popcount each, all independent, so no store address waits on the previous
   byte's count.  Entries past the mask are written and then overwritten. */
#define S1F_POS8(M, BASE, O)                                                   \
    do {                                                                       \
        uint64_t _m = (M);                                                     \
        uint32_t _b = (BASE);                                                  \
        uint32_t *_o = (O);                                                    \
        uint64_t c0 = (uint64_t)__builtin_popcountll(_m & 0xFFULL);            \
        uint64_t c1 = c0 + (uint64_t)__builtin_popcountll(_m & 0xFF00ULL);     \
        uint64_t c2 = c1 + (uint64_t)__builtin_popcountll(_m & 0xFF0000ULL);   \
        uint64_t c3 = c2 + (uint64_t)__builtin_popcountll(_m & 0xFF000000ULL); \
        uint64_t c4 = c3 +                                                     \
            (uint64_t)__builtin_popcountll(_m & 0xFF00000000ULL);              \
        uint64_t c5 = c4 +                                                     \
            (uint64_t)__builtin_popcountll(_m & 0xFF0000000000ULL);            \
        uint64_t c6 = c5 +                                                     \
            (uint64_t)__builtin_popcountll(_m & 0xFF000000000000ULL);          \
        uint64_t c7 = c6 +                                                     \
            (uint64_t)__builtin_popcountll(_m & 0xFF00000000000000ULL);        \
        S1F_P8_ONE(0, 0)                                                       \
        S1F_P8_ONE(1, c0)                                                      \
        S1F_P8_ONE(2, c1)                                                      \
        S1F_P8_ONE(3, c2)                                                      \
        S1F_P8_ONE(4, c3)                                                      \
        S1F_P8_ONE(5, c4)                                                      \
        S1F_P8_ONE(6, c5)                                                      \
        S1F_P8_ONE(7, c6)                                                      \
        (void)c7;                                                              \
    } while (0)
#define S1F_P8_ONE(B, KOFF)                                                    \
        {                                                                      \
            unsigned x = (unsigned)((_m >> (8 * (B))) & 0xFFu);                \
            __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);       \
            v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(_b + 8 * (B))));   \
            _mm256_storeu_si256((__m256i *)(_o + (KOFF)), v);                  \
        }

static inline void s1f_exp_pos8(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t c0 = (uint64_t)__builtin_popcountll(m & 0xFFULL);
    uint64_t c1 = c0 + (uint64_t)__builtin_popcountll(m & 0xFF00ULL);
    uint64_t c2 = c1 + (uint64_t)__builtin_popcountll(m & 0xFF0000ULL);
    uint64_t c3 = c2 + (uint64_t)__builtin_popcountll(m & 0xFF000000ULL);
    uint64_t c4 = c3 + (uint64_t)__builtin_popcountll(m & 0xFF00000000ULL);
    uint64_t c5 = c4 + (uint64_t)__builtin_popcountll(m & 0xFF0000000000ULL);
    uint64_t c6 = c5 + (uint64_t)__builtin_popcountll(m & 0xFF000000000000ULL);
#define S1F_P8(B, KOFF)                                                        \
    {                                                                         \
        unsigned x = (unsigned)((m >> (8 * (B))) & 0xFFu);                    \
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);          \
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + 8 * (B))));    \
        _mm256_storeu_si256((__m256i *)(o + (KOFF)), v);                      \
    }
    S1F_P8(0, 0)
    S1F_P8(1, c0)
    S1F_P8(2, c1)
    S1F_P8(3, c2)
    S1F_P8(4, c3)
    S1F_P8(5, c4)
    S1F_P8(6, c5)
    S1F_P8(7, c6)
#undef S1F_P8
}

/* Eight-entry batches with fixed offsets, then a scalar tail. */
static inline uint64_t s1f_exp_batch(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    uint64_t c = m;
    uint32_t *oo = o;
    for (int q = 0; q < S1F_BATCH2; q++) {
        oo[8 * q + 0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        oo[8 * q + 7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    }
    if (n <= (uint64_t)(8 * S1F_BATCH2)) return n;
    {
        uint32_t *t = o + 8 * S1F_BATCH2;
        uint64_t extra = 0;
        while (c) { *t++ = base + (uint32_t)__builtin_ctzll(c); extra++; c &= c - 1; }
        return (uint64_t)(8 * S1F_BATCH2) + extra;
    }
}

/* Four-entry batches with fixed offsets, then a scalar tail. */
static inline uint64_t s1f_exp_batch4(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 4) return n;
    {
        uint32_t *t = o + 4;
        uint64_t extra = 0;
        while (c) { *t++ = base + (uint32_t)__builtin_ctzll(c); extra++; c &= c - 1; }
        return 4 + extra;
    }
}

#if S1F_EXP2 == 11
/* ---------------------------------------------------- entry-emitter kernels --
   One of these is chosen per document from the probe (dens_ent_kernel; the
   modes binary can force one).  All four write the same position stream -- the
   gate compares the streams byte for byte -- and differ only in how a block's
   entry mask becomes positions:

     POS8  one 32-byte store per mask byte through the byte table: eight stores
           per block whatever its mask holds, and no serial advance chain.
     B2    two fixed tzcnt/blsr slots, then a scalar tail.
     B4    four fixed slots, then a scalar tail.
     B8    eight fixed slots, then a scalar tail; the shape the shipped
           two-phase build runs.

   Each is a separate noinline function, so the per-document choice costs one
   call per chunk (S1F_CHUNK blocks) and the three copies of B8 below sit at
   three addresses: their spread is the placement floor for any
   kernel-shaped change. */
static inline uint64_t s1f_ke_pos8(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    for (int b = 0; b < 8; b++) {
        unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
        _mm256_storeu_si256((__m256i *)o, v);
        o += (uint64_t)__builtin_popcount(x);
    }
    return (uint64_t)__builtin_popcountll(m);
}

static inline uint64_t s1f_ke_b2(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    if (!n) return 0;
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 2) return n;
    o += 2;
    uint64_t k = 2;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

#if defined(SP45_MODES)
/* The two-entry and four-entry shapes, and the duplicate placements, exist
   only in the measurement binary: the frozen-kernel rows show neither batch
   winning a cell, so the consolidated build does not carry them. */
static inline uint64_t s1f_ke_b4(uint64_t m, uint32_t base, uint32_t *o) {
    return s1f_exp_batch4(m, base, o);
}
#endif

static inline uint64_t s1f_ke_b8(uint64_t m, uint32_t base, uint32_t *o) {
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    if (!n) return 0;
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 8) return n;
    o += 8;
    uint64_t k = 8;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

#define S1F_DEFINE_KERNEL(NAME, BLOCK)                                        \
static __attribute__((noinline)) uint64_t                                     \
NAME(uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out, uint64_t k) {\
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        uint64_t m = ent[i];                                                  \
        if (!m) continue;                                                     \
        k += BLOCK(m, (uint32_t)((blk0 + i) << 6), out + k);                   \
    }                                                                         \
    return k;                                                                 \
}
S1F_DEFINE_KERNEL(s1f_k_pos8, s1f_ke_pos8)
S1F_DEFINE_KERNEL(s1f_k_b8, s1f_ke_b8)
#if defined(SP45_MODES)
S1F_DEFINE_KERNEL(s1f_k_b2, s1f_ke_b2)
S1F_DEFINE_KERNEL(s1f_k_b4, s1f_ke_b4)
/* two more identical copies of each winning kernel, for the floor */
S1F_DEFINE_KERNEL(s1f_k_b8_a, s1f_ke_b8)
S1F_DEFINE_KERNEL(s1f_k_b8_b, s1f_ke_b8)
S1F_DEFINE_KERNEL(s1f_k_pos8_a, s1f_ke_pos8)
S1F_DEFINE_KERNEL(s1f_k_pos8_b, s1f_ke_pos8)
#endif
#undef S1F_DEFINE_KERNEL

/* kernel ids: DENS_K_* above, plus the duplicate placements */
#define S1F_K_B8DUP_A   4
#define S1F_K_B8DUP_B   5
#define S1F_K_POS8DUP_A 6
#define S1F_K_POS8DUP_B 7

static void s1f_expand_k(int kern, uint64_t *ent, uint64_t blk0, uint64_t nblk,
                         uint32_t *out, uint64_t *nk) {
    uint64_t k = *nk;
    switch (kern) {
    case DENS_K_POS8:  k = s1f_k_pos8(ent, blk0, nblk, out, k); break;
#if defined(SP45_MODES)
    case DENS_K_B2:    k = s1f_k_b2(ent, blk0, nblk, out, k); break;
    case DENS_K_B4:    k = s1f_k_b4(ent, blk0, nblk, out, k); break;
    case S1F_K_B8DUP_A:   k = s1f_k_b8_a(ent, blk0, nblk, out, k); break;
    case S1F_K_B8DUP_B:   k = s1f_k_b8_b(ent, blk0, nblk, out, k); break;
    case S1F_K_POS8DUP_A: k = s1f_k_pos8_a(ent, blk0, nblk, out, k); break;
    case S1F_K_POS8DUP_B: k = s1f_k_pos8_b(ent, blk0, nblk, out, k); break;
#endif
    default:              k = s1f_k_b8(ent, blk0, nblk, out, k); break;
    }
    *nk = k;
}
#endif /* S1F_EXP2 == 11 */

static void s1f_expand(uint64_t *ent, uint64_t blk0, uint64_t nblk,
                       uint32_t *out, uint64_t *nk) {
#if S1F_EXP2 == 11
    s1f_expand_k(s1f_kern, ent, blk0, nblk, out, nk);
    return;
#endif
    uint64_t k = *nk;
#if S1F_EXP2 == 7
    /* the shipped density switch, with the dense side replaced by POS8 with
       prefix-popcount offsets (both sides inline, unlike S1F_EXP2=6 whose
       helpers stayed out of line). */
    {
        uint64_t tot = 0;
        for (uint64_t i = 0; i < nblk; i++)
            tot += (uint64_t)__builtin_popcountll(ent[i]);
        int dense = tot > (uint64_t)S1F_DENSE_THR * nblk;
        for (uint64_t i = 0; i < nblk; i++) {
            uint64_t m = ent[i];
            uint32_t base = (uint32_t)((blk0 + i) << 6);
            if (dense) {
                S1F_POS8(m, base, out + k);
                k += (uint64_t)__builtin_popcountll(m);
            } else {
                if (!m) continue;
                uint64_t c = m;
                uint64_t n = (uint64_t)__builtin_popcountll(m);
                uint32_t *o = out + k;
                o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                if (n <= 8) { k += n; continue; }
                o += 8;
                k += 8;
                while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
            }
        }
        *nk = k;
        return;
    }
#endif
#if S1F_EXP2 == 6
    {
        uint64_t tot = 0;
        for (uint64_t i = 0; i < nblk; i++)
            tot += (uint64_t)__builtin_popcountll(ent[i]);
        int dense = tot > (uint64_t)S1F_DENSE_THR * nblk;
        for (uint64_t i = 0; i < nblk; i++) {
            uint64_t m = ent[i];
            uint32_t base = (uint32_t)((blk0 + i) << 6);
            if (dense) {
                s1f_exp_pos8(m, base, out + k);
                k += (uint64_t)__builtin_popcountll(m);
            } else {
                k += s1f_exp_batch(m, base, out + k);
            }
        }
        *nk = k;
        return;
    }
#endif
#if S1F_EXP2 == 5
    /* POS8 with the eight store offsets computed as prefix popcounts: the
       shipped dense path advances `k` by one popcount per mask byte, an
       eight-link dependent chain per block.  Here the eight cumulative counts
       are independent (one popcount each, all from the same mask), so the
       store addresses are ready at once. */
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t m = ent[i];
        uint32_t base = (uint32_t)((blk0 + i) << 6);
        uint64_t c0 = (uint64_t)__builtin_popcountll(m & 0xFFULL);
        uint64_t c1 = c0 + (uint64_t)__builtin_popcountll(m & 0xFF00ULL);
        uint64_t c2 = c1 + (uint64_t)__builtin_popcountll(m & 0xFF0000ULL);
        uint64_t c3 = c2 + (uint64_t)__builtin_popcountll(m & 0xFF000000ULL);
        uint64_t c4 = c3 + (uint64_t)__builtin_popcountll(m & 0xFF00000000ULL);
        uint64_t c5 = c4 + (uint64_t)__builtin_popcountll(m & 0xFF0000000000ULL);
        uint64_t c6 = c5 + (uint64_t)__builtin_popcountll(m & 0xFF000000000000ULL);
        uint64_t c7 = c6 + (uint64_t)__builtin_popcountll(m & 0xFF00000000000000ULL);
        uint32_t *o = out + k;
#define S1F_P8(B, KOFF)                                                        \
        {                                                                     \
            unsigned x = (unsigned)((m >> (8 * (B))) & 0xFFu);                 \
            __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);       \
            v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + 8 * (B)))); \
            _mm256_storeu_si256((__m256i *)(o + (KOFF)), v);                   \
        }
        S1F_P8(0, 0)
        S1F_P8(1, c0)
        S1F_P8(2, c1)
        S1F_P8(3, c2)
        S1F_P8(4, c3)
        S1F_P8(5, c4)
        S1F_P8(6, c5)
        S1F_P8(7, c6)
#undef S1F_P8
        k += c7;
    }
    *nk = k;
    return;
#endif
#if S1F_EXP2 == 9
    for (uint64_t i = 0; i < nblk; i++) k += (uint64_t)__builtin_popcountll(ent[i]);
    *nk = k;
    return;
#endif
#if S1F_EXP2 == 3 || S1F_EXP2 == 4
    /* density switch per chunk: the fixed batches win while the entry count
       stays small, the byte-table form wins once every byte carries entries
       (it has no serial chain at all). */
    uint64_t tot = 0;
    for (uint64_t i = 0; i < nblk; i++)
        tot += (uint64_t)__builtin_popcountll(ent[i]);
    int dense = tot > 12 * nblk;
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t m = ent[i];
        uint32_t base = (uint32_t)((blk0 + i) << 6);
        if (!dense) {
#if S1F_EXP2 == 4
            uint64_t c = m, n = (uint64_t)__builtin_popcountll(m);
            uint32_t *o = out + k;
            for (int q = 0; q < 2; q++) {
                o[8 * q + 0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
                o[8 * q + 7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            }
            if (n <= 16) { k += n; continue; }
            o += 16;
            k += 16;
            while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
#else
            if (!m) continue;
            uint64_t c = m;
            uint64_t n = (uint64_t)__builtin_popcountll(m);
            uint32_t *o = out + k;
            o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
            if (n <= 8) { k += n; continue; }
            o += 8;
            k += 8;
            while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
#endif
        } else {
            for (int b = 0; b < 8; b++) {
                unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
                __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);
                v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
                _mm256_storeu_si256((__m256i *)(out + k), v);
                k += (uint64_t)__builtin_popcount(x);
            }
        }
    }
    *nk = k;
    return;
#endif
#if S1F_EXP2 == 10
    for (uint64_t i = 0; i < nblk; i++)
        k += s1f_exp_batch4(ent[i], (uint32_t)((blk0 + i) << 6), out + k);
    *nk = k;
    return;
#endif
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t m = ent[i];
        uint32_t base = (uint32_t)((blk0 + i) << 6);
#if S1F_EXP2 == 0
        while (m) { out[k++] = base + (uint32_t)__builtin_ctzll(m); m &= m - 1; }
#elif S1F_EXP2 == 1
        if (!m) continue;
        uint64_t c = m;
        uint64_t n = (uint64_t)__builtin_popcountll(m);
        uint32_t *o = out + k;
        o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
        if (n <= 8) { k += n; continue; }
        o += 8;
        k += 8;
        while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
#else
        for (int b = 0; b < 8; b++) {
            unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
            __m256i v = _mm256_load_si256((const __m256i *)xl_pos8[x]);
            v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
            _mm256_storeu_si256((__m256i *)(out + k), v);
            k += (uint64_t)__builtin_popcount(x);
        }
#endif
    }
    *nk = k;
}

#if S1F_XS == 14 || S1F_XS == 15
/* One block's entries: eight fixed slots, then the tail for a block with more
   (same shape as S1F_EXP2=1).  Returns the number of entries written. */
static inline uint64_t s1f_exp8(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    uint64_t c = m;
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[4] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[5] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[6] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[7] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 8) return n;
    o += 8;
    uint64_t k = 8;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

/* S1F_XS=14: the classify loop records both masks per block; this loop expands
   the entry stream and the escape-position list together, so the block walk is
   walked once and both masks are loaded from the same line.  `with_esc` is the
   document decision (S1F_XS_DYN): it is honoured outside the loop, so a
   document without a list runs a loop with no escape work at all. */
static void s1f_expand_x2(const uint64_t *e2, uint64_t blk0, uint64_t nblk,
                          uint32_t *out, uint64_t *nk, uint32_t *xo,
                          uint64_t *xk, int with_esc) {
    uint64_t k = *nk, kx = *xk;
    if (with_esc) {
        for (uint64_t i = 0; i < nblk; i++) {
            uint64_t m = e2[2 * i], e = e2[2 * i + 1];
            uint32_t base = (uint32_t)((blk0 + i) << 6);
            k += s1f_exp8(m, base, out + k);
            if (e) xl_emit_batch(e, base, xo, &kx);
        }
    } else {
        for (uint64_t i = 0; i < nblk; i++) {
            uint64_t m = e2[2 * i];
            uint32_t base = (uint32_t)((blk0 + i) << 6);
            k += s1f_exp8(m, base, out + k);
        }
    }
    *nk = k;
    *xk = kx;
}
#endif

static uint64_t s1f_build2(const uint8_t *b, uint64_t n, uint32_t *out,
                           uint64_t *uerr) {
    s1f_init();
#if defined(SP_MODES)
    dens_probe(b, n);
    s1f_xs_on = sp_list;
    if (sp_gate) s1f_xs_on &= (dens_doc_class != DENS_PLAIN);
#elif S1F_DENS
    dens_probe(b, n);               /* one document-level decision per build */
#endif
#if S1F_KL_DOC
    s1f_u8_decide();                /* gated or ungated DFA for this document */
#endif
#if S1F_ENT_PROBE
    s1f_ent_probe(b, n);
    dens_pick_kernel(s1f_ep_hits, s1f_ep_blocks);
    s1f_kern = dens_ent_kernel;
#if defined(SP45_MODES)
    if (sp45_kern >= 0) s1f_kern = sp45_kern;
#endif
#endif
#if S1F_XS_DYN && !defined(SP_MODES)
    s1f_xs_on = (dens_doc_class != DENS_PLAIN);
#endif
#if S1F_XS == 15
    int s1f_fold_doc;
#if defined(SP_MODES)
    s1f_fold_doc = sp_fold;
#elif S1F_FOLD_HEAVY
    s1f_fold_doc = s1f_xs_on && (dens_doc_class == DENS_HEAVY);
#else
    s1f_fold_doc = 0;
#endif
#endif
    s1f_ent_reserve((n + 63) / 64);
#if S1F_XS && !S1F_MASKS
    s1f_x_reserve(n);
    uint32_t *xpo = s1f_xp;
    uint64_t xk = 0;
#endif
#if defined(SP44_MODES)
    if (sp44_kind) {
        s1f_uk_reserve(((n + 63) / 64) ? ((n + 63) / 64) : 1);
        s1f_ukn = ((n + 63) / 64) ? ((n + 63) / 64) : 1;
    } else {
        free(s1f_uk);
        s1f_uk = NULL;
        s1f_ukcap = 0;
        s1f_ukn = 0;
    }
#endif
#if S1F_MASKS
    s1f_em_reserve(((n + 63) / 64) ? ((n + 63) / 64) : 1);
    s1f_emn = ((n + 63) / 64) ? ((n + 63) / 64) : 1;
#endif
    S1F st = {0, 0, 0, 0};
    uint64_t nb = (n + 63) / 64;
    uint64_t nk = 0, err = 0;
#if S1F_UTF8 == 3 || S1F_UTF8 == 4
    U8CARRY u8c;
    u8_carry_init(&u8c);
#endif
#if S1F_UTF8 == 5
    U8VCARRY u8v;
    u8v_carry_init(&u8v);
#endif
#if S1F_UTF8 == 6
    uint32_t u8s_need = 0;
    __m256i u8s_prev = _mm256_setzero_si256();
    (void)u8s_prev;
#endif
#if S1F_UTF8 && S1F_UTF8 != 3 && !(S1F_UTF8 == 7 && !S1F_KL_GATE)
    int prev_ascii = 1;
#endif
#if S1F_UTF8 && S1F_UTF8 != 3 && !(S1F_UTF8 == 7 && !S1F_KL_GATE)
    const __m256i high = _mm256_set1_epi8((char)0x80);
#endif
#if S1F_UTF8 == 2
    unsigned pend = 0;
#endif
#if S1F_UTF8 == 7 || S1F_UTF8 == 8
    __m256i u8k = _mm256_setzero_si256();
#endif
    for (uint64_t c0 = 0; c0 < nb; c0 += S1F_CHUNK) {
        uint64_t c1 = c0 + S1F_CHUNK;
        if (c1 > nb) c1 = nb;
        for (uint64_t bi = c0; bi < c1; bi++) {
            const uint8_t *p = b + (bi << 6);
            __m256i v0 = _mm256_loadu_si256((const __m256i *)p);
            __m256i v1 = _mm256_loadu_si256((const __m256i *)(p + 32));
            uint64_t qm, sm, im, wsm = 0, bm = 0, ctl = 0;
            s1f_masks(v0, v1, &st, &qm, &sm, &im, &wsm, &bm, &ctl);
            uint64_t ent = qm | (sm & ~im);
#if S1F_GRAIN == 0
            {
#if S1F_CTAB
                uint64_t ws = wsm;
#else
                uint64_t ws = (uint64_t)s1f_ws32(v0) |
                              ((uint64_t)s1f_ws32(v1) << 32);
#endif
                uint64_t S = ~(im | qm | sm | ws);
                uint64_t stm = S & ~((S << 1) | st.prevS);
                st.prevS = S >> 63;
                ent |= stm;
            }
#endif
            uint64_t lim = n - (bi << 6);
            if (lim < 64) ent &= (1ULL << lim) - 1ULL;
#if S1F_XS
#if defined(SP_MODES) || S1F_XS_DYN
            if (s1f_xs_on)
#else
            if (1)
#endif
            {
#if S1F_XS == 2
                s1f_xsink ^= xl_lanes(bm, ctl, im, &st.bs_prevb, &st.bs_prevs);
#elif S1F_XS == 8
                s1f_xsink ^= ctl;
#else
                uint64_t esc = (S1F_XS == 4)
                                   ? 0
                                   : (S1F_XS == 3)
                                         ? (ctl | bm)
                                         : s1f_lanes_im(bm, ctl, im,
                                                        &st.bs_prevb,
                                                        &st.bs_prevs);
                if (lim < 64) esc &= (1ULL << lim) - 1ULL;
#if defined(SP44_MODES)
                /* the carried class of every escape start: one mask store per
                   block, computed in the pass that already holds the vectors */
                if (s1f_uk)
                    /* only a backslash escape has a carried class: a control
                       byte that happens to be followed by 'u' is not `\u`.
                       A block with no escape start keeps a zero word and pays
                       none of the class work. */
                    s1f_uk[bi] =
                        esc ? k44_block(esc & bm, v0, v1, p, lim) : 0;
#endif
#ifdef S1F_XS_STATS
                { unsigned pc = (unsigned)__builtin_popcountll(esc);
                  s1f_xhist[pc > 8 ? 8 : pc]++;
                  s1f_xlanes_total += pc; s1f_xblocks++;
                  s1f_nim0 += (im == 0);
                  s1f_xbatches += pc ? (pc + 7) / 8 : 0; }
#endif
#if S1F_XS == 15
                if (s1f_fold_doc) s1f_e2[2 * (bi - c0) + 1] = esc;
                else xl_emit(esc, (uint32_t)(bi << 6), xpo, &xk);
#elif S1F_XS == 14
                s1f_e2[2 * (bi - c0) + 1] = esc;
#elif S1F_MASKS
                s1f_em[bi] = esc;
#else
                xl_emit(esc, (uint32_t)(bi << 6), xpo, &xk);
#endif
#endif
            }
#endif
#if S1F_XS == 15
            if (s1f_fold_doc) s1f_e2[2 * (bi - c0)] = ent;
            else s1f_ent[bi - c0] = ent;
#elif S1F_XS == 14
            s1f_e2[2 * (bi - c0)] = ent;
#else
            s1f_ent[bi - c0] = ent;
#endif
#if S1F_UTF8 == 4
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (s1f_u8_fold == 1) {
                    if (!ascii || u8c.need) {
                        err |= (uint64_t)u8_fold_vec(v0, v1, &u8c);
                    } else {
                        u8c.prev = v1;
                    }
                } else if (s1f_u8_fold == 2) {
                    /* no UTF-8 arm at all: the price floor */
                } else if (!(ascii && prev_ascii)) {
                    __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                    err |= (uint64_t)!_mm256_testz_si256(u, u);
                }
                if (!s1f_u8_fold) prev_ascii = ascii;
            }
#elif S1F_UTF8 == 5
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii)) {
                    err |= (uint64_t)u8_foldv_vec(v0, v1, &u8v);
                } else {
                    u8v.prev = v1;
                }
                prev_ascii = ascii;
            }
#elif S1F_UTF8 == 6
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!ascii || u8s_need) {
                    err |= (uint64_t)u8_fold6_vec(v0, v1, &u8s_need);
                } else {
                    u8s_prev = v1;
                }
            }
#elif S1F_UTF8 == 3
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!ascii || u8c.need) {
                    err |= (uint64_t)u8_fold_vec(v0, v1, &u8c);
                } else {
                    u8c.prev = v1;
                }
            }
#elif S1F_UTF8 == 7
#if S1F_KL_DOC
            if (s1f_u8_ungated) {
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            } else {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii))
                    u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
                prev_ascii = ascii;
            }
#elif S1F_KL_GATE
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii))
                    u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
                prev_ascii = ascii;
            }
#else
            u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
#endif
#elif S1F_UTF8 == 8
            if (s1f_u8_kl == 1) {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii))
                    u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
                prev_ascii = ascii;
            } else if (s1f_u8_kl == 3) {
                u8k = _mm256_or_si256(u8k, kl_err_vec_ld(v0, v1, p));
            } else if (s1f_u8_kl == 0) {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii)) {
                    __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                    err |= (uint64_t)!_mm256_testz_si256(u, u);
                }
                prev_ascii = ascii;
            }
#elif S1F_UTF8 == 2
            {
                uint64_t hm = (uint64_t)(uint32_t)_mm256_movemask_epi8(v0) |
                              ((uint64_t)(uint32_t)_mm256_movemask_epi8(v1) << 32);
                if (!hm) {
                    err |= pend;
                    pend = 0;
                } else {
                    __m256i u = _mm256_or_si256(s1f_uchunk_x(p, v0),
                                                    s1f_uchunk_x(p + 32, v1));
                    err |= (uint64_t)!_mm256_testz_si256(u, u);
                    pend = s1f_pend(b, n, bi);
                }
            }
#elif S1F_UTF8
            {
                __m256i any = _mm256_or_si256(v0, v1);
                int ascii = _mm256_testz_si256(any, high);
                if (!(ascii && prev_ascii)) {
                    __m256i u = _mm256_or_si256(s1f_uchunk(p), s1f_uchunk(p + 32));
                    err |= (uint64_t)!_mm256_testz_si256(u, u);
                }
                prev_ascii = ascii;
            }
#endif
        }
#if S1F_XS == 15
        if (s1f_fold_doc)
            s1f_expand_x2(s1f_e2, c0, c1 - c0, out, &nk, xpo, &xk, s1f_xs_on);
        else
            s1f_expand(s1f_ent, c0, c1 - c0, out, &nk);
#elif S1F_XS == 14
        s1f_expand_x2(s1f_e2, c0, c1 - c0, out, &nk, xpo, &xk, s1f_xs_on);
#else
        s1f_expand(s1f_ent, c0, c1 - c0, out, &nk);
#endif
    }
#if S1F_UTF8 == 7
    /* the block loop does not evaluate the position after its last one; a
       C0/C1/F5..FF there is reported one position later, so take it here */
    err |= (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);
#elif S1F_UTF8 == 8
    if (s1f_u8_kl == 1 || s1f_u8_kl == 3) {
        err |= (uint64_t)!_mm256_testz_si256(u8k, u8k);
        if (n && !(n & 63)) err |= (uint64_t)kl_tail_byte(b[n - 1]);
    }
#endif
#if S1F_UTF8
    *uerr = err;
#else
    (void)uerr;
#endif
#if S1F_XS && !S1F_MASKS
    s1f_xn = xk;
#endif
#ifdef S1F_UTF8_LIVE
    return nk ^ (err << 32);
#else
    return nk;
#endif
}

static uint64_t s1f_build_dispatch(const uint8_t *b, uint64_t n, uint32_t *out,
                                   uint64_t *uerr) {
#if S1F_TWOPHASE
    return s1f_build2(b, n, out, uerr);
#else
    return s1f_build(b, n, out, uerr);
#endif
}

/* The escape-position list produced by the last build (S1F_XS only). */
static const uint32_t *s1f_esc_list(uint64_t *nx) {
#if defined(SP_MODES) || S1F_XS_DYN
    if (!s1f_xs_on) { *nx = 0; return NULL; }
#endif
#if S1F_XS && !S1F_MASKS
    *nx = s1f_xn;
    return s1f_xp;
#else
    *nx = 0;
    return NULL;
#endif
}

/* The escape masks produced by the last build (S1F_XS=13 only): one word per
   64-byte document block. */
static const uint64_t *s1f_esc_masks(uint64_t *nm) {
#if S1F_MASKS
    *nm = s1f_emn;
    return s1f_em;
#else
    *nm = 0;
    return NULL;
#endif
}

/* The escape-kind record of the last build: one bit per document byte, set at
   every escape start whose class is `\u`; one word per 64-byte block. */
static const uint64_t *s1f_esc_kind(uint64_t *nm) {
#if defined(SP44_MODES)
    *nm = s1f_ukn;
    return s1f_uk;
#else
    *nm = 0;
    return NULL;
#endif
}
