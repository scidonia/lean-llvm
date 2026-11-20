/* bench-contract.c -- a bench-only stage-1 unit with the contracted outputs
   only.

   The stage-1 composite of `kernel/json/pipeline.c` materialises, per 64-byte
   block, six mask words in the caller's `mk` slot and one entry word in
   `entw`, reads them back to compose the next block's word and hand the word
   to the entry emitter, and threads three carry words through `sc` and two
   through `xcarry`.  Of those regions, `pipeline.h`'s post
   (`JsonPipelineContract.pipelineUnitsPost`) reads back exactly two: the entry
   position stream `ep`/`*nk` and the escape position list `xp`/`*nxp`.  The
   masks, the entry word, both carries and the UTF-8 stage's input are
   intermediates: the post names `mk`, `entw`, `sc` and `xcarry` only in its
   `UnchangedOutside` list (regions the run *may* write), and the route's
   adapter copies them out but reads none of them.

   This file is that observation turned into a shape: one pass per document
   that keeps the classifier's six words, both carries and the entry word in
   registers, emits the entry positions directly into the caller's stream,
   appends the escape positions, and writes nothing else.  It is the fused
   loop `tests/json-units-bench/bench-inline.c` already measures with two
   differences: the classifier is inlined into the loop instead of called per
   block, and the two intermediate slots are gone.

   The classifier, the two entry emitters and the escape list are copies at
   the measured compiler line, under this file's names and with the output
   slot replaced by a struct returned by value.  The two entry emitters and
   the escape list are `kernel/json/entry.c`'s and `kernel/json/escape.c`'s
   text.  The classifier is the **adopted** one: its escape mask is
   `kernel/json/s1_block.c` as it stands at main's 2373c4a (the arithmetic
   escape that replaced the pdep/pext/clz form; the rest of the function is
   unchanged), not this worktree's pre-adoption copy.  `kernel/json/` is not
   edited.  The copies are gated: `leanllvm_bench_contract_masks` runs the
   copied classifier over one block against `leanllvm_json_s1_masks`'s six
   words and carry, and `bench-contract.cc` compares every prototype's streams
   against `leanllvm_json_pipeline`'s over every corpus document before a row
   is timed.  A copy that drifts fails the gate; it does not produce a number.

   Not contracted, and therefore not present: `sc`, `mk`, `entw`, `xcarry`.
   The function takes the document, the entry stream and the escape list, and
   returns through the two cursors.  UTF-8 validity stays the separate
   `leanllvm_json_utf8` call it is in `pipeline.c`; the harness times the
   composite with it and both cores without it. */
#include <immintrin.h>
#include <stdint.h>

/* The layout the unit headers fix: `s1_block.h`'s carry at +0/+8/+16 and
   `s1_masks`'s six words at +0..+40.  Declared here rather than included so a
   header change cannot make this copy agree with itself. */
typedef struct { uint64_t esc_open, esc_ppar, im_carry; } bc_carry;
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } bc_masks;

/* ------------------------------------------------------------ classifier -- */
static inline uint64_t bc_prefix_xor(uint64_t x) {
    __m128i v = _mm_cvtsi64_si128((long long)x);
    return (uint64_t)_mm_cvtsi128_si64(
        _mm_clmulepi64_si128(v, _mm_set1_epi8((char)0xFF), 0x00));
}

/* The adopted kernel's escape mask, `s1f_escaped` as it stands at main's
   2373c4a: a run whose first lane is `s` and last lane is `e` escapes the lane
   after it exactly when `e + 1 - s` is odd, so adding the run's start bit to
   the backslash mask carries through the run and marks that lane; the sums are
   separated by the start's parity, because a carry stops on the non-backslash
   lane after a run.  A run that opens in the previous block has its start
   parity in `open & ppar`, which also gives lane zero's boundary escape.  The
   carry out of bit 63 of the odd-class sum is the outgoing run parity.  This
   is the classifier the tree ships; the prototype's arms differ from each
   other, not from this. */
static inline uint64_t bc_escaped(uint64_t bs, uint64_t *open, uint64_t *ppar) {
    const uint64_t even_lanes = 0x5555555555555555ULL;
    uint64_t odd_open = *open & *ppar;
    uint64_t starts = bs & ~(bs << 1);
    uint64_t alt = even_lanes ^ odd_open;
    uint64_t even_class = starts & alt;
    uint64_t odd_class = starts ^ even_class;
    uint64_t notbs = ~bs;
    uint64_t sum_even = bs + even_class;
    uint64_t sum_odd = bs + odd_class;
    uint64_t esc = ((sum_even & notbs) & ~even_lanes) |
                   ((sum_odd & notbs) & even_lanes) |
                   (odd_open & (notbs & 1));
    *ppar = (uint64_t)(sum_odd < bs);
    *open = bs >> 63;
    return esc;
}

static const uint8_t bc_lo_tab[32] __attribute__((aligned(32))) = {
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
    0x40, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x80, 0x82, 0x14, 0x01, 0xA8, 0x00, 0x00,
};
static const uint8_t bc_hi_tab[32] __attribute__((aligned(32))) = {
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x80, 0x00, 0x41, 0x02, 0x00, 0x30, 0x00, 0x0C,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static inline void bc_sw32(__m256i v, uint32_t *sm, uint32_t *ws) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)bc_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)bc_hi_tab), hi));
    *sm = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *ws = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8((char)0xC0)), z));
}

static inline uint64_t bc_sm_ws(__m256i v0, __m256i v1, uint64_t *ws_o) {
    uint32_t s0, s1, w0, w1;
    bc_sw32(v0, &s0, &w0);
    bc_sw32(v1, &s1, &w1);
    *ws_o = (uint64_t)w0 | ((uint64_t)w1 << 32);
    return (uint64_t)s0 | ((uint64_t)s1 << 32);
}

/* `s1f_masks`, with the six words as the return value rather than a caller
   slot: the caller's loop keeps them in registers. */
static inline __attribute__((always_inline))
bc_masks bc_masks64(__m256i v0, __m256i v1, bc_carry *st) {
    bc_masks m;
    __m256i q = _mm256_set1_epi8('"');
    __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    {
        const __m256i v19 = _mm256_set1_epi8(0x1F);
        m.ctl = (uint64_t)(uint32_t)_mm256_movemask_epi8(
                    _mm256_cmpeq_epi8(_mm256_min_epu8(v0, v19), v0)) |
                ((uint64_t)(uint32_t)_mm256_movemask_epi8(
                    _mm256_cmpeq_epi8(_mm256_min_epu8(v1, v19), v1)) << 32);
    }
    m.backslash = bm;
    m.ws = 0;
    m.delim = bc_sm_ws(v0, v1, &m.ws);
    qm &= ~bc_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint64_t im = bc_prefix_xor(qm) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    m.quote = qm;
    m.in_string = im;
    return m;
}

static inline __attribute__((always_inline))
bc_masks bc_block_masks(const uint8_t *p, bc_carry *st) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    return bc_masks64(v0, v1, st);
}

/* The gate's classifier: one block, six words and the carry out through the
   caller's objects.  It is the same inline body the fused loop uses, so a
   mismatch with `leanllvm_json_s1_masks` fails before any row is timed. */
void leanllvm_bench_contract_masks(const uint8_t *p, uint64_t *carry,
                                   uint64_t *out6) {
    bc_carry st = { carry[0], carry[1], carry[2] };
    bc_masks m = bc_block_masks(p, &st);
    carry[0] = st.esc_open;
    carry[1] = st.esc_ppar;
    carry[2] = st.im_carry;
    out6[0] = m.quote;
    out6[1] = m.delim;
    out6[2] = m.in_string;
    out6[3] = m.ws;
    out6[4] = m.backslash;
    out6[5] = m.ctl;
}

/* --------------------------------------------------------------- POS8 -- */
static uint32_t bc_pos8_tab[256][8] __attribute__((aligned(32)));
static int bc_pos8_ready;

const uint32_t *leanllvm_bench_contract_pos8_table(void) {
    if (bc_pos8_ready) return &bc_pos8_tab[0][0];
    for (unsigned m = 0; m < 256; m++) {
        unsigned o = 0;
        for (unsigned t = 0; t < 8; t++)
            if ((m >> t) & 1) bc_pos8_tab[m][o++] = t;
        while (o < 8) bc_pos8_tab[m][o++] = 0;
    }
    bc_pos8_ready = 1;
    return &bc_pos8_tab[0][0];
}

/* `entry.c`'s `inl_ke_pos8` (`bench-inline.c` copies it for the ablation): the
   table pointer is the loop's own, so the eight stores stay in the loop. */
static inline __attribute__((always_inline))
uint64_t bc_emit_pos8(uint64_t m, uint32_t base, uint32_t *o,
                      const uint32_t *tab) {
    if (!m) return 0;
    for (int b = 0; b < 8; b++) {
        unsigned x = (unsigned)((m >> (8 * b)) & 0xFFu);
        __m256i v = _mm256_load_si256((const __m256i *)(tab + 8 * x));
        v = _mm256_add_epi32(v, _mm256_set1_epi32((int)(base + (uint32_t)(8 * b))));
        _mm256_storeu_si256((__m256i *)o, v);
        o += (uint64_t)__builtin_popcount(x);
    }
    return (uint64_t)__builtin_popcountll(m);
}

/* `entry.c`'s `inl_ke_b8`: eight fixed tzcnt slots, then a scalar tail. */
static inline __attribute__((always_inline))
uint64_t bc_emit_b8(uint64_t m, uint32_t base, uint32_t *o) {
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

/* -------------------------------------------------------- escape list -- */
/* `escape.c`'s `xl_lanes`, `xl_batch`, `xl_emit_batch` and `xl_emit`, with the
   two carry words passed as registers rather than through `xcarry`. */
static inline __attribute__((always_inline))
uint64_t bc_esc_lanes(uint64_t bs, uint64_t ctl, uint64_t im,
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

static inline __attribute__((always_inline))
unsigned bc_esc_batch(uint64_t esc, uint32_t base, uint32_t *o) {
    uint64_t c = esc | 0x8000000000000000ULL;
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

static inline __attribute__((always_inline))
void bc_esc_emit(uint64_t esc, uint32_t base, uint32_t *out, uint64_t *k) {
    if (!esc) return;
    uint32_t *o = out + *k;
    unsigned n = bc_esc_batch(esc, base, o);
    *k += n;
    if (__builtin_expect(__builtin_popcountll(esc) > 8, 0)) {
        uint64_t c = esc;
        for (unsigned t = 0; t < 8; t++) c &= c - 1;
        o += 8;
        while (c) {
            unsigned b = bc_esc_batch(c, base, o);
            o += b;
            *k += b;
            for (unsigned t = 0; t < 8; t++) c &= c - 1;
        }
    }
}

/* ------------------------------------------------------- contracted pass -- */
/* One pass over the document.  `ep`/`*nk` is the entry position stream and
   `xp`/`*nxp` the escape position list, both cursors in/out; nothing else is
   written.  The entry emitter and the escape-list arm are compile-time
   selections here rather than a parameter: a caller-facing `arm` would be
   unswitched outside the loop by any implementation that cared, and leaving
   the branch inside costs the core loop the escape path's registers.  The
   four functions below are the four combinations; the dispatcher at the end
   picks one and is what the gate calls.

   The buffers' slack is the units': `ep` must hold `*nk + 64 * blocks + 8`
   words and `xp` must hold `*nxp + 64 * blocks + 8`, the widths the emit
   kernels' batch stores reach.  Only the counts are the stream.

   The escape carry starts at the document's first block, as `xcarry`'s zero
   staging does; the mask carry likewise, as `sc`'s. */
#define BC_PASS(NAME, EMIT, LIST)                                             \
void NAME(const uint8_t *b, uint64_t n, const uint32_t *tab,                   \
          uint32_t *ep, uint64_t *nk, uint32_t *xp, uint64_t *nxp) {           \
    bc_carry sc = { 0, 0, 0 };                                                 \
    uint64_t xc0 = 0, xc1 = 0;                                                 \
    uint64_t prevS = 0;                                                        \
    uint64_t k = *nk;                                                          \
    uint64_t xn = *nxp;                                                        \
    uint64_t nblk = (n + 63) >> 6;                                             \
    for (uint64_t i = 0; i < nblk; i++) {                                      \
        bc_masks m = bc_block_masks(b + (i << 6), &sc);                        \
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);                \
        uint64_t ent = m.quote | (m.delim & ~m.in_string);                     \
        ent |= S & ~((S << 1) | prevS);                                        \
        prevS = S >> 63;                                                       \
        uint64_t lim = n - (i << 6);                                           \
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;                             \
        uint32_t base = (uint32_t)(i << 6);                                    \
        k += EMIT;                                                             \
        if (LIST) {                                                            \
            uint64_t esc = bc_esc_lanes(m.backslash, m.ctl, m.in_string,       \
                                        &xc0, &xc1);                           \
            bc_esc_emit(esc, base, xp, &xn);                                   \
        }                                                                      \
    }                                                                          \
    *nk = k;                                                                   \
    *nxp = xn;                                                                 \
}

/* The emitter's returned count is the cursor step; the escape list advances
   `xn` through its own pointer. */
#define BC_POS8(ent, base, ep, k) bc_emit_pos8(ent, base, (ep) + (k), tab)
#define BC_B8(ent, base, ep, k)   bc_emit_b8(ent, base, (ep) + (k))

BC_PASS(leanllvm_bench_contract_core_pos8, BC_POS8(ent, base, ep, k), 0)
BC_PASS(leanllvm_bench_contract_core_b8,   BC_B8(ent, base, ep, k),   0)
BC_PASS(leanllvm_bench_contract_list_pos8, BC_POS8(ent, base, ep, k), 1)
BC_PASS(leanllvm_bench_contract_list_b8,   BC_B8(ent, base, ep, k),   1)
#undef BC_POS8
#undef BC_B8
#undef BC_PASS

void leanllvm_bench_contract(const uint8_t *b, uint64_t n, const uint32_t *tab,
                             uint32_t *ep, uint64_t *nk,
                             uint32_t *xp, uint64_t *nxp,
                             int b8, int list) {
    if (list) {
        if (b8)
            leanllvm_bench_contract_list_b8(b, n, tab, ep, nk, xp, nxp);
        else
            leanllvm_bench_contract_list_pos8(b, n, tab, ep, nk, xp, nxp);
    } else {
        if (b8)
            leanllvm_bench_contract_core_b8(b, n, tab, ep, nk, xp, nxp);
        else
            leanllvm_bench_contract_core_pos8(b, n, tab, ep, nk, xp, nxp);
    }
}

/* --------------------------------------------------- contracted split pass -- */
/* The same contracted output set as two passes: the mask pass keeps the six
   words and both carries in registers and writes only the entry words it
   composed (an internal scratch of eight bytes per block) and, when the arm
   selects it, the escape positions; the second pass is one entry-emitter call
   over that array.  The emitter is the unit's own call, as the split shape
   uses it, so the difference from `split_core` is the mask pass alone.

   The scratch is not a contract output: it holds nothing the post names, and
   its width is a block's entry word rather than the mask unit's six. */
extern uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                         uint64_t nblk, uint32_t *out,
                                         uint64_t k);
extern uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                       uint64_t nblk, uint32_t *out,
                                       uint64_t k);

#define BC_SPLIT(NAME, LIST)                                                  \
void NAME(const uint8_t *b, uint64_t n, const uint32_t *tab,                  \
          uint32_t *ep, uint64_t *nk, uint32_t *xp, uint64_t *nxp,            \
          uint64_t *ent, int b8) {                                            \
    bc_carry sc = { 0, 0, 0 };                                                \
    uint64_t xc0 = 0, xc1 = 0;                                                \
    uint64_t prevS = 0;                                                       \
    uint64_t xn = *nxp;                                                       \
    uint64_t nblk = (n + 63) >> 6;                                            \
    (void)tab;                                                                \
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        bc_masks m = bc_block_masks(b + (i << 6), &sc);                       \
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);               \
        uint64_t e = m.quote | (m.delim & ~m.in_string);                      \
        e |= S & ~((S << 1) | prevS);                                         \
        prevS = S >> 63;                                                      \
        uint64_t lim = n - (i << 6);                                          \
        if (lim < 64) e &= (1ULL << lim) - 1ULL;                              \
        ent[i] = e;                                                           \
        if (LIST) {                                                           \
            uint64_t esc = bc_esc_lanes(m.backslash, m.ctl, m.in_string,      \
                                        &xc0, &xc1);                          \
            bc_esc_emit(esc, (uint32_t)(i << 6), xp, &xn);                    \
        }                                                                     \
    }                                                                         \
    *nxp = xn;                                                                \
    *nk = b8 ? leanllvm_json_entry_b8(ent, 0, nblk, ep, *nk)                  \
             : leanllvm_json_entry_pos8(ent, 0, nblk, ep, *nk);               \
}

BC_SPLIT(leanllvm_bench_contract_split_core, 0)
BC_SPLIT(leanllvm_bench_contract_split_list, 1)
#undef BC_SPLIT

/* The first pass alone, for the time split: the classifier, the entry word
   composition and the entry-word store (and the escape list when `list`),
   with no emitter call.  The harness times it beside the emitter over the
   array it wrote and the UTF-8 unit over the document. */
#define BC_MASKPASS(NAME, LIST)                                               \
void NAME(const uint8_t *b, uint64_t n, uint64_t *ent, uint64_t *xp,          \
          uint64_t *nxp) {                                                    \
    bc_carry sc = { 0, 0, 0 };                                                \
    uint64_t xc0 = 0, xc1 = 0;                                                \
    uint64_t prevS = 0;                                                       \
    uint64_t xn = 0;                                                          \
    uint64_t nblk = (n + 63) >> 6;                                            \
    for (uint64_t i = 0; i < nblk; i++) {                                     \
        bc_masks m = bc_block_masks(b + (i << 6), &sc);                       \
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);               \
        uint64_t e = m.quote | (m.delim & ~m.in_string);                      \
        e |= S & ~((S << 1) | prevS);                                         \
        prevS = S >> 63;                                                      \
        uint64_t lim = n - (i << 6);                                          \
        if (lim < 64) e &= (1ULL << lim) - 1ULL;                              \
        ent[i] = e;                                                           \
        if (LIST) {                                                           \
            uint64_t esc = bc_esc_lanes(m.backslash, m.ctl, m.in_string,      \
                                        &xc0, &xc1);                          \
            bc_esc_emit(esc, (uint32_t)(i << 6), xp, &xn);                    \
        }                                                                     \
    }                                                                         \
    *nxp = xn;                                                                \
}

BC_MASKPASS(leanllvm_bench_contract_maskpass_core, 0)
BC_MASKPASS(leanllvm_bench_contract_maskpass_list, 1)
#undef BC_MASKPASS

void leanllvm_bench_contract_maskpass(const uint8_t *b, uint64_t n,
                                      uint64_t *ent, uint64_t *xp,
                                      uint64_t *nxp, int list) {
    if (list)
        leanllvm_bench_contract_maskpass_list(b, n, ent, xp, nxp);
    else
        leanllvm_bench_contract_maskpass_core(b, n, ent, xp, nxp);
}

/* ---------------------------------------------- candidate: fast mask pass -- */
/* Changes to the mask pass, all invisible to the contracted outputs and all
   on top of the adopted classifier (`bc_escaped` above is the shipped
   `s1f_escaped`).

   The composition asks the classifier for two masks it already computes
   rather than three: `delim` (the six structural bytes) and `neither` (neither
   structural nor whitespace).  `ws` is never needed on its own --
   `S = neither & ~quote & ~in_string` is the same complement the staged loop
   builds from four masks -- and `ctl` is needed only by the escape list, so
   the list-free body does not compute it at all.

   The block loop peels the final partial block so the `lim < 64` test is not
   in the full-block loop.  Everything else is the same loop, and the harness
   gates the entry stream and cursor against `leanllvm_json_pipeline` on every
   document before a row is timed. */

static inline void bc_sw32_dn(__m256i v, uint32_t *d, uint32_t *n) {
    const __m256i m4 = _mm256_set1_epi8(0x0F), z = _mm256_setzero_si256();
    __m256i lo = _mm256_and_si256(v, m4);
    __m256i hi = _mm256_and_si256(_mm256_srli_epi16(v, 4), m4);
    __m256i r = _mm256_and_si256(
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)bc_lo_tab), lo),
        _mm256_shuffle_epi8(_mm256_load_si256((const __m256i *)bc_hi_tab), hi));
    *d = (uint32_t)~_mm256_movemask_epi8(
        _mm256_cmpeq_epi8(_mm256_and_si256(r, _mm256_set1_epi8(0x3F)), z));
    *n = (uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(r, z));
}

static inline __attribute__((always_inline))
void bc_fast_masks64(__m256i v0, __m256i v1, bc_carry *st,
                     uint64_t *q_o, uint64_t *d_o, uint64_t *im_o,
                     uint64_t *n_o) {
    __m256i q = _mm256_set1_epi8('"');
    __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    uint64_t qq = qm & ~bc_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint32_t d0, d1, n0, n1;
    bc_sw32_dn(v0, &d0, &n0);
    bc_sw32_dn(v1, &d1, &n1);
    *d_o = (uint64_t)d0 | ((uint64_t)d1 << 32);
    *n_o = (uint64_t)n0 | ((uint64_t)n1 << 32);
    uint64_t im = bc_prefix_xor(qq) ^ st->im_carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *q_o = qq;
    *im_o = im;
}

/* Classifier only, both forms, for the time split: neither writes a stream,
   so a checksum of the masks keeps the work from being eliminated. */
void leanllvm_bench_contract_classify(const uint8_t *b, uint64_t n,
                                      uint64_t *sink) {
    bc_carry st = { 0, 0, 0 };
    uint64_t acc = 0, nblk = (n + 63) >> 6;
    for (uint64_t i = 0; i < nblk; i++) {
        bc_masks m = bc_block_masks(b + (i << 6), &st);
        acc ^= m.quote ^ m.delim ^ m.in_string ^ m.ws ^ m.backslash ^ m.ctl;
    }
    *sink ^= acc;
}

void leanllvm_bench_contract_classify_fast(const uint8_t *b, uint64_t n,
                                           uint64_t *sink) {
    bc_carry st = { 0, 0, 0 };
    uint64_t acc = 0, nblk = (n + 63) >> 6;
    for (uint64_t i = 0; i < nblk; i++) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        acc ^= q ^ d ^ im ^ nn;
    }
    *sink ^= acc;
}

/* The list-free mask pass: entry words only. */
void leanllvm_bench_contract_maskfast(const uint8_t *b, uint64_t n,
                                      uint64_t *ent) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    for (uint64_t i = 0; i < nfull; i++) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
    }
    if (rem) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
    }
}

/* The 4-wide sparse emitter: simdjson's `bit_indexer` step.  Four fixed
   slots cover a string-boundary block's quote/comma positions; only a block
   with more than four entries writes a second group. */
static inline __attribute__((always_inline))
uint64_t bc_emit4(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 4) return n;
    o += 4;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 8) return n;
    o += 4;
    uint64_t k = 8;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

void leanllvm_bench_contract_emit4(const uint64_t *ent, uint64_t nblk,
                                   uint32_t *ep, uint64_t *nk) {
    uint64_t k = 0;
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t m = ent[i];
        if (m) k += bc_emit4(m, (uint32_t)(i << 6), ep + k);
    }
    *nk = k;
}

void leanllvm_bench_contract_splitfast(const uint8_t *b, uint64_t n,
                                       uint32_t *ep, uint64_t *nk,
                                       uint64_t *ent) {
    leanllvm_bench_contract_maskfast(b, n, ent);
    leanllvm_bench_contract_emit4(ent, (n + 63) >> 6, ep, nk);
}

/* ------------------------------------------- candidate: 3-wide emitter -- */
/* The strings corpus's modal non-empty block carries three entry positions
   (the two quotes of a string boundary and the comma), so three fixed slots
   are the natural group; a block above three writes a second group of four
   before the scalar tail. */
static inline __attribute__((always_inline))
uint64_t bc_emit3(uint64_t m, uint32_t base, uint32_t *o) {
    if (!m) return 0;
    uint64_t n = (uint64_t)__builtin_popcountll(m);
    uint64_t c = m;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 3) return n;
    o += 3;
    o[0] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[1] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[2] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    o[3] = base + (uint32_t)__builtin_ctzll(c); c &= c - 1;
    if (n <= 7) return n;
    o += 4;
    uint64_t k = 7;
    while (c) { *o++ = base + (uint32_t)__builtin_ctzll(c); k++; c &= c - 1; }
    return k;
}

void leanllvm_bench_contract_emit3(const uint64_t *ent, uint64_t nblk,
                                   uint32_t *ep, uint64_t *nk) {
    uint64_t k = 0;
    for (uint64_t i = 0; i < nblk; i++) {
        uint64_t m = ent[i];
        if (m) k += bc_emit3(m, (uint32_t)(i << 6), ep + k);
    }
    *nk = k;
}

void leanllvm_bench_contract_splitfast3(const uint8_t *b, uint64_t n,
                                        uint32_t *ep, uint64_t *nk,
                                        uint64_t *ent) {
    leanllvm_bench_contract_maskfast(b, n, ent);
    leanllvm_bench_contract_emit3(ent, (n + 63) >> 6, ep, nk);
}

/* ------------------------------------- candidate: in-string half fast path -- */
/* A 32-byte half that begins inside a string and has no un-escaped quote is
   all string content: its structural, whitespace and scalar-start masks are
   zero whatever the bytes are, so the two-table classification of that half
   can be skipped.  The quote word decides it; the backslash word does not,
   because an escape may only hide a quote and there is none in the half.  The
   prefix xor is skipped too when the block's quote word is zero, which is the
   same case with the carry choosing all-ones or all-zeros.

   Measured and rejected.  The in-string pattern is irregular at 32-byte
   granularity, so the two skips mispredict: on `syn-strings-64k` the classifier
   costs 0.250 cycles per byte against `classify_fast`'s 0.204, and on
   `syn-strings-4m` 0.692 against 0.211.  It stays in the harness as the
   recorded negative result; the kept candidate is the branchless one below. */
static inline __attribute__((always_inline))
void bc_fast2_masks64(__m256i v0, __m256i v1, bc_carry *st,
                      uint64_t *q_o, uint64_t *d_o, uint64_t *im_o,
                      uint64_t *n_o) {
    __m256i q = _mm256_set1_epi8('"');
    __m256i bs = _mm256_set1_epi8('\\');
    uint64_t qm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, q)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, q)) << 32);
    uint64_t bm = (uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v0, bs)) |
                  ((uint64_t)(uint32_t)_mm256_movemask_epi8(_mm256_cmpeq_epi8(v1, bs)) << 32);
    uint64_t qq = qm & ~bc_escaped(bm, &st->esc_open, &st->esc_ppar);
    uint64_t carry = st->im_carry;
    uint32_t d0 = 0, d1 = 0, n0 = 0, n1 = 0;
    int lo_fast = (int)(carry & 1) && (uint32_t)qq == 0;
    int hi_fast = lo_fast && (uint32_t)(qq >> 32) == 0;
    if (!lo_fast) bc_sw32_dn(v0, &d0, &n0);
    if (!hi_fast) bc_sw32_dn(v1, &d1, &n1);
    uint64_t im;
    if (qq == 0)
        im = carry;
    else
        im = bc_prefix_xor(qq) ^ carry;
    st->im_carry = (uint64_t)((int64_t)im >> 63);
    *q_o = qq;
    *d_o = (uint64_t)d0 | ((uint64_t)d1 << 32);
    *n_o = (uint64_t)n0 | ((uint64_t)n1 << 32);
    *im_o = im;
}

void leanllvm_bench_contract_classify_fast2(const uint8_t *b, uint64_t n,
                                            uint64_t *sink) {
    bc_carry st = { 0, 0, 0 };
    uint64_t acc = 0, nblk = (n + 63) >> 6;
    for (uint64_t i = 0; i < nblk; i++) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast2_masks64(v0, v1, &st, &q, &d, &im, &nn);
        acc ^= q ^ d ^ im ^ nn;
    }
    *sink ^= acc;
}

void leanllvm_bench_contract_maskfast2(const uint8_t *b, uint64_t n,
                                       uint64_t *ent) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    for (uint64_t i = 0; i < nfull; i++) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast2_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
    }
    if (rem) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6) + 32));
        uint64_t q, d, im, nn;
        bc_fast2_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
    }
}

void leanllvm_bench_contract_splitfast2(const uint8_t *b, uint64_t n,
                                        uint32_t *ep, uint64_t *nk,
                                        uint64_t *ent) {
    leanllvm_bench_contract_maskfast2(b, n, ent);
    leanllvm_bench_contract_emit4(ent, (n + 63) >> 6, ep, nk);
}

/* The UTF-8 unit's Keiser-Lemire vector, copied here (kernel/json is not
   edited) so the mask pass can run its ASCII gate on the vectors already
   loaded instead of sweeping the document a second time.  The gated form's
   rule is the unit's: a block pays the DFA when it or its predecessor is
   non-ASCII, and the document-end tail byte is checked outside the loop. */
static const uint8_t bc_kl_t1[32] __attribute__((aligned(32))) = {
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
    0xe7, 0xa3, 0x83, 0x83, 0x8b, 0xcb, 0xcb, 0xcb,
    0xcb, 0xcb, 0xcb, 0xcb, 0xcb, 0xdb, 0xcb, 0xcb,
};
static const uint8_t bc_kl_t2[32] __attribute__((aligned(32))) = {
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
    0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02, 0x02,
    0x80, 0x80, 0x80, 0x80, 0x21, 0x01, 0x15, 0x49,
};
static const uint8_t bc_kl_t3[32] __attribute__((aligned(32))) = {
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
    0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
    0xe6, 0xae, 0xba, 0xba, 0x01, 0x01, 0x01, 0x01,
};

static inline __m256i bc_kl_err32(__m256i v, const uint8_t *p) {
    const __m256i m4 = _mm256_set1_epi8(0x0F);
    const __m256i b80 = _mm256_set1_epi8((char)0x80);
    __m256i p1 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 1));
    __m256i p2 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 2));
    __m256i p3 = _mm256_loadu_si256((const __m256i *)(const void *)(p - 3));
    __m256i sc = _mm256_and_si256(
        _mm256_and_si256(
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)bc_kl_t1),
                _mm256_and_si256(p1, m4)),
            _mm256_shuffle_epi8(
                _mm256_load_si256((const __m256i *)bc_kl_t2),
                _mm256_and_si256(_mm256_srli_epi16(p1, 4), m4))),
        _mm256_shuffle_epi8(
            _mm256_load_si256((const __m256i *)bc_kl_t3),
            _mm256_and_si256(_mm256_srli_epi16(v, 4), m4)));
    __m256i must = _mm256_and_si256(
        _mm256_or_si256(
            _mm256_subs_epu8(p2, _mm256_set1_epi8(0x60)),
            _mm256_subs_epu8(p3, _mm256_set1_epi8(0x70))),
        b80);
    return _mm256_xor_si256(sc, must);
}

static inline __m256i bc_kl_err_vec(__m256i v0, __m256i v1, const uint8_t *p) {
    return _mm256_or_si256(bc_kl_err32(v0, p), bc_kl_err32(v1, p + 32));
}

static inline int bc_kl_tail_byte(uint8_t b) {
    return (b & 0xFE) == 0xC0 || b >= 0xF5;
}

/* The mask pass with the UTF-8 stage's gated check fused into its loop.  The
   vectors are the ones the classifier already loaded, and the return word is
   the unit's error word, gated against `leanllvm_json_utf8`. */
uint64_t leanllvm_bench_contract_maskfast2_u8(const uint8_t *b, uint64_t n,
                                              uint64_t *ent) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    __m256i u8k = _mm256_setzero_si256();
    const __m256i high = _mm256_set1_epi8((char)0x80);
    int prev_ascii = 1;
    for (uint64_t i = 0; i <= nfull; i++) {
        if (i == nfull && !rem) break;
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast2_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        if (i < nfull)
            ent[i] = e;
        else
            ent[i] = e & ((1ULL << rem) - 1ULL);
        __m256i any = _mm256_or_si256(v0, v1);
        int ascii = _mm256_testz_si256(any, high);
        if (!(ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, bc_kl_err_vec(v0, v1, p));
        prev_ascii = ascii;
    }
    uint64_t err = (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)bc_kl_tail_byte(b[n - 1]);
    return err;
}

uint64_t leanllvm_bench_contract_splitfast2_u8(const uint8_t *b, uint64_t n,
                                               uint32_t *ep, uint64_t *nk,
                                               uint64_t *ent) {
    uint64_t err = leanllvm_bench_contract_maskfast2_u8(b, n, ent);
    leanllvm_bench_contract_emit4(ent, (n + 63) >> 6, ep, nk);
    return err;
}

/* The fast mask pass with the UTF-8 gate fused, peeled into a full-block loop
   and a partial last block.  The first form kept the partial-block test inside
   the loop and paid about 0.05 cycles per byte for it on the all-ASCII string
   corpus; peeling leaves the ASCII gate as the only added work. */
uint64_t leanllvm_bench_contract_maskfast_u8(const uint8_t *b, uint64_t n,
                                             uint64_t *ent) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    __m256i u8k = _mm256_setzero_si256();
    const __m256i high = _mm256_set1_epi8((char)0x80);
    int prev_ascii = 1;
    for (uint64_t i = 0; i < nfull; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
        __m256i any = _mm256_or_si256(v0, v1);
        int ascii = _mm256_testz_si256(any, high);
        if (!(ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, bc_kl_err_vec(v0, v1, p));
        prev_ascii = ascii;
    }
    if (rem) {
        const uint8_t *p = b + (nfull << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
        __m256i any = _mm256_or_si256(v0, v1);
        int ascii = _mm256_testz_si256(any, high);
        if (!(ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, bc_kl_err_vec(v0, v1, p));
    }
    uint64_t err = (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)bc_kl_tail_byte(b[n - 1]);
    return err;
}

uint64_t leanllvm_bench_contract_splitfast_u8(const uint8_t *b, uint64_t n,
                                              uint32_t *ep, uint64_t *nk,
                                              uint64_t *ent) {
    uint64_t err = leanllvm_bench_contract_maskfast_u8(b, n, ent);
    leanllvm_bench_contract_emit4(ent, (n + 63) >> 6, ep, nk);
    return err;
}

uint64_t leanllvm_bench_contract_splitfast3_u8(const uint8_t *b, uint64_t n,
                                               uint32_t *ep, uint64_t *nk,
                                               uint64_t *ent) {
    uint64_t err = leanllvm_bench_contract_maskfast_u8(b, n, ent);
    leanllvm_bench_contract_emit3(ent, (n + 63) >> 6, ep, nk);
    return err;
}

/* One pass with the emitter lagged one block: block `i`'s entry word is
   emitted after block `i+1` is classified, so the emitter's serial tzcnt
   chain overlaps the next block's vector work and no `ent` array is written.
   The mask words are contracted exactly as in the two-pass shape; the emitter
   is the same kernel, just called from the same loop.  This is the fused
   shape, and its proof cost is stated with the recommendation. */
uint64_t leanllvm_bench_contract_splitlag3(const uint8_t *b, uint64_t n,
                                           uint32_t *ep, uint64_t *nk) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    uint64_t k = 0, prev_ent = 0, prev_base = 0;
    int have = 0;
    for (uint64_t i = 0; i < nfull; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
        prev_ent = e;
        prev_base = (uint32_t)(i << 6);
        have = 1;
    }
    if (rem) {
        const uint8_t *p = b + (nfull << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        e &= (1ULL << rem) - 1ULL;
        if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
        prev_ent = e;
        prev_base = (uint32_t)(nfull << 6);
        have = 1;
    }
    if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
    *nk = k;
}

uint64_t leanllvm_bench_contract_splitlag3_u8(const uint8_t *b, uint64_t n,
                                              uint32_t *ep, uint64_t *nk) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    uint64_t k = 0, prev_ent = 0, prev_base = 0;
    int have = 0;
    __m256i u8k = _mm256_setzero_si256();
    const __m256i high = _mm256_set1_epi8((char)0x80);
    int prev_ascii = 1;
    for (uint64_t i = 0; i < nfull; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
        prev_ent = e;
        prev_base = (uint32_t)(i << 6);
        have = 1;
        __m256i any = _mm256_or_si256(v0, v1);
        int ascii = _mm256_testz_si256(any, high);
        if (!(ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, bc_kl_err_vec(v0, v1, p));
        prev_ascii = ascii;
    }
    if (rem) {
        const uint8_t *p = b + (nfull << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        e &= (1ULL << rem) - 1ULL;
        if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
        prev_ent = e;
        prev_base = (uint32_t)(nfull << 6);
        have = 1;
        __m256i any = _mm256_or_si256(v0, v1);
        int ascii = _mm256_testz_si256(any, high);
        if (!(ascii && prev_ascii))
            u8k = _mm256_or_si256(u8k, bc_kl_err_vec(v0, v1, p));
    }
    if (have) k += bc_emit3(prev_ent, prev_base, ep + k);
    *nk = k;
    uint64_t err = (uint64_t)!_mm256_testz_si256(u8k, u8k);
    if (n && !(n & 63)) err |= (uint64_t)bc_kl_tail_byte(b[n - 1]);
    return err;
}

/* The document-level ASCII class, accumulated in the mask pass: two `vpor`s
   per block over the vectors already loaded, one test after the loop.  A
   document whose bytes are all below 0x80 is valid UTF-8, so the UTF-8 unit's
   word is zero on its staged window (three zero bytes before and zero padding
   after are ASCII too, and its tail rule accepts every ASCII byte); the caller
   can then skip the unit's sweep entirely.  Otherwise the unit is called at
   its existing ABI, so its contract and theorem are unchanged. */
extern uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated);

int leanllvm_bench_contract_maskfast_probe(const uint8_t *b, uint64_t n,
                                           uint64_t *ent) {
    bc_carry st = { 0, 0, 0 };
    uint64_t prevS = 0;
    uint64_t nfull = n >> 6, rem = n & 63;
    __m256i a0 = _mm256_setzero_si256(), a1 = _mm256_setzero_si256();
    const __m256i high = _mm256_set1_epi8((char)0x80);
    for (uint64_t i = 0; i < nfull; i++) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (i << 6) + 32));
        a0 = _mm256_or_si256(a0, v0);
        a1 = _mm256_or_si256(a1, v1);
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        ent[i] = e;
    }
    if (rem) {
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6)));
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + (nfull << 6) + 32));
        a0 = _mm256_or_si256(a0, v0);
        a1 = _mm256_or_si256(a1, v1);
        uint64_t q, d, im, nn;
        bc_fast_masks64(v0, v1, &st, &q, &d, &im, &nn);
        uint64_t S = nn & ~q & ~im;
        uint64_t e = q | (d & ~im);
        e |= S & ~((S << 1) | prevS);
        ent[nfull] = e & ((1ULL << rem) - 1ULL);
    }
    return _mm256_testz_si256(_mm256_or_si256(a0, a1), high);
}

uint64_t leanllvm_bench_contract_splitprobe3(const uint8_t *b, uint64_t n,
                                             uint32_t *ep, uint64_t *nk,
                                             uint64_t *ent) {
    int ascii = leanllvm_bench_contract_maskfast_probe(b, n, ent);
    leanllvm_bench_contract_emit3(ent, (n + 63) >> 6, ep, nk);
    return ascii ? 0 : leanllvm_json_utf8(b, n, 0);
}

uint64_t leanllvm_bench_contract_splitprobe_b8(const uint8_t *b, uint64_t n,
                                               uint32_t *ep, uint64_t *nk,
                                               uint64_t *ent) {
    int ascii = leanllvm_bench_contract_maskfast_probe(b, n, ent);
    *nk = leanllvm_json_entry_b8(ent, 0, (n + 63) >> 6, ep, 0);
    return ascii ? 0 : leanllvm_json_utf8(b, n, 0);
}

uint64_t leanllvm_bench_contract_splitfast_b8_u8(const uint8_t *b, uint64_t n,
                                                 uint32_t *ep, uint64_t *nk,
                                                 uint64_t *ent) {
    uint64_t err = leanllvm_bench_contract_maskfast_u8(b, n, ent);
    *nk = leanllvm_json_entry_b8(ent, 0, (n + 63) >> 6, ep, 0);
    return err;
}

/* The class-selected composite.  `b8` is the pipeline's existing per-document
   emitter arm (pos8 on the dense/route class, b8 on strings/UTF-8), and the
   first block's ASCII class picks the UTF-8 mode: an ASCII-first document
   runs the probe and pays the UTF-8 unit only if a later block is non-ASCII;
   a document whose first block already carries a high byte runs the fused
   gate, because its DFA work overlaps the classifier.  A wrong guess costs a
   unit sweep, not a wrong answer: the probe mode still calls the unit when the
   document is not all ASCII.
   The emitter also follows the class: pos8 when the arm is dense, the 3-wide
   emitter on a document that fits the 64 KiB working-set choice, b8 otherwise
   (the 3-wide emitter's count branch costs more than its shorter group once
   the output stream leaves the cache, which the 4 MiB rows show). */
uint64_t leanllvm_bench_contract_splitauto(const uint8_t *b, uint64_t n,
                                           int b8, uint32_t *ep, uint64_t *nk,
                                           uint64_t *ent) {
    const __m256i high = _mm256_set1_epi8((char)0x80);
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)b);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(b + 32));
    int first_ascii = _mm256_testz_si256(_mm256_or_si256(v0, v1), high);
    int small = n <= (1u << 16);
    if (first_ascii) {
        int ascii = leanllvm_bench_contract_maskfast_probe(b, n, ent);
        if (!b8)
            *nk = leanllvm_json_entry_pos8(ent, 0, (n + 63) >> 6, ep, 0);
        else if (small)
            leanllvm_bench_contract_emit3(ent, (n + 63) >> 6, ep, nk);
        else
            *nk = leanllvm_json_entry_b8(ent, 0, (n + 63) >> 6, ep, 0);
        return ascii ? 0 : leanllvm_json_utf8(b, n, 0);
    }
    uint64_t err = leanllvm_bench_contract_maskfast_u8(b, n, ent);
    if (!b8)
        *nk = leanllvm_json_entry_pos8(ent, 0, (n + 63) >> 6, ep, 0);
    else if (small)
        leanllvm_bench_contract_emit3(ent, (n + 63) >> 6, ep, nk);
    else
        *nk = leanllvm_json_entry_b8(ent, 0, (n + 63) >> 6, ep, 0);
    return err;
}
