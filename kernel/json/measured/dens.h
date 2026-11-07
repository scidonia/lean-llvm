/* dens.h -- the document-level readings the gated builds use.  Scratch.

   Two readings, both taken once per build:

   ESCAPE DENSITY -- the probe wm.c's ZF_GATE already makes (`zf_escape_dense`):
   up to 64 samples, one 64-byte block apart, spread over the document,
   counting backslashes.  The gate here keeps three classes instead of one
   boolean, because the two decisions it drives have different boundaries:

     PLAIN   no backslash in the samples (< 1/64 per sampled block).  The
             document has no escapes to decode: the escape-position list is
             pure producer cost there and the body decoder is never called on
             a body, so the out-of-line shape is the right one.
     SPARSE  escapes present but under DENS_HEAVY_NUM per sampled block: the
             escaped bodies are the ones whose per-call prologue dominates, so
             the inlined decoder shape pays.
     HEAVY   at least DENS_HEAVY_NUM per sampled block: escaped bodies carry
             several positions each and the call is amortised, so the
             out-of-line shape pays (and the inlined `\u`-out-of-line shape
             measured worse on the two heavy files).

   The boundaries are scale free: the number of samples is a document-size
   artefact, so both tests compare hits against a multiple of the sample
   count.  On the seven benchmark files the readings are 0, 0, 0, 5, 36, 302,
   341 hits over 65 samples, i.e. the two groups are separated by a factor of
   seven at each boundary.

   UTF-8 ARM -- the third reading, added here: the share of blocks the DFA's
   per-block ASCII gate would skip (`ascii && prev_ascii`).  The gate skips
   work the classifier's own in-string mask would make redundant, so it is
   free on a document whose blocks are almost all ASCII and pure cost on one
   whose blocks almost never are: the test is ~0.8 ns/block and the DFA it
   skips is ~5 ns/block, so the gate pays while the skipped share stays above
   the crossing.  The crossing is not a property of the density alone -- it is
   ~85% for scanned high bytes and ~50% for run-shaped text (results48.md's
   synthetic sweep) -- so the reading is the skip share itself, sampled from
   adjacent block pairs spread over the document, and the decision is taken
   once per document.  A wrong reading costs time only: both arms validate the
   whole document.

   ENTRY DENSITY -- the second reading, added here: how many stage-1 entries
   (quotes, structurals outside strings, scalar starts) the document carries
   per 64-byte block.  It is measured by s1fuse.h's s1f_ent_probe over a block
   sample of its own (the entry stream's classifier needs its string and escape
   state, so the samples are contiguous windows rather than single scattered
   blocks), then handed to dens_pick_kernel.  The kernel that expands a block's
   entry mask into positions is cheapest at a different density: fixed batches
   of eight at the low end, four at the high end, and the POS8 byte-table form
   where a block's mask is dense enough that it writes a store per mask byte
   anyway.  The threshold table lives here; the measurements behind it are in
   results.md of this spike. */
#ifndef DENS_H
#define DENS_H

#include <immintrin.h>
#include <stdint.h>

#define DENS_PLAIN  0
#define DENS_SPARSE 1
#define DENS_HEAVY  2

/* entry-emitter kernels (stage 1's second pass over the block entry masks) */
#define DENS_K_POS8 0
#define DENS_K_B2   1
#define DENS_K_B4   2
#define DENS_K_B8   3

#ifndef DENS_PLAIN_NUM
#define DENS_PLAIN_NUM 1     /* hits/sample below 1/64: plain */
#endif
#ifndef DENS_HEAVY_NUM
#define DENS_HEAVY_NUM 2     /* hits/sample at or above 2: heavy */
#endif

/* Thresholds on the sampled entry density, in 1/256ths, so the pick needs no
   division.

   The frozen-kernel rows of results.md measured the four kernels against each
   other inside one binary on every benchmark document.  Two of them win
   somewhere; the two-entry and four-entry batches win nowhere, outside the
   placement floor of the identical-copy controls:

     document   probe e/blk  esc class  best kernel   delta vs the other
     canonical      6.84     SPARSE     POS8          -1.9..-2.8 ns/blk
     citm           7.88     PLAIN      B8            +1.1..+1.9 for POS8
     dense         26.38     PLAIN      POS8          -13.0 ns/blk
     twitter        7.92     SPARSE     POS8          -2.6..-3.5 ns/blk
     canada         9.88     PLAIN      POS8          -0.4..-0.9 ns/blk
     longstr        1.31     HEAVY      B8            +0.1 for POS8
     escdense       7.36     HEAVY      POS8          -0.3..-1.8 ns/blk

   So the table is: dense-like density -> POS8; a PLAIN document under 8.5
   entries/block -> B8; a document under two entries/block -> B8; everything
   else -> POS8.  The escape class is what separates citm from twitter: they
   have the same entry density (7.9) and opposite preferences, and only the
   escape reading tells them apart.  The PLAIN split at 8.5 is placed midway
   between the only two PLAIN documents that are not dense (citm 7.9, canada
   9.9); nothing measures between them, so that boundary is an interpolation,
   not a resolved crossing.

   DENS_K_B2 and DENS_K_B4 remain kernel ids (the measurement arms) but no
   document class selects them. */
#ifndef DENS_POS8_Q8
#define DENS_POS8_Q8 (20 * 256)   /* dense-like: twenty entries/block and up */
#endif
#ifndef DENS_B8_LOW_Q8
#define DENS_B8_LOW_Q8 (2 * 256)  /* under two entries/block: an 8-slot batch */
#endif
#ifndef DENS_PLAIN_B8_Q8
#define DENS_PLAIN_B8_Q8 (2176)   /* a PLAIN document under 8.5 e/blk: B8 */
#endif
/* The same boundary on a P-core.  canada (PLAIN, 9.88 e/blk) declares POS8 on
   the E-core and B8 on the P-core, so the window in which a PLAIN document
   takes B8 is wider there.  12 e/blk is canada plus a 2.1 e/blk margin; the
   only PLAIN document above it is dense (26.38), which POS8 wins by 13 ns/blk.
   Nothing measures between 12 and 26. */
#ifndef DENS_PLAIN_B8_Q8_P
#define DENS_PLAIN_B8_Q8_P (3072)
#endif

/* Which core class this process is running on.  Read once, cached.

   CPUID leaf 1Ah (Hybrid Information) reports a core type in EAX[31:24] on a
   hybrid part (CPUID.07H.0.EDX[15] says the leaf is valid).  On this machine
   (family 6 model 189) leaf 1Ah reads 0x40 on cpus 0-3 -- the four cores the
   kernel binds to its cpu_core PMU, max 4.9 GHz -- and 0x20 on cpus 4-7, the
   cpu_atom PMU, max 3.7 GHz.  The mapping is therefore 0x40 = P, 0x20 = E on
   this part; the two values are still stored and reported so a different part
   that encodes the other way is visible rather than silently misread.

   AT_HWCAP2 is not a substitute: it reads 0x2 on both classes (it is a
   process-wide auxv word, not a per-core one).  A single CPUID leaf costs a
   few hundred cycles, once, against a pipeline that runs ~100 ns/block. */
#define DENS_CORE_UNKNOWN 0
#define DENS_CORE_P 1
#define DENS_CORE_E 2

static int dens_core_type = -1;    /* leaf 1Ah EAX[31:24], -1 when unavailable */
static int dens_core_class = DENS_CORE_UNKNOWN;
static int dens_core_ready = 0;

static void dens_core_init(void) {
    if (dens_core_ready) return;
    dens_core_ready = 1;
#if defined(__x86_64__) || defined(__i386__)
    uint32_t a, b, c, d;
    __asm__ __volatile__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                         : "a"(0u), "c"(0u) : "memory");
    if (a >= 0x1Au) {
        __asm__ __volatile__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                             : "a"(7u), "c"(0u) : "memory");
        if ((d >> 15) & 1u) {
            __asm__ __volatile__("cpuid" : "=a"(a), "=b"(b), "=c"(c), "=d"(d)
                                 : "a"(0x1Au), "c"(0u) : "memory");
            dens_core_type = (int)((a >> 24) & 0xFFu);
            dens_core_class = dens_core_type == 0x40 ? DENS_CORE_P
                            : dens_core_type == 0x20 ? DENS_CORE_E
                            : DENS_CORE_UNKNOWN;
        }
    }
#endif
}

static inline const char *dens_core_name(int c) {
    return c == DENS_CORE_P ? "P" : c == DENS_CORE_E ? "E" : "?";
}

static inline const char *dens_kernel_name(int k) {
    return k == DENS_K_POS8 ? "POS8" : k == DENS_K_B8 ? "B8" : "other";
}

/* the class of the document the current build is working on; the stage-1
   dispatch sets it once per build, the consumer reads it */
static int dens_doc_class = DENS_SPARSE;

/* The UTF-8 arm's threshold, in 1/256ths of the sampled *skip* fraction --
   the share of blocks the per-block gate would skip (this block ASCII and the
   one before it ASCII).  The gate pays while the work it skips outweighs the
   test: 0.8 vs 5.0 ns/block standalone puts the naive crossing at 16%, the
   synthetic sweep in results48.md puts the measured crossing at ~85% for
   scattered high bytes and ~50% for run-shaped text, and the benchmark
   documents read 71% (twitter, gated wins by 2.2 ns/block on the E-core),
   1.7% (canonical, ungated wins) and 99.5-100% (the five ASCII files, gated
   wins by 2.3-3.6).  154/256 = 60% is the lowest threshold that keeps twitter
   gated; anything in 60..70% routes all seven documents the same way.
   A document below it runs the ungated DFA, which needs no sample at all. */
#ifndef DENS_U8_SKIP_Q8
#define DENS_U8_SKIP_Q8 154
#endif

/* the sampled readings (x256) and the arm they chose:
   0 = the gated DFA (the per-block ASCII test), 1 = the ungated one */
static int dens_u8_q8 = 0;          /* non-ASCII block fraction */
static int dens_u8_skip_q8 = 0;     /* block pairs the gate would skip */
static int dens_u8_ungated = 0;

/* Pick the UTF-8 arm.  `nonascii` of `samples` sampled blocks carry a high
   byte; `skip` of `pairs` adjacent sampled pairs would be skipped by the
   gate. */
static inline void dens_pick_u8(uint64_t nonascii, uint64_t samples,
                                uint64_t skip, uint64_t pairs) {
    dens_u8_q8 = samples ? (int)((nonascii << 8) / samples) : 0;
    dens_u8_skip_q8 = pairs ? (int)((skip << 8) / pairs) : 0;
#ifdef DENS_U8_FORCE
    dens_u8_ungated = DENS_U8_FORCE;
#else
    dens_u8_ungated = (dens_u8_skip_q8 < DENS_U8_SKIP_Q8);
#endif
}

/* the sampled entry density (entries per block, x256) and the kernel it chose */
static int dens_ent_q8 = 0;
static int dens_ent_kernel = DENS_K_B8;

static inline void dens_probe(const uint8_t *b, uint64_t n) {
#if defined(DENS_FORCE)
    (void)b; (void)n;
    dens_doc_class = DENS_FORCE;
#else
    const __m256i vbs = _mm256_set1_epi8('\\');
    uint64_t nb = n >> 6;
    if (!nb) { dens_doc_class = DENS_PLAIN; return; }
    uint64_t step = nb / 64;
    if (!step) step = 1;
    uint64_t hits = 0, samples = 0;
#if S1F_KL_DOC
    uint64_t hbs = 0, sks = 0, skn = 0;
#endif
    for (uint64_t i = 0; i < nb; i += step) {
        const uint8_t *p = b + (i << 6);
        __m256i v = _mm256_loadu_si256((const __m256i *)p);
        hits += (uint64_t)__builtin_popcount((unsigned)_mm256_movemask_epi8(
            _mm256_cmpeq_epi8(v, vbs)));
#if S1F_KL_DOC
        {
            __m256i vh = _mm256_loadu_si256((const __m256i *)(p + 32));
            int na = (_mm256_movemask_epi8(v) |
                      _mm256_movemask_epi8(vh)) != 0;
            hbs += (uint64_t)na;
            /* the gate skips block j when j and j-1 are both ASCII; sampling
               adjacent pairs spread over the document estimates that share
               without depending on the run structure of the text */
            if (i + 1 < nb) {
                const uint8_t *q = p + 64;
                __m256i w0 = _mm256_loadu_si256((const __m256i *)q);
                __m256i w1 = _mm256_loadu_si256((const __m256i *)(q + 32));
                int na1 = (_mm256_movemask_epi8(w0) |
                           _mm256_movemask_epi8(w1)) != 0;
                sks += (uint64_t)(!na && !na1);
                skn++;
            }
        }
#endif
        samples++;
    }
#if S1F_KL_DOC
    /* the UTF-8 arm's reading: this sample is strided over the whole
       document, while the entry probe's is the contiguous head */
    dens_pick_u8(hbs, samples, sks, skn);
#endif
    if (hits * 64 < samples * (uint64_t)DENS_PLAIN_NUM)
        dens_doc_class = DENS_PLAIN;
    else if (hits >= samples * (uint64_t)DENS_HEAVY_NUM)
        dens_doc_class = DENS_HEAVY;
    else
        dens_doc_class = DENS_SPARSE;
#endif
}

/* Pick the entry-emitter kernel from the sampled entry density.  `hits` is
   the number of entries in `blocks` sampled blocks. */
static inline void dens_pick_kernel(uint64_t hits, uint64_t blocks) {
#if defined(DENS_FORCEK)
    (void)hits; (void)blocks;
    dens_ent_q8 = (int)(DENS_FORCEK * 256);
    dens_ent_kernel = DENS_FORCEK;
#else
    int q8 = blocks ? (int)((hits << 8) / blocks) : 0;
    /* Unknown core class keeps the E-core boundary: if the class cannot be
       read, POS8 is the choice whose worst case is smaller (0.55 ns/block if
       the core turns out to be a P-core, against 0.9 the other way). */
    int plain_b8 = (dens_core_class == DENS_CORE_P) ? DENS_PLAIN_B8_Q8_P
                                                    : DENS_PLAIN_B8_Q8;
    dens_ent_q8 = q8;
    if (q8 >= DENS_POS8_Q8)               dens_ent_kernel = DENS_K_POS8;
    else if (q8 < DENS_B8_LOW_Q8)         dens_ent_kernel = DENS_K_B8;
    else if (dens_doc_class == DENS_PLAIN &&
             q8 < plain_b8)               dens_ent_kernel = DENS_K_B8;
    else                                  dens_ent_kernel = DENS_K_POS8;
#endif
}

#ifdef DENS_PRINT
#include <stdio.h>
static inline void dens_report(const char *name) {
    fprintf(stderr, "DENS %s core=%s type=%d class=%d ent_q8=%d kernel=%s "
                    "plain_b8_q8=%d u8_q8=%d u8_skip_q8=%d u8_arm=%s\n",
            name, dens_core_name(dens_core_class), dens_core_type,
            dens_doc_class, dens_ent_q8, dens_kernel_name(dens_ent_kernel),
            dens_core_class == DENS_CORE_P ? DENS_PLAIN_B8_Q8_P
                                           : DENS_PLAIN_B8_Q8,
            dens_u8_q8, dens_u8_skip_q8,
            dens_u8_ungated ? "ungated" : "gated");
}
#endif

#endif /* DENS_H */
