/* entry-opt.c -- the entry emitter's shapes measured against the shape
   `pipeline.c` calls today, on one document, in one binary.

   What is measured.  `pipeline.c` calls the installed emitter once per block,
   with `nblk = 1`.  On `syn-strings-64k` that is 1024 calls, 679 of whose words
   are nonzero and 84% of whose mask-byte groups are empty.  The shapes under
   test are

     emitter/perblock        the installed emitter, one call per block (today)
     emitter/batch           the installed emitter, one call over all words
     emitter/perblock-skip   the group loop with an empty byte's group skipped
     emitter/batch-skip      the same, batched
     emitter/perblock-sparse one 4-byte store per set lane, per block
     emitter/batch-sparse    the same, batched

   and, in the stage-1 loop's own context (mask unit, entry word, escape list),

     s1/prologue             the loop without an emitter
     s1/perblock             the loop plus the installed emitter, per block
     s1/batch                the loop plus the installed emitter, batched
     s1/batch-skip           the loop plus the skip shape, batched
     s1/batch-sparse         the loop plus the sparse shape, batched

   The stage-1 rows all store one entry word per block and all build the escape
   list, so their paired differences isolate the emission term and the call
   shape.  `pipeline` is the installed pipeline, a row the others are placed
   against rather than a claim about the route's interval.

   The gates.  Before the clock and again after it:

     - the pipeline call accepts with the document's recorded counts;
     - a separately run stage-1 loop writes the entry stream and escape list
       the pipeline wrote, and stage 2 over them writes the same header words
       and the same arena and event bytes;
     - every emitter and stage-1 shape writes the same entry stream, leaves no
       word at or past `k' + 8`, and gives stage 2 the same output;
     - the stage-1 shapes record the same mask words;
     - the emitters agree on the arms the row driver uses: the 64 single lanes,
       the 256 group-0 byte values, 65536 splitmix64 words as single-word
       streams, the empty and full words, a 4096-word splitmix64 stream, the
       1025-word line of the document's own words, 1024 random slices of that
       line, and the document's words batched -- each at a nonzero `blk0` as
       well as at 0 where the stream has more than one word.

   A gate failure exits 3 and prints nothing as a measurement.

   The statistics follow `cost-profile`: each round times every act `reps`
   times in a rotated order, an act's sample is the round's median, a row is
   the median of the round medians with the minimum and maximum beside it, and
   a delta is the median of that round's paired difference.  Every row carries
   a calibrated-clock figure: the chain is a dependent-add chain of 2,000,000
   iterations, so cycles are the round's act median times the iteration count
   over the round's chain time.  Each act is timed over `passes` full passes and
   the sample is the total divided by `passes`.

   Usage: entry-opt --doc <path> [--rounds N] [--reps N] [--passes N]
                    [--gates-only]

   Exit status: 0 on a complete run with every gate held; 2 on a bad argument
   or an unreadable document; 3 on a gate disagreement. */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "entry.h"
#include "escape.h"
#include "pipeline.h"
#include "s1_block.h"
#include "stage2.h"
#include "utf8.h"

/* The entry-opt unit's two other shapes (`entry_variants.c`). */
void eo_table_init(void);
int eo_table_check(void);
uint64_t eo_entry_pos8_skip(const uint64_t *ent, uint64_t blk0, uint64_t nblk,
                            uint32_t *out, uint64_t k);
uint64_t eo_entry_sparse(const uint64_t *ent, uint64_t blk0, uint64_t nblk,
                         uint32_t *out, uint64_t k);

#define ARM 2ULL
#define CHAIN_IT 2000000ULL
#define SENT_WORD 0xA5A5A5A5u
#define MAX_ACTS 16
#define MAX_REPS 401
#define MAX_ROUNDS 401

/* The document's recorded observation, so a different document cannot be
   measured under this report's name. */
#define EXPECT_SIZE ((uint64_t)65536)
#define EXPECT_NK ((uint64_t)2056)
#define EXPECT_NXP ((uint64_t)1772)
#define EXPECT_NDST ((uint64_t)55931)
#define EXPECT_NEV ((uint64_t)8907)

static volatile uint64_t sink;

/* ---------------------------------------------------------------- time -- */
static uint64_t now_ns(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
        perror("clock_gettime");
        exit(2);
    }
    return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

/* `add $1; dec; jne` is one iteration per cycle on this part. */
static uint64_t clock_chain(uint64_t it) {
    uint64_t x = 0;
    __asm__ volatile("1: add $1, %0\n\tdec %1\n\tjne 1b"
                     : "+r"(x), "+r"(it)
                     :
                     : "cc");
    return x + it;
}

/* --------------------------------------------------------------- stats -- */
static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y ? 1 : 0;
}

static uint64_t median_of(const uint64_t *v, size_t n) {
    uint64_t *t = malloc(n * sizeof *t);
    if (t == NULL) { fprintf(stderr, "entry-opt: out of memory\n"); exit(2); }
    memcpy(t, v, n * sizeof *t);
    qsort(t, n, sizeof *t, cmp_u64);
    uint64_t m = t[(n - 1) / 2];
    free(t);
    return m;
}

typedef struct { uint64_t median, min, max; } summary;

static summary summarise(const uint64_t *v, size_t n) {
    summary s;
    s.median = median_of(v, n);
    s.min = s.max = v[0];
    for (size_t i = 1; i < n; i++) {
        if (v[i] < s.min) s.min = v[i];
        if (v[i] > s.max) s.max = v[i];
    }
    return s;
}

static uint64_t fnv1a(uint64_t h, const uint8_t *p, uint64_t n) {
    for (uint64_t i = 0; i < n; i++) {
        h ^= p[i];
        h *= 0x100000001b3ull;
    }
    return h;
}

static void fill_sentinel(uint32_t *p, uint64_t n) {
    for (uint64_t i = 0; i < n; i++) p[i] = SENT_WORD;
}

/* --------------------------------------------------------------- state -- */
typedef struct {
    const uint8_t *doc;
    uint64_t n, blocks;
    uint64_t epcap, xpcap, dstcap, evcap;
    uint8_t *win;

    /* the buffers the emitter and stage-1 acts write */
    uint32_t *ep;
    uint32_t *xp;
    uint64_t *entws;
    s1_masks *mks;

    /* the pipeline's own call, for the reference and the `pipeline` act */
    uint64_t *sc_p, *mk_p, *entw_p, *nk_p, *xcarry_p, *nxp_p;
    uint32_t *ep_p, *xp_p;
    uint8_t *dst_p, *ev_p;
    uint64_t *ndst_p, *nev_p, *err_p;

    /* the reference observation */
    uint64_t ref_verdict, ref_nk, ref_nxp, ref_ndst, ref_nev, ref_err;
    uint32_t *ep_ref, *xp_ref;
    uint8_t *dst_ref, *ev_ref;

    /* the downstream check's own destination */
    uint8_t *dst_a, *ev_a;
    uint64_t *ndst_a, *nev_a, *err_a;

    uint64_t passes;
} state;

static state S;
static int gate_failures;

static void gate_fail(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
static void gate_fail(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    printf("GATE FAILED: ");
    vprintf(fmt, ap);
    printf("\n");
    va_end(ap);
    gate_failures++;
}

/* ----------------------------------------------------------- allocation -- */
static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (p == NULL) { fprintf(stderr, "entry-opt: out of memory\n"); exit(2); }
    return p;
}

static void *xcalloc(size_t n) {
    void *p = calloc(n ? n : 1, 1);
    if (p == NULL) { fprintf(stderr, "entry-opt: out of memory\n"); exit(2); }
    return p;
}

/* ------------------------------------------------------------- the call -- */
static void state_init(state *s, const char *path) {
    FILE *f = fopen(path, "rb");
    if (f == NULL) { perror(path); exit(2); }
    if (fseek(f, 0, SEEK_END) != 0) { perror("fseek"); exit(2); }
    long sz = ftell(f);
    if (sz < 0) { perror("ftell"); exit(2); }
    if (fseek(f, 0, SEEK_SET) != 0) { perror("fseek"); exit(2); }
    s->n = (uint64_t)sz;
    s->blocks = (s->n + 63) >> 6;
    s->epcap = 64 * s->blocks + 9;
    s->xpcap = 64 * s->blocks + 8;
    s->dstcap = s->n + 64;
    s->evcap = 13 * s->n + 128;

    s->win = xcalloc(3 + s->n + 32);
    /* The route stages the document at offset 3 of a zero-filled window and
       leaves 32 bytes past its end. */
    if (fread(s->win + 3, 1, s->n, f) != s->n) { perror("fread"); exit(2); }
    fclose(f);
    s->doc = s->win + 3;

    s->ep = xmalloc(4 * s->epcap);
    s->xp = xmalloc(4 * s->xpcap);
    s->entws = xmalloc(8 * s->blocks);
    s->mks = xmalloc(sizeof(s1_masks) * s->blocks);

    s->sc_p = xcalloc(24);
    s->mk_p = xcalloc(48);
    s->entw_p = xcalloc(8);
    s->nk_p = xcalloc(8);
    s->nxp_p = xcalloc(8);
    s->xcarry_p = xcalloc(16);
    s->ep_p = xmalloc(4 * s->epcap);
    s->xp_p = xmalloc(4 * s->xpcap);
    s->dst_p = xmalloc(s->dstcap);
    s->ev_p = xmalloc(s->evcap);
    s->ndst_p = xcalloc(8);
    s->nev_p = xcalloc(8);
    s->err_p = xcalloc(8);

    s->dst_a = xmalloc(s->dstcap);
    s->ev_a = xmalloc(s->evcap);
    s->ndst_a = xcalloc(8);
    s->nev_a = xcalloc(8);
    s->err_a = xcalloc(8);

    s->passes = 8;
}

static uint64_t call_pipeline(state *s) {
    memset(s->sc_p, 0, 24);
    memset(s->mk_p, 0, 48);
    memset(s->entw_p, 0, 8);
    memset(s->xcarry_p, 0, 16);
    *s->nk_p = *s->nxp_p = *s->ndst_p = *s->nev_p = *s->err_p = 0;
    return leanllvm_json_pipeline(s->doc, s->n, s->sc_p, s->mk_p, s->entw_p,
                                  s->ep_p, s->epcap, s->nk_p, s->xp_p,
                                  s->xpcap, s->nxp_p, s->xcarry_p,
                                  s->dst_p, s->dstcap, s->ndst_p,
                                  s->ev_p, s->evcap, s->nev_p, s->err_p,
                                  ARM);
}

/* The block loop `pipeline.c` runs before the emitter, with one entry word per
   block kept for the emitter shapes to read.  `rec` records the mask struct of
   each block for the upstream gate and is NULL in a timed act. */
static void s1_prologue(state *s, s1_masks *rec, uint64_t *nxp,
                        uint64_t xcarry[2]) {
    s1_carry sc = {0, 0, 0};
    s1_masks m;
    uint64_t prevS = 0;
    *nxp = 0;
    xcarry[0] = xcarry[1] = 0;
    for (uint64_t i = 0; i < s->blocks; i++) {
        leanllvm_json_s1_masks(s->doc + (i << 6), &sc, &m);
        if (rec != NULL) rec[i] = m;
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
        uint64_t ent = m.quote | (m.delim & ~m.in_string);
        ent |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = s->n - (i << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
        s->entws[i] = ent;
        leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i, s->xp,
                                  nxp, xcarry);
    }
}

static uint64_t emit_perblock(const uint64_t *entws, uint64_t blocks,
                              uint32_t *ep) {
    uint64_t k = 0;
    for (uint64_t i = 0; i < blocks; i++)
        k = leanllvm_json_entry_pos8(&entws[i], i, 1, ep, k);
    return k;
}

static uint64_t emit_perblock_skip(const uint64_t *entws, uint64_t blocks,
                                   uint32_t *ep) {
    uint64_t k = 0;
    for (uint64_t i = 0; i < blocks; i++)
        k = eo_entry_pos8_skip(&entws[i], i, 1, ep, k);
    return k;
}

static uint64_t emit_perblock_sparse(const uint64_t *entws, uint64_t blocks,
                                     uint32_t *ep) {
    uint64_t k = 0;
    for (uint64_t i = 0; i < blocks; i++)
        k = eo_entry_sparse(&entws[i], i, 1, ep, k);
    return k;
}

/* ---------------------------------------------------------------- gates -- */
static int check_words(const char *label, const uint32_t *got, uint64_t kg,
                       const uint32_t *want, uint64_t kw) {
    if (kg != kw) {
        gate_fail("%s: cursor got=%" PRIu64 " want=%" PRIu64, label, kg, kw);
        return 0;
    }
    for (uint64_t i = 0; i < kg; i++)
        if (got[i] != want[i]) {
            gate_fail("%s: word %" PRIu64 " got=0x%08" PRIx32
                      " want=0x%08" PRIx32, label, i, got[i], want[i]);
            return 0;
        }
    return 1;
}

static int check_no_write_past(const char *label, const uint32_t *buf,
                               uint64_t k, uint64_t cap) {
    for (uint64_t i = k + 8; i < cap; i++)
        if (buf[i] != SENT_WORD) {
            gate_fail("%s: word %" PRIu64 " past k'+8 was written (0x%08" PRIx32
                      ", k'=%" PRIu64 ")", label, i, buf[i], k);
            return 0;
        }
    return 1;
}

static int check_downstream(const char *label, const uint32_t *ep, uint64_t nk,
                            const uint32_t *xp, uint64_t nxp) {
    memset(S.dst_a, 0, S.dstcap);
    memset(S.ev_a, 0, S.evcap);
    *S.ndst_a = *S.nev_a = *S.err_a = 0;
    uint64_t v = leanllvm_json_stage2(S.doc, S.n, ep, nk, xp, nxp, S.dst_a,
                                      S.dstcap, S.ndst_a, S.ev_a, S.evcap,
                                      S.nev_a, S.err_a);
    sink ^= v ^ *S.ndst_a ^ *S.nev_a ^ *S.err_a;
    if (v != S.ref_verdict) {
        gate_fail("%s: stage2 verdict got=%" PRIu64 " want=%" PRIu64, label, v,
                  S.ref_verdict);
        return 0;
    }
    if (*S.ndst_a != S.ref_ndst || *S.nev_a != S.ref_nev ||
        *S.err_a != S.ref_err) {
        gate_fail("%s: stage2 cursors got=(%" PRIu64 ",%" PRIu64 ",%" PRIu64
                  ") want=(%" PRIu64 ",%" PRIu64 ",%" PRIu64 ")", label,
                  *S.ndst_a, *S.nev_a, *S.err_a, S.ref_ndst, S.ref_nev,
                  S.ref_err);
        return 0;
    }
    if (memcmp(S.dst_a, S.dst_ref, S.ref_ndst) != 0) {
        gate_fail("%s: stage2 arena differs", label);
        return 0;
    }
    if (memcmp(S.ev_a, S.ev_ref, S.ref_nev) != 0) {
        gate_fail("%s: stage2 events differ", label);
        return 0;
    }
    return 1;
}

/* The reference observation, recorded once, and the separate stage-1 loop the
   pipeline's own streams are compared against.  The recorded counts are
   asserted only for the document they were recorded on; on any other document
   the reference is this run's own pipeline call, and the gates still compare
   every shape against it. */
static int recorded_document;

static void gate_reference_record(void) {
    uint64_t v = call_pipeline(&S);
    S.ref_verdict = v;
    S.ref_nk = *S.nk_p;
    S.ref_nxp = *S.nxp_p;
    S.ref_ndst = *S.ndst_p;
    S.ref_nev = *S.nev_p;
    S.ref_err = *S.err_p;
    printf("reference doc-size=%" PRIu64 " blocks=%" PRIu64
           " verdict=%" PRIu64 " nk=%" PRIu64 " nxp=%" PRIu64
           " ndst=%" PRIu64 " nev=%" PRIu64 " err=%" PRIu64
           " arena_fnv=%016" PRIx64 " event_fnv=%016" PRIx64 "%s\n",
           S.n, S.blocks, v, S.ref_nk, S.ref_nxp, S.ref_ndst, S.ref_nev,
           S.ref_err, fnv1a(0xcbf29ce484222325ull, S.dst_p, S.ref_ndst),
           fnv1a(0xcbf29ce484222325ull, S.ev_p, S.ref_nev),
           recorded_document ? "" : " (unrecorded document)");
    if (v != 1) gate_fail("pipeline refused the document");
    if (recorded_document) {
        if (S.n != EXPECT_SIZE)
            gate_fail("document size %" PRIu64 " is not %" PRIu64, S.n,
                      EXPECT_SIZE);
        if (S.ref_nk != EXPECT_NK || S.ref_nxp != EXPECT_NXP ||
            S.ref_ndst != EXPECT_NDST || S.ref_nev != EXPECT_NEV ||
            S.ref_err != 0)
            gate_fail("pipeline counts are not the document's recorded ones");
    }

    S.ep_ref = xmalloc(4 * S.epcap);
    S.xp_ref = xmalloc(4 * S.xpcap);
    S.dst_ref = xmalloc(S.ref_ndst ? S.ref_ndst : 1);
    S.ev_ref = xmalloc(S.ref_nev ? S.ref_nev : 1);
    memcpy(S.ep_ref, S.ep_p, 4 * S.ref_nk);
    memcpy(S.xp_ref, S.xp_p, 4 * S.ref_nxp);
    memcpy(S.dst_ref, S.dst_p, S.ref_ndst);
    memcpy(S.ev_ref, S.ev_p, S.ref_nev);

    /* The separate stage-1 loop must write the pipeline's streams, record the
       mask words, and give stage 2 the pipeline's bytes. */
    fill_sentinel(S.ep, S.epcap);
    fill_sentinel(S.xp, S.xpcap);
    uint64_t nxp = 0, xcarry[2];
    s1_prologue(&S, S.mks, &nxp, xcarry);
    uint64_t k = emit_perblock(S.entws, S.blocks, S.ep);
    int ok = check_words("stage1/perblock entry", S.ep, k, S.ep_ref, S.ref_nk);
    ok &= check_words("stage1/perblock escape", S.xp, nxp, S.xp_ref, S.ref_nxp);
    ok &= check_no_write_past("stage1/perblock", S.ep, k, S.epcap);
    ok &= check_downstream("stage1/perblock", S.ep, k, S.xp, nxp);
    printf("gate pipeline-vs-stage1 entry_stream=%s escape_list=%s stage2=%s\n",
           ok ? "identical" : "DIFFER", ok ? "identical" : "DIFFER",
           ok ? "identical" : "DIFFER");
}

/* The pipeline re-run against the recorded observation: a timed or gated pass
   that corrupted the caller's buffers shows here. */
static void gate_pipeline_again(void) {
    uint64_t v = call_pipeline(&S);
    int ok = (v == S.ref_verdict) && (*S.nk_p == S.ref_nk) &&
             (*S.nxp_p == S.ref_nxp) && (*S.ndst_p == S.ref_ndst) &&
             (*S.nev_p == S.ref_nev) && (*S.err_p == S.ref_err) &&
             memcmp(S.ep_p, S.ep_ref, 4 * S.ref_nk) == 0 &&
             memcmp(S.xp_p, S.xp_ref, 4 * S.ref_nxp) == 0 &&
             memcmp(S.dst_p, S.dst_ref, S.ref_ndst) == 0 &&
             memcmp(S.ev_p, S.ev_ref, S.ref_nev) == 0;
    if (!ok) gate_fail("the pipeline's second call differs from the reference");
    printf("gate pipeline-again %s\n", ok ? "identical" : "DIFFER");
}

/* One emitter shape over the document's precomputed words. */
static void gate_emitter(const char *label, int kind) {
    fill_sentinel(S.ep, S.epcap);
    uint64_t k;
    switch (kind) {
    case 0: k = emit_perblock(S.entws, S.blocks, S.ep); break;
    case 1: k = leanllvm_json_entry_pos8(S.entws, 0, S.blocks, S.ep, 0); break;
    case 2: k = emit_perblock_skip(S.entws, S.blocks, S.ep); break;
    case 3: k = eo_entry_pos8_skip(S.entws, 0, S.blocks, S.ep, 0); break;
    case 4: k = emit_perblock_sparse(S.entws, S.blocks, S.ep); break;
    default: k = eo_entry_sparse(S.entws, 0, S.blocks, S.ep, 0); break;
    }
    int ok = check_words(label, S.ep, k, S.ep_ref, S.ref_nk);
    ok &= check_no_write_past(label, S.ep, k, S.epcap);
    ok &= check_downstream(label, S.ep, k, S.xp_ref, S.ref_nxp);
    printf("gate %-24s stream=%s bounds=%s downstream=%s\n", label,
           ok ? "identical" : "DIFFER", ok ? "ok" : "VIOLATED",
           ok ? "identical" : "DIFFER");
}

/* The stage-1 loop's shapes: upstream masks, entry stream, escape list and
   downstream output against the reference.  The first call records the mask
   words; the later ones compare against them. */
static void gate_stage1(const char *label, int kind) {
    static s1_masks *rec;
    static int rec_done;
    if (rec == NULL) rec = xmalloc(sizeof(s1_masks) * S.blocks);
    fill_sentinel(S.ep, S.epcap);
    fill_sentinel(S.xp, S.xpcap);
    uint64_t nxp = 0, xcarry[2];
    s1_prologue(&S, rec, &nxp, xcarry);
    int masks_ok = 1;
    if (!rec_done) {
        memcpy(S.mks, rec, sizeof(s1_masks) * S.blocks);
        rec_done = 1;
    } else {
        masks_ok = memcmp(S.mks, rec, sizeof(s1_masks) * S.blocks) == 0;
        if (!masks_ok) gate_fail("%s: mask words differ from the baseline", label);
    }
    uint64_t k;
    switch (kind) {
    case 0: k = emit_perblock(S.entws, S.blocks, S.ep); break;
    case 1: k = leanllvm_json_entry_pos8(S.entws, 0, S.blocks, S.ep, 0); break;
    case 2: k = eo_entry_pos8_skip(S.entws, 0, S.blocks, S.ep, 0); break;
    default: k = eo_entry_sparse(S.entws, 0, S.blocks, S.ep, 0); break;
    }
    int ok = masks_ok;
    ok &= check_words(label, S.ep, k, S.ep_ref, S.ref_nk);
    ok &= check_words(label, S.xp, nxp, S.xp_ref, S.ref_nxp);
    ok &= check_no_write_past(label, S.ep, k, S.epcap);
    ok &= check_downstream(label, S.ep, k, S.xp, nxp);
    printf("gate %-24s masks=%s stream=%s escape=%s downstream=%s\n", label,
           masks_ok ? "identical" : "DIFFER", ok ? "identical" : "DIFFER",
           ok ? "identical" : "DIFFER", ok ? "identical" : "DIFFER");
}

/* ---------------------------------------------------------------- arms -- */
static uint64_t splitmix64(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ull);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ull;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBull;
    return z ^ (z >> 31);
}

typedef uint64_t (*kernel_fn)(const uint64_t *, uint64_t, uint64_t, uint32_t *,
                              uint64_t);

/* One stream through one kernel into `out`, whose first `cap` words are the
   sentinel; returns the cursor. */
static uint64_t run_stream(kernel_fn fn, const uint64_t *ent, uint64_t blk0,
                           uint64_t nblk, uint32_t *out, uint64_t cap) {
    fill_sentinel(out, cap);
    return fn(ent, blk0, nblk, out, 0);
}

static uint64_t arm_cases;

/* Compare the two other shapes with the installed one on one stream.  `cap` is
   the sentinel-checked capacity and must exceed the largest cursor by 8. */
static int arm_case(const char *label, const uint64_t *ent, uint64_t blk0,
                    uint64_t nblk, uint64_t cap,
                    uint32_t *want, uint32_t *got) {
    arm_cases++;
    uint64_t kw = run_stream(leanllvm_json_entry_pos8, ent, blk0, nblk, want,
                             cap);
    char what[160];
    int ok = 1;
    uint64_t kg = run_stream(eo_entry_pos8_skip, ent, blk0, nblk, got, cap);
    snprintf(what, sizeof what, "arm skip %s blk0=%" PRIu64 " nblk=%" PRIu64,
             label, blk0, nblk);
    if (!(check_words(what, got, kg, want, kw) &&
          check_no_write_past(what, got, kg, cap)))
        ok = 0;
    kg = run_stream(eo_entry_sparse, ent, blk0, nblk, got, cap);
    snprintf(what, sizeof what, "arm sparse %s blk0=%" PRIu64 " nblk=%" PRIu64,
             label, blk0, nblk);
    if (!(check_words(what, got, kg, want, kw) &&
          check_no_write_past(what, got, kg, cap)))
        ok = 0;
    sink ^= kw;
    if (arm_cases % 32768 == 0)
        printf("gate arms: %" PRIu64 " streams\n", arm_cases);
    return ok;
}

static void gate_arms(void) {
    const uint64_t small = 80;
    const uint64_t mid = 64 * 4096 + 16;
    const uint64_t big = 64 * 1025 + 16;
    uint32_t *want_small = xmalloc(4 * small), *got_small = xmalloc(4 * small);
    uint32_t *want_mid = xmalloc(4 * mid), *got_mid = xmalloc(4 * mid);
    uint32_t *want_big = xmalloc(4 * big), *got_big = xmalloc(4 * big);
    uint64_t *one = xmalloc(8);
    uint64_t *stream = xmalloc(8 * 4096);
    uint64_t *line = xmalloc(8 * 1025);
    int ok = 1;

    for (unsigned t = 0; t < 64; t++) {
        one[0] = 1ull << t;
        ok &= arm_case("single-lane", one, 0, 1, small, want_small, got_small);
        ok &= arm_case("single-lane", one, 12345, 1, small, want_small,
                       got_small);
    }
    for (unsigned x = 0; x < 256; x++) {
        one[0] = x;
        ok &= arm_case("group0-byte", one, 0, 1, small, want_small, got_small);
    }
    one[0] = 0;
    ok &= arm_case("empty", one, 0, 1, small, want_small, got_small);
    one[0] = ~(uint64_t)0;
    ok &= arm_case("full", one, 0, 1, small, want_small, got_small);

    uint64_t seed = 0x243F6A8885A308D3ull;
    for (unsigned i = 0; i < 65536; i++) {
        one[0] = splitmix64(&seed);
        ok &= arm_case("splitmix-one", one, 0, 1, small, want_small,
                       got_small);
    }

    seed = 0x243F6A8885A308D3ull;
    for (unsigned i = 0; i < 4096; i++) stream[i] = splitmix64(&seed);
    ok &= arm_case("splitmix-stream", stream, 0, 4096, mid, want_mid, got_mid);
    ok &= arm_case("splitmix-stream", stream, 7, 4096, mid, want_mid, got_mid);

    /* The 1025-word line of the document's own words, which is the row
       driver's long-loop stream. */
    for (unsigned i = 0; i < 1025; i++) line[i] = S.entws[i % S.blocks];
    ok &= arm_case("long-loop", line, 0, 1025, big, want_big, got_big);
    ok &= arm_case("long-loop", line, 12345, 1025, big, want_big, got_big);

    /* Random slices of that line, so the loop's tail and a nonzero `blk0` are
       exercised together.  The slice stays inside the line: a read past it
       would land in whatever the allocation that follows holds, and the
       output's sentinel fill would then change the input between kernels.
       The capacity is the slice's largest possible stream plus the guard a
       nonzero word may write past the cursor. */
    seed = 0x13198A2E03707344ull;
    for (unsigned c = 0; c < 1024; c++) {
        uint64_t off = splitmix64(&seed) % 1025;
        uint64_t cnt = 1 + splitmix64(&seed) % (1025 - off);
        uint64_t blk0 = splitmix64(&seed) % 100000;
        uint32_t *w = xmalloc(4 * (64 * cnt + 16));
        uint32_t *g = xmalloc(4 * (64 * cnt + 16));
        ok &= arm_case("slice", line + off, blk0, cnt, 64 * cnt + 16, w, g);
        free(w);
        free(g);
    }

    /* The document's own words, batched, at two block offsets.  The capacity is
       this document's largest possible stream plus the guard. */
    {
        uint64_t doccap = 64 * S.blocks + 16;
        uint32_t *want_doc = xmalloc(4 * doccap);
        uint32_t *got_doc = xmalloc(4 * doccap);
        ok &= arm_case("document-words", S.entws, 0, S.blocks, doccap, want_doc,
                       got_doc);
        ok &= arm_case("document-words", S.entws, 12345, S.blocks, doccap,
                       want_doc, got_doc);
        free(want_doc);
        free(got_doc);
    }

    printf("gate arms streams=%" PRIu64 " result=%s\n", arm_cases,
           ok ? "identical" : "DIFFER");
    free(want_small); free(got_small); free(want_mid); free(got_mid);
    free(want_big); free(got_big); free(one); free(stream); free(line);
}

/* --------------------------------------------------------------- report -- */
static void report_shape(void) {
    uint64_t positions = 0, nonzero = 0, empty_groups = 0, groups = 0;
    uint64_t hist_bytes[9] = {0}, hist_pc[9] = {0}, pc_more = 0, bytes_more = 0;
    for (uint64_t i = 0; i < S.blocks; i++) {
        uint64_t ent = S.entws[i];
        unsigned pc = (unsigned)__builtin_popcountll(ent);
        positions += pc;
        if (ent != 0) {
            nonzero++;
            unsigned nb = 0;
            for (unsigned b = 0; b < 8; b++)
                if ((unsigned)((ent >> (8 * b)) & 0xFFu) != 0) nb++;
            groups += 8;
            empty_groups += 8 - nb;
            if (nb <= 8) hist_bytes[nb]++; else bytes_more++;
        }
        if (pc <= 8) hist_pc[pc]++; else pc_more++;
    }
    printf("shape blocks=%" PRIu64 " positions=%" PRIu64
           " nonzero_blocks=%" PRIu64 " zero_blocks=%" PRIu64 "\n",
           S.blocks, positions, nonzero, S.blocks - nonzero);
    printf("shape group_stores_baseline=%" PRIu64
           " group_stores_needed=%" PRIu64 " empty_groups=%" PRIu64
           " (%.1f%%)\n",
           groups, groups - empty_groups, empty_groups,
           groups ? 100.0 * (double)empty_groups / (double)groups : 0.0);
    printf("shape hist_positions_per_word:");
    for (unsigned i = 0; i <= 8; i++) printf(" %u:%" PRIu64, i, hist_pc[i]);
    printf(" >8:%" PRIu64 "\n", pc_more);
    printf("shape hist_nonzero_bytes_per_word:");
    for (unsigned i = 0; i <= 8; i++) printf(" %u:%" PRIu64, i, hist_bytes[i]);
    printf(" >8:%" PRIu64 "\n", bytes_more);
}

/* ---------------------------------------------------------------- acts -- */
typedef struct { const char *name; void (*fn)(void *); } act_desc;

static void act_emitter_perblock(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= emit_perblock(s->entws, s->blocks, s->ep);
}

static void act_emitter_batch(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= leanllvm_json_entry_pos8(s->entws, 0, s->blocks, s->ep, 0);
}

static void act_emitter_perblock_skip(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= emit_perblock_skip(s->entws, s->blocks, s->ep);
}

static void act_emitter_batch_skip(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= eo_entry_pos8_skip(s->entws, 0, s->blocks, s->ep, 0);
}

static void act_emitter_perblock_sparse(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= emit_perblock_sparse(s->entws, s->blocks, s->ep);
}

static void act_emitter_batch_sparse(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++)
        sink ^= eo_entry_sparse(s->entws, 0, s->blocks, s->ep, 0);
}

static void act_s1_prologue(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t nxp = 0, carry[2];
        s1_prologue(s, NULL, &nxp, carry);
        sink ^= nxp ^ s->entws[s->blocks - 1];
    }
}

static void act_s1_perblock(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t nxp = 0, carry[2];
        s1_prologue(s, NULL, &nxp, carry);
        sink ^= emit_perblock(s->entws, s->blocks, s->ep) ^ nxp;
    }
}

static void act_s1_batch(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t nxp = 0, carry[2];
        s1_prologue(s, NULL, &nxp, carry);
        sink ^= leanllvm_json_entry_pos8(s->entws, 0, s->blocks, s->ep, 0) ^ nxp;
    }
}

static void act_s1_batch_skip(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t nxp = 0, carry[2];
        s1_prologue(s, NULL, &nxp, carry);
        sink ^= eo_entry_pos8_skip(s->entws, 0, s->blocks, s->ep, 0) ^ nxp;
    }
}

static void act_s1_batch_sparse(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t nxp = 0, carry[2];
        s1_prologue(s, NULL, &nxp, carry);
        sink ^= eo_entry_sparse(s->entws, 0, s->blocks, s->ep, 0) ^ nxp;
    }
}

static void act_pipeline(void *vp) {
    state *s = vp;
    for (uint64_t p = 0; p < s->passes; p++) {
        uint64_t v = call_pipeline(s);
        sink ^= v ^ *s->nk_p ^ *s->nxp_p ^ *s->ndst_p ^ *s->nev_p;
    }
}

/* --------------------------------------------------------------- timing -- */
static void emit_rows(const act_desc *acts, unsigned nacts, uint64_t rounds,
                      const uint64_t *chain_ns,
                      uint64_t median[MAX_ACTS][MAX_ROUNDS]) {
    printf("\nstatistic: median of the round medians, min-max of those medians;"
           " cycles use each round's chain\n");
    printf("%-26s %10s %10s %10s %12s %9s\n", "act", "median_ns", "min_ns",
           "max_ns", "median_cyc", "us");
    for (unsigned a = 0; a < nacts; a++) {
        summary s = summarise(median[a], rounds);
        uint64_t *cyc = malloc(rounds * sizeof *cyc);
        for (uint64_t r = 0; r < rounds; r++)
            cyc[r] = (median[a][r] * CHAIN_IT) / chain_ns[r];
        summary c = summarise(cyc, rounds);
        printf("%-26s %10" PRIu64 " %10" PRIu64 " %10" PRIu64 " %12" PRIu64
               " %9.3f\n", acts[a].name, s.median, s.min, s.max, c.median,
               (double)s.median / 1000.0);
        free(cyc);
    }
}

typedef struct { int64_t median, min, max; } ssummary;

static int cmp_i64(const void *a, const void *b) {
    int64_t x = *(const int64_t *)a, y = *(const int64_t *)b;
    return x < y ? -1 : x > y ? 1 : 0;
}

static ssummary summarise_signed(const int64_t *v, size_t n) {
    int64_t *t = malloc(n * sizeof *t);
    if (t == NULL) { fprintf(stderr, "entry-opt: out of memory\n"); exit(2); }
    memcpy(t, v, n * sizeof *t);
    qsort(t, n, sizeof *t, cmp_i64);
    ssummary s;
    s.median = t[(n - 1) / 2];
    s.min = s.max = v[0];
    for (size_t i = 1; i < n; i++) {
        if (v[i] < s.min) s.min = v[i];
        if (v[i] > s.max) s.max = v[i];
    }
    free(t);
    return s;
}

static void emit_delta(const act_desc *acts, unsigned nacts, uint64_t rounds,
                       const char *base_name,
                       uint64_t median[MAX_ACTS][MAX_ROUNDS]) {
    int b = -1;
    for (unsigned a = 0; a < nacts; a++)
        if (strcmp(acts[a].name, base_name) == 0) b = (int)a;
    if (b < 0) return;
    printf("\npaired deltas vs %s (ns; each round's difference of the round's"
           " act medians, then the median of the differences)\n", base_name);
    printf("%-26s %12s %12s %12s %12s\n", "act", "median", "min", "max",
           "median_us");
    for (unsigned a = 0; a < nacts; a++) {
        if ((int)a == b) continue;
        int64_t *d = malloc(rounds * sizeof *d);
        for (uint64_t r = 0; r < rounds; r++)
            d[r] = (int64_t)median[a][r] - (int64_t)median[b][r];
        ssummary s = summarise_signed(d, rounds);
        printf("%-26s %+12" PRId64 " %+12" PRId64 " %+12" PRId64
               " %+12.3f\n", acts[a].name, s.median, s.min, s.max,
               (double)s.median / 1000.0);
        free(d);
    }
}

/* ----------------------------------------------------------------- main -- */
static void usage(void) {
    fprintf(stderr, "usage: entry-opt --doc <path> [--recorded] [--rounds N]"
                    " [--reps N] [--passes N] [--gates-only]\n");
}

int main(int argc, char **argv) {
    const char *doc = NULL;
    uint64_t rounds = 15, reps = 21, passes = 8;
    int gates_only = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--doc") == 0 && i + 1 < argc) doc = argv[++i];
        else if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc)
            rounds = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--reps") == 0 && i + 1 < argc)
            reps = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--passes") == 0 && i + 1 < argc)
            passes = strtoull(argv[++i], NULL, 10);
        else if (strcmp(argv[i], "--recorded") == 0) recorded_document = 1;
        else if (strcmp(argv[i], "--gates-only") == 0) gates_only = 1;
        else { usage(); return 2; }
    }
    if (doc == NULL) { usage(); return 2; }
    if (rounds == 0 || rounds > MAX_ROUNDS || reps == 0 || reps > MAX_REPS ||
        passes == 0) {
        fprintf(stderr, "entry-opt: rounds, reps and passes out of range\n");
        return 2;
    }

    state_init(&S, doc);
    S.passes = passes;
    eo_table_init();
    printf("entry-opt doc=%s size=%" PRIu64 " blocks=%" PRIu64
           " arm=%" PRIu64 " passes=%" PRIu64 " rounds=%" PRIu64
           " reps=%" PRIu64 "\n", doc, S.n, S.blocks, ARM, passes, rounds, reps);
    if (!eo_table_check()) gate_fail("the installed POS8 table is not the rule");
    printf("gate table: %s\n",
           gate_failures ? "DIFFER" : "identical to the rule");

    gate_reference_record();
    report_shape();

    gate_emitter("emitter/perblock", 0);
    gate_emitter("emitter/batch", 1);
    gate_emitter("emitter/perblock-skip", 2);
    gate_emitter("emitter/batch-skip", 3);
    gate_emitter("emitter/perblock-sparse", 4);
    gate_emitter("emitter/batch-sparse", 5);

    gate_stage1("s1/perblock", 0);
    gate_stage1("s1/batch", 1);
    gate_stage1("s1/batch-skip", 2);
    gate_stage1("s1/batch-sparse", 3);

    gate_arms();

    if (gate_failures != 0) {
        printf("gates: %d failure(s); no measurement\n", gate_failures);
        return 3;
    }
    printf("gates: all held before the clock\n");
    if (gates_only) return 0;

    act_desc acts[] = {
        {"emitter/perblock", act_emitter_perblock},
        {"emitter/batch", act_emitter_batch},
        {"emitter/perblock-skip", act_emitter_perblock_skip},
        {"emitter/batch-skip", act_emitter_batch_skip},
        {"emitter/perblock-sparse", act_emitter_perblock_sparse},
        {"emitter/batch-sparse", act_emitter_batch_sparse},
        {"s1/prologue", act_s1_prologue},
        {"s1/perblock", act_s1_perblock},
        {"s1/batch", act_s1_batch},
        {"s1/batch-skip", act_s1_batch_skip},
        {"s1/batch-sparse", act_s1_batch_sparse},
        {"pipeline", act_pipeline},
    };
    unsigned nacts = sizeof acts / sizeof acts[0];

    static uint64_t median[MAX_ACTS][MAX_ROUNDS];
    static uint64_t samples[MAX_ACTS][MAX_REPS];
    static uint64_t chain_ns[MAX_ROUNDS];
    for (uint64_t r = 0; r < rounds; r++) {
        uint64_t c0 = now_ns();
        uint64_t cv = clock_chain(CHAIN_IT);
        uint64_t c1 = now_ns();
        sink ^= cv;
        chain_ns[r] = c1 - c0;
        for (uint64_t rep = 0; rep < reps; rep++) {
            for (unsigned j = 0; j < nacts; j++) {
                unsigned idx = (unsigned)((r + rep * 7 + j) % nacts);
                uint64_t t0 = now_ns();
                acts[idx].fn(&S);
                uint64_t t1 = now_ns();
                samples[idx][rep] = (t1 - t0) / passes;
            }
        }
        for (unsigned a = 0; a < nacts; a++)
            median[a][r] = median_of(samples[a], reps);
    }

    uint64_t chain_med = median_of(chain_ns, rounds);
    printf("\nclock: chain=%" PRIu64 " ns / %" PRIu64 " iterations -> %.3f GHz"
           " (per-round range %.3f-%.3f GHz)\n", chain_med, CHAIN_IT,
           (double)CHAIN_IT / (double)chain_med,
           (double)CHAIN_IT / (double)summarise(chain_ns, rounds).max,
           (double)CHAIN_IT / (double)summarise(chain_ns, rounds).min);
    printf("context: the emitter rows are over the document's precomputed words;"
           " the stage-1 rows include the mask unit, the entry word and the"
           " escape list\n");
    emit_rows(acts, nacts, rounds, chain_ns, median);
    emit_delta(acts, nacts, rounds, "emitter/perblock", median);
    emit_delta(acts, nacts, rounds, "emitter/batch", median);
    emit_delta(acts, nacts, rounds, "s1/prologue", median);
    emit_delta(acts, nacts, rounds, "s1/perblock", median);
    emit_delta(acts, nacts, rounds, "s1/batch", median);

    gate_pipeline_again();
    gate_emitter("emitter/perblock", 0);
    gate_emitter("emitter/batch", 1);
    gate_emitter("emitter/perblock-skip", 2);
    gate_emitter("emitter/batch-skip", 3);
    gate_emitter("emitter/perblock-sparse", 4);
    gate_emitter("emitter/batch-sparse", 5);
    gate_stage1("s1/perblock", 0);
    gate_stage1("s1/batch", 1);
    gate_stage1("s1/batch-skip", 2);
    gate_stage1("s1/batch-sparse", 3);
    gate_arms();
    if (gate_failures != 0) {
        printf("gates after the clock: %d failure(s)\n", gate_failures);
        return 3;
    }
    printf("gates: all held after the clock\n");
    return 0;
}
