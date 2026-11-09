/* paired-pipeline.c -- Arm C: the assembled pipeline, staged against the same
   source compiled as one translation unit, in one binary.

   `paired.sh --unit pipeline` compiles two sides into this binary:

       kernel/json/pipeline.c and the five units
                                     the staged form.  `pipeline.c` is its own
                                     translation unit and each unit is its own,
                                     every call crossing the external ABI the
                                     unit's header declares.  This is the form
                                     the model's records are stated at: the
                                     block loop is the caller, and each unit
                                     boundary is a call site `pipelineCalls`
                                     resolves.  Its pipeline symbol is
                                     `probe_pipeline_staged`.
       the same six files            the one-TU form.  The same text compiled
       in one translation unit       as one translation unit, which is the
                                     form the recorded ratios were measured
                                     on; its pipeline symbol is
                                     `probe_pipeline_inlined`.  The compiler
                                     decides what it inlines, and `paired.sh`
                                     prints the call census each form keeps,
                                     so the difference the report measures is
                                     the one the compiler left, not one this
                                     comment claims.

   Both sides are the same source at the measured compiler line, so the
   difference the report measures is the staging cost and not a re-spelling of
   the body.  The staged form is the model's; the one-TU form is the measured
   form; the ratio is what says whether the staging was worth it.

   ## The entry table is the caller's

   `pipeline.c` does not initialise `xl_pos8`, the entry unit's table: the
   pos8 emitter reads it, and a run whose table is not built returns an empty
   entry stream and refuses every document at offset 0.  Each side's table is
   file-static inside its own translation unit, so each side has one, and the
   caller fills both here: the constructor below calls
   `leanllvm_json_entry_table` for the staged side and `probe_inl_entry_table`
   for the one-TU side, once, before the first pipeline call and outside every
   timed region.  That is the idiom `bench/paired-entry.c:79` uses and the
   precondition `pipeline.h` states.  The two 8 KiB copies are compared before
   the clock starts: they are the same table and a difference means one side's
   initialiser did not run.

   ## One act

   One act is one call to the pipeline over one document with every cursor at
   zero and the caller's buffers staged as `pipeline.h` describes: the document
   padded to its 64-byte block boundary with zero bytes and the three bytes
   before it zero, the entry stream's and the escape list's capacity, and the
   arena's and the event stream's.  `arm` is zero: the POS8 emitter, no escape
   list, the gated UTF-8 path -- the decision the measured table takes for a
   plain document (POS8 on both core classes, the list off, gated), and the
   caller's selector rather than a classifier.  Every report row prints it.

   ## Before the clock

   Both sides run every document once and must agree exactly on the verdict,
   the first error offset, the entry count, the escape count, the arena and
   event extents, and the bytes of all four buffers.  A difference is a setup
   fault (exit 3), not a timing.  Every document is valid JSON, so every
   verdict must be 1: a refusal at offset 0 is the signature of an entry table
   the caller did not initialise, and it is reported as that.

   The inputs are `probes/bench/json/`'s documents, passed by the shell.  A
   document shorter than one full block would divide the fixed per-document
   term by its block count, so it is reported as an observation with no delta
   claim, the way the escape arm reports its one-block input.

   ## The report

   The harness calls the two sides `first` (`probe_pipeline_staged`) and
   `second` (`probe_pipeline_inlined`).  The shell renames which build fills
   each role for each pair -- baseline, decision, reach and the arrangement
   control -- and passes the pair's labels, so a row says which two builds its
   columns are.  The difference is **`d = first - second` ns/block**: `d > 0`
   means the first side is slower.  Each row prints both columns, the
   difference and its direction, and the state word is derived from the same
   `d`, so a verdict can be checked against its own arithmetic.  A self-check
   fails the arm if a row's verdict or direction disagrees with its printed
   columns: a FAIL whose first column is not the larger is the class, and it
   is reported as a harness fault (exit 3), never printed as a verdict.

   Each round runs both sides twice, once in each order, and averages each
   side, so a drift inside the round lands on both and cancels in the
   difference.  The report is the median of `d` ns/block over the rounds, with
   a distribution-free 95% interval for the median from the order statistics,
   the mean with its normal-approximation interval, the per-round standard
   deviation and the one-sided rolling-window rate at the record's
   fifteen-round window.  The claim is one-sided: `d <= +0.5` ns/block, so the
   first side may not be slower than the second by more than 0.5 ns/block.  A
   row with fewer than 301 rounds is an observation and carries no claim; the
   shell's default for this unit is 301.

   `--self-control` runs the one-TU side against itself and requires exactly
   0.0, which checks the harness's dispatch and subtraction rather than the
   clock. */
#define _GNU_SOURCE
#include <sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t (*pipeline_fn)(const uint8_t *, uint64_t, uint64_t *,
                                uint64_t *, uint64_t *, uint32_t *, uint64_t,
                                uint64_t *, uint32_t *, uint64_t, uint64_t *,
                                uint64_t *, uint8_t *, uint64_t, uint64_t *,
                                uint8_t *, uint64_t, uint64_t *, uint64_t *,
                                uint64_t);

uint64_t probe_pipeline_staged(const uint8_t *, uint64_t, uint64_t *,
                               uint64_t *, uint64_t *, uint32_t *, uint64_t,
                               uint64_t *, uint32_t *, uint64_t, uint64_t *,
                               uint64_t *, uint8_t *, uint64_t, uint64_t *,
                               uint8_t *, uint64_t, uint64_t *, uint64_t *,
                               uint64_t);
uint64_t probe_pipeline_inlined(const uint8_t *, uint64_t, uint64_t *,
                                uint64_t *, uint64_t *, uint32_t *, uint64_t,
                                uint64_t *, uint32_t *, uint64_t, uint64_t *,
                                uint64_t *, uint8_t *, uint64_t, uint64_t *,
                                uint8_t *, uint64_t, uint64_t *, uint64_t *,
                                uint64_t);
void leanllvm_json_entry_table(uint32_t *);
void probe_inl_entry_table(uint32_t *);

/* Bytes of document work per timed act.  The smallest pass keeps a round's
   four acts in the tens of milliseconds, where a scheduler quantum or a
   frequency step is not a large fraction of the act. */
#define ACT_BYTES ((size_t)1 << 23)

/* The pipeline's own arms: POS8 emitter, no escape list, gated UTF-8. */
#define ARM ((uint64_t)0)

/* The record's round count for a claim, and the one-sided bound. */
#define CLAIM_ROUNDS 301
#define BOUND 0.5
#define ROLL_WINDOW 15

static uint32_t table_staged[2048];
static uint32_t table_inlined[2048];

/* The caller's staging of the entry table, once per side, before the first
   call.  `pipeline.h` states the precondition; this constructor meets it. */
__attribute__((constructor)) static void pipeline_arm_init(void) {
    leanllvm_json_entry_table(table_staged);
    probe_inl_entry_table(table_inlined);
}

typedef struct {
    char name[256];
    uint8_t *buf;          /* the document, three zero bytes before `doc` */
    const uint8_t *doc;
    uint64_t n;
    uint64_t nb;
    uint32_t *ep;
    uint32_t *xp;
    uint8_t *dst;
    uint8_t *ev;
    uint64_t epcap, xpcap, dstcap, evcap;
} input;

typedef struct {
    uint64_t verdict, err, nk, nxp, ndst, nev;
    uint64_t ep_h, xp_h, dst_h, ev_h;
} result;

static volatile uint64_t sink;

static double now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

static unsigned core_class(void) {
    unsigned eax, ebx, ecx, edx;
    __asm__ volatile("cpuid" : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
                     : "a"(0x1AU), "c"(0U));
    return (eax >> 24) & 0xFF;
}

static int cmp_double(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "paired-pipeline: out of memory\n");
        exit(2);
    }
    return p;
}

static uint8_t *aligned_bytes(size_t n) {
    void *p = NULL;
    if (posix_memalign(&p, 4096, n ? n : 1) != 0 || !p) {
        fprintf(stderr, "paired-pipeline: cannot allocate %zu bytes\n", n);
        exit(2);
    }
    memset(p, 0, n);
    return p;
}

static uint64_t fnv(const void *p, size_t n) {
    const uint8_t *q = (const uint8_t *)p;
    uint64_t h = 1469598103934665603ULL;
    for (size_t i = 0; i < n; i++) {
        h ^= q[i];
        h *= 1099511628211ULL;
    }
    return h;
}

/* add_document -- read one file and stage it as the units' `pre` requires:
   `b-3 .. b-1` zero, `b .. b+n-1` the document, and every byte of the last
   block past the document's end zero.  The capacities follow the units'
   stated obligations: the entry stream and the escape list can each take one
   position per document byte plus the emitters' slack, the arena one decoded
   byte per document byte plus the decoder's 64-byte slack per escaped body,
   and the event stream the measured encoding's widest record per entry. */
static int add_document(input *in, const char *path) {
    FILE *f = fopen(path, "rb");
    long m;
    uint64_t nb, blocks;
    size_t docbytes;

    if (!f) {
        fprintf(stderr, "SETUP: cannot read %s\n", path);
        return 3;
    }
    if (fseek(f, 0, SEEK_END) != 0 || (m = ftell(f)) < 0 ||
        fseek(f, 0, SEEK_SET) != 0) {
        fprintf(stderr, "SETUP: cannot size %s\n", path);
        fclose(f);
        return 3;
    }
    in->n = (uint64_t)m;
    nb = (in->n + 63) / 64;
    blocks = nb ? nb : 1;
    docbytes = (size_t)(blocks * 64) + 128;
    in->buf = aligned_bytes(docbytes);
    in->doc = in->buf + 64;
    if (fread((void *)in->doc, 1, in->n, f) != in->n) {
        fprintf(stderr, "SETUP: cannot read %s\n", path);
        fclose(f);
        return 3;
    }
    fclose(f);
    in->nb = nb;

    in->epcap = in->n + 8 * blocks + 64;
    in->xpcap = in->n + 8 * blocks + 64;
    in->dstcap = 68 * in->n + 65536;
    in->evcap = 24 * in->n + 65536;
    in->ep = xmalloc((size_t)in->epcap * sizeof *in->ep);
    in->xp = xmalloc((size_t)in->xpcap * sizeof *in->xp);
    in->dst = xmalloc((size_t)in->dstcap);
    in->ev = xmalloc((size_t)in->evcap);

    {
        const char *slash = strrchr(path, '/');
        const char *base = slash ? slash + 1 : path;
        size_t k = strlen(base);
        if (k >= sizeof in->name) k = sizeof in->name - 1;
        memcpy(in->name, base, k);
        in->name[k] = 0;
    }
    return 0;
}

/* run_pipeline -- one act's work, without timing it. */
static void run_pipeline(pipeline_fn f, input *in, result *r) {
    uint64_t sc[3] = {0, 0, 0};
    uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
    uint64_t ndst = 0, nev = 0, err = 0;

    memset(in->ep, 0, (size_t)in->epcap * sizeof *in->ep);
    memset(in->xp, 0, (size_t)in->xpcap * sizeof *in->xp);
    memset(in->dst, 0, (size_t)in->dstcap);
    memset(in->ev, 0, (size_t)in->evcap);
    r->verdict = f(in->doc, in->n, sc, mk, &entw, in->ep, in->epcap, &nk,
                   in->xp, in->xpcap, &nxp, xcarry, in->dst, in->dstcap,
                   &ndst, in->ev, in->evcap, &nev, &err, ARM);
    r->err = err;
    r->nk = nk;
    r->nxp = nxp;
    r->ndst = ndst;
    r->nev = nev;
    r->ep_h = fnv(in->ep, (size_t)nk * sizeof *in->ep);
    r->xp_h = fnv(in->xp, (size_t)nxp * sizeof *in->xp);
    r->dst_h = fnv(in->dst, (size_t)ndst);
    r->ev_h = fnv(in->ev, (size_t)nev);
}

static int same(const result *a, const result *b) {
    return a->verdict == b->verdict && a->err == b->err && a->nk == b->nk &&
           a->nxp == b->nxp && a->ndst == b->ndst && a->nev == b->nev &&
           a->ep_h == b->ep_h && a->xp_h == b->xp_h && a->dst_h == b->dst_h &&
           a->ev_h == b->ev_h;
}

/* run_act -- one timed act: `reps` pipeline calls, each with the caller's
   cursors reset, divided by the document's block count. */
static double run_act(pipeline_fn f, input *in) {
    size_t bytes = (size_t)(in->nb ? in->nb : 1) * 64;
    size_t reps = ACT_BYTES / bytes;
    double t0, t1;
    uint64_t acc = 0;

    if (reps < 1) reps = 1;
    t0 = now_ns();
    for (size_t i = 0; i < reps; i++) {
        uint64_t sc[3] = {0, 0, 0};
        uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
        uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
        uint64_t ndst = 0, nev = 0, err = 0;
        acc ^= f(in->doc, in->n, sc, mk, &entw, (uint32_t *)in->ep, in->epcap,
                 &nk, (uint32_t *)in->xp, in->xpcap, &nxp, xcarry,
                 (uint8_t *)in->dst, in->dstcap, &ndst, (uint8_t *)in->ev,
                 in->evcap, &nev, &err, ARM);
        acc ^= nk ^ nxp ^ ndst ^ nev ^ err;
    }
    t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)(reps * (in->nb ? in->nb : 1));
}

static double median_of(double *v, int n) {
    qsort(v, (size_t)n, sizeof *v, cmp_double);
    return (n % 2) ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

/* dsqrt -- the square root without libm, Newton from a power-of-two guess:
   the harness links with clang's default libraries only. */
static double dsqrt(double x) {
    double g;
    union { double d; uint64_t u; } v;
    if (x <= 0.0) return 0.0;
    v.d = x;
    v.u = (v.u >> 1) + 0x1FF8000000000000ULL;  /* an exponent-half guess */
    g = v.d;
    for (int i = 0; i < 6; i++) g = 0.5 * (g + x / g);
    return g;
}

/* binom_cdf -- P(X <= k) for X ~ Bin(n, 1/2).  The weights are computed
   relative to the mode, where the binomial's maximum is, so no partial sum or
   factor overflows: w[mode] = 1 and each neighbour follows from w's ratio. */
static double binom_cdf(int n, int k) {
    int mode = n / 2;
    long double *w, total = 0.0L, upto = 0.0L;
    if (k < 0) return 0.0;
    if (k >= n) return 1.0;
    w = xmalloc((size_t)(n + 1) * sizeof *w);
    w[mode] = 1.0L;
    for (int i = mode; i > 0; i--)
        w[i - 1] = w[i] * (long double)i / (long double)(n - i + 1);
    for (int i = mode; i < n; i++)
        w[i + 1] = w[i] * (long double)(n - i) / (long double)(i + 1);
    for (int i = 0; i <= n; i++) {
        total += w[i];
        if (i <= k) upto += w[i];
    }
    free(w);
    return (double)(upto / total);
}

/* median_interval -- the distribution-free 95% interval for the median from
   the order statistics: [x[r-1], x[n-r]] for the largest r with
   P(X <= r-1) <= 0.025.  For a sample too small to give a 95% interval the
   interval is the full range, which is the honest report rather than a
   narrower one the sample does not support. */
static void median_interval(const double *x, int n, int *k_out, double *lo,
                            double *hi) {
    int r = n;
    while (r > 1 && binom_cdf(n, r - 1) > 0.025) r--;
    *k_out = r;
    if (r == 1) {
        *lo = x[0];
        *hi = x[n - 1];
    } else {
        *lo = x[r - 1];
        *hi = x[n - r];
    }
}

/* rolling_rate -- how many of the record's fifteen-round windows have a
   median above the bound, one-sided. */
static int rolling_rate(const double *d, int n, int *windows) {
    double w[ROLL_WINDOW];
    int bad = 0;
    *windows = 0;
    if (n < ROLL_WINDOW) return 0;
    for (int i = 0; i + ROLL_WINDOW <= n; i++) {
        double m;
        memcpy(w, d + i, sizeof w);
        m = median_of(w, ROLL_WINDOW);
        if (m > BOUND) bad++;
        (*windows)++;
    }
    return bad;
}

static void usage(void) {
    fprintf(stderr,
            "usage: paired-pipeline --document <file> [--document <file>...] "
            "[--rounds N] [--build <id>] [--pair <name>] "
            "[--first-label <label>] [--second-label <label>] [--arms] "
            "[--self-control]\n");
}

int main(int argc, char **argv) {
    int rounds = CLAIM_ROUNDS, self_control = 0, arms = 0;
    const char *build = "unstated", *pair = "pair";
    const char *first_label = "first", *second_label = "second";
    input inputs[64];
    size_t ninputs = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--document") == 0 && i + 1 < argc) {
            int st;
            if (ninputs >= sizeof inputs / sizeof inputs[0]) {
                fprintf(stderr, "paired-pipeline: too many documents\n");
                return 2;
            }
            st = add_document(&inputs[ninputs], argv[++i]);
            if (st) return st;
            ninputs++;
        } else if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc) {
            rounds = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--build") == 0 && i + 1 < argc) {
            build = argv[++i];
        } else if (strcmp(argv[i], "--pair") == 0 && i + 1 < argc) {
            pair = argv[++i];
        } else if (strcmp(argv[i], "--first-label") == 0 && i + 1 < argc) {
            first_label = argv[++i];
        } else if (strcmp(argv[i], "--second-label") == 0 && i + 1 < argc) {
            second_label = argv[++i];
        } else if (strcmp(argv[i], "--arms") == 0) {
            arms = 1;
        } else if (strcmp(argv[i], "--self-control") == 0) {
            self_control = 1;
        } else {
            usage();
            return 2;
        }
    }
    if (rounds < 3) {
        fprintf(stderr, "paired-pipeline: --rounds needs at least 3\n");
        return 2;
    }
    if (ninputs == 0) {
        usage();
        return 2;
    }
    (void)arms; /* the shell passes the documents; they are the arm set */

    /* The caller's staging, asserted before the clock: both tables were
       filled, and they are the same table. */
    if (memcmp(table_staged, table_inlined, sizeof table_staged) != 0) {
        fprintf(stderr, "SETUP: the two sides' entry tables differ; one "
                        "initialiser did not run\n");
        return 3;
    }
    {
        uint64_t sum = 0;
        for (size_t i = 0; i < 2048; i++) sum += table_staged[i];
        if (sum == 0) {
            fprintf(stderr, "SETUP: the entry table is all zero; the caller "
                            "did not fill it\n");
            return 3;
        }
    }

    /* The two sides must be the same program's output before either is timed. */
    for (size_t k = 0; k < ninputs; k++) {
        result a, b;
        run_pipeline(probe_pipeline_staged, &inputs[k], &a);
        run_pipeline(probe_pipeline_inlined, &inputs[k], &b);
        if (!same(&a, &b)) {
            fprintf(stderr,
                    "SETUP: %s: the staged and one-TU sides disagree "
                    "(verdict %llu/%llu, err %llu/%llu, entries %llu/%llu)\n",
                    inputs[k].name, (unsigned long long)a.verdict,
                    (unsigned long long)b.verdict, (unsigned long long)a.err,
                    (unsigned long long)b.err, (unsigned long long)a.nk,
                    (unsigned long long)b.nk);
            return 3;
        }
        if (a.verdict != 1 || a.err != 0) {
            fprintf(stderr,
                    "SETUP: %s: the pipeline refused a valid document at "
                    "offset %llu; a refusal at offset 0 is an entry table the "
                    "caller did not initialise before the first call\n",
                    inputs[k].name, (unsigned long long)a.err);
            return 3;
        }
        if (inputs[k].n > 0 && a.nk == 0) {
            fprintf(stderr, "SETUP: %s: the entry stream is empty\n",
                    inputs[k].name);
            return 3;
        }
    }

    /* One discarded pass over every input and both sides, so the first timed
       round is not the one that warms the buffers and the core's frequency. */
    for (int pass = 0; pass < 2; pass++) {
        for (size_t k = 0; k < ninputs; k++) {
            run_act(probe_pipeline_staged, &inputs[k]);
            run_act(probe_pipeline_inlined, &inputs[k]);
        }
    }

    printf("# paired timing: the two sides of one pair, one act per document\n");
    printf("# ns/block: one block is 64 document bytes\n");
    printf("# d = first - second; d > 0 means the first side is slower.  The claim is one-sided: d <= +%.1f\n",
           BOUND);
    printf("# one act is one pipeline call over one document, every cursor at zero\n");
    printf("# the staged form is the model's; the one-TU form is the measured form\n");
    printf("# arm %llu (POS8 emitter, no escape list, gated UTF-8)\n",
           (unsigned long long)ARM);
    printf("# the entry table was filled by the caller: leanllvm_json_entry_table and probe_inl_entry_table, 2 x 8 KiB, before the first call\n");
    printf("pair %s\n", pair);
    printf("first %s\n", first_label);
    printf("second %s\n", second_label);
    printf("build %s\n", build);
    printf("core-class %u\n", core_class());
    printf("sched-cpu %d\n", sched_getcpu());
    printf("rounds %d\n", rounds);
    printf("self-control %s\n", self_control ? "yes" : "no");

    int failed = 0, selfcheck = 0;
    for (size_t k = 0; k < ninputs; k++) {
        pipeline_fn fa = probe_pipeline_staged;
        pipeline_fn fb = self_control ? fa : probe_pipeline_inlined;
        double *d = xmalloc((size_t)rounds * sizeof *d);
        double *av = xmalloc((size_t)rounds * sizeof *av);
        double *bv = xmalloc((size_t)rounds * sizeof *bv);
        int cpu = sched_getcpu(), cl = (int)core_class();
        double med, sd = 0.0, mean = 0.0;
        double lo, hi, mean_lo, mean_hi;
        int kk = 0, windows = 0, bad;
        const char *state;
        int bounded = inputs[k].nb >= 1 && inputs[k].nb * 64 >= 4096 &&
                      rounds >= CLAIM_ROUNDS;

        for (int r = 0; r < rounds; r++) {
            double x, y;
            if (fa == fb) {
                x = run_act(fa, &inputs[k]);
                y = x;
            } else {
                double a1, a2, b1, b2;
                if ((r & 1) == 0) {
                    a1 = run_act(fa, &inputs[k]);
                    b1 = run_act(fb, &inputs[k]);
                    b2 = run_act(fb, &inputs[k]);
                    a2 = run_act(fa, &inputs[k]);
                } else {
                    b1 = run_act(fb, &inputs[k]);
                    a1 = run_act(fa, &inputs[k]);
                    a2 = run_act(fa, &inputs[k]);
                    b2 = run_act(fb, &inputs[k]);
                }
                x = 0.5 * (a1 + a2);
                y = 0.5 * (b1 + b2);
            }
            av[r] = x;
            bv[r] = y;
            d[r] = x - y;   /* first - second: d > 0 means the first side is slower */
        }

        {
            double ma = median_of(av, rounds);
            double mb = median_of(bv, rounds);
            double *sorted = xmalloc((size_t)rounds * sizeof *sorted);
            /* The rolling rate needs the rounds in their run order, so it is
               taken before `d` is sorted for the median. */
            bad = rolling_rate(d, rounds, &windows);
            memcpy(sorted, d, (size_t)rounds * sizeof *sorted);
            qsort(sorted, (size_t)rounds, sizeof *sorted, cmp_double);
            med = median_of(d, rounds);
            median_interval(sorted, rounds, &kk, &lo, &hi);
            for (int r = 0; r < rounds; r++) mean += d[r];
            mean /= rounds;
            for (int r = 0; r < rounds; r++) {
                double e = d[r] - mean;
                sd += e * e;
            }
            sd = rounds > 1 ? sd / (rounds - 1) : 0.0;
            sd = dsqrt(sd);
            mean_lo = mean - 1.96 * sd / dsqrt((double)rounds);
            mean_hi = mean + 1.96 * sd / dsqrt((double)rounds);

            {
                int resolvable = (lo > 0.0) || (hi < 0.0);
                int claim_fail = 0;
                const char *direction =
                    med > 0.0 ? "first slower"
                    : med < 0.0 ? "first faster" : "equal";

                if (self_control) {
                    state = med == 0.0 ? "self-control exact"
                                       : "self-control FAIL";
                    if (med != 0.0) {
                        fprintf(stderr,
                                "FAIL: self-control reported %.6f, not 0.0\n",
                                med);
                        failed = 1;
                    }
                } else if (!bounded) {
                    state = "observation: no delta claim (rounds < 301 or "
                            "document under one block)";
                } else if (med > BOUND) {
                    state = "FAIL: the first side is slower by more than "
                            "+0.5 ns/block";
                    claim_fail = 1;
                    failed = 1;
                } else {
                    state = "within +0.5 ns/block (one-sided)";
                }

                /* The verdict must agree with the columns it prints.  A FAIL
                   whose first column is not the larger is the class this
                   check exists for: it is a harness fault (exit 3), never a
                   verdict. */
                if (!self_control && med != 0.0) {
                    if (claim_fail && !(ma > mb)) {
                        fprintf(stderr,
                                "SELF-CHECK: %s: d = %+.3f says the first side "
                                "is slower, but first(%s) = %.3f is not above "
                                "second(%s) = %.3f\n",
                                inputs[k].name, med, first_label, ma,
                                second_label, mb);
                        selfcheck = 1;
                    }
                    if (resolvable && ((med > 0.0) != (ma > mb))) {
                        fprintf(stderr,
                                "SELF-CHECK: %s: the direction and the columns "
                                "disagree (d = %+.3f, first = %.3f, "
                                "second = %.3f)\n",
                                inputs[k].name, med, ma, mb);
                        selfcheck = 1;
                    }
                }

                printf("%-20s pair %-9s cpu %d class %d first(%s) %9.3f "
                       "second(%s) %9.3f blocks %llu rounds %d build %s\n",
                       inputs[k].name, pair, cpu, cl, first_label, ma,
                       second_label, mb, (unsigned long long)inputs[k].nb,
                       rounds, build);
                printf("%-20s difference first-second %+8.3f ns/block "
                       "ci95 [%8.3f %8.3f] rank %d/%d mean %+8.3f "
                       "mean95 [%8.3f %8.3f] sd %8.3f roll%d %d/%d "
                       "direction %s resolvable %s %s\n",
                       inputs[k].name, med, lo, hi, kk, rounds, mean, mean_lo,
                       mean_hi, sd, ROLL_WINDOW, bad, windows, direction,
                       resolvable ? "yes" : "no", state);
            }
            free(sorted);
        }
        free(d);
        free(av);
        free(bv);
    }
    if (selfcheck) {
        fprintf(stderr,
                "FAIL: the harness's verdict and its columns disagreed; the "
                "arm reports no verdict from this run\n");
        return 3;
    }
    if (self_control && !failed) {
        printf("ok: the harness reports 0.0 against itself\n");
    } else if (!failed) {
        printf("ok: every claimed row is within the one-sided +0.5 ns/block "
               "bound (d = first - second)\n");
    }
    return failed ? 1 : 0;
}
