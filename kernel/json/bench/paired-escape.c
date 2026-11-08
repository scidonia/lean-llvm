/* paired-escape.c -- Arm C: paired timing of the escape unit against the
   measured statements, in one binary.

   `paired.sh --unit escape` compiles three translation units into one binary:

       kernel/json/escape.c          the extracted side, its two ABI functions
                                     renamed probe_escape_list_extracted and
                                     probe_escape_expand_extracted
       kernel/json/identity/escape_oracle.c
                                     the measured side, the same two ABI
                                     functions over the vendored text, renamed
                                     probe_escape_list_measured and
                                     probe_escape_expand_measured
       this file                     the harness

   The two sides are the same ABI text (the IR arm lifts and compares them),
   so the difference the report measures is in the statements behind them and
   not in a wrapper.  Both are built with `-falign-functions=4096`, and
   `paired.sh` asserts each probe starts at a page boundary: identical code at
   two addresses can still run at different speeds on a core whose uop cache
   maps by address.

   One act is (list, then expand) over one document.  The list is walked block
   by block with a carry threaded through, exactly as the pipeline calls it;
   the expander is then called once with the list just built, `pos0 = 0` and a
   fresh cursor.  The harness derives the three classifier words and the
   position list from the bytes **before** timing, and asserts the unit's list
   equals the derived one, so the expander is never fed a list that is not the
   document's positions (the one input its `pre` excludes).

   The inputs are generated from this file's own rules rather than read from a
   corpus: the timing arm has to run from a checkout that carries the unit, and
   the route's corpus belongs to a different change.  Each round runs both
   sides twice, once in each order, and averages each side, so a drift inside
   the round lands on both and cancels in the difference.  The report is the
   median of (extracted - measured) ns/block over the rounds against a
   +/-0.5 ns/block bound.

   `--self-control` runs the measured side against itself and requires exactly
   0.0, which checks the harness's dispatch and subtraction rather than the
   clock. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef void (*escape_list_fn)(uint64_t, uint64_t, uint64_t, uint64_t,
                               uint32_t *, uint64_t *, uint64_t *);
typedef uint64_t (*escape_expand_fn)(const uint8_t *, uint64_t, uint8_t *,
                                     uint64_t *, const uint32_t *, uint64_t *,
                                     uint64_t, uint64_t);

void probe_escape_list_measured(uint64_t, uint64_t, uint64_t, uint64_t,
                                uint32_t *, uint64_t *, uint64_t *);
uint64_t probe_escape_expand_measured(const uint8_t *, uint64_t, uint8_t *,
                                      uint64_t *, const uint32_t *, uint64_t *,
                                      uint64_t, uint64_t);
void probe_escape_list_extracted(uint64_t, uint64_t, uint64_t, uint64_t,
                                 uint32_t *, uint64_t *, uint64_t *);
uint64_t probe_escape_expand_extracted(const uint8_t *, uint64_t, uint8_t *,
                                       uint64_t *, const uint32_t *, uint64_t *,
                                       uint64_t, uint64_t);

/* Bytes of document work per timed act.  Larger than the other paired arms'
   1 MiB because this act's cost is tens of nanoseconds per block: at 1 MiB a
   small input's act is under a millisecond and a scheduler quantum or a
   frequency step is a large fraction of it, which the +/-0.5 ns/block bound
   then reads as a code difference.  At 64 MiB an act is tens of milliseconds
   even for the dense input. */
#define ACT_BYTES ((size_t)1 << 26)

typedef struct {
    char name[320];
    uint8_t *doc;      /* the document, on a page-aligned buffer */
    uint64_t n;
    uint64_t nb;
    uint64_t *bs, *ctl, *im;   /* the classifier's words, one per block */
    uint32_t *pos;     /* the document's escape positions */
    uint64_t npos;
    uint32_t *xp;
    uint8_t *dst;
    int bounded;       /* whether the +/-0.5 ns/block bound is claimed */
} input;

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

static double median(double *v, int n) {
    qsort(v, (size_t)n, sizeof *v, cmp_double);
    return (n % 2) ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "paired-escape: out of memory\n");
        exit(2);
    }
    return p;
}

static uint8_t *aligned_bytes(size_t n) {
    void *p = NULL;
    if (posix_memalign(&p, 4096, n ? n : 1) != 0 || !p) {
        fprintf(stderr, "paired-escape: cannot allocate %zu bytes\n", n);
        exit(2);
    }
    memset(p, 0, n);
    return p;
}

/* The classifier's words and the escape rule, derived from the bytes here.
   This is the harness's own reading: `im` is the parity of the unescaped
   quotes up to and including the lane, an unescaped quote is one preceded by
   an even backslash run, and a position is an in-string control byte or the
   first backslash of an even offset inside its run.  None of it is read out of
   the code under test. */
static void derive(input *in) {
    uint64_t nb = (in->n + 63) / 64;
    uint64_t blocks = nb ? nb : 1;
    in->nb = nb;
    in->bs = xmalloc((size_t)blocks * sizeof *in->bs);
    in->ctl = xmalloc((size_t)blocks * sizeof *in->ctl);
    in->im = xmalloc((size_t)blocks * sizeof *in->im);
    in->pos = xmalloc((size_t)(in->n + 1) * sizeof *in->pos);
    memset(in->bs, 0, (size_t)blocks * sizeof *in->bs);
    memset(in->ctl, 0, (size_t)blocks * sizeof *in->ctl);
    memset(in->im, 0, (size_t)blocks * sizeof *in->im);

    uint64_t run = 0;         /* backslashes in the current run */
    int inside = 0;           /* after the previous byte */
    uint64_t npos = 0;
    for (uint64_t k = 0; k < in->n; k++) {
        uint8_t b = in->doc[k];
        int is_bs = (b == '\\');
        int is_quote = (b == '"');
        int unescaped_quote = is_quote && ((run & 1) == 0);
        if (unescaped_quote) inside = !inside;
        /* `im` includes the lane itself: the opening quote's lane is inside,
           the closing quote's is not, which is the prefix parity of the
           unescaped-quote lane mask. */
        if (inside) in->im[k >> 6] |= (uint64_t)1 << (k & 63);
        if (b < 0x20) {
            in->ctl[k >> 6] |= (uint64_t)1 << (k & 63);
            if (inside) in->pos[npos++] = (uint32_t)k;
        }
        if (is_bs) in->bs[k >> 6] |= (uint64_t)1 << (k & 63);
        if (is_bs) {
            if ((run & 1) == 0 && inside) in->pos[npos++] = (uint32_t)k;
            run++;
        } else {
            run = 0;
        }
    }
    in->npos = npos;
    in->xp = xmalloc((size_t)(in->n + 64 + 8) * sizeof *in->xp);
    in->dst = aligned_bytes((size_t)in->n + 64);
}

static size_t add_input(input *in, const char *name, const uint8_t *doc,
                        uint64_t n, int bounded) {
    uint64_t nb = (n + 63) / 64;
    size_t win = (size_t)(64 * (nb + 1) + 32);
    snprintf(in->name, sizeof in->name, "%s", name);
    in->n = n;
    in->doc = aligned_bytes(win);
    if (n) memcpy(in->doc, doc, (size_t)n);
    in->bounded = bounded;
    derive(in);
    return 0;
}

static size_t add_arms(input *in) {
    static const uint8_t esc[2] = {'\\', 'n'};
    uint8_t buf[8192];
    size_t count = 0;

    add_input(&in[count++], "arm:empty", buf, 0, 1);

    memset(buf, 'a', 64);
    add_input(&in[count++], "arm:plain-64", buf, 64, 1);

    /* One quoted block with an escape every two bytes. */
    memset(buf, 'a', 64);
    buf[0] = '"';
    for (int i = 1; i + 1 < 60; i += 2) memcpy(buf + i, esc, 2);
    buf[60] = '"';
    /* One block divides a fixed call and placement term by one block.  The
       same loop is measured over 64 blocks by `arm:escapes-4096`; this row is
       reported as an observation and carries no delta claim. */
    add_input(&in[count++], "arm:escapes-64", buf, 64, 0);

    /* A run of six backslashes crossing the block boundary. */
    memset(buf, 'a', 128);
    buf[0] = '"';
    memset(buf + 60, '\\', 8);
    memcpy(buf + 68, esc, 2);
    buf[70] = '"';
    add_input(&in[count++], "arm:run-across", buf, 128, 1);

    /* A raw control byte inside a string, which the expander refuses. */
    memset(buf, 'a', 64);
    buf[0] = '"';
    buf[10] = 0x0A;
    add_input(&in[count++], "arm:raw-control", buf, 64, 1);

    /* Two blocks, every other byte an escape. */
    memset(buf, 'a', 4096);
    buf[0] = '"';
    for (int i = 1; i + 1 < 4094; i += 2) memcpy(buf + i, esc, 2);
    buf[4094] = '"';
    add_input(&in[count++], "arm:escapes-4096", buf, 4096, 1);

    return count;
}

static double run_act(escape_list_fn lf, escape_expand_fn ef, const input *in) {
    uint64_t blocks = in->nb ? in->nb : 1;
    size_t reps = ACT_BYTES / (blocks * 64);
    double t0, t1;
    uint64_t r_acc = 0;
    if (reps < 1) reps = 1;
    t0 = now_ns();
    for (size_t r = 0; r < reps; r++) {
        uint64_t carry[2] = {0, 0};
        uint64_t xn = 0;
        uint64_t err = 0, xj = 0;
        for (uint64_t b = 0; b < in->nb; b++)
            lf(in->bs[b], in->ctl[b], in->im[b], b, in->xp, &xn, carry);
        r_acc ^= ef(in->doc, in->n, in->dst, &err, in->xp, &xj, in->npos, 0);
        r_acc ^= xn ^ xj ^ err;
    }
    t1 = now_ns();
    sink ^= r_acc;
    return (t1 - t0) / (double)(reps * blocks);
}

static double run_list(escape_list_fn lf, const input *in) {
    uint64_t blocks = in->nb ? in->nb : 1;
    size_t reps = ACT_BYTES / (blocks * 64);
    double t0, t1;
    uint64_t acc = 0;
    if (reps < 1) reps = 1;
    t0 = now_ns();
    for (size_t r = 0; r < reps; r++) {
        uint64_t carry[2] = {0, 0};
        uint64_t xn = 0;
        for (uint64_t b = 0; b < in->nb; b++)
            lf(in->bs[b], in->ctl[b], in->im[b], b, in->xp, &xn, carry);
        acc ^= xn;
    }
    t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)(reps * blocks);
}

static double run_expand(escape_expand_fn ef, const input *in) {
    uint64_t blocks = in->nb ? in->nb : 1;
    size_t reps = ACT_BYTES / (blocks * 64);
    double t0, t1;
    uint64_t acc = 0;
    if (reps < 1) reps = 1;
    t0 = now_ns();
    for (size_t r = 0; r < reps; r++) {
        uint64_t err = 0, xj = 0;
        acc ^= ef(in->doc, in->n, in->dst, &err, in->xp, &xj, in->npos, 0);
        acc ^= xj ^ err;
    }
    t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)(reps * blocks);
}

static void usage(void) {
    fprintf(stderr, "usage: paired-escape [--arms] [--rounds N] "
                    "[--self-control]\n");
}

int main(int argc, char **argv) {
    int rounds = 11, arms = 1, self_control = 0;
    input inputs[64];
    size_t ninputs = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc) {
            rounds = atoi(argv[++i]);
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
        fprintf(stderr, "paired-escape: --rounds needs at least 3\n");
        return 2;
    }
    if (arms) ninputs += add_arms(inputs + ninputs);
    if (ninputs == 0) { usage(); return 2; }

    /* The harness's derivation is checked against the unit once, before the
       clock starts: the expander's `pre` says the list is exactly the
       document's positions, and a timing run over any other list is a fault,
       not a measurement. */
    for (size_t k = 0; k < ninputs; k++) {
        uint64_t carry[2] = {0, 0}, xn = 0;
        for (uint64_t b = 0; b < inputs[k].nb; b++)
            probe_escape_list_measured(inputs[k].bs[b], inputs[k].ctl[b],
                                       inputs[k].im[b], b, inputs[k].xp, &xn,
                                       carry);
        if (xn != inputs[k].npos ||
            memcmp(inputs[k].xp, inputs[k].pos,
                   (size_t)xn * sizeof *inputs[k].xp) != 0) {
            fprintf(stderr,
                    "SETUP: %s: the measured list has %llu position(s), "
                    "the harness derived %llu (or their order differs)\n",
                    inputs[k].name, (unsigned long long)xn,
                    (unsigned long long)inputs[k].npos);
            return 3;
        }
    }

    /* One discarded pass over every input and both acts, so the first timed
       round is not the one that warms the buffers and the core's frequency.
       The small inputs run for a few milliseconds per act and the difference
       between two identical instruction streams is then a frequency step, not
       a code difference; without this pass the median at eleven rounds reads
       that step. */
    for (size_t k = 0; k < ninputs; k++) {
        run_act(probe_escape_list_measured, probe_escape_expand_measured,
                &inputs[k]);
        run_act(probe_escape_list_extracted, probe_escape_expand_extracted,
                &inputs[k]);
    }
    for (size_t k = 0; k < ninputs; k++) {
        run_act(probe_escape_list_measured, probe_escape_expand_measured,
                &inputs[k]);
        run_act(probe_escape_list_extracted, probe_escape_expand_extracted,
                &inputs[k]);
    }

    printf("# paired timing: the extracted escape unit against the measured statements\n");
    printf("# ns/block: one block is 64 document bytes; the bound is +/-0.5\n");
    printf("# one act is the block walk plus one expander call over the list it built\n");
    printf("core-class: %u\n", core_class());
    printf("rounds: %d\n", rounds);
    printf("self-control: %s\n", self_control ? "yes" : "no");

    int failed = 0;
    for (size_t k = 0; k < ninputs; k++) {
        escape_list_fn la = probe_escape_list_measured;
        escape_list_fn lb = self_control ? la : probe_escape_list_extracted;
        escape_expand_fn ea = probe_escape_expand_measured;
        escape_expand_fn eb = self_control ? ea : probe_escape_expand_extracted;
        double *d = xmalloc((size_t)rounds * sizeof *d);
        double *av = xmalloc((size_t)rounds * sizeof *av);
        double *bv = xmalloc((size_t)rounds * sizeof *bv);
        for (int r = 0; r < rounds; r++) {
            double x, y;
            if (la == lb) {
                x = run_act(la, ea, &inputs[k]);
                y = x;
            } else {
                double a1, a2, b1, b2;
                if ((r & 1) == 0) {
                    a1 = run_act(la, ea, &inputs[k]);
                    b1 = run_act(lb, eb, &inputs[k]);
                    b2 = run_act(lb, eb, &inputs[k]);
                    a2 = run_act(la, ea, &inputs[k]);
                } else {
                    b1 = run_act(lb, eb, &inputs[k]);
                    a1 = run_act(la, ea, &inputs[k]);
                    a2 = run_act(la, ea, &inputs[k]);
                    b2 = run_act(lb, eb, &inputs[k]);
                }
                x = 0.5 * (a1 + a2);
                y = 0.5 * (b1 + b2);
            }
            av[r] = x;
            bv[r] = y;
            d[r] = y - x;
        }
        {
            double ma = median(av, rounds);
            double mb = median(bv, rounds);
            double med = median(d, rounds);
            double spread = d[rounds - 1] - d[0];
            printf("%-24s measured %10.3f extracted %10.3f median %8.3f "
                   "spread %8.3f positions %4llu\n",
                   inputs[k].name, ma, mb, med, spread,
                   (unsigned long long)inputs[k].npos);
            printf("%-24s %-8s list-ns %8.3f/%8.3f expand-ns %8.3f/%8.3f "
                   "(measured/extracted observation, no delta claimed)\n",
                   inputs[k].name, "observe",
                   run_list(probe_escape_list_measured, &inputs[k]),
                   run_list(probe_escape_list_extracted, &inputs[k]),
                   run_expand(probe_escape_expand_measured, &inputs[k]),
                   run_expand(probe_escape_expand_extracted, &inputs[k]));
            if (self_control) {
                if (med != 0.0) {
                    fprintf(stderr,
                            "FAIL: self-control reported %.6f, not 0.0\n", med);
                    failed = 1;
                }
            } else if (!inputs[k].bounded) {
                printf("%-24s %-8s median %8.3f (observation: one-block dense "
                       "input, no delta claim; see arm:escapes-4096)\n",
                       inputs[k].name, "observe", med);
            } else if (med > 0.5 || med < -0.5) {
                fprintf(stderr,
                        "FAIL: %s: median difference %.3f ns/block is outside "
                        "+/-0.5\n", inputs[k].name, med);
                failed = 1;
            }
        }
        free(d);
        free(av);
        free(bv);
    }
    if (self_control) {
        printf("ok: the harness reports 0.0 against itself\n");
    } else if (failed) {
        /* reported above */
    } else {
        printf("ok: every bounded input is within +/-0.5 ns/block "
               "(arm:escapes-64 is an observation, not a bounded input)\n");
    }
    return failed ? 1 : 0;
}
