/* paired-utf8.c -- Arm C: paired timing of the UTF-8 unit against the measured
   statements, in one binary.
 *
 * The file is compiled three times by `paired.sh --unit utf8`:
 *
 *     (nothing)                                   the measured side is the
 *                                                 script-generated stage TU,
 *                                                 named probe_utf8_measured
 *     -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_utf8_extracted
 *                                                 kernel/json/utf8.c
 *     -DPAIRED_MAIN                               the harness
 *
 * The two sides are two *texts*, not two include paths: the stage is a region
 * of the measured header rather than a function, so the measured side cannot be
 * selected with `-I`.  `paired.sh` generates it with
 * `source-identity.sh --unit utf8 --stage-tu` and renames its function, and the
 * extracted side is `kernel/json/utf8.c` behind a wrapper with the same ABI.
 * Both probes take the ABI's `(const uint8_t *b, uint64_t n, int ungated)`.
 *
 * The acts are (side x gate) pairs over one staged document: the gated arm
 * (the per-block ASCII test) and the ungated one, on each side.  The reported
 * comparison is the measured side against the extracted one **at the same gate
 * value** — two binaries built from two texts, in one process, in rotated
 * order, so a build-to-build or session-to-session shift cannot be read as a
 * difference between them.  Each round runs both acts twice, once in each
 * order, and averages each side, so a drift inside the round lands on both acts
 * and cancels in the difference instead of deciding it.  Per input and per gate
 * the report is the median of (extracted - measured) ns/block over the rounds,
 * against a +/-0.5 ns/block bound.
 *
 * The gated and ungated medians are printed beside it as an **observation** and
 * with no delta claim: the two arms are different code shapes whose cost is a
 * range (a skipped block runs the header and the latch, an evaluated one runs
 * the header, the DFA body and the latch), so a difference between them is a
 * property of the document's content and not a pair to be tested.  The
 * per-document `skip` and `eval` counts printed with them are **derived from
 * the document's bytes** by `probes/json/utf8_skip.h` — the same one function
 * the route's transcripts use — and not read out of the code under test: the
 * gate's two arms agree on every document's verdict, so the counts are the only
 * per-document trace of which arm did what.
 *
 * Placement: the flags align every function to 4 KiB, so the probes and the
 * call sites that reach them start at page boundaries on both sides.  The two
 * sides are the same machine code (the IR arm lifts and compares them), but
 * identical code at different addresses can still run at different speeds on a
 * core whose uop cache and I-cache map by address; giving both the same
 * geometry removes placement as a confounder.  `paired.sh` asserts the
 * alignment with `nm`.
 *
 * `--self-control` runs the measured side against itself and requires exactly
 * 0.0, which is a check on the harness's dispatch and subtraction rather than
 * on the clock.
 *
 * The inputs are the curated corpus `tests/json-utf8/corpus.tsv` — one input
 * per row, staged the way the route stages it — and eight generated arms that
 * put the gate's two shapes, the tail's 63/64/65 boundary and a mixed document
 * under the same instrument.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "../../../probes/json/utf8_skip.h"

typedef uint64_t (*paired_utf8_fn)(const uint8_t *, uint64_t, int);

uint64_t probe_utf8_measured(const uint8_t *, uint64_t, int);
uint64_t probe_utf8_extracted(const uint8_t *, uint64_t, int);

#if defined(PAIRED_PROBE)

/* ------------------------------------------------------------------ probe -- */

#if !defined(PROBE_NAME)
#error "a probe TU needs -DPROBE_NAME=<symbol>"
#endif

#define PAIRED_ALIGN __attribute__((aligned(4096)))

/* The extracted side is the unit's own translation unit, included so the
   probe's call reaches the code the object ships rather than a copy. */
#include "../utf8.c"

PAIRED_ALIGN uint64_t PROBE_NAME(const uint8_t *b, uint64_t n, int ungated) {
    return leanllvm_json_utf8(b, n, ungated);
}

#else /* PAIRED_MAIN */

/* ---------------------------------------------------------------- harness -- */

#define ACT_BYTES ((size_t)1 << 20)

typedef struct {
    char name[320];
    uint8_t *win;   /* three zero prefix bytes, the document, zero padding */
    uint64_t n;
} input;

static volatile uint64_t sink;

static double now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

/* The core class the process is running on: CPUID.1Ah.EAX[31:24]. */
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
        fprintf(stderr, "paired-utf8: out of memory\n");
        exit(2);
    }
    return p;
}

/* A page-aligned buffer, so the probe's own `aligned(4096)` attribute and this
   document's first byte are both at page boundaries. */
static uint8_t *aligned_bytes(size_t n) {
    void *p = NULL;
    if (posix_memalign(&p, 4096, n ? n : 1) != 0 || !p) {
        fprintf(stderr, "paired-utf8: cannot allocate %zu bytes\n", n);
        exit(2);
    }
    memset(p, 0, n);
    return p;
}

static size_t add_input(input *in, const char *name, const uint8_t *doc,
                        uint64_t n) {
    uint64_t nb = (n + 63) / 64;
    snprintf(in->name, sizeof in->name, "%s", name);
    in->n = n;
    in->win = aligned_bytes((size_t)(3 + 64 * (nb ? nb : 1)));
    in->win[0] = in->win[1] = in->win[2] = 0;
    if (n) memcpy(in->win + 3, doc, (size_t)n);
    return (size_t)n;
}

/* One corpus file: `label \t hex \t n \t expectation`, the route's columns.
   The expectation is the route's business; this harness stages the bytes. */
static size_t read_corpus(const char *path, input *in, size_t cap) {
    FILE *fp = fopen(path, "r");
    char line[65536];
    static uint8_t doc[4096];
    size_t count = 0;
    if (!fp) {
        fprintf(stderr, "paired-utf8: cannot read %s\n", path);
        exit(3);
    }
    while (fgets(line, sizeof line, fp)) {
        const char *f[4];
        size_t len[4], k = 0, hlen, i, l;
        const char *p = line;
        uint64_t n;
        l = strlen(line);
        while (l && (line[l - 1] == '\n' || line[l - 1] == '\r')) line[--l] = '\0';
        if (!l) continue;
        while (k < 4) {
            const char *q = strchr(p, '\t');
            f[k] = p;
            len[k] = q ? (size_t)(q - p) : strlen(p);
            k++;
            if (!q) break;
            p = q + 1;
        }
        if (k != 4) {
            fprintf(stderr, "paired-utf8: %s: not four tab-separated columns\n",
                    path);
            exit(3);
        }
        hlen = len[1];
        if (hlen == 1 && f[1][0] == '-') hlen = 0;
        else if ((hlen & 1) != 0 || hlen / 2 > sizeof doc) {
            fprintf(stderr, "paired-utf8: %s: hex is not whole bytes in range\n",
                    path);
            exit(3);
        }
        n = strtoull(f[2], NULL, 10);
        if (hlen / 2 != n) {
            fprintf(stderr, "paired-utf8: %s: %zu byte(s) of hex, n=%llu\n",
                    path, hlen / 2, (unsigned long long)n);
            exit(3);
        }
        for (i = 0; i < n; i++) {
            unsigned hi, lo;
            char a = f[1][2 * i], b = f[1][2 * i + 1];
            if (a >= '0' && a <= '9') hi = (unsigned)(a - '0');
            else if (a >= 'a' && a <= 'f') hi = (unsigned)(a - 'a' + 10);
            else { fprintf(stderr, "paired-utf8: %s: bad hex\n", path); exit(3); }
            if (b >= '0' && b <= '9') lo = (unsigned)(b - '0');
            else if (b >= 'a' && b <= 'f') lo = (unsigned)(b - 'a' + 10);
            else { fprintf(stderr, "paired-utf8: %s: bad hex\n", path); exit(3); }
            doc[i] = (uint8_t)(hi * 16 + lo);
        }
        if (count == cap) {
            fprintf(stderr, "paired-utf8: more than %zu corpus rows\n", cap);
            exit(3);
        }
        {
            char name[320];
            size_t ll = len[0] < 280 ? len[0] : 280;
            memcpy(name, f[0], ll);
            name[ll] = '\0';
            add_input(&in[count++], name, doc, n);
        }
    }
    fclose(fp);
    return count;
}

/* The generated arms: the gate's two shapes, the tail boundary, and a mixed
   document.  Each is a rule over the bytes, so the set is defined by this code
   and its names rather than by committed data. */
static size_t add_arms(input *in) {
    static const uint8_t euro[3] = {0xE2, 0x82, 0xAC};
    uint8_t buf[4096];
    size_t count = 0;

    memset(buf, 0x41, 64);
    add_input(&in[count++], "arm:ascii-64", buf, 64);

    memset(buf, 0x41, 4096);
    add_input(&in[count++], "arm:ascii-4096", buf, 4096);

    for (size_t i = 0; i < 4096; i += 3) {
        size_t k = 4096 - i < 3 ? 4096 - i : 3;
        memcpy(buf + i, euro, k);
    }
    add_input(&in[count++], "arm:high-4096", buf, 4096);

    /* Alternate one all-ASCII block with one block that carries a high byte, so
       the gate skips block 0 and nothing after it. */
    for (int b = 0; b < 64; b++) {
        if (b % 2 == 0) memset(buf + 64 * b, 0x41, 64);
        else
            for (int i = 0; i < 64; i += 3) memcpy(buf + 64 * b + i, euro, 3);
    }
    add_input(&in[count++], "arm:mixed-4096", buf, 4096);

    for (int L = 63; L <= 65; L++) {
        memset(buf, 0x41, (size_t)L);
        buf[L - 1] = 0xE2;
        {
            char name[64];
            snprintf(name, sizeof name, "arm:tail-%d", L);
            add_input(&in[count++], name, buf, (uint64_t)L);
        }
    }

    memset(buf, 0x41, 200);
    buf[200] = 0xC3;
    buf[201] = 0xA9;
    add_input(&in[count++], "arm:ascii-200-c3a9", buf, 202);

    return count;
}

static double run_act(paired_utf8_fn fn, const input *in, int ungated) {
    uint64_t nb = (in->n + 63) / 64;
    size_t blocks = nb ? (size_t)nb : 1;
    size_t reps = ACT_BYTES / (blocks * 64);
    uint64_t e = 0;
    double t0, t1;
    if (reps < 1) reps = 1;
    t0 = now_ns();
    for (size_t r = 0; r < reps; r++)
        e = fn(in->win + 3, in->n, ungated);
    t1 = now_ns();
    sink ^= e;
    return (t1 - t0) / (double)(reps * blocks);
}

static void usage(void) {
    fprintf(stderr, "usage: paired-utf8 [--corpus FILE]... [--arms] "
                    "[--rounds N] [--self-control]\n");
}

int main(int argc, char **argv) {
    int rounds = 11, arms = 0, self_control = 0, ncorpus = 0;
    const char *corpus[32];
    input inputs[512];
    size_t ninputs = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc) {
            rounds = atoi(argv[++i]);
        } else if (strcmp(argv[i], "--arms") == 0) {
            arms = 1;
        } else if (strcmp(argv[i], "--self-control") == 0) {
            self_control = 1;
        } else if (strcmp(argv[i], "--corpus") == 0 && i + 1 < argc) {
            if (ncorpus == 32) { usage(); return 2; }
            corpus[ncorpus++] = argv[++i];
        } else {
            usage();
            return 2;
        }
    }
    if (rounds < 3) {
        fprintf(stderr, "paired-utf8: --rounds needs at least 3\n");
        return 2;
    }
    for (int i = 0; i < ncorpus; i++)
        ninputs += read_corpus(corpus[i], inputs + ninputs,
                               sizeof inputs / sizeof *inputs - ninputs);
    if (arms) ninputs += add_arms(inputs + ninputs);
    if (ninputs == 0) { usage(); return 2; }

    {
        /* One discarded pass over every input and act, so the first measured
           round is not the one that warms the buffers and the core's
           frequency. */
        for (size_t k = 0; k < ninputs; k++)
            for (int g = 0; g < 2; g++) {
                run_act(probe_utf8_measured, &inputs[k], g);
                run_act(probe_utf8_extracted, &inputs[k], g);
            }

        printf("# paired timing: the extracted UTF-8 unit against the measured statements\n");
        printf("# ns/block: one block is 64 document bytes; the bound is +/-0.5\n");
        printf("# the gated and ungated medians are an observation, not a pair\n");
        printf("# skip/eval are DERIVED from the document's bytes (probes/json/utf8_skip.h), not measured\n");
        printf("core-class: %u\n", core_class());
        printf("rounds: %d\n", rounds);
        printf("self-control: %s\n", self_control ? "yes" : "no");
        printf("acts: gated = the per-block ASCII test, ungated = evaluate every block\n");

        int failed = 0;
        size_t skipped_rows = 0, evaluated_rows = 0;
        for (size_t k = 0; k < ninputs; k++) {
            double obs[2][2];
            for (int g = 0; g < 2; g++) {
                paired_utf8_fn a = probe_utf8_measured;
                paired_utf8_fn b = self_control ? a : probe_utf8_extracted;
                double *d = xmalloc((size_t)rounds * sizeof *d);
                double *av = xmalloc((size_t)rounds * sizeof *av);
                double *bv = xmalloc((size_t)rounds * sizeof *bv);
                for (int r = 0; r < rounds; r++) {
                    double x, y;
                    if (a == b) {
                        x = run_act(a, &inputs[k], g);
                        y = x;
                    } else {
                        double a1, a2, b1, b2;
                        if ((r & 1) == 0) {
                            a1 = run_act(a, &inputs[k], g);
                            b1 = run_act(b, &inputs[k], g);
                            b2 = run_act(b, &inputs[k], g);
                            a2 = run_act(a, &inputs[k], g);
                        } else {
                            b1 = run_act(b, &inputs[k], g);
                            a1 = run_act(a, &inputs[k], g);
                            a2 = run_act(a, &inputs[k], g);
                            b2 = run_act(b, &inputs[k], g);
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
                    printf("%-24s %-8s measured %10.3f extracted %10.3f "
                           "median %8.3f spread %8.3f\n",
                           inputs[k].name, g ? "ungated" : "gated", ma, mb, med,
                           spread);
                    obs[g][0] = ma;
                    obs[g][1] = mb;
                    if (self_control) {
                        if (med != 0.0) {
                            fprintf(stderr,
                                    "FAIL: self-control reported %.6f, not 0.0\n",
                                    med);
                            failed = 1;
                        }
                    } else if (med > 0.5 || med < -0.5) {
                        fprintf(stderr,
                                "FAIL: %s/%s: median difference %.3f ns/block is "
                                "outside +/-0.5\n",
                                inputs[k].name, g ? "ungated" : "gated", med);
                        failed = 1;
                    }
                }
                free(d);
                free(av);
                free(bv);
            }
            {
                /* The observation: the two gate values' medians, and the counts
                   the gate's rule gives for this document.  No delta is
                   claimed. */
                uint64_t nb = (inputs[k].n + 63) / 64, skip, eval;
                utf8_block_counts(inputs[k].win + 3, inputs[k].n, 0, &skip, &eval);
                printf("%-24s %-8s gated-ns %10.3f ungated-ns %10.3f "
                       "skip %4llu eval %4llu blocks %4llu\n",
                       inputs[k].name, "observe", obs[0][1], obs[1][1],
                       (unsigned long long)skip, (unsigned long long)eval,
                       (unsigned long long)nb);
                skipped_rows += (size_t)skip;
                evaluated_rows += (size_t)eval;
            }
        }
        printf("blocks observed: %zu skipped, %zu evaluated (derived)\n",
               skipped_rows, evaluated_rows);
        if (self_control) {
            printf("ok: the harness reports 0.0 against itself\n");
        } else if (failed) {
            /* reported above */
        } else {
            printf("ok: every input and gate value is within +/-0.5 ns/block\n");
        }
        return failed ? 1 : 0;
    }
}

#endif
