/* paired.c -- Arm C: paired timing of the extracted mask unit against the
   measured one, in one binary, selected per process.

   The file is compiled three times by `paired.sh`:

     -DPAIRED_PROBE=measured -DPROBE_NAME=probe_measured   the measured unit
     -DPAIRED_PROBE=kernel   -DPROBE_NAME=probe_kernel     the extracted unit
     -DPAIRED_MAIN                                         the harness

   The two probe translation units carry distinct symbols and are never linked
   with LTO, so each call through a function pointer reaches the code that
   translation unit emitted.  One binary holding both is the point: the two
   acts run in the same process, on the same data, in the same round, in
   rotated order, so a build-to-build or session-to-session shift cannot be
   read as a difference between the implementations.

   Each act gets a fresh copy of the input's carry words, because `s1f_masks`
   writes the carry it leaves; the copy is outside the timed region.

   Reported per input: the median of (extracted - measured) ns/block over the
   rounds, and the round-to-round spread.  The claim is a bound on that median,
   not on any single round; `--self-control` swaps in the measured unit for
   both acts and requires exactly 0.0, which is a check on the harness's
   dispatch and subtraction rather than on the clock. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct { uint64_t esc_open, esc_ppar, im_carry; } paired_carry;
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } paired_masks;

void probe_measured(const uint8_t *p, paired_carry *c, paired_masks *o);
void probe_kernel(const uint8_t *p, paired_carry *c, paired_masks *o);

#if defined(PAIRED_PROBE)

/* ------------------------------------------------------------------ probe -- */

#if defined(PAIRED_MEASURED)
#include "s1fuse.h"
#else
#include "s1_block.c"
#endif

/* Both probes share the measured `s1f_masks` name and see the same three-word
   carry: the measured `S1F` has six fields and the mask function touches the
   first three, so the cast reads the same object the measured build reads.

   Each probe is placed at a 4 KiB boundary.  The two bodies are the same
   machine code (identity is Arm B's job; the instruction streams compare equal),
   but two identical bodies at different absolute addresses can still run at
   different speeds on a core whose uop cache and I-cache map by address: a
   700-byte function's start offset decides which sets it occupies.  Giving both
   the same geometry removes placement as a confounder, so the reported number
   is the code's cost and not its address's. */
#define PAIRED_ALIGN __attribute__((aligned(4096)))

PAIRED_ALIGN void PROBE_NAME(const uint8_t *p, paired_carry *c, paired_masks *o) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    uint64_t qm, sm, im, ws, bm, ctl;
    s1f_masks(v0, v1, (S1F *)c, &qm, &sm, &im, &ws, &bm, &ctl);
    o->quote = qm;
    o->delim = sm;
    o->in_string = im;
    o->ws = ws;
    o->backslash = bm;
    o->ctl = ctl;
}

#else /* PAIRED_MAIN */

/* ---------------------------------------------------------------- harness -- */

#define BLOCK 64
#define STATES 8

typedef void (*probe_fn)(const uint8_t *, paired_carry *, paired_masks *);

/* The eight carry states: the two escape fields and the two in-string words. */
static const paired_carry states[STATES] = {
    {0, 0, 0}, {0, 0, ~(uint64_t)0}, {0, 1, 0}, {0, 1, ~(uint64_t)0},
    {1, 0, 0}, {1, 0, ~(uint64_t)0}, {1, 1, 0}, {1, 1, ~(uint64_t)0},
};

typedef struct {
    char name[256];
    uint8_t *blocks;
    paired_carry *carries;
    size_t nblocks;
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
        fprintf(stderr, "paired: out of memory\n");
        exit(2);
    }
    return p;
}

static size_t add_arm(input *in, const char *name, size_t nblocks) {
    in->blocks = xmalloc(nblocks * BLOCK);
    in->carries = xmalloc(nblocks * sizeof *in->carries);
    snprintf(in->name, sizeof in->name, "%s", name);
    in->nblocks = nblocks;
    return nblocks;
}

/* arm:byte -- every byte value in every lane, under each carry state. */
static size_t arm_byte(input *in) {
    size_t n = add_arm(in, "arm:byte", (size_t)STATES * 64 * 256), i = 0;
    for (int s = 0; s < STATES; s++)
        for (size_t pos = 0; pos < 64; pos++)
            for (unsigned v = 0; v < 256; v++) {
                uint8_t *b = in->blocks + i * BLOCK;
                memset(b, 0x61, BLOCK);
                b[pos] = (uint8_t)v;
                in->carries[i] = states[s];
                i++;
            }
    return n;
}

/* arm:alphabet -- every 4-byte sequence of the 16-symbol class alphabet. */
static size_t arm_alphabet(input *in) {
    static const uint8_t alphabet[16] = {0x00, 0x09, 0x0A, 0x0D, 0x1F, 0x20,
                                         0x22, 0x2C, 0x3A, 0x5B, 0x5C, 0x5D,
                                         0x7B, 0x7D, 0x61, 0x80};
    size_t n = add_arm(in, "arm:alphabet", (size_t)STATES * 65536), i = 0;
    for (int s = 0; s < STATES; s++)
        for (unsigned q = 0; q < 65536; q++) {
            uint8_t *b = in->blocks + i * BLOCK;
            memset(b, 0x61, BLOCK);
            b[0] = alphabet[(q >> 12) & 15];
            b[1] = alphabet[(q >> 8) & 15];
            b[2] = alphabet[(q >> 4) & 15];
            b[3] = alphabet[q & 15];
            in->carries[i] = states[s];
            i++;
        }
    return n;
}

static uint64_t splitmix_next(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* arm:random -- a fixed-seed stream, the same blocks on every run. */
static size_t arm_random(input *in) {
    size_t n = add_arm(in, "arm:random", (size_t)STATES * 4096), i = 0;
    uint64_t seed = 0x5C1D01A5EEDULL;
    for (int s = 0; s < STATES; s++)
        for (int k = 0; k < 4096; k++) {
            uint8_t *b = in->blocks + i * BLOCK;
            for (int j = 0; j < 8; j++) {
                uint64_t w = splitmix_next(&seed);
                memcpy(b + j * 8, &w, 8);
            }
            in->carries[i] = states[s];
            i++;
        }
    return n;
}

/* corpus -- one input per --corpus file, one window per 64-byte offset. */
static size_t add_corpus(input *in, const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "paired: cannot read %s\n", path);
        exit(2);
    }
    if (fseek(f, 0, SEEK_END) != 0) {
        fprintf(stderr, "paired: cannot seek %s\n", path);
        exit(2);
    }
    long size = ftell(f);
    if (size < 0) {
        fprintf(stderr, "paired: cannot size %s\n", path);
        exit(2);
    }
    rewind(f);
    uint8_t *data = xmalloc((size_t)size);
    if (size > 0 && fread(data, 1, (size_t)size, f) != (size_t)size) {
        fprintf(stderr, "paired: cannot read %s\n", path);
        exit(2);
    }
    fclose(f);
    size_t n = size >= BLOCK ? (size_t)size - (BLOCK - 1) : 0;
    add_arm(in, path, n);
    for (size_t i = 0; i < n; i++) {
        memcpy(in->blocks + i * BLOCK, data + i, BLOCK);
        in->carries[i] = states[i % STATES];
    }
    free(data);
    return n;
}

/* Blocks per timed act: a short corpus file is repeated until the act is long
   enough that the clock and the call overhead are not the measurement.  The
   repetition is of the same blocks, and both acts get the same count. */
#define ACT_BLOCKS ((size_t)1 << 20)

static double run_act(probe_fn fn, const input *in, paired_carry *work) {
    paired_masks out;
    size_t reps = ACT_BLOCKS / (in->nblocks ? in->nblocks : 1);
    if (reps < 1) reps = 1;
    memcpy(work, in->carries, in->nblocks * sizeof *work);
    double t0 = now_ns();
    for (size_t r = 0; r < reps; r++)
        for (size_t i = 0; i < in->nblocks; i++)
            fn(in->blocks + i * BLOCK, &work[i], &out);
    double t1 = now_ns();
    sink ^= out.quote ^ out.delim ^ out.in_string ^ out.ws ^ out.backslash ^ out.ctl;
    return (t1 - t0) / (double)(reps * in->nblocks);
}

static void usage(void) {
    fprintf(stderr,
            "usage: paired [--corpus FILE]... [--arms] [--rounds N] "
            "[--self-control]\n");
}

int main(int argc, char **argv) {
    input *inputs = NULL;
    size_t ninputs = 0, cap = 0;
    int rounds = 11, arms = 0, self_control = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--corpus") == 0 && i + 1 < argc) {
            if (ninputs == cap) {
                cap = cap ? 2 * cap : 8;
                inputs = realloc(inputs, cap * sizeof *inputs);
                if (!inputs) {
                    fprintf(stderr, "paired: out of memory\n");
                    return 2;
                }
            }
            add_corpus(&inputs[ninputs++], argv[++i]);
        } else if (strcmp(argv[i], "--rounds") == 0 && i + 1 < argc) {
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
        fprintf(stderr, "paired: --rounds needs at least 3\n");
        return 2;
    }
    if (arms) {
        if (ninputs + 3 > cap) {
            cap = ninputs + 3;
            inputs = realloc(inputs, cap * sizeof *inputs);
            if (!inputs) {
                fprintf(stderr, "paired: out of memory\n");
                return 2;
            }
        }
        arm_byte(&inputs[ninputs++]);
        arm_alphabet(&inputs[ninputs++]);
        arm_random(&inputs[ninputs++]);
    }
    if (ninputs == 0) {
        usage();
        return 2;
    }

    probe_fn a = probe_measured;
    probe_fn b = self_control ? probe_measured : probe_kernel;
    size_t biggest = 0;
    for (size_t i = 0; i < ninputs; i++)
        if (inputs[i].nblocks > biggest) biggest = inputs[i].nblocks;
    paired_carry *work = xmalloc(biggest * sizeof *work);

    printf("core-class: %u\n", core_class());
    printf("rounds: %d\n", rounds);
    printf("self-control: %s\n", self_control ? "yes" : "no");
    printf("%-28s %14s %14s %10s %10s\n", "input", "measured", "extracted",
           "median", "spread");

    int failed = 0;
    for (size_t k = 0; k < ninputs; k++) {
        if (inputs[k].nblocks == 0) {
            printf("%-28s %14s %14s %10s %10s\n", inputs[k].name, "-", "-",
                   "skipped", "no window");
            continue;
        }
        double *d = xmalloc((size_t)rounds * sizeof *d);
        double *av = xmalloc((size_t)rounds * sizeof *av);
        double *bv = xmalloc((size_t)rounds * sizeof *bv);
        for (int r = 0; r < rounds; r++) {
            double x, y;
            if (a == b) {
                x = run_act(a, &inputs[k], work);
                y = x;
            } else if ((r & 1) == 0) {
                x = run_act(a, &inputs[k], work);
                y = run_act(b, &inputs[k], work);
            } else {
                y = run_act(b, &inputs[k], work);
                x = run_act(a, &inputs[k], work);
            }
            av[r] = x;
            bv[r] = y;
            d[r] = y - x;
        }
        double ma = median(av, rounds);
        double mb = median(bv, rounds);
        double med = median(d, rounds);
        double spread = d[rounds - 1] - d[0];
        printf("%-28s %14.3f %14.3f %10.3f %10.3f\n", inputs[k].name, ma, mb,
               med, spread);
        if (self_control) {
            if (med != 0.0) {
                fprintf(stderr, "FAIL: self-control reported %.6f, not 0.0\n", med);
                failed = 1;
            }
        } else if (med > 0.5 || med < -0.5) {
            fprintf(stderr, "FAIL: %s: median difference %.3f ns/block is outside +/-0.5\n",
                    inputs[k].name, med);
            failed = 1;
        }
        free(d);
        free(av);
        free(bv);
    }
    if (self_control) {
        printf("ok: the harness reports 0.0 against itself\n");
    } else {
        printf("ok: every input's median difference is within +/-0.5 ns/block\n");
    }
    return failed ? 1 : 0;
}

#endif
