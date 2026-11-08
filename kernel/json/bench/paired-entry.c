/* paired-entry.c -- Arm C: paired timing of the entry unit's two kernels
   against the measured ones, in one binary, selected per process.

   The file is compiled three times by `paired.sh --unit entry`:

     -DPAIRED_PROBE=measured  -DPROBE_NAME=probe_entry_measured   (vendored headers)
     -DPAIRED_PROBE=extracted -DPROBE_NAME=probe_entry_extracted  (kernel/json/entry.c)
     -DPAIRED_MAIN                                                (the harness)

   Each probe translation unit holds one kernel of each shape -- `pos8` and
   `b8` -- over the measured `(uint64_t *ent, uint64_t blk0, uint64_t nblk,
   uint32_t *out, uint64_t k)` signature, and a constructor that initialises its
   own table before anything is timed.  The two TUs are never linked with LTO,
   so each call through the function pointer reaches the code that TU emitted,
   and the unit's static kernels keep internal linkage on both sides.

   The acts are the four (kernel x side) pairs.  One binary holding all four is
   the point: within a round they run on the same masks, in the same process, in
   rotated order, so a build-to-build or session-to-session shift cannot be read
   as a difference between the implementations.  Each round runs both acts twice,
   once in each order, and averages each side, so a drift inside the round lands
   on both acts and cancels in the difference instead of deciding it.  Per input
   and per kernel the report is the median of (extracted - measured) ns/block
   over the rounds.

   Placement: the flags align every function to 4 KiB, so the kernels and the
   call sites that reach them start at page boundaries on both sides.  The two
   bodies are the same machine code (Arm B lifts and compares them), but
   identical code at different addresses can still run at different speeds on a
   core whose uop cache and I-cache map by address; giving both the same
   geometry removes placement as a confounder, so the reported number is the
   code's cost and not its address's.  `paired.sh` asserts the alignment with
   `nm`.

   Reported per input and kernel: the median difference and the round-to-round
   spread.  The claim is a bound on that median, not on any single round;
   `--self-control` swaps the measured kernel in for the extracted one and
   requires exactly 0.0, which is a check on the harness's dispatch and
   subtraction rather than on the clock.

   The masks are one per block, so the timed call is one kernel invocation over
   `nblk` masks -- the block loop's own shape, with the loop inside the timed
   region rather than around it. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uint64_t (*paired_entry_fn)(uint64_t *, uint64_t, uint64_t, uint32_t *,
                                    uint64_t);

uint64_t probe_entry_measured_pos8(uint64_t *, uint64_t, uint64_t, uint32_t *,
                                   uint64_t);
uint64_t probe_entry_measured_b8(uint64_t *, uint64_t, uint64_t, uint32_t *,
                                 uint64_t);
uint64_t probe_entry_extracted_pos8(uint64_t *, uint64_t, uint64_t, uint32_t *,
                                    uint64_t);
uint64_t probe_entry_extracted_b8(uint64_t *, uint64_t, uint64_t, uint32_t *,
                                  uint64_t);

#if defined(PAIRED_PROBE)

/* ------------------------------------------------------------------ probe -- */

#if defined(PAIRED_MEASURED)
#include "s1fuse.h"
#else
#include "../entry.c"
#endif

#define PAIRED_PASTE_(a, b) a##b
#define PAIRED_PASTE(a, b) PAIRED_PASTE_(a, b)
#define PAIRED_ALIGN __attribute__((aligned(4096)))

/* The table is written once, outside the timed region, on both sides: an
   unreachable initialiser would fold the array to zeros and the timed loop
   would read a table that is not the one the object ships. */
__attribute__((constructor)) static void paired_entry_init(void) {
    xl_pos8_init();
}

PAIRED_ALIGN uint64_t PAIRED_PASTE(PROBE_NAME, _pos8)(
    uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out, uint64_t k) {
    return s1f_k_pos8(ent, blk0, nblk, out, k);
}

PAIRED_ALIGN uint64_t PAIRED_PASTE(PROBE_NAME, _b8)(
    uint64_t *ent, uint64_t blk0, uint64_t nblk, uint32_t *out, uint64_t k) {
    return s1f_k_b8(ent, blk0, nblk, out, k);
}

#else /* PAIRED_MAIN */

/* ---------------------------------------------------------------- harness -- */

typedef struct {
    char name[256];
    uint64_t *masks;
    size_t nblk;
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
        fprintf(stderr, "paired-entry: out of memory\n");
        exit(2);
    }
    return p;
}

static size_t add_arm(input *in, const char *name, size_t nblk) {
    in->masks = xmalloc(nblk * sizeof *in->masks);
    snprintf(in->name, sizeof in->name, "%s", name);
    in->nblk = nblk;
    return nblk;
}

static uint64_t splitmix_next(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* arm:single -- one lane set, at every lane of the block. */
static size_t arm_single(input *in) {
    size_t n = add_arm(in, "arm:single", 64);
    for (size_t i = 0; i < n; i++) in->masks[i] = 1ULL << i;
    return n;
}

/* arm:group -- each of the 256 values in the block's first mask byte, which is
   every row of the table the `pos8` kernel reads. */
static size_t arm_group(input *in) {
    size_t n = add_arm(in, "arm:group", 256);
    for (size_t i = 0; i < n; i++) in->masks[i] = (uint64_t)i;
    return n;
}

/* arm:random -- the first 4,096 masks of a fixed-seed stream, the same masks on
   every run, so the sample is defined by the seed and the count alone and both
   are printed with the result.

   4,096 rather than a longer stream on purpose: the arm is repeated until the
   act is long enough, so the cost that is measured is the emitter's.  A stream
   whose stores outgrow the cache measures memory bandwidth instead, and then it
   reports the machine's current load as well as the code -- which it did: at
   65,536 masks the same comparison swung by 0.6 ns/block between runs on the
   efficiency cores while the two bodies were byte-identical. */
#define ARM_RANDOM_COUNT ((size_t)4096)
#define ARM_RANDOM_SEED 0x5C1D01A5EEDULL

static size_t arm_random(input *in) {
    size_t n = add_arm(in, "arm:random", ARM_RANDOM_COUNT);
    uint64_t seed = ARM_RANDOM_SEED;
    for (size_t i = 0; i < n; i++) in->masks[i] = splitmix_next(&seed);
    return n;
}

/* arm:empty and arm:full -- the two ends, each a single block. */
static size_t arm_empty(input *in) {
    size_t n = add_arm(in, "arm:empty", 1);
    in->masks[0] = 0;
    return n;
}

static size_t arm_full(input *in) {
    size_t n = add_arm(in, "arm:full", 1);
    in->masks[0] = ~(uint64_t)0;
    return n;
}

/* arm:long -- 1,025 blocks in one call: a run longer than any corpus document,
   so the block loop's iteration count is exercised well past a handful. */
static size_t arm_long(input *in) {
    size_t n = add_arm(in, "arm:long", 1025);
    uint64_t seed = 0xC0FFEE5EEDULL;
    for (size_t i = 0; i < n; i++) in->masks[i] = splitmix_next(&seed);
    return n;
}

/* Blocks per timed act: a short input is repeated until the act is long enough
   that the clock and the call overhead are not the measurement.  The repetition
   is of the same masks, and every act gets the same count. */
#define ACT_BLOCKS ((size_t)1 << 20)

/* The buffer holds the largest count an input can produce (64 positions per
   block) plus the eight lanes an emitter may write past the count. */
static uint32_t *out_buf;

static double run_act(paired_entry_fn fn, const input *in) {
    size_t reps = ACT_BLOCKS / (in->nblk ? in->nblk : 1);
    if (reps < 1) reps = 1;
    uint64_t k = 0;
    double t0 = now_ns();
    for (size_t r = 0; r < reps; r++)
        k = fn(in->masks, 0, in->nblk, out_buf, 0);
    double t1 = now_ns();
    sink ^= k ^ out_buf[0] ^ out_buf[k ? k - 1 : 0];
    return (t1 - t0) / (double)(reps * in->nblk);
}

static void usage(void) {
    fprintf(stderr,
            "usage: paired-entry [--arms] [--rounds N] [--self-control]\n");
}

int main(int argc, char **argv) {
    int rounds = 11, arms = 0, self_control = 0;

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
        fprintf(stderr, "paired-entry: --rounds needs at least 3\n");
        return 2;
    }

    input *inputs = NULL;
    size_t ninputs = 0;
    if (arms) {
        inputs = xmalloc(6 * sizeof *inputs);
        arm_single(&inputs[ninputs++]);
        arm_group(&inputs[ninputs++]);
        arm_random(&inputs[ninputs++]);
        arm_empty(&inputs[ninputs++]);
        arm_full(&inputs[ninputs++]);
        arm_long(&inputs[ninputs++]);
    }
    if (ninputs == 0) {
        usage();
        return 2;
    }

    size_t biggest = 0;
    for (size_t i = 0; i < ninputs; i++)
        if (inputs[i].nblk > biggest) biggest = inputs[i].nblk;
    out_buf = xmalloc((64 * biggest + 8) * sizeof *out_buf);
    /* Touch every page of the buffer before anything is timed: the act that
       writes a page first takes its faults, and with the acts in rotated order
       that would be one side on some rounds and the other on others. */
    memset(out_buf, 0, (64 * biggest + 8) * sizeof *out_buf);

    /* The four acts, as (kernel name, measured, extracted) triples. */
    paired_entry_fn pairs[2][2] = {
        {probe_entry_measured_pos8, probe_entry_extracted_pos8},
        {probe_entry_measured_b8, probe_entry_extracted_b8},
    };
    static const char *kernel_names[2] = {"pos8", "b8"};

    /* One discarded pass over every input and every act, so the first measured
       round is not the one that warms the tables, the mask arrays and the
       core's frequency.  Without it the first input of a run -- `arm:single`,
       whose cost is a few nanoseconds -- reported a 25% difference between two
       identical bodies on a P core, because the measured act happened to draw
       the cold start on six of the eleven rounds. */
    for (size_t k = 0; k < ninputs; k++)
        for (int kern = 0; kern < 2; kern++) {
            run_act(pairs[kern][0], &inputs[k]);
            run_act(pairs[kern][1], &inputs[k]);
        }

    printf("core-class: %u\n", core_class());
    printf("rounds: %d\n", rounds);
    printf("self-control: %s\n", self_control ? "yes" : "no");
    printf("arms: single=64 group=256 random=%zu(seed=0x%llX) empty=1 full=1 "
           "long=1025\n",
           (size_t)ARM_RANDOM_COUNT, (unsigned long long)ARM_RANDOM_SEED);
    printf("%-14s %-6s %12s %12s %10s %10s\n", "input", "kernel", "measured",
           "extracted", "median", "spread");

    int failed = 0;
    for (size_t k = 0; k < ninputs; k++) {
        for (int kern = 0; kern < 2; kern++) {
            paired_entry_fn a = pairs[kern][0];
            paired_entry_fn b = self_control ? a : pairs[kern][1];
            double *d = xmalloc((size_t)rounds * sizeof *d);
            double *av = xmalloc((size_t)rounds * sizeof *av);
            double *bv = xmalloc((size_t)rounds * sizeof *bv);
            for (int r = 0; r < rounds; r++) {
                double x, y;
                if (a == b) {
                    x = run_act(a, &inputs[k]);
                    y = x;
                } else {
                    /* Each round runs both orders and averages each side, so a
                       drift inside the round -- another process arriving and
                       leaving, a frequency step -- lands on both acts and
                       cancels in the difference instead of deciding it.  The
                       round-to-round rotation is kept as well: the order the
                       round *starts* with alternates. */
                    double a1, a2, b1, b2;
                    if ((r & 1) == 0) {
                        a1 = run_act(a, &inputs[k]);
                        b1 = run_act(b, &inputs[k]);
                        b2 = run_act(b, &inputs[k]);
                        a2 = run_act(a, &inputs[k]);
                    } else {
                        b1 = run_act(b, &inputs[k]);
                        a1 = run_act(a, &inputs[k]);
                        a2 = run_act(a, &inputs[k]);
                        b2 = run_act(b, &inputs[k]);
                    }
                    x = 0.5 * (a1 + a2);
                    y = 0.5 * (b1 + b2);
                }
                av[r] = x;
                bv[r] = y;
                d[r] = y - x;
            }
            double ma = median(av, rounds);
            double mb = median(bv, rounds);
            double med = median(d, rounds);
            double spread = d[rounds - 1] - d[0];
            printf("%-14s %-6s %12.3f %12.3f %10.3f %10.3f\n", inputs[k].name,
                   kernel_names[kern], ma, mb, med, spread);
            if (self_control) {
                if (med != 0.0) {
                    fprintf(stderr, "FAIL: self-control reported %.6f, not 0.0\n", med);
                    failed = 1;
                }
            } else if (med > 0.5 || med < -0.5) {
                fprintf(stderr,
                        "FAIL: %s/%s: median difference %.3f ns/block is outside +/-0.5\n",
                        inputs[k].name, kernel_names[kern], med);
                failed = 1;
            }
            free(d);
            free(av);
            free(bv);
        }
    }
    if (self_control) {
        printf("ok: the harness reports 0.0 against itself\n");
    } else {
        printf("ok: every input and kernel is within +/-0.5 ns/block\n");
    }
    return failed ? 1 : 0;
}

#endif
