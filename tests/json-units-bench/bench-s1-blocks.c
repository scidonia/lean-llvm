/* bench-s1-blocks.c -- the contracted block unit at its own ABI, v1 against v2.

   The v1 shape is `tests/json-units-bench/s1_blocks_v1.c` (the probe-only body
   frozen at 64c3efe) followed, when the document is not all ASCII, by the
   separate `leanllvm_json_utf8` call at `arm`'s bit 2 — which is what the
   pipeline does with the v1 unit.  The v2 shape is the current
   `kernel/json/s1_blocks.c`, whose loop carries the UTF-8 DFA and whose return
   word is `ascii | (utf8_error << 1)`.

   Both are called at the same boundary: the document staged at offset four of a
   zeroed buffer (the three bytes before it zero), the caller's `ent` array, the
   escape stream and its cursor, and the carry pair reset before every pass.
   `arm` is one of 0, 2, 4, 6: bit 1 the escape list, bit 2 the ungated UTF-8
   gate.  Before a row is timed the two actors must agree on the entry words,
   the escape stream, the carry pair and the two return bits; a disagreement
   exits 3 rather than producing a number.

   The driver prints one row per (document, arm, actor) and one paired ratio
   row.  Times are the median of `--rounds` round medians of `--reps`
   repetitions, in ns/byte; the ratio is the fused row over the v1 row in the
   same round.  This is a bench-only file; it is not part of any route. */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern uint64_t leanllvm_json_s1_blocks_v1(const uint8_t *b, uint64_t n,
                                           uint64_t *ent, uint32_t *xp,
                                           uint64_t *nxp, uint64_t *xcarry,
                                           uint64_t arm);
extern uint64_t leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n,
                                        uint64_t *ent, uint32_t *xp,
                                        uint64_t *nxp, uint64_t *xcarry,
                                        uint64_t arm);
extern uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated);

#define DOC_OFFSET 4

typedef struct {
    const char *name;
    uint8_t *base;
    uint64_t n;
    uint64_t blocks;
    uint64_t *ent1, *ent2;
    uint32_t *xp1, *xp2;
    size_t xp_cap;
} Doc;

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

static uint64_t blocks_of(uint64_t n) { return (n + 63) / 64; }

static int cmp_u64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y ? 1 : 0;
}

static uint64_t median(uint64_t *v, int n) {
    qsort(v, (size_t)n, sizeof *v, cmp_u64);
    return (n & 1) ? v[n / 2] : (v[n / 2 - 1] + v[n / 2]) / 2;
}

/* The two actors' full observable boundary, compared before timing.  The v1
   composite is the probe followed, on a non-ASCII document, by the separate
   unit at `arm`'s bit 2 — what `pipeline.c` does with the v1 unit. */
static void gate(Doc *d, int *bad) {
    for (uint64_t arm = 0; arm < 8; arm += 2) {
        uint64_t nxp1 = 0, nxp2 = 0, xc1[2] = {0, 0}, xc2[2] = {0, 0};
        memset(d->ent1, 0xA5, (size_t)(8 * d->blocks));
        memset(d->ent2, 0xA5, (size_t)(8 * d->blocks));
        memset(d->xp1, 0xA5, d->xp_cap);
        memset(d->xp2, 0xA5, d->xp_cap);
        uint64_t r1 = leanllvm_json_s1_blocks_v1(d->base + DOC_OFFSET, d->n,
                                                 d->ent1, d->xp1, &nxp1, xc1, arm);
        uint64_t err = (r1 & 1) ? 0
            : leanllvm_json_utf8(d->base + DOC_OFFSET, d->n, (int)((arm >> 2) & 1));
        uint64_t w1 = (r1 & 1) | (err << 1);
        uint64_t w2 = leanllvm_json_s1_blocks(d->base + DOC_OFFSET, d->n,
                                              d->ent2, d->xp2, &nxp2, xc2, arm);
        if (w1 != w2) {
            fprintf(stderr, "gate: %s arm=%llu word %llu against %llu\n",
                    d->name, (unsigned long long)arm,
                    (unsigned long long)w1, (unsigned long long)w2);
            *bad = 1;
        }
        if (memcmp(d->ent1, d->ent2, (size_t)(8 * d->blocks)) != 0) {
            fprintf(stderr, "gate: %s arm=%llu entry words differ\n",
                    d->name, (unsigned long long)arm);
            *bad = 1;
        }
        if (nxp1 != nxp2 || xc1[0] != xc2[0] || xc1[1] != xc2[1]) {
            fprintf(stderr, "gate: %s arm=%llu cursor/carry differ\n",
                    d->name, (unsigned long long)arm);
            *bad = 1;
        }
        if (memcmp(d->xp1, d->xp2, d->xp_cap) != 0) {
            fprintf(stderr, "gate: %s arm=%llu escape stream differs\n",
                    d->name, (unsigned long long)arm);
            *bad = 1;
        }
    }
}

static int load_doc(const char *path, Doc *d) {
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "bench-s1-blocks: cannot read %s\n", path); return 1; }
    if (fseek(f, 0, SEEK_END) != 0) { fclose(f); return 1; }
    long sz = ftell(f);
    if (sz < 0 || fseek(f, 0, SEEK_SET) != 0) { fclose(f); return 1; }
    d->n = (uint64_t)sz;
    d->blocks = blocks_of(d->n);
    d->base = calloc(1, (size_t)(DOC_OFFSET + 64 * d->blocks));
    d->ent1 = malloc((size_t)(8 * d->blocks));
    d->ent2 = malloc((size_t)(8 * d->blocks));
    d->xp_cap = (size_t)(4 * (64 * d->blocks + 8));
    d->xp1 = malloc(d->xp_cap);
    d->xp2 = malloc(d->xp_cap);
    if (!d->base || !d->ent1 || !d->ent2 || !d->xp1 || !d->xp2) return 1;
    if (d->n && fread(d->base + DOC_OFFSET, 1, (size_t)d->n, f) != d->n) {
        fclose(f); return 1;
    }
    fclose(f);
    d->name = path;
    return 0;
}

int main(int argc, char **argv) {
    int rounds = 9, reps = 31, no_check = 0, ndocs = 0;
    Doc docs[16];
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--rounds") && i + 1 < argc) rounds = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--reps") && i + 1 < argc) reps = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--no-check")) no_check = 1;
        else if (argv[i][0] == '-') {
            fprintf(stderr, "bench-s1-blocks: bad argument %s\n", argv[i]);
            return 2;
        } else {
            if (ndocs >= 16) return 2;
            if (load_doc(argv[i], &docs[ndocs++]) != 0) return 3;
        }
    }
    if (ndocs == 0) { fprintf(stderr, "bench-s1-blocks: no documents\n"); return 2; }

    if (!no_check) {
        int bad = 0;
        for (int i = 0; i < ndocs; i++) gate(&docs[i], &bad);
        if (bad) return 3;
    }

    printf("instrument bench=s1-blocks rounds=%d reps=%d\n", rounds, reps);
    for (int di = 0; di < ndocs; di++) {
        Doc *d = &docs[di];
        printf("doc name=%s bytes=%llu blocks=%llu\n", d->name,
               (unsigned long long)d->n, (unsigned long long)d->blocks);
        for (uint64_t arm = 0; arm < 8; arm += 2) {
            uint64_t *v1 = calloc((size_t)rounds, sizeof *v1);
            uint64_t *v2 = calloc((size_t)rounds, sizeof *v2);
            uint64_t checksum = 0;
            for (int r = 0; r < rounds; r++) {
                uint64_t t = now_ns();
                for (int k = 0; k < reps; k++) {
                    uint64_t nxp = 0, xc[2] = {0, 0};
                    uint64_t w = leanllvm_json_s1_blocks_v1(
                        d->base + DOC_OFFSET, d->n, d->ent1, d->xp1, &nxp, xc, arm);
                    uint64_t err = (w & 1) ? 0
                        : leanllvm_json_utf8(d->base + DOC_OFFSET, d->n,
                                             (int)((arm >> 2) & 1));
                    checksum ^= d->ent1[k % (int)(d->blocks ? d->blocks : 1)] ^
                                (w | (err << 1)) ^ nxp;
                }
                v1[r] = now_ns() - t;
                t = now_ns();
                for (int k = 0; k < reps; k++) {
                    uint64_t nxp = 0, xc[2] = {0, 0};
                    uint64_t w = leanllvm_json_s1_blocks(
                        d->base + DOC_OFFSET, d->n, d->ent2, d->xp2, &nxp, xc, arm);
                    checksum ^= d->ent2[k % (int)(d->blocks ? d->blocks : 1)] ^ w ^ nxp;
                }
                v2[r] = now_ns() - t;
            }
            uint64_t m1 = median(v1, rounds), m2 = median(v2, rounds);
            printf("row doc=%s arm=%llu actor=v1 ns=%llu ns_per_byte=%.6f "
                   "cycles_per_byte=%.4f checksum=0x%llx\n",
                   d->name, (unsigned long long)arm, (unsigned long long)m1,
                   (double)m1 / (double)(reps * d->n),
                   (double)m1 / (double)(reps * d->n), (unsigned long long)checksum);
            printf("row doc=%s arm=%llu actor=v2 ns=%llu ns_per_byte=%.6f "
                   "cycles_per_byte=%.4f checksum=0x%llx\n",
                   d->name, (unsigned long long)arm, (unsigned long long)m2,
                   (double)m2 / (double)(reps * d->n),
                   (double)m2 / (double)(reps * d->n), (unsigned long long)checksum);
            printf("ratio doc=%s arm=%llu v2_over_v1=%.6f\n", d->name,
                   (unsigned long long)arm, (double)m2 / (double)m1);
            free(v1);
            free(v2);
        }
    }
    return 0;
}
