/* init_guard_check.c -- the POS8 table's initialisation dependency, both ways.
 *
 * `leanllvm_json_entry_pos8` reads the entry unit's file-static `xl_pos8`
 * table, which only `leanllvm_json_entry_table` fills.  The pipeline does not
 * call the initialiser, so a caller that selects arm bit 0 clear without
 * calling it first is breaking a contract the header states.  The table is
 * zero-initialised, so the emitter would otherwise write a well-formed but
 * wrong position stream and the caller would get a plausible answer.
 *
 * This probe makes the two outcomes observable:
 *
 *   initialised  fill the table, run the pipeline twice on the same staged
 *                document -- arm 0 (pos8) and arm 1 (b8) -- and require both to
 *                accept and to write the same entry stream.  That is the
 *                initialised path unchanged: pos8's stream is b8's, which
 *                reads no table.
 *   bare         call the pipeline with arm 0 and no initialisation.  The
 *                emitter must trap before it can return, so the process dies
 *                by SIGILL and this program prints nothing.  If it returns,
 *                the probe prints the result and exits 1: a guard that did not
 *                fire is the defect, not a row.
 *   b8-bare      call the pipeline with arm 1 and no initialisation.  B8 reads
 *                no table, so it must accept; this is the control that the
 *                trap in `bare` is the pos8 table's check and not some
 *                unrelated startup failure.
 *
 * The staging is `driver.c`'s: three zero prefix bytes, the document, and 64
 * bytes per block of padding, so the mask unit's unconditional 64-byte reads
 * stay inside the window.  Exit status: 0 when the mode's expectation holds, 1
 * when it does not, 3 on a setup fault (an allocation that failed).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "entry.h"
#include "pipeline.h"

/* The document is a small accepted one; the outcome under test is the table's,
   not the document class's.  Five bytes, one block. */
static const uint8_t document[] = "[1,2]";
#define DOC_LEN ((uint64_t)(sizeof document - 1))

typedef struct {
    uint64_t verdict, nk, nxp, ndst, nev, err;
    uint32_t *ep;
} observation;

static void observation_free(observation *o) {
    free(o->ep);
    memset(o, 0, sizeof *o);
}

/* One pipeline call over the fixed document, at `arm`, with the table filled
   first when `initialise` is non-zero.  Returns 0, or -1 when an allocation
   failed. */
static int run(uint64_t arm, int initialise, observation *out) {
    const uint64_t n = DOC_LEN;
    const uint64_t nb = (n + 63) / 64;
    const uint64_t epcap = 64 * nb + 9, xpcap = 64 * nb + 8;
    const uint64_t dstcap = n + 64, evcap = 13 * n + 128;
    const uint64_t winlen = 3 + 64 * nb + 32;

    memset(out, 0, sizeof *out);
    uint8_t *win = (uint8_t *)calloc(winlen, 1);
    uint8_t *sc = (uint8_t *)calloc(24, 1);
    uint8_t *mk = (uint8_t *)calloc(48, 1);
    uint8_t *entw = (uint8_t *)calloc(8, 1);
    uint32_t *ep = (uint32_t *)calloc(4 * epcap, 1);
    uint64_t *nk = (uint64_t *)calloc(8, 1);
    uint32_t *xp = (uint32_t *)calloc(4 * xpcap, 1);
    uint64_t *nxp = (uint64_t *)calloc(8, 1);
    uint8_t *xcarry = (uint8_t *)calloc(16, 1);
    uint8_t *dst = (uint8_t *)calloc(dstcap, 1);
    uint64_t *ndst = (uint64_t *)calloc(8, 1);
    uint8_t *ev = (uint8_t *)calloc(evcap, 1);
    uint64_t *nev = (uint64_t *)calloc(8, 1);
    uint64_t *err = (uint64_t *)calloc(8, 1);
    int ok = win && sc && mk && entw && ep && nk && xp && nxp && xcarry &&
             dst && ndst && ev && nev && err;
    if (ok) {
        memcpy(win + 3, document, (size_t)n);
        if (initialise) {
            static uint32_t table[256 * 8];
            leanllvm_json_entry_table(table);
        }
        out->verdict = leanllvm_json_pipeline(
            win + 3, n, (uint64_t *)sc, (uint64_t *)mk, (uint64_t *)entw,
            ep, epcap, nk, xp, xpcap, nxp, (uint64_t *)xcarry,
            dst, dstcap, ndst, ev, evcap, nev, err, arm);
        out->nk = *nk;
        out->nxp = *nxp;
        out->ndst = *ndst;
        out->nev = *nev;
        out->err = *err;
        out->ep = ep;
    }
    free(win);
    free(sc);
    free(mk);
    free(entw);
    free(nk);
    free(xp);
    free(nxp);
    free(xcarry);
    free(dst);
    free(ndst);
    free(ev);
    free(nev);
    free(err);
    if (!ok) {
        free(ep);
        return -1;
    }
    return 0;
}

static int initialised(void) {
    observation pos8, b8;
    if (run(0, 1, &pos8) != 0 || run(1, 1, &b8) != 0) {
        fprintf(stderr, "SETUP: a staging allocation failed\n");
        return 3;
    }
    int same = pos8.verdict == b8.verdict && pos8.nk == b8.nk &&
               pos8.nk <= UINT64_MAX / 4 &&
               memcmp(pos8.ep, b8.ep, (size_t)(pos8.nk * 4)) == 0;
    printf("pos8 verdict=%llu nk=%llu b8 verdict=%llu nk=%llu streams=%s\n",
           (unsigned long long)pos8.verdict, (unsigned long long)pos8.nk,
           (unsigned long long)b8.verdict, (unsigned long long)b8.nk,
           same ? "identical" : "different");
    int ok = pos8.verdict == 1 && b8.verdict == 1 && same && pos8.nk > 0;
    observation_free(&pos8);
    observation_free(&b8);
    return ok ? 0 : 1;
}

static int bare(void) {
    observation pos8;
    if (run(0, 0, &pos8) != 0) {
        fprintf(stderr, "SETUP: a staging allocation failed\n");
        return 3;
    }
    printf("UNGUARDED pos8 verdict=%llu nk=%llu nxp=%llu ndst=%llu nev=%llu err=%llu\n",
           (unsigned long long)pos8.verdict, (unsigned long long)pos8.nk,
           (unsigned long long)pos8.nxp, (unsigned long long)pos8.ndst,
           (unsigned long long)pos8.nev, (unsigned long long)pos8.err);
    fprintf(stderr,
            "FAIL: the pos8 pipeline returned without the entry table "
            "initialised\n");
    observation_free(&pos8);
    return 1;
}

static int b8_bare(void) {
    observation b8;
    if (run(1, 0, &b8) != 0) {
        fprintf(stderr, "SETUP: a staging allocation failed\n");
        return 3;
    }
    printf("b8 verdict=%llu nk=%llu err=%llu\n",
           (unsigned long long)b8.verdict, (unsigned long long)b8.nk,
           (unsigned long long)b8.err);
    int ok = b8.verdict == 1 && b8.nk > 0;
    observation_free(&b8);
    return ok ? 0 : 1;
}

int main(int argc, char **argv) {
    if (argc == 2) {
        if (strcmp(argv[1], "initialised") == 0) return initialised();
        if (strcmp(argv[1], "bare") == 0) return bare();
        if (strcmp(argv[1], "b8-bare") == 0) return b8_bare();
    }
    fprintf(stderr,
            "usage: init_guard_check initialised|bare|b8-bare\n");
    return 3;
}
