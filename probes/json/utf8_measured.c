/* utf8_measured.c -- the UTF-8 route's measured actor.
 *
 * The route's third actor is not a copy of the unit and not a copy of the
 * statements: it is the measured `s1f_build2` itself, compiled from the
 * vendored headers at the measured `-D` set, over the same rows as the object
 * and the Lean body.  The stage is a region of that function's block loop
 * rather than a header function, so there is no symbol an include path could
 * swap; this translation unit includes `s1fuse.h` and calls the function.
 *
 * It prints the same nine columns as `utf8_driver.c`:
 *
 *     <source> <label> <n> <gate> <path> <word> <skip> <eval> <padded>
 *
 * `word` is `s1f_build2`'s `uerr`, in the same units (0 accepted, 1 rejected);
 * `skip` and `eval` are derived from the staged window's bytes by
 * `utf8_skip.h`'s one function, exactly as the driver derives them.
 *
 * **The gate, and why the build sets it.**  At this `-D` set `s1f_build2` calls
 * `dens_probe` and then `s1f_u8_decide` (`s1fuse.h:1622-1627`), so which arm a
 * document takes is decided per document from the sampled skip share — one row
 * would yield one arm and the other arm would never run.  Two builds close
 * that: `-DDENS_U8_FORCE=0` and `=1`, which `dens_pick_u8` honours by assigning
 * the constant (`dens.h:204-208`).  The knob alone is not enough, because
 * `dens_pick_u8` is reached only from `dens_probe`, which returns before it for
 * `nb = 0` (`dens.h:221-222`) — so every document under 64 bytes would keep the
 * static's default and a `=1` build would report the gated arm on 65,792 rows.
 * This file therefore calls `dens_pick_u8(0, 0, 0, 0)` before `s1f_build2`
 * under `#ifdef DENS_U8_FORCE`: that reaches the measured function's own
 * assignment, unconditionally, and `s1f_build2`'s `dens_probe` re-sets the same
 * constant for `nb ≥ 1`.  The call is inside the `#ifdef` because without the
 * define it would compute `0 < DENS_U8_SKIP_Q8` — the ungated arm — and change
 * the default build's behaviour; assigning the static directly is refused
 * because it would write state the measured function owns.
 *
 * `path` is the TU-static `s1f_u8_ungated` **read back after the call**, so the
 * field is the arm the measured code actually selected rather than the one this
 * file asked for.  `gate` is the build's forced value, printed as `u` for 1 and
 * `g` for 0; the two are equal on every row or the transcript is a setup fault,
 * which is what the route asserts.
 *
 * Nothing here reads a clock or a file: `--corpus` reads the committed TSV, and
 * `--arms` generates the counted arms from `utf8_rows.h`.
 *
 * Exit status: 0 when every row was produced, 2 on a usage error, 3 when a
 * corpus file cannot be read or a row does not fit the staging buffer.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "s1fuse.h"

#include "utf8_rows.h"
#include "utf8_skip.h"

#define BLK_MAX 32u

static uint8_t win[3 + 64 * BLK_MAX];
static uint32_t out[64 * BLK_MAX + 16];

/* The gate this build forces, as the row's letter. */
static char build_gate(void) {
#if defined(DENS_U8_FORCE) && DENS_U8_FORCE
    return 'u';
#else
    return 'g';
#endif
}

static void emit(void *ctx, const char *source, const char *label,
                 const uint8_t *p, const uint8_t *d, uint64_t n) {
    uint64_t nb = (n + 63) / 64, skip, eval, uerr = 0;
    int path;
    (void)ctx;
    if (n > UTF8_DOC_MAX || nb > BLK_MAX) {
        fprintf(stderr, "setup: %s/%s: n=%llu does not fit the staging buffer\n",
                source, label, (unsigned long long)n);
        exit(3);
    }
    memset(win, 0, sizeof win);
    memcpy(win, p, 3);
    if (n) memcpy(win + 3, d, n);
#ifdef DENS_U8_FORCE
    dens_pick_u8(0, 0, 0, 0);
#endif
    s1f_build2(win + 3, n, out, &uerr);
    path = s1f_u8_ungated;
    utf8_block_counts(win + 3, n, path, &skip, &eval);
    if (skip + eval != nb) {
        fprintf(stderr, "setup: %s/%s: %llu + %llu blocks, %llu counted\n",
                source, label, (unsigned long long)skip,
                (unsigned long long)eval, (unsigned long long)nb);
        exit(3);
    }
    if (uerr > 1) {
        fprintf(stderr, "setup: %s/%s: uerr=%llu, which the stage cannot return\n",
                source, label, (unsigned long long)uerr);
        exit(3);
    }
    printf("%s\t%s\t%llu\t%c\t%c\t%llu\t%llu\t%llu\t%d\n", source, label,
           (unsigned long long)n, build_gate(), path ? 'u' : 'g',
           (unsigned long long)uerr, (unsigned long long)skip,
           (unsigned long long)eval, (n % 64) != 0);
}

static void usage(void) {
    fprintf(stderr, "usage: utf8_measured [--corpus FILE]... [--arms]\n"
                    "  --corpus FILE  a four-column TSV: label, hex, n, expectation\n"
                    "  --arms         generate the counted arms\n");
}

int main(int argc, char **argv) {
    char *corpus[64];
    int ncorpus = 0, arms = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--corpus") == 0 && i + 1 < argc) {
            if (ncorpus == 64) { usage(); return 2; }
            corpus[ncorpus++] = argv[++i];
        } else if (strcmp(argv[i], "--arms") == 0) {
            arms = 1;
        } else {
            usage();
            return 2;
        }
    }
    if (ncorpus == 0 && !arms) { usage(); return 2; }

    utf8_rows_run(ncorpus, corpus, arms, emit, NULL);
    return 0;
}
