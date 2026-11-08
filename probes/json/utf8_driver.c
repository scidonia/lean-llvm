/* utf8_driver.c -- the UTF-8 route's object actor and its scalar reference.
 *
 * Two modes over the row list `probes/json/utf8_rows.h` enumerates:
 *
 *   [--corpus FILE]... [--arms] --ungated 0|1
 *       the object actor: stage each row's window, call `leanllvm_json_utf8`
 *       through the compiled object, print one line per row.
 *
 *   [--corpus FILE]... [--arms] --reference
 *       the scalar reference: print, for each row, the verdict computed here
 *       over the staged window and over the document alone.
 *
 * The row line is nine tab-separated columns, and the other two actors print
 * the same nine, so the three transcripts compare byte for byte:
 *
 *     <source> <label> <n> <gate> <path> <word> <skip> <eval> <padded>
 *
 * `source` is the corpus argument as given, or `arm:<arm>`; `label` is the
 * row's identity inside its source; `n` is the document's length in bytes;
 * `gate` is the gate value the row was run at and `path` the effective path
 * the actor used, in the same letters, `g` for the gated arm (the per-block
 * ASCII test) and `u` for the ungated one; `word` is the stage's error word,
 * `0` accepted and `1` rejected; `padded` is `n % 64 != 0`.
 *
 * `skip` and `eval` are **derived** from the staged window's bytes by
 * `utf8_skip.h`'s one function, not read out of the code under test: the
 * counts are the gate's only per-document trace, because the two arms' verdicts
 * are equal on every document of this matrix.  `skip + eval` is the block count
 * and the driver asserts that as it computes them.
 *
 * The reference mode prints, tab-separated,
 *
 *     <source> <label> <n> <window> <document>
 *
 * in the stage's units — `0` accepted, `1` rejected.  The predicate is the
 * valid-prefix one the stage's verdict is judged against: a concatenation of
 * complete RFC 3629 §4 characters, then at most one proper prefix of a
 * character, where a byte that can never begin a character is rejected even as
 * the last byte.  Its two forms read different byte strings and have different
 * jobs:
 *
 *   - the **window** form reads the staged window — three prefix bytes, the
 *     document, and zero padding to the 64-byte boundary the block count
 *     counts — which is what the DFA reads, so it is the expectation on every
 *     row;
 *   - the **document** form reads the document alone.  It disagrees with the
 *     window form exactly where the document ends inside a character, and
 *     `tests/json-utf8/check.sh` asserts each arm's disagreement count.
 *
 * The reference is written once, here, and not per actor: the Lean body's own
 * expectation is the specification's relation, so that comparison is between
 * two derivations rather than between a text and its copy.
 *
 * Exit status: 0 when every row was produced, 2 on a usage error, 3 when a
 * corpus file cannot be read or a row does not fit the staging buffer.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "utf8.h"
#include "utf8_rows.h"
#include "utf8_skip.h"

/* ------------------------------------------------------------ the reference -- */

/* 0 accepts, 1 rejects: the valid-prefix predicate over `doc`, for `n` bytes.
   A lead requires its continuations; a lead whose continuations are not all
   present is accepted, being a proper prefix of one character; and the range
   restriction is the lead's own first continuation (no overlong form, no
   encoded surrogate, nothing above U+10FFFF). */
static int ref_err(const uint8_t *doc, uint64_t n) {
    uint64_t i = 0;
    while (i < n) {
        uint8_t c = doc[i];
        uint64_t need;
        uint8_t lo, hi;
        if (c < 0x80) { i += 1; continue; }
        if (c >= 0xC2 && c <= 0xDF) { need = 1; lo = 0x80; hi = 0xBF; }
        else if (c >= 0xE0 && c <= 0xEF) {
            need = 2;
            lo = (c == 0xE0) ? 0xA0 : 0x80;
            hi = (c == 0xED) ? 0x9F : 0xBF;
        } else if (c >= 0xF0 && c <= 0xF4) {
            need = 3;
            lo = (c == 0xF0) ? 0x90 : 0x80;
            hi = (c == 0xF4) ? 0x8F : 0xBF;
        } else {
            return 1;
        }
        {
            uint64_t present = n - i - 1 < need ? n - i - 1 : need;
            for (uint64_t k = 1; k <= present; k++) {
                uint8_t d = doc[i + k];
                uint8_t a = (k == 1) ? lo : 0x80;
                uint8_t z = (k == 1) ? hi : 0xBF;
                if (d < a || d > z) return 1;
            }
            if (present < need) return 0;
        }
        i += 1 + need;
    }
    return 0;
}

/* -------------------------------------------------------------- the staging -- */

#define BLK_MAX 32u /* the block count a staged window holds, with slack */

static uint8_t win[3 + 64 * BLK_MAX];

/* Stage the window: three prefix bytes, the document, zeros to the boundary. */
static void stage_window(const uint8_t *p, const uint8_t *d, uint64_t n) {
    memset(win, 0, sizeof win);
    memcpy(win, p, 3);
    if (n) memcpy(win + 3, d, n);
}

/* ------------------------------------------------------------------ the row -- */

static int reference_mode;
static int ungated;

static void emit(void *ctx, const char *source, const char *label,
                 const uint8_t *p, const uint8_t *d, uint64_t n) {
    uint64_t nb = (n + 63) / 64;
    (void)ctx;
    if (n > UTF8_DOC_MAX || nb > BLK_MAX) {
        fprintf(stderr, "setup: %s/%s: n=%llu does not fit the staging buffer\n",
                source, label, (unsigned long long)n);
        exit(3);
    }
    stage_window(p, d, n);
    if (reference_mode) {
        printf("%s\t%s\t%llu\t%d\t%d\n", source, label, (unsigned long long)n,
               ref_err(win, 3 + 64 * nb), ref_err(d, n));
        return;
    }
    {
        uint64_t skip, eval, w = leanllvm_json_utf8(win + 3, n, ungated);
        utf8_block_counts(win + 3, n, ungated, &skip, &eval);
        if (skip + eval != nb) {
            fprintf(stderr, "setup: %s/%s: %llu + %llu blocks, %llu counted\n",
                    source, label, (unsigned long long)skip,
                    (unsigned long long)eval, (unsigned long long)nb);
            exit(3);
        }
        printf("%s\t%s\t%llu\t%c\t%c\t%llu\t%llu\t%llu\t%d\n", source, label,
               (unsigned long long)n, ungated ? 'u' : 'g', ungated ? 'u' : 'g',
               (unsigned long long)w, (unsigned long long)skip,
               (unsigned long long)eval, (n % 64) != 0);
    }
}

/* -------------------------------------------------------------------- main -- */

static void usage(void) {
    fprintf(stderr,
            "usage: utf8_driver [--corpus FILE]... [--arms] [--reference] "
            "[--ungated 0|1]\n"
            "  --corpus FILE  a four-column TSV: label, hex, n, expectation\n"
            "  --arms         generate the counted arms\n"
            "  --reference    print the scalar reference instead of the object's rows\n"
            "  --ungated N    0 gated, 1 ungated (default 0)\n");
}

int main(int argc, char **argv) {
    char *corpus[64];
    int ncorpus = 0, arms = 0, have_ungated = 0;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--corpus") == 0 && i + 1 < argc) {
            if (ncorpus == 64) { usage(); return 2; }
            corpus[ncorpus++] = argv[++i];
        } else if (strcmp(argv[i], "--arms") == 0) {
            arms = 1;
        } else if (strcmp(argv[i], "--reference") == 0) {
            reference_mode = 1;
        } else if (strcmp(argv[i], "--ungated") == 0 && i + 1 < argc) {
            char *v = argv[++i];
            if (strcmp(v, "0") == 0) { ungated = 0; have_ungated = 1; }
            else if (strcmp(v, "1") == 0) { ungated = 1; have_ungated = 1; }
            else { usage(); return 2; }
        } else {
            usage();
            return 2;
        }
    }
    if (reference_mode && have_ungated) {
        fprintf(stderr, "setup: --reference is over both gate values at once\n");
        return 2;
    }
    if (ncorpus == 0 && !arms) { usage(); return 2; }

    utf8_rows_run(ncorpus, corpus, arms, emit, NULL);
    return 0;
}
