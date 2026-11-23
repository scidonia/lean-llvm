/* guard_check.c -- the escape-list arm's equivalence check: stage 2 with the
 * list against stage 2 without it.
 *
 * Stage 1's escape-position list is an input to the decoding route, not to the
 * verdict.  A list-free call classifies each string body by scanning its own
 * span and decodes it with the escape unit's list-free decoder, so the two arms
 * must produce the same consumer-observable output on every document:
 *
 *   * for every document, the pipeline is called twice on the same bytes with
 *     the same staging -- once with arm 2 (the list) and once with arm 0 (no
 *     list) -- and the two results are compared field for field: the verdict,
 *     the entry cursor, the arena and event extents, the error offset, the
 *     arena bytes and the event bytes.  The escape-list count is stage 1's
 *     output and is reported, not compared;
 *   * the list is nevertheless checked as the document fact it is: where the
 *     guard fires (no backslash and no byte at or below `0x1F`), the arm-2 list
 *     must be empty;
 *   * the comparison's own control is `guard.sh`'s defect build, not a property
 *     of the corpus: a stage 2 whose list-free arm returns the input span
 *     without validating it must make arm 0 disagree with arm 2 on the
 *     escape-bearing rows.  A comparison that cannot see that build differ
 *     would be an equality over nothing.
 *
 * A row prints `<source> <label> n=<n> guard=<0|1> nxp=<arm-2 count>
 * identical=<0|1>`, and the last line is the summary.  Exit status: 0 when
 * every row holds, 1 when one does not, 3 on a setup fault (an unreadable file,
 * a bad hex row, an allocation that failed).
 *
 * The probe stages the document exactly as `driver.c` and the route do -- the
 * three zero prefix bytes, the document, and 64 bytes per block of padding, so
 * the mask unit's unconditional 64-byte reads stay inside the buffer -- and
 * fills the entry unit's POS8 table once before the first call.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "escape_guard.h"
#include "pipeline.h"
#include "entry.h"

/* One call's observable result.  `dst` and `ev` point into the buffers the
   call wrote, owned by the caller of `run`. */
typedef struct {
    uint64_t verdict, nk, nxp, ndst, nev, err;
    uint8_t *dst, *ev;
    uint32_t *ep, *xp;
} result;

static void result_free(result *r) {
    free(r->ep);
    free(r->xp);
    free(r->dst);
    free(r->ev);
    memset(r, 0, sizeof *r);
}

/* The pipeline over one document at one arm word, in the route's capacities.
   Returns 0, or -1 when an allocation failed; every buffer is fresh, so the
   two calls of a comparison share no state. */
static int run(const uint8_t *doc, uint64_t n, uint64_t arm, result *out) {
    memset(out, 0, sizeof *out);
    uint64_t nb = n / 64 + (n % 64 != 0);
    uint64_t epcap = 64 * nb + 9, xpcap = 64 * nb + 8;
    uint64_t dstcap = n + 64, evcap = 13 * n + 128;
    uint64_t winlen = 3 + 64 * nb + 32;

    uint8_t *win = (uint8_t *)calloc(winlen ? winlen : 1, 1);
    uint64_t *sc = (uint64_t *)calloc(24, 1);
    uint64_t *mk = (uint64_t *)calloc(48, 1);
    uint64_t *entw = (uint64_t *)calloc(8, 1);
    uint32_t *ep = (uint32_t *)calloc(4 * epcap, 1);
    uint64_t *nk = (uint64_t *)calloc(8, 1);
    uint32_t *xp = (uint32_t *)calloc(4 * xpcap, 1);
    uint64_t *nxp = (uint64_t *)calloc(8, 1);
    uint64_t *xcarry = (uint64_t *)calloc(16, 1);
    uint8_t *dst = (uint8_t *)calloc(dstcap, 1);
    uint64_t *ndst = (uint64_t *)calloc(8, 1);
    uint8_t *ev = (uint8_t *)calloc(evcap, 1);
    uint64_t *nev = (uint64_t *)calloc(8, 1);
    uint64_t *err = (uint64_t *)calloc(8, 1);
    int ok = win && sc && mk && entw && ep && nk && xp && nxp && xcarry && dst &&
             ndst && ev && nev && err;
    if (ok) {
        if (n) memcpy(win + 3, doc, (size_t)n);
        out->verdict = leanllvm_json_pipeline(
            win + 3, n, sc, mk, entw, ep, epcap, nk, xp, xpcap, nxp, xcarry,
            dst, dstcap, ndst, ev, evcap, nev, err, arm);
        out->nk = *nk;
        out->nxp = *nxp;
        out->ndst = *ndst;
        out->nev = *nev;
        out->err = *err;
        out->dst = dst;
        out->ev = ev;
        out->ep = ep;
        out->xp = xp;
    }
    free(win);
    free(sc);
    free(mk);
    free(entw);
    free(nk);
    free(nxp);
    free(xcarry);
    free(ndst);
    free(nev);
    free(err);
    if (!ok) {
        free(ep);
        free(xp);
        free(dst);
        free(ev);
        return -1;
    }
    return 0;
}

/* 1 when the two calls' consumer-observable results are identical, field for
   field and byte for byte: the verdict, the entry cursor, the arena and event
   extents, the refusal offset, and both payloads.  The escape-list count is
   not compared: it is stage 1's output, and the list-free arm leaves it zero
   by construction. */
static int identical(const result *a, const result *b) {
    /* The list is stage 1's output, not a consumer-observable: arm 0 leaves
       nxp zero by construction.  Everything the call reports after stage 2 —
       the verdict, the entry cursor, the arena and event extents, the refusal
       offset and both payloads — must be the same whether the list was built
       or the bodies were rescanned. */
    if (a->verdict != b->verdict || a->nk != b->nk ||
        a->ndst != b->ndst || a->nev != b->nev || a->err != b->err)
        return 0;
    if (a->ndst && memcmp(a->dst, b->dst, (size_t)a->ndst) != 0) return 0;
    if (a->nev && memcmp(a->ev, b->ev, (size_t)a->nev) != 0) return 0;
    return 1;
}

/* The first field the two results disagree in, for the diagnostic. */
static const char *first_difference(const result *a, const result *b) {
    if (a->verdict != b->verdict) return "verdict";
    if (a->nk != b->nk) return "nk";
    if (a->ndst != b->ndst) return "ndst";
    if (a->nev != b->nev) return "nev";
    if (a->err != b->err) return "err";
    if (a->ndst && memcmp(a->dst, b->dst, (size_t)a->ndst) != 0) return "arena";
    if (a->nev && memcmp(a->ev, b->ev, (size_t)a->nev) != 0) return "events";
    return "none";
}

static int hexval(int c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* Decode the corpus's lowercase-hex document form, which `-` spells as the
   empty document.  Returns 0 and the bytes, or -1 on a malformed row. */
static int decode_hex(const char *hex, uint8_t **out, uint64_t *n) {
    if (strcmp(hex, "-") == 0) {
        *out = (uint8_t *)calloc(1, 1);
        *n = 0;
        return *out ? 0 : -1;
    }
    size_t len = strlen(hex);
    if (len % 2 != 0) return -1;
    uint8_t *p = (uint8_t *)calloc(len / 2 ? len / 2 : 1, 1);
    if (!p) return -1;
    for (size_t i = 0; i < len; i += 2) {
        int hi = hexval((unsigned char)hex[i]);
        int lo = hexval((unsigned char)hex[i + 1]);
        if (hi < 0 || lo < 0) {
            free(p);
            return -1;
        }
        p[i / 2] = (uint8_t)((hi << 4) | lo);
    }
    *out = p;
    *n = len / 2;
    return 0;
}

static uint64_t rows_compared, rows_fired, rows_with_list;

/* One document's comparison: arm 0 (stage 1 emits no list; stage 2 rescans each
   body) against arm 2 (the stage-1 list), on the consumer-observable output.
   Returns 0 when the row holds and 1 when it does not; the diagnostic is on
   stderr. */
static int check_row(const char *source, const char *label, const uint8_t *doc,
                     uint64_t n) {
    int skip = leanllvm_route_escape_can_skip(doc, n);
    result arm2, rescan;
    if (run(doc, n, 2, &arm2) != 0 || run(doc, n, 0, &rescan) != 0) {
        fprintf(stderr, "SETUP: %s: an allocation failed\n", label);
        return 3;
    }
    int same = identical(&arm2, &rescan);

    rows_compared++;
    if (skip) rows_fired++;
    if (arm2.nxp) rows_with_list++;

    printf("%s %s n=%llu guard=%d nxp=%llu identical=%d\n", source, label,
           (unsigned long long)n, skip, (unsigned long long)arm2.nxp, same);

    int bad = 0;
    if (!same) {
        fprintf(stderr,
                "FAIL: %s: arm 0 and arm 2 differ (first field %s; arm-2 list "
                "%llu entries)\n",
                label, first_difference(&arm2, &rescan),
                (unsigned long long)arm2.nxp);
        bad = 1;
    }
    if (skip && arm2.nxp != 0) {
        fprintf(stderr,
                "FAIL: %s: the guard fired and the arm-2 list is not empty "
                "(%llu entries)\n",
                label, (unsigned long long)arm2.nxp);
        bad = 1;
    }
    result_free(&arm2);
    result_free(&rescan);
    return bad;
}

int main(int argc, char **argv) {
    uint32_t *tab = (uint32_t *)calloc(2048, 4);
    if (!tab) {
        fprintf(stderr, "SETUP: the entry table's slot could not be allocated\n");
        return 3;
    }
    leanllvm_json_entry_table(tab);
    free(tab);

    int status = 0;
    if (argc == 4 && strcmp(argv[1], "--hex") == 0) {
        /* The escape corpus's row form: one label and its hex bytes.  The row's
           source is the corpus the caller reads the row from. */
        uint8_t *doc = NULL;
        uint64_t n = 0;
        if (decode_hex(argv[3], &doc, &n) != 0) {
            fprintf(stderr, "SETUP: --hex needs an even-length hex string or -: %s\n",
                    argv[3]);
            return 3;
        }
        status = check_row("hex", argv[2], doc, n);
        free(doc);
    } else if (argc == 2) {
        FILE *f = fopen(argv[1], "rb");
        if (!f) {
            fprintf(stderr, "SETUP: cannot read %s\n", argv[1]);
            return 3;
        }
        fseek(f, 0, SEEK_END);
        long sz = ftell(f);
        fseek(f, 0, SEEK_SET);
        if (sz < 0) {
            fclose(f);
            fprintf(stderr, "SETUP: cannot size %s\n", argv[1]);
            return 3;
        }
        uint8_t *doc = (uint8_t *)calloc((size_t)sz ? (size_t)sz : 1, 1);
        if (!doc) {
            fclose(f);
            fprintf(stderr, "SETUP: cannot allocate %ld bytes\n", sz);
            return 3;
        }
        if (sz && fread(doc, 1, (size_t)sz, f) != (size_t)sz) {
            fclose(f);
            free(doc);
            fprintf(stderr, "SETUP: cannot read %s\n", argv[1]);
            return 3;
        }
        fclose(f);
        /* The label is the file name; the source is the file path. */
        const char *label = strrchr(argv[1], '/');
        label = label ? label + 1 : argv[1];
        status = check_row("file", label, doc, (uint64_t)sz);
        free(doc);
    } else {
        fprintf(stderr, "usage: guard_check <file>\n"
                        "       guard_check --hex <label> <hex-or->\n");
        return 3;
    }
    fprintf(stderr, "summary rows_compared=%llu rows_fired=%llu "
            "rows_with_list=%llu status=%d\n",
           (unsigned long long)rows_compared,
           (unsigned long long)rows_fired,
           (unsigned long long)rows_with_list, status);
    return status;
}
