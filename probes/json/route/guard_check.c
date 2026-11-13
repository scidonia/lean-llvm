/* guard_check.c -- the escape-list guard's equivalence check and its control.
 *
 * `escape_guard.h` claims a fact about the document: with no backslash byte and
 * no byte at or below `0x1F`, the stage-1 escape list arm 2 builds is empty on
 * every block, so the pipeline's arm bit 1 can be cleared.  "The list is empty"
 * is what the claim rests on and it is checked here rather than assumed:
 *
 *   * for every document, the pipeline is called twice on the same bytes with
 *     the same staging -- once with arm 2 and once with the arm the guard
 *     selects -- and the two results are compared field for field: the verdict,
 *     the four cursors, the error offset, the arena bytes and the event bytes;
 *   * where the guard fires, the observation's `nxp` must be zero and the two
 *     results must be byte-identical, so the claim is the list's own emptiness
 *     and not a coincidence of the two arms' reporting;
 *   * the control runs arm 0 on a document whose arm-2 list is not empty, and
 *     must see the results diverge: a guard whose forced decision changes
 *     nothing would be indistinguishable from a guard that never fires.
 *
 * A row prints `<source> <label> n=<n> guard=<0|1> nxp=<arm-2 count>
 * identical=<0|1> control=<none|fired>`, and the last line is the summary the
 * caller asserts its controls on.  Exit status: 0 when every row holds, 1 when
 * one does not, 3 on a setup fault (an unreadable file, a bad hex row, an
 * allocation that failed).
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

/* 1 when the two calls' observable results are identical, field for field and
   byte for byte.  A difference in any cursor is a difference even where the
   payloads happen to agree: the cursor is what stage 2 was told the list
   length was. */
static int identical(const result *a, const result *b) {
    if (a->verdict != b->verdict || a->nk != b->nk || a->nxp != b->nxp ||
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
    if (a->nxp != b->nxp) return "nxp";
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

static uint64_t rows_compared, rows_fired, rows_with_list, controls_fired;

/* One document's comparison, the claim and the control.  Returns 0 when the
   row holds and 1 when it does not; the diagnostic is on stderr. */
static int check_row(const char *source, const char *label, const uint8_t *doc,
                     uint64_t n) {
    int skip = leanllvm_route_escape_can_skip(doc, n);
    result arm2, guarded;
    if (run(doc, n, 2, &arm2) != 0 || run(doc, n, skip ? 0 : 2, &guarded) != 0) {
        fprintf(stderr, "SETUP: %s: an allocation failed\n", label);
        return 3;
    }
    int same = identical(&arm2, &guarded);
    int control = 0; /* 0 = none, 1 = fired */
    result forced;
    int have_forced = 0;
    if (arm2.nxp) {
        if (run(doc, n, 0, &forced) != 0) {
            fprintf(stderr, "SETUP: %s: an allocation failed\n", label);
            result_free(&arm2);
            result_free(&guarded);
            return 3;
        }
        have_forced = 1;
        control = identical(&arm2, &forced) ? 0 : 1;
    }

    rows_compared++;
    if (skip) rows_fired++;
    if (arm2.nxp) rows_with_list++;
    if (control) controls_fired++;

    printf("%s %s n=%llu guard=%d nxp=%llu identical=%d control=%s\n", source,
           label, (unsigned long long)n, skip, (unsigned long long)arm2.nxp,
           same, control ? "fired" : (have_forced ? "absent" : "none"));

    int bad = 0;
    if (skip && !same) {
        fprintf(stderr,
                "FAIL: %s: the guard fired and the arms differ (first field "
                "%s; nxp %llu against %llu)\n",
                label, first_difference(&arm2, &guarded),
                (unsigned long long)arm2.nxp,
                (unsigned long long)guarded.nxp);
        bad = 1;
    }
    if (skip && arm2.nxp != 0) {
        fprintf(stderr,
                "FAIL: %s: the guard fired and the arm-2 list is not empty "
                "(%llu entries)\n",
                label, (unsigned long long)arm2.nxp);
        bad = 1;
    }
    if (!skip && arm2.nxp && !control) {
        fprintf(stderr,
                "FAIL: %s: the control did not fire (arm 0 and arm 2 agree on "
                "a document whose arm-2 list holds %llu entries)\n",
                label, (unsigned long long)arm2.nxp);
        bad = 1;
    }
    if (have_forced) result_free(&forced);
    result_free(&arm2);
    result_free(&guarded);
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
            "rows_with_list=%llu controls_fired=%llu status=%d\n",
           (unsigned long long)rows_compared,
           (unsigned long long)rows_fired,
           (unsigned long long)rows_with_list,
           (unsigned long long)controls_fired, status);
    return status;
}
