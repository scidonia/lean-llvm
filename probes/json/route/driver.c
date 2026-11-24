/* driver.c -- the C caller the Lean route's staging is compared against.
 *
 * It stages the document exactly as `LeanLLVM.JsonCallRoute.stagedStore` does
 * and calls `leanllvm_json_pipeline` directly, printing the same three lines as
 * `RouteMain.lean`: the observation, the arena and the event stream.  The check
 * compares all three, byte for byte: agreement is evidence that the Lean
 * wrapper builds the staging the record demands, and that its output is the
 * object's rather than a Lean-side recomputation.  Comparing the observation
 * alone would let equal lengths and verdicts conceal different values.
 *
 * `--noevent <file>` calls `leanllvm_json_pipeline_noevent` on the same staged
 * document, with a scratch buffer at the entry's `pre` (`n + 64`) in place of
 * the destination and event buffers, and prints one line:
 *
 *   reading verdict=<v> nk=<n> nxp=<n> err=<n> tokens=<n> values=<n> sum=<n>
 *
 * The line is the form `--consume-noevent` prints, so the route's arm and this
 * actor's reading are compared without transcription.  The default form, with
 * no flag, is the event arm's three lines; the flag adds an arm and changes
 * nothing about the certified one.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "escape_guard.h"
#include "pipeline.h"
#include "stage2_noevent.h"
#include "entry.h"

/* One payload line, in `RouteMain.lean`'s form: the label, then two lowercase
   hex digits per byte. */
static void print_hex(const char *label, const uint8_t *p, uint64_t n) {
    printf("%s=", label);
    for (uint64_t i = 0; i < n; i++) printf("%02x", p[i]);
    printf("\n");
}

int main(int argc, char **argv) {
    int noevent = 0;
    int argi = 1;
    if (argc >= 2 && strcmp(argv[1], "--noevent") == 0) {
        noevent = 1;
        argi = 2;
    }
    if (argc != argi + 1) {
        fprintf(stderr, "usage: driver [--noevent] <file>\n");
        return 1;
    }
    FILE *f = fopen(argv[argi], "rb");
    if (!f) { fprintf(stderr, "driver: cannot read %s\n", argv[argi]); return 2; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *doc = (uint8_t *)malloc((size_t)sz + 1);
    if (fread(doc, 1, (size_t)sz, f) != (size_t)sz) { fclose(f); return 2; }
    fclose(f);

    uint64_t n = (uint64_t)sz;
    if (n == 0) {
        fprintf(stderr, "refused: empty input: the pipeline record's domain requires a non-empty document\n");
        return 2;
    }
    if (n > 1048576) {
        fprintf(stderr, "refused: input too long: the record's bound is 1048576 bytes, the document is %llu\n",
                (unsigned long long)n);
        return 2;
    }
    uint64_t nb = (n + 63) / 64;
    uint64_t epcap = 64 * nb + 9, xpcap = 64 * nb + 8;
    uint64_t dstcap = n + 64, evcap = 13 * n + 128;
    uint64_t winlen = 3 + 64 * nb + 32;
    uint8_t *win = (uint8_t *)calloc(winlen, 1);
    memcpy(win + 3, doc, (size_t)n);

    uint8_t *sc = (uint8_t *)calloc(24, 1);
    uint8_t *mk = (uint8_t *)calloc(48, 1);
    uint8_t *entw = (uint8_t *)calloc(8, 1);
    uint32_t *ep = (uint32_t *)calloc(4 * epcap, 1);
    uint64_t *nk = (uint64_t *)calloc(8, 1);
    uint32_t *xp = (uint32_t *)calloc(4 * xpcap, 1);
    uint64_t *nxp = (uint64_t *)calloc(8, 1);
    uint64_t *xcarry = (uint64_t *)calloc(16, 1);

    uint32_t *tab = (uint32_t *)calloc(2048, 4);
    leanllvm_json_entry_table(tab);

    /* The arm the route selects.  Bit 1 is the escape-list gate, and the guard
       clears it on a document whose list arm 2 would build is empty, so the two
       actors call the object with the same arm word and not merely with the
       same staging.  `escape_guard.h` states the condition and why it is the
       list's emptiness; `guard.sh` checks the two arms' outputs byte for byte
       on every document the guard fires on. */
    uint64_t arm = leanllvm_route_escape_can_skip(doc, n) ? 0 : 2;

    if (noevent) {
        /* The same stage-1 buffers and the same arm word; the destination and
           event buffers are replaced by the scratch buffer at the entry's
           `pre`, and the reading slots start zeroed as the entry declares. */
        uint8_t *scratch = (uint8_t *)calloc((size_t)n + 64, 1);
        uint64_t *tokens = (uint64_t *)calloc(8, 1);
        uint64_t *values = (uint64_t *)calloc(8, 1);
        uint64_t *sum = (uint64_t *)calloc(8, 1);
        uint64_t *err = (uint64_t *)calloc(8, 1);
        uint64_t verdict = leanllvm_json_pipeline_noevent(
            win + 3, n, (uint64_t *)sc, (uint64_t *)mk, (uint64_t *)entw,
            ep, epcap, (uint64_t *)nk, xp, xpcap, (uint64_t *)nxp,
            (uint64_t *)xcarry, scratch, n + 64, tokens, values, sum, err, arm);
        printf("reading verdict=%llu nk=%llu nxp=%llu err=%llu tokens=%llu "
               "values=%llu sum=%llu\n",
               (unsigned long long)verdict, (unsigned long long)*nk,
               (unsigned long long)*nxp, (unsigned long long)*err,
               (unsigned long long)*tokens, (unsigned long long)*values,
               (unsigned long long)*sum);
        free(scratch); free(tokens); free(values); free(sum); free(err);
        return 0;
    }

    uint8_t *dst = (uint8_t *)calloc(dstcap, 1);
    uint64_t *ndst = (uint64_t *)calloc(8, 1);
    uint8_t *ev = (uint8_t *)calloc(evcap, 1);
    uint64_t *nev = (uint64_t *)calloc(8, 1);
    uint64_t *err = (uint64_t *)calloc(8, 1);

    uint64_t verdict = leanllvm_json_pipeline(
        win + 3, n, (uint64_t *)sc, (uint64_t *)mk, (uint64_t *)entw,
        ep, epcap, (uint64_t *)nk, xp, xpcap, (uint64_t *)nxp,
        (uint64_t *)xcarry, dst, dstcap, (uint64_t *)ndst, ev, evcap,
        (uint64_t *)nev, (uint64_t *)err, arm);

    printf("verdict=%llu nk=%llu nxp=%llu ndst=%llu nev=%llu err=%llu\n",
           (unsigned long long)verdict, (unsigned long long)*nk,
           (unsigned long long)*nxp, (unsigned long long)*ndst,
           (unsigned long long)*nev, (unsigned long long)*err);
    print_hex("arena", dst, *ndst);
    print_hex("events", ev, *nev);
    return 0;
}
