/* ent_rows.c -- the row reader for `identity/ent_oracle.c`.
 *
 * `ent_oracle.c` exposes `ent_oracle_row` and has no `main`: no measured
 * function computes the `ent` word on its own, so the statements are copied
 * into that file and driven here.  This reader consumes the specification
 * route's `--ent` rows on stdin — `label qm sm im ws prevS n bi`, whitespace
 * separated — and prints the same label and the seven inputs it consumed,
 * followed by the oracle's `S`, its `ent` before the tail mask, and its
 * tail-masked word:
 *
 *   label qm sm im ws prevS n bi S ent tailed
 *
 * `S`, `ent` and `tailed` are `0x` and sixteen lowercase hex digits, because a
 * 64-lane word above 2^53 is not exact in a decimal reader's arithmetic; the
 * inputs are echoed as the tokens read, so the two streams are compared whole
 * line by line and a mismatch is attributed to the half it lives in.
 *
 * `lim = n - (bi << 6)` is derived inside `ent_oracle_row`, from the row's `n`
 * and `bi`, exactly as the specification derives it: the tail arithmetic is
 * part of the word under comparison, not a field of the harness.
 *
 * Exit status: 0 when every row was read and written, 2 when a row cannot be
 * read, so a malformed stream is a setup fault and not a word disagreement. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

/* The types `ent_oracle.c` defines; they are declared again here because the
 * oracle publishes no header, and only the layout crosses the interface. */
typedef struct { uint64_t prevS; } ent_carry;
typedef struct { uint64_t scalar, ent, tailed; } ent_row;

extern ent_row ent_oracle_row(uint64_t qm, uint64_t sm, uint64_t im,
                              uint64_t wsm, ent_carry *state, uint64_t n,
                              uint64_t bi);

int main(void) {
    char line[1024];
    while (fgets(line, sizeof line, stdin) != NULL) {
        char label[512], qm[32], sm[32], im[32], ws[32], prevS[32], n[32], bi[32];
        if (sscanf(line, "%511s %31s %31s %31s %31s %31s %31s %31s",
                   label, qm, sm, im, ws, prevS, n, bi) != 8) {
            fprintf(stderr, "ent_rows: cannot read a row: %s", line);
            return 2;
        }

        ent_carry st = { .prevS = strtoull(prevS, NULL, 10) };
        ent_row row = ent_oracle_row(strtoull(qm, NULL, 10),
                                     strtoull(sm, NULL, 10),
                                     strtoull(im, NULL, 10),
                                     strtoull(ws, NULL, 10),
                                     &st,
                                     strtoull(n, NULL, 10),
                                     strtoull(bi, NULL, 10));

        printf("%s %s %s %s %s %s %s %s 0x%016llx 0x%016llx 0x%016llx\n",
               label, qm, sm, im, ws, prevS, n, bi,
               (unsigned long long)row.scalar,
               (unsigned long long)row.ent,
               (unsigned long long)row.tailed);
    }
    return 0;
}
