/* utf8_rows.h -- the UTF-8 route's rows, enumerated once for the C actors.
 *
 * The route compares three actors on the same rows: the object built from
 * `kernel/json/utf8.c`, the Lean body `utf8Function` through
 * `leanllvm-json-utf8`, and the measured statements hosted by
 * `utf8_measured.c`.  This header is the row list the two C actors share —
 * `utf8_driver.c` and `utf8_measured.c` — so the arms are one text and not a
 * copy per program.  The Lean side enumerates the same rows from its own
 * definition, which is what makes the three transcripts' identities a
 * comparison rather than a repetition: an arm rule that drifted on either side
 * shows as a missing, extra or renamed row.
 *
 * A row is `(source, label, prefix, document, n)`: `source` is the corpus
 * argument as given, or `arm:<arm>`; `label` is the row's identity inside its
 * source; `prefix` is the three bytes before the document; `document` is `n`
 * bytes.  The callback owns the staging and printing, and must not retain the
 * pointers — both buffers are reused per row.
 *
 * The enumeration:
 *
 *   arm:empty   the empty document.
 *   arm:b1      every one-byte document (256).
 *   arm:b2      every two-byte document (65,536).
 *   arm:b3      six three-byte leads (E0 E1 EC ED EE EF) against the nine
 *               continuation bytes 7F 80 8F 90 9F A0 BF C0 FF in each of the
 *               two following positions (6 × 9 × 9 = 486).  The nine values
 *               are what makes the grid carry four bytes in 0x80..0x9F, two in
 *               0xA0..0xBF and three outside 0x80..0xBF, so the arm's per-lead
 *               rejection counts are the range restrictions of RFC 3629 §4.
 *   arm:b4      seven four-byte leads (F0 F1 F3 F4 F5 F7 FF) against the same
 *               nine values in each of the three following positions
 *               (7 × 9 × 9 × 9 = 5,103).
 *   arm:tail    eight suffixes at every total length they fit, in three
 *               layouts.  The suffixes are F0, F0 90, F0 90 80, E2, C3, C0, F5
 *               and 80; a suffix of length k runs over L = k..70, so with six
 *               one-byte suffixes, one two-byte and one three-byte the
 *               suffixes contribute 6 × 70 + 69 + 68 = 557 lengths per layout
 *               and the arm is 3 × 557 = 1,671.  The layouts are `raw` (0x41
 *               before the suffix, document ends at the suffix), `pad` (the
 *               suffix at position L inside a document of the next 64-byte
 *               boundary, 0x41 after it) and `pre` (0x41 before the suffix up
 *               to that boundary, suffix still last).
 *   arm:prefix  six documents (80, A0, E0 80 80, ED A0 80, F4 90 80 80, C0 AF)
 *               under each of the three-byte prefixes 00 00 00, 41 41 41 and
 *               F0 90 80 — the ABI's staging obligation, and the two rows it
 *               moves (6 × 3 = 18).
 *   arm:place   eight sequences (C3 A9, E2 82 AC, F0 9F 98 80, F4 90 80 80,
 *               E0 80 80, ED A0 80, C0 AF, 80) at every offset 0..63 of a
 *               document of length 64 + offset with 0x41 before them, so the
 *               block boundary falls at every position inside a sequence and
 *               then at every position after it (8 × 64 = 512).
 *
 * Every arm row stages the three zero prefix bytes the ABI requires except
 * `arm:prefix`, whose subject is those bytes.
 *
 * The corpus file is a four-column TSV with no header — `label`, the
 * document's bytes as lowercase hex pairs (`-` for the empty document), `n`,
 * and the expectation in the stage's units (0 accepted, 1 rejected).  Its line
 * count is its row count.  A malformed line exits 2; an unreadable file exits
 * 3, so a setup fault is never read as an assertion result.
 */
#ifndef LEANLLVM_UTF8_ROWS_H
#define LEANLLVM_UTF8_ROWS_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define UTF8_DOC_MAX 1024u /* the longest document any row defines, with slack */

typedef void utf8_row_fn(void *ctx, const char *source, const char *label,
                         const uint8_t *pre, const uint8_t *doc, uint64_t n);

static const uint8_t utf8_zero3[3] = {0, 0, 0};
static const uint8_t utf8_cls9[9] = {0x7F, 0x80, 0x8F, 0x90, 0x9F,
                                     0xA0, 0xBF, 0xC0, 0xFF};
static const uint8_t utf8_leads3[6] = {0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF};
static const uint8_t utf8_leads4[7] = {0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xF7, 0xFF};

/* `label \t hex \t n \t expectation`, read into one callback row.  The
   expectation column is the route's business, not the enumerator's: the third
   column is checked against the decoded length and the fourth is read only to
   prove it is present and one of the two values. */
static void utf8_corpus_file(const char *path, utf8_row_fn *fn, void *ctx) {
    static uint8_t doc[UTF8_DOC_MAX];
    FILE *fp = fopen(path, "r");
    char line[65536];
    unsigned long lineno = 0;
    if (!fp) {
        fprintf(stderr, "setup: cannot read %s\n", path);
        exit(3);
    }
    while (fgets(line, sizeof line, fp)) {
        const char *f[4];
        size_t len[4];
        size_t k = 0, hlen;
        const char *p = line;
        unsigned long l;
        lineno++;
        l = strlen(line);
        while (l && (line[l - 1] == '\n' || line[l - 1] == '\r')) line[--l] = '\0';
        if (!l) continue;
        while (k < 4) {
            const char *q = strchr(p, '\t');
            f[k] = p;
            len[k] = q ? (size_t)(q - p) : strlen(p);
            k++;
            if (!q) break;
            p = q + 1;
        }
        if (k != 4) {
            fprintf(stderr, "setup: %s:%lu: not four tab-separated columns\n",
                    path, lineno);
            exit(2);
        }
        if (!(len[3] == 1 && (f[3][0] == '0' || f[3][0] == '1'))) {
            fprintf(stderr, "setup: %s:%lu: expectation is not 0 or 1\n", path,
                    lineno);
            exit(2);
        }
        if (len[0] >= 256) {
            fprintf(stderr, "setup: %s:%lu: label too long\n", path, lineno);
            exit(2);
        }
        hlen = len[1];
        if (hlen == 1 && f[1][0] == '-') hlen = 0;
        else if ((hlen & 1) != 0) {
            fprintf(stderr, "setup: %s:%lu: hex is not whole bytes\n", path,
                    lineno);
            exit(2);
        }
        {
            uint64_t n = strtoull(f[2], NULL, 10);
            size_t i;
            char label[256];
            if (hlen / 2 != n || n > UTF8_DOC_MAX) {
                fprintf(stderr, "setup: %s:%lu: %zu byte(s) of hex, n=%llu\n",
                        path, lineno, hlen / 2, (unsigned long long)n);
                exit(2);
            }
            for (i = 0; i < n; i++) {
                int hi, lo;
                char a = f[1][2 * i], b = f[1][2 * i + 1];
                if (a >= '0' && a <= '9') hi = a - '0';
                else if (a >= 'a' && a <= 'f') hi = a - 'a' + 10;
                else { fprintf(stderr, "setup: %s:%lu: hex digit '%c'\n", path,
                               lineno, a); exit(2); }
                if (b >= '0' && b <= '9') lo = b - '0';
                else if (b >= 'a' && b <= 'f') lo = b - 'a' + 10;
                else { fprintf(stderr, "setup: %s:%lu: hex digit '%c'\n", path,
                               lineno, b); exit(2); }
                doc[i] = (uint8_t)(hi * 16 + lo);
            }
            memcpy(label, f[0], len[0]);
            label[len[0]] = '\0';
            fn(ctx, path, label, utf8_zero3, doc, n);
        }
    }
    fclose(fp);
}

/* The eight suffixes of `arm:tail`, their lengths, and the three layouts. */
static const char *utf8_tail_name[8] = {"f0", "f090", "f09080", "e2",
                                        "c3", "c0",  "f5",     "80"};
static const uint8_t utf8_tail_len[8] = {1, 2, 3, 1, 1, 1, 1, 1};
static const uint8_t utf8_tail_byte[8][3] = {
    {0xF0, 0x00, 0x00}, {0xF0, 0x90, 0x00}, {0xF0, 0x90, 0x80},
    {0xE2, 0x00, 0x00}, {0xC3, 0x00, 0x00}, {0xC0, 0x00, 0x00},
    {0xF5, 0x00, 0x00}, {0x80, 0x00, 0x00},
};
static const char *utf8_layout_name[3] = {"raw", "pad", "pre"};

static void utf8_arms(utf8_row_fn *fn, void *ctx) {
    static uint8_t doc[UTF8_DOC_MAX];
    char label[64];

    fn(ctx, "arm:empty", "empty", utf8_zero3, doc, 0);

    for (int a = 0; a < 256; a++) {
        doc[0] = (uint8_t)a;
        snprintf(label, sizeof label, "%02x", a);
        fn(ctx, "arm:b1", label, utf8_zero3, doc, 1);
    }
    for (int a = 0; a < 256; a++)
        for (int b = 0; b < 256; b++) {
            doc[0] = (uint8_t)a;
            doc[1] = (uint8_t)b;
            snprintf(label, sizeof label, "%02x%02x", a, b);
            fn(ctx, "arm:b2", label, utf8_zero3, doc, 2);
        }
    for (int li = 0; li < 6; li++)
        for (int x = 0; x < 9; x++)
            for (int y = 0; y < 9; y++) {
                doc[0] = utf8_leads3[li];
                doc[1] = utf8_cls9[x];
                doc[2] = utf8_cls9[y];
                snprintf(label, sizeof label, "%02x%02x%02x", doc[0], doc[1],
                         doc[2]);
                fn(ctx, "arm:b3", label, utf8_zero3, doc, 3);
            }
    for (int li = 0; li < 7; li++)
        for (int x = 0; x < 9; x++)
            for (int y = 0; y < 9; y++)
                for (int z = 0; z < 9; z++) {
                    doc[0] = utf8_leads4[li];
                    doc[1] = utf8_cls9[x];
                    doc[2] = utf8_cls9[y];
                    doc[3] = utf8_cls9[z];
                    snprintf(label, sizeof label, "%02x%02x%02x%02x", doc[0],
                             doc[1], doc[2], doc[3]);
                    fn(ctx, "arm:b4", label, utf8_zero3, doc, 4);
                }
    for (int pi = 0; pi < 8; pi++) {
        int k = utf8_tail_len[pi];
        for (int L = k; L <= 70; L++) {
            uint64_t lp = (uint64_t)((L + 63) / 64) * 64;
            for (int vi = 0; vi < 3; vi++) {
                uint64_t n;
                memset(doc, 0x41, (size_t)lp);
                if (vi == 0) {
                    n = (uint64_t)L;
                    memcpy(doc + (L - k), utf8_tail_byte[pi], (size_t)k);
                } else if (vi == 1) {
                    n = lp;
                    memcpy(doc + (L - k), utf8_tail_byte[pi], (size_t)k);
                    memset(doc + L, 0x41, (size_t)(lp - (uint64_t)L));
                } else {
                    n = lp;
                    memcpy(doc + (lp - (uint64_t)k), utf8_tail_byte[pi],
                           (size_t)k);
                }
                snprintf(label, sizeof label, "%s/%s/L%d", utf8_tail_name[pi],
                         utf8_layout_name[vi], L);
                fn(ctx, "arm:tail", label, utf8_zero3, doc, n);
            }
        }
    }
    {
        static const uint8_t pres[3][3] = {
            {0x00, 0x00, 0x00}, {0x41, 0x41, 0x41}, {0xF0, 0x90, 0x80}};
        static const char *pre_name[3] = {"zero", "a3", "f09080"};
        static const uint8_t docs[6][4] = {
            {0x80, 0x00, 0x00, 0x00}, {0xA0, 0x00, 0x00, 0x00},
            {0xE0, 0x80, 0x80, 0x00}, {0xED, 0xA0, 0x80, 0x00},
            {0xF4, 0x90, 0x80, 0x80}, {0xC0, 0xAF, 0x00, 0x00}};
        static const uint64_t dns[6] = {1, 1, 3, 3, 4, 2};
        static const char *doc_name[6] = {"80", "a0", "e08080", "eda080",
                                          "f4908080", "c0af"};
        for (int di = 0; di < 6; di++)
            for (int pi = 0; pi < 3; pi++) {
                memcpy(doc, docs[di], sizeof docs[di]);
                snprintf(label, sizeof label, "%s/%s", doc_name[di],
                         pre_name[pi]);
                fn(ctx, "arm:prefix", label, pres[pi], doc, dns[di]);
            }
    }
    {
        static const uint8_t seqs[8][4] = {
            {0xC3, 0xA9, 0x00, 0x00}, {0xE2, 0x82, 0xAC, 0x00},
            {0xF0, 0x9F, 0x98, 0x80}, {0xF4, 0x90, 0x80, 0x80},
            {0xE0, 0x80, 0x80, 0x00}, {0xED, 0xA0, 0x80, 0x00},
            {0xC0, 0xAF, 0x00, 0x00}, {0x80, 0x00, 0x00, 0x00}};
        static const uint8_t lens[8] = {2, 3, 4, 4, 3, 3, 2, 1};
        for (int si = 0; si < 8; si++) {
            int k = lens[si];
            for (int o = 0; o < 64; o++) {
                uint64_t n = (uint64_t)(64 + o);
                memset(doc, 0x41, (size_t)(n - (uint64_t)k));
                memcpy(doc + (n - (uint64_t)k), seqs[si], (size_t)k);
                snprintf(label, sizeof label, "seq%d/off%d", si, o);
                fn(ctx, "arm:place", label, utf8_zero3, doc, n);
            }
        }
    }
}

/* Every row, corpus files first in the order given, then the arms. */
static void utf8_rows_run(int ncorpus, char **corpus, int arms,
                          utf8_row_fn *fn, void *ctx) {
    for (int i = 0; i < ncorpus; i++) utf8_corpus_file(corpus[i], fn, ctx);
    if (arms) utf8_arms(fn, ctx);
}

#endif
