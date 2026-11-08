/* escape_driver.c -- the escape-list route's rows and its scalar reference.
 *
 * The route compares two derivations over the same committed corpus:
 *
 *   * the measured actor -- `probes/json/escape_measured.c` linked into this
 *     binary, which returns the stream the vendored stage-1 builder left in
 *     `s1f_esc_list` and its count;
 *   * the reference below -- a byte scan written from the escape rule, not
 *     from the emitter's text.  It walks the document once, tracks whether a
 *     byte is inside a string, and records a position for every in-string
 *     control byte and for every backslash at an even offset inside its run
 *     (the first of `\\`, `\\\`, ...).  The string state follows the same
 *     quoting the scanner sees: an unescaped quote opens and closes a string,
 *     and a run of odd length escapes the byte after it.
 *
 * A row is one line:
 *
 *     <source>\t<label>\t<n>\t<count>\t<positions or ->
 *
 * with the positions space-separated in document order, so the line is the
 * ordered sequence and not a set.  `--measured` prints the actor's rows,
 * `--reference` the reference's; the route compares the two transcripts line
 * for line.  `--expect FILE` prints the actor's rows and compares them with an
 * expectation transcript, reporting `mismatch: <label>` on stderr and exiting
 * 1 on disagreement.  `--class` prints, per row,
 *
 *     <source>\t<label>\t<derived>\t<exhibited>
 *
 * where `derived` is the document gate re-derived from the bytes by the
 * function below (`plain` or `listed`) and `exhibited` is what the measured
 * actor did (`listed` when it left a list, `plain` when it left none), so the
 * route can check the gate's rule as a relation between two independent
 * observations.
 *
 * The corpus is a three-column TSV with no header -- `label`, the document's
 * bytes as lowercase hex pairs (`-` for the empty document), `n`.  The driver
 * stages each document zero-padded to a 64-byte boundary, which is the
 * measured builder's own read contract, and reads only the `n` bytes back from
 * the reference.
 *
 * Nothing here reaches a clock, a file other than the corpus and the
 * expectation, or a network.  A malformed corpus or expectation line exits 2;
 * an unreadable file exits 3, so a setup fault is never read as an assertion.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ESC_DOC_MAX 4096u

/* The measured actor's boundary, from `escape_measured.c`. */
const uint32_t *escape_measured_list(const uint8_t *doc, uint64_t n,
                                     uint64_t *nx);

/* ------------------------------------------------------------ the reference -- */

/* The escape rule over the document's bytes.  A position is an in-string
   control byte, or a backslash whose offset inside its own run is even.  The
   run length is what decides both the parity and whether the byte after the
   run is escaped (and so whether an unescaped quote closes the string there). */
static uint64_t ref_positions(const uint8_t *d, uint64_t n, uint32_t *out) {
    uint64_t k = 0, i = 0, run = 0;
    int in_string = 0;
    while (i < n) {
        uint8_t c = d[i];
        if (!in_string) {
            if (c == '"') {
                in_string = 1;
                run = 0;
            }
            i++;
            continue;
        }
        if (c == '\\') {
            if ((run & 1) == 0) out[k++] = (uint32_t)i;
            run++;
            i++;
            continue;
        }
        {
            int escaped = (int)(run & 1);
            run = 0;
            if (c < 0x20) out[k++] = (uint32_t)i;
            else if (c == '"' && !escaped) in_string = 0;
        }
        i++;
    }
    return k;
}

/* ---------------------------------------------------------- the gate rule -- */

/* The per-document gate the measured builder consults before it builds an
   escape list, re-derived here from the document's bytes instead of read back
   from the builder.  `kernel/json/measured/dens.h`:
     * a document with no whole 64-byte block is PLAIN (`dens.h:222`);
     * otherwise blocks are sampled from the first at the stride `nb/64`, at
       least one (`dens.h:223-224`);
     * each sampled block contributes only the backslashes among its low 32
       bytes (`dens.h:227-234`);
     * the document is PLAIN when `hits*64 < samples*DENS_PLAIN_NUM`
       (`dens.h:261-262`), with `DENS_PLAIN_NUM` 1 (`dens.h:68-70`, no
       measured `-D` overriding it).
   Only PLAIN versus not matters to the escape list: a PLAIN document clears
   `s1f_xs_on` and the builder leaves no list (`s1fuse.h:1636`, `:1944-1946`).
   The route supplies `DENS_PLAIN_NUM` from the header itself when it compiles
   this driver, so the derivation cannot drift from the threshold. */
#ifndef DENS_PLAIN_NUM
#define DENS_PLAIN_NUM 1
#endif

static int derived_plain(const uint8_t *d, uint64_t n) {
    uint64_t nb = n >> 6, step, hits = 0, samples = 0;
    if (!nb) return 1;
    step = nb / 64;
    if (!step) step = 1;
    for (uint64_t i = 0; i < nb; i += step) {
        const uint8_t *p = d + (i << 6);
        unsigned low = 0;
        for (unsigned j = 0; j < 32; j++) low += (p[j] == '\\');
        hits += low;
        samples++;
    }
    return hits * 64 < samples * (uint64_t)DENS_PLAIN_NUM;
}

/* The same rule's four readings, for the rows that ask why a document landed
   in its arm.  `step` is printed as the stride the loop actually used, which is
   `nb/64` and at least one (`dens.h:223-224`); `samples` and `hits` are what
   the threshold at `:261-262` consumes.  `--gate` reports these and nothing
   else, so a reader can check the arithmetic of a suppressed row instead of
   trusting the class. */
struct gate_reading {
    uint64_t nb, step, samples, hits;
    int plain;
};

static struct gate_reading gate_of(const uint8_t *d, uint64_t n) {
    struct gate_reading g = {0, 0, 0, 0, 1};
    g.nb = n >> 6;
    if (!g.nb) return g;
    g.step = g.nb / 64;
    if (!g.step) g.step = 1;
    for (uint64_t i = 0; i < g.nb; i += g.step) {
        const uint8_t *p = d + (i << 6);
        unsigned low = 0;
        for (unsigned j = 0; j < 32; j++) low += (p[j] == '\\');
        g.hits += low;
        g.samples++;
    }
    g.plain = g.hits * 64 < g.samples * (uint64_t)DENS_PLAIN_NUM;
    return g;
}

/* -------------------------------------------------------------- the staging -- */

static uint8_t stage[ESC_DOC_MAX + 64];
static uint32_t ref_out[ESC_DOC_MAX];

static void stage_document(const uint8_t *doc, uint64_t n) {
    memset(stage, 0, sizeof stage);
    if (n) memcpy(stage, doc, n);
}

/* ------------------------------------------------------------------ the row -- */

static int reference_mode;
static int class_mode;
static int gate_mode;

struct row_ctx {
    FILE *expect;          /* NULL unless --expect */
    int bad;
    unsigned long rows;
};

/* Format one row; the buffer is caller-owned and large enough for the longest
   document the staging buffer accepts. */
static void format_row(char *line, size_t cap, const char *source,
                       const char *label, uint64_t n, const uint32_t *pos,
                       uint64_t k) {
    size_t off = (size_t)snprintf(line, cap, "%s\t%s\t%llu\t%llu\t", source,
                                  label, (unsigned long long)n,
                                  (unsigned long long)k);
    if (k == 0) {
        off += (size_t)snprintf(line + off, cap - off, "-");
    } else {
        for (uint64_t i = 0; i < k; i++)
            off += (size_t)snprintf(line + off, cap - off, "%s%u",
                                    i ? " " : "", pos[i]);
    }
    snprintf(line + off, cap - off, "\n");
}

static void row_emit(void *vctx, const char *source, const char *label,
                     const uint8_t *doc, uint64_t n) {
    struct row_ctx *ctx = (struct row_ctx *)vctx;
    char line[65536];

    if (gate_mode) {
        struct gate_reading g = gate_of(doc, n);
        snprintf(line, sizeof line, "%s\t%s\t%llu\t%llu\t%llu\t%llu\t%s\n",
                 source, label, (unsigned long long)g.nb,
                 (unsigned long long)g.step, (unsigned long long)g.samples,
                 (unsigned long long)g.hits, g.plain ? "plain" : "listed");
    } else if (class_mode) {
        uint64_t k = 0;
        const uint32_t *p;
        stage_document(doc, n);
        p = escape_measured_list(stage, n, &k);
        if (k && !p) {
            fprintf(stderr, "setup: %s/%s: count %llu without a stream\n",
                    source, label, (unsigned long long)k);
            exit(3);
        }
        snprintf(line, sizeof line, "%s\t%s\t%s\t%s\n", source, label,
                 derived_plain(doc, n) ? "plain" : "listed",
                 p ? "listed" : "plain");
    } else if (reference_mode) {
        uint64_t k = ref_positions(doc, n, ref_out);
        format_row(line, sizeof line, source, label, n, ref_out, k);
    } else {
        stage_document(doc, n);
        {
            uint64_t k = 0;
            const uint32_t *p = escape_measured_list(stage, n, &k);
            if (k && !p) {
                fprintf(stderr, "setup: %s/%s: count %llu without a stream\n",
                        source, label, (unsigned long long)k);
                exit(3);
            }
            format_row(line, sizeof line, source, label, n, p, k);
        }
    }

    fputs(line, stdout);

    if (ctx->expect) {
        char want[65536];
        if (!fgets(want, sizeof want, ctx->expect)) {
            fprintf(stderr, "setup: the expectation has no row %lu (%s)\n",
                    ctx->rows + 1, label);
            exit(3);
        }
        if (strcmp(want, line) != 0) {
            fprintf(stderr, "mismatch: %s\n", label);
            ctx->bad = 1;
        }
    }
    ctx->rows++;
}

/* -------------------------------------------------------------------- main -- */

static void usage(void) {
    fprintf(stderr,
            "usage: escape_driver [--corpus FILE]... [--measured|--reference] "
            "[--expect FILE]\n"
            "  --corpus FILE  a three-column TSV: label, hex, n\n"
            "  --measured     print the measured emitter's rows (default)\n"
            "  --reference    print the scalar reference's rows\n"
            "  --class        print each row's re-derived and exhibited class\n"
            "  --gate         print the gate's own reading of each row\n"
            "  --expect FILE  compare the measured rows with an expectation\n");
}

static int hex_digit(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    return -1;
}

typedef void esc_row_fn(void *ctx, const char *source, const char *label,
                        const uint8_t *doc, uint64_t n);

static void corpus_file(const char *path, esc_row_fn *fn, void *ctx) {
    static uint8_t doc[ESC_DOC_MAX];
    FILE *fp = fopen(path, "r");
    char line[65536];
    unsigned long lineno = 0;
    if (!fp) {
        fprintf(stderr, "setup: cannot read %s\n", path);
        exit(3);
    }
    while (fgets(line, sizeof line, fp)) {
        const char *f[3];
        size_t len[3];
        size_t k = 0, hlen, l;
        const char *p = line;
        lineno++;
        l = strlen(line);
        while (l && (line[l - 1] == '\n' || line[l - 1] == '\r')) line[--l] = '\0';
        if (!l) continue;
        while (k < 3) {
            const char *q = strchr(p, '\t');
            f[k] = p;
            len[k] = q ? (size_t)(q - p) : strlen(p);
            k++;
            if (!q) break;
            p = q + 1;
        }
        if (k != 3) {
            fprintf(stderr, "setup: %s:%lu: not three tab-separated columns\n",
                    path, lineno);
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
            char label[256];
            if (hlen / 2 != n || n > ESC_DOC_MAX) {
                fprintf(stderr, "setup: %s:%lu: %zu byte(s) of hex, n=%llu\n",
                        path, lineno, hlen / 2, (unsigned long long)n);
                exit(2);
            }
            for (size_t i = 0; i < n; i++) {
                int hi = hex_digit(f[1][2 * i]);
                int lo = hex_digit(f[1][2 * i + 1]);
                if (hi < 0 || lo < 0) {
                    fprintf(stderr, "setup: %s:%lu: not lowercase hex\n", path,
                            lineno);
                    exit(2);
                }
                doc[i] = (uint8_t)(hi * 16 + lo);
            }
            memcpy(label, f[0], len[0]);
            label[len[0]] = '\0';
            fn(ctx, path, label, doc, n);
        }
    }
    fclose(fp);
}

int main(int argc, char **argv) {
    char *corpus[64];
    int ncorpus = 0;
    const char *expect_path = NULL;
    struct row_ctx ctx = {NULL, 0, 0};

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--corpus") == 0 && i + 1 < argc) {
            if (ncorpus == 64) { usage(); return 2; }
            corpus[ncorpus++] = argv[++i];
        } else if (strcmp(argv[i], "--measured") == 0) {
            reference_mode = 0;
        } else if (strcmp(argv[i], "--reference") == 0) {
            reference_mode = 1;
        } else if (strcmp(argv[i], "--class") == 0) {
            class_mode = 1;
        } else if (strcmp(argv[i], "--gate") == 0) {
            gate_mode = 1;
        } else if (strcmp(argv[i], "--expect") == 0 && i + 1 < argc) {
            expect_path = argv[++i];
        } else {
            usage();
            return 2;
        }
    }
    if (ncorpus == 0) { usage(); return 2; }
    if (reference_mode && expect_path) {
        fprintf(stderr, "setup: --expect compares the measured actor\n");
        return 2;
    }
    if (class_mode && (reference_mode || expect_path)) {
        fprintf(stderr, "setup: --class reports the measured actor's gate\n");
        return 2;
    }
    if (gate_mode && (class_mode || reference_mode || expect_path)) {
        fprintf(stderr, "setup: --gate reports the gate's own arithmetic alone\n");
        return 2;
    }

    if (expect_path) {
        ctx.expect = fopen(expect_path, "r");
        if (!ctx.expect) {
            fprintf(stderr, "setup: cannot read %s\n", expect_path);
            return 3;
        }
    }

    for (int c = 0; c < ncorpus; c++) corpus_file(corpus[c], row_emit, &ctx);

    if (ctx.expect) {
        char extra[65536];
        if (fgets(extra, sizeof extra, ctx.expect)) {
            fprintf(stderr, "setup: the expectation has more rows than the corpus\n");
            fclose(ctx.expect);
            return 3;
        }
        fclose(ctx.expect);
    }
    return ctx.bad ? 1 : 0;
}
