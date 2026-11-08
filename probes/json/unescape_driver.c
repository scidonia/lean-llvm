/* unescape_driver.c -- the escape expander's counted matrix and its scalar
 * reference.
 *
 * The matrix puts one body under two derivations.  The actor is
 * `probes/json/unescape_measured.c`'s `unescape_measured`, which is the
 * vendored `us_dec_x` (`usdec.h:858`) compiled at the measured `-D` set; the
 * reference below is written from the escape rule, not from the decoder's
 * text, and it keeps its own cursor so the carry is compared as well as the
 * bytes.
 *
 * A row is one line:
 *
 *     <group>\t<label>\t<n>\t<pos0>\t<positions>\t<measured>\t<reference>\t<verdict>
 *
 * where each side is `len=<l>:<hex of the decoded bytes>` or
 * `refused@<off>` (the body-relative offset of the first refused escape), the
 * positions are the document-absolute list entries consumed, and the verdict
 * is `agree` or `DIFFER`.  The cursor index both sides end at is compared too
 * and printed as `cursor=<k>` in the measured column when the two cursors
 * differ, which is the only row shape a byte comparison alone would miss.
 *
 * The reference's rule, stated once:
 *
 *   * a position names a byte of the body; bytes before it are copied;
 *   * a control byte (below 0x20) at a position is refused at its offset --
 *     a raw control byte is not a character of a JSON string;
 *   * a position that does not start an escape is refused at its offset: the
 *     list is the document's escape positions, and its entries are trusted, so
 *     a row whose list names something else is a broken precondition and not a
 *     case the decoder claims anything about (the measured step reads the byte
 *     *after* the position without checking the position's own byte;
 *     `usdec.h:384-386`);
 *   * a simple escape is one output byte and two input bytes;
 *   * `\uXXXX` is the code point encoded UTF-8, six input bytes; a high
 *     surrogate immediately followed by `\uXXXX` holding a low surrogate is
 *     one code point from the pair, twelve input bytes, and it consumes the
 *     pair's second list entry as well;
 *   * a lone surrogate is the three-byte form of its own code point, which is
 *     what the measured encoder does (`uj.c:11-13`, `uj_enc` at `uj.c:49`), so
 *     the relation to the model's code-point list survives a document that
 *     carries one;
 *   * a truncated escape, a bad hex digit, or an unknown escape letter is
 *     refused at the escape's offset;
 *   * the decoder never writes past the decoded extent, and the measured run
 *     copy stores whole 32-byte vectors, so the driver keeps slack after the
 *     destination and compares only the returned length.
 *
 * Two buffering facts about the measured code, because a row that ignored them
 * would crash rather than disagree (`us_run_long` at `usdec.h:835-843` copies
 * through `us_run` at `:396-411`, which at `US_W == 64` issues a 32-byte load
 * unconditionally and a second one when `len > 32`): **the body needs 32
 * readable bytes past its end**, and the destination needs 32 writable bytes
 * past the decoded extent — the second store reaches `j + 64` only when the run
 * is longer than 32, in which case the extent is at least `j + len` further
 * on.  The driver keeps `DOC_MAX` with the tail zero-filled and `DST_SLACK` of
 * 128 after the output; the body is zeroed per group so a row's slack is
 * defined rather than whatever the last group left.
 *
 * Nothing here reaches a clock, the network, or a file.  A mismatch exits 1 and
 * the row count is asserted against the formula the groups add up to, so a
 * missing group cannot pass.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define OUT_MAX 512u
#define DST_SLACK 128u
#define DOC_MAX 256u

/* The measured actor's boundary, from `unescape_measured.c`. */
size_t unescape_measured(const uint8_t *body, uint64_t n, uint8_t *dst,
                         size_t *err, const uint32_t *xp, uint64_t *xj,
                         uint64_t nxp, uint64_t pos0);

/* ------------------------------------------------------------ the reference -- */

struct outcome {
    int refused;
    uint64_t err;       /* body-relative, when refused */
    uint64_t len;       /* decoded length, when not */
    uint64_t cursor;    /* index into the position list */
    uint8_t out[OUT_MAX];
};

/* UTF-8, with a lone surrogate encoded as the three-byte form of its own code
   point; values 0..0x10FFFF only (the \u step cannot produce more). */
static void put_utf8(uint8_t *o, uint64_t *j, uint32_t cp) {
    if (cp < 0x80) {
        o[(*j)++] = (uint8_t)cp;
    } else if (cp < 0x800) {
        o[(*j)++] = (uint8_t)(0xC0 | (cp >> 6));
        o[(*j)++] = (uint8_t)(0x80 | (cp & 0x3F));
    } else if (cp < 0x10000) {
        o[(*j)++] = (uint8_t)(0xE0 | (cp >> 12));
        o[(*j)++] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        o[(*j)++] = (uint8_t)(0x80 | (cp & 0x3F));
    } else {
        o[(*j)++] = (uint8_t)(0xF0 | (cp >> 18));
        o[(*j)++] = (uint8_t)(0x80 | ((cp >> 12) & 0x3F));
        o[(*j)++] = (uint8_t)(0x80 | ((cp >> 6) & 0x3F));
        o[(*j)++] = (uint8_t)(0x80 | (cp & 0x3F));
    }
}

static int hex4(const uint8_t *q, uint32_t *cp) {
    uint32_t v = 0;
    for (int i = 0; i < 4; i++) {
        uint8_t c = q[i];
        uint32_t d;
        if (c >= '0' && c <= '9') d = (uint32_t)(c - '0');
        else if (c >= 'a' && c <= 'f') d = (uint32_t)(c - 'a' + 10);
        else if (c >= 'A' && c <= 'F') d = (uint32_t)(c - 'A' + 10);
        else return 0;
        v = (v << 4) | d;
    }
    *cp = v;
    return 1;
}

static int simple_value(uint8_t c) {
    switch (c) {
    case '"': return '"';
    case '\\': return '\\';
    case '/': return '/';
    case 'b': return 8;
    case 'f': return 12;
    case 'n': return 10;
    case 'r': return 13;
    case 't': return 9;
    default: return -1;
    }
}

static struct outcome ref_decode(const uint8_t *d, uint64_t n, uint64_t pos0,
                                 const uint32_t *xp, uint64_t nxp,
                                 uint64_t cursor) {
    struct outcome r;
    uint64_t k = cursor, i = 0, j = 0;
    uint64_t endp = pos0 + n;

    memset(&r, 0, sizeof r);
    while (k < nxp && xp[k] < pos0) k++;
    while (k < nxp) {
        uint64_t q = xp[k], b, adv;
        uint32_t cp;
        int sv;

        if (q >= endp) break;
        k++;
        b = q - pos0;
        while (i < b) r.out[j++] = d[i++];
        if (d[b] < 0x20) { r.refused = 1; r.err = b; r.cursor = k; return r; }
        if (d[b] != '\\') { r.refused = 1; r.err = b; r.cursor = k; return r; }
        if (b + 1 >= n) { r.refused = 1; r.err = b; r.cursor = k; return r; }
        sv = simple_value(d[b + 1]);
        if (sv >= 0) {
            r.out[j++] = (uint8_t)sv;
            i = b + 2;
            continue;
        }
        if (d[b + 1] != 'u') { r.refused = 1; r.err = b; r.cursor = k; return r; }
        if (b + 6 > n) { r.refused = 1; r.err = b; r.cursor = k; return r; }
        if (!hex4(d + b + 2, &cp)) { r.refused = 1; r.err = b; r.cursor = k; return r; }
        adv = 6;
        if ((cp - 0xD800u) < 0x400u && b + 12 <= n && d[b + 6] == '\\' &&
            d[b + 7] == 'u') {
            uint32_t lo;
            if (hex4(d + b + 8, &lo) && (lo - 0xDC00u) < 0x400u) {
                cp = 0x10000u + ((cp - 0xD800u) << 10) + (lo - 0xDC00u);
                adv = 12;
            }
        }
        put_utf8(r.out, &j, cp);
        i = b + adv;
        k += (adv == 12);
    }
    while (i < n) r.out[j++] = d[i++];
    r.len = j;
    r.cursor = k;
    return r;
}

/* ------------------------------------------------------------------ the rows -- */

static unsigned long rows, differs;
static unsigned long group_rows[16];
static const char *group_name[16];
static unsigned ngroups;

static uint8_t body[DOC_MAX];   /* zero-filled per group; the measured copy reads past the end */

static void begin_group(const char *name) {
    memset(body, 0, sizeof body);
    group_name[ngroups] = name;
    group_rows[ngroups++] = 0;
}

/* One row: build the document and its list, run both sides, print the row. */
static void row(const uint8_t *body, uint64_t n, uint64_t pos0,
                const uint32_t *xp, uint64_t nxp, const char *label) {
    static uint8_t dst[OUT_MAX + DST_SLACK];
    struct outcome want, got;
    char m[OUT_MAX * 2 + 64], rf[OUT_MAX * 2 + 64];
    char plist[256];
    size_t err = (size_t)-1, glen;
    uint64_t xj = 0, i;
    int bad;

    /* Stage the body at its absolute start so the actor's `pos0` arithmetic
       sees the same addresses the reference's indices describe; the leading
       bytes and the slack stay unread by both. */
    memset(dst, 0xA5, sizeof dst);
    err = (size_t)-1;
    glen = unescape_measured(body, n, dst, &err, xp, &xj, nxp, pos0);
    want = ref_decode(body, n, pos0, xp, nxp, 0);

    if (glen == (size_t)-1) {
        snprintf(m, sizeof m, "refused@%zu", err);
    } else {
        size_t off = (size_t)snprintf(m, sizeof m, "len=%zu:", glen);
        for (i = 0; i < glen; i++)
            off += (size_t)snprintf(m + off, sizeof m - off, "%02x", dst[i]);
    }
    if (glen != (size_t)-1 && xj != want.cursor)
        snprintf(m + strlen(m), sizeof m - strlen(m), ":cursor=%llu",
                 (unsigned long long)xj);

    if (want.refused) {
        snprintf(rf, sizeof rf, "refused@%llu", (unsigned long long)want.err);
    } else {
        size_t off = (size_t)snprintf(rf, sizeof rf, "len=%llu:",
                                      (unsigned long long)want.len);
        for (i = 0; i < want.len; i++)
            off += (size_t)snprintf(rf + off, sizeof rf - off, "%02x", want.out[i]);
    }
    if (want.refused)
        snprintf(rf + strlen(rf), sizeof rf - strlen(rf), ":cursor=%llu",
                 (unsigned long long)want.cursor);

    bad = want.refused != (glen == (size_t)-1);
    if (!bad && want.refused)
        bad = want.err != (uint64_t)err || want.cursor != xj;
    if (!bad && !want.refused)
        bad = want.len != (uint64_t)glen || want.cursor != xj ||
              memcmp(want.out, dst, want.len) != 0;

    plist[0] = '\0';
    if (!nxp) snprintf(plist, sizeof plist, "-");
    for (i = 0; i < nxp; i++)
        snprintf(plist + strlen(plist), sizeof plist - strlen(plist), "%s%u",
                 i ? " " : "", xp[i]);

    printf("%s\t%s\t%llu\t%llu\t%s\t%s\t%s\t%s\n", group_name[ngroups - 1],
           label, (unsigned long long)n, (unsigned long long)pos0, plist, m, rf,
           bad ? "DIFFER" : "agree");
    rows++;
    group_rows[ngroups - 1]++;
    if (bad) differs++;
}

/* A body of `len` bytes: `pre` 'a's, the two-byte escape `\n`, then 'a's. */
static uint64_t simple_at(uint8_t *buf, uint64_t len, uint64_t pre) {
    uint64_t i;
    for (i = 0; i < len; i++) buf[i] = 'a';
    buf[pre] = '\\';
    buf[pre + 1] = 'n';
    return len;
}

static void group_simple(void) {
    static const uint8_t letters[8] = {'"', '\\', '/', 'b', 'f', 'n', 'r', 't'};
    uint32_t xp[2];
    char label[64];
    begin_group("simple");
    for (unsigned i = 0; i < sizeof letters; i++) {
        body[0] = '\\';
        body[1] = letters[i];
        xp[0] = 0;
        snprintf(label, sizeof label, "escape:%c", letters[i]);
        row(body, 2, 0, xp, 1, label);
    }
}

static void group_u_bmp(void) {
    static const uint32_t cps[11] = {0x0000, 0x001F, 0x0041, 0x007F, 0x0080,
                                     0x07FF, 0x0800, 0xD7FF, 0xE000, 0xFFFD,
                                     0xFFFF};
    static const char *hex[11] = {"0000", "001F", "0041", "007F", "0080",
                                  "07FF", "0800", "D7FF", "E000", "FFFD",
                                  "FFFF"};
    uint32_t xp[2];
    (void)cps;
    begin_group("u-bmp");
    for (unsigned i = 0; i < sizeof hex / sizeof *hex; i++) {
        body[0] = '\\';
        body[1] = 'u';
        memcpy(body + 2, hex[i], 4);
        xp[0] = 0;
        row(body, 6, 0, xp, 1, hex[i]);
    }
}

static void group_pair(void) {
    static const char *hi[3] = {"D800", "DBFF", "D83D"};
    static const char *lo[3] = {"DC00", "DFFF", "DE00"};
    uint32_t xp[3];
    begin_group("pair");
    for (unsigned i = 0; i < 3; i++) {
        char label[32];
        body[0] = '\\'; body[1] = 'u';
        memcpy(body + 2, hi[i], 4);
        body[6] = '\\'; body[7] = 'u';
        memcpy(body + 8, lo[i], 4);
        xp[0] = 0;
        xp[1] = 6;      /* the pair's second entry is in the list and is consumed */
        snprintf(label, sizeof label, "%s+%s", hi[i], lo[i]);
        row(body, 12, 0, xp, 2, label);
    }
}

static void group_pair_edge(void) {
    uint32_t xp[3];
    begin_group("pair-edge");
    body[0] = '\\'; body[1] = 'u';
    memcpy(body + 2, "D800", 4);
    xp[0] = 0;
    row(body, 6, 0, xp, 1, "lone-high");
    body[0] = '\\'; body[1] = 'u';
    memcpy(body + 2, "DC00", 4);
    row(body, 6, 0, xp, 1, "lone-low");
    body[0] = '\\'; body[1] = 'u';
    memcpy(body + 2, "D800", 4);
    body[6] = '\\'; body[7] = 'u';
    memcpy(body + 8, "0041", 4);
    xp[0] = 0; xp[1] = 6;
    row(body, 12, 0, xp, 2, "high+non-low");
    body[0] = '\\'; body[1] = 'u';
    memcpy(body + 2, "D800", 4);
    body[6] = '\\'; body[7] = 'u';
    memcpy(body + 8, "D800", 4);
    row(body, 12, 0, xp, 2, "high+high");
}

static void group_refused(void) {
    uint32_t xp[2];
    begin_group("refused");
    body[0] = '\\'; body[1] = 'x'; xp[0] = 0;
    row(body, 2, 0, xp, 1, "unknown-letter");
    memcpy(body, "\\u12", 4); xp[0] = 0;
    row(body, 4, 0, xp, 1, "short-u");
    body[0] = 'a'; body[1] = '\\'; xp[0] = 1;
    row(body, 2, 0, xp, 1, "trailing-backslash");
    memcpy(body, "\\uZZZZ", 6); xp[0] = 0;
    row(body, 6, 0, xp, 1, "bad-hex");
}

static void group_control(void) {
    uint32_t xp[2];
    begin_group("control");
    body[0] = 'a'; body[1] = 0x0A; body[2] = 'b';
    xp[0] = 1;
    row(body, 3, 0, xp, 1, "raw-0a");
}

static void group_offset(void) {
    uint32_t xp[4];
    char label[64];
    begin_group("offset");
    for (uint64_t k = 0; k <= 8; k++) {
        simple_at(body, 16, k);
        xp[0] = (uint32_t)k;
        snprintf(label, sizeof label, "in16@%llu", (unsigned long long)k);
        row(body, 16, 0, xp, 1, label);
    }
    {
        static const uint64_t at[5] = {60, 61, 62, 63, 64};
        for (unsigned i = 0; i < 5; i++) {
            simple_at(body, 80, at[i]);
            xp[0] = (uint32_t)at[i];
            snprintf(label, sizeof label, "in80@%llu",
                     (unsigned long long)at[i]);
            row(body, 80, 0, xp, 1, label);
        }
    }
}

static void group_multi(void) {
    uint32_t xp[8];
    begin_group("multi");
    memcpy(body, "a\\nb\\tc", 7);
    xp[0] = 1; xp[1] = 4;
    row(body, 7, 0, xp, 2, "two-simple");
    memcpy(body, "x\\n\\uD83D\\uDE00y", 16);
    xp[0] = 1; xp[1] = 3; xp[2] = 9;
    row(body, 16, 0, xp, 3, "simple+pair");
    memcpy(body, "\\uD83D\\uDE00\\n", 14);
    xp[0] = 0; xp[1] = 6; xp[2] = 12;
    row(body, 14, 0, xp, 3, "pair+simple");
    for (int i = 0; i < 90; i++) body[i] = 'a';
    body[20] = '\\'; body[21] = 'n';
    body[80] = '\\'; body[81] = 't';
    xp[0] = 20; xp[1] = 80;
    row(body, 90, 0, xp, 2, "far-apart");
}

static void group_carry(void) {
    uint32_t xp[8];
    begin_group("carry");
    simple_at(body, 8, 3);
    xp[0] = 64 + 3;
    row(body, 8, 64, xp, 1, "pos0-64");
    xp[0] = 0; xp[1] = 64 + 3; xp[2] = 72; xp[3] = 99;
    row(body, 8, 64, xp, 4, "below-and-above");
    xp[0] = 0; xp[1] = 1; xp[2] = 63; xp[3] = 64 + 3; xp[4] = 72;
    row(body, 8, 64, xp, 5, "three-below");
}

static void group_empty(void) {
    begin_group("empty");
    body[0] = 0;
    row(body, 0, 0, NULL, 0, "empty");
}

int main(void) {
    unsigned long expected = 8 + 11 + 3 + 4 + 4 + 1 + (9 + 5) + 4 + 3 + 1;

    group_simple();
    group_u_bmp();
    group_pair();
    group_pair_edge();
    group_refused();
    group_control();
    group_offset();
    group_multi();
    group_carry();
    group_empty();

    printf("\n");
    for (unsigned g = 0; g < ngroups; g++)
        printf("group\t%s\t%lu\n", group_name[g], group_rows[g]);
    printf("total\trows\t%lu\n", rows);
    printf("total\texpected\t%lu\n", expected);
    printf("total\tdiffer\t%lu\n", differs);

    if (rows != expected) {
        fprintf(stderr, "setup: %lu rows, the group bounds add to %lu\n", rows,
                expected);
        return 2;
    }
    return differs ? 1 : 0;
}
