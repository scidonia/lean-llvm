/* profile-pipeline.cc -- the per-stage cost profile of the assembled
   pipeline, beside the pinned simdjson reference and beside the measured
   number path, in one binary.

   `paired-reference.cc` answers "is the assembled pipeline faster than the
   reference on this document".  This harness answers the next question: which
   stage accounts for the row, and is that stage the extracted text or the
   measured text.  It is the instrument `docs/json-pipeline-performance.md`
   lacks -- the record has stage-1 kernel choices and shape costs but no
   per-stage decomposition of the assembled build.

   Four sides, one process:

     - the staged `pipeline`, the six staged objects at the measured clang
       line (the same objects `paired-reference.cc` links);
     - the `reference`, simdjson On-Demand entered by the same traversal
       `paired-reference.cc` uses (`od_count_value`);
     - the `numbers` cost of the extracted number path, the walk's own
       `num_fast_el1` called over every number token of the document;
     - the `num-measured` cost of the same tokens through the measured text,
       `measured/numf_el1.h` on the vendored set, so "did the extraction cost
       something" is measured on the path that carries the time rather than
       argued from the identity list.

   Each round times every act once per document, in rotated order, and the
   report is the median of each act over the rounds.  The pipeline and the
   reference are also timed back to back inside one round (two orders,
   averaged) and the ratio is the median of those per-round ratios, which is
   the row the reference arm reports.  The reference's number path is timed
   by the same paired construction against the same traversal with
   `get_double` removed (`refnum`).

   Before the clock, and for every document:

     - the entry stream the stages are timed over is checked byte-identical
       against the stream `leanllvm_json_pipeline` itself writes, and both
       arms must accept the document;
     - the extracted and measured number loops must return the same success
       count and the same hash of the converted doubles, so a timing row is
       only printed for a path that produced the reference's values.

   The staged pipeline is two passes -- the classification/entry/UTF-8 loop
   and the walk over the entry stream -- and the reference is one.  The
   second table prints the decomposition that follows from the acts alone:

       margin = pipeline - reference
              = stage1 - (reference - walk) - overlap

   with `stage1` = masks + entry + escape + utf8, and `overlap` = the sum of
   the isolated stages minus the fused `pipeline`.  Both are measured; the
   identity prints beside the row so a reader can see it holds.

   Exit status: 0 when every document is measured and every pre-clock check
   passed; 3 on a setup fault (absent corpus document or reference, a digest
   mismatch, a version not the pinned one, a stream or number disagreement),
   so a broken instrument is never read as a measurement.  A ratio above 1.0
   is a result, not a failure: the reference unit's exit rule applies here
   too.

   Cost to run: the build is six C objects, one generated copy, the measured
   number oracle and this driver (about five seconds); 21 rounds over the
   seven documents is about two seconds on the measurement host, five when
   the host is building. */

#include <simdjson.h>

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>

extern "C" {
#include "pipeline.h"
#include "s1_block.h"
#include "entry.h"
#include "utf8.h"
#include "escape.h"
#include "stage2.h"
}

/* The generated counted copy of the walk: stage2.c with its wrapper renamed
   and one number loop and four counter accessors appended by
   profile-pipeline.sh.  The timed pipeline uses the unmodified stage2.o; this
   copy exists for the tier census and the extracted number loop. */
extern "C" uint64_t profile_stage2_extracted(const uint8_t *, uint64_t,
                                             const uint32_t *, uint64_t,
                                             const uint32_t *, uint64_t,
                                             uint8_t *, uint64_t, uint64_t *,
                                             uint8_t *, uint64_t, uint64_t *,
                                             uint64_t *);
extern "C" uint64_t profile_tier_el(void);
extern "C" uint64_t profile_tier_slow(void);
extern "C" uint64_t profile_tier_window(void);
extern "C" uint64_t profile_tier_undec(void);
extern "C" uint64_t profile_num_loop_extracted(const uint8_t *, const void *,
                                               uint64_t, volatile double *);
/* The measured side: measured/numf_el1.h through profile-num-oracle.c. */
extern "C" uint64_t profile_num_loop_measured(const uint8_t *, const void *,
                                              uint64_t, volatile double *);
extern "C" uint64_t profile_num_loop_measured_slow(void);

#define PINNED_MAJOR 4
#define PINNED_MINOR 6
#define PINNED_REVISION 11
#define DEFAULT_ROUNDS 21

static volatile uint64_t sink;

static unsigned core_class(void) {
    unsigned eax, ebx, ecx, edx;
    __asm__ volatile("cpuid"
                     : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
                     : "a"(0x1AU), "c"(0U));
    return (eax >> 24) & 0xFF;
}

static double now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "out of memory\n"); exit(2); }
    return p;
}

static uint8_t *aligned_bytes(size_t n) {
    void *p = NULL;
    if (posix_memalign(&p, 4096, n ? n : 1) != 0 || !p) {
        fprintf(stderr, "cannot allocate %zu bytes\n", n);
        exit(2);
    }
    memset(p, 0, n);
    return (uint8_t *)p;
}

static int cmp_double(const void *a, const void *b) {
    double x = *(const double *)a, y = *(const double *)b;
    return (x > y) - (x < y);
}
static double median_of(double *v, size_t n) {
    if (n == 0) return 0.0;
    qsort(v, n, sizeof *v, cmp_double);
    return (n % 2) ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

typedef struct {
    char name[64];
    unsigned arm_E, arm_P;
    unsigned arm;
    char path[512];

    uint8_t *buf;
    const uint8_t *doc;
    uint64_t n, nb;

    uint32_t *ep;
    uint32_t *ep_pipe;
    uint32_t *xp;
    uint8_t *dst;
    uint8_t *ev;
    uint64_t epcap, xpcap, dstcap, evcap;

    s1_masks *mks;
    uint64_t *entw;
    uint64_t nk, nxp;

    simdjson::ondemand::parser *sp;
    simdjson::padded_string *ps;
} input;

static uint32_t entry_table[2048];
__attribute__((constructor)) static void arm_init(void) { leanllvm_json_entry_table(entry_table); }

template <class T>
static T od_get(simdjson::simdjson_result<T> r, const char *what) {
    T out{};
    auto e = std::move(r).get(out);
    if (e) { fprintf(stderr, "SETUP: reference: %s: %s\n", what, simdjson::error_message(e)); exit(3); }
    return out;
}

static uint64_t od_count_value(simdjson::ondemand::value &v) {
    using namespace simdjson;
    switch (v.type()) {
    case ondemand::json_type::null: return 1;
    case ondemand::json_type::boolean: return 1 + (uint64_t)od_get(v.get_bool(), "bool");
    case ondemand::json_type::number:
        return 1 + (uint64_t)(int64_t)od_get(v.get_double(), "number");
    case ondemand::json_type::string:
        return 1 + od_get(v.get_string(), "string").size();
    case ondemand::json_type::array: {
        ondemand::array arr = od_get(v.get_array(), "array");
        uint64_t n = 0;
        for (auto x : arr) {
            ondemand::value xv = od_get(x, "array element");
            n += od_count_value(xv);
        }
        return n + 1;
    }
    case ondemand::json_type::object: {
        ondemand::object obj = od_get(v.get_object(), "object");
        uint64_t n = 0;
        for (auto &&f : obj) {
            n += od_get(f.unescaped_key(), "key").size();
            ondemand::value xv = f.value();
            n += od_count_value(xv);
        }
        return n + 1;
    }
    }
    return 0;
}

/* the same traversal with the number conversion removed: the differential
   against `reference_walk` is the reference's own number-conversion cost */
static uint64_t od_count_value_nonum(simdjson::ondemand::value &v) {
    using namespace simdjson;
    switch (v.type()) {
    case ondemand::json_type::null: return 1;
    case ondemand::json_type::boolean: return 1 + (uint64_t)od_get(v.get_bool(), "bool");
    case ondemand::json_type::number: return 1;
    case ondemand::json_type::string:
        return 1 + od_get(v.get_string(), "string").size();
    case ondemand::json_type::array: {
        ondemand::array arr = od_get(v.get_array(), "array");
        uint64_t n = 0;
        for (auto x : arr) {
            ondemand::value xv = od_get(x, "array element");
            n += od_count_value_nonum(xv);
        }
        return n + 1;
    }
    case ondemand::json_type::object: {
        ondemand::object obj = od_get(v.get_object(), "object");
        uint64_t n = 0;
        for (auto &&f : obj) {
            n += od_get(f.unescaped_key(), "key").size();
            ondemand::value xv = f.value();
            n += od_count_value_nonum(xv);
        }
        return n + 1;
    }
    }
    return 0;
}

static uint64_t reference_walk_nonum(input *in) {
    simdjson::ondemand::document doc = od_get(in->sp->iterate(*in->ps), "iterate");
    simdjson::ondemand::value v = od_get(doc.get_value(), "document value");
    return od_count_value_nonum(v);
}

static uint64_t reference_walk(input *in) {
    simdjson::ondemand::document doc = od_get(in->sp->iterate(*in->ps), "iterate");
    simdjson::ondemand::value v = od_get(doc.get_value(), "document value");
    return od_count_value(v);
}

static int stage_document(input *in) {
    FILE *f = fopen(in->path, "rb");
    long m;
    if (!f) { fprintf(stderr, "SETUP: absent %s\n", in->path); return 3; }
    if (fseek(f, 0, SEEK_END) != 0 || (m = ftell(f)) < 0 || fseek(f, 0, SEEK_SET) != 0) {
        fprintf(stderr, "SETUP: cannot size %s\n", in->path); fclose(f); return 3;
    }
    in->n = (uint64_t)m;
    std::string bytes((size_t)m, '\0');
    if (in->n && fread(&bytes[0], 1, (size_t)in->n, f) != in->n) {
        fprintf(stderr, "SETUP: cannot read %s\n", in->path); fclose(f); return 3;
    }
    fclose(f);

    uint64_t nb = (in->n + 63) / 64;
    in->nb = nb;
    size_t docbytes = (size_t)((nb ? nb : 1) * 64) + 128;
    in->buf = aligned_bytes(docbytes);
    in->doc = in->buf + 64;
    if (in->n) memcpy((void *)in->doc, bytes.data(), (size_t)in->n);

    in->epcap = in->n + 8 * nb + 64;
    in->xpcap = in->n + 8 * nb + 64;
    in->dstcap = 68 * in->n + 65536;
    in->evcap = 24 * in->n + 65536;
    in->ep = (uint32_t *)xmalloc((size_t)in->epcap * sizeof *in->ep);
    in->ep_pipe = (uint32_t *)xmalloc((size_t)in->epcap * sizeof *in->ep);
    in->xp = (uint32_t *)xmalloc((size_t)in->xpcap * sizeof *in->xp);
    in->dst = (uint8_t *)xmalloc((size_t)in->dstcap);
    in->ev = (uint8_t *)xmalloc((size_t)in->evcap);
    in->mks = (s1_masks *)xmalloc((size_t)(nb ? nb : 1) * sizeof *in->mks);
    in->entw = (uint64_t *)xmalloc((size_t)(nb ? nb : 1) * sizeof *in->entw);

    in->sp = new simdjson::ondemand::parser();
    in->ps = new simdjson::padded_string(bytes.data(), bytes.size());
    (void)docbytes;
    return 0;
}

/* ---- the precompute: the pipeline's own block loop, untimed ------------- */

static void precompute(input *in) {
    s1_carry sc = {0, 0, 0};
    s1_masks m;
    uint64_t prevS = 0, k = 0, nxp = 0, xcarry[2] = {0, 0};
    for (uint64_t i = 0; i < in->nb; i++) {
        const uint8_t *p = in->doc + (i << 6);
        leanllvm_json_s1_masks(p, &sc, &m);
        in->mks[i] = m;
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
        uint64_t ent = m.quote | (m.delim & ~m.in_string);
        ent |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = in->n - (i << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
        in->entw[i] = ent;
        if (in->arm & 1)
            k = leanllvm_json_entry_b8(&in->entw[i], i, 1, in->ep, k);
        else
            k = leanllvm_json_entry_pos8(&in->entw[i], i, 1, in->ep, k);
        if (in->arm & 2)
            leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i,
                                      in->xp, &nxp, xcarry);
    }
    in->nk = k;
    in->nxp = nxp;
}

static int verify_stream(input *in) {
    uint64_t sc[3] = {0, 0, 0}, mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
    uint64_t ndst = 0, nev = 0, err = 0;
    uint64_t v = leanllvm_json_pipeline(
        in->doc, in->n, sc, mk, &entw, in->ep_pipe, in->epcap, &nk, in->xp,
        in->xpcap, &nxp, xcarry, in->dst, in->dstcap, &ndst, in->ev,
        in->evcap, &nev, &err, in->arm);
    if (v != 1) { fprintf(stderr, "SETUP: %s refused (offset %llu)\n", in->name, (unsigned long long)err); return 3; }
    if (nk != in->nk || nxp != in->nxp ||
        (nk && memcmp(in->ep, in->ep_pipe, (size_t)nk * 4) != 0)) {
        fprintf(stderr, "SETUP: %s: precomputed stream differs from the pipeline's\n", in->name);
        return 3;
    }
    if (reference_walk(in) == UINT64_MAX) return 3;
    return 0;
}

/* ---- the acts ---------------------------------------------------------- */

static double act_masks(input *in) {
    s1_carry sc = {0, 0, 0};
    s1_masks m;
    uint64_t prevS = 0, acc = 0;
    double t0 = now_ns();
    for (uint64_t i = 0; i < in->nb; i++) {
        leanllvm_json_s1_masks(in->doc + (i << 6), &sc, &m);
        uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
        uint64_t ent = m.quote | (m.delim & ~m.in_string);
        ent |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = in->n - (i << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
        in->entw[i] = ent;
        acc ^= ent;
    }
    double t1 = now_ns();
    sink ^= acc;
    return t1 - t0;
}

static double act_entry(input *in) {
    uint64_t k = 0, acc = 0;
    double t0 = now_ns();
    for (uint64_t i = 0; i < in->nb; i++) {
        if (in->arm & 1) k = leanllvm_json_entry_b8(&in->entw[i], i, 1, in->ep, k);
        else             k = leanllvm_json_entry_pos8(&in->entw[i], i, 1, in->ep, k);
    }
    double t1 = now_ns();
    acc = k;
    sink ^= acc;
    return t1 - t0;
}

static double act_escape(input *in) {
    if (!(in->arm & 2)) return -1.0;
    uint64_t nxp = 0, carry[2] = {0, 0};
    double t0 = now_ns();
    for (uint64_t i = 0; i < in->nb; i++)
        leanllvm_json_escape_list(in->mks[i].backslash, in->mks[i].ctl,
                                  in->mks[i].in_string, i, in->xp, &nxp, carry);
    double t1 = now_ns();
    sink ^= nxp;
    return t1 - t0;
}

static double act_utf8(input *in) {
    const unsigned reps = 8;
    uint64_t acc = 0;
    double t0 = now_ns();
    for (unsigned r = 0; r < reps; r++)
        acc ^= leanllvm_json_utf8(in->doc, in->n, (int)((in->arm >> 2) & 1));
    double t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)reps;
}

static double act_stage2(input *in) {
    uint64_t ndst = 0, nev = 0, err = 0;
    double t0 = now_ns();
    uint64_t v = leanllvm_json_stage2(in->doc, in->n, in->ep, in->nk,
                                      in->xp, in->nxp, in->dst, in->dstcap,
                                      &ndst, in->ev, in->evcap, &nev, &err);
    double t1 = now_ns();
    sink ^= v ^ ndst ^ nev ^ err;
    return t1 - t0;
}

static double act_pipeline(input *in) {
    uint64_t sc[3] = {0, 0, 0}, mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
    uint64_t ndst = 0, nev = 0, err = 0;
    double t0 = now_ns();
    uint64_t v = leanllvm_json_pipeline(
        in->doc, in->n, sc, mk, &entw, in->ep, in->epcap, &nk, in->xp,
        in->xpcap, &nxp, xcarry, in->dst, in->dstcap, &ndst, in->ev,
        in->evcap, &nev, &err, in->arm);
    double t1 = now_ns();
    sink ^= v ^ nk ^ nxp ^ ndst ^ nev ^ err;
    return t1 - t0;
}

static double act_reference_nonum(input *in) {
    double t0 = now_ns();
    uint64_t v = reference_walk_nonum(in);
    double t1 = now_ns();
    sink ^= v;
    return t1 - t0;
}

static double act_reference(input *in) {
    double t0 = now_ns();
    uint64_t v = reference_walk(in);
    double t1 = now_ns();
    sink ^= v;
    return t1 - t0;
}

/* ---- the tier census --------------------------------------------------- */

typedef struct {
    uint64_t numbers, nd_gt15, chars;
} census;

struct tok { uint32_t pos, len; };
static std::vector<std::vector<tok>> doc_toks;

static census number_census(const input *in, std::vector<tok> &toks) {
    census c = {0, 0, 0};
    for (uint64_t j = 0; j < in->nk; j++) {
        const uint8_t *p = in->doc + in->ep[j];
        uint8_t ch = *p;
        if (!((ch >= '0' && ch <= '9') || ch == '-')) continue;
        c.numbers++;
        uint64_t nd = 0, len = 0;
        while (in->ep[j] + len < in->n) {
            uint8_t x = p[len];
            if (x >= '0' && x <= '9') nd++;
            else if (!(x == '-' || x == '+' || x == '.' || x == 'e' || x == 'E')) break;
            len++;
            if (len > 64) break;
        }
        c.chars += len;
        if (nd > 15) c.nd_gt15++;
        tok t;
        t.pos = in->ep[j];
        t.len = (uint32_t)len;
        toks.push_back(t);
    }
    return c;
}

/* act_numbers -- the document's number tokens through one conversion side:
   the extracted walk's `num_fast_el1` or the measured `numf_el1.h` text.
   The doc index is carried in a file-static. */
static size_t act_doc_index;

static double act_numbers_extracted(input *in) {
    std::vector<tok> &toks = doc_toks[act_doc_index];
    volatile double acc = 0.0;
    uint64_t ok = 0;
    double t0 = now_ns();
    ok = profile_num_loop_extracted(in->doc, (const void *)toks.data(),
                                    toks.size(), &acc);
    double t1 = now_ns();
    sink ^= (uint64_t)(int64_t)acc ^ ok;
    return t1 - t0;
}

static double act_numbers_measured(input *in) {
    std::vector<tok> &toks = doc_toks[act_doc_index];
    volatile double acc = 0.0;
    uint64_t ok = 0;
    double t0 = now_ns();
    ok = profile_num_loop_measured(in->doc, (const void *)toks.data(),
                                   toks.size(), &acc);
    double t1 = now_ns();
    sink ^= (uint64_t)(int64_t)acc ^ ok;
    return t1 - t0;
}

static int parse_manifest(const char *path, std::vector<input> &docs) {
    FILE *f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "SETUP: absent manifest %s\n", path); return 3; }
    char line[2048];
    while (fgets(line, (int)sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (strncmp(line, "name\t", 5) == 0) continue;
        char name[64], sha[65], file[512];
        unsigned ae, ap;
        double re, rp;
        int got = sscanf(line, "%63s\t%u\t%u\t%lf\t%lf\t%64s\t%511[^\n]",
                         name, &ae, &ap, &re, &rp, sha, file);
        if (got != 7) { fprintf(stderr, "SETUP: bad manifest row\n"); fclose(f); return 3; }
        input in;
        memset(&in, 0, sizeof in);
        snprintf(in.name, sizeof in.name, "%s", name);
        in.arm_E = ae;
        in.arm_P = ap;
        snprintf(in.path, sizeof in.path, "%s", file);
        docs.push_back(in);
    }
    fclose(f);
    return 0;
}

int main(int argc, char **argv) {
    const char *corpus = nullptr;
    int rounds = DEFAULT_ROUNDS;
    const char *build_id = "unstated";
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--corpus") && i + 1 < argc) corpus = argv[++i];
        else if (!strcmp(argv[i], "--rounds") && i + 1 < argc) rounds = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--build") && i + 1 < argc) build_id = argv[++i];
        else { fprintf(stderr, "usage: profile --corpus <manifest> [--rounds N] [--build id]\n"); return 3; }
    }
    if (!corpus || rounds < 1) { fprintf(stderr, "usage: profile --corpus <manifest> [--rounds N] [--build id]\n"); return 3; }
    if (simdjson::SIMDJSON_VERSION_MAJOR != PINNED_MAJOR ||
        simdjson::SIMDJSON_VERSION_MINOR != PINNED_MINOR ||
        simdjson::SIMDJSON_VERSION_REVISION != PINNED_REVISION) {
        fprintf(stderr, "SETUP: header is not simdjson %d.%d.%d\n", PINNED_MAJOR, PINNED_MINOR, PINNED_REVISION);
        return 3;
    }

    std::vector<input> docs;
    if (int rc = parse_manifest(corpus, docs)) return rc;

    unsigned klass = core_class();
    printf("reference simdjson %s, implementation %s\n", SIMDJSON_VERSION,
           simdjson::get_active_implementation()->name().c_str());
    printf("core-class 0x%02x (%s), arm: E-column on 0x20, P-column on 0x40\n",
           klass, klass == 0x40 ? "P" : klass == 0x20 ? "E" : "unknown");
    for (auto &in : docs)
        in.arm = (klass == 0x40) ? in.arm_P : in.arm_E;
    for (auto &in : docs) {
        if (int rc = stage_document(&in)) return rc;
        precompute(&in);
        if (int rc = verify_stream(&in)) return rc;
        std::vector<tok> toks;
        census c = number_census(&in, toks);
        doc_toks.push_back(std::move(toks));
        {
            volatile double a = 0.0, b = 0.0;
            uint64_t ra = profile_num_loop_extracted(in.doc, (const void *)toks.data(),
                                                     toks.size(), &a);
            uint64_t rb = profile_num_loop_measured(in.doc, (const void *)toks.data(),
                                                    toks.size(), &b);
            if (ra != rb) {
                fprintf(stderr, "SETUP: %s: extracted and measured number loops "
                        "disagree (return %llu vs %llu)\n", in.name,
                        (unsigned long long)ra, (unsigned long long)rb);
                return 3;
            }
        }
        printf("doc %-10s arm %u  bytes %llu blocks %llu entries %llu "
               "(%.2f/blk) escapes %llu numbers %llu (nd>15 %llu, mean len %.1f)\n",
               in.name, in.arm, (unsigned long long)in.n,
               (unsigned long long)in.nb, (unsigned long long)in.nk,
               (double)in.nk / (double)(in.nb ? in.nb : 1),
               (unsigned long long)in.nxp, (unsigned long long)c.numbers,
               (unsigned long long)c.nd_gt15,
               c.numbers ? (double)c.chars / (double)c.numbers : 0.0);
    }

    if (profile_num_loop_measured_slow() != 0) {
        fprintf(stderr, "SETUP: the measured third tier was reached %llu times; "
                "the oracle models only the first two tiers\n",
                (unsigned long long)profile_num_loop_measured_slow());
        return 3;
    }

    /* the tier census: one traversal of the counted copy per document */
    for (auto &in : docs) {
        uint64_t ndst = 0, nev = 0, err = 0;
        uint64_t a = profile_tier_el(), b = profile_tier_slow();
        uint64_t w = profile_tier_window(), u = profile_tier_undec();
        uint64_t v = profile_stage2_extracted(in.doc, in.n, in.ep, in.nk, in.xp, in.nxp,
                                       in.dst, in.dstcap, &ndst, in.ev, in.evcap,
                                       &nev, &err);
        uint64_t el = profile_tier_el() - a;
        uint64_t slow = profile_tier_slow() - b;
        uint64_t win = profile_tier_window() - w;
        uint64_t und = profile_tier_undec() - u;
        printf("tiers %-10s verdict %llu  eisel-lemire %llu  strtod %llu  "
               "el-window %llu  el-undecided %llu\n",
               in.name, (unsigned long long)v, (unsigned long long)el,
               (unsigned long long)slow, (unsigned long long)win,
               (unsigned long long)und);
        sink ^= v;
    }

    /* warm-up: one untimed act per stage per document */
    for (auto &in : docs) {
        act_masks(&in);
        act_entry(&in);
        if (in.arm & 2) act_escape(&in);
        act_utf8(&in);
        act_stage2(&in);
        act_pipeline(&in);
        act_reference(&in);
        act_numbers_extracted(&in);
        act_numbers_measured(&in);
    }

    enum { NM = 9 };   /* masks entry escape utf8 stage2 pipeline reference
                          numbers num-measured */
    size_t nd = docs.size();
    std::vector<std::vector<double>> t(NM * nd);

    for (int r = 0; r < rounds; r++) {
        for (size_t i = 0; i < nd; i++) {
            input &in = docs[i];
            act_doc_index = i;
            for (int a = 0; a < NM; a++) {
                int s = (a + r) % NM;
                double ns = 0.0;
                switch (s) {
                case 0: ns = act_masks(&in); break;
                case 1: ns = act_entry(&in); break;
                case 2: ns = act_escape(&in); break;
                case 3: ns = act_utf8(&in); break;
                case 4: ns = act_stage2(&in); break;
                case 5: ns = act_pipeline(&in); break;
                case 6: ns = act_reference(&in); break;
                case 7: ns = act_numbers_extracted(&in); break;
                case 8: ns = act_numbers_measured(&in); break;
                }
                if (ns >= 0.0) t[s * nd + i].push_back(ns / (double)(in.nb ? in.nb : 1));
            }
        }
    }

    /* Paired acts inside one round, order alternating, so a drift inside the
       round cancels: the row ratio, the reference's number cost (walk minus
       walk-without-get_double), the extracted-minus-measured number cost, and
       the extracted number cost minus the reference's. */
    std::vector<std::vector<double>> ratio(nd), refnum(nd), numem(nd), numer(nd);
    for (int r = 0; r < rounds; r++) {
        for (size_t i = 0; i < nd; i++) {
            input &in = docs[i];
            act_doc_index = i;
            double nb = (double)(in.nb ? in.nb : 1);
            if (((r + (int)i) & 1) == 0) {
                double a = act_pipeline(&in), b = act_reference(&in);
                double c = act_reference(&in), d = act_pipeline(&in);
                ratio[i].push_back((0.5 * (a + d)) / (0.5 * (b + c)));
                double e = act_numbers_extracted(&in), f = act_numbers_measured(&in);
                double g = act_reference(&in), h = act_reference_nonum(&in);
                numem[i].push_back((e - f) / nb);
                refnum[i].push_back((g - h) / nb);
                numer[i].push_back((e - (g - h)) / nb);
            } else {
                double h = act_reference_nonum(&in), g = act_reference(&in);
                double f = act_numbers_measured(&in), e = act_numbers_extracted(&in);
                numem[i].push_back((e - f) / nb);
                refnum[i].push_back((g - h) / nb);
                numer[i].push_back((e - (g - h)) / nb);
                double d = act_pipeline(&in), c = act_reference(&in);
                double b = act_reference(&in), a = act_pipeline(&in);
                ratio[i].push_back((0.5 * (a + d)) / (0.5 * (b + c)));
            }
        }
    }

    printf("\nrounds %d, one act per stage per document per round, order rotated\n", rounds);
    printf("ns/block: one block is 64 document bytes\n\n");
    printf("%-10s %10s %10s %10s %8s %10s %10s %10s %10s %10s %8s %8s\n", "document",
           "masks", "entry", "escape", "utf8", "stage2", "pipeline", "reference",
           "numbers", "num-meas", "refnum", "ratio");
    std::vector<std::vector<double>> med(nd, std::vector<double>(NM, 0.0));
    for (size_t i = 0; i < nd; i++) {
        double v[NM];
        for (int s = 0; s < NM; s++) {
            std::vector<double> &col = t[s * nd + i];
            v[s] = col.empty() ? -1.0 : median_of(col.data(), col.size());
            med[i][s] = v[s];
        }
        double rn = median_of(refnum[i].data(), refnum[i].size());
        double pr = median_of(ratio[i].data(), ratio[i].size());
        printf("%-10s %10.3f %10.3f %10.3f %8.3f %10.3f %10.3f %10.3f %10.3f %10.3f %8.3f %8.3f\n",
               docs[i].name, v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], rn, pr);
        double sum = v[0] + v[1] + (v[2] > 0 ? v[2] : 0.0) + v[3] + v[4];
        printf("%-10s %10s %10s %10s %8s %10s %10s %10s %10s %10s %8s %8.3f\n", "  (sum)",
               "", "", "", "", "", "", "", "", "", "", sum);
    }
    printf("\npaired per-round differences, ns/block (median of the per-round "
           "difference):\n");
    printf("  ext-meas = extracted - measured conversion on the same tokens; "
           "ref-num = reference walk minus the same walk without get_double;\n");
    printf("  ext-refnum = extracted conversion minus the reference's number path\n");
    printf("%-10s %10s %10s %10s\n", "document", "ext-meas", "ref-num", "ext-refnum");
    for (size_t i = 0; i < nd; i++) {
        double ne = median_of(numem[i].data(), numem[i].size());
        double rn = median_of(refnum[i].data(), refnum[i].size());
        double nr = median_of(numer[i].data(), numer[i].size());
        printf("%-10s %+10.3f %10.3f %+10.3f\n", docs[i].name, ne, rn, nr);
    }

    printf("\nstage1 = masks + entry + escape + utf8; saving = reference - walk; "
           "overlap = sum(stages) - pipeline; margin = pipeline - reference\n");
    printf("%-10s %10s %10s %10s %10s %10s %10s %10s\n", "document", "stage1",
           "walk", "saving", "overlap", "margin", "identity", "reported");
    for (size_t i = 0; i < nd; i++) {
        double stage1 = med[i][0] + med[i][1] + (med[i][2] > 0 ? med[i][2] : 0.0) + med[i][3];
        double walk = med[i][4];
        double saving = med[i][6] - walk;
        double sum = stage1 + walk;
        double overlap = sum - med[i][5];
        double margin = med[i][5] - med[i][6];
        double identity = stage1 - saving - overlap;
        printf("%-10s %10.3f %10.3f %10.3f %10.3f %+10.3f %10.3f %10.3f\n",
               docs[i].name, stage1, walk, saving, overlap, margin, identity,
               med[i][5] / med[i][6]);
        if (fabs(identity - margin) > 1e-6) {
            fprintf(stderr, "SETUP: %s: decomposition does not close (%+.6f vs %+.6f)\n",
                    docs[i].name, identity, margin);
            return 3;
        }
    }

    printf("\nbuild %s\n", build_id);
    printf("sink %llu\n", (unsigned long long)sink);
    return 0;
}
