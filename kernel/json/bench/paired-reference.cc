/* paired-reference.cc -- Arm C: the assembled pipeline against the pinned
   external reference, over the seven measured documents, in one binary.

   `paired.sh --unit reference` compiles this harness together with the staged
   pipeline -- `kernel/json/pipeline.c` and the five units as their own
   translation units, the form the model's records are stated at -- and links
   it against the reference parser named on the configuration line the shell
   prints.  Both arms of every row live in this one binary and are entered from
   it: the pipeline through `leanllvm_json_pipeline`, the reference through
   simdjson On-Demand's `iterate`.  A cross-binary comparison is not a
   comparison (`docs/json-pipeline-performance.md` §7.2), so the two numbers of
   a row are taken in one process, in one window, on one document.

   ## The reference is named, not assumed

   The measured record (`docs/json-pipeline-performance.md` §3) does not state
   which simdjson release its ratios were taken against.  The scratch harness
   that produced them is linked against the store's simdjson 4.6.11 -- its build
   line names that path and its RUNPATH resolves there -- so 4.6.11 is the
   reference this arm measures against, and the version question is answered
   before any row is compared rather than after.  The harness prints the
   header's version and the active implementation's name, and refuses to report
   a row unless both name the pinned release.  A 4.6.11 row is therefore a
   comparison against a named reference: it is not presented as a reproduction
   of the record's numbers, which came from a scratch tree, a different
   pipeline build and a rotation this harness does not share.

   ## The document and its arm

   The corpus is `reference-corpus.tsv`, read here: each row names the document,
   the arm the record's decision table selects for it on each core class, the
   record's ratio, and the bytes' digest.  The digest is checked by the shell
   before this binary runs, so a substituted file is refused rather than
   measured.  The arm is the caller's selector `pipeline.h` documents -- bit 0
   B8/POS8, bit 1 the escape list, bit 2 the gated/ungated UTF-8 stage -- not a
   re-derived classifier: the record's decisions are the parameter.

   ## One act

   One pipeline act is one call over one document with every cursor at zero and
   the caller's buffers staged as `pipeline.h` describes: the document padded to
   its 64-byte block boundary with zero bytes and three zero bytes before it.
   One reference act is one `iterate` over the same document's bytes followed by
   the full value traversal the record's reference binary performed -- every
   member key unescaped, every string fetched (which validates it), every number
   converted.  Both acts allocate nothing per call: the reference's parser and
   this file's buffers are staged before the clock.

   ## Before the clock

   Both arms run every document once, and the pipeline's verdict and the
   reference's traversal must both accept it.  The events, the arena and the
   first error offset are not compared with the reference here: that
   differential is `tests/json-pipeline/check.sh`'s, and a second, weaker copy
   of it would be a gate that does not gate.  What this harness refuses is a
   document either arm does not accept, because a timing over a refused document
   measures the refusal path and not the pass.

   ## The row

   `rounds` interleaved rounds, warmed once.  Every round runs both arms twice
   on every document -- once in each order -- and averages each arm's two
   readings, so a drift inside the round cancels.  The report prints, per
   document, each arm's median ns/block, the median of the per-round ratios,
   the ratio's per-round range, the arm, and the record's ratio for the core
   class the run is pinned to.  `ratio = pipeline / reference`: below 1.0 means
   the pipeline is faster.  `d = record - measured` is printed for the reader
   and carries no verdict -- whether the milestone is met is a claim about the
   project, not about this instrument. */

#include "simdjson.h"

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

/* The staged pipeline's ABI.  `pipeline.h` is a C header and this translation
   unit is C++ because the reference is a C++ library; the two entry points are
   declared here with C linkage rather than included, so the header stays one
   declaration for one language. */
extern "C" {
uint64_t leanllvm_json_pipeline(const uint8_t *b, uint64_t n,
                                uint64_t *sc, uint64_t *mk, uint64_t *entw,
                                uint32_t *ep, uint64_t epcap, uint64_t *nk,
                                uint32_t *xp, uint64_t xpcap, uint64_t *nxp,
                                uint64_t *xcarry,
                                uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                                uint8_t *ev, uint64_t evcap, uint64_t *nev,
                                uint64_t *err, uint64_t arm);
void leanllvm_json_entry_table(uint32_t *);
}

/* The reference release this arm measures against.  The shell also checks the
   header enum before compiling; this is the check at run time, where a binary
   linked against a different soname would otherwise report a row. */
#define PINNED_MAJOR 4
#define PINNED_MINOR 6
#define PINNED_REVISION 11

/* Bytes of document work per timed act, as the in-tree arm uses: a round's acts
   are tens of milliseconds, where a scheduler quantum or a frequency step is
   not a large fraction of the act. */
#define ACT_BYTES ((size_t)1 << 23)

#define DEFAULT_ROUNDS 15

static volatile uint64_t sink;

static void setup_fail(const char *fmt, const char *what, const char *detail) {
    fprintf(stderr, "SETUP: ");
    fprintf(stderr, fmt, what, detail);
    fprintf(stderr, "\n");
    exit(3);
}

static double now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC_RAW, &t);
    return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

/* The core class the record reports its ratios per (§7.3): 0x40 is the P-core
   class, 0x20 the E-core class.  The arm a document takes can depend on it --
   `canada` selects POS8 on E and B8 on P -- so the arm is resolved here from
   the same word the record's threshold is stated at. */
static unsigned core_class(void) {
    unsigned eax, ebx, ecx, edx;
    __asm__ volatile("cpuid"
                     : "=a"(eax), "=b"(ebx), "=c"(ecx), "=d"(edx)
                     : "a"(0x1AU), "c"(0U));
    return (eax >> 24) & 0xFF;
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

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) {
        fprintf(stderr, "paired-reference: out of memory (%zu bytes)\n", n);
        exit(2);
    }
    return p;
}

static uint8_t *aligned_bytes(size_t n) {
    void *p = NULL;
    if (posix_memalign(&p, 4096, n ? n : 1) != 0 || !p) {
        fprintf(stderr, "paired-reference: cannot allocate %zu bytes\n", n);
        exit(2);
    }
    memset(p, 0, n);
    return (uint8_t *)p;
}

typedef struct {
    char name[64];
    unsigned arm_E, arm_P;
    unsigned arm;              /* resolved from the core class */
    double record_E, record_P;
    char sha256[65];
    char path[512];

    uint8_t *buf;              /* 64 zero bytes, then the document, padded */
    const uint8_t *doc;
    uint64_t n;                /* the document's own length */
    uint64_t nb;               /* its block count, 64 bytes to a block */

    uint32_t *ep;
    uint32_t *xp;
    uint8_t *dst;
    uint8_t *ev;
    uint64_t epcap, xpcap, dstcap, evcap;

    simdjson::ondemand::parser *sp;
    simdjson::padded_string *ps;
} input;

/* The entry table is the caller's (`pipeline.h` states the precondition): the
   pos8 emitter reads a file-static table, and a run whose table is not built
   refuses every document at offset 0. */
static uint32_t entry_table[2048];

__attribute__((constructor)) static void reference_arm_init(void) {
    leanllvm_json_entry_table(entry_table);
}

/* parse_manifest -- read the corpus table.  A missing document is named with
   its digest: the exact artefact the harness lacks, not a silent short corpus. */
static int parse_manifest(const char *path, std::vector<input> &docs) {
    FILE *f = fopen(path, "rb");
    if (!f) {
        fprintf(stderr, "SETUP: absent: corpus manifest %s\n", path);
        return 3;
    }
    char line[2048];
    while (fgets(line, (int)sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (strncmp(line, "name\t", 5) == 0) continue;
        char name[64], sha[65], file[512];
        unsigned ae, ap;
        double re, rp;
        int got = sscanf(line, "%63s\t%u\t%u\t%lf\t%lf\t%64s\t%511[^\n]",
                         name, &ae, &ap, &re, &rp, sha, file);
        if (got != 7) {
            fprintf(stderr, "SETUP: corpus manifest row is not seven columns: %s",
                    line);
            fclose(f);
            return 3;
        }
        if (strcmp(sha, "-") == 0) {
            fprintf(stderr, "SETUP: corpus row %s carries no digest\n", name);
            fclose(f);
            return 3;
        }
        input in;
        memset(&in, 0, sizeof in);
        snprintf(in.name, sizeof in.name, "%s", name);
        in.arm_E = ae;
        in.arm_P = ap;
        in.record_E = re;
        in.record_P = rp;
        snprintf(in.sha256, sizeof in.sha256, "%s", sha);
        snprintf(in.path, sizeof in.path, "%s", file);
        docs.push_back(in);
    }
    fclose(f);
    if (docs.empty()) {
        fprintf(stderr, "SETUP: corpus manifest %s names no document\n", path);
        return 3;
    }
    return 0;
}

/* stage_document -- read one file and stage it as the pipeline's `pre`
   requires, plus the reference's own padded copy.  The capacities follow the
   units' stated obligations, as the in-tree pipeline arm sizes them. */
static int stage_document(input *in) {
    FILE *f = fopen(in->path, "rb");
    long m;
    uint64_t nb, blocks;
    size_t docbytes;
    std::string bytes;

    if (!f) {
        fprintf(stderr, "SETUP: absent: document %s (%s, sha256 %s)\n",
                in->name, in->path, in->sha256);
        return 3;
    }
    if (fseek(f, 0, SEEK_END) != 0 || (m = ftell(f)) < 0 ||
        fseek(f, 0, SEEK_SET) != 0) {
        fprintf(stderr, "SETUP: cannot size %s\n", in->path);
        fclose(f);
        return 3;
    }
    in->n = (uint64_t)m;
    bytes.resize((size_t)m);
    if (in->n && fread(&bytes[0], 1, (size_t)in->n, f) != in->n) {
        fprintf(stderr, "SETUP: cannot read %s\n", in->path);
        fclose(f);
        return 3;
    }
    fclose(f);

    nb = (in->n + 63) / 64;
    blocks = nb ? nb : 1;
    docbytes = (size_t)(blocks * 64) + 128;
    in->buf = aligned_bytes(docbytes);
    in->doc = in->buf + 64;
    if (in->n) memcpy((void *)in->doc, bytes.data(), (size_t)in->n);
    in->nb = nb;

    in->epcap = in->n + 8 * blocks + 64;
    in->xpcap = in->n + 8 * blocks + 64;
    in->dstcap = 68 * in->n + 65536;
    in->evcap = 24 * in->n + 65536;
    in->ep = (uint32_t *)xmalloc((size_t)in->epcap * sizeof *in->ep);
    in->xp = (uint32_t *)xmalloc((size_t)in->xpcap * sizeof *in->xp);
    in->dst = (uint8_t *)xmalloc((size_t)in->dstcap);
    in->ev = (uint8_t *)xmalloc((size_t)in->evcap);

    in->sp = new simdjson::ondemand::parser();
    in->ps = new simdjson::padded_string(bytes.data(), bytes.size());
    return 0;
}

/* ------------------------------------------------------------- the reference */

template <class T>
static T od_get(simdjson::simdjson_result<T> r, const char *what) {
    T out{};
    auto e = std::move(r).get(out);
    if (e) {
        fprintf(stderr, "SETUP: reference: %s: %s\n", what,
                simdjson::error_message(e));
        exit(3);
    }
    return out;
}

/* the reference act -- the traversal the record's reference binary performed:
   every string fetched (which validates it), every key unescaped, every number
   converted, and a count accumulated so the compiler cannot elide the walk. */
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

static uint64_t reference_walk(input *in) {
    simdjson::ondemand::document doc = od_get(in->sp->iterate(*in->ps), "iterate");
    simdjson::ondemand::value v = od_get(doc.get_value(), "document value");
    return od_count_value(v);
}

/* ---------------------------------------------------------------- the acts */

/* one pipeline act's work, without timing it */
static void pipeline_call(input *in, uint64_t *verdict, uint64_t *err_out) {
    uint64_t sc[3] = {0, 0, 0};
    uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
    uint64_t ndst = 0, nev = 0, err = 0;
    *verdict = leanllvm_json_pipeline(
        in->doc, in->n, sc, mk, &entw, in->ep, in->epcap, &nk, in->xp,
        in->xpcap, &nxp, xcarry, in->dst, in->dstcap, &ndst, in->ev, in->evcap,
        &nev, &err, in->arm);
    *err_out = err;
}

static size_t act_reps(input *in) {
    size_t bytes = (size_t)(in->nb ? in->nb : 1) * 64;
    size_t reps = ACT_BYTES / (bytes ? bytes : 1);
    return reps ? reps : 1;
}

/* ns/block for one timed act of the pipeline side */
static double time_pipeline(input *in) {
    size_t reps = act_reps(in);
    uint64_t acc = 0;
    double t0, t1;

    t0 = now_ns();
    for (size_t i = 0; i < reps; i++) {
        uint64_t sc[3] = {0, 0, 0};
        uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
        uint64_t entw = 0, nk = 0, nxp = 0, xcarry[2] = {0, 0};
        uint64_t ndst = 0, nev = 0, err = 0;
        acc ^= leanllvm_json_pipeline(
            in->doc, in->n, sc, mk, &entw, in->ep, in->epcap, &nk, in->xp,
            in->xpcap, &nxp, xcarry, in->dst, in->dstcap, &ndst, in->ev,
            in->evcap, &nev, &err, in->arm);
        acc ^= nk ^ nxp ^ ndst ^ nev ^ err;
    }
    t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)(reps * (in->nb ? in->nb : 1));
}

/* ns/block for one timed act of the reference side */
static double time_reference(input *in) {
    size_t reps = act_reps(in);
    uint64_t acc = 0;
    double t0, t1;

    t0 = now_ns();
    for (size_t i = 0; i < reps; i++) acc += reference_walk(in);
    t1 = now_ns();
    sink ^= acc;
    return (t1 - t0) / (double)(reps * (in->nb ? in->nb : 1));
}

static void usage(void) {
    fprintf(stderr,
            "usage: paired-reference --corpus <manifest> [--rounds N] "
            "[--build <id>]\n");
}

int main(int argc, char **argv) {
    const char *corpus = NULL, *build = "unstated";
    int rounds = DEFAULT_ROUNDS;

    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--corpus") && i + 1 < argc) {
            corpus = argv[++i];
        } else if (!strcmp(argv[i], "--rounds") && i + 1 < argc) {
            rounds = atoi(argv[++i]);
        } else if (!strcmp(argv[i], "--build") && i + 1 < argc) {
            build = argv[++i];
        } else {
            usage();
            return 3;
        }
    }
    if (!corpus) {
        usage();
        return 3;
    }
    if (rounds < 1) {
        fprintf(stderr, "SETUP: --rounds must be at least 1\n");
        return 3;
    }

    /* The reference version is established before anything is measured. */
    printf("reference simdjson %s (header enum %d.%d.%d)\n", SIMDJSON_VERSION,
           (int)simdjson::SIMDJSON_VERSION_MAJOR,
           (int)simdjson::SIMDJSON_VERSION_MINOR,
           (int)simdjson::SIMDJSON_VERSION_REVISION);
    if (simdjson::SIMDJSON_VERSION_MAJOR != PINNED_MAJOR ||
        simdjson::SIMDJSON_VERSION_MINOR != PINNED_MINOR ||
        simdjson::SIMDJSON_VERSION_REVISION != PINNED_REVISION) {
        fprintf(stderr,
                "SETUP: the header is not the pinned reference %d.%d.%d\n",
                PINNED_MAJOR, PINNED_MINOR, PINNED_REVISION);
        return 3;
    }
    printf("reference implementation %s\n",
           simdjson::get_active_implementation()->name().c_str());

    std::vector<input> docs;
    if (int rc = parse_manifest(corpus, docs)) return rc;

    unsigned klass = core_class();
    printf("core-class 0x%02x (%s), arm: E-column on 0x20, P-column on 0x40\n",
           klass, klass == 0x40 ? "P" : klass == 0x20 ? "E" : "unknown");
    for (auto &in : docs) {
        in.arm = (klass == 0x40) ? in.arm_P : in.arm_E;
        if (int rc = stage_document(&in)) return rc;
    }

    /* Before the clock: both arms must accept every document.  A timing over a
       refused document measures the refusal path, not the pass. */
    for (auto &in : docs) {
        uint64_t verdict = 0, err = 0;
        pipeline_call(&in, &verdict, &err);
        if (verdict != 1) {
            fprintf(stderr,
                    "SETUP: document %s: the pipeline refused it (offset %llu, "
                    "arm %u); a timing over a refusal is not this row\n",
                    in.name, (unsigned long long)err, in.arm);
            return 3;
        }
        (void)reference_walk(&in);
        printf("gate %-10s pipeline accept, reference accept, %llu blocks, arm %u\n",
               in.name, (unsigned long long)in.nb, in.arm);
    }

    /* Warm-up: one untimed act each side per document, so the first timed act
       does not carry first-touch page faults or a cold instruction cache. */
    for (auto &in : docs) {
        sink ^= reference_walk(&in);
        sink ^= (uint64_t)time_pipeline(&in);
    }

    size_t nd = docs.size();
    std::vector<std::vector<double>> pr(nd), rf(nd), ratio(nd);
    for (auto &v : pr) v.reserve((size_t)rounds);
    for (auto &v : rf) v.reserve((size_t)rounds);
    for (auto &v : ratio) v.reserve((size_t)rounds);

    printf("\nrounds %d, one act per arm per order, two orders per round, "
           "averaged\n", rounds);
    printf("ratio = pipeline / reference ns per block; below 1.0 is faster\n\n");

    for (int r = 0; r < rounds; r++) {
        for (size_t i = 0; i < nd; i++) {
            input &in = docs[i];
            double a1, b1, a2, b2;
            if (((r + (int)i) & 1) == 0) {
                /* pipeline then reference, then reference then pipeline */
                a1 = time_pipeline(&in);
                b1 = time_reference(&in);
                b2 = time_reference(&in);
                a2 = time_pipeline(&in);
            } else {
                b1 = time_reference(&in);
                a1 = time_pipeline(&in);
                a2 = time_pipeline(&in);
                b2 = time_reference(&in);
            }
            double a = 0.5 * (a1 + a2), b = 0.5 * (b1 + b2);
            pr[i].push_back(a);
            rf[i].push_back(b);
            ratio[i].push_back(a / b);
        }
    }

    printf("%-10s %4s %10s %10s %8s %8s %8s %8s %8s\n", "document", "arm",
           "pipe", "reference", "ratio", "lo", "hi", "record", "delta");
    printf("%-10s %4s %10s %10s %8s %8s %8s %8s %8s\n", "", "", "ns/blk",
           "ns/blk", "", "", "", "", "");
    int worst = 0;
    for (size_t i = 0; i < nd; i++) {
        std::vector<double> p = pr[i], q = rf[i], o = ratio[i];
        double mp = median_of(p.data(), p.size());
        double mr = median_of(q.data(), q.size());
        double mo = median_of(o.data(), o.size());
        double lo = *std::min_element(o.begin(), o.end());
        double hi = *std::max_element(o.begin(), o.end());
        double record = (klass == 0x40) ? docs[i].record_P : docs[i].record_E;
        printf("%-10s %4u %10.3f %10.3f %8.3f %8.3f %8.3f %8.3f %+8.3f\n",
               docs[i].name, docs[i].arm, mp, mr, mo, lo, hi, record,
               record - mo);
        if (mo > 1.0) worst++;
    }

    printf("\nbuild %s\n", build);
    printf("%zu of %zu documents above 1.0 against the named reference "
           "(simdjson %s)\n", (size_t)worst, nd, SIMDJSON_VERSION);
    printf("the record's ratios are the scratch tree's; this table is a "
           "comparison against the named reference, not their reproduction\n");
    return 0;
}
