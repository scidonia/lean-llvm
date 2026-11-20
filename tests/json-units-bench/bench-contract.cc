/* bench-contract.cc -- the paired harness for the contracted single-pass
   stage 1 against the current pipeline and simdjson 5.0.5.

   One process, one document in hand, every arm entered from this file:

   * `contract_*` -- `bench-contract.c`'s single pass: the classifier, the
     entry word and both carries in registers, the entry positions and the
     escape positions written and nothing else.  `_core` runs it with the
     escape-list arm off, `_list` with it on, `_plain` with the UTF-8 unit's
     call after the loop and no list (the composite the unit bench records),
     and `_full` with both.
   * `staged_*` -- the current pipeline's stage 1, block for block:
     `leanllvm_json_s1_masks` into the caller's `mk` slot, the entry word
     composed from it and written to `entw`, one entry-emitter call per block,
     the escape-list call when the arm selects it, and the UTF-8 call after the
     loop.  It is `kernel/json/pipeline.c`'s loop without the stage-2 tail.
     Its four arms have the same list/UTF-8 combination as the contract's.
   * `split_*` -- the split shape the unit bench records as the best existing
     one: the masks and the entry word composed into an `ent` array over the
     whole document (the escape list appended from the same pass when the arm
     selects it), then one entry-emitter call over that array.  The array is an
     internal scratch of 8 bytes per block, the same role `mk` plays today at
     48; it is not one of the contract's outputs.  Its arms have the same
     combinations as the other two.
   * `splitc_*` -- the same two passes with the contracted mask pass: the six
     mask words stay in registers and only the entry word is written to the
     scratch.  It is the candidate shape, because it removes the intermediate
     slots without putting the emitter into the mask loop.
   * `stage1` -- simdjson 5.0.5's `dom_parser_implementation::stage1` in
     `stage1_mode::regular`: classification, the string/escape state, UTF-8
     validation and its structural-index array.

   ## The gates, before any row

   For every document and before the clock:
   - the prototype's classifier equals `leanllvm_json_s1_masks` on every
     block, in all six words and in all three carry words;
   - `leanllvm_json_pipeline` -- the tree's own staged pipeline, called at the
     document arm -- writes the entry stream, its cursor, the escape list and
     its count; every arm's first `k` and `nxp` words must equal them;
   - the two UTF-8 gate values agree with each other;
   - the entry emitter and the escape list are the same ones on both sides, so
     a mismatch is a defect in this prototype, not an arm difference.

   A gate failure exits 3; no row is printed after it.

   ## The rows

   Rounds are interleaved: every round runs every arm once in one order and
   once in the reverse, and takes the smaller of the arm's two readings, so a
   drift inside the round cancels and a scheduler preemption of one reading is
   not charged to the arm (`kernel/json/bench/paired-reference.cc`'s shape,
   with the minimum as the estimator because the host is shared).  The
   report prints, per document and arm, the median ns/byte, GB/s and calibrated
   cycles per byte, and the median and range of the per-round ratio to the
   arm's counterpart.  Every timed act's output checksum must equal the
   warm-up's; a disagreement exits 3 rather than printing a number.

   Flags and provenance are the shell's (`bench-contract.sh`); the harness is
   compiled at the units' measured line, and the simdjson library is the
   realised 5.0.5 store output, not recompiled.

     bench-contract --doc <name>=<path> [--doc ...] [--rounds <n>] [--samples]

   Exit status: 0 on success, 2 on a bad argument or unreadable document, 3
   when a gate fails. */

#define _GNU_SOURCE 1

#include "simdjson.h"

#include <algorithm>
#include <cerrno>
#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ctime>
#include <string>
#include <vector>

#if defined(__x86_64__)
#include <cpuid.h>
#include <x86intrin.h>
#endif
#if defined(__linux__)
#include <sched.h>
#endif

/* The units' ABIs, declared as the headers declare them, so a header change
   cannot make this file agree with itself.  `pipeline.h` and the unit headers
   are C; they are included with C linkage and no other use is made of them. */
extern "C" {
#include "../../kernel/json/escape.h"
#include "../../kernel/json/entry.h"
#include "../../kernel/json/pipeline.h"
#include "../../kernel/json/s1_block.h"
#include "../../kernel/json/utf8.h"

void leanllvm_bench_contract(const uint8_t *b, uint64_t n, const uint32_t *tab,
                             uint32_t *ep, uint64_t *nk,
                             uint32_t *xp, uint64_t *nxp, int b8, int list);
void leanllvm_bench_contract_masks(const uint8_t *p, uint64_t *carry,
                                   uint64_t *out6);
const uint32_t *leanllvm_bench_contract_pos8_table(void);
}

#define BLOCK 64
#define MAX_DOCS 64
#define DEFAULT_ROUNDS 15

static volatile uint64_t sink;

/* ------------------------------------------------------------------ time -- */
static uint64_t now_ns(void) {
  struct timespec t;
  if (clock_gettime(CLOCK_MONOTONIC_RAW, &t) != 0) {
    std::perror("clock_gettime");
    std::exit(2);
  }
  return (uint64_t)t.tv_sec * 1000000000ull + (uint64_t)t.tv_nsec;
}

static volatile uint64_t cal_sink;

static void serial_chain(uint64_t n) {
  uint64_t x = cal_sink;
#if defined(__x86_64__)
  __asm__ __volatile__("1:\n\t"
                       "addq $1, %0\n\t"
                       "decq %1\n\t"
                       "jne 1b\n\t"
                       : "+r"(x), "+r"(n)
                       :
                       : "cc");
#else
  while (n--) x += 1;
#endif
  cal_sink = x;
}

static double calibrate_ghz(void) {
  const uint64_t iterations = 1ull << 25;
  serial_chain(1ull << 20);
  uint64_t t0 = now_ns();
  serial_chain(iterations);
  uint64_t t1 = now_ns();
  uint64_t ns = t1 - t0;
  return ns ? (double)iterations / (double)ns : 0.0;
}

static void die(int code, const char *what) {
  std::fprintf(stderr, "bench-contract: %s\n", what);
  std::exit(code);
}

static uint64_t mix(uint64_t h, uint64_t v) {
  return (h ^ v) * 0x100000001B3ull;
}

/* --------------------------------------------------------------- document -- */
struct Doc {
  std::string name;
  std::vector<uint8_t> bytes;  /* the document as read, for simdjson */
  std::vector<uint8_t> win;    /* 3 zero before, the document, zero padding */
  const uint8_t *b = nullptr;
  uint64_t n = 0;
  uint64_t blocks = 0;
  int b8 = 0;

  /* Per-arm streams.  Every buffer carries the units' slack: one block's 64
     positions plus the emitters' eight-slot batch past the count. */
  std::vector<uint32_t> ep_c, ep_s, ep_split, ep_ref;
  std::vector<uint32_t> xp_c, xp_s, xp_split, xp_ref;
  std::vector<uint64_t> ent_v;
  std::vector<uint64_t> ent_f;

  /* The act's own results, read by its check before the next act runs. */
  uint64_t nk_act = 0, nxp_act = 0, u8 = 0, cl_act = 0;

  /* The reference cursors the gates compared against. */
  uint64_t nk_ref = 0, nxp_ref = 0;
};

static Doc docs[MAX_DOCS];
static int ndocs;
static const uint32_t *g_tab;      /* the prototype's POS8 table */
static uint32_t g_unit_tab[2048];  /* the entry unit's table, for its kernels */

static void add_doc(const char *spec) {
  const char *eq = std::strchr(spec, '=');
  if (eq == nullptr || eq == spec) die(2, "expected --doc <name>=<path>");
  if (ndocs >= MAX_DOCS) die(2, "too many documents");
  Doc *d = &docs[ndocs++];
  d->name.assign(spec, (size_t)(eq - spec));
  const char *path = eq + 1;
  FILE *f = std::fopen(path, "rb");
  if (f == nullptr) {
    std::fprintf(stderr, "bench-contract: %s: %s\n", path, std::strerror(errno));
    std::exit(2);
  }
  std::fseek(f, 0, SEEK_END);
  long sz = std::ftell(f);
  std::fseek(f, 0, SEEK_SET);
  if (sz <= 0) die(2, "empty or unreadable document");
  d->bytes.resize((size_t)sz);
  if (std::fread(d->bytes.data(), 1, (size_t)sz, f) != (size_t)sz)
    die(2, "short read");
  std::fclose(f);
}

/* The document's staging: three zero bytes before it (the UTF-8 unit's
   start-of-document rule), zero padding to the block boundary (both windows)
   and thirty-two more readable zero bytes (the escape decoder's read past). */
static void stage_doc(Doc *d) {
  d->n = d->bytes.size();
  d->blocks = (d->n + BLOCK - 1) / BLOCK;
  size_t padblocks = (size_t)d->blocks * BLOCK;
  d->win.assign(3 + padblocks + BLOCK, 0);
  std::memcpy(d->win.data() + 3, d->bytes.data(), d->bytes.size());
  d->b = d->win.data() + 3;

  size_t words = (size_t)(d->n + 64 * d->blocks + 64);
  d->ep_c.assign(words, 0);
  d->ep_s.assign(words, 0);
  d->ep_split.assign(words, 0);
  d->ep_ref.assign(words, 0);
  d->xp_c.assign(words, 0);
  d->xp_s.assign(words, 0);
  d->xp_split.assign(words, 0);
  d->xp_ref.assign(words, 0);
  d->ent_v.assign((size_t)d->blocks + 2, 0);
  d->ent_f.assign((size_t)d->blocks + 2, 0);

  /* The measured arm selection `docs/json-pipeline-performance.md` records:
     POS8 on the route and dense documents, B8 on the strings and UTF-8
     documents. */
  d->b8 = (d->name.find("strings") != std::string::npos ||
           d->name.find("utf8") != std::string::npos);
}

/* ------------------------------------------------------------------- arms -- */
enum Arm {
  A_CONTRACT_CORE,
  A_STAGED_CORE,
  A_SPLIT_CORE,
  A_CONTRACT_LIST,
  A_STAGED_LIST,
  A_SPLIT_LIST,
  A_CONTRACT_PLAIN,
  A_STAGED_PLAIN,
  A_SPLIT_PLAIN,
  A_CONTRACT_FULL,
  A_STAGED_FULL,
  A_SPLIT_FULL,
  A_SPLITC_CORE,
  A_SPLITC_LIST,
  A_SPLITC_PLAIN,
  A_SPLITC_FULL,
  A_MASK_CORE,
  A_MASK_LIST,
  A_EMIT_B8,
  A_U8,
  A_CLASSIFY,
  A_CLASSIFY_FAST,
  A_MASK_FAST,
  A_EMIT4,
  A_SPLITFAST_CORE,
  A_SPLITFAST_PLAIN,
  A_CLASSIFY_FAST2,
  A_MASK_FAST2,
  A_SPLITFAST2_CORE,
  A_SPLITFAST2_PLAIN,
  A_SPLITFAST2U_PLAIN,
  A_EMIT3,
  A_SPLITFAST3_CORE,
  A_SPLITFAST_U8,
  A_SPLITFAST3_U8,
  A_SPLITLAG3,
  A_SPLITLAG3_U8,
  A_SPLITPROBE3,
  A_SPLITPROBE_B8,
  A_SPLITFAST_B8_U8,
  A_SPLITAUTO,
  A_STAGE1,
  A_COUNT
};

static const char *arm_name(int a) {
  switch (a) {
    case A_CONTRACT_CORE: return "contract_core";
    case A_STAGED_CORE: return "staged_core";
    case A_SPLIT_CORE: return "split_core";
    case A_CONTRACT_LIST: return "contract_list";
    case A_STAGED_LIST: return "staged_list";
    case A_SPLIT_LIST: return "split_list";
    case A_CONTRACT_PLAIN: return "contract_plain";
    case A_STAGED_PLAIN: return "staged_plain";
    case A_SPLIT_PLAIN: return "split_plain";
    case A_CONTRACT_FULL: return "contract_full";
    case A_STAGED_FULL: return "staged_full";
    case A_SPLIT_FULL: return "split_full";
    case A_SPLITC_CORE: return "splitc_core";
    case A_SPLITC_LIST: return "splitc_list";
    case A_SPLITC_PLAIN: return "splitc_plain";
    case A_SPLITC_FULL: return "splitc_full";
    case A_MASK_CORE: return "mask_core";
    case A_MASK_LIST: return "mask_list";
    case A_EMIT_B8: return "emit_b8";
    case A_U8: return "u8";
    case A_CLASSIFY: return "classify";
    case A_CLASSIFY_FAST: return "classify_fast";
    case A_MASK_FAST: return "mask_fast";
    case A_EMIT4: return "emit4";
    case A_SPLITFAST_CORE: return "splitfast_core";
    case A_SPLITFAST_PLAIN: return "splitfast_plain";
    case A_CLASSIFY_FAST2: return "classify_fast2";
    case A_MASK_FAST2: return "mask_fast2";
    case A_SPLITFAST2_CORE: return "splitfast2_core";
    case A_SPLITFAST2_PLAIN: return "splitfast2_plain";
    case A_SPLITFAST2U_PLAIN: return "splitfast2u_plain";
    case A_EMIT3: return "emit3";
    case A_SPLITFAST3_CORE: return "splitfast3_core";
    case A_SPLITFAST_U8: return "splitfast_u8";
    case A_SPLITFAST3_U8: return "splitfast3_u8";
    case A_SPLITLAG3: return "splitlag3";
    case A_SPLITLAG3_U8: return "splitlag3_u8";
    case A_SPLITPROBE3: return "splitprobe3";
    case A_SPLITPROBE_B8: return "splitprobe_b8";
    case A_SPLITFAST_B8_U8: return "splitfast_b8_u8";
    case A_SPLITAUTO: return "splitauto";
    default: return "stage1";
  }
}

/* `pipeline.c`'s loop without the stage-2 tail: the three stage-1 units at
   their own entry points and the entry word composed between them. */
static void staged_pass(Doc *d, int list) {
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t k = 0, xn = 0;
  uint64_t entw[2];
  uint64_t xc[2] = {0, 0};
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  for (uint64_t i = 0; i < nblk; i++) {
    leanllvm_json_s1_masks(d->b + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    entw[0] = ent;
    k = d->b8 ? leanllvm_json_entry_b8(entw, i, 1, d->ep_s.data(), k)
              : leanllvm_json_entry_pos8(entw, i, 1, d->ep_s.data(), k);
    if (list)
      leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i,
                                d->xp_s.data(), &xn, xc);
  }
  d->nk_act = k;
  d->nxp_act = xn;
}

/* The split shape: masks and entry word into the array (and the escape list
   from the same pass when it is selected), one emitter call. */
static void split_pass(Doc *d, int list) {
  s1_carry sc = {0, 0, 0};
  s1_masks m;
  uint64_t prevS = 0;
  uint64_t xn = 0;
  uint64_t xc[2] = {0, 0};
  uint64_t nblk = (d->n + BLOCK - 1) / BLOCK;
  for (uint64_t i = 0; i < nblk; i++) {
    leanllvm_json_s1_masks(d->b + (i << 6), &sc, &m);
    uint64_t S = ~(m.quote | m.delim | m.in_string | m.ws);
    uint64_t ent = m.quote | (m.delim & ~m.in_string);
    ent |= S & ~((S << 1) | prevS);
    prevS = S >> 63;
    uint64_t lim = d->n - (i << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    d->ent_v[i] = ent;
    if (list)
      leanllvm_json_escape_list(m.backslash, m.ctl, m.in_string, i,
                                d->xp_split.data(), &xn, xc);
  }
  d->nk_act = d->b8
    ? leanllvm_json_entry_b8(d->ent_v.data(), 0, nblk, d->ep_split.data(), 0)
    : leanllvm_json_entry_pos8(d->ent_v.data(), 0, nblk, d->ep_split.data(), 0);
  d->nxp_act = xn;
}

extern "C" void leanllvm_bench_contract_split_core(
    const uint8_t *b, uint64_t n, const uint32_t *tab, uint32_t *ep,
    uint64_t *nk, uint32_t *xp, uint64_t *nxp, uint64_t *ent, int b8);
extern "C" void leanllvm_bench_contract_split_list(
    const uint8_t *b, uint64_t n, const uint32_t *tab, uint32_t *ep,
    uint64_t *nk, uint32_t *xp, uint64_t *nxp, uint64_t *ent, int b8);
extern "C" void leanllvm_bench_contract_maskpass(
    const uint8_t *b, uint64_t n, uint64_t *ent, uint32_t *xp, uint64_t *nxp,
    int list);
extern "C" void leanllvm_bench_contract_classify(
    const uint8_t *b, uint64_t n, uint64_t *sink);
extern "C" void leanllvm_bench_contract_classify_fast(
    const uint8_t *b, uint64_t n, uint64_t *sink);
extern "C" void leanllvm_bench_contract_maskfast(
    const uint8_t *b, uint64_t n, uint64_t *ent);
extern "C" void leanllvm_bench_contract_emit4(
    const uint64_t *ent, uint64_t nblk, uint32_t *ep, uint64_t *nk);
extern "C" void leanllvm_bench_contract_splitfast(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" void leanllvm_bench_contract_classify_fast2(
    const uint8_t *b, uint64_t n, uint64_t *sink);
extern "C" void leanllvm_bench_contract_maskfast2(
    const uint8_t *b, uint64_t n, uint64_t *ent);
extern "C" void leanllvm_bench_contract_splitfast2(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_maskfast2_u8(
    const uint8_t *b, uint64_t n, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitfast2_u8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" void leanllvm_bench_contract_emit3(
    const uint64_t *ent, uint64_t nblk, uint32_t *ep, uint64_t *nk);
extern "C" void leanllvm_bench_contract_splitfast3(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitfast_u8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitfast3_u8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" void leanllvm_bench_contract_splitlag3(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk);
extern "C" uint64_t leanllvm_bench_contract_splitlag3_u8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk);
extern "C" int leanllvm_bench_contract_maskfast_probe(
    const uint8_t *b, uint64_t n, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitprobe3(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitprobe_b8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitfast_b8_u8(
    const uint8_t *b, uint64_t n, uint32_t *ep, uint64_t *nk, uint64_t *ent);
extern "C" uint64_t leanllvm_bench_contract_splitauto(
    const uint8_t *b, uint64_t n, int b8, uint32_t *ep, uint64_t *nk,
    uint64_t *ent);

static void splitc_pass(Doc *d, int list) {
  d->nk_act = 0;
  d->nxp_act = 0;
  if (list)
    leanllvm_bench_contract_split_list(d->b, d->n, g_tab, d->ep_c.data(),
                                       &d->nk_act, d->xp_c.data(), &d->nxp_act,
                                       d->ent_v.data(), d->b8);
  else
    leanllvm_bench_contract_split_core(d->b, d->n, g_tab, d->ep_c.data(),
                                       &d->nk_act, d->xp_c.data(), &d->nxp_act,
                                       d->ent_v.data(), d->b8);
}

static void contract_pass(Doc *d, int list) {
  d->nk_act = 0;
  d->nxp_act = 0;
  leanllvm_bench_contract(d->b, d->n, g_tab, d->ep_c.data(), &d->nk_act,
                          d->xp_c.data(), &d->nxp_act, d->b8, list);
}

/* The split's first pass alone; it writes the same `ent` array the split
   shape's second pass reads. */
static void mask_pass(Doc *d, int list) {
  uint64_t xn = 0;
  leanllvm_bench_contract_maskpass(d->b, d->n, d->ent_v.data(),
                                   d->xp_c.data(), &xn, list);
  d->nxp_act = xn;
}

/* The split's second pass alone over the array a previous act wrote.  Its
   cursor is the stream's count, as the unit returns it. */
static void emit_b8_pass(Doc *d) {
  d->nk_act = leanllvm_json_entry_b8(d->ent_v.data(), 0, d->blocks,
                                     d->ep_c.data(), 0);
  d->nxp_act = 0;
}

static void classify_pass(Doc *d, int fast) {
  d->cl_act = 0;
  if (fast)
    leanllvm_bench_contract_classify_fast(d->b, d->n, &d->cl_act);
  else
    leanllvm_bench_contract_classify(d->b, d->n, &d->cl_act);
}

static void maskfast_pass(Doc *d) {
  leanllvm_bench_contract_maskfast(d->b, d->n, d->ent_f.data());
}

static void emit4_pass(Doc *d) {
  leanllvm_bench_contract_emit4(d->ent_v.data(), d->blocks, d->ep_c.data(),
                                &d->nk_act);
  d->nxp_act = 0;
}

static void splitfast_pass(Doc *d) {
  leanllvm_bench_contract_splitfast(d->b, d->n, d->ep_c.data(), &d->nk_act,
                                    d->ent_f.data());
  d->nxp_act = 0;
}

static void classify2_pass(Doc *d) {
  d->cl_act = 0;
  leanllvm_bench_contract_classify_fast2(d->b, d->n, &d->cl_act);
}

static void maskfast2_pass(Doc *d) {
  leanllvm_bench_contract_maskfast2(d->b, d->n, d->ent_f.data());
}

static void splitfast2_pass(Doc *d) {
  leanllvm_bench_contract_splitfast2(d->b, d->n, d->ep_c.data(), &d->nk_act,
                                     d->ent_f.data());
  d->nxp_act = 0;
}

static uint64_t splitfast2u_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitfast2_u8(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static void emit3_pass(Doc *d) {
  leanllvm_bench_contract_emit3(d->ent_v.data(), d->blocks, d->ep_c.data(),
                                &d->nk_act);
  d->nxp_act = 0;
}

static void splitfast3_pass(Doc *d) {
  leanllvm_bench_contract_splitfast3(d->b, d->n, d->ep_c.data(), &d->nk_act,
                                     d->ent_f.data());
  d->nxp_act = 0;
}

static uint64_t splitfast_u8_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitfast_u8(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static uint64_t splitfast3_u8_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitfast3_u8(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static void splitlag3_pass(Doc *d) {
  d->nk_act = 0;
  leanllvm_bench_contract_splitlag3(d->b, d->n, d->ep_c.data(), &d->nk_act);
  d->nxp_act = 0;
}

static uint64_t splitlag3u_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitlag3_u8(d->b, d->n, d->ep_c.data(),
                                               &d->nk_act);
  d->nxp_act = 0;
  return d->u8;
}

static uint64_t splitprobe3_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitprobe3(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static uint64_t splitprobe_b8_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitprobe_b8(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static uint64_t splitfast_b8_u8_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitfast_b8_u8(
      d->b, d->n, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

static uint64_t splitauto_pass(Doc *d) {
  d->nk_act = 0;
  d->u8 = leanllvm_bench_contract_splitauto(
      d->b, d->n, d->b8, d->ep_c.data(), &d->nk_act, d->ent_f.data());
  d->nxp_act = 0;
  return d->u8;
}

/* --------------------------------------------------------------- checks -- */
static uint64_t stream_check(const uint32_t *p, uint64_t n, uint64_t extra) {
  uint64_t h = mix(0x84222325CBF29CE4ull, n);
  for (uint64_t i = 0; i < n; i++) h = mix(h, p[i]);
  return mix(h, extra);
}

static uint64_t ent_check(const uint64_t *p, uint64_t n) {
  uint64_t h = mix(0x84222325CBF29CE4ull, n);
  for (uint64_t i = 0; i < n; i++) h = mix(h, p[i]);
  return h;
}

/* simdjson's stage-1 act and its check, `simdjson-baseline.cc`'s shape. */
struct S1Result {
  simdjson::error_code err;
  uint32_t n;
};

static S1Result stage1_act(simdjson::dom::parser &parser,
                           const simdjson::padded_string &ps) {
  S1Result r;
  r.err = parser.implementation->stage1(
      reinterpret_cast<const uint8_t *>(ps.data()), ps.size(),
      simdjson::stage1_mode::regular);
  r.n = parser.implementation->n_structural_indexes;
  return r;
}

static uint64_t stage1_check(const simdjson::dom::parser &parser,
                             const S1Result &r) {
  uint64_t h = mix(0x84222325CBF29CE4ull, (uint64_t)r.err);
  h = mix(h, r.n);
  const uint32_t *idx = parser.implementation->structural_indexes.get();
  for (uint32_t i = 0; i < r.n; i++) h = mix(h, idx[i]);
  return h;
}

/* ---------------------------------------------------------- pipeline ref -- */
/* The tree's own pipeline, as the gate's reference.  It writes its own ep/xp
   buffers and also runs the UTF-8 stage and stage 2; the stage-2 capacities
   are generous here, because gating is not the row. */
static void pipeline_reference(Doc *d) {
  std::vector<uint64_t> sc(3, 0), mk(6, 0), xcarry(2, 0);
  uint64_t entw = 0;
  uint64_t nk = 0, nxp = 0, ndst = 0, nev = 0;
  uint64_t err = 0;
  uint64_t epcap = (uint64_t)d->ep_ref.size();
  uint64_t xpcap = (uint64_t)d->xp_ref.size();
  uint64_t dstcap = 4 * d->n + (1 << 16);
  uint64_t evcap = 16 * d->n + (1 << 16);
  std::vector<uint8_t> dst((size_t)dstcap, 0), ev((size_t)evcap, 0);
  uint64_t arm = (uint64_t)(d->b8 ? 1 : 0) | 2;
  (void)leanllvm_json_pipeline(
      d->b, d->n, sc.data(), mk.data(), &entw, d->ep_ref.data(), epcap, &nk,
      d->xp_ref.data(), xpcap, &nxp, xcarry.data(), dst.data(), dstcap, &ndst,
      ev.data(), evcap, &nev, &err, arm);
  d->nk_act = nk;
  d->nxp_act = nxp;
}

/* ------------------------------------------------------------------ gates -- */
static void gate_masks(Doc *d) {
  s1_carry a = {0, 0, 0};
  uint64_t carry[3] = {0, 0, 0};
  for (uint64_t i = 0; i < d->blocks; i++) {
    s1_masks m;
    uint64_t o6[6];
    leanllvm_json_s1_masks(d->b + (i << 6), &a, &m);
    leanllvm_bench_contract_masks(d->b + (i << 6), carry, o6);
    if (o6[0] != m.quote || o6[1] != m.delim || o6[2] != m.in_string ||
        o6[3] != m.ws || o6[4] != m.backslash || o6[5] != m.ctl) {
      std::fprintf(stderr,
                   "bench-contract: %s: block %" PRIu64
                   " masks differ: [%" PRIu64 ",%" PRIu64 ",%" PRIu64
                   ",%" PRIu64 ",%" PRIu64 ",%" PRIu64
                   "] vs [%" PRIu64 ",%" PRIu64 ",%" PRIu64 ",%" PRIu64
                   ",%" PRIu64 ",%" PRIu64 "]\n",
                   d->name.c_str(), i, m.quote, m.delim, m.in_string, m.ws,
                   m.backslash, m.ctl, o6[0], o6[1], o6[2], o6[3], o6[4], o6[5]);
      std::exit(3);
    }
    if (carry[0] != a.esc_open || carry[1] != a.esc_ppar ||
        carry[2] != a.im_carry) {
      std::fprintf(stderr,
                   "bench-contract: %s: block %" PRIu64 " carry differs\n",
                   d->name.c_str(), i);
      std::exit(3);
    }
  }
}

static void gate_streams(Doc *d) {
  /* The reference: the tree's pipeline. */
  pipeline_reference(d);
  d->nk_ref = d->nk_act;
  d->nxp_ref = d->nxp_act;
  const uint64_t nk_ref = d->nk_ref, nxp_ref = d->nxp_ref;

  /* The prototype, with the escape list. */
  contract_pass(d, 1);
  if (d->nk_act != nk_ref) die(3, "contract entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i]) die(3, "contract entry position differs");
  if (d->nxp_act != nxp_ref) die(3, "contract escape count differs from pipeline");
  for (uint64_t i = 0; i < nxp_ref; i++)
    if (d->xp_c[i] != d->xp_ref[i]) die(3, "contract escape position differs");

  /* The current staged loop. */
  staged_pass(d, 1);
  if (d->nk_act != nk_ref) die(3, "staged entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_s[i] != d->ep_ref[i]) die(3, "staged entry position differs");
  if (d->nxp_act != nxp_ref) die(3, "staged escape count differs from pipeline");
  for (uint64_t i = 0; i < nxp_ref; i++)
    if (d->xp_s[i] != d->xp_ref[i]) die(3, "staged escape position differs");

  /* Both with the list arm off: the entry stream is the same, the list is
     empty. */
  contract_pass(d, 0);
  if (d->nk_act != nk_ref || d->nxp_act != 0)
    die(3, "contract (no list) cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i]) die(3, "contract (no list) differs");
  staged_pass(d, 0);
  if (d->nk_act != nk_ref || d->nxp_act != 0)
    die(3, "staged (no list) cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_s[i] != d->ep_ref[i]) die(3, "staged (no list) differs");

  /* The split shape's streams, with and without the list. */
  split_pass(d, 1);
  if (d->nk_act != nk_ref) die(3, "split entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_split[i] != d->ep_ref[i]) die(3, "split entry position differs");
  if (d->nxp_act != nxp_ref) die(3, "split escape count differs from pipeline");
  for (uint64_t i = 0; i < nxp_ref; i++)
    if (d->xp_split[i] != d->xp_ref[i]) die(3, "split escape position differs");
  split_pass(d, 0);
  if (d->nk_act != nk_ref || d->nxp_act != 0)
    die(3, "split (no list) cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_split[i] != d->ep_ref[i]) die(3, "split (no list) differs");

  /* The contracted split shape, with and without the list. */
  splitc_pass(d, 1);
  if (d->nk_act != nk_ref) die(3, "splitc entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i]) die(3, "splitc entry position differs");
  if (d->nxp_act != nxp_ref) die(3, "splitc escape count differs from pipeline");
  for (uint64_t i = 0; i < nxp_ref; i++)
    if (d->xp_c[i] != d->xp_ref[i]) die(3, "splitc escape position differs");
  splitc_pass(d, 0);
  if (d->nk_act != nk_ref || d->nxp_act != 0)
    die(3, "splitc (no list) cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i]) die(3, "splitc (no list) differs");

  /* The candidate's mask pass, block for block against the splitc mask pass
     (whose stream just gated against the pipeline), and its stream. */
  splitc_pass(d, 0);
  maskfast_pass(d);
  for (uint64_t i = 0; i < d->blocks; i++)
    if (d->ent_f[i] != d->ent_v[i])
      die(3, "candidate entry word differs from splitc");
  splitfast_pass(d);
  if (d->nk_act != nk_ref) die(3, "candidate entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "candidate entry position differs");

  splitc_pass(d, 0);
  maskfast2_pass(d);
  for (uint64_t i = 0; i < d->blocks; i++)
    if (d->ent_f[i] != d->ent_v[i])
      die(3, "candidate2 entry word differs from splitc");
  splitfast2_pass(d);
  if (d->nk_act != nk_ref) die(3, "candidate2 entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "candidate2 entry position differs");
  if (splitfast2u_pass(d) != leanllvm_json_utf8(d->b, d->n, 0))
    die(3, "candidate2 fused UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "candidate2u entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "candidate2u entry position differs");

  mask_pass(d, 0);
  splitfast3_pass(d);
  if (d->nk_act != nk_ref) die(3, "candidate3 entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "candidate3 entry position differs");
  uint64_t u8_ref = leanllvm_json_utf8(d->b, d->n, 0);
  if (splitfast_u8_pass(d) != u8_ref)
    die(3, "fused UTF-8 word differs from the unit (emit4)");
  if (d->nk_act != nk_ref) die(3, "fused entry cursor differs (emit4)");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "fused entry position differs (emit4)");
  if (splitfast3_u8_pass(d) != u8_ref)
    die(3, "fused UTF-8 word differs from the unit (emit3)");
  if (d->nk_act != nk_ref) die(3, "fused entry cursor differs (emit3)");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "fused entry position differs (emit3)");
  splitlag3_pass(d);
  if (d->nk_act != nk_ref) die(3, "lagged entry cursor differs from pipeline");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "lagged entry position differs");
  if (splitlag3u_pass(d) != u8_ref)
    die(3, "lagged fused UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "lagged fused entry cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "lagged fused entry position differs");
  if (splitprobe3_pass(d) != u8_ref)
    die(3, "probe+emit3 UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "probe+emit3 entry cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "probe+emit3 entry position differs");
  if (splitprobe_b8_pass(d) != u8_ref)
    die(3, "probe+b8 UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "probe+b8 entry cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "probe+b8 entry position differs");
  if (splitfast_b8_u8_pass(d) != u8_ref)
    die(3, "fused+b8 UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "fused+b8 entry cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "fused+b8 entry position differs");
  if (splitauto_pass(d) != u8_ref)
    die(3, "selected UTF-8 word differs from the unit");
  if (d->nk_act != nk_ref) die(3, "selected entry cursor differs");
  for (uint64_t i = 0; i < nk_ref; i++)
    if (d->ep_c[i] != d->ep_ref[i])
      die(3, "selected entry position differs");

  /* The UTF-8 stage's two gate values. */
  if (leanllvm_json_utf8(d->b, d->n, 0) != leanllvm_json_utf8(d->b, d->n, 1))
    die(3, "UTF-8 gate values differ");
}

/* --------------------------------------------------------------- the row -- */
static int cmp_double(const void *a, const void *b) {
  double x = *(const double *)a, y = *(const double *)b;
  return x < y ? -1 : x > y ? 1 : 0;
}

static double median_of(std::vector<double> &v) {
  std::sort(v.begin(), v.end());
  size_t n = v.size();
  if (n == 0) return 0.0;
  return (n & 1) ? v[n / 2] : 0.5 * (v[n / 2 - 1] + v[n / 2]);
}

int main(int argc, char **argv) {
  int rounds = DEFAULT_ROUNDS;
  int samples = 0;
  for (int i = 1; i < argc; i++) {
    if (!std::strcmp(argv[i], "--doc") && i + 1 < argc) {
      add_doc(argv[++i]);
    } else if (!std::strcmp(argv[i], "--rounds") && i + 1 < argc) {
      rounds = std::atoi(argv[++i]);
      if (rounds < 3) die(2, "rounds must be at least 3");
    } else if (!std::strcmp(argv[i], "--samples")) {
      samples = 1;
    } else {
      std::fprintf(stderr, "bench-contract: bad argument %s\n", argv[i]);
      return 2;
    }
  }
  if (ndocs == 0) die(2, "no documents");

  /* Both tables, once, before any clock. */
  leanllvm_json_entry_table(g_unit_tab);
  g_tab = leanllvm_bench_contract_pos8_table();

  int cpu = -1;
#if defined(__linux__)
  cpu = sched_getcpu();
#endif
  std::string impl(simdjson::get_active_implementation()->name());
  std::printf("instrument bench=contract rounds=%d cpu=%d simdjson=%s"
              " implementation=%s\n",
              rounds, cpu, SIMDJSON_VERSION, impl.c_str());

  for (int di = 0; di < ndocs; di++) {
    Doc *d = &docs[di];
    stage_doc(d);
    gate_masks(d);
    gate_streams(d);

    /* Warm-up per arm, and the checksum every timed act must reproduce. */
    S1Result s1_ref{simdjson::SUCCESS, 0};
    simdjson::padded_string ps(reinterpret_cast<const char *>(d->bytes.data()),
                              d->bytes.size());
    simdjson::dom::parser dp;
    if (auto e = dp.allocate(ps.size(), dp.max_depth())) {
      std::fprintf(stderr, "bench-contract: %s: dom allocate: %s\n",
                   d->name.c_str(), simdjson::error_message(e));
      std::exit(3);
    }
    s1_ref = stage1_act(dp, ps);
    uint64_t s1_ref_check = stage1_check(dp, s1_ref);
    sink ^= s1_ref_check;

    uint64_t ref[A_COUNT] = {0};
    contract_pass(d, 0);
    ref[A_CONTRACT_CORE] = stream_check(d->ep_c.data(), d->nk_act, 0);
    staged_pass(d, 0);
    ref[A_STAGED_CORE] = stream_check(d->ep_s.data(), d->nk_act, 0);
    split_pass(d, 0);
    ref[A_SPLIT_CORE] = stream_check(d->ep_split.data(), d->nk_act, 0);
    contract_pass(d, 1);
    ref[A_CONTRACT_LIST] = stream_check(d->ep_c.data(), d->nk_act, d->nxp_act);
    staged_pass(d, 1);
    ref[A_STAGED_LIST] = stream_check(d->ep_s.data(), d->nk_act, d->nxp_act);
    split_pass(d, 1);
    ref[A_SPLIT_LIST] = stream_check(d->ep_split.data(), d->nk_act, d->nxp_act);
    contract_pass(d, 0);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_CONTRACT_PLAIN] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    staged_pass(d, 0);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_STAGED_PLAIN] = stream_check(d->ep_s.data(), d->nk_act, d->u8);
    split_pass(d, 0);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLIT_PLAIN] = stream_check(d->ep_split.data(), d->nk_act, d->u8);
    contract_pass(d, 1);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_CONTRACT_FULL] = stream_check(d->ep_c.data(), d->nk_act,
                                        mix(d->nxp_act, d->u8));
    staged_pass(d, 1);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_STAGED_FULL] = stream_check(d->ep_s.data(), d->nk_act,
                                      mix(d->nxp_act, d->u8));
    split_pass(d, 1);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLIT_FULL] = stream_check(d->ep_split.data(), d->nk_act,
                                     mix(d->nxp_act, d->u8));
    splitc_pass(d, 0);
    ref[A_SPLITC_CORE] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitc_pass(d, 1);
    ref[A_SPLITC_LIST] = stream_check(d->ep_c.data(), d->nk_act, d->nxp_act);
    splitc_pass(d, 0);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLITC_PLAIN] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitc_pass(d, 1);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLITC_FULL] = stream_check(d->ep_c.data(), d->nk_act,
                                      mix(d->nxp_act, d->u8));
    mask_pass(d, 0);
    ref[A_MASK_CORE] = ent_check(d->ent_v.data(), d->blocks);
    mask_pass(d, 1);
    ref[A_MASK_LIST] = mix(ent_check(d->ent_v.data(), d->blocks),
                           stream_check(d->xp_c.data(), d->nxp_act,
                                        d->nxp_act));
    mask_pass(d, 0);
    emit_b8_pass(d);
    ref[A_EMIT_B8] = stream_check(d->ep_c.data(), d->nk_act, 0);
    ref[A_U8] = leanllvm_json_utf8(d->b, d->n, 0);
    classify_pass(d, 0);
    ref[A_CLASSIFY] = d->cl_act;
    classify_pass(d, 1);
    ref[A_CLASSIFY_FAST] = d->cl_act;
    mask_pass(d, 0);
    maskfast_pass(d);
    ref[A_MASK_FAST] = ent_check(d->ent_f.data(), d->blocks);
    emit4_pass(d);
    ref[A_EMIT4] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitfast_pass(d);
    ref[A_SPLITFAST_CORE] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitfast_pass(d);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLITFAST_PLAIN] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    classify2_pass(d);
    ref[A_CLASSIFY_FAST2] = d->cl_act;
    mask_pass(d, 0);
    maskfast2_pass(d);
    ref[A_MASK_FAST2] = ent_check(d->ent_f.data(), d->blocks);
    splitfast2_pass(d);
    ref[A_SPLITFAST2_CORE] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitfast2_pass(d);
    d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
    ref[A_SPLITFAST2_PLAIN] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitfast2u_pass(d);
    ref[A_SPLITFAST2U_PLAIN] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    mask_pass(d, 0);
    emit3_pass(d);
    ref[A_EMIT3] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitfast3_pass(d);
    ref[A_SPLITFAST3_CORE] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitfast_u8_pass(d);
    ref[A_SPLITFAST_U8] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitfast3_u8_pass(d);
    ref[A_SPLITFAST3_U8] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitlag3_pass(d);
    ref[A_SPLITLAG3] = stream_check(d->ep_c.data(), d->nk_act, 0);
    splitlag3u_pass(d);
    ref[A_SPLITLAG3_U8] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitprobe3_pass(d);
    ref[A_SPLITPROBE3] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitprobe_b8_pass(d);
    ref[A_SPLITPROBE_B8] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitfast_b8_u8_pass(d);
    ref[A_SPLITFAST_B8_U8] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    splitauto_pass(d);
    ref[A_SPLITAUTO] = stream_check(d->ep_c.data(), d->nk_act, d->u8);
    ref[A_STAGE1] = s1_ref_check;

    /* The acts.  Each updates `nk_act`/`nxp_act`/`u8`; `check_arm` reads them
       immediately after the clock. */
    S1Result s1_timed{simdjson::SUCCESS, 0};
    auto act = [&](int a) {
      switch (a) {
        case A_CONTRACT_CORE: contract_pass(d, 0); break;
        case A_STAGED_CORE: staged_pass(d, 0); break;
        case A_SPLIT_CORE: split_pass(d, 0); break;
        case A_CONTRACT_LIST: contract_pass(d, 1); break;
        case A_STAGED_LIST: staged_pass(d, 1); break;
        case A_SPLIT_LIST: split_pass(d, 1); break;
        case A_CONTRACT_PLAIN:
          contract_pass(d, 0);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_STAGED_PLAIN:
          staged_pass(d, 0);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_SPLIT_PLAIN:
          split_pass(d, 0);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_CONTRACT_FULL:
          contract_pass(d, 1);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_STAGED_FULL:
          staged_pass(d, 1);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_SPLIT_FULL:
          split_pass(d, 1);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_SPLITC_CORE: splitc_pass(d, 0); break;
        case A_SPLITC_LIST: splitc_pass(d, 1); break;
        case A_SPLITC_PLAIN:
          splitc_pass(d, 0);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_SPLITC_FULL:
          splitc_pass(d, 1);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_MASK_CORE: mask_pass(d, 0); break;
        case A_MASK_LIST: mask_pass(d, 1); break;
        case A_EMIT_B8: emit_b8_pass(d); break;
        case A_U8: d->u8 = leanllvm_json_utf8(d->b, d->n, 0); break;
        case A_CLASSIFY: classify_pass(d, 0); break;
        case A_CLASSIFY_FAST: classify_pass(d, 1); break;
        case A_MASK_FAST: maskfast_pass(d); break;
        case A_EMIT4: emit4_pass(d); break;
        case A_SPLITFAST_CORE: splitfast_pass(d); break;
        case A_SPLITFAST_PLAIN:
          splitfast_pass(d);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_CLASSIFY_FAST2: classify2_pass(d); break;
        case A_MASK_FAST2: maskfast2_pass(d); break;
        case A_SPLITFAST2_CORE: splitfast2_pass(d); break;
        case A_SPLITFAST2_PLAIN:
          splitfast2_pass(d);
          d->u8 = leanllvm_json_utf8(d->b, d->n, 0);
          break;
        case A_SPLITFAST2U_PLAIN: splitfast2u_pass(d); break;
        case A_EMIT3: emit3_pass(d); break;
        case A_SPLITFAST3_CORE: splitfast3_pass(d); break;
        case A_SPLITFAST_U8: splitfast_u8_pass(d); break;
        case A_SPLITFAST3_U8: splitfast3_u8_pass(d); break;
        case A_SPLITLAG3: splitlag3_pass(d); break;
        case A_SPLITLAG3_U8: splitlag3u_pass(d); break;
        case A_SPLITPROBE3: splitprobe3_pass(d); break;
        case A_SPLITPROBE_B8: splitprobe_b8_pass(d); break;
        case A_SPLITFAST_B8_U8: splitfast_b8_u8_pass(d); break;
        case A_SPLITAUTO: splitauto_pass(d); break;
        default: s1_timed = stage1_act(dp, ps); break;
      }
    };
    auto check_arm = [&](int a) -> uint64_t {
      switch (a) {
        case A_CONTRACT_CORE: return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_STAGED_CORE: return stream_check(d->ep_s.data(), d->nk_act, 0);
        case A_SPLIT_CORE: return stream_check(d->ep_split.data(), d->nk_act, 0);
        case A_SPLIT_LIST:
          return stream_check(d->ep_split.data(), d->nk_act, d->nxp_act);
        case A_CONTRACT_LIST:
          return stream_check(d->ep_c.data(), d->nk_act, d->nxp_act);
        case A_STAGED_LIST:
          return stream_check(d->ep_s.data(), d->nk_act, d->nxp_act);
        case A_CONTRACT_PLAIN:
          return stream_check(d->ep_c.data(), d->nk_act, d->u8);
        case A_STAGED_PLAIN:
          return stream_check(d->ep_s.data(), d->nk_act, d->u8);
        case A_SPLIT_PLAIN:
          return stream_check(d->ep_split.data(), d->nk_act, d->u8);
        case A_CONTRACT_FULL:
          return stream_check(d->ep_c.data(), d->nk_act,
                              mix(d->nxp_act, d->u8));
        case A_STAGED_FULL:
          return stream_check(d->ep_s.data(), d->nk_act,
                              mix(d->nxp_act, d->u8));
        case A_SPLIT_FULL:
          return stream_check(d->ep_split.data(), d->nk_act,
                              mix(d->nxp_act, d->u8));
        case A_SPLITC_CORE: return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_SPLITC_LIST:
          return stream_check(d->ep_c.data(), d->nk_act, d->nxp_act);
        case A_SPLITC_PLAIN:
          return stream_check(d->ep_c.data(), d->nk_act, d->u8);
        case A_SPLITC_FULL:
          return stream_check(d->ep_c.data(), d->nk_act,
                              mix(d->nxp_act, d->u8));
        case A_MASK_CORE:
          return ent_check(d->ent_v.data(), d->blocks);
        case A_MASK_LIST:
          return mix(ent_check(d->ent_v.data(), d->blocks),
                     stream_check(d->xp_c.data(), d->nxp_act, d->nxp_act));
        case A_EMIT_B8:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_U8: return d->u8;
        case A_CLASSIFY: return d->cl_act;
        case A_CLASSIFY_FAST: return d->cl_act;
        case A_MASK_FAST:
          return ent_check(d->ent_f.data(), d->blocks);
        case A_EMIT4:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_SPLITFAST_CORE:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_SPLITFAST_PLAIN:
          return stream_check(d->ep_c.data(), d->nk_act, d->u8);
        case A_CLASSIFY_FAST2: return d->cl_act;
        case A_MASK_FAST2:
          return ent_check(d->ent_f.data(), d->blocks);
        case A_SPLITFAST2_CORE:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_SPLITFAST2_PLAIN:
        case A_SPLITFAST2U_PLAIN:
          return stream_check(d->ep_c.data(), d->nk_act, d->u8);
        case A_EMIT3:
        case A_SPLITFAST3_CORE:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        case A_SPLITFAST_U8:
        case A_SPLITFAST3_U8:
        case A_SPLITLAG3_U8:
        case A_SPLITPROBE3:
        case A_SPLITPROBE_B8:
        case A_SPLITFAST_B8_U8:
        case A_SPLITAUTO:
          return stream_check(d->ep_c.data(), d->nk_act, d->u8);
        case A_SPLITLAG3:
          return stream_check(d->ep_c.data(), d->nk_act, 0);
        default: return stage1_check(dp, s1_timed);
      }
    };

    /* Interleaved rounds: forward then reverse, the smaller of the arm's two
       readings within the round.  One unrecorded round warms every arm before
       the first recorded one. */
    std::vector<double> read[A_COUNT];
    for (int r = -1; r < rounds; r++) {
      double got[A_COUNT][2];
      int fwd[A_COUNT];
      for (int a = 0; a < A_COUNT; a++) fwd[a] = a;
      if (r & 1) std::reverse(fwd, fwd + A_COUNT);
      for (int pass = 0; pass < 2; pass++) {
        for (int t = 0; t < A_COUNT; t++) {
          int a = fwd[pass == 0 ? t : A_COUNT - 1 - t];
          uint64_t t0 = now_ns();
          act(a);
          uint64_t t1 = now_ns();
          uint64_t h = check_arm(a);
          if (h != ref[a]) {
            std::fprintf(stderr,
                         "bench-contract: %s/%s: timed checksum %016" PRIx64
                         " != warm-up %016" PRIx64 "\n",
                         d->name.c_str(), arm_name(a), h, ref[a]);
            std::exit(3);
          }
          got[a][pass] = (double)(t1 - t0);
        }
      }
      if (r < 0) continue;
      for (int a = 0; a < A_COUNT; a++)
        read[a].push_back(got[a][0] < got[a][1] ? got[a][0] : got[a][1]);
    }

    /* Per-arm summaries and per-round ratios to their counterparts. */
    double ns[A_COUNT], cyc[A_COUNT];
    double ghz = 0.5 * (calibrate_ghz() + calibrate_ghz());
    for (int a = 0; a < A_COUNT; a++) {
      std::vector<double> v = read[a];
      ns[a] = median_of(v) / (double)d->n;   /* ns per byte */
      cyc[a] = ns[a] * ghz;
    }
    const int base[A_COUNT] = {
      A_STAGED_CORE, A_CONTRACT_CORE, A_CONTRACT_CORE,
      A_STAGED_LIST, A_CONTRACT_LIST, A_CONTRACT_LIST,
      A_STAGED_PLAIN, A_CONTRACT_PLAIN, A_CONTRACT_PLAIN,
      A_STAGED_FULL, A_CONTRACT_FULL, A_CONTRACT_FULL,
      A_CONTRACT_CORE, A_CONTRACT_LIST, A_CONTRACT_PLAIN, A_CONTRACT_FULL,
      A_SPLITC_PLAIN, A_SPLITC_LIST, A_SPLITC_CORE, A_SPLITC_PLAIN,
      A_MASK_CORE, A_MASK_CORE, A_SPLITC_PLAIN, A_SPLITC_CORE,
      A_SPLITC_CORE, A_STAGE1,
      A_MASK_CORE, A_SPLITC_PLAIN, A_SPLITC_CORE, A_STAGE1, A_STAGE1,
      A_SPLITC_CORE, A_SPLITC_CORE, A_STAGE1, A_STAGE1,
      A_SPLITFAST3_CORE, A_STAGE1,
      A_STAGE1, A_STAGE1, A_STAGE1, A_STAGE1,
      A_SPLITC_PLAIN
    };
    /* A second pair, for the rows whose adoption question is against the
       current pipeline rather than against the fused shape: the contracted
       split against the staged loop at the same list/UTF-8 combination. */
    const int base2[A_COUNT] = {
      -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1,
      A_STAGED_CORE, A_STAGED_LIST, A_STAGED_PLAIN, A_STAGED_FULL,
      -1, -1, -1, -1, -1, -1,
      A_MASK_CORE, A_EMIT_B8, A_SPLITC_CORE, A_SPLITC_PLAIN,
      A_MASK_CORE, A_MASK_FAST, A_SPLITC_CORE, A_SPLITC_PLAIN,
      A_SPLITC_PLAIN, A_EMIT_B8, A_SPLITC_CORE, A_SPLITC_PLAIN,
      A_SPLITC_PLAIN, A_SPLITFAST3_CORE, A_SPLITC_PLAIN,
      A_SPLITC_PLAIN, A_SPLITC_PLAIN, A_SPLITC_PLAIN, A_SPLITC_PLAIN, -1
    };
    const char *status = s1_ref.err == simdjson::SUCCESS ? "ok" : "rejected";

    for (int a = 0; a < A_COUNT; a++) {
      double ratio = 0, lo = 0, hi = 0;
      int have_ratio = 1;
      if ((a == A_STAGE1 && s1_ref.err != simdjson::SUCCESS) ||
          (base[a] == A_STAGE1 && s1_ref.err != simdjson::SUCCESS) ||
          a == A_STAGED_CORE || a == A_STAGED_LIST || a == A_STAGED_PLAIN ||
          a == A_STAGED_FULL) {
        /* A rejected stage 1 prices less work than the units, and a staged
           row's ratio is its contract counterpart's inverse: neither is a
           row. */
        have_ratio = 0;
      } else {
        std::vector<double> rr;
        for (int r = 0; r < rounds; r++)
          rr.push_back(read[a][r] / read[base[a]][r]);
        std::sort(rr.begin(), rr.end());
        ratio = median_of(rr);
        lo = rr.front();
        hi = rr.back();
      }
      std::printf("row cpu=%d doc=%s arm=%s emitter=%s bytes=%" PRIu64
                  " blocks=%" PRIu64 " median_ns_per_byte=%.6f gbps=%.3f"
                  " cycles_per_byte=%.4f core_ghz=%.3f status=%s",
                  cpu, d->name.c_str(), arm_name(a), d->b8 ? "b8" : "pos8",
                  d->n,
                  d->blocks, ns[a], 1.0 / ns[a], cyc[a], ghz, status);
      if (have_ratio)
        std::printf(" ratio=%.4f ratio_low=%.4f ratio_high=%.4f ratio_to=%s",
                    ratio, lo, hi, arm_name(base[a]));
      else
        std::printf(" ratio=. ratio_to=-");
      if (base2[a] >= 0) {
        std::vector<double> rr;
        for (int r = 0; r < rounds; r++)
          rr.push_back(read[a][r] / read[base2[a]][r]);
        std::sort(rr.begin(), rr.end());
        std::printf(" ratio2=%.4f ratio2_low=%.4f ratio2_high=%.4f"
                    " ratio2_to=%s",
                    median_of(rr), rr.front(), rr.back(),
                    arm_name(base2[a]));
      } else {
        std::printf(" ratio2=. ratio2_to=-");
      }
      std::printf("\n");
      if (samples) {
        std::printf("samples doc=%s arm=%s", d->name.c_str(), arm_name(a));
        for (double v : read[a]) std::printf(" %.1f", v);
        std::printf("\n");
      }
    }
    std::printf("doc cpu=%d name=%s bytes=%" PRIu64 " blocks=%" PRIu64
                " emitter=%s entry_positions=%" PRIu64
                " escape_positions=%" PRIu64 " utf8_word=%" PRIu64
                " stage1_status=%s stage1_structurals=%u\n",
                cpu, d->name.c_str(), d->n, d->blocks, d->b8 ? "b8" : "pos8",
                d->nk_ref, d->nxp_ref, leanllvm_json_utf8(d->b, d->n, 0),
                status, s1_ref.n);
  }
  (void)sink;
  return 0;
}
