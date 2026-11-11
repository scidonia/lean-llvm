#include <stdint.h>
#include <immintrin.h>

/* The window scanner's candidate body, as C, for capture with
 *
 *   clang -S -emit-llvm -O2 -mavx2 -fno-slp-vectorize
 *
 * and demotion with
 *
 *   opt -passes='reg2mem,instnamer'
 *
 * by probes/install/ir/capture-json-scan.sh.  This is not the certified body:
 * the certified body is printed from the Lean AST in
 * LeanLLVM/Refinement/JsonScanBody.lean into
 * probes/install/ir/json-scan-body.ll, and this source, with the fixture
 * captured from it, is the measured record of what the compiler makes of the
 * algorithm.  Nothing certifies these bytes.
 *
 * The ABI is the one
 * LeanLLVM/Refinement/JsonScanABI.lean fixes: `i32 @leanllvm_json_scan_window(
 * ptr %in, ptr %out, ptr %state, i32 %valid)` reads the first `valid` bytes of
 * `%in`, writes one 32-bit structural mask at `%out` and the next carry in the
 * sixteen-byte slot at `%state`, and returns the status word.
 *
 * Three lane masks, one byte rule.  A full window (`valid == 32`) computes the
 * three per-lane tests the skip path reads -- quote, backslash and `< 0x20` --
 * with the AVX2 chain, and a short window accumulates the same three masks
 * scalar-ly over its own lanes, because the thirty-two-byte load is only
 * legitimate when the caller promises thirty-two readable bytes.  Both paths
 * then run one byte-rule loop over `valid` lanes, with the carry in the slot's
 * four words and the stop as an early `ret`, so the rule has one description in
 * the emitted code.
 *
 * Two source shapes here exist for the fragment's sake, and neither changes the
 * value computed:
 *
 *   * the twelve-byte structural set is tested through a membership table in
 *     two 64-bit halves, not a comparison chain.  A chain of equality
 *     comparisons on one byte is folded by the optimiser into a `switch`, and
 *     the fragment has no form for `switch`;
 *   * the byte rule computes its answer as a value -- nested conditional
 *     expressions over `b`, the carry and the lane index -- and branches only
 *     on the computed stop word.  A branch chain on `b` is a `switch` for the
 *     same reason.  The one other branch is the skip test, which is a
 *     conjunction of mask bits and one byte comparison: a lane is skipped only
 *     when it certainly cannot change the carry.
 *
 * The structural mask is accumulated scalar-ly, also for the fragment's sake: a
 * word derived from `movemask` and then stored is rewritten into a store of the
 * packed `<32 x i1>` vector, and giving the word another integer use, storing it
 * as bytes or as two halves does not prevent the rewrite.  So `%out` is filled
 * by the lane loop that reads the bytes.
 *
 * `-fno-slp-vectorize` is not cosmetic: with the SLP vectoriser enabled the
 * structural-mask pass is turned into `insertelement`/`shufflevector` over
 * `<8 x i8>` constants, and the two `#pragma clang loop` lines cover the loop
 * vectoriser, which loop metadata does not extend to straight-line SLP. */

typedef struct {
  uint32_t flags;
  uint32_t count;
  uint32_t lo;
  uint32_t hi;
} slot_t;

#define K_CLOSE 64u
#define K_REFUSE 128u
#define R_CONTROL 512u
#define R_BADUTF8 768u
#define STATUS(k, kind, reason) ((k) + 1u | (kind) | (reason))

/* The twelve bytes `IsStructOrSpaceB` marks: bytes 0..63 in the low half,
 * 64..127 in the high half, and nothing at or above 128. */
#define STRUCT_LO 0x0400100500002600ULL
#define STRUCT_HI 0x2800000038000000ULL

static inline __attribute__((always_inline)) uint32_t bits(__m256i m) {
  return (uint32_t)_mm256_movemask_epi8(m);
}

static inline __attribute__((always_inline)) uint32_t is_struct(uint32_t b) {
  uint64_t t = (b < 64u) ? STRUCT_LO : ((b < 128u) ? STRUCT_HI : 0ULL);
  return (uint32_t)((t >> (b & 63u)) & 1ULL);
}

int32_t leanllvm_json_scan_window(const uint8_t *in, uint32_t *out,
                                  slot_t *st, uint32_t valid) {
  uint32_t ms = 0u;
  uint32_t mq = 0u;
  uint32_t mb = 0u;
  uint32_t mc = 0u;

  if (valid == 32u) {
    __m256i v = _mm256_loadu_si256((const __m256i *)in);
    mq = bits(_mm256_cmpeq_epi8(v, _mm256_set1_epi8('"')));
    mb = bits(_mm256_cmpeq_epi8(v, _mm256_set1_epi8('\\')));
    mc = bits(_mm256_cmpeq_epi8(
        _mm256_and_si256(v, _mm256_set1_epi8((char)0xE0)),
        _mm256_setzero_si256()));
  }

#pragma clang loop vectorize(disable) unroll(disable)
  for (uint32_t k = 0; k < valid; k++) {
    uint32_t b = in[k];
    uint32_t bit = 1u << k;
    ms |= is_struct(b) << k;
    if (valid != 32u) {
      mq |= (b == 0x22u) << k;
      mb |= (b == 0x5Cu) << k;
      mc |= (b < 0x20u) << k;
    }
  }

  *out = ms;

#pragma clang loop vectorize(disable) unroll(disable)
  for (uint32_t k = 0; k < valid; k++) {
    uint32_t bit = 1u << k;
    uint32_t b = in[k];
    uint32_t flags = st->flags & 3u;
    uint32_t count = st->count;
    uint32_t lo = st->lo;
    uint32_t hi = st->hi;

    if (flags == 1u && count == 0u && !(mq & bit) && !(mb & bit) &&
        !(mc & bit) && b < 0x80u)
      continue;

    uint32_t inside = flags & 1u;
    uint32_t odd = (flags & 2u) != 0u;
    uint32_t cont = (count != 0u);
    uint32_t isq = (b == 0x22u);
    uint32_t isb = (b == 0x5Cu);
    uint32_t isc = (b < 0x20u);
    uint32_t contok = (lo <= b) & (b <= hi);
    uint32_t apply = inside & (1u - isc) & (b < 0x80u);

    uint32_t l1 = (b >= 0xC2u) & (b <= 0xDFu);
    uint32_t l2 = (b == 0xE0u);
    uint32_t l3 = (b >= 0xE1u) & (b <= 0xECu);
    uint32_t l4 = (b == 0xEDu);
    uint32_t l5 = (b >= 0xEEu) & (b <= 0xEFu);
    uint32_t l6 = (b == 0xF0u);
    uint32_t l7 = (b >= 0xF1u) & (b <= 0xF3u);
    uint32_t l8 = (b == 0xF4u);
    uint32_t lead = l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8;
    uint32_t ln = l1 | 2u * (l2 | l3 | l4 | l5) | 3u * (l6 | l7 | l8);
    uint32_t llo = l1 * 0x80u | l2 * 0xA0u | (l3 | l4 | l5) * 0x80u |
                   l6 * 0x90u | (l7 | l8) * 0x80u;
    uint32_t lhi = l1 * 0xBFu | l2 * 0xBFu | l3 * 0xBFu | l4 * 0x9Fu |
                   l5 * 0xBFu | l6 * 0xBFu | l7 * 0xBFu | l8 * 0x8Fu;

    uint32_t nflags = cont ? flags
                    : odd ? (flags - 2u)
                    : isq ? (inside ? flags : 1u)
                    : isb ? (3u * inside)
                    : flags;
    uint32_t ncount = cont ? (contok ? count - 1u : count) : (lead ? ln : 0u);
    uint32_t nlo = cont ? (contok ? (count == 1u ? 0u : 0x80u) : lo)
                        : (lead ? llo : 0u);
    uint32_t nhi = cont ? (contok ? (count == 1u ? 0u : 0xBFu) : hi)
                        : (lead ? lhi : 0u);
    uint32_t stop = cont ? (contok ? 0u : STATUS(k, K_REFUSE, R_BADUTF8))
                  : odd ? 0u
                  : isq ? (inside ? STATUS(k, K_CLOSE, 0u) : 0u)
                  : isb ? 0u
                  : (inside & isc) ? STATUS(k, K_REFUSE, R_CONTROL)
                  : (apply & (1u - lead)) ? STATUS(k, K_REFUSE, R_BADUTF8)
                  : 0u;

    uint32_t keep = (stop != 0u);
    st->flags = keep ? flags : nflags;
    st->count = keep ? count : ncount;
    st->lo = keep ? lo : nlo;
    st->hi = keep ? hi : nhi;
    if (keep) return (int32_t)stop;
  }
  return 0;
}
