/* escape_guard.h -- whether the stage-1 escape list can be skipped.
 *
 * `pipeline.h`'s arm bit 1 selects the escape list: with it set, the pipeline
 * calls `leanllvm_json_escape_list` on every 64-byte block; with it clear it
 * never calls it and `*nxp` stays zero.  The list is
 * `(ctl | e) & in_string` per block (`kernel/json/escape.c`'s `xl_lanes`),
 * where `e` is the block's escape-start lanes -- every bit of `e` is derived
 * from the block's backslash lanes -- and `ctl` is the block's raw control-byte
 * lanes.  So
 *
 *     no byte is 0x5C  AND  no byte is at or below 0x1F
 *
 * implies the list is empty on every block, which makes the two arm words the
 * same call: the only work arm bit 1 adds is that call, and stage 2 reads the
 * list through `*nxp` alone.  The condition is necessary for this pipeline's
 * list, not merely sufficient for the backslash part: a raw control byte
 * inside a string is a position too, and the escape corpus's
 * `short:raw-control` (`{"a":"<LF>"}`) is a document with no backslash whose
 * arm-2 list is not empty.  It is not the measured build's density gate and
 * says nothing about it (`kernel/json/README.md`): this is arm 2's own list.
 *
 * The two byte classes are the two lanes the stage-1 mask unit reports
 * (`s1_block.h`'s `backslash` and `ctl`), read as presence over the document
 * instead of as sixty-four-lane words: the guard is the fact the lanes carry,
 * and a full mask pass costs 12 ns/block where this scan costs 1.6-2.1 over a
 * document and 0.4-0.6 where the early exit finds a backslash
 * (`probes/json/core-shape/shape.sh`'s paired table).  The list it replaces
 * costs 1.1-4.9 ns/block, so the guard is only worth taking if it is cheaper
 * than the thing it skips -- which is the measurement, not this comment.
 *
 * The scan reads `b[0 .. n-1]` and no byte past it, in 32-byte chunks and a
 * scalar tail; the document's staged window has 64 readable bytes per block for
 * the pipeline's own unaligned reads, which this scan does not need.  It
 * allocates nothing, reads nothing else, and has no failure mode.
 */
#ifndef LEANLLVM_ROUTE_ESCAPE_GUARD_H
#define LEANLLVM_ROUTE_ESCAPE_GUARD_H

#include <immintrin.h>
#include <stdint.h>

/* 1 when the document carries neither a backslash nor a control byte, so the
   stage-1 escape list is empty and the pipeline's arm bit 1 may be cleared;
   0 otherwise, which leaves the arm the caller selected.

   A backslash anywhere settles the answer, so the first chunk that carries one
   returns immediately: on the documents whose list is not empty the scan stops
   at the first escape, which is the class the guard cannot help and therefore
   the one it must not tax.  The control bytes are accumulated and tested once at
   the end, because one anywhere means the same answer. */
static inline int leanllvm_route_escape_can_skip(const uint8_t *b, uint64_t n) {
  const __m256i backslash = _mm256_set1_epi8((char)0x5C);
  const __m256i ctl19 = _mm256_set1_epi8(0x1F);
  const __m256i zero = _mm256_setzero_si256();
  __m256i controls = zero;
  uint64_t i = 0;
  for (; i + 32 <= n; i += 32) {
    __m256i v = _mm256_loadu_si256((const __m256i *)(const void *)(b + i));
    /* The mask unit's `backslash` lane: `v == '\\'`. */
    __m256i bs = _mm256_cmpeq_epi8(v, backslash);
    if (!_mm256_testz_si256(bs, bs)) return 0;
    /* The mask unit's `ctl` lane: `min_epu8(v, 0x1F) == v`, i.e. `v <= 0x1F`. */
    controls = _mm256_or_si256(
        controls, _mm256_cmpeq_epi8(_mm256_min_epu8(v, ctl19), v));
  }
  if (!_mm256_testz_si256(controls, controls)) return 0;
  for (; i < n; i++) {
    if (b[i] == 0x5C || b[i] <= 0x1F) return 0;
  }
  return 1;
}

#endif
