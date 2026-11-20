/* s1_block.c -- the stage-1 classification mask unit of the measured SIMD JSON
   pipeline.

   The classifier, its two tables and `s1f_masks` are the measured text of
   kernel/json/measured/s1fuse.h and live in `s1_block_impl.h`, which the
   contracted block unit (`s1_blocks.c`) includes as well.  The file's own text
   is `leanllvm_json_s1_masks`, the wrapper that stages a 64-byte block at the
   ABI of s1_block.h and publishes all six mask words; the block unit runs the
   same classifier without materialising them.

   `s1f_masks` keeps its measured name, its measured parameter type `S1F *` and
   its measured signature, so the token diff and the IR diff both compare the
   measured function rather than a re-spelling of it; `S1F` is this unit's
   three-word carry, the same object as `s1_carry`. */
#include "s1_block.h"

#include "s1_block_impl.h"

/* The ABI of s1_block.h.  The two loads are the new code: the measured
   `_mm256_loadu_si256` pair lives in `s1f_build2`, which is the pipeline loop
   and not this unit.  They are unaligned loads, so the unit's contract asks
   for 64 readable bytes and no alignment. */
void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry, s1_masks *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    uint64_t qm, sm, im, ws, bm, ctl;
    s1f_masks(v0, v1, (S1F *)carry, &qm, &sm, &im, &ws, &bm, &ctl);
    out->quote = qm;
    out->delim = sm;
    out->in_string = im;
    out->ws = ws;
    out->backslash = bm;
    out->ctl = ctl;
}
