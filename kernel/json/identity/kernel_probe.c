/* kernel_probe.c -- the extracted side of the IR identity arm.

   The translation unit is `s1_block.c` itself, included so the probe can call
   the unit's internal `static inline` `s1f_masks` instead of the public
   wrapper: the wrapper's loads are this unit's new code, and the comparison is
   about the mask function both sides share.  `llvm-extract` lifts the probe
   (and nothing else) out of the module.

   The probe's signature is `oracle.c`'s, character for character, including the
   `void *` carry it casts: a difference in a struct's arity would be reported
   by `llvm-diff` as a type difference and would say nothing about the code. */
#include "../s1_block.c"

void stage1_block_probe(const uint8_t *p, void *st, uint64_t *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    s1f_masks(v0, v1, (S1F *)st, &out[0], &out[1], &out[2], &out[3], &out[4],
              &out[5]);
}
