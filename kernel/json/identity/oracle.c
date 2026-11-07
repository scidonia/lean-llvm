/* oracle.c -- the measured side of the IR identity arm.

   It includes the vendored measured header and calls `s1f_masks` with the two
   32-byte half vectors and a 64-bit output word per mask, which is exactly what
   the measured build loop does at `s1fuse.h:1701-1705`.  The probe function is
   the unit both arms lift out of their module and compare.

   The measured translation unit reaches the header through
   `sb34.c` -> `p16.c` -> `s2port.h` -> `usdec.h`, and `p16.c` supplies the libc
   headers the header's own functions use.  This TU is deliberately not that
   chain (it does not vendor stage 2 or the unescape sources): it restores the
   two libc headers the unevaluated functions need and includes the header
   alone.  `source-identity.sh --preprocess` is what shows this reduction does
   not change the mask region.

   `s1f_masks` is `static inline`; at the pinned flags it is inlined into the
   probe, so the module `ir-identity.sh` extracts holds the whole computation.

   The probe takes `void *` for the carry and casts inside: the measured `S1F`
   has six words and this unit's carry three, and the mask function touches only
   the first three.  Sharing the probe signature keeps both sides' functions
   type-identical, so `llvm-diff` compares code and not a struct's arity. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#if !defined(S1F_XS) || S1F_XS != 5
#error "compile oracle.c with -DS1F_XS=5, the measured configuration (build49.sh:21)"
#endif

#include "../measured/s1fuse.h"

#if S1F_CTAB != 1
#error "the measured S1F_CTAB is 1 (s1fuse.h:384-386), the table path"
#endif

void stage1_block_probe(const uint8_t *p, void *st, uint64_t *out) {
    __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
    __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
    s1f_masks(v0, v1, (S1F *)st, &out[0], &out[1], &out[2], &out[3], &out[4],
              &out[5]);
}
