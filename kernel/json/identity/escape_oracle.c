/* escape_oracle.c -- the measured side of the escape unit's IR identity arm.

   It includes the vendored measured text and exposes the two entry points with
   the same names and the same signatures as `kernel/json/escape.c`, so
   `llvm-extract` lifts the measured statements and the unit's statements under
   one symbol each and `llvm-diff` compares them.

   The list half is `xlist.h`'s `xl_lanes` and `xl_emit`; `s1fuse.h` is what
   selects the measured `XL_EMIT=1` arm (`S1F_XS=5`, `s1fuse.h:70-71`) and it
   includes `xlist.h`.  The expander half is `usdec.h`'s `us_dec_x` at the
   measured `US_EMIT4=1`; `uj.c` comes first because the measured chain puts it
   first (`p16.c:57`) and `usdec.h` references `UJ_UNESC` and `uj_enc_word`
   from it.

   The wrappers are the unit's own new text, character for character: their
   bodies are what the two sides have in common and therefore what the arm
   compares.  A tidied parameter, a cast moved or a result channel added here
   would make the comparison describe a translation layer rather than the
   measured statements. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <immintrin.h>

#include "../measured/uj.c"
#include "../measured/usdec.h"
#include "../measured/s1fuse.h"

#if S1F_XS != 5
#error "compile escape_oracle.c with -DS1F_XS=5, the measured configuration (build49.sh:21)"
#endif
#if !defined(US_EMIT4) || US_EMIT4 != 1
#error "compile escape_oracle.c with -DUS_EMIT4=1, the measured configuration (build49.sh:28)"
#endif

void leanllvm_json_escape_list(uint64_t bs, uint64_t ctl, uint64_t im,
                               uint64_t blk0, uint32_t *xp,
                               uint64_t *xn, uint64_t *carry) {
    uint64_t esc = xl_lanes(bs, ctl, im, &carry[0], &carry[1]);
    xl_emit(esc, (uint32_t)(blk0 << 6), xp, xn);
}

uint64_t leanllvm_json_escape_expand(const uint8_t *b, uint64_t n, uint8_t *dst,
                                     uint64_t *err, const uint32_t *xp,
                                     uint64_t *xj, uint64_t nxp, uint64_t pos0) {
    return (uint64_t)us_dec_x(b, n, dst, (size_t *)err, xp, xj, nxp, pos0);
}
