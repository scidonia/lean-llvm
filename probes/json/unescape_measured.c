/* unescape_measured.c -- the measured per-body escape expander, one TU.
 *
 * `us_dec_x` is the list-driven decoder the stage-2 consumer calls
 * (`s2port.h:257` in the measured tree) and the body of the escape unit's
 * second entry point.  Its kernels are `us_dec_kernel` (`usdec.h:557`) and
 * `us_body_kernel` (`usdec.h:1148`); the entry itself is the carry-and-loop
 * form at `usdec.h:858`.
 *
 * This translation unit is the measured one, not a copy of it: it includes
 * `kernel/json/measured/uj.c` and `kernel/json/measured/usdec.h`, at the
 * measured `-D` set (`build49.sh:19-21`: `-DUS_EMIT4=1`, and `S2_DEC_GATE=2`
 * selecting `usdec_gate.h` in the consumer).  `uj.c` comes first because the
 * measured chain puts it first: `sb34.c:28` includes `p16.c`, whose `:57` is
 * `#include "uj.c"`, before `:29` includes `s2port.h`, and `usdec.h`'s escape
 * step and encoder reference `UJ_UNESC`, `UJ_HEX`, `uj_enc` and `uj_enc_word`
 * from that file.  Nothing under `kernel/json/measured/` is edited.
 *
 * The entry point below is this TU's boundary: the body's bytes, the body's
 * absolute start, the document's position list and the list cursor in; the
 * decoded length or `US_FAIL`, the first error offset, and the advanced cursor
 * out.  The carry is in the signature rather than assumed, because the caller
 * that walks several bodies carries it: `k` advances past the positions below
 * `pos0`, and a decoded surrogate pair consumes the pair's second position
 * (`usdec.h:900-904`).
 *
 * `dst` needs 64 bytes of slack past the decoded extent: `us_run_long` copies
 * whole 64-byte windows and the run copy may store a whole vector past the
 * run's end (`usdec.h:396-411`).  The probe stages the slack itself.  The body
 * needs 32 readable bytes past its end for the same reason, on every path:
 * `us_run`'s first load is unconditional, so the last short segment loads a
 * whole vector from `p + i` with `i` up to `n`.  Neither is a property of the
 * probe; both are what a caller of the measured entry must stage.
 */
#include <stdint.h>
#include <string.h>
#include <immintrin.h>

#include "uj.c"
#include "usdec.h"

#if !defined(US_EMIT4) || US_EMIT4 != 1
#error "compile unescape_measured.c with -DUS_EMIT4=1, the measured configuration (build49.sh:26)"
#endif
#if US_ESC != 0
#error "the measured US_ESC is 0: simple inline, \\u inline (usdec.h:56-59, build49.sh sets no -DUS_ESC)"
#endif
#if US_XP_INLINE != 0
#error "the measured US_XP_INLINE is 0: us_dec_x is out of line (usdec.h:850-853)"
#endif
#if US_EXP != 0
#error "the measured US_EXP is 0: the consumer walks the compacted list (build49.sh sets no -DUS_EXP)"
#endif

/* One body: decode `n` bytes at absolute `pos0`, consuming the document's
   position list from `*xj`.  Returns the decoded length, or ((size_t)-1) on a
   refused escape with `*err` set to the body-relative offset. */
size_t unescape_measured(const uint8_t *body, uint64_t n, uint8_t *dst,
                         size_t *err, const uint32_t *xp, uint64_t *xj,
                         uint64_t nxp, uint64_t pos0) {
    return us_dec_x(body, n, dst, err, xp, xj, nxp, pos0);
}
