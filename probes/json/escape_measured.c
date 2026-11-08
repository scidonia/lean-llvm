/* escape_measured.c -- the measured stage-1 escape-position emitter, one TU.
 *
 * The escape list is the pipeline's third stage-1 output: for every byte
 * inside a string that is either a control byte or the first backslash of a
 * run, the byte's position, in document order.  The emitter is the vendored
 * configuration's, not a copy of it: this translation unit includes
 * `kernel/json/measured/s1fuse.h`, which at the measured `-D` set
 * (`S1F_XS=5`) selects `XL_EMIT 1` from `xlist.h` and, through `S1F_XS_DYN`,
 * suppresses the list on a PLAIN document.  Nothing in `kernel/json/measured/`
 * is edited; the route compiles this file against that directory.
 *
 * The entry point below is this TU's boundary: a document's bytes in, the
 * `uint32_t` stream the measured builder left and its count out.  The stream
 * is the builder's own `s1f_esc_list`, so the positions and the count are
 * exactly what `xl_emit` left in it -- the fixed eight-entry batch's writes
 * past the true count are not read, and a PLAIN document returns the NULL and
 * zero the measured gate leaves.  The caller stages the document with 64
 * readable bytes per block, which is the builder's own contract.
 *
 * `s1f_build_dispatch` also builds the entry stream, which this entry point
 * discards: the measured builder owns both streams and the escape list is read
 * from the same build, so the emitter runs in the loop it was measured in and
 * not in a second one written here.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "s1fuse.h"

/* One document: return the measured escape-position list and its count.
   `doc` must have 64 readable bytes per block. */
const uint32_t *escape_measured_list(const uint8_t *doc, uint64_t n,
                                     uint64_t *nx) {
    uint64_t nb = (n + 63) / 64;
    uint64_t err = 0;
    /* One position per byte at most, plus the batch's eight-entry reserve at
       the end of the document. */
    uint32_t *ent = (uint32_t *)malloc(((nb ? nb : 1) * 64 + 16) * sizeof *ent);
    if (!ent) {
        *nx = 0;
        return NULL;
    }
    (void)s1f_build_dispatch(doc, n, ent, &err);
    free(ent);
    return s1f_esc_list(nx);
}
