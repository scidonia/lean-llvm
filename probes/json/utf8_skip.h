/* utf8_skip.h -- the gate's per-document block counts, derived from a staged
 * window.
 *
 * The UTF-8 stage's two arms differ in one thing only: a block whose sixty-four
 * bytes are all below 0x80, when the block before it is too, is skipped by the
 * gated arm and evaluated by the ungated one.  The verdict does not depend on
 * which arm ran, so the counts are the only per-document trace of the gate —
 * and they are a property of the staged window's bytes, not of the code under
 * test.  This header is that derivation, written once: `utf8_driver.c` prints
 * the counts beside the object's rows, `utf8_measured.c` beside the measured
 * statements', and `kernel/json/bench/paired-utf8.c` beside the timing
 * transcript.  The Lean body derives the same counts in Lean and the route's
 * script compares the two, so the numbers are never checked only against
 * themselves.
 *
 * The rule, precisely, with `nb = (n + 63) / 64` blocks:
 *
 *   - block `bi` is *all-ASCII* when its sixty-four bytes are all below 0x80,
 *     where a block past the document's last byte reads the window's zero
 *     padding;
 *   - block 0's predecessor is the three-byte prefix, which the stager leaves
 *     zero, so block 0 is skipped by the gated arm exactly when it is
 *     all-ASCII (`prev_ascii` starts set in the measured loop);
 *   - every other block is skipped when it and its predecessor are all-ASCII;
 *   - `skip + eval` is `nb`, which is asserted where the counts are computed.
 *
 * `doc` is the staged window's document pointer — the byte after the three
 * prefix bytes — and `n` its length, so the caller passes the same pointer the
 * unit was called with.  The window must be zero-filled past the document:
 * that padding is inside the last block and is part of what the classification
 * reads.
 */
#ifndef LEANLLVM_UTF8_SKIP_H
#define LEANLLVM_UTF8_SKIP_H

#include <stdint.h>

static void utf8_block_counts(const uint8_t *doc, uint64_t n, int ungated,
                              uint64_t *skip, uint64_t *eval) {
    uint64_t nb = (n + 63) / 64, s = 0, e = 0;
    int prev_ascii = 1;
    for (uint64_t bi = 0; bi < nb; bi++) {
        const uint8_t *blk = doc + (bi << 6);
        int ascii = 1;
        for (uint64_t k = 0; k < 64; k++)
            if (blk[k] >= 0x80) { ascii = 0; break; }
        if (!ungated && ascii && prev_ascii) s++;
        else e++;
        prev_ascii = ascii;
    }
    *skip = s;
    *eval = e;
}

#endif
