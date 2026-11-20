/* s1_blocks.c -- the contracted stage-1 mask pass.

   One loop over the document's 64-byte blocks runs the classifier and reduces
   its masks to the block's entry word: the unescaped quote, the structural
   byte outside a string, and the run start carried from the previous block's
   top scalar lane.  The word is clamped past the document's end and stored at
   `ent[i]`; when the gate selects the escape list, the block's backslash,
   control and in-string words go to the escape unit by value and the list's
   carry is the caller's `xcarry`.

   The classifier carry lives in this body and starts at zero, so no caller
   stages it.  The six mask words, the in-string carry and the previous block's
   scalar lane are registers; the unit has no stack and writes only `ent`, and
   `xp`/`*nxp`/`xcarry` when the gate selects the list.  The entry emitter is
   the caller's: it reads the `ent` array in one call over all blocks. */
#include "s1_blocks.h"

#include "escape.h"
#include "s1_block_impl.h"

void leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n, uint64_t *ent,
                             uint32_t *xp, uint64_t *nxp, uint64_t *xcarry,
                             uint64_t arm) {
    uint64_t nblk = (n + 63) >> 6;
    uint64_t prevS = 0;              /* the previous block's top scalar lane */
    S1F st = {0, 0, 0};              /* block-local classifier carry */

    for (uint64_t i = 0; i < nblk; i++) {
        const uint8_t *p = b + (i << 6);
        __m256i v0 = _mm256_loadu_si256((const __m256i *)(const void *)p);
        __m256i v1 = _mm256_loadu_si256((const __m256i *)(const void *)(p + 32));
        uint64_t qm, sm, im, ws, bm, ctl;
        s1f_masks(v0, v1, &st, &qm, &sm, &im, &ws, &bm, &ctl);
        uint64_t S = ~(qm | sm | im | ws);
        uint64_t e = qm | (sm & ~im);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = n - (i << 6);
        if (lim < 64) e &= (1ULL << lim) - 1ULL;
        ent[i] = e;
        if (arm & 2)
            leanllvm_json_escape_list(bm, ctl, im, i, xp, nxp, xcarry);
    }
}
