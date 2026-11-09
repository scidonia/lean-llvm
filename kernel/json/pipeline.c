/* pipeline.c -- the assembled JSON pipeline: the caller of the stage-1 units.

   The block loop runs the mask unit over every 64-byte block of the document,
   turns the block's masks into the entry word, hands that word to the selected
   entry emitter, and appends the block's escape positions to the caller's list
   when the gate selects that arm.  After the loop the UTF-8 stage's word is the
   document-level validity verdict and stage 2 walks the entry stream into the
   caller's event stream and arena.

   Each unit is reached through the external entry point it publishes
   (`s1_block.h`, `entry.h`, `utf8.h`, `escape.h`), and this file is the one the
   timed object is compiled from.  The measured build instead inlines the whole
   pipeline into one translation unit; the staged form is what makes the
   refinements composable, and `PROVENANCE.md` records the difference.

   Every buffer the units write is the caller's (see `pipeline.h`): this body
   has no `alloca` and no initialising store, so a run of it touches only staged
   bytes.

   The pipeline's own text is the three lines of stage 1 the units do not carry:
   the scalar word `S` and its run starts, the entry word's composition, and the
   tail clamp that keeps lanes past the document's end out of the last block.
   That rule is `JsonScanSpec.entryMask64` and `limMask`; the rest of the loop is
   the units' own behaviour. */
#include "pipeline.h"

#include "entry.h"
#include "escape.h"
#include "s1_block.h"
#include "utf8.h"

uint64_t leanllvm_json_pipeline(const uint8_t *b, uint64_t n,
                                uint64_t *sc, uint64_t *mk, uint64_t *entw,
                                uint32_t *ep, uint64_t epcap, uint64_t *nk,
                                uint32_t *xp, uint64_t xpcap, uint64_t *nxp,
                                uint64_t *xcarry,
                                uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                                uint8_t *ev, uint64_t evcap, uint64_t *nev,
                                uint64_t *err, uint64_t arm) {
    s1_masks *m = (s1_masks *)mk;
    uint64_t nblk = (n + 63) >> 6;
    uint64_t prevS = 0;              /* the previous block's top scalar lane */
    uint64_t k = *nk;                /* the entry stream's cursor */

    (void)epcap;
    (void)xpcap;

    for (uint64_t i = 0; i < nblk; i++) {
        const uint8_t *p = b + (i << 6);
        leanllvm_json_s1_masks(p, (s1_carry *)sc, m);
        uint64_t S = ~(m->quote | m->delim | m->in_string | m->ws);
        uint64_t ent = m->quote | (m->delim & ~m->in_string);
        ent |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = n - (i << 6);
        if (lim < 64) ent &= (1ULL << lim) - 1ULL;
        entw[0] = ent;
        if (arm & 1)
            k = leanllvm_json_entry_b8(entw, i, 1, ep, k);
        else
            k = leanllvm_json_entry_pos8(entw, i, 1, ep, k);
        if (arm & 2)
            leanllvm_json_escape_list(m->backslash, m->ctl, m->in_string, i,
                                      xp, nxp, xcarry);
    }
    *nk = k;

    /* The document-level validity verdict, and the finalisation rule that owns
       an invalid UTF-8 document: the unit reports that the document is invalid
       and not where, so the refusal is the document's end. */
    if (leanllvm_json_utf8(b, n, (int)((arm >> 2) & 1)) != 0) {
        *err = n;
        return 0;
    }

    /* Stage 2 owns the remaining refusals — the structural, number and string
       rules and the first offset of each — and the arena and event cursors are
       the caller's. */
    return leanllvm_json_stage2(b, n, ep, k, xp, *nxp,
                                dst, dstcap, ndst, ev, evcap, nev, err);
}
