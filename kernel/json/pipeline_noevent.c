/* pipeline_noevent.c -- the assembled pipeline with the no-event stage-2 tail.

   The block loop is `kernel/json/pipeline.c`'s, text unchanged: the mask unit
   over every 64-byte block, the entry word's composition, the emitter `arm`
   bit 0 selects, the escape list where `arm` bit 1 builds it, the tail clamp,
   and the UTF-8 stage's document-level verdict.  The entry stream's cursor and
   the escape list's count are written to `*nk` and `*nxp` before the tail, so
   both routes expose the same stage-1 outputs.

   Only the tail differs.  The entry stream is walked by
   `leanllvm_json_stage2_noevent` with the caller's scratch buffer, and the
   reading the certified route's consumer fold makes of the event stream and
   arena is accumulated into the caller's three slots; no arena and no event
   stream exist on this side.

   The buffers, the `arm` word and the UTF-8 refusal rule are `pipeline.h`'s;
   this entry keeps that ABI with the destination and event triplets replaced
   by the scratch pair, and `stage2_noevent.h` states the reading, the scratch
   capacity's precondition and the refusal slots. */
#include "stage2_noevent.h"

#include "entry.h"
#include "escape.h"
#include "s1_block.h"
#include "utf8.h"

uint64_t leanllvm_json_pipeline_noevent(const uint8_t *b, uint64_t n,
                                        uint64_t *sc, uint64_t *mk,
                                        uint64_t *entw, uint32_t *ep,
                                        uint64_t epcap, uint64_t *nk,
                                        uint32_t *xp, uint64_t xpcap,
                                        uint64_t *nxp, uint64_t *xcarry,
                                        uint8_t *scratch, uint64_t scratchcap,
                                        uint64_t *tokens, uint64_t *values,
                                        uint64_t *sum, uint64_t *err,
                                        uint64_t arm) {
    /* The three reading slots are pure outputs and are written on every call:
       zero from here until the tail's accumulation, so a refusal from either
       the UTF-8 gate above the tail or the walk inside it leaves zero, and an
       acceptance overwrites all three. */
    *tokens = 0;
    *values = 0;
    *sum = 0;

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
            /* POS8 reads the entry unit's table; the emitter traps if
               `leanllvm_json_entry_table` has not run (pipeline.h). */
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
       rules and the first offset of each — and the reading is accumulated into
       the caller's three slots instead of an arena and an event stream. */
    return leanllvm_json_stage2_noevent(b, n, ep, k, xp, *nxp,
                                        scratch, scratchcap,
                                        tokens, values, sum, err);
}
