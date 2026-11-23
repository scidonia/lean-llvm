/* pipeline_fast_plain.c -- the split-stage-1 full-pipeline candidate.

   `split_plain` from `tests/json-units-bench/bench-contract.cc` is
   `split_pass(d, 0)` followed by the UTF-8 unit: the staged six-word
   classifier, the entry-word composition, one entry-emitter call over the
   collected words, and the separate `leanllvm_json_utf8` sweep.  This file
   carries that stage 1 and the unchanged stage 2, with the emitter selected
   per entry rather than by the bench's per-document class word.  The header
   states the ABI, the staging promises, the pos8 table obligation and the
   fields a harness compares; `pipeline.h` is the default route's ABI and is
   not changed by this file.

   This file carries no bench harness, no clock and no arm selector, and it
   includes no `LeanLLVM/Refinement` machinery: it is a prototype of the
   shape, gated by the harness over the corpus rather than by a theorem. */
#include "pipeline_fast_plain.h"

#include <stdint.h>

#include "entry.h"
#include "s1_block.h"
#include "stage2.h"
#include "utf8.h"

/* The split stage 1 and the two stage-1 tails.  The body takes the certified
   pipeline's argument list — the two caller-staged stage-1 slots `sc` (24 B)
   and `mk` (48 B), the `ent` array, the entry stream, the two cursors and the
   `arm` selector — so it stages exactly what `pipeline.c` stages and has no
   `alloca` of its own.  The classifier, the entry-word composition and the tail
   clamp are `pipeline.c`'s three lines; the emitter is one call over the
   collected words, as the split shape uses it.  `arm & 1` selects the emitter
   (B8 on a set bit), `arm & 2` is unused (the shape is list-free), and the
   UTF-8 gate is the default's ungated call. */
uint64_t pf_plain_pipeline(const uint8_t *b, uint64_t n, uint64_t *sc,
                                  uint64_t *mk, uint64_t *ent, uint32_t *ep,
                                  uint64_t epcap, uint64_t *nk, uint32_t *xp,
                                  uint64_t xpcap, uint64_t *nxp,
                                  uint64_t *xcarry, uint8_t *dst, uint64_t dstcap,
                                  uint64_t *ndst, uint8_t *ev, uint64_t evcap,
                                  uint64_t *nev, uint64_t *err, uint64_t arm) {
    s1_masks *m = (s1_masks *)mk;
    uint64_t prevS = 0;
    uint64_t nblk = (n + 63) >> 6;
    uint64_t k;

    (void)epcap;
    (void)xpcap;
    (void)xcarry;

    for (uint64_t i = 0; i < nblk; i++) {
        leanllvm_json_s1_masks(b + (i << 6), (s1_carry *)sc, m);
        uint64_t S = ~(m->quote | m->delim | m->in_string | m->ws);
        uint64_t e = m->quote | (m->delim & ~m->in_string);
        e |= S & ~((S << 1) | prevS);
        prevS = S >> 63;
        uint64_t lim = n - (i << 6);
        if (lim < 64) e &= (1ULL << lim) - 1ULL;
        ent[i] = e;
    }

    k = (arm & 1) ? leanllvm_json_entry_b8(ent, 0, nblk, ep, *nk)
                  : leanllvm_json_entry_pos8(ent, 0, nblk, ep, *nk);
    *nk = k;

    /* The document-level verdict keeps the default's rule and its order: the
       entry stream is written first, and an invalid document is refused at
       its end, because the UTF-8 stage reports that the document is invalid
       and not where. */
    if (leanllvm_json_utf8(b, n, 0) != 0) {
        *err = n;
        return 0;
    }

    /* Stage 2 owns the remaining refusals; the shape is list-free, so
       `xp`/`*nxp` are the caller's and pass through unchanged. */
    return leanllvm_json_stage2(b, n, ep, k, xp, *nxp,
                                dst, dstcap, ndst, ev, evcap, nev, err);
}

/* The pos8 entry reads the entry unit's static table, so the caller's
   obligation is `leanllvm_json_entry_table` once before the first call
   (`entry.h`); an unfilled table traps in the pos8 wrapper rather than
   emitting a well-formed stream of wrong positions.  The b8 entry below needs
   no initialisation. */
uint64_t leanllvm_json_pipeline_fast_plain_pos8(const uint8_t *b, uint64_t n,
                                                uint64_t *ent,
                                                uint32_t *ep, uint64_t epcap,
                                                uint64_t *nk,
                                                uint32_t *xp, uint64_t xpcap,
                                                uint64_t *nxp,
                                                uint8_t *dst, uint64_t dstcap,
                                                uint64_t *ndst,
                                                uint8_t *ev, uint64_t evcap,
                                                uint64_t *nev,
                                                uint64_t *err) {
    /* This entry is the caller of the proved body: it stages the two slots the
       certified pipeline's caller stages (`s1_block.h`: 24 and 48 zero bytes)
       and selects the POS8 arm.  The allocation is the caller's, not the
       body's, which is why `pf_plain_pipeline` has no `alloca`. */
    uint64_t sc[3] = {0, 0, 0};
    uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t xcarry[2] = {0, 0};
    return pf_plain_pipeline(b, n, sc, mk, ent, ep, epcap, nk, xp, xpcap, nxp,
                             xcarry, dst, dstcap, ndst, ev, evcap, nev, err, 0);
}

uint64_t leanllvm_json_pipeline_fast_plain_b8(const uint8_t *b, uint64_t n,
                                              uint64_t *ent,
                                              uint32_t *ep, uint64_t epcap,
                                              uint64_t *nk,
                                              uint32_t *xp, uint64_t xpcap,
                                              uint64_t *nxp,
                                              uint8_t *dst, uint64_t dstcap,
                                              uint64_t *ndst,
                                              uint8_t *ev, uint64_t evcap,
                                              uint64_t *nev,
                                              uint64_t *err) {
    uint64_t sc[3] = {0, 0, 0};
    uint64_t mk[6] = {0, 0, 0, 0, 0, 0};
    uint64_t xcarry[2] = {0, 0};
    return pf_plain_pipeline(b, n, sc, mk, ent, ep, epcap, nk, xp, xpcap, nxp,
                             xcarry, dst, dstcap, ndst, ev, evcap, nev, err, 1);
}
