/* pipeline.h -- the assembled JSON pipeline's one entry point.

   `kernel/json/pipeline.c` is the caller the five stage-1 units were hoisted
   for: the block loop that runs the mask unit over every 64-byte block, turns
   each block's masks into the entry word and hands it to the selected entry
   emitter, appends each block's escape positions to the caller's list where the
   gate selects that arm, and then hands the entry stream to stage 2.  The
   measured build inlines all of this into one translation unit; this header is
   the staged form's ABI, with every unit reached through its own external
   entry point, because an inlined body of thousands of instructions admits no
   compositional proof.

   ## The caller stages every buffer

   Nothing here allocates, and the body has no `alloca` and no `llvm.memset`:
   every scratch the units write is the caller's, so the model's run of the body
   touches only bytes the caller staged.  The four scratch objects are

     - `sc`:     the mask unit's three-word carry (`s1_carry`), all zero for a
                 document's first block;
     - `mk`:     the mask unit's six-word output slot (`s1_masks`);
     - `entw`:   the entry word's one-word slot, read back by the emitter;
     - `xcarry`: the escape list's two-word carry, both zero for a document's
                 first block.

   `mk` and `sc` are written by the mask unit and read back here, and `entw` is
   written here and read back by the entry emitter, so each is a real memory
   object and the caller sizes it at the structs `s1_block.h` and `entry.h`
   declare.

   ## The ABI

   The document is `b .. b+n-1`.  The entry stream is the caller's `ep` with
   capacity `epcap` `uint32_t`s and cursor `*nk`; the escape list is `xp` with
   capacity `xpcap` and count `*nxp`; the decoded-string arena is `dst` with
   capacity `dstcap` and cursor `*ndst`; the event stream is `ev` with capacity
   `evcap` and count `*nev`.  `*err` is the first error offset when the run
   refuses, and is not written when it accepts.

   `arm` selects the three per-document arms, and each is a selector rather
   than a classifier:

     - bit 0: the entry emitter, `0` = `leanllvm_json_entry_pos8`,
       `1` = `leanllvm_json_entry_b8` (C99's selection theorem: either emitter's
       stream is the other's, so the choice cannot change the document's class);
     - bit 1: the escape-list gate, `0` = no list, `1` = build it.  This is the
       measured density probe's decision, and it is an **arm selector**, not an
       escape-presence test: a document can carry escapes and still be given no
       list;
     - bit 2: the UTF-8 stage's `ungated` parameter, whose two block paths agree
       on the verdict.

   Bits 3 and above are reserved and must be zero.

   The return is the verdict, `1` for acceptance and `0` for refusal.  A refusal
   is one of: a non-zero UTF-8 stage word (`*err = n`, because that stage
   reports that the document is invalid and not where, and the refusal is the
   document-end rule), or stage 2's own refusal, whose offset it writes.
   Whether the accept/refuse verdict, the event stream and the first error
   offset are the reference parser's is the pipeline's specification, not this
   header's claim.

   The escape *expander* is not called here: in the measured assembly stage 2's
   consumer calls it per string (`s2port.h:526-529`), and the assembled form
   keeps that call one level down, so the expander's record is consumed inside
   `stage2_satisfies` rather than here.

   See README.md for the assembly's provenance, its capture and its limits. */
#ifndef LEANLLVM_KERNEL_JSON_PIPELINE_H
#define LEANLLVM_KERNEL_JSON_PIPELINE_H

#include <stdint.h>

/* The stage-2 slot, which `kernel/json/stage2.h` provides once the unit exists.
   Declared here in the shape the pipeline consumes: the document, the entry
   stream, the escape list, and the caller's arena and event stream.  It returns
   the verdict (`1` acceptance, `0` refusal) and writes `*err` on a refusal. */
uint64_t leanllvm_json_stage2(const uint8_t *b, uint64_t n,
                              const uint32_t *ep, uint64_t nep,
                              const uint32_t *xp, uint64_t nxp,
                              uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                              uint8_t *ev, uint64_t evcap, uint64_t *nev,
                              uint64_t *err);

uint64_t leanllvm_json_pipeline(const uint8_t *b, uint64_t n,
                                uint64_t *sc, uint64_t *mk, uint64_t *entw,
                                uint32_t *ep, uint64_t epcap, uint64_t *nk,
                                uint32_t *xp, uint64_t xpcap, uint64_t *nxp,
                                uint64_t *xcarry,
                                uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                                uint8_t *ev, uint64_t evcap, uint64_t *nev,
                                uint64_t *err, uint64_t arm);

#endif
