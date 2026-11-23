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
       stream is the other's, so the choice cannot change the document's class).
       Bit 0 clear is the only arm with a setup obligation: POS8 reads the entry
       unit's file-static position table, and that table is filled only by
       `leanllvm_json_entry_table` (`entry.h`); see below.
     - bit 1: the escape-list gate, `0` = no list, `1` = build it.  This is an
       **arm selector**, not an escape-presence test: a document can carry
       escapes and still be given no list.  The shipping policy clears it on
       every document, and stage 2 then classifies each string body by scanning
       its own span; the list arm remains byte-exact and observationally
       equivalent on every consumer-visible field (`probes/json/route/guard.sh`);
     - bit 2: the UTF-8 stage's `ungated` parameter, whose two block paths agree
       on the verdict.

   Bits 3 and above are reserved and must be zero.

   ## Bit 0 clear requires the entry table

   `leanllvm_json_entry_pos8` reads `xl_pos8`, `entry.c`'s zero-initialised
   static table.  Its only writer is `leanllvm_json_entry_table`, which fills
   the unit's table and then the caller's 8 KiB slot; this pipeline does not
   call it, the loader does not fill it, and the emitter has no lazy
   initialiser of its own.  A caller that selects bit 0 clear must therefore
   call `leanllvm_json_entry_table` before its first pipeline call -- once per
   process, with an 8 KiB slot of its own.  If it does not, the pos8 wrapper
   traps (SIGILL) before it can return: a zero table would yield positions
   that are well formed and wrong, and the caller must not be able to mistake
   that for a document refusal.  Bit 0 set reads no table, so a pipeline that
   only ever runs b8 has no such obligation.  The trap is the enforced form of
   this clause; a caller that initialises sees no change to the ABI, the arm
   word, the return or `*err`.

   The return is the verdict, `1` for acceptance and `0` for refusal.  A refusal
   is one of: a non-zero UTF-8 stage word (`*err = n`, because that stage
   reports that the document is invalid and not where, and the refusal is the
   document-end rule), or stage 2's own refusal, whose offset it writes.
   Whether the accept/refuse verdict, the event stream and the first error
   offset are the reference parser's is the pipeline's specification, not this
   header's claim.

   The escape decoder is not called here: stage 2's string arm calls it per
   body (`stage2.c`'s `s2_string_body`), through `leanllvm_json_escape_expand`
   when a list was supplied and `leanllvm_json_escape_decode` when it was not.
   The assembled form keeps those calls one level down, so the decoder's record
   is consumed inside `stage2_satisfies` rather than here.

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
