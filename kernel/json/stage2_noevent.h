/* stage2_noevent.h -- the no-event stage-2 entry point.

   `kernel/json/stage2_noevent.c` walks the same entry stream `stage2.h`
   describes, validates the same grammar and bodies with the same helper text,
   and writes no event record and no arena.  Instead it accumulates the reading
   the unchanged consumer fold makes of the certified route's event stream and
   arena, and reports it in three output slots.  The certified entry point and
   the shipped route are untouched: this is an additive unit, not a switch.

   ## The caller stages the scratch, and its capacity is a `pre`

   Nothing here allocates.  `scratch` is a caller-staged buffer with capacity
   `scratchcap`; it is an input, not an output, and its contents after a call
   are unspecified.  A decoded escaped body is written through it, so it must
   carry `len + US_SLACK` writable bytes for every string body the walk reaches,
   `len` the body's source length and `US_SLACK` the decoder's own slack past the
   decoded extent (`stage2.h`, "The decoded body of an escaped string").  A call
   that under-stages it is outside the unit's domain, and the violation traps
   exactly as the certified walk's `out_reserve` and `z_arena_reserve` do
   rather than overrunning.  There is no `*scratch_used`: no consumer reads the
   scratch's extent, and the reading the model states is a byte sum, not a
   cursor.

   ## The entry stream and the escape list

   `b .. b+n-1` is the document and `ep` with count `nep` its entry stream, in
   document order: quote characters, the structural bytes and the first byte of
   every scalar (`stage2.h`).  `xp` with count `nxp` is the stage-1 escape
   position list, and `xp`/`nxp` carry exactly the meaning and precondition
   `stage2.h` gives them: the list is required when the document carries
   escapes, and `nxp = 0` is a call for a document with none.  A body with no
   list entry is the certified walk's plain span form; the unit adds no
   list-free decoder of its own and calls no escape entry the certified stage-2
   unit does not call.

   ## The twelve slots

   The return is the verdict: `1` for acceptance, `0` for refusal.  On a
   refusal the three reading slots hold zero and `*err` is the first error
   offset the certified walk reports; on acceptance `*err` is not written.
   `values = tokens` is build mode (`probes/json/route/cost-profile/cost-profile.c`
   folds the consumer that way), so `tokens` and `values` are the same count.

   On acceptance the reading is the fold's, not a different arithmetic:

     `tokens`  one per event the certified stream would carry: one per entry
               that emits a record, so every structural token, key, string and
               scalar;
     `values`  the build-mode consumer's record count, which is `tokens`;
     `sum`     the fold's sum: the arena's byte sum plus, for every event, the
               tag byte and the record's `len` and `payload` words as the
               13/9/1-byte encoding declares them (`stage2.h`), added in
               `uint64_t`.  The arena's byte sum is the sum of every decoded
               escaped body's bytes in document order; a plain string body
               contributes no arena byte, its record naming a span into the
               input.

   `sum` is a 64-bit word, so it wraps modulo `2 ^ 64`; the reading is the exact
   mathematical sum when that sum is below `2 ^ 64`.  The differential's corpus
   is built to stay inside that bound, which is the condition under which the
   gate compares exact values.

   ## The object's symbols

   The unit's helper text is the certified unit's own: `stage2_noevent.c`
   includes `stage2.c` with its entry renamed, so every helper the walk calls
   except its literal comparison is that file's text byte for byte.  That one,
   `ne_lit`, is this unit's own: the certified check takes a `const char *` and
   the fragment has no global constants, so the packer stands in for it, and
   whether the two agree on the verdict and the offset is the refinement
   obligation stated over the pinned body and exercised by the differential —
   not a claim of this header.  The include therefore also defines the
   renamed certified entry as a second global in this object; nothing calls it,
   and the unit's symbol census records the pair alongside the one undefined
   project symbol, `leanllvm_json_escape_expand`, which is the escape entry the
   certified stage-2 unit itself calls.

   Whether this unit's accumulation equals the certified route's fold is the
   differential gate's subject, not this header's claim. */
#ifndef LEANLLVM_KERNEL_JSON_STAGE2_NOEVENT_H
#define LEANLLVM_KERNEL_JSON_STAGE2_NOEVENT_H

#include <stdint.h>

uint64_t leanllvm_json_stage2_noevent(const uint8_t *b, uint64_t n,
                                      const uint32_t *ep, uint64_t nep,
                                      const uint32_t *xp, uint64_t nxp,
                                      uint8_t *scratch, uint64_t scratchcap,
                                      uint64_t *tokens, uint64_t *values,
                                      uint64_t *sum, uint64_t *err);

/* The assembled pipeline with the reading tail: `kernel/json/pipeline.c`'s
   block loop and `arm` word, and the entry above in place of the certified
   stage 2.  The ABI is `leanllvm_json_pipeline`'s with the destination and
   event triplets replaced by the scratch pair; `*nk` and `*nxp` are stage 1's
   own outputs, written before the tail runs, and `tokens`, `values` and `sum`
   hold the reading the entry above reports.

   The three reading slots are written on every call.  On a refusal -- the
   UTF-8 stage's document-level one or the walk's -- they hold zero and `*err`
   is the first error offset, `n` for the UTF-8 stage's.  An acceptance writes
   the reading over all three.  They must be three distinct eight-byte objects,
   overlapping neither the document, the entry and escape streams, nor the
   scratch and stage-1 staging buffers. */
uint64_t leanllvm_json_pipeline_noevent(const uint8_t *b, uint64_t n,
                                        uint64_t *sc, uint64_t *mk,
                                        uint64_t *entw, uint32_t *ep,
                                        uint64_t epcap, uint64_t *nk,
                                        uint32_t *xp, uint64_t xpcap,
                                        uint64_t *nxp, uint64_t *xcarry,
                                        uint8_t *scratch, uint64_t scratchcap,
                                        uint64_t *tokens, uint64_t *values,
                                        uint64_t *sum, uint64_t *err,
                                        uint64_t arm);

#endif
