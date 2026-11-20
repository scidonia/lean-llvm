/* s1_blocks.h -- the contracted stage-1 block unit's one public entry point.

   The document in, one 64-bit entry word per 64-byte block at `ent`, and the
   escape positions appended to `xp`/`*nxp` when the gate selects that arm.  The
   block words are the stage-1 composition (`JsonScanSpec.entryMask64`): the
   unescaped quote, the structural byte outside a string, and the run start
   carried from the previous block, clamped past the document's end.  The six
   mask words, both classifier carries and the entry word stay in registers, so
   this unit has no caller-staged scratch object and no initialising store.

   `ent` holds `(n + 63) >> 6` words; its extent is derived from `n`, as the
   entry stream's and the escape list's are, and the caller stages it.  The
   classifier reads 64 bytes per block unconditionally, so `b` must have
   `64 * ((n + 63) >> 6)` bytes readable (the padded tail is the caller's, as
   for the mask unit).  `xcarry` is the escape list's carry (`escape.h`): the
   unit reads it only when `arm & 2`, and writes it only then.

   Arm bits are the pipeline's: bit 1 selects the escape list, bit 0 selects
   the entry emitter (the caller's, not this unit's), bit 2 the UTF-8 stage's
   error arm.  Bits at and above 3 are reserved and ignored. */
#ifndef LEANLLVM_KERNEL_JSON_S1_BLOCKS_H
#define LEANLLVM_KERNEL_JSON_S1_BLOCKS_H

#include <stdint.h>

void leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n, uint64_t *ent,
                             uint32_t *xp, uint64_t *nxp, uint64_t *xcarry,
                             uint64_t arm);

#endif
