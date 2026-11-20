/* s1_blocks.h -- the contracted stage-1 block unit's one public entry point.

   The document in, one 64-bit entry word per 64-byte block at `ent`, and the
   escape positions appended to `xp`/`*nxp` when the gate selects that arm.  The
   block words are the stage-1 composition (`JsonScanSpec.entryMask64`): the
   unescaped quote, the structural byte outside a string, and the run start
   carried from the previous block, clamped past the document's end.  The masks
   the composition reads, both classifier carries, the entry word and the UTF-8
   stage's accumulator stay in registers, so this unit has no caller-staged
   scratch object and no initialising store.  The composition's scalar word is
   the fast pass's `neither & ~quote & ~in_string`; the classifier's whitespace
   word is not computed, and the control-byte word is measured only on the
   escape list's arm, which is the only reader it has.  The final partial block
   is peeled into its own body, so the `lim < 64` clamp is not in the
   full-block loop.

   The same loop runs the UTF-8 stage's Keiser-Lemire DFA over the block's own
   vectors and the three bytes before the block, accumulating the stage's error
   vector and the previous block's ASCII answer.  The three bytes at `b - 3`,
   `b - 2` and `b - 1` must be readable and zero, as `utf8.h` requires: the
   caller stages them.  `ent` holds `(n + 63) >> 6` words; its extent is derived
   from `n`, as the entry stream's and the escape list's are, and the caller
   stages it.  The block loop reads 64 bytes per block unconditionally, so `b`
   must have `64 * ((n + 63) >> 6)` bytes readable (the padded tail is the
   caller's, as for the mask unit).  `xcarry` is the escape list's carry
   (`escape.h`): the unit reads it only when `arm & 2`, and writes it only then.

   The return word:

     bit 0   the ASCII probe, as in the unit's first body: 1 exactly when every
             document byte is below 0x80 (an empty document is vacuously ASCII);
     bit 1   the UTF-8 stage's error word: 1 exactly when the staged window
             (`b - 3 .. b`, the document, and the zero padding to the 64-byte
             boundary) is *not* a valid prefix (`utf8WinPrefix`), 0 when it is;
     bit 2+  zero.

   `r & 1` is the ASCII class and `r & 2` the UTF-8 verdict, so the pipeline
   reads the verdict here and does not call `leanllvm_json_utf8` after this
   unit.  The two bits are independent in the encoding but not in fact: an
   all-ASCII document is a valid prefix, so `r & 1 = 1` implies `r & 2 = 0`.

   Arm bits are the pipeline's.  Bit 1 selects the escape list and bit 2 selects
   the UTF-8 gate (`0` gated, `1` ungated), the same sense as `utf8.h`'s
   `ungated` argument: ungated runs the DFA on every block, gated skips an
   all-ASCII block whose predecessor is all-ASCII.  Bit 0 (the entry emitter)
   belongs to the caller's stage and is ignored here.  Bits at and above 3 are
   reserved and ignored. */
#ifndef LEANLLVM_KERNEL_JSON_S1_BLOCKS_H
#define LEANLLVM_KERNEL_JSON_S1_BLOCKS_H

#include <stdint.h>

uint64_t leanllvm_json_s1_blocks(const uint8_t *b, uint64_t n, uint64_t *ent,
                                 uint32_t *xp, uint64_t *nxp, uint64_t *xcarry,
                                 uint64_t arm);

#endif
