/* entry.h -- the entry unit's four public entry points.

   A block's `ent` word becomes positions in the caller's 32-bit stream.  The
   unit takes `nblk` mask words at `ent`, the index `blk0` of the first of them
   in the document, the caller's buffer at `out`, and the cursor `k` the stream
   has reached; it returns the cursor after the last word it appended.  Lane 0
   of `ent[0]` is byte 0 of block `blk0`, so lane `t` of `ent[i]` is byte
   `64 * (blk0 + i) + t` of the document.

   `leanllvm_json_entry_pos8`, `leanllvm_json_entry_b8` and
   `leanllvm_json_entry_b3` are three emitters of the same stream -- the
   arithmetic below and `entry.c`'s header explain how they differ -- and any
   one's output is another's.  None allocates, none reads or writes anything
   but the caller's three objects, and none selects a kernel: which one a
   document gets is the caller's decision.

   The contract the three share:

     - the `k' - k` words written at `out[k .. k')` are the positions of the
       set lanes of `ent[0]`, `ent[1]`, ... in that order, each as
       `64 * (blk0 + i) + lane` truncated to 32 bits;
     - `ent` is read and not written;
     - bytes of `out` outside `[k, k' + 8)` are not written.  POS8 writes one
       eight-lane group per mask byte whatever the byte holds, so its last
       written lane in a block is `k' + 7` when the block's final mask byte is
       empty; B8 writes exactly its count above eight lanes and eight slots
       below, so its last written lane is `k' + 6`; B3 writes three slots, then
       four more above three lanes, and exactly its count above seven, so its
       last written lane is `k' + 2` (a four-lane block is the worst case: its
       second group reaches `k + 6 = k' + 2`).  The lanes between `k'` and that
       last one hold whatever the emitter's own stores left there and are not
       part of the stream: give the buffer eight words of slack past the
       largest count the input can reach, and read only the `k'` words.

   The buffer's slack is the caller's, and so is the 32-bit width: the base is
   `(uint32_t)((blk0 + i) << 6)`, so a document at or above 2^32 bytes
   truncates.

   POS8 reads the unit's own static table, and that table is not part of this
   ABI: `leanllvm_json_entry_table` fills it and nothing else does.  The pos8
   wrapper checks the initialiser's ready word on every call, so a pos8 call
   made before `leanllvm_json_entry_table` has run traps rather than emitting
   positions from the zero-initialised table, which would be a well-formed
   stream of wrong positions.  B8 and B3 read no table and carry no such
   obligation.  A caller that selects the emitter per document must
   initialise before its first pos8 call; `pipeline.h`'s arm bit 0 states the
   same obligation at the pipeline's boundary.  See README.md for the unit's
   provenance and limits. */
#ifndef LEANLLVM_KERNEL_JSON_ENTRY_H
#define LEANLLVM_KERNEL_JSON_ENTRY_H

#include <stdint.h>

uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                  uint64_t nblk, uint32_t *out, uint64_t k);

uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                uint64_t nblk, uint32_t *out, uint64_t k);

/* Three slots, then four, then a scalar tail: the sparse-document emitter.
   Its output stream is the same as `…_pos8`'s and `…_b8`'s. */
uint64_t leanllvm_json_entry_b3(const uint64_t *ent, uint64_t blk0,
                                uint64_t nblk, uint32_t *out, uint64_t k);

/* Fill the caller's 256 x 8 `uint32_t` (8 KiB) with the unit's own table,
   initialising it first if the process has not.  Row `m` holds the offsets of
   `m`'s set bits in order, padded to eight entries with zeros.  This is the
   only function that fills the table the POS8 emitter reads. */
void leanllvm_json_entry_table(uint32_t *dst);

#endif
