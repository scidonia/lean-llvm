/* entry.h -- the entry unit's three public entry points.

   A block's `ent` word becomes positions in the caller's 32-bit stream.  The
   unit takes `nblk` mask words at `ent`, the index `blk0` of the first of them
   in the document, the caller's buffer at `out`, and the cursor `k` the stream
   has reached; it returns the cursor after the last word it appended.  Lane 0
   of `ent[0]` is byte 0 of block `blk0`, so lane `t` of `ent[i]` is byte
   `64 * (blk0 + i) + t` of the document.

   `leanllvm_json_entry_pos8` and `leanllvm_json_entry_b8` are two emitters of
   the same stream -- the arithmetic below and `entry.c`'s header explain how
   they differ -- and either one's output is the other's.  Neither allocates,
   neither reads or writes anything but the caller's three objects, and neither
   selects a kernel: which one a document gets is the caller's decision.

   The contract the two share:

     - the `k' - k` words written at `out[k .. k')` are the positions of the
       set lanes of `ent[0]`, `ent[1]`, ... in that order, each as
       `64 * (blk0 + i) + lane` truncated to 32 bits;
     - `ent` is read and not written;
     - bytes of `out` outside `[k, k' + 8)` are not written.  POS8 writes one
       eight-lane group per mask byte whatever the byte holds, so its last
       written lane in a block is `k' + 7` when the block's final mask byte is
       empty; B8 writes exactly its count above eight lanes and eight slots
       below, so its last written lane is `k' + 6`.  The lanes between `k'` and
       that last one hold whatever the emitter's own stores left there and are
       not part of the stream: give the buffer eight words of slack past the
       largest count the input can reach, and read only the `k'` words.

   The buffer's slack is the caller's, and so is the 32-bit width: the base is
   `(uint32_t)((blk0 + i) << 6)`, so a document at or above 2^32 bytes
   truncates.  See README.md for the unit's provenance and limits. */
#ifndef LEANLLVM_KERNEL_JSON_ENTRY_H
#define LEANLLVM_KERNEL_JSON_ENTRY_H

#include <stdint.h>

uint64_t leanllvm_json_entry_pos8(const uint64_t *ent, uint64_t blk0,
                                  uint64_t nblk, uint32_t *out, uint64_t k);

uint64_t leanllvm_json_entry_b8(const uint64_t *ent, uint64_t blk0,
                                uint64_t nblk, uint32_t *out, uint64_t k);

/* Fill the caller's 256 x 8 `uint32_t` (8 KiB) with the unit's own table,
   initialising it first if the process has not.  Row `m` holds the offsets of
   `m`'s set bits in order, padded to eight entries with zeros. */
void leanllvm_json_entry_table(uint32_t *dst);

#endif
