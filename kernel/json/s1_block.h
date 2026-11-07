/* s1_block.h -- the stage-1 classification mask unit's one public entry point.

   Sixty-four bytes at `p` in, six 64-bit mask words at `out`, and the carry
   the next block enters with, in place at `carry`.  The words are, in struct
   order, the unescaped-quote, structural (delimiter), in-string, whitespace,
   backslash and control masks, lane 0 of each being byte 0 of the block.  The
   escaped-quote mask is not a seventh word: it is `quote_raw & ~quote`, which
   is what the specification derives rather than a stored value.

   Byte offsets are fixed by these two definitions: the carry at +0/+8/+16 and
   the output at +0/+8/+16/+24/+32/+40.  The unit reads 64 bytes
   unconditionally, so the caller stages a block at an address where 64 bytes
   are readable; it makes no alignment demand and no aliasing claim.  See
   README.md for the unit's provenance and limits. */
#ifndef LEANLLVM_KERNEL_JSON_S1_BLOCK_H
#define LEANLLVM_KERNEL_JSON_S1_BLOCK_H

#include <stdint.h>

/* The carry the previous block leaves: whether it ended inside a run of
   backslashes (`esc_open`), the parity of that run (`esc_ppar`), and the
   in-string word the prefix xor starts from (`im_carry`, 0 or all-ones). */
typedef struct { uint64_t esc_open, esc_ppar, im_carry; } s1_carry;

/* The block's six mask words. */
typedef struct { uint64_t quote, delim, in_string, ws, backslash, ctl; } s1_masks;

void leanllvm_json_s1_masks(const uint8_t *p, s1_carry *carry, s1_masks *out);

#endif
