/* escape.h -- the escape-position list and the list-driven escape expander.

   Two stages of the measured SIMD JSON pipeline, each hoisted to its own
   entry point.  The list is stage 1's: for every byte inside a string that is
   either a control byte or the first backslash of a run, its document
   position.  The expander is stage 2's list-driven decoder: a string body, its
   document offset, and the document's position list become the decoded body.

   Neither entry point computes the per-document gate.  Whether a document gets
   a list at all is the measured density probe's decision
   (`kernel/json/measured/dens.h`), and it is an **arm selector**: it answers
   PLAIN for documents that do carry escapes (seven of the route's twenty-one
   rows do), so an absent list is not a claim that the document has no escape.
   The caller passes the arm it selected; this unit has one shape of list and
   states it once.

   ## `leanllvm_json_escape_list`

   One 64-byte block's escape positions are appended to the caller's stream.
   `bs`, `ctl` and `im` are the classifier's three words for that block, not
   bytes: lane `t` of each is document byte `64 * blk0 + t`, and `im` is the
   in-string mask.  The unit is the measured `xl_lanes` and `xl_emit` over
   them, so the masks come from the mask unit and are not recomputed here.

   The caller's obligations, each measured:

     - `bs`, `ctl` and `im` are the block's classifier words.  A caller that
       passes a different block's words gets that block's list, and nothing
       here can tell.
     - `carry[0]` is 1 when the previous block's last byte is a backslash and
       `carry[1]` is 1 when that backslash starts an escape; both are zero at
       the document's first block (`blk0 == 0`).  The unit updates them to this
       block's last byte and escape start, so a caller walking blocks in order
       threads the same pair through every call.  A range that starts inside a
       document without the carry it inherited is a different list, and the
       unit cannot recover it from one block.
     - `*xn` is the number of positions already in `xp`.  At least
       **`*xn + 64 + 8` entries** must be writable: one block cannot hold more
       than 64 positions, and the measured eight-entry batch writes its whole
       slot run past the true count, so the last up to eight slots are inside
       the buffer and outside the stream.  Only `*xn` entries are the stream;
       read the count and not the slots after it.
     - `*xn < 2^63`: the count is a cursor the unit adds to the stream base and
       sign-extends into an address, so a count with the high bit set leaves the
       range the address arithmetic is defined on.  A caller that starts each
       block's count at zero and advances it by at most 64 per block never
       approaches the bound.
     - `blk0 < 2^32 / 64`: the position base is `(uint32_t)(blk0 << 6)`, so a
       document at or above 2^32 bytes truncates.  This is the entry stream's
       width limit as well.

   The block is read from the caller's masks only: the unit does not read `b`.
   `*xn` is advanced by the number of real positions, and the slots the batch
   wrote past it are not part of the stream.

   ## `leanllvm_json_escape_expand`

   The measured `us_dec_x`, with its eight parameters and its return value.

   `b .. b+n-1` is the body; `pos0` is the document offset of `b[0]`; `xp` and
   `*xj` are the document's position list and the cursor into it.  The run is
   refused with `~0ULL` when an escape is malformed, and `*err` is then the
   body-relative offset of the escape.  On success the return is the number of
   bytes written at `dst`, `*xj` is advanced past the positions the body
   consumed, and `*err` is unchanged.

   The caller's obligations, each measured rather than conventional:

     - **`xp` is exactly this body's escape positions**, `*xn` entries in
       order, not merely a `uint32_t` array of that capacity.  The list-driven
       path has no behind-the-cursor guard (`usdec.h:880` computes `b - i`
       with no `b < i` test, unlike the scan-driven kernels at `:709`, `:723`,
       `:757`, `:771`, `:1094`), so a position inside an escape the previous
       one consumed underflows the run length and the copy faults.  A caller
       that built the list through `leanllvm_json_escape_list` has this by
       construction; a caller that truncated, filtered or reused another
       document's list does not.
     - `b + n .. b + n + 31` is **readable**.  `us_run`'s first load
       (`usdec.h:398`) is unconditional, and it is on every path, so the run
       copy loads 32 bytes at `p + i` for `i` up to `n`.
     - **`dst` needs 64 writable bytes past the decoded extent; the measured
       form writes at most 32.**  `us_run` stores one 32-byte vector
       unconditionally (`usdec.h:398`) and, with `US_W == 64`, a second at
       `dst + 32 .. dst + 63` when its arm takes it (`:399-410`).  The
       measured form is `US_RUN2=0` (`:78-79`), so the second store is taken
       only for a run longer than 32 bytes; the farthest write past the
       decoded extent is then 32 bytes, from the unconditional first store on
       a zero-length copy, and 31 for a non-empty run of at most 32.  This
       header asks for 64 because that is the whole extent the pinned function
       can write — the `US_RUN2=1` form stores the second vector
       unconditionally — so a caller is correct for every arm of the file it
       is the ABI for, and a caller reserving only the measured form's 32
       would be correct for this build and overrun if the switch were flipped.
       The vendored comment at `usdec.h:390-392`, "up to 31 bytes past the
       run", is accurate for a non-empty run in the measured form and
       understates the empty copy (32) and the unselected form (63).
     - `*xj <= nxp`, `pos0 + n` does not wrap, and `dst` does not overlap
       `b` or `xp`.  The unit copies runs with vector loads and stores, so an
       overlapping destination changes both operands; nothing here claims what
       happens when they overlap.

   See README.md for the unit's provenance, its limits and its identity arms. */
#ifndef LEANLLVM_KERNEL_JSON_ESCAPE_H
#define LEANLLVM_KERNEL_JSON_ESCAPE_H

#include <stdint.h>

void leanllvm_json_escape_list(uint64_t bs, uint64_t ctl, uint64_t im,
                               uint64_t blk0, uint32_t *xp,
                               uint64_t *xn, uint64_t *carry);

uint64_t leanllvm_json_escape_expand(const uint8_t *b, uint64_t n, uint8_t *dst,
                                     uint64_t *err, const uint32_t *xp,
                                     uint64_t *xj, uint64_t nxp, uint64_t pos0);

#endif
