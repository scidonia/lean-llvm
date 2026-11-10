/* stage2.h -- the stage-2 unit's one entry point.

   `kernel/json/stage2.c` is the walk `pipeline.h` hands the entry stream to:
   one pass over the entry positions, a switch on the byte at each position, a
   scope stack of container type and state per depth, the string bodies decoded
   from the stage-1 escape list, and the value/event stream and the first error
   offset written into the caller's buffers.  The measured build inlines the
   walk into the pipeline's translation unit; this header is the staged form's
   ABI, because an inlined parser admits no compositional proof.

   ## The caller stages every buffer

   No modelled run allocates.  The arena's base is `dst` with capacity `dstcap`
   and cursor `*ndst`, and the event stream's base is `ev` with capacity `evcap`
   and cursor `*nev`; both are the caller's and both append, so a record's arena
   offset is an offset into `dst` and every cursor movement is reported back.
   The measured walk grows its two buffers by reallocation (`s2port.h`'s
   `ZOut`, whose `z_arena_reserve` and the event stream's `out_reserve` are the
   growth); here that growth is the caller's promise instead, stated in the
   unit's record as `pre`: `dst` carries `dstcap - *ndst` writable bytes from
   the cursor and `ev` carries `evcap - *nev`.  A reserve that would exceed
   them traps rather than overrunning: a caller that under-reserves is outside
   the unit's domain, and the refusal channel below is a *parse* refusal, never
   a capacity one.

   ## A number token has no length bound

   The walk's number conversion is the tiered path, and its third tier is this
   unit's own `to_double`: it reads at most 768 significant digits into a fixed
   buffer, records in one sticky bit whether any digit past them is nonzero,
   and rounds once from the exact value of the retained digits and that bit.
   It allocates nothing, so the token's length is the document's and not a
   resource: no token is truncated, refused, or made to allocate, and the
   domain has no token-length edge.

   The buffer bounds the *decimal window*, not the token.  The digits past it
   change the result only through the sticky bit, and 768 is the number that
   makes that exact: every binary64 value and every midpoint of two adjacent
   ones needs at most 768 significant decimal digits (`log10((2^54-1)*5^1075)
   = 767.65`), so every boundary a rounding decision is made against is
   represented inside the window and the sticky bit only has to say whether the
   value is strictly above the retained decimal.

   ## The undefined symbols the object leaves

   For the unit's own object these are the C library's `memcpy`, `memset`, the
   fortified copies and the stack protector.  No project symbol is undefined,
   and no allocator, process terminator or library conversion appears at all:
   the number conversion above allocates nothing and calls nothing.  The
   identity arm checks the project half;
   a name outside this list appearing there is a widening of the domain and
   must be recorded, not absorbed.

   The decoded body of an escaped string is written at the arena cursor with
   the decoder's own slack (`US_SLACK`, 64 bytes at the measured `US_EMIT4=1`)
   past the decoded extent, so the capacity promise covers that slack as well
   as the bytes the record names.

   ## The ABI

   The document is `b .. b+n-1`.  `ep` with count `nep` is the entry stream,
   in document order: quote characters, the structural bytes and the first
   byte of every scalar.  `xp` with count `nxp` is the stage-1 escape-position
   list; the walk threads its own cursor internally, so a document with no
   escapes passes `nxp = 0`.  `*err` is the first error offset when the run
   refuses, and is not written when it accepts.

   The run validates the grammar, validates each string body and materialises
   the event stream: those are the measured walk's `S2_VAL | S2_STR | S2_EV`
   flags, fixed here rather than taken as a parameter, because the pipeline's
   call site is what selects them and the record's post is stated at them.

   The event stream is the measured encoding: one byte of tag for `{`, `}`,
   `[`, `]`, `true`, `false` and `null`; a tag byte followed by the value's
   eight IEEE bytes for a number (`T_NUM`); and, for a key or a string, a tag
   byte, the decoded length as four little-endian bytes, then eight bytes whose
   top bit marks a span into the input (offset in the low bits) and whose clear
   bit marks an offset into the arena (`s2port.h`'s record at the `T_KEY` /
   `T_STR` arm).

   The return is the verdict, `1` for acceptance and `0` for refusal.  The
   refusals are the walk's own: the structural rules, the number and literal
   rules, the string-body rules, and the end-of-stream rules (an unclosed
   container, no value, an unterminated string), each with the first offset
   the measured walk reports.

   Whether the accept/refuse verdict, the event stream and the first error
   offset are the reference parser's is the pipeline's specification, not this
   header's claim. */
#ifndef LEANLLVM_KERNEL_JSON_STAGE2_H
#define LEANLLVM_KERNEL_JSON_STAGE2_H

#include <stdint.h>

uint64_t leanllvm_json_stage2(const uint8_t *b, uint64_t n,
                              const uint32_t *ep, uint64_t nep,
                              const uint32_t *xp, uint64_t nxp,
                              uint8_t *dst, uint64_t dstcap, uint64_t *ndst,
                              uint8_t *ev, uint64_t evcap, uint64_t *nev,
                              uint64_t *err);

#endif
