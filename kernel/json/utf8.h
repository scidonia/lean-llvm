/* utf8.h -- the UTF-8 validity unit's one entry point.

   The unit is the measured pipeline's stage-1 UTF-8 validity stage: the
   Keiser-Lemire `pshufb` table DFA over one 64-byte block, run for every block
   of the document, and the document-end rule applied after the loop.  `b` is
   the document's first byte, `n` its length in bytes, and `ungated` selects
   which of the stage's two block paths a block takes; the returned word is the
   stage's error word, so the document is accepted exactly when the return is
   zero.

   The verdict does not depend on `ungated`: the two paths differ only in
   whether an all-ASCII block whose predecessor is all-ASCII runs the DFA, and
   skipping that run cannot change the accumulated word.  Which path a document
   gets is the caller's decision, as is the document-level rule at the tail.

   The caller stages the document; the unit does not.  Four obligations, each
   measured rather than conventional:

     - `3 <= b`, and the three bytes `b-3 .. b-1` read as zero -- the document's
       start.  The DFA's state crosses the buffer start: with `F0 90 80` staged
       there, a document beginning `80` flips from reject to accept.
     - `n` is the document's length, and `b .. b+n-1` is the document.
     - `b+n .. b+64*ceil(n/64)-1` is readable and zero.  Those bytes are inside
       the scanned window and the verdict depends on them; a non-zero padding
       byte can suppress a rejection.
     - `n < 2^63`.  The block count is `(n + 63) / 64`, computed in a 64-bit
       word that wraps above that bound, and `n` is itself an index in the
       tail's read of `b[n-1]`.

   The block count is derived from `n` alone -- the block sequence is the
   document's first `n` bytes in 64-byte blocks -- so `n` is the length of the
   byte string the body scans, and a caller that also carries a length has one
   value and not two.

   One *consequence* rather than an obligation, stated because a caller will
   ask: with `n % 64 != 0` the zero padding supplies the position after the last
   document byte, so a truncated final character is rejected, while with
   `n % 64 = 0` that position does not exist and a truncated `C2-F4` tail is
   accepted (`C0`, `C1` and `F5-FF` are still rejected by the tail test).  The
   document-level rule for the truncation is finalisation's, not this stage's,
   and applying it is the caller's business.

   See README.md for the unit's provenance, its limits and its identity arms. */
#ifndef LEANLLVM_KERNEL_JSON_UTF8_H
#define LEANLLVM_KERNEL_JSON_UTF8_H

#include <stdint.h>

uint64_t leanllvm_json_utf8(const uint8_t *b, uint64_t n, int ungated);

#endif
