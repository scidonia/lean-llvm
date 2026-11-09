/* emit24.c -- the gated index emitter with the token kind folded into the
   entry's spare bits.  Scratch experiment.

   scan_cand_gated (v16e.ll) writes a bare u32 position per candidate.  A
   position below 2^27 leaves five high bits free; this variant fills them with
   the walk's own K_* kind, read from the input byte at the emitted position.
   The walk then dispatches without loading the byte or the kind table.  The
   cost is one byte load and one table lookup per emitted entry, paid in the
   emitter's already load-bound loop, against two loads removed per structural
   token in the walk.

   The block shape follows scan_cand_gated: for a block with at least `thr`
   candidates, eight slots are written unconditionally (a cttz of zero yields
   base+64, a slot that is written but not counted) and the remainder is
   drained by a loop; below the threshold the candidates are drained one at a
   time.  The extra seven slots are garbage beyond the returned count, exactly
   as in the reference emitter, and the caller's array has the slack. */
#ifndef EMIT24_H
#define EMIT24_H

#define E24_SHIFT 5

static const uint8_t E24_KIND[256] = {
    [','] = 20, [':'] = 21,
    ['{'] = 1, ['}'] = 2, ['['] = 3, [']'] = 4,
    ['"'] = 6
};

static inline __attribute__((always_inline)) uint32_t
e24_entry(const uint8_t *buf, uint64_t pos) {
    return ((uint32_t)pos << E24_SHIFT) | (uint32_t)E24_KIND[buf[pos]];
}

uint64_t scan_cand_kind(const uint8_t *buf, const uint64_t *cand, uint32_t *idx,
                        uint64_t nblocks, uint64_t thr) {
    uint64_t k = 0;
    for (uint64_t b = 0; b < nblocks; b++) {
        uint64_t c = cand[b];
        if (!c) continue;
        uint64_t base = b << 6;
        uint64_t n = (uint64_t)__builtin_popcountll(c);
        if (n >= thr) {
            uint32_t *slot = idx + k;
            uint64_t cc = c;
            for (int t = 0; t < 8; t++) {
                slot[t] = e24_entry(buf, base + (uint64_t)__builtin_ctzll(cc));
                cc &= cc - 1;
            }
            k += n;
            if (n > 8) {
                uint32_t *e = slot + 8;
                while (cc) {
                    *e++ = e24_entry(buf, base + (uint64_t)__builtin_ctzll(cc));
                    cc &= cc - 1;
                }
            }
        } else {
            while (c) {
                idx[k++] = e24_entry(buf, base + (uint64_t)__builtin_ctzll(c));
                c &= c - 1;
            }
        }
    }
    return k;
}

#endif
