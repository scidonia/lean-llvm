/* ent_oracle.c -- the measured `ent` word's statements, in one text.

   No measured function computes the `ent` word on its own.  The block loop
   computes it inline in three places -- `s1f_ent_probe`
   (`measured/s1fuse.h:519-536`), `s1f_build` (`:873-894`) and `s1f_build2`
   (`:1706-1722`) -- so the word has no body an identity arm could lift and
   compare the way the mask and the entry units' bodies are compared.  What it
   has is text, and this file is that text: the statements of the third site,
   copied into one function.

   Three things are applied to the copy, and nothing else:

     - the `S1F_CTAB` arm is resolved to the table path, the measured build's
       value (`s1fuse.h:384-386`), so `uint64_t ws = wsm;` stands where the
       conditional pair stood;
     - the braces that group the `S1F_GRAIN == 0` arm's statements are left
       out, so the statements sit at one scope and `S` can be returned beside
       the words it produces.  They are structure, not statements:
       `identity/ent-identity.sh` drops brace-only lines from both sides;
     - the `#if S1F_GRAIN == 0` guard is kept, because it is the measured text's
       own statement of which granularity this word is.  An undefined
       `S1F_GRAIN` evaluates to 0 in `#if`, so the file needs no build flag for
       it, and the build passes none.

   `identity/ent-identity.sh` diffs these tokens against each of the three
   vendored sites, so the three inline copies are shown to be one text and this
   file is shown to be that text.

   The row interface is `ent_oracle_row`: a block's four masks, the previous
   block's top-lane bit and the document end in, the scalar word `S`, the entry
   word before the tail mask and the tail-masked word out.  That is what the
   specification's `specScalar64`, `entryMask64` and its tail application are
   compared against, row by row.

   The four words are the caller's: this file does not compute a mask, and it
   claims nothing about whether they are the specification's.  That identity is
   the mask unit's (`s1_masks_refines`), and the comparison here is of the
   composition built on top of it. */
#include <stdint.h>

/* The carry field these statements read and write: the previous block's
   top-lane bit of `S`.  The measured carry type keeps it after the three fields
   the mask unit owns, and the copied statements address it by name. */
typedef struct { uint64_t prevS; } ent_carry;

/* One block's three words: the scalar-run word, the entry word before the tail
   mask, and the entry word the tail mask leaves. */
typedef struct { uint64_t scalar, ent, tailed; } ent_row;

ent_row ent_oracle_row(uint64_t qm, uint64_t sm, uint64_t im, uint64_t wsm,
                       ent_carry *state, uint64_t n, uint64_t bi) {
    ent_carry st = *state;
    ent_row row;

    uint64_t ent = qm | (sm & ~im);
#if S1F_GRAIN == 0
    uint64_t ws = wsm;
    uint64_t S = ~(im | qm | sm | ws);
    uint64_t stm = S & ~((S << 1) | st.prevS);
    st.prevS = S >> 63;
    ent |= stm;
#endif
    row.scalar = S;
    row.ent = ent;
    uint64_t lim = n - (bi << 6);
    if (lim < 64) ent &= (1ULL << lim) - 1ULL;
    row.tailed = ent;

    *state = st;
    return row;
}
