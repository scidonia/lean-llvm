/* The candidate's eight-lane fold with the boxed-`Nat` counter made static.
 *
 * `probes/install/Candidate.lean` writes the seam as
 *
 *     go i acc = if i < 8 then
 *                  let shift := 8 * i
 *                  let b := (x >>> shift) &&& 0xFF
 *                  go (i + 1) (if b = 0x2C then acc ||| (0x80 <<< shift) else acc)
 *                else acc
 *     commaMask8 x = go 0 0
 *
 * with `i : Nat`.  The emitted IR of that loop is outside the fragment
 * `LeanLLVM.Semantics` models: the counter is a heap `lean_object*`, the
 * comparison and the increment are calls into the `Nat` runtime
 * (`lean_nat_dec_lt`, `lean_nat_mul`, `lean_nat_add`, `lean_unsigned_to_nat`,
 * `lean_dec`), and the loop is closed by `phi` nodes over the boxed counter.
 * The captured emission is kept in `candidate.raw.ll`.
 *
 * This file keeps the fold and writes the recursion out lane by lane, with a
 * literal shift per lane, so no induction variable and no `Nat` remain.  The
 * compare is written against `0` on `x ^ 0x2C..` rather than against `0x2C` on
 * `x`, which is the form `LeanLLVM.Vellum.CommaMask.byteLoop` uses; the two
 * agree because `0x2C` fits in a byte, and `byteLoop_eq_spec` connects that
 * form to the lane specification.
 */
#include <stdint.h>

#define LANE(i)                                                         \
  do {                                                                  \
    const unsigned shift = 8u * (i);                                    \
    const uint64_t b = (m >> shift) & 0xFFu;                            \
    acc = (b == 0) ? (acc | (0x80ULL << shift)) : acc;                  \
  } while (0)

uint64_t leanllvm_comma_mask8(uint64_t x) {
  const uint64_t m = x ^ 0x2C2C2C2C2C2C2C2CULL;
  uint64_t acc = 0;
  LANE(0);
  LANE(1);
  LANE(2);
  LANE(3);
  LANE(4);
  LANE(5);
  LANE(6);
  LANE(7);
  return acc;
}
