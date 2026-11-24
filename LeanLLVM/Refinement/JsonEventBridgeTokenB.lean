/-
`hT`: the token decoder agrees with the tape's own decoder on every tape the
tape decoder accepts.

`TokenDecoderAgrees` (`JsonEventBridge`) is
`parseValueT t = decodeTape t`.  The agreement itself is proved in
`JsonEventBridgeDecode`: it relates a successful `decodeValue` to the token
parse's value and remainder, and the two tape-decoder tails to the token side's
element and member parses.  This module applies those facts to the tape the
reference parser produces: `decodeTape_correct` fixes the decoded value and the
exhaustion of the token list, and the shared facts at the token list's own
length plus one turn that into the token parse's result.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonEventBridge
import LeanLLVM.Refinement.JsonEventBridgeDecode

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- **`hT`: the token decoder agrees with the tape's decoder.**  Every tape the
reference parser accepts is read identically by `parseValueT` and `decodeTape`.
The tape decoder's success fixes the value and consumes the token list; the
shared facts of `JsonEventBridgeDecode` give the token parse that same value and
remainder at the fuel the tape's token count supplies. -/
theorem tokenDecoderAgrees_of_parse {bs : List UInt8} {t : Tape}
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t) :
    TokenDecoderAgrees t := by
  obtain ⟨v, hdec, hin, -⟩ :=
    decodeTape_correct Limits.default (ByteString.literal bs) t hparse
  rcases t with ⟨input, toks⟩
  simp only at hin
  subst hin
  have hdecv : decodeTape ⟨ByteString.literal bs, toks⟩ = some v := hdec
  unfold TokenDecoderAgrees parseValueT
  dsimp only
  rw [hdecv]
  unfold decodeTape at hdec
  split at hdec
  · rename_i d hdv
    split at hdec
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨hrest, hcur⟩ := hcond
      simp only [decide_eq_true_eq] at hrest
      injection hdec with hval
      -- the shared facts at the token list's own length plus one
      obtain ⟨r, hr⟩ := parseValueTB_value_at hdv
      obtain ⟨w, hw⟩ := parseValueTB_remainder_at hdv
      have hw2 : r = d.rest := congrArg Prod.snd (Option.some.inj (hr ▸ hw))
      rw [hw2] at hr
      rw [hrest] at hr
      rw [hr]
      simp only [hval]
    · cases hdec
  · cases hdec

end LeanLLVM.Refinement
