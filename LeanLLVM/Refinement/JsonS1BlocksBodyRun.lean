/-
The body's remaining steps: the table region's words, the neither word, the
carry-less product, and the entry chain's arithmetic.

The table region and the quote word are the mask unit's instructions at the same
register spellings, so their steps are the mask unit's, moved to this unit's call
environment by `evalInstr_blocks_of_masks`.  The steps written here are the ones
whose destination or operand names the block unit renames (`%or.i99` for the raw
quote word, `%29` for the product), and the entry chain, which the mask unit
computes through the carry slot and the output slot rather than in registers.
-/
import LeanLLVM.Refinement.JsonS1BlocksIdentities

namespace LeanLLVM.Refinement.JsonS1BlocksSteps

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.Pclmul (clmul)
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonScanSpec

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ### The body's tail -/

/-- The body's instructions after its six leading `phi`s. -/
def bodyTail : List Instr := bodyInstrs.drop 6

theorem phiTail_split : bodyInstrs = phiInstrs ++ bodyTail := rfl

theorem neitherLanes_length (k : Ctx) : (neitherLanes k).length = 64 := by
  simp [neitherLanes, andWordLanes_length, andWordLanesHi_length]

/-! ### The neither word -/

/-- `%or23.i = bitcast <64 x i1> %28 to i64`: the neither word. -/
theorem b_neither (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%28" = some (.vec 64 1 (neitherLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s) (.bitcastMask "%or23.i" 64 (.reg "%28")) =
      some (stateAt (("%or23.i", .int 64 (neitherW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_bitcastMask (hv := by simp only [stateAt, evalOperand, h])
    (neitherLanes_length k)]
  rfl

/-! ### The carry-less product -/

/-- `%29 = call @llvm.x86.pclmulqdq(%vecinit1.i.i.i, <2 x i64> <-1, 0>, i8 0)`. -/
theorem b_pclmul29 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%vecinit1.i.i.i" = some (.vec 2 64 (vecInitLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.call "%29" (.vec 2 (.int 64)) "llvm.x86.pclmulqdq"
          [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
           (.vec 2 (.int 64), JsonS1BlocksIR.lanesOf 64 [-1, 0]), (.int 8, JsonS1BlocksIR.lit 8 0)]) =
      some (stateAt (("%29", .vec 2 64 (pclmulLanes k)) :: env) s) := by
  have hneg : (BitVec.ofInt 64 (-1) : BitVec 64) = BitVec.allOnes 64 := by decide
  have ha : evalOperands (stateAt env s)
      [(.vec 2 (.int 64), .reg "%vecinit1.i.i.i"),
       (.vec 2 (.int 64), JsonS1BlocksIR.lanesOf 64 [-1, 0]), (.int 8, JsonS1BlocksIR.lit 8 0)]
      = some [.vec 2 64 (vecInitLanes k),
          .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0] := by
    rw [evalOperands_cons (v := .vec 2 64 (vecInitLanes k))
      (vs := [.vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0], .int 8 0])
      (by simp only [stateAt, evalOperand, h])
      (evalOperands_cons (v := .vec 2 64 [BitVec.ofInt 64 (-1), BitVec.ofInt 64 0])
        (vs := [.int 8 0])
        (by simp [stateAt, evalOperand, JsonS1BlocksIR.lanesOf, Const.toValue]) rfl)]
  rw [JsonS1MasksIR.evalInstr_call ha
    (s1BlocksCalls_pclmulqdq (andQuoteW k) 0 (BitVec.ofInt 64 (-1)) (BitVec.ofInt 64 0)
      s.mem s.next)]
  simp only [stateAt, State.bind, pclmulLanes, vecInitLanes, hneg]

/-- `%vecext.i.i.i = extractelement <2 x i64> %29, i64 0`. -/
theorem b_vecext29 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%29" = some (.vec 2 64 (pclmulLanes k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.extractelement "%vecext.i.i.i" 2 64 (.reg "%29") (JsonS1BlocksIR.lit 64 0)) =
      some (stateAt (("%vecext.i.i.i", .int 64 (vecextW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_extractelement
    (vv := .vec 2 64 (pclmulLanes k)) (lanes := pclmulLanes k)
    (x := clmul (andQuoteW k) (BitVec.allOnes 64)) (wi := 64) (k := (BitVec.ofInt 64 0))
    (hv := by simp only [stateAt, evalOperand, h])
    (hl := vecLanes_self (by simp [pclmulLanes]))
    (hi := by simp only [stateAt, evalOperand, JsonS1BlocksIR.lit, Const.toValue])
    (hx := by simp [pclmulLanes, vecextW])]
  simp only [stateAt, State.bind, vecextW]

/-! ### The in-string word and the carry

The body takes the incoming in-string word from its register carry, so the two
steps are the mask unit's chain at `%st.sroa.11.0175` instead of `%35`. -/

/-- `%xor.i = xor i64 %vecext.i.i.i, %st.sroa.11.0175`. -/
theorem b_xorIn (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%vecext.i.i.i" = some (.int 64 (vecextW k)))
    (h2 : lookupName env "%st.sroa.11.0175" = some (.int 64 (seedW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%xor.i" .xor 64 (.reg "%vecext.i.i.i") (.reg "%st.sroa.11.0175")) =
      some (stateAt (("%xor.i", .int 64 (inStringWord k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := vecextW k) (y := seedW k)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, h2])
    (r := (inStringWord k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, inStringWord])]
  simp only [stateAt, State.bind, ofNat_toNat]

/-- `%shr.i = ashr i64 %xor.i, 63`. -/
theorem b_imSign (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor.i" = some (.int 64 (inStringWord k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shr.i" .ashr 64 (.reg "%xor.i") (JsonS1BlocksIR.lit 64 63)) =
      some (stateAt (("%shr.i", .int 64 (imSignW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := inStringWord k) (y := (BitVec.ofInt 64 63))
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, JsonS1BlocksIR.lit, Const.toValue])
    (r := (imSignW k).toNat) (hr := by
      show (some ((BitVec.ofNat 64 (inStringWord k).toNat).sshiftRight
        (BitVec.ofNat 64 (BitVec.ofInt 64 63).toNat).toNat)).map BitVec.toNat
        = some (imSignW k).toNat
      rw [show (BitVec.ofNat 64 (BitVec.ofInt 64 63).toNat) = (63 : BitVec 64) from by decide,
        show (63 : BitVec 64).toNat = 63 from by decide,
        show (BitVec.ofNat 64 (inStringWord k).toNat) = inStringWord k from
          ofNat_toNat (inStringWord k)]
      unfold imSignW
      rw [bv_toNat]
      rfl)]
  simp only [stateAt, State.bind, ofNat_toNat]

/-! ### The entry word's chain -/

/-- `%not7 = xor i64 %xor.i, -1`. -/
theorem b_not7 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%xor.i" = some (.int 64 (inStringWord k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%not7" .xor 64 (.reg "%xor.i") (JsonS1BlocksIR.lit 64 (-1))) =
      some (stateAt (("%not7", .int 64 (notXorW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := inStringWord k) (y := (BitVec.ofInt 64 (-1)))
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, JsonS1BlocksIR.lit, Const.toValue])
    (r := (notXorW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, notXorW,
        show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])]
  simp only [stateAt, State.bind, ofNat_toNat]

/-- `%30 = or i64 %and.i, %xor.i`. -/
theorem b_or30 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and.i" = some (.int 64 (andQuoteW k)))
    (h2 : lookupName env "%xor.i" = some (.int 64 (inStringWord k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%30" .or 64 (.reg "%and.i") (.reg "%xor.i")) =
      some (stateAt (("%30", .int 64 (orQImW k)) :: env) s) :=
  step_binop_v _ _ _ "%30" .or "%and.i" "%xor.i" (andQuoteW k) (inStringWord k)
    (orQImW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, orQImW])

/-- `%31 = xor i64 %30, -1`. -/
theorem b_not31 (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%30" = some (.int 64 (orQImW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%31" .xor 64 (.reg "%30") (JsonS1BlocksIR.lit 64 (-1))) =
      some (stateAt (("%31", .int 64 (notQImW k)) :: env) s) :=
  step_binop_imm _ _ _ "%31" .xor "%30" (BitVec.ofInt 64 (-1)) (orQImW k) (notQImW k) h (by
    simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, notQImW,
      show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])

/-- `%and8 = and i64 %or23.i, %31`: the scalar word. -/
theorem b_scalar (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or23.i" = some (.int 64 (neitherW k)))
    (h2 : lookupName env "%31" = some (.int 64 (notQImW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and8" .and 64 (.reg "%or23.i") (.reg "%31")) =
      some (stateAt (("%and8", .int 64 (scalarW k)) :: env) s) :=
  step_binop_v _ _ _ "%and8" .and "%or23.i" "%31" (neitherW k) (notQImW k)
    (scalarW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, scalarW])

/-- `%and10 = and i64 %or19.i, %not7`: the delimiter outside a string. -/
theorem b_delimNotIm (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%or19.i" = some (.int 64 (or5W k)))
    (h2 : lookupName env "%not7" = some (.int 64 (notXorW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and10" .and 64 (.reg "%or19.i") (.reg "%not7")) =
      some (stateAt (("%and10", .int 64 (delimNotImW k)) :: env) s) :=
  step_binop_v _ _ _ "%and10" .and "%or19.i" "%not7" (or5W k) (notXorW k)
    (delimNotImW k) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, delimNotImW])

/-- `%shl11 = shl i64 %and8, 1`. -/
theorem b_shlScalar (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and8" = some (.int 64 (scalarW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shl11" .shl 64 (.reg "%and8") (JsonS1BlocksIR.lit 64 1)) =
      some (stateAt (("%shl11", .int 64 (shlScalarW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := scalarW k) (y := BitVec.ofInt 64 1)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, JsonS1BlocksIR.lit, Const.toValue])
    (r := (shlScalarW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, ofNat_toNat]
      rw [show (BitVec.ofInt 64 1).toNat = 1 from by decide]
      simp only [shlScalarW, bv_toNat, ofNat_toNat, BitVec.shiftLeft_eq])]
  simp only [stateAt, State.bind, ofNat_toNat]

/-- `%or12 = or i64 %shl11, %prevS.0180`. -/
theorem b_orPrev (env : Env) (s : State) (k : Ctx) (p : BitVec 64)
    (h : lookupName env "%shl11" = some (.int 64 (shlScalarW k)))
    (h2 : lookupName env "%prevS.0180" = some (.int 64 p)) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%or12" .or 64 (.reg "%shl11") (.reg "%prevS.0180")) =
      some (stateAt (("%or12", .int 64 (orPrevW k p)) :: env) s) :=
  step_binop_v _ _ _ "%or12" .or "%shl11" "%prevS.0180" (shlScalarW k) p
    (orPrevW k p) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, orPrevW])

/-- `%not13 = xor i64 %or12, -1`. -/
theorem b_notOrPrev (env : Env) (s : State) (k : Ctx) (p : BitVec 64)
    (h : lookupName env "%or12" = some (.int 64 (orPrevW k p))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%not13" .xor 64 (.reg "%or12") (JsonS1BlocksIR.lit 64 (-1))) =
      some (stateAt (("%not13", .int 64 (notOrPrevW k p)) :: env) s) :=
  step_binop_imm _ _ _ "%not13" .xor "%or12" (BitVec.ofInt 64 (-1)) (orPrevW k p)
    (notOrPrevW k p) h (by
    simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, notOrPrevW,
      show (BitVec.ofInt 64 (-1)) = BitVec.allOnes 64 from by decide])

/-- `%and14 = and i64 %and8, %not13`: the scalar starts. -/
theorem b_andScalar (env : Env) (s : State) (k : Ctx) (p : BitVec 64)
    (h : lookupName env "%and8" = some (.int 64 (scalarW k)))
    (h2 : lookupName env "%not13" = some (.int 64 (notOrPrevW k p))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%and14" .and 64 (.reg "%and8") (.reg "%not13")) =
      some (stateAt (("%and14", .int 64 (andScalarW k p)) :: env) s) :=
  step_binop_v _ _ _ "%and14" .and "%and8" "%not13" (scalarW k) (notOrPrevW k p)
    (andScalarW k p) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, andScalarW])

/-- `%32 = or i64 %and10, %and14`. -/
theorem b_or32 (env : Env) (s : State) (k : Ctx) (p : BitVec 64)
    (h : lookupName env "%and10" = some (.int 64 (delimNotImW k)))
    (h2 : lookupName env "%and14" = some (.int 64 (andScalarW k p))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%32" .or 64 (.reg "%and10") (.reg "%and14")) =
      some (stateAt (("%32", .int 64 (or32W k p)) :: env) s) :=
  step_binop_v _ _ _ "%32" .or "%and10" "%and14" (delimNotImW k) (andScalarW k p)
    (or32W k p) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, or32W])

/-- `%or15 = or i64 %32, %and.i`: the entry word. -/
theorem b_entry (env : Env) (s : State) (k : Ctx) (p : BitVec 64)
    (h : lookupName env "%32" = some (.int 64 (or32W k p)))
    (h2 : lookupName env "%and.i" = some (.int 64 (andQuoteW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%or15" .or 64 (.reg "%32") (.reg "%and.i")) =
      some (stateAt (("%or15", .int 64 (entryW k p)) :: env) s) :=
  step_binop_v _ _ _ "%or15" .or "%32" "%and.i" (or32W k p) (andQuoteW k)
    (entryW k p) h h2 (by
      simp only [evalBinopNat, evalBinop, Option.map, bv_toNat, ofNat_toNat, entryW])

/-- `%shr16 = lshr i64 %and8, 63`: the next block's `prevS`. -/
theorem b_prevOut (env : Env) (s : State) (k : Ctx)
    (h : lookupName env "%and8" = some (.int 64 (scalarW k))) :
    evalInstr s1BlocksCalls (stateAt env s)
        (.binop "%shr16" .lshr 64 (.reg "%and8") (JsonS1BlocksIR.lit 64 63)) =
      some (stateAt (("%shr16", .int 64 (prevOutW k)) :: env) s) := by
  rw [JsonS1MasksIR.evalInstr_binop (x := scalarW k) (y := BitVec.ofInt 64 63)
    (ha := by simp only [stateAt, evalOperand, h])
    (hb := by simp only [stateAt, evalOperand, JsonS1BlocksIR.lit, Const.toValue])
    (r := (prevOutW k).toNat) (hr := by
      simp only [evalBinopNat, evalBinop, Option.map, ofNat_toNat]
      rw [show (BitVec.ofInt 64 63).toNat = 63 from by decide]
      simp only [prevOutW, bv_toNat, ofNat_toNat]
      rfl)]
  simp only [stateAt, State.bind, ofNat_toNat]

end LeanLLVM.Refinement.JsonS1BlocksSteps
