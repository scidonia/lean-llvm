/-
Tier 1 at the body: the four links between `num_fast_el1`'s inlined blocks and
`StrtodTier1.emittedRefinesOn_tier1`.

`JsonStage2NumFastArm` names the boundary: the tier-1 path is
`if.end230` → `if.then241` → `if.then253` → `cond.true`/`cond.false` →
`cleanup282.thread`, and four links are missing between the body's blocks and the
tier module's statement.  This module is those four links, at the body's own
instruction lists.

1. **The chain steps.**  `evalInstr` defines `uitofp`, `fmul`, `fdiv`, `fneg`,
   the eight-byte `double` load, the `double`-typed `getelementptr`, the
   `double` select and the `double` store, but the tree had no step lemma for
   any of them, so no block of the path could be stepped.  The `step_*` and
   `denoteCode_*` theorems below are those steps, each at the shape
   `BlockEval` settles for the integer forms.
2. **The class test.**  `%or.cond304` at `if.end230` and `%or.cond306` at
   `if.then241` are the body's two range gates; `Tier1` is
   `digitCount d ≤ 15 ∧ -22 ≤ eff d ≤ 22`.  `orCond304_one`/`orCond306_one`
   prove both gates hold at the model's counters, so a tier-1 lexeme never
   leaves the fast path.
3. **The mantissa.**  `%add244 = %30 * %ip + %fr` with `%30` the read table row
   is `Decimal.mantissa d` when the carried registers are the fraction's digit
   count, the integer digits' value and the fraction digits' value:
   `ifThen241_add244_eq_mantissa`.  The `idig < 19` cap is inert at `≤ 15`
   digits: `mantissa_lt_two_pow_64`.
4. **The tick algebra.**  `uitofpBits`, `fmulBits`, `fdivBits` and `fnegBits`
   are defined as `packMag ∘ roundMag` at bit level, so the arithmetic the tier
   module took as the platform's single correctly rounded operation is the
   tree's own definition: `fmulBits_uitofp`, `fdivBits_uitofp` and
   `fnegBits_packMag` read `packMag (roundMag (mant * 10 ^ k * 2 ^ 1074) 1)`
   back out of the expression's bits, and `roundMag_eq_of_ratio` is what makes
   the tick shift cancel.

**What the links do not close.**  Link 3 is stated at the registers the merge
block carries; no theorem in the tree ties `%ip.5708717729` and `%fr.5718728` at
`if.end230` to `Decimal.digitsNat d.ip` and `Decimal.digitsNat fs`.  The digit
runs (`JsonStage2NumFastDigitRuns`) carry the accumulator existentially and prove
the *counts*; `JsonStage2NumFastArm`'s list already names this as the residual.
So `NumFastBodyArm`'s tier-1 obligation is discharged up to that register tie,
and the block it stops at is `if.end230`'s `%ip`/`%fr` phi values.
-/
import LeanLLVM.Refinement.JsonStage2NumFastStarts
import LeanLLVM.Refinement.JsonStage2NumFastCounters
import LeanLLVM.StrtodTier1

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.JSON
open LeanLLVM.StrtodTier1
open LeanLLVM.StrtodRefine

namespace NumFastTier1

/-! ### Link 1: the chain steps the tier-1 blocks need

Each is the `denoteCode` step for one `evalInstr` form the tier module's path
uses and the tree had no step for.  The float-valued instructions bind
`.float (BitVec 64)`; the two memory forms read and write eight bytes, the same
extent the `i64` forms do, and the `double` `getelementptr` scales its index by
`Ty.double.sizeBytes = 8`. -/

/-- The instruction at an arbitrary state: the step's body, before the state
builder is applied.  `BlockEval`'s integer steps are staged the same way, so the
`evalOperand` hypothesis is the one the block's own call site supplies. -/
theorem evalInstr_uitofp (calls : Calls) (s : State) (d : String) (wIn : Nat) (v : String)
    {x : BitVec wIn} (hv : evalOperand s (.reg v) = some (.int wIn x)) :
    evalInstr calls s (.uitofp d wIn (.reg v)) =
      some (s.bind d (.float (uitofpBits x.toNat))) := by
  simp [evalInstr, hv]

theorem evalInstr_fmul (calls : Calls) (s : State) (d a b : String) {x y : BitVec 64}
    (ha : evalOperand s (.reg a) = some (.float x))
    (hb : evalOperand s (.reg b) = some (.float y)) :
    evalInstr calls s (.fmul d (.reg a) (.reg b)) =
      some (s.bind d (.float (fmulBits x y))) := by
  simp [evalInstr, ha, hb]

theorem evalInstr_fdiv (calls : Calls) (s : State) (d a b : String) {x y : BitVec 64}
    (ha : evalOperand s (.reg a) = some (.float x))
    (hb : evalOperand s (.reg b) = some (.float y)) :
    evalInstr calls s (.fdiv d (.reg a) (.reg b)) =
      some (s.bind d (.float (fdivBits x y))) := by
  simp [evalInstr, ha, hb]

theorem evalInstr_fneg (calls : Calls) (s : State) (d v : String) {x : BitVec 64}
    (hv : evalOperand s (.reg v) = some (.float x)) :
    evalInstr calls s (.fneg d (.reg v)) = some (s.bind d (.float (fnegBits x))) := by
  simp [evalInstr, hv]

theorem evalInstr_store_double (calls : Calls) (s : State) (v p : String) {x : BitVec 64}
    {a : Nat} (hv : evalOperand s (.reg v) = some (.float x))
    (hp : evalOperand s (.reg p) = some (.ptr a)) :
    evalInstr calls s (.store Ty.double (.reg v) (.reg p)) =
      some { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) } := by
  simp [evalInstr, storeValue, hv, hp]

/-- `%d = uitofp i64 %v to double`. -/
theorem step_uitofp (calls : Calls) (env : Env) (s : State) (d v : String) (wIn : Nat)
    {x : BitVec wIn} (hv : lookupName env v = some (.int wIn x)) :
    evalInstr calls (stateAt env s) (.uitofp d wIn (.reg v)) =
      some (stateAt ((d, .float (uitofpBits x.toNat)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    evalInstr_uitofp calls (stateAt env s) d wIn v
      (evalOperand_reg_of env s v (.int wIn x) hv)

/-- `%d = fmul double %a, %b`. -/
theorem step_fmul (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y)) :
    evalInstr calls (stateAt env s) (.fmul d (.reg a) (.reg b)) =
      some (stateAt ((d, .float (fmulBits x y)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    evalInstr_fmul calls (stateAt env s) d a b
      (evalOperand_reg_of env s a (.float x) ha)
      (evalOperand_reg_of env s b (.float y) hb)

/-- `%d = fdiv double %a, %b`. -/
theorem step_fdiv (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y)) :
    evalInstr calls (stateAt env s) (.fdiv d (.reg a) (.reg b)) =
      some (stateAt ((d, .float (fdivBits x y)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    evalInstr_fdiv calls (stateAt env s) d a b
      (evalOperand_reg_of env s a (.float x) ha)
      (evalOperand_reg_of env s b (.float y) hb)

/-- `%d = fneg double %v`. -/
theorem step_fneg (calls : Calls) (env : Env) (s : State) (d v : String)
    {x : BitVec 64} (hv : lookupName env v = some (.float x)) :
    evalInstr calls (stateAt env s) (.fneg d (.reg v)) =
      some (stateAt ((d, .float (fnegBits x)) :: env) s) := by
  simpa only [stateAt, State.bind] using
    evalInstr_fneg calls (stateAt env s) d v
      (evalOperand_reg_of env s v (.float x) hv)

/-- `%d = load double, ptr %p`, at the eight bytes a binary64 occupies. -/
theorem step_load_double (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : BitVec 64}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes b.toNat 8)) :
    evalInstr calls (stateAt env s) (.load d Ty.double (.reg p)) =
      some (stateAt ((d, .float b) :: env) s) := by
  have hv' : loadValue s.mem Ty.double a = some (.float b) := by
    simp only [loadValue, hv, natToBytes_toNat, pow256_eight,
      Nat.mod_eq_of_lt b.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [stateAt, State.bind] using
    JsonS1MasksIR.evalInstr_load (s := stateAt env s) (ty := Ty.double)
      (evalOperand_reg_of env s p (.ptr a) hp) hv'

/-- `%d = getelementptr double, ptr %base, i64 %off`: the index scaled by the
element type's eight bytes. -/
theorem step_gep_double (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d Ty.double (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  have h := evalInstr_gep (calls := calls) (s := stateAt env s) (d := d)
    (elemTy := Ty.double) (base := (.reg base)) (off := (.reg off)) (a := a)
    (w := 64) (n := idx)
    (evalOperand_reg_of env s base (.ptr a) hb)
    (evalOperand_reg_of env s off (.int 64 idx) ho) hpos
  simpa only [numFast_sb_double, stateAt, State.bind] using h

/-- `%d = select i1 %c, %a, %b` on two `double` values. -/
theorem step_select_double (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.float x))
    (hb : lookupName env b = some (.float y)) :
    evalInstr calls (stateAt env s) (.select d Ty.double (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .float (if bb = 1 then x else y)) :: env) s) := by
  have hc' : evalOperand (stateAt env s) (.reg c) = some (.int 1 bb) :=
    evalOperand_reg_of env s c (.int 1 bb) hc
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.float x) :=
    evalOperand_reg_of env s a (.float x) ha
  have hb' : evalOperand (stateAt env s) (.reg b) = some (.float y) :=
    evalOperand_reg_of env s b (.float y) hb
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst bb
    simp only [show ((0 : BitVec 1) = 1) = False from by decide, ite_false,
      stateAt, State.bind]
    exact JsonS1MasksIR.evalInstr_select_false hc' ha' hb'
  · subst bb
    simp only [show ((1 : BitVec 1) = 1) = True from by decide, ite_true,
      stateAt, State.bind]
    exact JsonS1MasksIR.evalInstr_select_true hc' ha' hb'

/-- `store double %v, ptr %p`. -/
theorem step_store_double (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.float x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store Ty.double (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  simpa only [stateAt] using
    evalInstr_store_double calls (stateAt env s) v p
      (evalOperand_reg_of env s v (.float x) hv)
      (evalOperand_reg_of env s p (.ptr a) hp)

/-! ### The chain forms, one per step -/

theorem denoteCode_uitofp (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) (is : List Instr) :
    denoteCode calls (.uitofp d wIn (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float (uitofpBits x.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_uitofp calls env s d v wIn hv)]

theorem denoteCode_fmul (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y))
    (is : List Instr) :
    denoteCode calls (.fmul d (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float (fmulBits x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_fmul calls env s d a b ha hb)]

theorem denoteCode_fdiv (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.float x)) (hb : lookupName env b = some (.float y))
    (is : List Instr) :
    denoteCode calls (.fdiv d (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float (fdivBits x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_fdiv calls env s d a b ha hb)]

theorem denoteCode_fneg (calls : Calls) (env : Env) (s : State) (d v : String)
    {x : BitVec 64} (hv : lookupName env v = some (.float x)) (is : List Instr) :
    denoteCode calls (.fneg d (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float (fnegBits x)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_fneg calls env s d v hv)]

theorem denoteCode_load_double (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : BitVec 64}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes b.toNat 8)) (is : List Instr) :
    denoteCode calls (.load d Ty.double (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float b) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_load_double calls env s d p hp hv)]

theorem denoteCode_gep_double (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d Ty.double (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep_double calls env s d base off hb ho hpos)]

theorem denoteCode_select_double (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.float x))
    (hb : lookupName env b = some (.float y)) (is : List Instr) :
    denoteCode calls (.select d Ty.double (.reg c) (.reg a) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .float (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_double calls env s d c a b hc ha hb)]

theorem denoteCode_store_double (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.float x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store Ty.double (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_store_double calls env s v p hv hp)]

/-! ### Link 4: the bit-level arithmetic

The tier module's "one correctly rounded operation" is `packMag ∘ roundMag` in
this tree: `uitofpBits` is `packMag (roundMag (x * 2 ^ 1074) 1) false`, and
`fmulBits`/`fdivBits` divide back out.  The lemmas below read the code back out
of the pattern (`ofBits_packMag_false`), find the exact operand's tick value
(`roundMag_exact`), and cancel the tick shift (`roundMag_eq_of_ratio`). -/

/-- The tick value `packMag` puts behind the pattern. -/
theorem packMag_toNat_fin {c : Code} (hc : c.IsMag) (neg : Bool) :
    (packMag (.fin c) neg).toNat =
      (if neg then 2 ^ 63 else 0) +
        (c.expField * 2 ^ 52 +
          (if c.expField = 0 then c.mant else c.mant - 2 ^ 52)) := by
  have hb : (if neg then 2 ^ 63 else 0) +
        (c.expField * 2 ^ 52 +
          (if c.expField = 0 then c.mant else c.mant - 2 ^ 52)) < 2 ^ 64 := by
    rcases hc with ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩
    · rw [hE]
      cases neg <;> simp only [Bool.false_eq_true, reduceIte, ite_true] <;> omega
    · have hEne : ¬ c.expField = 0 := by omega
      cases neg <;> simp only [hEne, Bool.false_eq_true, reduceIte, ite_true] <;> omega
  simp only [packMag, Mag.toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]

/-- The trailing field a code's pattern carries: subnormal is the significand,
normal drops the implicit bit. -/
def codeMant (c : Code) : Nat := if c.expField = 0 then c.mant else c.mant - 2 ^ 52

theorem codeMant_lt {c : Code} (hc : c.IsMag) : codeMant c < 2 ^ 52 := by
  unfold codeMant
  rcases hc with ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩
  · rw [hE]; simp only [reduceIte]; exact hm
  · have hne : ¬ c.expField = 0 := by omega
    simp only [hne, reduceIte]; omega

theorem codeMant_eq (c : Code) : codeMant c = if c.expField = 0 then c.mant else c.mant - 2 ^ 52 :=
  rfl

/-- A positive finite code's pattern reads back as the code's fields, with the
sign clear. -/
theorem ofBits_packMag_false {c : Code} (hc : c.IsMag) :
    F64.ofBits (packMag (.fin c) false) = F64.mk false c.expField (codeMant c) := by
  have hb : (packMag (.fin c) false).toNat = c.expField * 2 ^ 52 + codeMant c := by
    have h := packMag_toNat_fin hc false
    simp only [Bool.false_eq_true, reduceIte, Nat.zero_add] at h
    rw [← codeMant_eq] at h
    exact h
  have hmod : c.expField % 2048 = c.expField := by
    rcases hc with ⟨h, _⟩ | ⟨_, h, _, _⟩ <;> omega
  have hdiv : (c.expField * 2 ^ 52 + codeMant c) / 2 ^ 63 = 0 := by
    have := codeMant_lt hc; omega
  have hd52 : (c.expField * 2 ^ 52 + codeMant c) / 2 ^ 52 = c.expField := by
    have := codeMant_lt hc; omega
  have hm52 : (c.expField * 2 ^ 52 + codeMant c) % 2 ^ 52 = codeMant c := by
    have := codeMant_lt hc; omega
  simp only [F64.ofBits, hb, hdiv, hd52, hm52, hmod,
    show decide ((0 : Nat) = 1) = false from by decide]

/-- The magnitude behind a positive finite code's pattern is the code's tick
value. -/
theorem magTicks_ofBits_packMag_false {c : Code} (hc : c.IsMag) :
    F64.magTicks (F64.ofBits (packMag (.fin c) false)) = c.ticks := by
  rw [ofBits_packMag_false hc]
  by_cases hE : c.expField = 0
  · have hcm : codeMant c = c.mant := by simp [codeMant, hE]
    simp only [F64.magTicks, hE, reduceIte, Code.ticks, hcm]
  · have ht : codeMant c + 2 ^ 52 = c.mant := by
      unfold codeMant
      rw [if_neg hE]
      rcases hc with ⟨h, _⟩ | ⟨_, _, hm1, _⟩
      · omega
      · exact Nat.sub_add_cancel hm1
    simp only [F64.magTicks, hE, reduceIte, Code.ticks, ht]

theorem isNaN_ofBits_packMag_false {c : Code} (hc : c.IsMag) :
    (F64.ofBits (packMag (.fin c) false)).isNaN = false := by
  rw [ofBits_packMag_false hc]
  have hE : c.expField ≠ 2047 := by
    rcases hc with ⟨h, _⟩ | ⟨_, h, _, _⟩ <;> omega
  simp only [F64.isNaN, show (c.expField == 2047) = false from by
    rw [beq_eq_false_iff_ne]; exact hE, Bool.false_and]

theorem isInf_ofBits_packMag_false {c : Code} (hc : c.IsMag) :
    (F64.ofBits (packMag (.fin c) false)).isInf = false := by
  rw [ofBits_packMag_false hc]
  have hE : c.expField ≠ 2047 := by
    rcases hc with ⟨h, _⟩ | ⟨_, h, _, _⟩ <;> omega
  simp only [F64.isInf, show (c.expField == 2047) = false from by
    rw [beq_eq_false_iff_ne]; exact hE, Bool.false_and]

theorem isZero_ofBits_packMag_false {c : Code} (hc : c.IsMag) (hpos : 0 < c.ticks) :
    (F64.ofBits (packMag (.fin c) false)).isZero = false := by
  rw [ofBits_packMag_false hc]
  by_cases hE : c.expField = 0
  · have hm : c.mant ≠ 0 := by
      have := hpos; rw [Code.ticks, if_pos hE] at this; omega
    have hcm : codeMant c = c.mant := by simp [codeMant, hE]
    rw [F64.isZero, hcm,
      show (c.expField == 0) = true from by rw [beq_iff_eq]; exact hE,
      show (c.mant == 0) = false from by rw [beq_eq_false_iff_ne]; exact hm]
    rfl
  · rw [F64.isZero,
      show (c.expField == 0) = false from by rw [beq_eq_false_iff_ne]; exact hE]
    rfl

/-- The sign field of a positive finite code's pattern is clear. -/
theorem neg_ofBits_packMag_false {c : Code} (hc : c.IsMag) :
    (F64.ofBits (packMag (.fin c) false)).neg = false := by
  rw [ofBits_packMag_false hc]

/-- **The product of two exact nonnegative operands**, at the tree's bit model:
the encoding `fmulBits` returns is `packMag` of the one rounded product in
ticks. -/
theorem fmulBits_pack {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag) :
    fmulBits (packMag (.fin c₁) false) (packMag (.fin c₂) false) =
      packMag (roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074)) false := by
  simp only [fmulBits, isNaN_ofBits_packMag_false h₁, isNaN_ofBits_packMag_false h₂,
    isInf_ofBits_packMag_false h₁, isInf_ofBits_packMag_false h₂,
    magTicks_ofBits_packMag_false h₁, magTicks_ofBits_packMag_false h₂,
    neg_ofBits_packMag_false h₁, neg_ofBits_packMag_false h₂,
    Bool.false_or, Bool.false_and, Bool.and_false, Bool.false_bne,
    Bool.false_eq_true, ite_true, ite_false]

/-- **The quotient of two exact nonnegative operands**, at the same model. -/
theorem fdivBits_pack {c₁ c₂ : Code} (h₁ : c₁.IsMag) (h₂ : c₂.IsMag)
    (hpos : 0 < c₂.ticks) :
    fdivBits (packMag (.fin c₁) false) (packMag (.fin c₂) false) =
      packMag (roundMag (c₁.ticks * 2 ^ 1074) c₂.ticks) false := by
  have hz : (F64.ofBits (packMag (.fin c₂) false)).isZero = false :=
    isZero_ofBits_packMag_false h₂ hpos
  simp only [fdivBits, isNaN_ofBits_packMag_false h₁, isNaN_ofBits_packMag_false h₂,
    isInf_ofBits_packMag_false h₁, isInf_ofBits_packMag_false h₂,
    hz,
    magTicks_ofBits_packMag_false h₁, magTicks_ofBits_packMag_false h₂,
    neg_ofBits_packMag_false h₁, neg_ofBits_packMag_false h₂,
    Bool.false_or, Bool.false_and, Bool.and_false, Bool.false_bne,
    Bool.false_eq_true, ite_true, ite_false]

/-! #### The exact operands

`x * 2 ^ 1074` for `0 < x < 2 ^ 53` is a binary64 magnitude exactly, so
`roundMag` answers the code whose tick value is that integer.  The shift is
`x.log2`: the significand is `x` shifted so its leading bit is the implicit
one. -/

theorem pow_log2_le {x : Nat} (hx : x ≠ 0) : 2 ^ x.log2 ≤ x := by
  apply Nat.le_of_not_lt
  intro h
  exact absurd ((Nat.log2_lt hx).mpr h) (by omega)

theorem lt_pow_log2_succ {x : Nat} (hx : x ≠ 0) : x < 2 ^ (x.log2 + 1) :=
  (Nat.log2_lt hx).mp (Nat.lt_succ_self _)

/-- A positive integer below `2 ^ 53`, shifted into the binary64 grid at the
tick unit: the magnitude's two-factor form. -/
theorem isB64Mag_mul_two_pow {x : Nat} (h1 : 0 < x) (h2 : x < 2 ^ 53) :
    IsB64Mag (x * 2 ^ 1074) := by
  have hx : x ≠ 0 := by omega
  have hLle : x.log2 + 1 ≤ 53 := (Nat.log2_lt hx).mpr h2
  have hsL : 52 - x.log2 + x.log2 = 52 := by omega
  have hle : 2 ^ x.log2 ≤ x := pow_log2_le hx
  have hlt : x < 2 ^ (x.log2 + 1) := lt_pow_log2_succ hx
  refine Or.inr (Or.inr ⟨1074 - (52 - x.log2), x * 2 ^ (52 - x.log2), by omega,
    ?_, ?_, ?_⟩)
  · calc 2 ^ 52 = 2 ^ (x.log2 + (52 - x.log2)) := by
          rw [show x.log2 + (52 - x.log2) = 52 by omega]
      _ = 2 ^ x.log2 * 2 ^ (52 - x.log2) := Nat.pow_add 2 _ _
      _ ≤ x * 2 ^ (52 - x.log2) := Nat.mul_le_mul_right _ hle
  · calc x * 2 ^ (52 - x.log2) < 2 ^ (x.log2 + 1) * 2 ^ (52 - x.log2) :=
        Nat.mul_lt_mul_of_pos_right hlt (two_pow_pos (52 - x.log2))
      _ = 2 ^ ((x.log2 + 1) + (52 - x.log2)) := (Nat.pow_add 2 _ _).symm
      _ = 2 ^ 53 := by rw [show (x.log2 + 1) + (52 - x.log2) = 53 by omega]
  · have hexp : 52 - x.log2 + (1074 - (52 - x.log2)) = 1074 := by omega
    rw [Nat.mul_assoc, ← Nat.pow_add, hexp]

/-- **`roundMag` at an exact tick value**: no rounding happens, so the code's
tick value is the integer itself. -/
theorem roundMag_exact {x : Nat} (h1 : 0 < x) (h2 : x < 2 ^ 53) :
    ∃ c : Code, roundMag (x * 2 ^ 1074) 1 = .fin c ∧ c.IsMag ∧
      c.ticks = x * 2 ^ 1074 := by
  have hM : IsB64Mag (x * 2 ^ 1074) := isB64Mag_mul_two_pow h1 h2
  have hno : ¬ overflowTicks * 1 ≤ x * 2 ^ 1074 := by
    have hlt : x * 2 ^ 1074 < 2 ^ 53 * 2 ^ 1074 :=
      Nat.mul_lt_mul_of_pos_right h2 (two_pow_pos 1074)
    have hpow : (2 : Nat) ^ 53 * 2 ^ 1074 = 2 ^ 1127 := by
      rw [← Nat.pow_add]
    have hover : (2 : Nat) ^ 2097 ≤ overflowTicks := by
      unfold overflowTicks; decide
    rw [hpow] at hlt
    omega
  obtain ⟨c, hc, hcM⟩ := roundMag_isCode (P := x * 2 ^ 1074) (d := 1)
    (by decide) hno
  refine ⟨c, hc, hcM, ?_⟩
  have hdist := roundMag_nearest (P := x * 2 ^ 1074) (d := 1)
    (by decide) hno hc hM
  have hzero : distNum (x * 2 ^ 1074) 1 (x * 2 ^ 1074) = 0 := by
    simp only [distNum, Nat.mul_one, Nat.le_refl, ite_true, Nat.sub_self]
  rw [hzero] at hdist
  unfold distNum at hdist
  split at hdist <;> omega

/-- **`uitofpBits` reads as its own tick value**: for `0 < x < 2 ^ 53` the
conversion is exact, so the code behind the pattern has tick value
`x * 2 ^ 1074`. -/
theorem uitofpBits_spec {x : Nat} (h1 : 0 < x) (h2 : x < 2 ^ 53) :
    ∃ c : Code, uitofpBits x = packMag (.fin c) false ∧ c.IsMag ∧
      c.ticks = x * 2 ^ 1074 := by
  obtain ⟨c, hc, hcM, ht⟩ := roundMag_exact h1 h2
  exact ⟨c, by simp only [uitofpBits, hc], hcM, ht⟩

/-- **The product's tick algebra.**  The two `packMag`s `fmulBits` reads as
operands are exact, and the one rounding of their product in ticks is the one
rounding of `x * y * 2 ^ 1074`. -/
theorem fmulBits_uitofp {x y : Nat} (hx1 : 0 < x) (hx2 : x < 2 ^ 53)
    (hy1 : 0 < y) (hy2 : y < 2 ^ 53) :
    fmulBits (uitofpBits x) (uitofpBits y) =
      packMag (roundMag (x * y * 2 ^ 1074) 1) false := by
  obtain ⟨c₁, h₁, h₁M, ht₁⟩ := uitofpBits_spec hx1 hx2
  obtain ⟨c₂, h₂, h₂M, ht₂⟩ := uitofpBits_spec hy1 hy2
  have hr : roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074) =
      roundMag (x * y * 2 ^ 1074) 1 := by
    rw [ht₁, ht₂]
    exact roundMag_eq_of_ratio (by decide : 0 < 2 ^ 1074) (by decide : 0 < 1)
      (by simp only [Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm])
  rw [h₁, h₂, fmulBits_pack h₁M h₂M, hr]

/-- **The quotient's tick algebra.**  The division's exact value in ticks is
`x * 2 ^ 1074 / y`, and the tick shift cancels the same way. -/
theorem fdivBits_uitofp {x y : Nat} (hx1 : 0 < x) (hx2 : x < 2 ^ 53)
    (hy1 : 0 < y) (hy2 : y < 2 ^ 53) :
    fdivBits (uitofpBits x) (uitofpBits y) =
      packMag (roundMag (x * 2 ^ 1074) y) false := by
  obtain ⟨c₁, h₁, h₁M, ht₁⟩ := uitofpBits_spec hx1 hx2
  obtain ⟨c₂, h₂, h₂M, ht₂⟩ := uitofpBits_spec hy1 hy2
  have hpos : 0 < c₂.ticks := by
    rw [ht₂]; exact Nat.mul_pos hy1 (two_pow_pos 1074)
  have hr : roundMag (c₁.ticks * 2 ^ 1074) c₂.ticks =
      roundMag (x * 2 ^ 1074) y := by
    rw [ht₁, ht₂]
    exact roundMag_eq_of_ratio (Nat.mul_pos hy1 (two_pow_pos 1074)) (by omega)
      (by simp only [Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm])
  rw [h₁, h₂, fdivBits_pack h₁M h₂M hpos, hr]

/-- The sign bit's flip at a positive code: `fneg` is the pattern with the sign
bit set. -/
theorem fnegBits_packMag_false {c : Code} (hc : c.IsMag) :
    fnegBits (packMag (.fin c) false) = packMag (.fin c) true := by
  rw [fnegBits, ofBits_packMag_false hc]
  simp only [Bool.not_false, F64.toBits, F64.toNat, reduceIte, packMag, Mag.toNat,
    codeMant_eq]
  rw [Nat.add_assoc]

/-! ### Link 1 (continued): the remaining step shapes the path uses

`if.then241` addresses `@NUMF_EL1_P10` with an `i64` `getelementptr`, and
`if.then253` compares signed, so two more chain steps are needed beside the
float forms above. -/

/-- `%d = getelementptr i64, ptr %base, i64 %off`. -/
theorem step_gep64_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 64) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  have h := evalInstr_gep (calls := calls) (s := stateAt env s) (d := d)
    (elemTy := .int 64) (base := (.reg base)) (off := (.reg off)) (a := a)
    (w := 64) (n := idx)
    (evalOperand_reg_of env s base (.ptr a) hb)
    (evalOperand_reg_of env s off (.int 64 idx) ho) hpos
  simpa only [show (Ty.int 64).sizeBytes = 8 from by decide, stateAt, State.bind] using h

theorem denoteCode_gep64_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 64) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep64_reg calls env s d base off hb ho hpos)]

/-- `%d = getelementptr i64, ptr @base, i64 %off`: the global form, which is how
the two tables are addressed. -/
theorem step_gep64_global (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 64) (.global base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.global base) = some (.ptr a) :=
    evalOperand_reg_of env s base (.ptr a) hb
  have h := evalInstr_gep (calls := calls) (s := stateAt env s) (d := d)
    (elemTy := .int 64) (base := (.global base)) (off := (.reg off)) (a := a)
    (w := 64) (n := idx) hb'
    (evalOperand_reg_of env s off (.int 64 idx) ho) hpos
  simpa only [show (Ty.int 64).sizeBytes = 8 from by decide, stateAt, State.bind] using h

theorem denoteCode_gep64_global (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 64) (.global base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep64_global calls env s d base off hb ho hpos)]

/-- `%d = icmp sgt i64 %a, <c>`. -/
theorem step_icmp_sgt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.icmp d .sgt 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 1 (evalICmp .sgt x c)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    evalOperand_reg_of env s a (.int 64 x) ha
  have h := JsonS1MasksIR.evalInstr_icmp (calls := calls) (s := stateAt env s) (d := d)
    (pred := .sgt) (w := 64) (a := (.reg a)) (b := (.imm (.int 64 c)))
    ha' (evalOperand_lit_of (stateAt env s) 64 c)
  rw [h]
  simp only [evalICmpNat_toNat, stateAt, State.bind]

theorem denoteCode_icmp_sgt_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64} (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.icmp d .sgt 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .sgt x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_sgt_imm calls env s d a ha)]

/-- `%d = sub i64 <c>, %b`. -/
theorem step_sub_imm_reg (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64} (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .sub 64 (.imm (.int 64 c)) (.reg b)) =
      some (stateAt ((d, .int 64 (c - y)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.reg b) = some (.int 64 y) :=
    evalOperand_reg_of env s b (.int 64 y) hb
  have hr : evalBinopNat .sub 64 c.toNat y.toNat = some (c - y).toNat := by
    simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]
  have h := JsonS1MasksIR.evalInstr_binop (calls := calls) (s := stateAt env s)
    (d := d) (op := .sub) (w := 64) (a := (.imm (.int 64 c))) (b := (.reg b))
    (evalOperand_lit_of (stateAt env s) 64 c) hb' hr
  rw [h]
  simp only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem denoteCode_sub_imm_reg (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64} (hb : lookupName env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.binop d .sub 64 (.imm (.int 64 c)) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (c - y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_sub_imm_reg calls env s d b hb)]

/-- The global form of the `double` `getelementptr`, which addresses the power
table. -/
theorem step_gep_double_global (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d Ty.double (.global base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.global base) = some (.ptr a) :=
    evalOperand_reg_of env s base (.ptr a) hb
  have h := evalInstr_gep (calls := calls) (s := stateAt env s) (d := d)
    (elemTy := Ty.double) (base := (.global base)) (off := (.reg off)) (a := a)
    (w := 64) (n := idx) hb'
    (evalOperand_reg_of env s off (.int 64 idx) ho) hpos
  simpa only [numFast_sb_double, stateAt, State.bind] using h

theorem denoteCode_gep_double_global (calls : Calls) (env : Env) (s : State)
    (d base off : String) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d Ty.double (.global base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat * 8)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep_double_global calls env s d base off hb ho hpos)]

/-- `%d = select i1 %c, %a, %b` on two one-bit values. -/
theorem step_select_bit1_reg (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {bb x y : BitVec 1}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) :
    evalInstr calls (stateAt env s) (.select d (.int 1) (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with rfl | rfl
  · simp only [evalInstr, evalOperand, hc, ha, hb, State.bind, stateAt,
      show ((0 : BitVec 1) = 1) = False from by decide, ite_false, ite_true]
  · simp only [evalInstr, evalOperand, hc, ha, hb, State.bind, stateAt,
      show ((1 : BitVec 1) = 1) = True from by decide, ite_true]

/-- The immediate form of the one-bit select, which is how the gate's
conjunction is written. -/
theorem step_select_bit1_imm (calls : Calls) (env : Env) (s : State) (d c a : String)
    {bb x y : BitVec 1}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 1 x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 1) (.reg c) (.reg a) (.imm (.int 1 y))) =
      some (stateAt ((d, .int 1 (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with rfl | rfl
  · simp only [evalInstr, evalOperand, Const.toValue, hc, ha, State.bind, stateAt,
      show ((0 : BitVec 1) = 1) = False from by decide, ite_false, ite_true]
  · simp only [evalInstr, evalOperand, Const.toValue, hc, ha, State.bind, stateAt,
      show ((1 : BitVec 1) = 1) = True from by decide, ite_true]

theorem denoteCode_select_bit1_reg (calls : Calls) (env : Env) (s : State)
    (d c a b : String) {bb x y : BitVec 1}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 1 x))
    (hb : lookupName env b = some (.int 1 y)) (is : List Instr) :
    denoteCode calls (.select d (.int 1) (.reg c) (.reg a) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 1 (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_bit1_reg calls env s d c a b hc ha hb)]

theorem denoteCode_select_bit1_imm (calls : Calls) (env : Env) (s : State)
    (d c a : String) {bb x y : BitVec 1}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 1 x)) (is : List Instr) :
    denoteCode calls (.select d (.int 1) (.reg c) (.reg a) (.imm (.int 1 y)) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 1 (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_bit1_imm calls env s d c a hc ha)]

/-- `%d = mul i64 %a, %b`, the register form the mantissa product uses. -/
theorem step_mul_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .mul 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x * y)) :: env) s) := by
  have ha' : evalOperand (stateAt env s) (.reg a) = some (.int 64 x) :=
    evalOperand_reg_of env s a (.int 64 x) ha
  have hb' : evalOperand (stateAt env s) (.reg b) = some (.int 64 y) :=
    evalOperand_reg_of env s b (.int 64 y) hb
  have hr : evalBinopNat .mul 64 x.toNat y.toNat = some (x * y).toNat := by
    simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat]
  have h := JsonS1MasksIR.evalInstr_binop (calls := calls) (s := stateAt env s)
    (d := d) (op := .mul) (w := 64) (a := (.reg a)) (b := (.reg b)) ha' hb' hr
  rw [h]
  simp only [stateAt, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem denoteCode_mul_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.binop d .mul 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x * y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_mul_reg calls env s d a b ha hb)]

/-! ### A block evaluator at the float shapes

`BlockEval`'s `block_step` knows the integer and memory forms; the tier-1 path
needs the forms above too.  The macro adds them and keeps `block_eval`'s two
phases, so a block's proof stays the statement of its environment. -/

macro "t1_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_icmp_sgt_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_sub_imm_reg _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep_double_global _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_mul_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit1_reg _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_select_bit1_imm _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep64_reg _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_gep64_global _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_uitofp _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_fmul _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_fdiv _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_fneg _ _ _ _ _ ?_ _]
   | rw [denoteCode_load_double _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_gep_double _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_select_double _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_store_double _ _ _ _ _ ?_ ?_ _]))

macro "t1_eval" : tactic => `(tactic| (repeat t1_step; block_close))

/-! ### Link 2: the two range gates at the body

`if.end230`'s `%or.cond304` is `select i1 %cmp233, i1 %29, i1 false` — the
conjunction `nd < 20 ∧ -45 ≤ eff ≤ 45` with the range test read only when the
digit count passes — and `if.then241`'s `%or.cond306` is
`nd < 16 ∧ -22 ≤ eff ≤ 22`.  At the model's counters (`numFast_ifEnd230_counts`)
`Tier1` makes both conjunction bits one, so a tier-1 lexeme never leaves the
fast path. -/

/-- The merge block's environment, from predecessor `if.end226`: its five `phi`
sources, the two counters, and the four gate values. -/
def t1GateEnv (env : Env) (exp10 idig ip fr fdig : BitVec 64) : Env :=
  ("%or.cond304", .int 1
    (if evalICmp .ult (fdig + idig) (20#64) = 1 then
      evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0)) ::
  ("%29", .int 1 (evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64))) ::
  ("%28", .int 64 ((exp10 - fdig) + (45#64))) ::
  ("%cmp233", .int 1 (evalICmp .ult (fdig + idig) (20#64))) ::
  ("%add232", .int 64 (fdig + idig)) ::
  ("%sub231", .int 64 (exp10 - fdig)) ::
  ("%fdig.4719727", .int 64 fdig) ::
  ("%fr.5718728", .int 64 fr) ::
  ("%ip.5708717729", .int 64 ip) ::
  ("%idig.4709716730", .int 64 idig) ::
  ("%exp10.4731", .int 64 exp10) :: env

theorem t1GateEnv_sub (env : Env) (exp10 idig ip fr fdig : BitVec 64) :
    lookupName (t1GateEnv env exp10 idig ip fr fdig) "%sub231"
      = some (.int 64 (exp10 - fdig)) := by
  simp only [t1GateEnv]
  block_lk

theorem t1GateEnv_add (env : Env) (exp10 idig ip fr fdig : BitVec 64) :
    lookupName (t1GateEnv env exp10 idig ip fr fdig) "%add232"
      = some (.int 64 (fdig + idig)) := by
  simp only [t1GateEnv]
  block_lk

/-- `if.end230`, at its own instruction list: the five `phi`s from
`if.end226`, `%sub231 = %exp10 - %fdig`, `%add232 = %fdig + %idig`, the two
range tests and the conjunctive select. -/
theorem t1_ifEnd230_denote (calls : Calls) (env : Env) (s : State)
    {exp10 idig ip fr fdig : BitVec 64}
    (hpre : s.pre = some "if.end226")
    (he : lookupName env "%exp10.4" = some (.int 64 exp10))
    (hi : lookupName env "%idig.4" = some (.int 64 idig))
    (hip : lookupName env "%ip.5" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.4" = some (.int 64 fdig)) :
    denoteCode calls numFastIfEnd230Instrs (stateAt env s) =
      some (stateAt (t1GateEnv env exp10 idig ip fr fdig) s) := by
  unfold numFastIfEnd230Instrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%exp10.4" _ he
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%idig.4" _ hi
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%ip.5" _ hip
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%fr.5" _ hfr
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%fdig.4" _ hfd
  · simp only [runCells]
    rw [denoteCode_sub_reg _ _ _ "%sub231" "%exp10.4731" "%fdig.4719727"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_add_reg _ _ _ "%add232" "%fdig.4719727" "%idig.4709716730"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_icmp_ult_imm _ _ _ "%cmp233" "%add232" (by block_lk) _]
    rw [denoteCode_add_imm _ _ _ "%28" "%sub231" (by block_lk) _]
    rw [denoteCode_icmp_ult_imm _ _ _ "%29" "%28" (by block_lk) _]
    rw [denoteCode_select_bit1_imm _ _ _ "%or.cond304" "%cmp233" "%29"
      (by block_lk) (by block_lk) _]
    rw [denoteCode_nil]
    rfl

theorem t1_ifEnd230_step (calls : Calls) (env : Env) (s : State)
    {exp10 idig ip fr fdig : BitVec 64}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (he : lookupName env "%exp10.4" = some (.int 64 exp10))
    (hi : lookupName env "%idig.4" = some (.int 64 idig))
    (hip : lookupName env "%ip.5" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.4" = some (.int 64 fdig))
    (hbit : evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) = 1 ∧
      evalICmp .ult (fdig + idig) (20#64) = 1) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t1GateEnv env exp10 idig ip fr fdig)
        { s with pc := "if.then241", pre := some "if.end230" }) := by
  refine numFast_step_at (s' := stateAt (t1GateEnv env exp10 idig ip fr fdig) s)
    (b := ⟨"if.end230", numFastIfEnd230Instrs,
      Term.condbr (Operand.reg "%or.cond304") "if.then241" "if.end285"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd230Instrs] using numFast_findBlock_if_end230
  · simpa only [denoteCode_nil] using t1_ifEnd230_denote calls env s hpre he hi hip hfr hfd
  · have hlk : lookupName (t1GateEnv env exp10 idig ip fr fdig) "%or.cond304"
        = some (.int 1
          (if evalICmp .ult (fdig + idig) (20#64) = 1 then
            evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0)) :=
      lookupName_cons_self ..
    have hone : (if evalICmp .ult (fdig + idig) (20#64) = 1 then
        evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0) = 1 := by
      rw [hbit.2, if_pos rfl]; exact hbit.1
    rw [numFast_execTerm_condbr_one _ "%or.cond304" _ _ hlk hone]
    simp only [stateAt, hpc]

/-! ### Link 3: the mantissa word

`if.then241` reads `@NUMF_EL1_P10[fdig]` and forms `%add244 = %30 * %ip + %fr`.
With `%30` the table's `10 ^ fdig` and `%ip`/`%fr` the two digit runs' values,
that word is `Decimal.mantissa d`; at `≤ 15` digits the `i64` sum does not wrap
(`mantissa_lt_two_pow_64`). -/

/-- `if.then241`, from its `findBlock` pin. -/
def t1IfThen241Instrs : List Instr :=
  [Instr.gep "%arrayidx242" (Ty.int 64) (Operand.global "@NUMF_EL1_P10")
      (Operand.reg "%fdig.4719727"),
   Instr.load "%30" (Ty.int 64) (Operand.reg "%arrayidx242"),
   Instr.binop "%mul243" (BinOp.mul) 64 (Operand.reg "%30") (Operand.reg "%ip.5708717729"),
   Instr.binop "%add244" (BinOp.add) 64 (Operand.reg "%mul243") (Operand.reg "%fr.5718728"),
   Instr.icmp "%cmp245" (IPred.ult) 64 (Operand.reg "%add232")
     (Operand.imm (Const.int 64 0x0000000000000010#64)),
   Instr.binop "%31" (BinOp.add) 64 (Operand.reg "%sub231")
     (Operand.imm (Const.int 64 0x0000000000000016#64)),
   Instr.icmp "%32" (IPred.ult) 64 (Operand.reg "%31")
     (Operand.imm (Const.int 64 0x000000000000002d#64)),
   Instr.select "%or.cond306" (Ty.int 1) (Operand.reg "%cmp245") (Operand.reg "%32")
     (Operand.imm (Const.int 1 0x0#1))]

theorem t1_findBlock_ifThen241 :
    numFastBody.findBlock "if.then241" =
      some ⟨"if.then241", t1IfThen241Instrs,
        Term.condbr (Operand.reg "%or.cond306") "if.then253" "if.end268"⟩ := by
  simpa only [t1IfThen241Instrs] using numFast_findBlock_if_then241

/-- The mantissa word's block, from the gate's environment.  The load is read at
the table row the caller stages, so the loaded `ten` is a parameter. -/
def t1MantEnv (env : Env) (p10 : Nat) (fdig ip fr add232 sub231 : BitVec 64)
    (ten : BitVec 64) : Env :=
  ("%or.cond306", .int 1
    (if evalICmp .ult add232 (16#64) = 1 then
      evalICmp .ult (sub231 + (22#64)) (45#64) else 0)) ::
  ("%32", .int 1 (evalICmp .ult (sub231 + (22#64)) (45#64))) ::
  ("%31", .int 64 (sub231 + (22#64))) ::
  ("%cmp245", .int 1 (evalICmp .ult add232 (16#64))) ::
  ("%add244", .int 64 (ten * ip + fr)) ::
  ("%mul243", .int 64 (ten * ip)) ::
  ("%30", .int 64 ten) ::
  ("%arrayidx242", .ptr (p10 + (fdig.signExtend 64).toNat * 8)) :: env

theorem t1_ifThen241_denote (calls : Calls) (env : Env) (s : State)
    {p10 : Nat} {fdig ip fr add232 sub231 ten : BitVec 64}
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hfd : lookupName env "%fdig.4719727" = some (.int 64 fdig))
    (hip : lookupName env "%ip.5708717729" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5718728" = some (.int 64 fr))
    (had : lookupName env "%add232" = some (.int 64 add232))
    (hsu : lookupName env "%sub231" = some (.int 64 sub231))
    (hpos : (fdig.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (fdig.signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8)) :
    denoteCode calls t1IfThen241Instrs (stateAt env s) =
      some (stateAt (t1MantEnv env p10 fdig ip fr add232 sub231 ten) s) := by
  unfold t1IfThen241Instrs
  rw [denoteCode_gep64_global _ _ _ "%arrayidx242" "@NUMF_EL1_P10" "%fdig.4719727"
    hg (by simpa only [stateAt] using hfd) hpos _]
  rw [denoteCode_load64 _ _ _ "%30" "%arrayidx242" (by block_lk)
    (by simpa only [stateAt] using hread) _]
  rw [denoteCode_mul_reg _ _ _ "%mul243" "%30" "%ip.5708717729" (by block_lk) (by block_lk) _]
  rw [denoteCode_add_reg _ _ _ "%add244" "%mul243" "%fr.5718728"
    (by block_lk) (by block_lk) _]
  rw [denoteCode_icmp_ult_imm _ _ _ "%cmp245" "%add232" (by block_lk) _]
  rw [denoteCode_add_imm _ _ _ "%31" "%sub231" (by block_lk) _]
  rw [denoteCode_icmp_ult_imm _ _ _ "%32" "%31" (by block_lk) _]
  rw [denoteCode_select_bit1_imm _ _ _ "%or.cond306" "%cmp245" "%32"
    (by block_lk) (by block_lk) _]
  rw [denoteCode_nil]
  rfl

/-- The mantissa link at the model.  `%ip` is the integer digits' value, `%fr`
the fraction's, `%fdig` their count and `%30` the table's `10 ^ fdig`; then the
block's sum is `Decimal.mantissa d`, in `i64` and as a `Nat`.  The three
premises are the ones the arm's boundary names: `%ip`/`%fr`'s tie to
`digitsNat`, and the table row. -/
theorem t1_add244_eq_mantissa {d : Decimal} {fs : Bytes} {ip ten fr : BitVec 64}
    (hf : d.fr = some fs)
    (hip : ip = BitVec.ofNat 64 (Decimal.digitsNat d.ip))
    (hfr : fr = BitVec.ofNat 64 (Decimal.digitsNat fs))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hipb : Decimal.digitsNat d.ip < 2 ^ 64)
    (hfsb : Decimal.digitsNat fs < 2 ^ 64)
    (h10 : 10 ^ fs.length < 2 ^ 64)
    (hbound : d.mantissa < 2 ^ 64) :
    ten * ip + fr = BitVec.ofNat 64 d.mantissa := by
  have hm : d.mantissa
      = Decimal.digitsNat d.ip * 10 ^ fs.length + Decimal.digitsNat fs := by
    simp only [Decimal.mantissa, hf, Option.getD_some]
  have hsum : Decimal.digitsNat d.ip * 10 ^ fs.length + Decimal.digitsNat fs < 2 ^ 64 := by
    rw [← hm]; exact hbound
  subst hip
  subst hfr
  subst hten
  rw [hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
  rw [show 10 ^ fs.length % 2 ^ 64 = 10 ^ fs.length from Nat.mod_eq_of_lt h10,
    show Decimal.digitsNat d.ip % 2 ^ 64 = Decimal.digitsNat d.ip
      from Nat.mod_eq_of_lt hipb,
    show Decimal.digitsNat fs % 2 ^ 64 = Decimal.digitsNat fs
      from Nat.mod_eq_of_lt hfsb]
  rw [show 10 ^ fs.length * Decimal.digitsNat d.ip = Decimal.digitsNat d.ip * 10 ^ fs.length
      from Nat.mul_comm _ _]
  rw [show Decimal.digitsNat d.ip * 10 ^ fs.length % 2 ^ 64
      = Decimal.digitsNat d.ip * 10 ^ fs.length
      from Nat.mod_eq_of_lt (by omega)]

/-! ### Link 2, proved: the gates are one at `Tier1`

At the counters `JsonStage2NumFastCounters` reads, `Tier1` makes both range
tests true: `digitCount ≤ 15 < 16 < 20` and `|eff| ≤ 22` puts `eff + 22` in
`[0, 44]` and `eff + 45` in `[23, 67]`. -/

theorem gate_ult_one {w : Nat} {x y : BitVec w} (h : x.toNat < y.toNat) :
    evalICmp .ult x y = 1 :=
  (NumFastStarts.ult_iff_one x y).mpr h

theorem t1_orCond304_bits {d : Decimal} {exp10 fdig idig : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (h1 : Tier1 d) :
    evalICmp .ult (fdig + idig) (20#64) = 1 ∧
      evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) = 1 := by
  have hnd : digitCount d ≤ 19 := by have := h1.1; omega
  have hrange : -45 ≤ eff d ∧ eff d ≤ 45 := by
    have := h1.2; omega
  have hne := numFast_ifEnd230_counts (d := d) hE hF hI
  obtain ⟨hadd, hsub⟩ := hne
  have hneff := numEff_eq_eff_of_specRange hnd hrange
  constructor
  · rw [hadd]
    apply gate_ult_one
    simp only [BitVec.toNat_ofNat]
    have := h1.1; omega
  · rw [hsub, hneff]
    apply gate_ult_one
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have := h1.2; omega

theorem t1_orCond306_bits {d : Decimal} {sub add : BitVec 64}
    (hA : add = BitVec.ofNat 64 (digitCount d))
    (hS : sub = BitVec.ofInt 64 (eff d))
    (h1 : Tier1 d) :
    evalICmp .ult add (16#64) = 1 ∧
      evalICmp .ult (sub + (22#64)) (45#64) = 1 := by
  constructor
  · rw [hA]
    apply gate_ult_one
    simp only [BitVec.toNat_ofNat]
    have := h1.1; omega
  · rw [hS]
    apply gate_ult_one
    simp only [BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
    have := h1.2; omega

/-- The conjunction's value at `if.end230`, from the two bits. -/
theorem t1_gate304_one {b₁ b₂ : BitVec 1} (h₁ : b₁ = 1) (h₂ : b₂ = 1) :
    (if b₁ = 1 then b₂ else 0) = 1 := by
  rw [h₁, if_pos rfl, h₂]

theorem t1_gate306_one {b₁ b₂ : BitVec 1} (h₁ : b₁ = 1) (h₂ : b₂ = 1) :
    (if b₁ = 1 then b₂ else 0) = 1 := by
  rw [h₁, if_pos rfl, h₂]

/-! ### Links 3 and 4, read together: the expression's bits

`%add244` is the mantissa (link 3), `%conv256` its `uitofp`, and the table row is
`uitofpBits (10 ^ k)`.  The product (or quotient) is then `packMag` of the one
rounded exact value, by link 4.  These are the two expressions `strtodSpec`'s
`roundMag` sees: `opP`/`opD`; their statements follow the power-table entry's
exactness below. -/

/-! #### The power table's entries

`10 ^ k` for `k ≤ 22` is an exact binary64 value: it is `5 ^ k * 2 ^ k`, and
`5 ^ k < 2 ^ 53`, so the integer's trailing power of two is outside the
significand.  `uitofpBits (10 ^ k)` therefore reads back its own tick value,
which is what the power-table row's bytes say. -/

theorem ten_pow_factor (k : Nat) : (10 : Nat) ^ k = 5 ^ k * 2 ^ k := by
  rw [← Nat.mul_pow]

theorem five_pow_lt {k : Nat} (hk : k ≤ 22) : (5 : Nat) ^ k < 2 ^ 53 := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 5) hk
  have h22 : (5 : Nat) ^ 22 < 2 ^ 53 := by decide
  omega

theorem ten_pow_lt {k : Nat} (hk : k ≤ 22) : (10 : Nat) ^ k < 2 ^ 75 := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 10) hk
  have h22 : (10 : Nat) ^ 22 < 2 ^ 75 := by decide
  omega

/-- The power's tick value is on the binary64 lattice. -/
theorem isB64Mag_pow10_ticks {k : Nat} (hk : k ≤ 22) :
    IsB64Mag (10 ^ k * 2 ^ 1074) := by
  have h5 : (5 : Nat) ^ k < 2 ^ 53 := five_pow_lt hk
  have hx : (5 : Nat) ^ k ≠ 0 := by
    have := Nat.pow_pos (by decide : (0 : Nat) < 5) (n := k); omega
  have hLle : ((5 : Nat) ^ k).log2 + 1 ≤ 53 := (Nat.log2_lt hx).mpr h5
  have hle : 2 ^ ((5 : Nat) ^ k).log2 ≤ (5 : Nat) ^ k := pow_log2_le hx
  have hlt : (5 : Nat) ^ k < 2 ^ (((5 : Nat) ^ k).log2 + 1) := lt_pow_log2_succ hx
  rw [ten_pow_factor]
  refine Or.inr (Or.inr ⟨(k + 1074) - (52 - ((5 : Nat) ^ k).log2),
    (5 : Nat) ^ k * 2 ^ (52 - ((5 : Nat) ^ k).log2), by omega, ?_, ?_, ?_⟩)
  · calc 2 ^ 52 = 2 ^ (((5 : Nat) ^ k).log2 + (52 - ((5 : Nat) ^ k).log2)) := by
          rw [show ((5 : Nat) ^ k).log2 + (52 - ((5 : Nat) ^ k).log2) = 52 by omega]
      _ = 2 ^ ((5 : Nat) ^ k).log2 * 2 ^ (52 - ((5 : Nat) ^ k).log2) := Nat.pow_add 2 _ _
      _ ≤ (5 : Nat) ^ k * 2 ^ (52 - ((5 : Nat) ^ k).log2) := Nat.mul_le_mul_right _ hle
  · calc (5 : Nat) ^ k * 2 ^ (52 - ((5 : Nat) ^ k).log2)
        < 2 ^ (((5 : Nat) ^ k).log2 + 1) * 2 ^ (52 - ((5 : Nat) ^ k).log2) :=
          Nat.mul_lt_mul_of_pos_right hlt (two_pow_pos (52 - ((5 : Nat) ^ k).log2))
      _ = 2 ^ ((((5 : Nat) ^ k).log2 + 1) + (52 - ((5 : Nat) ^ k).log2)) :=
          (Nat.pow_add 2 _ _).symm
      _ = 2 ^ 53 := by rw [show ((((5 : Nat) ^ k).log2 + 1) + (52 - ((5 : Nat) ^ k).log2)) = 53
          by omega]
  · have hexp : 52 - ((5 : Nat) ^ k).log2 +
        ((k + 1074) - (52 - ((5 : Nat) ^ k).log2)) = k + 1074 := by omega
    conv_rhs => rw [Nat.mul_assoc, ← Nat.pow_add, hexp]
    conv_lhs => rw [Nat.mul_assoc, ← Nat.pow_add]

/-- `roundMag` at the power's exact tick value. -/
theorem roundMag_exact_pow10 {k : Nat} (hk : k ≤ 22) :
    ∃ c : Code, roundMag (10 ^ k * 2 ^ 1074) 1 = .fin c ∧ c.IsMag ∧
      c.ticks = 10 ^ k * 2 ^ 1074 := by
  have hM : IsB64Mag (10 ^ k * 2 ^ 1074) := isB64Mag_pow10_ticks hk
  have hno : ¬ overflowTicks * 1 ≤ 10 ^ k * 2 ^ 1074 := by
    have ht := ten_pow_lt hk
    have hlt : 10 ^ k * 2 ^ 1074 < 2 ^ 75 * 2 ^ 1074 :=
      Nat.mul_lt_mul_of_pos_right ht (two_pow_pos 1074)
    have hpow : (2 : Nat) ^ 75 * 2 ^ 1074 = 2 ^ 1149 := by
      rw [← Nat.pow_add]
    have hover : (2 : Nat) ^ 2097 ≤ overflowTicks := by
      unfold overflowTicks; decide
    rw [hpow] at hlt
    omega
  obtain ⟨c, hc, hcM⟩ := roundMag_isCode (P := 10 ^ k * 2 ^ 1074) (d := 1)
    (by decide) hno
  refine ⟨c, hc, hcM, ?_⟩
  have hdist := roundMag_nearest (P := 10 ^ k * 2 ^ 1074) (d := 1)
    (by decide) hno hc hM
  have hzero : distNum (10 ^ k * 2 ^ 1074) 1 (10 ^ k * 2 ^ 1074) = 0 := by
    simp only [distNum, Nat.mul_one, Nat.le_refl, ite_true, Nat.sub_self]
  rw [hzero] at hdist
  unfold distNum at hdist
  split at hdist <;> omega

theorem pow10_uitofp_spec {k : Nat} (hk : k ≤ 22) :
    ∃ c : Code, uitofpBits (10 ^ k) = packMag (.fin c) false ∧ c.IsMag ∧
      c.ticks = 10 ^ k * 2 ^ 1074 := by
  obtain ⟨c, hc, hcM, ht⟩ := roundMag_exact_pow10 hk
  exact ⟨c, by simp only [uitofpBits, hc], hcM, ht⟩

/-- **The product with a power-table entry**: the tree's one rounding of the
exact product, which is link 4 at `cond.true`. -/
theorem fmulBits_pow_uitofp {k m : Nat} (hk : k ≤ 22) (hm1 : 0 < m)
    (hm2 : m < 2 ^ 53) :
    fmulBits (uitofpBits (10 ^ k)) (uitofpBits m)
      = packMag (roundMag (10 ^ k * m * 2 ^ 1074) 1) false := by
  obtain ⟨c₁, h₁, h₁M, ht₁⟩ := pow10_uitofp_spec hk
  obtain ⟨c₂, h₂, h₂M, ht₂⟩ := uitofpBits_spec hm1 hm2
  have hr : roundMag (c₁.ticks * c₂.ticks) (2 ^ 1074) =
      roundMag (10 ^ k * m * 2 ^ 1074) 1 := by
    rw [ht₁, ht₂]
    exact roundMag_eq_of_ratio (by decide : 0 < 2 ^ 1074) (by decide : 0 < 1)
      (by simp only [Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm])
  rw [h₁, h₂, fmulBits_pack h₁M h₂M, hr]

/-- **The quotient by a power-table entry**, the division mirror at
`cond.false`. -/
theorem fdivBits_uitofp_pow {k m : Nat} (hk : k ≤ 22) (hm1 : 0 < m)
    (hm2 : m < 2 ^ 53) :
    fdivBits (uitofpBits m) (uitofpBits (10 ^ k))
      = packMag (roundMag (m * 2 ^ 1074) (10 ^ k)) false := by
  obtain ⟨c₁, h₁, h₁M, ht₁⟩ := uitofpBits_spec hm1 hm2
  obtain ⟨c₂, h₂, h₂M, ht₂⟩ := pow10_uitofp_spec hk
  have hpos : 0 < c₂.ticks := by
    rw [ht₂]
    have h := Nat.pow_pos (by decide : (0 : Nat) < 10) (n := k)
    exact Nat.mul_pos h (two_pow_pos 1074)
  have hr : roundMag (c₁.ticks * 2 ^ 1074) c₂.ticks =
      roundMag (m * 2 ^ 1074) (10 ^ k) := by
    rw [ht₁, ht₂]
    exact roundMag_eq_of_ratio
      (Nat.mul_pos (Nat.pow_pos (by decide : (0 : Nat) < 10) (n := k)) (two_pow_pos 1074))
      (Nat.pow_pos (by decide : (0 : Nat) < 10) (n := k))
      (by simp only [Nat.one_mul, Nat.mul_one, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm])
  rw [h₁, h₂, fdivBits_pack h₁M h₂M hpos, hr]

/-- **The emitted product is `opP`'s one rounding.**  With `k = eff d ≥ 0`,
`mant = d.mantissa` and a positive mantissa, the body's `fmul` of the table row
and `%conv256` is `packMag` of `roundMag (opP d) (opD d)`.  The zero mantissa
is `uitofpBits_zero`'s case: both sides are `+0`. -/
theorem t1_fmul_value {d : Decimal} {mant k : Nat}
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hmant : mant = d.mantissa) (hk : k = (eff d).toNat) (heff : 0 ≤ eff d)
    (hm1 : 0 < mant) :
    fmulBits (uitofpBits (10 ^ k)) (uitofpBits mant)
      = packMag (roundMag (opP d) (opD d)) false := by
  have hk22 : k ≤ 22 := by
    rw [hk]; exact toNat_le_of_le heff h1.2.2
  have hm2 : mant < 2 ^ 53 := by
    rw [hmant]; exact mantissa_lt hwf h1.1
  rw [fmulBits_pow_uitofp hk22 hm1 hm2]
  have hP : opP d = 10 ^ k * mant * 2 ^ 1074 := by
    unfold opP
    rw [if_pos heff, ← hk, ← hmant]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hD : opD d = 1 := by unfold opD; rw [if_pos heff]
  rw [hP, hD]

/-- **The emitted quotient is `opP`'s one rounding.**  The `eff < 0` mirror. -/
theorem t1_fdiv_value {d : Decimal} {mant k : Nat}
    (hwf : d.wellFormed) (h1 : Tier1 d)
    (hmant : mant = d.mantissa) (hk : k = (eff d).natAbs) (heff : eff d < 0)
    (hm1 : 0 < mant) :
    fdivBits (uitofpBits mant) (uitofpBits (10 ^ k))
      = packMag (roundMag (opP d) (opD d)) false := by
  have hk22 : k ≤ 22 := by
    rw [hk]; exact natAbs_le_of_between h1.2.1 h1.2.2
  have hm2 : mant < 2 ^ 53 := by
    rw [hmant]; exact mantissa_lt hwf h1.1
  rw [fdivBits_uitofp_pow hk22 hm1 hm2]
  have hP : opP d = mant * 2 ^ 1074 := by
    unfold opP
    rw [if_neg (by omega), ← hmant]
  have hD : opD d = 10 ^ k := by
    unfold opD
    rw [if_neg (by omega), ← hk]
  rw [hP, hD]

/-- The encoding a magnitude and sign have, as the bits: `toBits` is
`packMag`'s pattern. -/
theorem binary64_toBits_eq_packMag {c : Code} (hc : c.IsMag) (neg : Bool) :
    (Binary64.fin neg c.expField c.mant).toBits = (packMag (.fin c) neg).toNat := by
  rw [packMag_toNat_fin hc neg]
  simp only [Binary64.toBits, codeMant_eq, Nat.add_assoc]

/-- The zero mantissa's conversion: `uitofp` of zero is `+0`, whose pattern is
all zeroes.  The tier-1 class admits `0` (`"0"`, `"0.0e5"`), and the expression
is then `+0` on either side, which is why the product lemmas above are stated
at a positive mantissa and this is its own case. -/
theorem uitofpBits_zero : uitofpBits 0 = 0 := by
  have h0 : (0 : Nat) * 2 ^ 1074 = 0 := by rw [Nat.zero_mul]
  rw [uitofpBits, h0, roundMag_zero (by decide : 0 < 1)]
  rfl

/-- **The stored bits at the sign select.**  `%cond266` is
`if %tobool274.not = 1 then cond else fneg cond`; with `cond`'s bits the positive
`packMag` of the rounding and the sign reading `%tobool274.not = 1 ↔ ¬d.neg`,
the stored bits are `strtodSpec`'s. -/
theorem t1_store_bits {d : Decimal} {c : Code} (hc : c.IsMag)
    (hrc : roundMag d.ticks.1 d.ticks.2 = .fin c) {sign : BitVec 1}
    (hsign : (sign = 1) ↔ d.neg = false) :
    (if sign = 1 then packMag (.fin c) false else fnegBits (packMag (.fin c) false))
      = BitVec.ofNat 64 (strtodSpec d).toBits := by
  by_cases hs : sign = 1
  · rw [if_pos hs]
    have hd : d.neg = false := hsign.mp hs
    rw [strtodSpec_eq_binOf, hd, hrc]
    simp only [binOf, binary64_toBits_eq_packMag hc false, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  · rw [if_neg hs, fnegBits_packMag_false hc]
    have hd : d.neg = true := by
      cases hdn : d.neg
      · exact absurd (hsign.mpr hdn) hs
      · rfl
    rw [strtodSpec_eq_binOf, hd, hrc]
    simp only [binOf, binary64_toBits_eq_packMag hc true, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]

/-- `cleanup282.thread`, from its `findBlock` pin. -/
def t1Cleanup282ThreadInstrs : List Instr :=
  [Instr.phi "%cond" Ty.double [("cond.true", (Operand.reg "%mul258")),
                                ("cond.false", (Operand.reg "%div"))],
   Instr.fneg "%fneg" (Operand.reg "%cond"),
   Instr.select "%cond266" Ty.double (Operand.reg "%tobool274.not")
     (Operand.reg "%cond") (Operand.reg "%fneg"),
   Instr.store Ty.double (Operand.reg "%cond266") (Operand.reg "%out")]

theorem t1_findBlock_cleanup282_thread :
    numFastBody.findBlock "cleanup282.thread" =
      some ⟨"cleanup282.thread", t1Cleanup282ThreadInstrs, Term.br "cleanup300"⟩ := by
  simpa only [t1Cleanup282ThreadInstrs] using numFast_findBlock_cleanup282_thread

/-- The store block's environment: the selected `%cond`, its negation, and the
sign-selected `%cond266`. -/
def t1StoreEnv (env : Env) (c : BitVec 64) (sign : BitVec 1) : Env :=
  ("%cond266", .float (if sign = 1 then c else fnegBits c)) ::
  ("%fneg", .float (fnegBits c)) ::
  ("%cond", .float c) :: env

/-- `cleanup282.thread` from `cond.true`: the `phi`, the `fneg`, the sign select
and the store at `%out`. -/
theorem t1_cleanup282_thread_denote (calls : Calls) (env : Env) (s : State)
    {c : BitVec 64} {sign : BitVec 1} {out : Nat}
    (hpre : s.pre = some "cond.true")
    (hc : lookupName env "%mul258" = some (.float c))
    (hs : lookupName env "%tobool274.not" = some (.int 1 sign))
    (ho : lookupName env "%out" = some (.ptr out)) :
    denoteCode calls t1Cleanup282ThreadInstrs (stateAt env s) =
      some (stateAt (t1StoreEnv env c sign) ({ s with mem := writeBytes s.mem out (natToBytes (if sign = 1 then c else fnegBits c).toNat 8) })) := by
  unfold t1Cleanup282ThreadInstrs
  block_phi_run
  rotate_left 1
  · exact hpre
  · rfl
  · simp only [phiIncoming]; rfl
  · exact evalOperand_reg_of env s "%mul258" _ hc
  · simp only [runCells]
    rw [denoteCode_fneg _ _ _ "%fneg" "%cond" (by block_lk) _]
    rw [denoteCode_select_double _ _ _ "%cond266" "%tobool274.not" "%cond" "%fneg"
      (by block_lk) (by block_lk) (by block_lk) _]
    rw [denoteCode_store_double _ _ _ "%cond266" "%out" (by block_lk) (by block_lk) _]
    rw [denoteCode_nil]
    rfl

theorem t1_cleanup282_thread_step (calls : Calls) (env : Env) (s : State)
    {c : BitVec 64} {sign : BitVec 1} {out : Nat}
    (hpc : s.pc = "cleanup282.thread") (hpre : s.pre = some "cond.true")
    (hc : lookupName env "%mul258" = some (.float c))
    (hs : lookupName env "%tobool274.not" = some (.int 1 sign))
    (ho : lookupName env "%out" = some (.ptr out)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (t1StoreEnv env c sign) ({ s with mem := writeBytes s.mem out (natToBytes (if sign = 1 then c else fnegBits c).toNat 8), pc := "cleanup300", pre := some "cleanup282.thread" })) := by
  refine numFast_step_at
    (s' := stateAt (t1StoreEnv env c sign) ({ s with mem := writeBytes s.mem out (natToBytes (if sign = 1 then c else fnegBits c).toNat 8) }))
    (b := ⟨"cleanup282.thread", t1Cleanup282ThreadInstrs, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, t1Cleanup282ThreadInstrs]
      using t1_findBlock_cleanup282_thread
  · simpa only [denoteCode_nil]
      using t1_cleanup282_thread_denote calls env s hpre hc hs ho
  · simp only [execTerm, stateAt, hpc]

/-! ### The residual, named

Link 3 is stated at `%ip` and `%fr`; the tree proves the runs' *counts* and
carries the accumulators existentially (`JsonStage2NumFastDigitRuns`), so the
two registers at `if.end230` are the boundary's remaining tie.  This theorem is
that residual as a statement: if the tier-1 expression's one rounding is the
code `c` (which links 3 and 4 give when `%add244` is the mantissa and `%30` the
table row), the stored bits are `strtodSpec`'s. -/
theorem t1_tier1_store_of_accumulators {d : Decimal} {c : Code}
    (hrc : roundMag (opP d) (opD d) = .fin c) (hc : c.IsMag)
    {sign : BitVec 1} (hsign : (sign = 1) ↔ d.neg = false) :
    (if sign = 1 then packMag (.fin c) false else fnegBits (packMag (.fin c) false))
      = BitVec.ofNat 64 (strtodSpec d).toBits := by
  have hrc' : roundMag d.ticks.1 d.ticks.2 = .fin c := by
    rw [← opP_eq_ticks, ← opD_eq_ticks]; exact hrc
  exact t1_store_bits hc hrc' hsign

/-! ### Axiom footprints

Printed so the build records each link's footprint.  None is expected to carry
`sorryAx`; the exact-value declarations may carry `Classical.choice` through the
adapter's `Rat` construction, as `StrtodTier1` records. -/

#print axioms t1_add244_eq_mantissa
#print axioms t1_orCond304_bits
#print axioms t1_orCond306_bits
#print axioms t1_fmul_value
#print axioms t1_fdiv_value
#print axioms binary64_toBits_eq_packMag
#print axioms t1_store_bits
#print axioms t1_ifEnd230_denote
#print axioms t1_ifThen241_denote
#print axioms fmulBits_uitofp
#print axioms fdivBits_uitofp
#print axioms fdivBits_uitofp_pow
#print axioms pow10_uitofp_spec

end NumFastTier1

end LeanLLVM.Refinement
