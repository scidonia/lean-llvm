/-
The class dispatch and the kernel route.

`num_fast_el1` decides between its three arms at two range tests: `if.end230`'s
`%or.cond304` on the digit count and the exponent, and `if.then241`'s
`%or.cond306` on the narrower tier-1 window.  This module states those two
tests as the model's class predicates, then follows the kernel's route from the
outer gate to the end of its store.

1. **The counters' wrapped range algebra.**  `%add232` is the sum of the
   fraction's and the integer's digit counts and `%sub231` the exponent less the
   fraction's count; the two `icmp ult` tests at the block read them as a
   wrapped sixty-four-bit value.  Under the registers' own domain — a digit
   count below `2 ^ 64` and an exponent inside the signed range — the tests are
   the model's `digitCount` and `numEff` intervals (`ult_digitCount`,
   `ult_add45`, `ult_add22`), and both windows are proved as equivalences.
2. **The two class ties.**  `t1GateEnv` is the environment `if.end230` leaves
   and `t1MantEnv` the one `if.then241` leaves; the gate bits there are the
   model's `Tier1`/`Tier2Eligible`/`Fallback` tests (`numFast_gate304_iff`,
   `numFast_gate306_iff`) and, at the specification's own `eff`, the same
   (`numFast_gate304_iff_eff`, `numFast_gate306_iff_eff`).
3. **The kernel route.**  `if.then241`'s false edge reaches `if.end268`, whose
   kernel call is the guard's decision (`numFast_ifEnd268_accept`/`_refuse` in
   `JsonStage2NumFastTier2`); on the accept bit `cleanup282` loads the guard's
   eight bytes, applies the lexeme's sign and stores them at `%out`
   (`numFast_cleanup282_step_accept`), and `cleanup300` returns `1`.  On the
   refuse bit `cleanup282.thread462` ends the lifetime and reaches `if.end285`,
   the fallback's entry (`numFast_cleanup282_thread462_step`).
4. **The two seams.**  `numFast_tier2_accept_run` composes the accept route from
   the merge block to the return; `numFast_tier2_refuse_run` composes the
   refusal from the merge block to `if.end285`.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastTier2
import LeanLLVM.Refinement.JsonStage2NumFastTier1
import LeanLLVM.Refinement.JsonStage2NumFastBody

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open ByteString

/-! ### The counters' wrapped range algebra

`%add232`'s unsigned reading is the digit count and `%sub231`'s the emitted
exponent (`numFast_ifEnd230_counts`); the tests compare them as wrapped
sixty-four-bit values, so the intervals below carry the registers' own domain. -/

/-- An unsigned test on two registers, at the counts they were formed from. -/
theorem ult_ofNat {n m : Nat} (hn : n < 2 ^ 64) (hm : m < 2 ^ 64) :
    evalICmp .ult (BitVec.ofNat 64 n) (BitVec.ofNat 64 m) = 1 ↔ n < m := by
  rw [NumFastStarts.ult_iff_one]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm]

/-- `digitCount <u 20` is `digitCount ≤ 19` when the count fits the register. -/
theorem ult_digitCount {n : Nat} (hn : n < 2 ^ 64) :
    evalICmp .ult (BitVec.ofNat 64 n) (20#64) = 1 ↔ n ≤ 19 := by
  rw [ult_ofNat hn (by decide : 20 < 2 ^ 64)]
  omega

/-- `eff + 45 <u 91` is `-45 ≤ eff ≤ 45` at a sixty-four-bit signed value. -/
theorem ult_add45 {e : Int} (hr : -(2 ^ 63 : Int) ≤ e ∧ e < 2 ^ 63) :
    evalICmp .ult (BitVec.ofInt 64 e + (45#64)) (91#64) = 1 ↔
      -45 ≤ e ∧ e ≤ 45 := by
  rw [NumFastStarts.ult_iff_one]
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt,
    show (45#64).toNat = 45 from by decide, show (91#64).toNat = 91 from by decide]
  omega

/-- `eff + 22 <u 45` is `-22 ≤ eff ≤ 22` at the same domain. -/
theorem ult_add22 {e : Int} (hr : -(2 ^ 63 : Int) ≤ e ∧ e < 2 ^ 63) :
    evalICmp .ult (BitVec.ofInt 64 e + (22#64)) (45#64) = 1 ↔
      -22 ≤ e ∧ e ≤ 22 := by
  rw [NumFastStarts.ult_iff_one]
  simp only [BitVec.toNat_add, BitVec.toNat_ofInt,
    show (22#64).toNat = 22 from by decide, show (45#64).toNat = 45 from by decide]
  omega

/-- The conjunction's value: the select's two bits are the two tests. -/
theorem select_bit_and {b₁ b₂ : BitVec 1} :
    (if b₁ = 1 then b₂ else 0) = 1 ↔ b₁ = 1 ∧ b₂ = 1 := by
  by_cases h : b₁ = 1
  · rw [ite_eq_left h]
    exact ⟨fun hb => ⟨h, hb⟩, fun hh => hh.2⟩
  · rw [ite_eq_right h]
    exact ⟨fun h0 => absurd h0 (by decide), fun hh => absurd hh.1 h⟩

/-! ### The two class ties

The gate's environment is `NumFastTier1.t1GateEnv` — the five `phi`s, the two
counters and the four gate cells — and the inner window's is
`NumFastTier1.t1MantEnv` at the carried `%add232` and `%sub231`. -/

/-- The outer gate at `if.end230`'s environment: the block's `%or.cond304` is
`1` exactly when the lexeme is inside the outer window. -/
theorem numFast_gate304_iff {d : Decimal} {env : Env}
    {exp10 idig ip fr fdig : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hnd : digitCount d < 2 ^ 64)
    (hr : -(2 ^ 63 : Int) ≤ numEff d ∧ numEff d < 2 ^ 63) :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%or.cond304"
        = some (.int 1 1) ↔
      (digitCount d ≤ 19 ∧ -45 ≤ numEff d ∧ numEff d ≤ 45) := by
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) hE hF hI
  have hlk : lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%or.cond304"
      = some (.int 1
        (if evalICmp .ult (fdig + idig) (20#64) = 1 then
          evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0)) := by
    simp only [NumFastTier1.t1GateEnv]
    block_lk
  rw [hlk]
  simp only [Option.some.injEq, Value.int.injEq, true_and, heq_iff_eq]
  rw [select_bit_and]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hadd] at h1
    rw [hsub] at h2
    obtain ⟨hlo, hhi⟩ := (ult_add45 hr).mp h2
    exact ⟨(ult_digitCount hnd).mp h1, hlo, hhi⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_⟩
    · rw [hadd]
      exact (ult_digitCount hnd).mpr h1
    · rw [hsub]
      exact (ult_add45 hr).mpr ⟨h2, h3⟩

/-- The outer gate at the specification's `eff`: the same bit is the model's
`digitCount d ≤ 19 ∧ -45 ≤ eff d ≤ 45`. -/
theorem numFast_gate304_iff_eff {d : Decimal} {env : Env}
    {exp10 idig ip fr fdig : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hnd : digitCount d < 2 ^ 64)
    (hr : -(2 ^ 63 : Int) ≤ numEff d ∧ numEff d < 2 ^ 63) :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%or.cond304"
        = some (.int 1 1) ↔
      (digitCount d ≤ 19 ∧ -45 ≤ eff d ∧ eff d ≤ 45) := by
  rw [numFast_gate304_iff hE hF hI hnd hr]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have he : numEff d = eff d :=
      numEff_eq_eff_of_numGates h1 ⟨by omega, by omega⟩
    exact ⟨h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    have he : numEff d = eff d := numEff_eq_eff_of_specRange h1 ⟨h2, h3⟩
    exact ⟨h1, by omega, by omega⟩

/-- The inner window at `if.then241`'s environment: the block's `%or.cond306`
is `1` exactly when the lexeme is inside tier 1's window. -/
theorem numFast_gate306_iff {d : Decimal} {env : Env} {p10 : Nat}
    {exp10 idig ip fr fdig ten : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hnd : digitCount d < 2 ^ 64)
    (hr : -(2 ^ 63 : Int) ≤ numEff d ∧ numEff d < 2 ^ 63) :
    lookupName
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) "%or.cond306"
        = some (.int 1 1) ↔
      (digitCount d ≤ 15 ∧ -22 ≤ numEff d ∧ numEff d ≤ 22) := by
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) hE hF hI
  have hlk : lookupName
      (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
        p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) "%or.cond306"
      = some (.int 1
        (if evalICmp .ult (fdig + idig) (16#64) = 1 then
          evalICmp .ult ((exp10 - fdig) + (22#64)) (45#64) else 0)) := by
    simp only [NumFastTier1.t1MantEnv]
    block_lk
  rw [hlk]
  simp only [Option.some.injEq, Value.int.injEq, true_and, heq_iff_eq]
  rw [select_bit_and]
  constructor
  · rintro ⟨h1, h2⟩
    rw [hadd] at h1
    have h1' : digitCount d < 16 :=
      (ult_ofNat hnd (by decide : 16 < 2 ^ 64)).mp h1
    rw [hsub] at h2
    obtain ⟨hlo, hhi⟩ := (ult_add22 hr).mp h2
    exact ⟨by omega, hlo, hhi⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_⟩
    · rw [hadd]
      exact (ult_ofNat hnd (by decide : 16 < 2 ^ 64)).mpr (by omega)
    · rw [hsub]
      exact (ult_add22 hr).mpr ⟨h2, h3⟩

/-- The inner window at the specification's `eff`: the same bit is the model's
`digitCount d ≤ 15 ∧ -22 ≤ eff d ≤ 22`. -/
theorem numFast_gate306_iff_eff {d : Decimal} {env : Env} {p10 : Nat}
    {exp10 idig ip fr fdig ten : BitVec 64}
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hF : fdig = BitVec.ofNat 64 (fracDigits d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hnd : digitCount d < 2 ^ 64)
    (hr : -(2 ^ 63 : Int) ≤ numEff d ∧ numEff d < 2 ^ 63) :
    lookupName
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) "%or.cond306"
        = some (.int 1 1) ↔
      (digitCount d ≤ 15 ∧ -22 ≤ eff d ∧ eff d ≤ 22) := by
  rw [numFast_gate306_iff hE hF hI hnd hr]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have he : numEff d = eff d :=
      numEff_eq_eff_of_numGates (by omega) ⟨by omega, by omega⟩
    exact ⟨h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    have he : numEff d = eff d :=
      numEff_eq_eff_of_specRange (by omega) ⟨by omega, by omega⟩
    exact ⟨h1, by omega, by omega⟩


/-! ### The two gate steps' false edges

`if.end230` takes `if.end285` at a false outer bit and `if.then241` takes
`if.end268` at a false inner bit.  Both blocks' denotations are
`JsonStage2NumFastTier1`'s; these are their false-edge steps. -/

/-- `if.end230`'s false edge: the outer bit is zero, so the body leaves for the
fallback's entry. -/
theorem numFast_ifEnd230_step_false {calls : Calls} {env : Env} {s : State}
    {exp10 idig ip fr fdig : BitVec 64}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (he : lookupName env "%exp10.4" = some (.int 64 exp10))
    (hi : lookupName env "%idig.4" = some (.int 64 idig))
    (hip : lookupName env "%ip.5" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5" = some (.int 64 fr))
    (hfd : lookupName env "%fdig.4" = some (.int 64 fdig))
    (hbit : (if evalICmp .ult (fdig + idig) (20#64) = 1 then
        evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0) = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
        { s with pc := "if.end285", pre := some "if.end230" }) := by
  refine numFast_step_at (s' := stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) s)
    (b := ⟨"if.end230", numFastIfEnd230Instrs,
      Term.condbr (Operand.reg "%or.cond304") "if.then241" "if.end285"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastIfEnd230Instrs] using numFast_findBlock_if_end230
  · simpa only [denoteCode_nil] using
      NumFastTier1.t1_ifEnd230_denote calls env s hpre he hi hip hfr hfd
  · have hlk : lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%or.cond304"
        = some (.int 1
          (if evalICmp .ult (fdig + idig) (20#64) = 1 then
            evalICmp .ult ((exp10 - fdig) + (45#64)) (91#64) else 0)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%or.cond304" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-- `if.then241`'s false edge: the inner window's bit is zero, so the body
reaches the kernel's site. -/
theorem numFast_ifThen241_step_false {calls : Calls} {env : Env} {s : State}
    {p10 : Nat} {fdig ip fr add232 sub231 ten : BitVec 64}
    (hpc : s.pc = "if.then241")
    (hg : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hfd : lookupName env "%fdig.4719727" = some (.int 64 fdig))
    (hip : lookupName env "%ip.5708717729" = some (.int 64 ip))
    (hfr : lookupName env "%fr.5718728" = some (.int 64 fr))
    (had : lookupName env "%add232" = some (.int 64 add232))
    (hsu : lookupName env "%sub231" = some (.int 64 sub231))
    (hpos : (fdig.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (p10 + (fdig.signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8))
    (hbit : (if evalICmp .ult add232 (16#64) = 1 then
        evalICmp .ult (sub231 + (22#64)) (45#64) else 0) = 0) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (NumFastTier1.t1MantEnv env p10 fdig ip fr add232 sub231 ten)
        { s with pc := "if.end268", pre := some "if.then241" }) := by
  refine numFast_step_at
    (s' := stateAt (NumFastTier1.t1MantEnv env p10 fdig ip fr add232 sub231 ten) s)
    (b := ⟨"if.then241", NumFastTier1.t1IfThen241Instrs,
      Term.condbr (Operand.reg "%or.cond306") "if.then253" "if.end268"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, NumFastTier1.t1IfThen241Instrs] using
      NumFastTier1.t1_findBlock_ifThen241
  · simpa only [denoteCode_nil] using
      NumFastTier1.t1_ifThen241_denote calls env s hg hfd hip hfr had hsu hpos hread
  · have hlk : lookupName
        (NumFastTier1.t1MantEnv env p10 fdig ip fr add232 sub231 ten) "%or.cond306"
        = some (.int 1 (if evalICmp .ult add232 (16#64) = 1 then
            evalICmp .ult (sub231 + (22#64)) (45#64) else 0)) :=
      lookupName_cons_self ..
    rw [numFast_execTerm_condbr_zero _ "%or.cond306" _ _ hlk hbit]
    simp only [stateAt, hpc]

/-! ### The guard's code is a magnitude, and its bytes are the specification's

The kernel's encoding `tier2Bits` is the code's own field word; a code the guard
decides is a binary64 magnitude, so the positive pattern `packMag` reads back as
that word and the sign select turns it into `strtodSpec`'s bits. -/

/-- `roundMag`'s finite result is a binary64 magnitude. -/
theorem roundMag_fin_isMag {P d : Nat} {c : Code} (hd : 0 < d)
    (h : roundMag P d = .fin c) : c.IsMag := by
  unfold roundMag at h
  by_cases hov : overflowTicks * d ≤ P
  · rw [ite_eq_left hov] at h
    exact absurd h (by simp)
  · rw [ite_eq_right hov] at h
    by_cases hsub : P < d * 2 ^ 52
    · rw [ite_eq_left hsub] at h
      injection h with hc
      subst hc
      exact subCode_isMag hd hsub
    · rw [ite_eq_right hsub] at h
      injection h with hc
      subst hc
      exact normalCode_isMag hd hov hsub

/-- **The guard's decision is a binary64 magnitude.**  At zero the code is
`⟨0, 0⟩`; otherwise `elGuardRefinesOn` reads it as `roundMag`'s finite result. -/
theorem elTier2Code_isMag {w : Nat} {q : Int} {c : Code} (hw64 : w < 2 ^ 64)
    (h : LeanLLVM.ElGuardRefine.elTier2Code w q = some c) : c.IsMag := by
  by_cases hw : w = 0
  · unfold LeanLLVM.ElGuardRefine.elTier2Code at h
    dsimp only at h
    split at h
    · exact absurd h (by simp)
    · rw [ite_eq_left hw] at h
      injection h with hc
      subst hc
      exact Or.inl ⟨rfl, by decide⟩
  · have hpos : 0 < w := Nat.pos_of_ne_zero hw
    have hd : 0 < (LeanLLVM.ElGuardRefine.valueTicks w q).2 := by
      unfold LeanLLVM.ElGuardRefine.valueTicks
      split
      · exact Nat.one_pos
      · exact Nat.pow_pos (by decide)
    exact roundMag_fin_isMag hd
      (LeanLLVM.ElGuardRefine.elGuardRefinesOn w q c hpos hw64 h)

/-- The code's magnitude word is its field word: `Mag.toNat` at `codeBits`. -/
theorem mag_toNat_fin (c : Code) : (Mag.fin c).toNat = tier2Bits c := by
  simp only [Mag.toNat, tier2Bits, LeanLLVM.ElGuardRefine.codeBits]
  by_cases hE : c.expField = 0 <;> simp [hE]

/-- The positive pattern of a magnitude is its field word. -/
theorem ofNat_tier2Bits_eq_packMag {c : Code} (hc : c.IsMag) :
    BitVec.ofNat 64 (tier2Bits c) = packMag (.fin c) false := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, NumFastTier1.packMag_toNat_fin hc false]
  simp only [Bool.false_eq_true, reduceIte, Nat.zero_add]
  have hlt : tier2Bits c < 2 ^ 64 := by
    have hp : (packMag (.fin c) false).toNat = tier2Bits c := by
      rw [NumFastTier1.packMag_toNat_fin hc false]
      simp only [Bool.false_eq_true, reduceIte, Nat.zero_add]
      exact mag_toNat_fin c
    have := (packMag (.fin c) false).isLt
    rwa [hp] at this
  rw [Nat.mod_eq_of_lt hlt]
  exact (mag_toNat_fin c).symm

/-- A magnitude's field word is below `2 ^ 64`. -/
theorem tier2Bits_lt {c : Code} (hc : c.IsMag) : tier2Bits c < 2 ^ 64 := by
  have hp : (packMag (.fin c) false).toNat = tier2Bits c := by
    rw [NumFastTier1.packMag_toNat_fin hc false]
    simp only [Bool.false_eq_true, reduceIte, Nat.zero_add]
    exact mag_toNat_fin c
  have := (packMag (.fin c) false).isLt
  rwa [hp] at this

/-- `Binary64.toBits` at a finite code is the sign bit and the field word. -/
theorem fin_toBits_eq (c : Code) (neg : Bool) :
    (Binary64.fin neg c.expField c.mant).toBits
      = (if neg then 2 ^ 63 else 0) + tier2Bits c := by
  simp only [Binary64.toBits, tier2Bits, LeanLLVM.ElGuardRefine.codeBits]
  by_cases hE : c.expField = 0
  · simp [hE]
  · rw [ite_eq_right hE, ite_eq_right hE, Nat.add_assoc]

/-- **The accept's stored word is the specification's bits.**  The loaded word
is the guard's encoding, the `fneg` sets the pattern's sign bit
(`fnegBits_packMag_false`) and the select is the lexeme's sign, so the block's
store writes `strtodSpec`'s eight bytes. -/
theorem numFast_accept_words {d : Decimal} {c : Code} (hcM : c.IsMag)
    {sign : BitVec 1} (hsign : (sign = 1) ↔ d.neg = false)
    (hs : strtodSpec d = Binary64.fin d.neg c.expField c.mant) :
    (if sign = 1 then BitVec.ofNat 64 (tier2Bits c)
      else fnegBits (BitVec.ofNat 64 (tier2Bits c))).toNat
      = (strtodSpec d).toBits := by
  have hlt := tier2Bits_lt hcM
  have hx : (BitVec.ofNat 64 (tier2Bits c)).toNat = tier2Bits c := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [hs, fin_toBits_eq]
  by_cases hsig : sign = 1
  · rw [ite_eq_left hsig]
    have hd : d.neg = false := hsign.mp hsig
    rw [hd]
    simp only [Bool.false_eq_true, reduceIte, Nat.zero_add]
    exact hx
  · rw [ite_eq_right hsig]
    have hd : d.neg = true := by
      cases hdn : d.neg with
      | false => exact absurd (hsign.mpr hdn) hsig
      | true => rfl
    rw [hd]
    simp only [reduceIte]
    rw [ofNat_tier2Bits_eq_packMag hcM, NumFastTier1.fnegBits_packMag_false hcM,
      NumFastTier1.packMag_toNat_fin hcM true]
    simp only [ite_true]
    congr 1
    exact mag_toNat_fin c

/-! ### The accepting store block

`cleanup282` is the kernel's accepting arm: the counter `@g_nume1_el` is
incremented, the guard's eight bytes at `%d269` are loaded as a `double`, the
sign is applied and the word is stored at `%out`.  The block is read from its
pin and its denotation is the chain of those instructions. -/

/-- The conversion's call set answers the lifetime marker's end. -/
theorem stage2NumFastCalls_lifetime_end (epow : Int → Option EPow)
    (args : List Value) (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "llvm.lifetime.end.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := by
  simp only [stage2NumFastCalls, numFastCalls,
    ite_eq_right (by decide : ¬ ("llvm.lifetime.end.p0" = "num_d8_el1")),
    ite_eq_right (by decide : ¬ ("llvm.lifetime.end.p0" = "num_el_el1")),
    ite_eq_right (by decide : ¬ ("llvm.lifetime.end.p0" = "stk_mul_u64")),
    s2HelperCalls, JsonStage2IR.stage2Calls]

/-- The accepting block's last instruction: the kernel buffer's lifetime ends. -/
theorem denoteCode_lifetime_end (epow : Int → Option EPow) (env : Env) (s : State)
    {q : Nat} (hd : lookupName env "%d269" = some (.ptr q)) :
    denoteCode (stage2NumFastCalls epow)
      [Instr.callVoid "llvm.lifetime.end.p0"
        [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
         (Ty.ptr, (Operand.reg "%d269"))]] (stateAt env s) =
      some (stateAt env { s with mem := s.mem, next := s.next }) := by
  rw [denoteCode_callVoid_some (stage2NumFastCalls epow) env s "llvm.lifetime.end.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
     (Ty.ptr, (Operand.reg "%d269"))]
    [.int 64 0x0000000000000008#64, .ptr q]
    { ret := .int 1 0, mem := s.mem, next := s.next }
    (evalOperands_lifetimeMark (s := s) hd)
    (stage2NumFastCalls_lifetime_end _ _ _ _) []]
  rw [denoteCode_nil]

/-- `cleanup282`, from its `findBlock` pin. -/
def numFastCleanup282Instrs : List Instr :=
  [Instr.load "%35" (Ty.int 64) (Operand.global "@g_nume1_el"),
   Instr.binop "%inc273" (BinOp.add) 64 (Operand.reg "%35")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.store (Ty.int 64) (Operand.reg "%inc273") (Operand.global "@g_nume1_el"),
   Instr.load "%36" Ty.double (Operand.reg "%d269"),
   Instr.fneg "%fneg276" (Operand.reg "%36"),
   Instr.select "%cond279" Ty.double (Operand.reg "%tobool274.not")
     (Operand.reg "%36") (Operand.reg "%fneg276"),
   Instr.store Ty.double (Operand.reg "%cond279") (Operand.reg "%out"),
   Instr.callVoid "llvm.lifetime.end.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
      (Ty.ptr, (Operand.reg "%d269"))]]

theorem numFast_findBlock_cleanup282_named :
    numFastBody.findBlock "cleanup282" =
      some ⟨"cleanup282", numFastCleanup282Instrs, Term.br "cleanup300"⟩ := by
  simpa only [numFastCleanup282Instrs] using numFast_findBlock_cleanup282

/-- The accepting block's environment: the counter's old word, its successor,
the loaded word, its negation and the sign-selected value. -/
def numFastAcceptEnv (env : Env) (gv x : BitVec 64) (sign : BitVec 1) : Env :=
  ("%cond279", .float (if sign = 1 then x else fnegBits x)) ::
  ("%fneg276", .float (fnegBits x)) ::
  ("%36", .float x) ::
  ("%inc273", .int 64 (gv + 1)) ::
  ("%35", .int 64 gv) :: env

/-- The accepting block's memory: the counter's successor at `@g_nume1_el`, then
the sign-selected word at `%out`. -/
def numFastAcceptMem (s : State) (g out : Nat) (gv x : BitVec 64) (sign : BitVec 1) : State :=
  let m := (writeBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) out
    (natToBytes ((if sign = 1 then x else fnegBits x)).toNat 8))
  { s with mem := m }

/-- `%d = load i64, ptr @sym`: the global form of the word load. -/
theorem step_load64_global (calls : Calls) (env : Env) (s : State) (d sym : String)
    {a : Nat} {v : BitVec 64}
    (hp : lookupName env sym = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) :
    evalInstr calls (stateAt env s) (.load d (.int 64) (.global sym)) =
      some (stateAt ((d, .int 64 v) :: env) s) := by
  have hp' : evalOperand (stateAt env s) (.global sym) = some (.ptr a) := by
    simp only [evalOperand, stateAt, hp]
  have hv' : loadValue s.mem (.int 64) a = some (.int 64 v) := by
    rw [loadValue_i64_of_readBytes hv, natToBytes_toNat, pow256_eight,
      Nat.mod_eq_of_lt v.isLt]
    simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [JsonS1MasksIR.evalInstr_load (s := stateAt env s) (ty := .int 64)
    hp' (by simpa only [stateAt] using hv')]
  simp only [stateAt, State.bind]

theorem denoteCode_load64_global (calls : Calls) (env : Env) (s : State)
    (d sym : String) {a : Nat} {v : BitVec 64}
    (hp : lookupName env sym = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) (is : List Instr) :
    denoteCode calls (.load d (.int 64) (.global sym) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_load64_global calls env s d sym hp hv)]

/-- `store i64 %v, ptr @sym`: the global form of the word store. -/
theorem step_store64_global (calls : Calls) (env : Env) (s : State) (v sym : String)
    {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.int 64 x))
    (hp : lookupName env sym = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 64) (.reg v) (.global sym)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hp' : evalOperand (stateAt env s) (.global sym) = some (.ptr a) := by
    simp only [evalOperand, stateAt, hp]
  have hv' : evalOperand (stateAt env s) (.reg v) = some (.int 64 x) :=
    evalOperand_reg_of env s v (.int 64 x) hv
  have hs : storeValue (stateAt env s) (.int 64) (.int 64 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    simp [storeValue, stateAt]
  simp only [evalInstr, hv', hp', hs]

theorem denoteCode_store64_global (calls : Calls) (env : Env) (s : State)
    (v sym : String) {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.int 64 x))
    (hp : lookupName env sym = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.reg v) (.global sym) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_store64_global calls env s v sym hv hp)]

/-- The accepting block's denotation: the counter's successor at
`@g_nume1_el`, then the sign-selected word at `%out`. -/
theorem numFast_cleanup282_denote (epow : Int → Option EPow)
    (env : Env) (s : State) {g q out : Nat} {gv x : BitVec 64} {sign : BitVec 1}
    (hg : lookupName env "@g_nume1_el" = some (.ptr g))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hbuf : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) q 8
      = some (natToBytes x.toNat 8)) :
    denoteCode (stage2NumFastCalls epow) numFastCleanup282Instrs (stateAt env s) =
      some (stateAt (numFastAcceptEnv env gv x sign)
        (numFastAcceptMem s g out gv x sign)) := by
  unfold numFastCleanup282Instrs
  rw [denoteCode_load64_global _ _ _ "%35" "@g_nume1_el" hg hgv]
  rw [denoteCode_add_imm _ _ _ "%inc273" "%35" (by block_lk) _]
  rw [denoteCode_store64_global _ _ _ "%inc273" "@g_nume1_el" (by block_lk) (by block_lk) _]
  rw [NumFastTier1.denoteCode_load_double _ _ _ "%36" "%d269" (by block_lk) hbuf _]
  rw [NumFastTier1.denoteCode_fneg _ _ _ "%fneg276" "%36" (by block_lk) _]
  rw [NumFastTier1.denoteCode_select_double _ _ _ "%cond279" "%tobool274.not"
    "%36" "%fneg276" (by block_lk) (by block_lk) (by block_lk) _]
  rw [NumFastTier1.denoteCode_store_double _ _ _ "%cond279" "%out"
    (by block_lk) (by block_lk) _]
  have hdl : lookupName (numFastAcceptEnv env gv x sign) "%d269" = some (.ptr q) := by
    simp only [numFastAcceptEnv]
    repeat rw [lookupName_cons_ne _ _ (by decide)]
    exact hd
  have h := denoteCode_lifetime_end epow (numFastAcceptEnv env gv x sign)
    (numFastAcceptMem s g out gv x sign) hdl
  simp only [numFastAcceptEnv, numFastAcceptMem, stateAt] at h ⊢
  exact h

/-- The accepting block's step: the counter's successor is in the memory and
the body continues at `cleanup300`. -/
theorem numFast_cleanup282_step (epow : Int → Option EPow)
    (env : Env) (s : State) {g q out : Nat} {gv x : BitVec 64} {sign : BitVec 1}
    (hpc : s.pc = "cleanup282")
    (hg : lookupName env "@g_nume1_el" = some (.ptr g))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hbuf : readBytes (writeBytes s.mem g (natToBytes (gv + 1).toNat 8)) q 8
      = some (natToBytes x.toNat 8)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt (numFastAcceptEnv env gv x sign)
        ({ numFastAcceptMem s g out gv x sign with pc := "cleanup300", pre := some "cleanup282" })) := by
  refine numFast_step_at
    (s' := stateAt (numFastAcceptEnv env gv x sign)
      (numFastAcceptMem s g out gv x sign))
    (b := ⟨"cleanup282", numFastCleanup282Instrs, Term.br "cleanup300"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastCleanup282Instrs] using numFast_findBlock_cleanup282_named
  · simpa only [denoteCode_nil] using
      numFast_cleanup282_denote epow env s hg hd hsig hout hgv hbuf
  · simp only [execTerm, stateAt, hpc, numFastAcceptMem]

/-! ### The refusing exit block

`cleanup282.thread462` ends the kernel buffer's lifetime and branches to the
fallback's entry. -/

/-- `cleanup282.thread462`, from its `findBlock` pin. -/
def numFastCleanup282Thread462Instrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.end.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000008#64))),
      (Ty.ptr, (Operand.reg "%d269"))]]

theorem numFast_findBlock_cleanup282_thread462_named :
    numFastBody.findBlock "cleanup282.thread462" =
      some ⟨"cleanup282.thread462", numFastCleanup282Thread462Instrs,
        Term.br "if.end285"⟩ := by
  simpa only [numFastCleanup282Thread462Instrs]
    using numFast_findBlock_cleanup282_thread462

/-- The refusing block's denotation: the lifetime marker writes nothing. -/
theorem numFast_cleanup282_thread462_denote (epow : Int → Option EPow)
    (env : Env) (s : State) {q : Nat}
    (hd : lookupName env "%d269" = some (.ptr q)) :
    denoteCode (stage2NumFastCalls epow) numFastCleanup282Thread462Instrs (stateAt env s) =
      some (stateAt env { s with mem := s.mem, next := s.next }) := by
  simpa only [numFastCleanup282Thread462Instrs] using denoteCode_lifetime_end epow env s hd

/-- The refusing block's step: the body leaves for `if.end285`. -/
theorem numFast_cleanup282_thread462_step (epow : Int → Option EPow)
    (env : Env) (s : State) {q : Nat}
    (hpc : s.pc = "cleanup282.thread462")
    (hd : lookupName env "%d269" = some (.ptr q)) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt env { s with pc := "if.end285", pre := some "cleanup282.thread462" }) := by
  refine numFast_step_at (s' := stateAt env { s with mem := s.mem, next := s.next })
    (b := ⟨"cleanup282.thread462", numFastCleanup282Thread462Instrs,
      Term.br "if.end285"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc, numFastCleanup282Thread462Instrs]
      using numFast_findBlock_cleanup282_thread462_named
  · simpa only [denoteCode_nil] using
      numFast_cleanup282_thread462_denote epow env s hd
  · simp only [execTerm, stateAt, hpc]

/-! ### The kernel site's two edges

`if.end268` jumps at the kernel's own answer: the decision bit is zero on an
acceptance and one on a refusal, and the route's targets are the accepting store
and the refusing lifetime end. -/

/-- `if.end268`'s accepting edge: the block's bit is zero and the body continues
at `cleanup282` with the guard's eight bytes written at `%d269`. -/
theorem numFast_ifEnd268_step_accept (epow : Int → Option EPow)
    {env : Env} {s : State} {a b : BitVec 64} {q bits : Nat}
    (hpc : s.pc = "if.end268")
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hdec : numElEl1 epow a.toNat b.toInt = some bits) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt
        (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) :: env)
        { s with mem := writeBytes s.mem q (natToBytes bits 8), next := s.next, pc := "cleanup282", pre := some "if.end268" }) := by
  have hcode := numFast_ifEnd268_denote_accepted (s := s) epow ha hb hd hdec
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.end268", numFastIfEnd268Instrs,
        Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by
    rw [show (stateAt env s).pc = "if.end268" from hpc]
    exact numFast_findBlock_if_end268_named
  have hbit : lookupName
      (stateAt (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) :: env)
        { s with mem := writeBytes s.mem q (natToBytes bits 8), next := s.next }).env
      "%tobool271.not" = some (.int 1 0) := by
    simp only [stateAt, lookupName_cons_self]
  simp only [step, hfind, hcode]
  rw [numFast_execTerm_condbr_zero _ "%tobool271.not" _ _ hbit rfl]
  simp only [stateAt, hpc]

/-- `if.end268`'s refusing edge: the block's bit is one and the body continues
at `cleanup282.thread462` with the caller's memory. -/
theorem numFast_ifEnd268_step_refuse (epow : Int → Option EPow)
    {env : Env} {s : State} {a b : BitVec 64} {q : Nat}
    (hpc : s.pc = "if.end268")
    (ha : lookupName env "%add244" = some (.int 64 a))
    (hb : lookupName env "%sub231" = some (.int 64 b))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hdec : numElEl1 epow a.toNat b.toInt = none) :
    step (stage2NumFastCalls epow) numFastBody (stateAt env s) =
      .jump (stateAt
        (("%tobool271.not", .int 1 1) :: ("%call270", .int 32 0) :: env)
        { s with mem := s.mem, next := s.next, pc := "cleanup282.thread462", pre := some "if.end268" }) := by
  have hcode := numFast_ifEnd268_denote_refused (s := s) epow ha hb hd hdec
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.end268", numFastIfEnd268Instrs,
        Term.condbr (Operand.reg "%tobool271.not") "cleanup282.thread462" "cleanup282"⟩ := by
    rw [show (stateAt env s).pc = "if.end268" from hpc]
    exact numFast_findBlock_if_end268_named
  have hbit : lookupName
      (stateAt (("%tobool271.not", .int 1 1) :: ("%call270", .int 32 0) :: env)
        { s with mem := s.mem, next := s.next }).env
      "%tobool271.not" = some (.int 1 1) := by
    simp only [stateAt, lookupName_cons_self]
  simp only [step, hfind, hcode]
  rw [numFast_execTerm_condbr_one _ "%tobool271.not" _ _ hbit rfl]
  simp only [stateAt, hpc]

/-! ### Environment lookups through the route's cells

Each builder's cells are the block's own bindings, newest first; a name the
block did not bind falls through to the caller's environment.  These are the
lookups the route's hypotheses need at the state each step is stated at. -/

/-- The mantissa block's `%add244`. -/
theorem lookup_mant_add {env : Env} {p10 : Nat}
    {exp10 idig ip fr fdig ten : BitVec 64} :
    lookupName
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) "%add244"
      = some (.int 64 (ten * ip + fr)) := by
  simp only [NumFastTier1.t1MantEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

/-- The mantissa block's `%sub231`. -/
theorem lookup_mant_sub {env : Env} {p10 : Nat}
    {exp10 idig ip fr fdig ten : BitVec 64} :
    lookupName
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) "%sub231"
      = some (.int 64 (exp10 - fdig)) := by
  simp only [NumFastTier1.t1MantEnv, NumFastTier1.t1GateEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

/-- `natToBytes` reads a value through its low sixty-four bits. -/
theorem natToBytes_mod_pow256 (v n : Nat) : natToBytes (v % 256 ^ n) n = natToBytes v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [natToBytes, Nat.pow_succ']
      rw [show v % (256 * 256 ^ n) % 256 = v % 256 from Nat.mod_mul_right_mod v 256 (256 ^ n)]
      congr 1
      rw [show v % (256 * 256 ^ n) / 256 = v / 256 % 256 ^ n from
        Nat.mod_mul_right_div_self v 256 (256 ^ n)]
      exact ih (v / 256)

/-- `cleanup300`'s accepting edge from the kernel's store block: the same `1`, at
the `cleanup282` incoming the pin carries. -/
theorem numFast_cleanup300_denote_accept {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "cleanup282") :
    denoteCode calls numFastCleanup300Instrs (stateAt env s) =
      some (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  unfold numFastCleanup300Instrs
  block_eval

/-- The kernel's return at the accepting edge. -/
theorem numFast_step_cleanup300_accept {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "cleanup300") (hpre : s.pre = some "cleanup282") :
    step calls numFastBody (stateAt env s) =
      .ret (some (.int 32 1)) (stateAt (("%retval.8", .int 32 1) :: env) s) := by
  refine numFast_step_at
    (s' := stateAt (("%retval.8", .int 32 1) :: env) s)
    (b := ⟨"cleanup300", numFastCleanup300Instrs,
      Term.ret (Ty.int 32) (some (Operand.reg "%retval.8"))⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using numFast_findBlock_cleanup300
  · simpa only [denoteCode_nil] using
      numFast_cleanup300_denote_accept (calls := calls) (env := env) (s := s) hpre
  · simp only [execTerm, evalOperand, stateAt, lookupName_cons_self]
/-! ### The kernel arm

The accept route from the merge block: the outer gate's step, the inner window's
false edge, the kernel's acceptance and the accepting store, then the return. -/

/-- An eight-byte read is `readBytes` at its own bytes. -/
theorem readBytes_writeBytes_outside8 (m : Mem) (bs : List UInt8) :
    ∀ {start a k : Nat}, start + bs.length ≤ a ∨ a + k ≤ start →
      readBytes (writeBytes m start bs) a k = readBytes m a k
  | start, a, 0, _ => by simp only [readBytes]
  | start, a, k + 1, h => by
      have ha : a < start ∨ start + bs.length ≤ a := by
        rcases h with h | h
        · exact Or.inr h
        · exact Or.inl (by omega)
      simp only [readBytes]
      rw [readByte_writeBytes_outside m bs ha]
      cases hr : readByte m a with
      | none => rfl
      | some b =>
          have h' : start + bs.length ≤ a + 1 ∨ (a + 1) + k ≤ start := by
            rcases h with h | h
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          rw [readBytes_writeBytes_outside8 m bs (start := start) (a := a + 1) (k := k) h']

/-- A sign-extended sixty-four-bit count at its own value. -/
theorem sExt_ofNat64' {j : Nat} (hj : j < 2 ^ 63) :
    ((BitVec.ofNat 64 j).signExtend 64).toNat = j := by
  simp [BitVec.toNat_ofNat, BitVec.signExtend]
  omega

/-- The accepting arm's outcome: the return word `1` and its three writes. -/
def numFastTier2Out (s : State) (q g out : Nat) (gv : BitVec 64) (bits : Nat)
    (d : Decimal) : CallOutcome :=
  { ret := .int 32 1
    mem := writeBytes (writeBytes (writeBytes s.mem q (natToBytes bits 8)) g
      (natToBytes (gv + 1).toNat 8)) out (wordBytes 8 (strtodSpec d).toBits)
    next := s.next }

/-- The merge block's environment at the lexeme's counters. -/
def numFastGateAt (env : Env) (d : Decimal) (fs : Bytes) : Env :=
  NumFastTier1.t1GateEnv env (BitVec.ofInt 64 (expVal d)) (BitVec.ofNat 64 (intDigits d))
    (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) (BitVec.ofNat 64 (Decimal.digitsNat fs))
    (BitVec.ofNat 64 (fracDigits d))

/-- The mantissa block's environment at the same counters. -/
def numFastKernelAt (env : Env) (d : Decimal) (fs : Bytes) (p10 : Nat)
    (ten : BitVec 64) : Env :=
  NumFastTier1.t1MantEnv (numFastGateAt env d fs) p10 (BitVec.ofNat 64 (fracDigits d))
    (BitVec.ofNat 64 (Decimal.digitsNat d.ip)) (BitVec.ofNat 64 (Decimal.digitsNat fs))
    (BitVec.ofNat 64 (fracDigits d) + BitVec.ofNat 64 (intDigits d))
    (BitVec.ofInt 64 (expVal d) - BitVec.ofNat 64 (fracDigits d)) ten

/-- The kernel site's environment after a refusal. -/
def numFastKernelRefuseAt (env : Env) (d : Decimal) (fs : Bytes) (p10 : Nat)
    (ten : BitVec 64) : Env :=
  ("%tobool271.not", .int 1 1) :: ("%call270", .int 32 0) ::
    numFastKernelAt env d fs p10 ten

/-- The state `if.then241` leaves. -/
def numFastAtKernel (s : State) : State :=
  { s with pc := "if.end268", pre := some "if.then241" }

/-- The state `if.end268`'s acceptance leaves: the guard's bytes at `%d269`. -/
def numFastAtAcceptStore (s : State) (q bits : Nat) : State :=
  { s with mem := writeBytes s.mem q (natToBytes bits 8), next := s.next, pc := "cleanup282", pre := some "if.end268" }

/-- The state `if.end268`'s refusal leaves. -/
def numFastAtRefuseStore (s : State) : State :=
  { s with pc := "cleanup282.thread462", pre := some "if.end268" }

set_option maxHeartbeats 4000000 in

/-! ### The route's environment lookups

Each block's cells are named here once, so the route's statements read a lookup
at the block's own environment rather than a peeling term at every use. -/

theorem lookup_gate_fdig {env : Env} {exp10 idig ip fr fdig : BitVec 64} :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%fdig.4719727"
      = some (.int 64 fdig) := by
  simp only [NumFastTier1.t1GateEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

theorem lookup_gate_ip {env : Env} {exp10 idig ip fr fdig : BitVec 64} :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%ip.5708717729"
      = some (.int 64 ip) := by
  simp only [NumFastTier1.t1GateEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

theorem lookup_gate_fr {env : Env} {exp10 idig ip fr fdig : BitVec 64} :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "%fr.5718728"
      = some (.int 64 fr) := by
  simp only [NumFastTier1.t1GateEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rw [lookupName_cons_self]

theorem lookup_gate_p10 {env : Env} {exp10 idig ip fr fdig : BitVec 64} {p10 : Nat}
    (h : lookupName env "@NUMF_EL1_P10" = some (.ptr p10)) :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) "@NUMF_EL1_P10"
      = some (.ptr p10) := by
  simp only [NumFastTier1.t1GateEnv]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  exact h

theorem lookup_gate_tail {env : Env} {exp10 idig ip fr fdig : BitVec 64}
    {n : String} {v : Value}
    (h1 : "%or.cond304" ≠ n) (h2 : "%29" ≠ n) (h3 : "%28" ≠ n)
    (h4 : "%cmp233" ≠ n) (h5 : "%add232" ≠ n) (h6 : "%sub231" ≠ n)
    (h7 : "%fdig.4719727" ≠ n) (h8 : "%fr.5718728" ≠ n) (h9 : "%ip.5708717729" ≠ n)
    (h10 : "%idig.4709716730" ≠ n) (h11 : "%exp10.4731" ≠ n)
    (h : lookupName env n = some v) :
    lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) n = some v := by
  simp only [NumFastTier1.t1GateEnv]
  exact lookupName_cons_tail h1 (lookupName_cons_tail h2 (lookupName_cons_tail h3
    (lookupName_cons_tail h4 (lookupName_cons_tail h5 (lookupName_cons_tail h6
      (lookupName_cons_tail h7 (lookupName_cons_tail h8 (lookupName_cons_tail h9
        (lookupName_cons_tail h10 (lookupName_cons_tail h11 h))))))))))

theorem lookup_mant_tail {env : Env} {exp10 idig ip fr fdig : BitVec 64} {p10 : Nat}
    {ten : BitVec 64} {n : String} {v : Value}
    (h1 : "%or.cond306" ≠ n) (h2 : "%32" ≠ n) (h3 : "%31" ≠ n) (h4 : "%cmp245" ≠ n)
    (h5 : "%add244" ≠ n) (h6 : "%mul243" ≠ n) (h7 : "%30" ≠ n) (h8 : "%arrayidx242" ≠ n)
    (h : lookupName (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) n = some v) :
    lookupName
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten) n = some v := by
  simp only [NumFastTier1.t1MantEnv]
  exact lookupName_cons_tail h1 (lookupName_cons_tail h2 (lookupName_cons_tail h3
    (lookupName_cons_tail h4 (lookupName_cons_tail h5 (lookupName_cons_tail h6
      (lookupName_cons_tail h7 (lookupName_cons_tail h8 h)))))))

theorem lookup_two {env : Env} {k1 k2 : String} {w1 w2 : Value} {n : String} {v : Value}
    (h1 : k1 ≠ n) (h2 : k2 ≠ n) (h : lookupName env n = some v) :
    lookupName ((k1, w1) :: (k2, w2) :: env) n = some v :=
  lookupName_cons_tail h1 (lookupName_cons_tail h2 h)

/-- The state `cleanup300` is reached at: the accepting store's memory, at the
return block. -/
def numFastAtReturn (s : State) : State :=
  { s with pc := "cleanup300", pre := some "cleanup282" }

/-- The accepting store's memory is the outcome's: the three writes coincide. -/
theorem numFastAcceptMem_eq {d : Decimal} {c : Code} (hcM : c.IsMag)
    {sign : BitVec 1} (hsign : (sign = 1) ↔ d.neg = false)
    (hspec : strtodSpec d = Binary64.fin d.neg c.expField c.mant)
    (s : State) (q g out : Nat) (gv : BitVec 64) :
    (numFastAcceptMem (numFastAtAcceptStore s q (tier2Bits c)) g out gv
        (BitVec.ofNat 64 (tier2Bits c)) sign).mem
      = (numFastTier2Out s q g out gv (tier2Bits c) d).mem := by
  simp only [numFastAcceptMem, numFastAtAcceptStore, numFastTier2Out,
    wordBytes, numFast_accept_words hcM hsign hspec]

/-- The accepting arm's frame at its three stores: the counter's slot, the
kernel's buffer and the output word are the only regions the route writes. -/
theorem numFastTier2OutMem_frame (s : State) (q g out err : Nat) (gv : BitVec 64)
    (c : Code) (d : Decimal) :
    UnchangedOutside s.mem
      (writeBytes (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8)) out (wordBytes 8 (strtodSpec d).toBits))
      [(q, 8), (g, 8), (out, 8), (err, 8)] := by
  have h1 : UnchangedOutside s.mem
      (writeBytes s.mem q (natToBytes (tier2Bits c) 8))
      [(q, 8), (g, 8), (out, 8), (err, 8)] :=
    (UnchangedOutside.refl' s.mem [(q, 8), (g, 8), (out, 8), (err, 8)]).write_le
      (a := q) (w := 8) (bs := natToBytes (tier2Bits c) 8)
      ⟨(q, 8), by simp, le_rfl, by omega⟩ (by simp only [natToBytes_length]; omega)
  have h2 : UnchangedOutside (writeBytes s.mem q (natToBytes (tier2Bits c) 8))
      (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8))
      [(q, 8), (g, 8), (out, 8), (err, 8)] :=
    (UnchangedOutside.refl' (writeBytes s.mem q (natToBytes (tier2Bits c) 8))
      [(q, 8), (g, 8), (out, 8), (err, 8)]).write_le
      (a := g) (w := 8) (bs := natToBytes (gv + 1).toNat 8)
      ⟨(g, 8), by simp, le_rfl, by omega⟩ (by simp only [natToBytes_length]; omega)
  have h3 : UnchangedOutside
      (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8))
      (writeBytes (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8)) out (wordBytes 8 (strtodSpec d).toBits))
      [(q, 8), (g, 8), (out, 8), (err, 8)] :=
    (UnchangedOutside.refl'
      (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8))
      [(q, 8), (g, 8), (out, 8), (err, 8)]).write_le
      (a := out) (w := 8) (bs := wordBytes 8 (strtodSpec d).toBits)
      ⟨(out, 8), by simp, le_rfl, by omega⟩
        (by simp only [wordBytes, natToBytes_length]; omega)
  exact (h1.trans' h2).trans' h3

set_option maxHeartbeats 2000000 in
/-- The kernel's route from the merge block's environment, at the model's
counters: four control steps from `if.then241` to the return. -/
theorem numFast_tier2_chain {env : Env} {s : State} {d : Decimal} {fs : Bytes}
    {exp10 idig ip fr fdig : BitVec 64} {sign : BitVec 1} {out g q p10 err : Nat}
    {gv ten : BitVec 64} {c : Code}
    (hc : LeanLLVM.ElGuardRefine.elTier2Code d.mantissa (eff d) = some c)
    (hpc : s.pc = "if.then241") (hpre : s.pre = some "if.end230")
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hip : ip = BitVec.ofNat 64 (Decimal.digitsNat d.ip))
    (hfr : fr = BitVec.ofNat 64 (Decimal.digitsNat fs))
    (hfd : fdig = BitVec.ofNat 64 (fracDigits d))
    (hfs : d.fr = some fs)
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hg : lookupName env "@g_nume1_el" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + (fdig.signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8))
    (hdisj : q + 8 ≤ g ∨ g + 8 ≤ q)
    (hipb : Decimal.digitsNat d.ip < 2 ^ 64)
    (hfsb : Decimal.digitsNat (d.fr.getD empty) < 2 ^ 64)
    (h10 : 10 ^ fs.length < 2 ^ 64)
    (hmbound : d.mantissa < 2 ^ 64)
    (hwf : d.wellFormed) (h2 : Tier2 d kernelDecides)
    (hsign : (sign = 1) ↔ d.neg = false) :
    runFuel (stage2NumFastCalls guardTable) 4 numFastBody
      (stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) s) =
      some (.ret (some (.int 32 1))
        (numFastTier2Out s q g out gv (tier2Bits c) d).mem) ∧
    UnchangedOutside s.mem
      (writeBytes (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8)) out (wordBytes 8 (strtodSpec d).toBits))
      [(q, 8), (g, 8), (out, 8), (err, 8)] ∧
    numClassOf (digitCount d) (numEff d) (kernelDecides d) = .kernel := by
  have hT2 : Tier2 d kernelDecides := h2
  obtain ⟨hnt1, helig, hk⟩ := h2
  obtain ⟨hnd19, hlo45, hhi45⟩ := helig
  have hnd : digitCount d < 2 ^ 64 := by omega
  have hneff : numEff d = eff d := numEff_eq_eff_of_specRange (by omega) ⟨hlo45, hhi45⟩
  have hrE : -(2 ^ 63 : Int) ≤ eff d ∧ eff d < 2 ^ 63 := by omega
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) hE hfd hI
  have hb306ne : (if evalICmp .ult (fdig + idig) (16#64) = 1 then
      evalICmp .ult ((exp10 - fdig) + (22#64)) (45#64) else 0) ≠ 1 := by
    intro h
    obtain ⟨h1, h2⟩ := select_bit_and.mp h
    rw [hadd] at h1
    rw [hsub, hneff] at h2
    have h16 : digitCount d < 16 := (ult_ofNat hnd (by decide)).mp h1
    obtain ⟨hlo, hhi⟩ := (ult_add22 hrE).mp h2
    exact hnt1 ⟨by omega, by omega, by omega⟩
  have hb306 : (if evalICmp .ult (fdig + idig) (16#64) = 1 then
      evalICmp .ult ((exp10 - fdig) + (22#64)) (45#64) else 0) = 0 := by
    rcases bitVec1_eq_zero_or_one _ with h | h
    · exact h
    · exact absurd h hb306ne
  have hfsget : d.fr.getD empty = fs := by rw [hfs]; rfl
  have hfrac : fracDigits d ≤ 19 := fracDigits_le_nineteen hnd19
  have hsE : (fdig.signExtend 64).toNat = fracDigits d := by
    rw [hfd]; exact sExt_ofNat64' (by omega)
  have hpos : (fdig.signExtend 64).toNat < 2 ^ 63 := by rw [hsE]; omega
  have hmant : ten * ip + fr = BitVec.ofNat 64 d.mantissa :=
    NumFastTier1.t1_add244_eq_mantissa (d := d) (ip := ip) (ten := ten) (fr := fr)
      hip (by rw [hfsget]; exact hfr) (by rw [hfsget]; exact hten) hipb
      (by simpa only [hfsget] using hfsb) (by rw [hfsget]; exact h10) hmbound
  have hexp : exp10 - fdig = BitVec.ofInt 64 (eff d) := by rw [hsub, hneff]
  have hdec : numElEl1 guardTable (ten * ip + fr).toNat (exp10 - fdig).toInt
      = some (tier2Bits c) := by
    have hv := numFast_ifEnd268_value (d := d) (a := ten * ip + fr) (b := exp10 - fdig)
      hmant hexp hwf hnd19 hrE
    rw [hv, hc]
    rfl
  have hcM : c.IsMag := elTier2Code_isMag (by omega) hc
  have hspec : strtodSpec d = Binary64.fin d.neg c.expField c.mant := by
    have hbin : numTier2Binary d = Binary64.fin d.neg c.expField c.mant := by
      unfold numTier2Binary
      rw [← StrtodTier1.eff_eq_exponent, hc]
    rw [← numTier2Binary_eq_strtodSpec hwf hnd19 hk]
    exact hbin
  have hgv1 : readBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g 8
      = some (natToBytes gv.toNat 8) := by
    refine (readBytes_writeBytes_outside8 s.mem (natToBytes (tier2Bits c) 8)
      (start := q) (a := g) (k := 8) ?_).trans hgv
    rw [natToBytes_length]
    rcases hdisj with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hxnat : (BitVec.ofNat 64 (tier2Bits c)).toNat = tier2Bits c % 2 ^ 64 := by
    rw [BitVec.toNat_ofNat]
  have hbuf : readBytes
      (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8)) q 8
      = some (natToBytes (BitVec.ofNat 64 (tier2Bits c)).toNat 8) := by
    rw [readBytes_writeBytes_outside8 (writeBytes s.mem q (natToBytes (tier2Bits c) 8))
      (natToBytes (gv + 1).toNat 8) (start := g) (a := q) (k := 8) (by
        rw [natToBytes_length]
        rcases hdisj with h | h
        · exact Or.inr h
        · exact Or.inl h)]
    have hsame : readBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) q 8
        = some (natToBytes (tier2Bits c) 8) := by
      simpa only [natToBytes_length] using
        (readBytes_writeBytes_same s.mem (natToBytes (tier2Bits c) 8) (addr := q))
    rw [hsame]
    congr 1
    rw [hxnat]
    have hmod := natToBytes_mod_pow256 (tier2Bits c) 8
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide] at hmod
    rw [← hmod]
  have hstep1 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) s) =
      .jump (stateAt
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
        { s with pc := "if.end268", pre := some "if.then241" }) :=
    numFast_ifThen241_step_false (calls := stage2NumFastCalls guardTable)
      (env := NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) (s := s)
      (p10 := p10) (fdig := fdig) (ip := ip) (fr := fr)
      (add232 := fdig + idig) (sub231 := exp10 - fdig) (ten := ten)
      hpc (lookup_gate_p10 hp10) lookup_gate_fdig lookup_gate_ip lookup_gate_fr
      (NumFastTier1.t1GateEnv_add env exp10 idig ip fr fdig)
      (NumFastTier1.t1GateEnv_sub env exp10 idig ip fr fdig) hpos hrow10 hb306
  have hstep2 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt
        (NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
        { s with pc := "if.end268", pre := some "if.then241" }) =
      .jump (stateAt
        (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
          NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
            p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
        (numFastAtAcceptStore s q (tier2Bits c))) :=
    numFast_ifEnd268_step_accept guardTable
      (env := NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
        p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
      (s := { s with pc := "if.end268", pre := some "if.then241" })
      (a := ten * ip + fr) (b := exp10 - fdig) (q := q) (bits := tier2Bits c) rfl
      lookup_mant_add
      (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (NumFastTier1.t1GateEnv_sub env exp10 idig ip fr fdig))
      (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (lookup_gate_tail (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd))
      hdec
  have hstep3 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt
        (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
          NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
            p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
        (numFastAtAcceptStore s q (tier2Bits c))) =
      .jump (stateAt
        (numFastAcceptEnv
          (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
            NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
              p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
          gv (BitVec.ofNat 64 (tier2Bits c)) sign)
        (numFastAtReturn
          (numFastAcceptMem (numFastAtAcceptStore s q (tier2Bits c)) g out gv
            (BitVec.ofNat 64 (tier2Bits c)) sign))) :=
    numFast_cleanup282_step guardTable
      (env := ("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
        NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
          p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
      (s := numFastAtAcceptStore s q (tier2Bits c))
      (g := g) (q := q) (out := out) (gv := gv)
      (x := BitVec.ofNat 64 (tier2Bits c)) (sign := sign) rfl
      (lookup_two (by decide) (by decide)
        (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (lookup_gate_tail (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hg)))
      (lookup_two (by decide) (by decide)
        (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (lookup_gate_tail (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd)))
      (lookup_two (by decide) (by decide)
        (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (lookup_gate_tail (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsig)))
      (lookup_two (by decide) (by decide)
        (lookup_mant_tail (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (lookup_gate_tail (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hout)))
      hgv1 hbuf
  have hstep4 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt
        (numFastAcceptEnv
          (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
            NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
              p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
          gv (BitVec.ofNat 64 (tier2Bits c)) sign)
        (numFastAtReturn
          (numFastAcceptMem (numFastAtAcceptStore s q (tier2Bits c)) g out gv
            (BitVec.ofNat 64 (tier2Bits c)) sign))) =
      .ret (some (.int 32 1))
        (stateAt
          (("%retval.8", .int 32 1) ::
            numFastAcceptEnv
              (("%tobool271.not", .int 1 0) :: ("%call270", .int 32 1) ::
                NumFastTier1.t1MantEnv (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig)
                  p10 fdig ip fr (fdig + idig) (exp10 - fdig) ten)
              gv (BitVec.ofNat 64 (tier2Bits c)) sign)
          (numFastAtReturn
            (numFastAcceptMem (numFastAtAcceptStore s q (tier2Bits c)) g out gv
              (BitVec.ofNat 64 (tier2Bits c)) sign))) :=
    numFast_step_cleanup300_accept rfl rfl
  refine ⟨?_, ?_, numClassOf_kernel hT2⟩
  · rw [show (4 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix hstep1 3]
    rw [show (3 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix hstep2 2]
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix hstep3 1]
    simp only [runFuel]
    rw [hstep4]
    simp only [stateAt, numFastAtReturn]
    rw [numFastAcceptMem_eq (d := d) (c := c) hcM hsign hspec s q g out gv]
  · exact numFastTier2OutMem_frame s q g out err gv c d


/-- The kernel's refusing route, from the merge block's environment at the
model's counters: three control steps from `if.then241` to `if.end285`'s entry. -/
theorem numFast_tier2_refuse_chain {env : Env} {s : State} {d : Decimal} {fs : Bytes}
    {exp10 idig ip fr fdig : BitVec 64} {q p10 : Nat} {ten : BitVec 64}
    (hpc : s.pc = "if.then241") (hpre : s.pre = some "if.end230")
    (hE : exp10 = BitVec.ofInt 64 (expVal d))
    (hI : idig = BitVec.ofNat 64 (intDigits d))
    (hip : ip = BitVec.ofNat 64 (Decimal.digitsNat d.ip))
    (hfr : fr = BitVec.ofNat 64 (Decimal.digitsNat fs))
    (hfd : fdig = BitVec.ofNat 64 (fracDigits d))
    (hfs : d.fr = some fs)
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + (fdig.signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8))
    (hipb : Decimal.digitsNat d.ip < 2 ^ 64)
    (hfsb : Decimal.digitsNat (d.fr.getD empty) < 2 ^ 64)
    (h10 : 10 ^ fs.length < 2 ^ 64)
    (hmbound : d.mantissa < 2 ^ 64)
    (hwf : d.wellFormed) (hnt1 : ¬ Tier1 d) (helig : Tier2Eligible d)
    (hk : kernelDecides d = false) :
    ∃ e : State, e.pc = "if.end285" ∧ e.pre = some "cleanup282.thread462" ∧
      e.mem = s.mem ∧ e.next = s.next ∧
      numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback ∧
      ∀ k, runFuel (stage2NumFastCalls guardTable) (3 + k) numFastBody
        (stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) s) =
        runFuel (stage2NumFastCalls guardTable) k numFastBody e := by
  obtain ⟨hnd19, hlo45, hhi45⟩ := helig
  have hnd : digitCount d < 2 ^ 64 := by omega
  have hneff : numEff d = eff d := numEff_eq_eff_of_specRange (by omega) ⟨hlo45, hhi45⟩
  have hrE : -(2 ^ 63 : Int) ≤ eff d ∧ eff d < 2 ^ 63 := by omega
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) hE hfd hI
  have hb306ne : (if evalICmp .ult (fdig + idig) (16#64) = 1 then
      evalICmp .ult ((exp10 - fdig) + (22#64)) (45#64) else 0) ≠ 1 := by
    intro h
    obtain ⟨h1, h2⟩ := select_bit_and.mp h
    rw [hadd] at h1
    rw [hsub, hneff] at h2
    have h16 : digitCount d < 16 := (ult_ofNat hnd (by decide)).mp h1
    obtain ⟨hlo, hhi⟩ := (ult_add22 hrE).mp h2
    exact hnt1 ⟨by omega, by omega, by omega⟩
  have hb306 : (if evalICmp .ult (fdig + idig) (16#64) = 1 then
      evalICmp .ult ((exp10 - fdig) + (22#64)) (45#64) else 0) = 0 := by
    rcases bitVec1_eq_zero_or_one _ with h | h
    · exact h
    · exact absurd h hb306ne
  have hfsget : d.fr.getD empty = fs := by rw [hfs]; rfl
  have hfrac : fracDigits d ≤ 19 := fracDigits_le_nineteen hnd19
  have hsE : (fdig.signExtend 64).toNat = fracDigits d := by
    rw [hfd]; exact sExt_ofNat64' (by omega)
  have hpos : (fdig.signExtend 64).toNat < 2 ^ 63 := by rw [hsE]; omega
  have hmant : ten * ip + fr = BitVec.ofNat 64 d.mantissa :=
    NumFastTier1.t1_add244_eq_mantissa (d := d) (ip := ip) (ten := ten) (fr := fr)
      hip (by rw [hfsget]; exact hfr) (by rw [hfsget]; exact hten) hipb
      (by simpa only [hfsget] using hfsb) (by rw [hfsget]; exact h10) hmbound
  have hexp : exp10 - fdig = BitVec.ofInt 64 (eff d) := by rw [hsub, hneff]
  have hks : LeanLLVM.ElGuardRefine.elTier2Code d.mantissa (eff d) = none := by
    have hs := hk
    unfold kernelDecides at hs
    rw [← StrtodTier1.eff_eq_exponent] at hs
    cases hh : LeanLLVM.ElGuardRefine.elTier2Code d.mantissa (eff d) with
    | none => rfl
    | some c => rw [hh] at hs; exact absurd hs (by simp)
  have hdec : numElEl1 guardTable (ten * ip + fr).toNat (exp10 - fdig).toInt = none := by
    have hv := numFast_ifEnd268_value (d := d) (a := ten * ip + fr) (b := exp10 - fdig)
      hmant hexp hwf hnd19 hrE
    rw [hv, hks]
    rfl
  have hclass : numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback :=
    numClassOf_fallback ⟨hnt1, Or.inr hk⟩
  have hstep1 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt (NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) s) =
      .jump (stateAt (numFastKernelAt env d fs p10 ten) (numFastAtKernel s)) := by
    simpa only [numFastKernelAt, numFastAtKernel, numFastGateAt, stateAt,
      hE, hI, hip, hfr, hfd] using
      (numFast_ifThen241_step_false (calls := stage2NumFastCalls guardTable)
        (env := NumFastTier1.t1GateEnv env exp10 idig ip fr fdig) (s := s)
        (p10 := p10) (fdig := fdig) (ip := ip) (fr := fr)
        (add232 := fdig + idig) (sub231 := exp10 - fdig) (ten := ten)
        hpc
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        (by simp only [NumFastTier1.t1GateEnv]; block_lk)
        hpos hrow10 hb306)
  have hstep2 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt (numFastKernelAt env d fs p10 ten) (numFastAtKernel s)) =
      .jump (stateAt (numFastKernelRefuseAt env d fs p10 ten) (numFastAtRefuseStore s)) :=
    numFast_ifEnd268_step_refuse guardTable
      (env := numFastKernelAt env d fs p10 ten) (s := numFastAtKernel s)
      (a := ten * ip + fr) (b := exp10 - fdig) (q := q) rfl
      (by
        have h := lookup_mant_add (env := env) (exp10 := exp10) (idig := idig)
          (ip := ip) (fr := fr) (fdig := fdig) (p10 := p10) (ten := ten)
        simpa only [numFastKernelAt, numFastGateAt, hE, hI, hip, hfr, hfd] using h)
      (by simpa only [numFastKernelAt, numFastGateAt, hE, hI, hip, hfr, hfd] using (lookup_mant_sub
        (env := env) (exp10 := exp10) (idig := idig) (ip := ip) (fr := fr)
        (fdig := fdig) (p10 := p10) (ten := ten)))
      (by
        simp only [numFastKernelAt, numFastGateAt, NumFastTier1.t1MantEnv,
          NumFastTier1.t1GateEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hd)
      hdec
  have hstep3 : step (stage2NumFastCalls guardTable) numFastBody
      (stateAt (numFastKernelRefuseAt env d fs p10 ten) (numFastAtRefuseStore s)) =
      .jump (stateAt (numFastKernelRefuseAt env d fs p10 ten)
        ({ numFastAtKernel s with pc := "if.end285", pre := some "cleanup282.thread462" })) :=
    numFast_cleanup282_thread462_step guardTable
      (env := numFastKernelRefuseAt env d fs p10 ten) (s := numFastAtRefuseStore s)
      (q := q) rfl
      (by
        simp only [numFastKernelRefuseAt, numFastKernelAt, numFastGateAt,
          NumFastTier1.t1MantEnv, NumFastTier1.t1GateEnv]
        repeat rw [lookupName_cons_ne _ _ (by decide)]
        exact hd)
  refine ⟨stateAt (numFastKernelRefuseAt env d fs p10 ten)
      ({ numFastAtKernel s with pc := "if.end285", pre := some "cleanup282.thread462" }),
    rfl, rfl, rfl, rfl, hclass, ?_⟩
  intro k
  rw [show (3 : Nat) + k = 1 + (2 + k) from by omega,
    runFuel_jump_prefix hstep1 (2 + k)]
  rw [show (2 : Nat) + k = 1 + (1 + k) from by omega,
    runFuel_jump_prefix hstep2 (1 + k)]
  exact runFuel_jump_prefix hstep3 k


set_option maxHeartbeats 2000000 in
/-- The kernel's accepting arm, from the merge block: five control steps to the
return, with the guard's eight bytes at `%d269`, the counter's successor at
`@g_nume1_el` and `strtodSpec`'s bytes at `%out`. -/
theorem numFast_tier2_accept_run {env : Env} {s : State} {d : Decimal} {fs : Bytes}
    {sign : BitVec 1} {out g q p10 err : Nat} {gv ten : BitVec 64} {c : Code}
    (hc : LeanLLVM.ElGuardRefine.elTier2Code d.mantissa (eff d) = some c)
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (hE : lookupName env "%exp10.4" = some (.int 64 (BitVec.ofInt 64 (expVal d))))
    (hI : lookupName env "%idig.4" = some (.int 64 (BitVec.ofNat 64 (intDigits d))))
    (hip : lookupName env "%ip.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))))
    (hfr : lookupName env "%fr.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))))
    (hfd : lookupName env "%fdig.4"
      = some (.int 64 (BitVec.ofNat 64 (fracDigits d))))
    (hfs : d.fr = some fs)
    (hsig : lookupName env "%tobool274.not" = some (.int 1 sign))
    (hout : lookupName env "%out" = some (.ptr out))
    (hg : lookupName env "@g_nume1_el" = some (.ptr g))
    (hgv : readBytes s.mem g 8 = some (natToBytes gv.toNat 8))
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hdisj : q + 8 ≤ g ∨ g + 8 ≤ q)
    (hipb : Decimal.digitsNat d.ip < 2 ^ 64)
    (hfsb : Decimal.digitsNat (d.fr.getD empty) < 2 ^ 64)
    (h10 : 10 ^ fs.length < 2 ^ 64)
    (hmbound : d.mantissa < 2 ^ 64)
    (hwf : d.wellFormed) (h2 : Tier2 d kernelDecides)
    (hsign : (sign = 1) ↔ d.neg = false) :
    runFuel (stage2NumFastCalls guardTable) 5 numFastBody (stateAt env s) =
      some (.ret (some (.int 32 1))
        (numFastTier2Out s q g out gv (tier2Bits c) d).mem) ∧
    UnchangedOutside s.mem
      (writeBytes (writeBytes (writeBytes s.mem q (natToBytes (tier2Bits c) 8)) g
        (natToBytes (gv + 1).toNat 8)) out (wordBytes 8 (strtodSpec d).toBits))
      [(q, 8), (g, 8), (out, 8), (err, 8)] ∧
    numClassOf (digitCount d) (numEff d) (kernelDecides d) = .kernel := by
  obtain ⟨hnt1, helig, hk⟩ := h2
  obtain ⟨hnd19, hlo45, hhi45⟩ := helig
  have hnd : digitCount d < 2 ^ 64 := by omega
  have hneff : numEff d = eff d := numEff_eq_eff_of_specRange (by omega) ⟨hlo45, hhi45⟩
  have hrE : -(2 ^ 63 : Int) ≤ eff d ∧ eff d < 2 ^ 63 := by omega
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) rfl rfl rfl
  have hbit1 : evalICmp .ult
      (BitVec.ofNat 64 (fracDigits d) + BitVec.ofNat 64 (intDigits d)) (20#64) = 1 := by
    rw [hadd]; exact (ult_digitCount hnd).mpr (by omega)
  have hbit2 : evalICmp .ult
      (BitVec.ofInt 64 (expVal d) - BitVec.ofNat 64 (fracDigits d) + (45#64)) (91#64) = 1 := by
    rw [hsub, hneff]; exact (ult_add45 hrE).mpr ⟨hlo45, hhi45⟩
  have h1 : step (stage2NumFastCalls guardTable) numFastBody (stateAt env s) =
      .jump (stateAt
        (NumFastTier1.t1GateEnv env (BitVec.ofInt 64 (expVal d))
          (BitVec.ofNat 64 (intDigits d)) (BitVec.ofNat 64 (Decimal.digitsNat d.ip))
          (BitVec.ofNat 64 (Decimal.digitsNat fs)) (BitVec.ofNat 64 (fracDigits d)))
        { s with pc := "if.then241", pre := some "if.end230" }) :=
    NumFastTier1.t1_ifEnd230_step (stage2NumFastCalls guardTable) env s hpc hpre hE hI hip hfr hfd
      ⟨hbit2, hbit1⟩
  have hrow10' : readBytes s.mem
      (p10 + ((BitVec.ofNat 64 (fracDigits d)).signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8) := by
    have hfrac : fracDigits d ≤ 19 := fracDigits_le_nineteen hnd19
    rw [sExt_ofNat64' (by omega)]; exact hrow10
  obtain ⟨hrun, hframe, hclass⟩ := numFast_tier2_chain (d := d) (fs := fs)
    (exp10 := BitVec.ofInt 64 (expVal d)) (idig := BitVec.ofNat 64 (intDigits d))
    (ip := BitVec.ofNat 64 (Decimal.digitsNat d.ip))
    (fr := BitVec.ofNat 64 (Decimal.digitsNat fs)) (fdig := BitVec.ofNat 64 (fracDigits d))
    (sign := sign) (out := out) (g := g) (q := q) (p10 := p10) (err := err)
    (gv := gv) (ten := ten) (c := c) hc
    (s := { s with pc := "if.then241", pre := some "if.end230" }) rfl rfl
    rfl rfl rfl rfl rfl hfs hsig hout hg hgv hp10 hd hten hrow10' hdisj hipb hfsb h10 hmbound
    hwf (show Tier2 d kernelDecides from ⟨hnt1, ⟨hnd19, hlo45, hhi45⟩, hk⟩) hsign
  refine ⟨?_, hframe, hclass⟩
  rw [show (5 : Nat) = 1 + 4 from rfl, runFuel_jump_prefix h1 4]
  exact hrun
set_option maxHeartbeats 2000000 in
/-- The kernel's refusing arm, from the merge block: four control steps to
`if.end285`'s entry, the caller's memory and the fallback's class. -/
theorem numFast_tier2_refuse_run {env : Env} {s : State} {d : Decimal} {fs : Bytes}
    {q p10 : Nat} {ten : BitVec 64}
    (hpc : s.pc = "if.end230") (hpre : s.pre = some "if.end226")
    (hE : lookupName env "%exp10.4" = some (.int 64 (BitVec.ofInt 64 (expVal d))))
    (hI : lookupName env "%idig.4" = some (.int 64 (BitVec.ofNat 64 (intDigits d))))
    (hip : lookupName env "%ip.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))))
    (hfr : lookupName env "%fr.5"
      = some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat fs))))
    (hfd : lookupName env "%fdig.4"
      = some (.int 64 (BitVec.ofNat 64 (fracDigits d))))
    (hfs : d.fr = some fs)
    (hp10 : lookupName env "@NUMF_EL1_P10" = some (.ptr p10))
    (hd : lookupName env "%d269" = some (.ptr q))
    (hten : ten = BitVec.ofNat 64 (10 ^ fs.length))
    (hrow10 : readBytes s.mem (p10 + fracDigits d * 8) 8
      = some (natToBytes ten.toNat 8))
    (hipb : Decimal.digitsNat d.ip < 2 ^ 64)
    (hfsb : Decimal.digitsNat (d.fr.getD empty) < 2 ^ 64)
    (h10 : 10 ^ fs.length < 2 ^ 64)
    (hmbound : d.mantissa < 2 ^ 64)
    (hwf : d.wellFormed) (hnt1 : ¬ Tier1 d) (helig : Tier2Eligible d)
    (hk : kernelDecides d = false) :
    ∃ e : State, e.pc = "if.end285" ∧ e.pre = some "cleanup282.thread462" ∧
      e.mem = s.mem ∧ e.next = s.next ∧
      numClassOf (digitCount d) (numEff d) (kernelDecides d) = .fallback ∧
      ∀ k, runFuel (stage2NumFastCalls guardTable) (4 + k) numFastBody (stateAt env s) =
        runFuel (stage2NumFastCalls guardTable) k numFastBody e := by
  obtain ⟨hnd19, hlo45, hhi45⟩ := helig
  have hnd : digitCount d < 2 ^ 64 := by omega
  have hneff : numEff d = eff d := numEff_eq_eff_of_specRange (by omega) ⟨hlo45, hhi45⟩
  have hrE : -(2 ^ 63 : Int) ≤ eff d ∧ eff d < 2 ^ 63 := by omega
  obtain ⟨hadd, hsub⟩ := numFast_ifEnd230_counts (d := d) rfl rfl rfl
  have hbit1 : evalICmp .ult
      (BitVec.ofNat 64 (fracDigits d) + BitVec.ofNat 64 (intDigits d)) (20#64) = 1 := by
    rw [hadd]; exact (ult_digitCount hnd).mpr (by omega)
  have hbit2 : evalICmp .ult
      (BitVec.ofInt 64 (expVal d) - BitVec.ofNat 64 (fracDigits d) + (45#64)) (91#64) = 1 := by
    rw [hsub, hneff]; exact (ult_add45 hrE).mpr ⟨hlo45, hhi45⟩
  have h1 : step (stage2NumFastCalls guardTable) numFastBody (stateAt env s) =
      .jump (stateAt
        (NumFastTier1.t1GateEnv env (BitVec.ofInt 64 (expVal d))
          (BitVec.ofNat 64 (intDigits d)) (BitVec.ofNat 64 (Decimal.digitsNat d.ip))
          (BitVec.ofNat 64 (Decimal.digitsNat fs)) (BitVec.ofNat 64 (fracDigits d)))
        { s with pc := "if.then241", pre := some "if.end230" }) :=
    NumFastTier1.t1_ifEnd230_step (stage2NumFastCalls guardTable) env s hpc hpre hE hI hip hfr hfd
      ⟨hbit2, hbit1⟩
  have hrow10' : readBytes s.mem
      (p10 + ((BitVec.ofNat 64 (fracDigits d)).signExtend 64).toNat * 8) 8
      = some (natToBytes ten.toNat 8) := by
    have hfrac : fracDigits d ≤ 19 := fracDigits_le_nineteen hnd19
    rw [sExt_ofNat64' (by omega)]; exact hrow10
  have hElig : Tier2Eligible d := ⟨hnd19, hlo45, hhi45⟩
  obtain ⟨e, hepc, hepre, hemem, henext, hclass, hrun⟩ :=
    numFast_tier2_refuse_chain (d := d) (fs := fs)
      (exp10 := BitVec.ofInt 64 (expVal d)) (idig := BitVec.ofNat 64 (intDigits d))
      (ip := BitVec.ofNat 64 (Decimal.digitsNat d.ip))
      (fr := BitVec.ofNat 64 (Decimal.digitsNat fs)) (fdig := BitVec.ofNat 64 (fracDigits d))
      (q := q) (p10 := p10) (ten := ten)
      (s := { s with pc := "if.then241", pre := some "if.end230" }) rfl rfl
      rfl rfl rfl rfl rfl hfs hp10 hd hten hrow10' hipb hfsb h10 hmbound hwf hnt1 hElig hk
  refine ⟨e, hepc, hepre, ?_, ?_, hclass, ?_⟩
  · rw [← hemem]
  · rw [← henext]
  · intro k
    rw [show (4 : Nat) + k = 1 + (3 + k) from by omega,
      runFuel_jump_prefix h1 (3 + k)]
    exact hrun k

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.numFast_gate304_iff_eff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_gate304_iff_eff

/-- info: 'LeanLLVM.Refinement.numFast_gate306_iff_eff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_gate306_iff_eff

/-- info: 'LeanLLVM.Refinement.numFast_tier2_accept_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_tier2_accept_run

/-- info: 'LeanLLVM.Refinement.numFast_tier2_refuse_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numFast_tier2_refuse_run

end LeanLLVM.Refinement
