/-
# The head byte's class, transported into the default arm's three routes

`HcontClass` (`JsonStage2WalkDispatchHcontArms`) selects the head switch's arm from one
comparison tree and splits its default arm by the tag test.  The default arm's continuations
below `if.else387.i` read a *different* set of bits on the same byte: the route to the
letters span, to `'f'` or to the class-C span is decided by `slt %8 110` and `eq %8 102`,
and the seam's tag test (`eq %8 45 ||| ult (%8 + 208) 10`) decides whether the walk takes
the plain-value arm instead.  Those bits are functions of the byte, so they are the
class's — but they are not *fields* of the class's constructors, and the branch theorems
in `JsonStage2WalkDispatchClassCase` therefore still take them as premises.

This module is the transport: from a constructor's range bits and the derived signed and
unsigned readings of the byte, it produces exactly the premises each default route's branch
needs — the tag test clear, `slt %8 110`, `eq %8 102` (or its negation), `slt %8 116` and
`eq %8 116`, and `slt %8 125`.  Each branch below takes one `HcontClass` constructor's
fields, builds the head chain from the payload's document row at those bits, and returns
the arm the corresponding branch produces.  So the class case that reads
`HcontClass.complete` has a branch at every default-value class, and the only facts it
passes are the class's own fields.

## The arithmetic, named once

`evalICmp` is `BitVec.ofBool` of the underlying comparison, so an `icmp` result is `1`
exactly when the comparison holds and `0` exactly when it fails.  The readings below turn
that into `toInt`/`toNat` propositions, and `omega` then carries the range from the class's
pivots to the route's tests.  The signed order is the program's (`icmp slt`), so the byte's
negative half is *below* every positive literal, which is why the low class's `%8 < 44`
covers `128 … 255` as well as `0 … 43`.

The tag test's unsigned half is the one non-linear step: `(%8 + 208) u< 10` means
`%8 ∈ {48, …, 57}` as an `i8`, and a byte at or above `58` (or below `44`) is outside it.
`tag_zero_of_toInt_ge_58` and `tag_zero_of_toInt_lt_44` state the two cases as `toNat`
arithmetic, rewriting `(%8 + 208).toNat` by `BitVec.toNat_add`, so the modular sum is a
`toNat - 48` residue rather than a symbolic modulus.  `toNat_eq_of_toInt_nonneg` is the
byte's signed/unsigned bridge at the non-negative half, and `toNat_ge_128_of_toInt_neg` the
negative half's.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassCase
import LeanLLVM.Refinement.JsonStage2WalkDispatchDefaultLane

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The byte's readings

The literals the comparisons use are fixed, so their `toInt` readings are computations;
the simp set makes `simpa` reduce a comparison's bound to the number written in the
program. -/

@[simp] theorem toInt_8_34 : (BitVec.ofNat 8 34).toInt = 34 := by decide
@[simp] theorem toInt_8_44 : (BitVec.ofNat 8 44).toInt = 44 := by decide
@[simp] theorem toInt_8_45 : (BitVec.ofNat 8 45).toInt = 45 := by decide
@[simp] theorem toInt_8_58 : (BitVec.ofNat 8 58).toInt = 58 := by decide
@[simp] theorem toInt_8_91 : (BitVec.ofNat 8 91).toInt = 91 := by decide
@[simp] theorem toInt_8_93 : (BitVec.ofNat 8 93).toInt = 93 := by decide
@[simp] theorem toInt_8_102 : (BitVec.ofNat 8 102).toInt = 102 := by decide
@[simp] theorem toInt_8_110 : (BitVec.ofNat 8 110).toInt = 110 := by decide
@[simp] theorem toInt_8_116 : (BitVec.ofNat 8 116).toInt = 116 := by decide
@[simp] theorem toInt_8_123 : (BitVec.ofNat 8 123).toInt = 123 := by decide
@[simp] theorem toInt_8_124 : (BitVec.ofNat 8 124).toInt = 124 := by decide
@[simp] theorem toInt_8_125 : (BitVec.ofNat 8 125).toInt = 125 := by decide
@[simp] theorem toInt_8_13 : (BitVec.ofNat 8 13).toInt = 13 := by decide
@[simp] theorem toInt_8_32 : (BitVec.ofNat 8 32).toInt = 32 := by decide
@[simp] theorem toInt_8_208 : (BitVec.ofNat 8 208).toInt = (-48 : Int) := by decide
@[simp] theorem toInt_8_10 : (BitVec.ofNat 8 10).toInt = 10 := by decide

/-- `icmp slt` at one is the signed order. -/
theorem toInt_lt_of_slt_one {w : Nat} {x a : BitVec w}
    (h : evalICmp .slt x a = 1) : x.toInt < a.toInt := by
  by_contra hc
  have h0 : evalICmp .slt x a = 0 := by simp [evalICmp, BitVec.slt_eq_decide, hc]
  rw [h] at h0
  exact absurd h0 (by decide)

/-- `icmp slt` at zero is the negated signed order. -/
theorem toInt_ge_of_slt_zero {w : Nat} {x a : BitVec w}
    (h : evalICmp .slt x a = 0) : a.toInt ≤ x.toInt := by
  by_contra hc
  have hlt : x.toInt < a.toInt := lt_of_not_ge hc
  have h1 : evalICmp .slt x a = 1 := by simp [evalICmp, BitVec.slt_eq_decide, hlt]
  rw [h] at h1
  exact absurd h1 (by decide)

/-- The signed order at one. -/
theorem slt_one_of_toInt_lt {w : Nat} {x a : BitVec w}
    (h : x.toInt < a.toInt) : evalICmp .slt x a = 1 := by
  simp [evalICmp, BitVec.slt_eq_decide, h]

/-- The signed order at zero. -/
theorem slt_zero_of_toInt_ge {w : Nat} {x a : BitVec w}
    (h : a.toInt ≤ x.toInt) : evalICmp .slt x a = 0 := by
  simp [evalICmp, BitVec.slt_eq_decide, not_lt.mpr h]

/-- Equality at zero, from the signed readings. -/
theorem eq_zero_of_toInt_ne {w : Nat} {x c : BitVec w}
    (h : x.toInt ≠ c.toInt) : evalICmp .eq x c = 0 := by
  have hne : x ≠ c := by
    intro he
    exact h (by rw [he])
  simp [evalICmp, hne]

/-- Two equal words compare equal. -/
theorem eq_one_of_eq {w : Nat} {x c : BitVec w} (h : x = c) : evalICmp .eq x c = 1 := by
  subst h
  simp [evalICmp]

/-- Equality at zero reads as unequal signed values. -/
theorem toInt_ne_of_eq_zero {w : Nat} {x c : BitVec w}
    (h : evalICmp .eq x c = 0) : x.toInt ≠ c.toInt := by
  intro he
  have hx : x = c := BitVec.toInt_inj.mp he
  have h1 : evalICmp .eq x c = 1 := eq_one_of_eq hx
  rw [h] at h1
  exact absurd h1 (by decide)

/-- Equality at one reads as equal signed values. -/
theorem toInt_eq_of_eq_one {w : Nat} {x c : BitVec w}
    (h : evalICmp .eq x c = 1) : x.toInt = c.toInt := by
  by_contra hc
  have h0 : evalICmp .eq x c = 0 := eq_zero_of_toInt_ne (x := x) (c := c) hc
  rw [h] at h0
  exact absurd h0 (by decide)

/-- `icmp ult` at zero is the negated unsigned order.  This is the same reading
`JsonEscapeDecodeRun`'s `evalICmp_ult_zero_iff` gives, restated here because the walk's
modules do not import the escape chain. -/
theorem ult_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ult x y = (0 : BitVec 1) ↔ ¬ x.toNat < y.toNat := by
  unfold evalICmp
  cases hb : BitVec.ult x y
  · have h : ¬ x.toNat < y.toNat := by
      intro hlt
      have htrue : BitVec.ult x y = true := (BitVec.ult_iff_toNat_lt).2 hlt
      rw [htrue] at hb
      exact Bool.noConfusion hb
    simp [h]
  · have h : x.toNat < y.toNat := by
      rw [← BitVec.ult_iff_toNat_lt]
      exact hb
    simp [h]

/-- A non-negative signed reading is the unsigned one: the byte's top bit is clear. -/
theorem toNat_lt_128_of_toInt_nonneg {x : BitVec 8} (h : 0 ≤ x.toInt) :
    x.toNat < 128 := by
  have hlt := x.isLt
  by_contra hc
  have hge : 128 ≤ x.toNat := by omega
  have hcond : ¬ 2 * x.toNat < 2 ^ 8 := by omega
  have hto : x.toInt = (x.toNat : Int) - ((2 ^ 8 : Nat) : Int) := by
    rw [show BitVec.toInt x
        = if 2 * x.toNat < 2 ^ 8 then (x.toNat : Int)
          else (x.toNat : Int) - ((2 ^ 8 : Nat) : Int) from rfl]
    rw [ite_eq_right hcond]
  rw [hto] at h
  have h2 : ((2 ^ 8 : Nat) : Int) = 256 := by decide
  omega

/-- The signed reading equals `toNat` on the byte's non-negative half. -/
theorem toNat_eq_of_toInt_nonneg {x : BitVec 8} (h : 0 ≤ x.toInt) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_of_lt]
  have := toNat_lt_128_of_toInt_nonneg h
  omega

/-- A negative signed reading puts the byte in `128 … 255`. -/
theorem toNat_ge_128_of_toInt_neg {x : BitVec 8} (h : x.toInt < 0) :
    128 ≤ x.toNat := by
  by_contra hc
  have hlt128 : x.toNat < 128 := by omega
  have hti : x.toInt = (x.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]
    omega
  omega

/-! ### The tag test at the two ranges the default classes occupy -/

/-- A byte at or above `58` in the signed order is not `45` and not `48 … 57`, so the
seam's tag test is clear.  `toNat` is `toInt` here because the byte is non-negative, and
`toNat + 208` rewrites as `256 + (toNat - 48)`, whose residue is `toNat - 48 ≥ 10`. -/
theorem tag_zero_of_toInt_ge_58 {x : BitVec 8} (h : 58 ≤ x.toInt) :
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  have hti : x.toInt = (x.toNat : Int) := toNat_eq_of_toInt_nonneg (by omega)
  have hn : 58 ≤ x.toNat := by omega
  have hne45 : evalICmp .eq x (BitVec.ofNat 8 45) = 0 := by
    apply eq_zero_of_toInt_ne
    simp only [toInt_8_45]
    omega
  have hult : evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 0 := by
    rw [ult_zero_iff, BitVec.toNat_add]
    have h208 : (BitVec.ofNat 8 208).toNat = 208 := by decide
    have h10 : (BitVec.ofNat 8 10).toNat = 10 := by decide
    rw [h208, h10]
    have hlt := x.isLt
    have hsplit : x.toNat + 208 = 2 ^ 8 + (x.toNat - 48) := by omega
    rw [hsplit, Nat.add_mod_left]
    have hlt2 : x.toNat - 48 < 2 ^ 8 := by omega
    rw [Nat.mod_eq_of_lt hlt2]
    omega
  rw [hne45, hult]
  decide

/-- A byte below `44` in the signed order is either `0 … 43` or, being negative,
`128 … 255`; neither is `45` and neither is in `48 … 57`, so the tag test is clear. -/
theorem tag_zero_of_toInt_lt_44 {x : BitVec 8} (h : x.toInt < 44) :
    (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0 := by
  have hne45 : evalICmp .eq x (BitVec.ofNat 8 45) = 0 := by
    apply eq_zero_of_toInt_ne
    simp only [toInt_8_45]
    omega
  have hult : evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) = 0 := by
    rw [ult_zero_iff, BitVec.toNat_add]
    have h208 : (BitVec.ofNat 8 208).toNat = 208 := by decide
    have h10 : (BitVec.ofNat 8 10).toNat = 10 := by decide
    rw [h208, h10]
    have hlt := x.isLt
    by_cases hpos : 0 ≤ x.toInt
    · have hti := toNat_eq_of_toInt_nonneg hpos
      have hn : x.toNat ≤ 43 := by omega
      have hsum : x.toNat + 208 < 2 ^ 8 := by omega
      rw [Nat.mod_eq_of_lt hsum]
      omega
    · have hneg : x.toInt < 0 := lt_of_not_ge hpos
      have hge := toNat_ge_128_of_toInt_neg hneg
      have hsplit : x.toNat + 208 = 2 ^ 8 + (x.toNat - 48) := by omega
      rw [hsplit, Nat.add_mod_left]
      have hlt2 : x.toNat - 48 < 2 ^ 8 := by omega
      rw [Nat.mod_eq_of_lt hlt2]
      omega
  rw [hne45, hult]
  decide

/-! ### The default-value branches

Each branch takes one `HcontClass` constructor's fields (as `HcontClass.complete` produces
them), the payload's default document row and a non-whitespace byte class, and returns the
arm.  The route facts are derived from the class's range bits by the readings above.

The classes are the **tag-clear** default arms: `defaultValueLow`, `defaultValueMid`,
`otherValue`, `defaultValueBracket`, `defaultValueBracketHigh` and `defaultValueBrace`.
`value` is the tag-set arm and is `.scalar`'s (its `HcontScalarPrefix` is the relevant
row); `defaultValueHigh` is the `.ws`/`.cleanup` pair's class.  Neither is a route below
`if.else387.i`, so neither appears here. -/

/-- **`.defaultValueLow`** — the byte's signed reading is below `44`, so its route is the
letters span and its tag test is clear. -/
theorem hcontArm_defaultValueLow {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1)
    (hne34 : evalICmp .eq x (BitVec.ofNat 8 34) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx44 : x.toInt < 44 := by simpa using toInt_lt_of_slt_one h44
  have hbit := tag_zero_of_toInt_lt_44 (x := x) hx44
  have h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0 :=
    eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let ch := lowHeadChain_of_lane hInv hblock hk h8 h91 h44 hne34 hbit r hb
  exact hcontArm_letters_of_class hInv hk h8 hbit h110 hne102 ch hc

/-- **`.defaultValueMid`** — `58 < %8 < 91`, so the route is the letters span. -/
theorem hcontArm_defaultValueMid {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 0)
    (hne58 : evalICmp .eq x (BitVec.ofNat 8 58) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx91 : x.toInt < 91 := by simpa using toInt_lt_of_slt_one h91
  have hge58 : 58 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h58
  have hbit := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0 :=
    eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let ch := midHeadChain_of_lane hInv hblock hk h8 h91 h44 h58 hne58 hbit r hb
  exact hcontArm_letters_of_class hInv hk h8 hbit h110 hne102 ch hc

/-- **`.otherValue`** — the tag-clear half of `HeadArm.defaultValue`: `44 ≤ %8 < 58` and
`%8 ≠ 44`, which excludes the tag-set bytes, so the route is the letters span.  The tag
bit is the constructor's own field. -/
theorem hcontArm_otherValue {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (h44 : evalICmp .slt x (BitVec.ofNat 8 44) = 0)
    (h58 : evalICmp .slt x (BitVec.ofNat 8 58) = 1)
    (hne44 : evalICmp .eq x (BitVec.ofNat 8 44) = 0)
    (hbit : (evalICmp .eq x (BitVec.ofNat 8 45) |||
      evalICmp .ult (x + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx58 : x.toInt < 58 := by simpa using toInt_lt_of_slt_one h58
  have h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0 :=
    eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let ch := othHeadChain_of_lane hInv hblock hk h8 h91 h44 h58 hne44 hbit r hb
  exact hcontArm_letters_of_class hInv hk h8 hbit h110 hne102 ch hc

/-- **`.defaultValueBracket`** — the byte `92`, whose route is the letters span. -/
theorem hcontArm_defaultValueBracket {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 1)
    (hne91 : evalICmp .eq x (BitVec.ofNat 8 91) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx93 : x.toInt < 93 := by simpa using toInt_lt_of_slt_one h93
  have hge91 : 91 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h91
  have hne91' : x.toInt ≠ 91 := by simpa using toInt_ne_of_eq_zero hne91
  have hbit := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have h110 : evalICmp .slt x (BitVec.ofNat 8 110) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0 :=
    eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 102)
      (by simp only [toInt_8_102]; omega)
  let ch := brkHeadChain_of_lane hInv hblock hk h8 h91 h123 h93 hne91 hbit r hb
  exact hcontArm_letters_of_class hInv hk h8 hbit h110 hne102 ch hc

/-- **`.defaultValueBracketHigh`** — `94 … 122`, the one default class whose byte spans two
routes: `'f'` at `102`, the letters span below `110` (and not `102`), and the class-C span
from `110` on.  The class-C span's four leaves are selected by the same dispatch the
emitted `LeafBlock56`/`LeafBlock58` pair performs. -/
theorem hcontArm_defaultValueBracketHigh {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 1)
    (h93 : evalICmp .slt x (BitVec.ofNat 8 93) = 0)
    (hne93 : evalICmp .eq x (BitVec.ofNat 8 93) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hx123 : x.toInt < 123 := by simpa using toInt_lt_of_slt_one h123
  have hge93 : 93 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h93
  have hne93' : x.toInt ≠ 93 := by simpa using toInt_ne_of_eq_zero hne93
  have hbit := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have h125one : evalICmp .slt x (BitVec.ofNat 8 125) = 1 :=
    slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 125)
      (by simp only [toInt_8_125]; omega)
  let ch := bhHeadChain_of_lane hInv hblock hk h8 h91 h123 h93 hne93 hbit r hb
  by_cases h110one : evalICmp .slt x (BitVec.ofNat 8 110) = 1
  · by_cases h102one : evalICmp .eq x (BitVec.ofNat 8 102) = 1
    · exact hcontArm_fLetter_of_class hInv hk h8 hbit h110one h102one ch hc
    · have hne102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0 := bitZeroOfNeOne h102one
      exact hcontArm_letters_of_class hInv hk h8 hbit h110one hne102 ch hc
  · have h110zero : evalICmp .slt x (BitVec.ofNat 8 110) = 0 := bitZeroOfNeOne h110one
    have h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq x (BitVec.ofNat 8 125) = 1 := Or.inl h125one
    by_cases h110eq : evalICmp .eq x (BitVec.ofNat 8 110) = 1
    · have h116one : evalICmp .slt x (BitVec.ofNat 8 116) = 1 :=
        slt_one_of_toInt_lt (x := x) (a := BitVec.ofNat 8 116) (by
          have hx110 : x.toInt = 110 := by
            have := toInt_eq_of_eq_one h110eq
            simpa using this
          simp only [toInt_8_116]
          omega)
      exact hcontArm_classC_56True_of_class hInv hk h8 h110zero h116one h110eq h125 ch hc
    · have h110eqz : evalICmp .eq x (BitVec.ofNat 8 110) = 0 := bitZeroOfNeOne h110eq
      by_cases h116one : evalICmp .slt x (BitVec.ofNat 8 116) = 1
      · exact hcontArm_classC_56Else_of_class hInv hk h8 h110zero h116one h110eqz h125 ch hc
      · have h116zero : evalICmp .slt x (BitVec.ofNat 8 116) = 0 := bitZeroOfNeOne h116one
        by_cases h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 1
        · exact hcontArm_classC_58True_of_class hInv hk h8 h110zero h116zero h116eq h125 ch hc
        · exact hcontArm_classC_58Else_of_class hInv hk h8 h110zero h116zero (bitZeroOfNeOne h116eq) h125 ch hc

/-- **`.defaultValueBrace`** — the byte `124`, whose route is the class-C span's last
leaf (`117 … 125`'s else arm, kind `0`). -/
theorem hcontArm_defaultValueBrace {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G}
    {s : State} {x : BitVec 8}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (h91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (h123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (h125 : evalICmp .slt x (BitVec.ofNat 8 125) = 1)
    (hne123 : evalICmp .eq x (BitVec.ofNat 8 123) = 0)
    (r : HcontDefaultRow G C s) (hb : HcontHeadByte G r.v) (hc : HcontClassRows G) :
    Nonempty (HcontArm (stage2Calls stage2SubCalls) G C s) := by
  have hge123 : 123 ≤ x.toInt := by simpa using toInt_ge_of_slt_zero h123
  have hx125 : x.toInt < 125 := by simpa using toInt_lt_of_slt_one h125
  have hne123' : x.toInt ≠ 123 := by simpa using toInt_ne_of_eq_zero hne123
  have hbit := tag_zero_of_toInt_ge_58 (x := x) (by omega)
  have h110zero : evalICmp .slt x (BitVec.ofNat 8 110) = 0 :=
    slt_zero_of_toInt_ge (x := x) (a := BitVec.ofNat 8 110)
      (by simp only [toInt_8_110]; omega)
  have h116zero : evalICmp .slt x (BitVec.ofNat 8 116) = 0 :=
    slt_zero_of_toInt_ge (x := x) (a := BitVec.ofNat 8 116)
      (by simp only [toInt_8_116]; omega)
  have h116eq : evalICmp .eq x (BitVec.ofNat 8 116) = 0 :=
    eq_zero_of_toInt_ne (x := x) (c := BitVec.ofNat 8 116)
      (by simp only [toInt_8_116]; omega)
  have h125' : evalICmp .slt x (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq x (BitVec.ofNat 8 125) = 1 := Or.inl h125
  let ch := brcHeadChain_of_lane hInv hblock hk h8 h91 h123 h125 hne123 hbit r hb
  exact hcontArm_classC_58Else_of_class hInv hk h8 h110zero h116zero h116eq h125' ch hc

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.tag_zero_of_toInt_ge_58
#print axioms LeanLLVM.Refinement.WalkScope.tag_zero_of_toInt_lt_44
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_defaultValueLow
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_defaultValueMid
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_otherValue
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_defaultValueBracket
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_defaultValueBracketHigh
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_defaultValueBrace

end WalkScope
end LeanLLVM.Refinement
