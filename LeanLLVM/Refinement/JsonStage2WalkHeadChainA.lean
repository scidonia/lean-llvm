/-
The walk's head chain through the dispatch's high-byte fall-throughs.

`NodeBlock21` is the outer loop's head, and the token's dispatch is the switch of
comparisons it opens with.  This module is one path through that switch as a single
`WalkChain`: the first byte is not below any of the pivot's constants, so every pivot
takes its fall-through —

`NodeBlock21 → NodeBlock19 → NodeBlock17 → LeafBlock15 → sw.default.i →
cond.end349.i → if.end372.i`

— the entry count's test at `sw.default.i` failing, and `cond.end349.i`'s position
against the entry's index failing too, so the chain lands at the token's end `phi`.

Each link's facts are its own: the class's four bits resolve the `icmp` arms, the two
count words at `sw.default.i` and the token's position and gap cells at `cond.end349.i`
are the caller's.  The carried block accumulates one `with` per link, and a
`with`-nest at depth two is not a term, so each carry and each intermediate state is
named once (`HeadAC₁`…`HeadAC₆`, `headAS₁`…`headAS₅`) and every hypothesis is stated at
the name rather than at a restated nest.
-/
import LeanLLVM.Refinement.JsonStage2WalkStepsPath

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The carries, named

One per link: the target's block on the carry the previous link left. -/

/-- `NodeBlock19`'s carry: `%8 < 91` fails at the head. -/
abbrev HeadAC₁ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock19" }

/-- `NodeBlock17`'s carry: `%8 < 123` fails too. -/
abbrev HeadAC₂ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₁ C with block := "NodeBlock17" }

/-- `LeafBlock15`'s carry: `%8 < 125` fails. -/
abbrev HeadAC₃ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₂ C with block := "LeafBlock15" }

/-- `sw.default.i`'s carry: the leaf's `%8 = 125` fails. -/
abbrev HeadAC₄ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₃ C with block := "sw.default.i" }

/-- `cond.end349.i`'s carry: the entry count's test fails at the default arm. -/
abbrev HeadAC₅ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₄ C with block := "cond.end349.i" }

/-- `if.end372.i`'s carry: the position is not above the entry's index, so the
token's end `phi` is entered. -/
abbrev HeadAC₆ {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { HeadAC₅ C with block := "if.end372.i" }

/-! ### The states, named

Each is the state a link's successor is, as the link's own conclusion states it: the
`bind` of the cell the block computes, at the next block and its predecessor. -/

/-- The state `NodeBlock21` leaves on the arm `%8 < 91` does not take. -/
def headAS₁ (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
    pc := "NodeBlock19", pre := some s.pc }

/-- The state `NodeBlock19` leaves on the arm `%8 < 123` does not take. -/
def headAS₂ (s : State) (x : BitVec 8) : State :=
  { (headAS₁ s x).bind "%Pivot20" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 123))) with
    pc := "NodeBlock17", pre := some (headAS₁ s x).pc }

/-- The state `NodeBlock17` leaves on the arm `%8 < 125` does not take. -/
def headAS₃ (s : State) (x : BitVec 8) : State :=
  { (headAS₂ s x).bind "%Pivot18" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 125))) with
    pc := "LeafBlock15", pre := some (headAS₂ s x).pc }

/-- The state `LeafBlock15` leaves on the arm `%8 = 125` does not take. -/
def headAS₄ (s : State) (x : BitVec 8) : State :=
  { (headAS₃ s x).bind "%SwitchLeaf16" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 125))) with
    pc := "sw.default.i", pre := some (headAS₃ s x).pc }

/-- The state `sw.default.i` leaves on the arm the entry count's test fails. -/
def headAS₅ (s : State) (x : BitVec 8) (inc nep : BitVec 64) : State :=
  { (headAS₄ s x).bind "%cmp343.i" (.int 1 (evalICmp .ult inc nep)) with
    pc := "cond.end349.i", pre := some (headAS₄ s x).pc }

/-! ### The chain -/

/-- **The head's high-byte fall-through to the token's end.**  Six links from the head at
`NodeBlock21` to `if.end372.i`: the dispatch's four pivots all fall through, the entry
count's test fails at the default arm, and the token's position is not above the entry's
index.

The hypotheses are the class's: the four `icmp` bits, the two count words read at
`sw.default.i` and the token's position and gap cells read at `cond.end349.i`.  The start
and end states and carries are the named ones, so a longer traversal appends this chain
where it begins and continues from `if.end372.i`. -/
theorem walkHeadChainA {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "NodeBlock21")
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 0)
    (hlt123 : evalICmp .slt x (BitVec.ofNat 8 123) = 0)
    (hlt125 : evalICmp .slt x (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq x (BitVec.ofNat 8 125) = 0)
    {inc nep c ix : BitVec 64} {reg : String}
    (hinc : evalOperand (headAS₄ s x) (.reg "%inc.i") = some (.int 64 inc))
    (hnep : evalOperand (headAS₄ s x) (.reg "%nep") = some (.int 64 nep))
    (hge : evalICmp .ult inc nep = 0)
    (hpre5 : phiIncoming "sw.default.i"
      [("cond.true345.i", Operand.reg "%conv347.i"),
       ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav5 : lookupName (headAS₅ s x inc nep).env reg = some (.int 64 c))
    (hidx5 : lookupName (headAS₅ s x inc nep).env "%idxprom.i" = some (.int 64 ix))
    (htok5 : lookupName (headAS₅ s x inc nep).env "%t352.i" = some (.ptr C.stage.tok))
    (hgap5 : lookupName (headAS₅ s x inc nep).env "%gap.i" = some (.ptr (C.stage.tok + 20)))
    (hugt : evalICmp .ugt c ix = 0) :
    WalkChain (stage2Calls stage2SubCalls) G C s (HeadAC₆ C)
      (condEnd349OutAt (headAS₅ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)) := by
  -- the four arms, resolved by the class's bits
  have hres₁ : (if evalICmp .slt x (BitVec.ofNat 8 91) = 1 then
      "NodeBlock5" else "NodeBlock19") = "NodeBlock19" := by
    rw [hlt91]; rfl
  have hres₂ : (if evalICmp .slt x (BitVec.ofNat 8 123) = 1 then
      "NodeBlock11" else "NodeBlock17") = "NodeBlock17" := by
    rw [hlt123]; rfl
  have hres₃ : (if evalICmp .slt x (BitVec.ofNat 8 125) = 1 then
      "LeafBlock13" else "LeafBlock15") = "LeafBlock15" := by
    rw [hlt125]; rfl
  have hres₄ : (if evalICmp .eq x (BitVec.ofNat 8 125) = 1 then
      "if.then53.i" else "sw.default.i") = "sw.default.i" := by
    rw [hne125]; rfl
  have hres₅ : (if evalICmp .ult inc nep = 1 then
      "cond.true345.i" else "cond.end349.i") = "cond.end349.i" := by
    rw [hge]; rfl
  have hres₆ : (if evalICmp .ugt c ix = 1 then
      "land.lhs.true357.i" else "if.end372.i") = "if.end372.i" := by
    rw [hugt]; rfl
  -- the byte's operand fact at each pivot, peeled past the cells the pivots bind
  have h8₁ : evalOperand (headAS₁ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₂ : evalOperand (headAS₂ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  have h8₃ : evalOperand (headAS₃ s x) (.reg "%8") = some (.int 8 x) := by
    simp only [headAS₃, headAS₂, headAS₁, evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot18") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot20") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)]
    exact h8
  -- 1. the head's first pivot
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.NodeBlock21_at (calls := stage2Calls stage2SubCalls) G C s hInv hblock h8
  have hl₁' : WalkLink (stage2Calls stage2SubCalls) G C s (HeadAC₁ C) (headAS₁ s x) := by
    have hst : s₁ = headAS₁ s x := by
      rw [hs₁, hres₁]
      rfl
    rw [hst] at hl₁
    rw [hres₁] at hl₁
    exact hl₁
  -- 2. the second pivot
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock19_at (calls := stage2Calls stage2SubCalls) G (HeadAC₁ C)
      (headAS₁ s x) hl₁'.inv' rfl h8₁
  have hl₂' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₁ C) (headAS₁ s x)
      (HeadAC₂ C) (headAS₂ s x) := by
    have hst : s₂ = headAS₂ s x := by
      rw [hs₂, hres₂]
      rfl
    rw [hst] at hl₂
    rw [hres₂] at hl₂
    exact hl₂
  -- 3. the third pivot
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.NodeBlock17_at (calls := stage2Calls stage2SubCalls) G (HeadAC₂ C)
      (headAS₂ s x) hl₂'.inv' rfl h8₂
  have hl₃' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₂ C) (headAS₂ s x)
      (HeadAC₃ C) (headAS₃ s x) := by
    have hst : s₃ = headAS₃ s x := by
      rw [hs₃, hres₃]
      rfl
    rw [hst] at hl₃
    rw [hres₃] at hl₃
    exact hl₃
  -- 4. the leaf's equality test
  obtain ⟨s₄, hl₄, hs₄⟩ :=
    WalkLink.LeafBlock15_at (calls := stage2Calls stage2SubCalls) G (HeadAC₃ C)
      (headAS₃ s x) hl₃'.inv' rfl h8₃
  have hl₄' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₃ C) (headAS₃ s x)
      (HeadAC₄ C) (headAS₄ s x) := by
    have hst : s₄ = headAS₄ s x := by
      rw [hs₄, hres₄]
      rfl
    rw [hst] at hl₄
    rw [hres₄] at hl₄
    exact hl₄
  -- 5. the default arm's entry count
  obtain ⟨s₅, hl₅, hs₅⟩ :=
    WalkLink.sw_default_i_at (calls := stage2Calls stage2SubCalls) G (HeadAC₄ C)
      (headAS₄ s x) hl₄'.inv' rfl hinc hnep
  have hl₅' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₄ C) (headAS₄ s x)
      (HeadAC₅ C) (headAS₅ s x inc nep) := by
    have hst : s₅ = headAS₅ s x inc nep := by
      rw [hs₅, hres₅]
      rfl
    rw [hst] at hl₅
    rw [hres₅] at hl₅
    exact hl₅
  -- 6. the token's position against the entry's index
  obtain ⟨s₆, hl₆, hs₆⟩ :=
    WalkLink.cond_end349_i_at G (HeadAC₅ C) (headAS₅ s x inc nep) hl₅'.inv' rfl
      (p := "sw.default.i") rfl hpre5 hav5 hidx5 htok5 hgap5
  rw [hres₆] at hl₆
  rw [hs₆] at hl₆
  have hl₆' : WalkLink (stage2Calls stage2SubCalls) G (HeadAC₅ C) (headAS₅ s x inc nep)
      (HeadAC₆ C)
      (condEnd349OutAt (headAS₅ s x inc nep) c ix C.stage.tok (C.stage.tok + 20)) := hl₆
  exact WalkChain.tail hl₁' (WalkChain.tail hl₂' (WalkChain.tail hl₃'
    (WalkChain.tail hl₄' (WalkChain.tail hl₅' (WalkChain.tail hl₆'
      (WalkChain.nil hl₆'.inv'))))))
