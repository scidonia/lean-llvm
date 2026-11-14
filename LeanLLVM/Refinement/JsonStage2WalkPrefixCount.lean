/-
The head path to the extra-token scan, counted.

## The structural fact, for the third time

**`WalkChain` is a `Prop`, and its `steps` is existential by necessity** — a `Nat`-valued
length over a `Prop` would be a large elimination — so a consumer that must *price* needs
segments, not chains.  This is the third place it bites, and each time the resolution was
the same: a counted twin, not a derivation.

| appearance | what needed the count | resolution |
|---|---|---|
| `walkScanRounds457` | the scan's round | `hround` returns a segment |
| `walkHeadChainToScan` | the last entry's price | `hprice` became a bundle field |
| `consumer_tail_seg` | the tail's count, to compose it | the count existed — `3` — and a **name** did not |
| this module | the price, again | counted twins and a `Nat` |

The third row is the fact one layer further in: **a count without a name is not a
composable count.**  `consumer_tail_seg` returns a segment at `3` already; its target
state is existential, and `WalkSegment.trans` needs the next piece's source state to be
the same *term*, so the count was there and unusable.  `consumerTailSegAt` is the same
proof at `ScanEntry s r₁ r₂ r₃ ei cd c rdv x`.

## The prefix, piece by piece

| piece | counted form | count |
|---|---|---|
| `walkHeadChainA` | `walkHeadChainASeg` | 6 |
| the seam (`WalkLink.if_end372_i_at`) | `WalkSegment.of_link` | 1 |
| `walkHeadChainC` | `walkHeadChainCSeg` | 5 |
| `consumer_tail_chain` | `consumerTailSegAt` | 3 |
| `walkScanChain457_ws` | `walkScanLinks457` (already counted) | 3 |

`consumerTailSegAt` exists beside the committed `consumer_tail_seg`, which already
returns a segment at count `3` — but its target *state* is existential, and the scan's
segment needs its premises at that state.  A counted piece that cannot be composed is not
counted for this purpose, so the twin names `ScanEntry s r₁ r₂ r₃ ei cd c rdv x`: the
state `TailS₃ (TailS₂ (TailS₁ s …) …) …` is exactly that abbreviation.

The two `Seg` twins are copies of the committed proofs at the `Seg` constructors: the
links, their named targets and their peels are unchanged, and the composition line is
`Seg.tail` in place of `WalkChain.tail`.  That is what the third appearance costs — the
count is a property of *how* the chain was built, so it cannot be recovered from the
chain.

The total is `(((6 + 1) + 5) + 3) + 3 = 18`, and the price at the last entry is then
`18 + 7 ≤ 32 · Δk`, i.e. `25 ≤ 32` at `Δk = 1`: `omega`, not a hypothesis.
-/

import LeanLLVM.Refinement.JsonStage2WalkHeadChainA
import LeanLLVM.Refinement.JsonStage2WalkHeadChainC
import LeanLLVM.Refinement.JsonStage2WalkHeadChainScan
import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessFinish

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head's fall-through, counted -/

theorem walkHeadChainASeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
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
    Seg (stage2Calls stage2SubCalls) G C s (HeadAC₆ C)
      (headEndS C s x inc nep c ix) 6 := by
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
  exact Seg.tail hl₁' (Seg.tail hl₂' (Seg.tail hl₃'
    (Seg.tail hl₄' (Seg.tail hl₅' (Seg.tail hl₆'
      (Seg.nil hl₆'.inv'))))))

/-! ### The class-C span, counted -/

theorem walkHeadChainCSeg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i")
    {x1 : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x1))
    (h₁ : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (h₂ : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (h₃ : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0) :
    Seg calls G C s (HeadC₄₁₃ C) (HeadS413 s x1) 5 := by
  -- 1. the empty body at `if.else387.i`
  obtain ⟨s₁, hl₁, hs₁⟩ := headChain_else387_at (calls := calls) G C s hInv hblock
  rw [hs₁] at hl₁
  have h8₁ : evalOperand (HeadS62 s) (.reg "%8") = some (.int 8 x1) := h8
  -- 2. `NodeBlock62`, whose bit is clear
  obtain ⟨s₂, hl₂, hs₂⟩ := WalkLink.NodeBlock62_at (calls := calls) (G := G)
    (C := HeadC₆₂ C) (s := HeadS62 s) hl₁.inv' rfl h8₁
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock54"
    else "NodeBlock60") = "NodeBlock60" from by rw [h₁]; rfl] at hs₂ hl₂
  have hs₂' : s₂ = HeadS60 s x1 := hs₂
  rw [hs₂'] at hl₂
  have h8₂ : evalOperand (HeadS60 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 3. `NodeBlock60`, whose bit is clear
  obtain ⟨s₃, hl₃, hs₃⟩ := WalkLink.NodeBlock60_at (calls := calls) (G := G)
    (C := HeadC₆₀ C) (s := HeadS60 s x1) hl₂.inv' rfl h8₂
  rw [show (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock56"
    else "LeafBlock58") = "LeafBlock58" from by rw [h₂]; rfl] at hs₃ hl₃
  have hs₃' : s₃ = HeadS58 s x1 := hs₃
  rw [hs₃'] at hl₃
  have h8₃ : evalOperand (HeadS58 s x1) (.reg "%8") = some (.int 8 x1) := by
    simp only [HeadS58, HeadS60, HeadS62, State.bind, evalOperand,
      lookupName_cons_ne (k := "%Pivot61") (n := "%8") _ _ (by decide),
      lookupName_cons_ne (k := "%Pivot63") (n := "%8") _ _ (by decide)]
    exact h8
  -- 4. `LeafBlock58`, whose bit is clear
  obtain ⟨s₄, hl₄, hs₄⟩ := WalkLink.LeafBlock58_at (calls := calls) (G := G)
    (C := HeadC₅₈ C) (s := HeadS58 s x1) hl₃.inv' rfl h8₃
  rw [show (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.then413.i"
    else "if.else405.i") = "if.else405.i" from by rw [h₃]; rfl] at hs₄ hl₄
  have hs₄' : s₄ = HeadS405 s x1 := hs₄
  rw [hs₄'] at hl₄
  -- 5. the empty body at `if.else405.i`
  obtain ⟨s₅, hl₅, hs₅⟩ := headChain_else405_at (calls := calls) G (HeadC₄₀₅ C)
    (HeadS405 s x1) hl₄.inv' rfl
  have hs₅' : s₅ = HeadS413 s x1 := hs₅
  rw [hs₅'] at hl₅
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃
    (Seg.tail hl₄ (Seg.tail hl₅ (Seg.nil hl₅.inv')))))

/-! ### The tail, counted at the named scan entry -/

theorem consumerTailSegAt {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) (ei cd : Nat) :
    ∀ (_hInv : WalkInv G C s) (_hblock : C.block = "if.then413.i")
    (p : String) (_reg : String) (c : BitVec 32) (op : Operand) (rdv : BitVec 32)
    (x : BitVec 32),
    s.pre = some p →
    phiIncoming p
      [("if.else405.i", .imm (.int 32 (BitVec.ofNat 32 0))),
       ("if.then403.i", .imm (.int 32 (BitVec.ofNat 32 10))),
       ("if.then397.i", .imm (.int 32 (BitVec.ofNat 32 9))),
       ("if.end372.i", .imm (.int 32 (BitVec.ofNat 32 7))),
       ("LeafBlock58", .imm (.int 32 (BitVec.ofNat 32 8)))] = some op →
    evalOperand (stateAt s.env s) op = some (.int 32 c) →
    lookupName s.env "%kind404.i" = some (.ptr (C.stage.tok + 16)) →
    lookupName s.env "%root_done.i" = some (.ptr (G.next0 + 8)) →
    readBytes (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4))
      (G.next0 + 8) 4 = some (natToBytes rdv.toNat 4) →
    s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next →
    stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r₁ →
    r₁.ret = .int 32 x →
    evalICmp .eq x (BitVec.ofNat 32 0) = 0 →
    readBytes r₁.mem C.stage.z 8 = some (wordBytes 8 G.ev) →
    lookupName s.env "%c.i" = some (.ptr (TailCarry₂ C).stage.c) →
    lookupName s.env "%t352.i" = some (.ptr (TailCarry₂ C).stage.tok) →
    lookupName s.env "%z" = some (.ptr (TailCarry₂ C).stage.z) →
    stage2Calls stage2SubCalls "od_scalar_value"
      [.ptr (TailCarry₂ C).stage.c, .ptr (TailCarry₂ C).stage.tok,
       .ptr (TailCarry₂ C).stage.z] r₁.mem r₁.next = some r₂ →
    s2ScalarValueAppend r₁.mem r₂.mem (TailCarry₂ C).stage.z ev.encodedBytes →
    r₂.ret = .int 32 (BitVec.ofNat 32 1) →
    G.ev < 2 ^ 64 → C.evlen < 2 ^ 64 → C.events.length < C.k →
    s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next →
    stage2Calls stage2SubCalls "s2_after_value"
      [.int 32 (BitVec.ofNat 32 C.sp), .ptr (G.next0 + 8),
       .ptr (TailCarry₃ C ev).stage.ctype, .ptr (TailCarry₃ C ev).stage.cst]
      r₂.mem r₂.next = some r₃ →
    lookupName s.env "%ee.1.i" = some (.int 64 (BitVec.ofNat 64 ei)) →
    lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 cd)) →
    cd - ei ≤ C.inner → ei < cd → cd < 2 ^ 64 →
    Seg (stage2Calls stage2SubCalls) G C s (TailCarryScan C ev)
      (ScanEntry s r₁ r₂ r₃ ei cd c rdv x) 3 := by
  intro hInv hblock p reg c op rdv x hpre hinc hop hkind hrd hread hpre' hcall₁ hret₁
    hbit0 hzreadJ hc ht ho hcall₂ happ₂ hret₂ hev64 hevlen64 hlt hpre447 hcall₃ hei hcd
    hinner hlt2 hcd64
  -- 1. the value-position call
  have hx413 : ∀ r, stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 rdv,
       .ptr C.stage.ctype, .ptr C.stage.cst]
      (writeBytes s.mem (C.stage.tok + 16) (natToBytes c.toNat 4)) s.next = some r →
      r.ret = .int 32 x := by
    intro r hr
    have h : r = r₁ := Option.some.inj (hr.symm.trans hcall₁)
    rw [h]; exact hret₁
  obtain ⟨r₁', s₁', hcall₁', hl₁, hs₁'⟩ := walkIfThen413_at (G := G) (C := C) (s := s)
    (p := p) (reg := reg) (x := x) (op := op) hInv hblock hpre hinc hop hkind hrd hread hpre'
    hx413
  have hr₁ : r₁' = r₁ := Option.some.inj (hcall₁'.symm.trans hcall₁)
  rw [hr₁] at hs₁'
  have hs₁ : s₁' = TailS₁ s r₁ c rdv x := hs₁'
  rw [hs₁] at hl₁
  rw [show { C with block := (if evalICmp .eq x (BitVec.ofNat 32 0) = 1
      then "if.then418.i" else "if.then425.i") } = TailCarry₂ C from by rw [hbit0]; rfl] at hl₁
  -- 2. the scalar call's emit arm
  obtain ⟨s₂', hl₂, hs₂'⟩ := walkIfThen425_emit_at (G := G) (C := TailCarry₂ C)
    (s := TailS₁ s r₁ c rdv x) hl₁.inv' rfl
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%c.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%c.i") _ _ (by decide)] using hc)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%t352.i") _ _ (by decide)] using ht)
    (by simpa only [TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%z") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%z") _ _ (by decide)] using ho)
    (by simpa only [TailS₁, stateAt] using hzreadJ)
    (by simpa only [TailS₁, stateAt] using hcall₂) happ₂ hret₂ hev64 hevlen64 hlt
  have hs₂ : s₂' = TailS₂ (TailS₁ s r₁ c rdv x) r₂ := hs₂'
  rw [hs₂] at hl₂
  -- 3. the copy call, at the scan's entry
  obtain ⟨r₃', s₃', hcall₃', hl₃, hs₃'⟩ := walkIfThen447_at (G := G) (C := TailCarry₃ C ev)
    (s := TailS₂ (TailS₁ s r₁ c rdv x) r₂) hl₂.inv' rfl
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%root_done.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%root_done.i") _ _ (by decide)] using hrd)
    (by simpa only [TailS₂, TailS₁, stateAt] using hpre447)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%ee.1.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%ee.1.i") _ _ (by decide)] using hei)
    (by simpa only [TailS₂, TailS₁, stateAt, cells, State.bind,
      lookupName_cons_ne (k := "%tobool428.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call427.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%tobool417.not.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%call416.i") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%38") (n := "%cond350.i") _ _ (by decide),
      lookupName_cons_ne (k := "%.sink372") (n := "%cond350.i") _ _ (by decide)] using hcd)
    hinner hlt2 hcd64
  have hr₃ : r₃' = r₃ := Option.some.inj (hcall₃'.symm.trans hcall₃)
  rw [hr₃] at hs₃'
  have hbit1 : evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = (1 : BitVec 1) := by
    have h1 : (BitVec.ofNat 64 ei).toNat < (BitVec.ofNat 64 cd).toNat := by
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [show evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)
        = BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd)) from rfl,
      show BitVec.ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = true from
        (BitVec.ult_iff_toNat_lt).2 h1]
    rfl
  rw [show (if evalICmp .ult (BitVec.ofNat 64 ei) (BitVec.ofNat 64 cd) = 1
      then "land.rhs457.i" else "if.end473.i") = "land.rhs457.i" from by rw [hbit1]; rfl] at hl₃
  have hs₃ : s₃' = TailS₃ (TailS₂ (TailS₁ s r₁ c rdv x) r₂) r₃ ei cd := hs₃'
  rw [hs₃] at hl₃
  subst hs₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

/-! ### The prefix, as one segment at its own count -/

theorem hlastPrefixSeg {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
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
    (hugt : evalICmp .ugt c ix = 0)
    {p : String} {op : Operand} {e : BitVec 64} {b8 : BitVec 8}
    (hpre6 : (headEndS C s x inc nep c ix).pre = some p)
    (hin6 : phiIncoming p
      [("cond.end349.i", (Operand.reg "%idxprom.i")),
       ("while.body370.i", (Operand.reg "%cond350.i")),
       ("LeafBlock43", (Operand.reg "%ee.0.i238")),
       ("LeafBlock46", (Operand.reg "%ee.0.i238")),
       ("LeafBlock48", (Operand.reg "%ee.0.i238")),
       ("LeafBlock33", (Operand.reg "%cond350.i")),
       ("LeafBlock35", (Operand.reg "%cond350.i")),
       ("LeafBlock37", (Operand.reg "%cond350.i"))] = some op)
    (hv6 : evalOperand (headEndS C s x inc nep c ix) op = some (.int 64 e))
    (hend6 : lookupName (headEndS C s x inc nep c ix).env "%end.i" =
      some (.ptr (C.stage.tok + 8)))
    (h8end : lookupName (headEndS C s x inc nep c ix).env "%8" = some (.int 8 b8))
    (hbit6 : (evalICmp .eq b8 (BitVec.ofNat 8 45) |||
      evalICmp .ult (b8 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    {x1 : BitVec 8}
    (h8c : evalOperand (seamAt C s x inc nep c ix e b8) (.reg "%8") = some (.int 8 x1))
    (hc110 : evalICmp .slt x1 (BitVec.ofNat 8 110) = 0)
    (hc116 : evalICmp .slt x1 (BitVec.ofNat 8 116) = 0)
    (hceq116 : evalICmp .eq x1 (BitVec.ofNat 8 116) = 0)
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord)
    {cA rdv : BitVec 32} {xA : BitVec 32} {ei cd : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (TailStartC C)
      (TailStart C s x inc nep c ix e b8 x1)
      (TailCarryScan (TailStartC C) ev)
      (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) 3)
    {idx : BitVec 64} {a q : Nat} {bs : List UInt8} {src : String} {sel : Operand}
    (hpreS : (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).pre = some src)
    (hincS : phiIncoming src
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some sel)
    (hopS : evalOperand (stateAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).env (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA)) sel = some (.int 64 idx))
    (h3S : lookupName (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).env "%3" = some (.ptr a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hreadS : readBytes (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA).mem (a + (idx.signExtend 64).toNat) 1 = some bs)
    (hbsS : bytesToNat bs = q)
    (hloc105 : WalkLocal (ScanC₁₀₅ (TailCarryScan (TailStartC C) ev))
      (landRhs457OutAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q))
    {x47 : BitVec 8}
    (h47 : evalOperand (landRhs457OutAt (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q) (.reg "%47") = some (.int 8 x47))
    (hbit47 : evalICmp .slt x47 (BitVec.ofNat 8 13) = 1)
    (hws47 : evalICmp .ule (x47 + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1)
    (hloc96 : WalkLocal (ScanC₉₆ (TailCarryScan (TailStartC C) ev))
      (ScanS₉₆ (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47))
    (hlatch : WalkLocal { TailCarryScan (TailStartC C) ev with block := "while.body462.i" }
      (Latch462S (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA) idx a q x47)) :
    ∃ (s' : State),
      s' = Latch462S (ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd
          cA rdv xA) idx a q x47 ∧
      WalkSegment (stage2Calls stage2SubCalls) G C s (ScanLatchC C ev) s'
        ((((6 + 1) + 5) + 3) + 3) := by
  -- the head's fall-through, six links
  have hA : Seg (stage2Calls stage2SubCalls) G C s (HeadAC₆ C)
      (headEndS C s x inc nep c ix) 6 :=
    walkHeadChainASeg (G := G) (C := C) (s := s) hInv hblock h8 hlt91 hlt123 hlt125 hne125
      hinc hnep hge hpre5 hav5 hidx5 htok5 hgap5 hugt
  -- the seam, one link
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.if_end372_i_at (calls := stage2Calls stage2SubCalls) (G := G) (C := HeadAC₆ C)
      (s := headEndS C s x inc nep c ix) (Seg.measure hA).inv' rfl
      (hpre := hpre6) (hin := hin6) (hv := hv6) (hend := hend6) (h8 := h8end)
      (hbit := hbit6)
  rw [hs₁] at hl₁
  have hAB : WalkSegment (stage2Calls stage2SubCalls) G (HeadAC₆ C)
      (headEndS C s x inc nep c ix) (HeadSeamC C)
      (seamAt C s x inc nep c ix e b8) 1 := WalkSegment.of_link hl₁
  -- the class-C span, five links
  have hC : Seg (stage2Calls stage2SubCalls) G (HeadSeamC C)
      (seamAt C s x inc nep c ix e b8) (TailStartC C)
      (TailStart C s x inc nep c ix e b8 x1) 5 :=
    walkHeadChainCSeg (G := G) (C := HeadSeamC C)
      (s := seamAt C s x inc nep c ix e b8) hAB.inv' rfl h8c hc110 hc116 hceq116
  -- the scan's three links, at the latch
  obtain ⟨s₄, hs₄, hscan⟩ :=
    walkScanLinks457 (calls := stage2Calls stage2SubCalls) (G := G)
      (C := TailCarryScan (TailStartC C) ev)
      (s := ScanEntry (TailStart C s x inc nep c ix e b8 x1) r₁ r₂ r₃ ei cd cA rdv xA)
      hTail.inv' rfl hpreS hincS hopS h3S hpos hreadS hbsS hloc105 h47 hbit47 hws47
      hloc96 hlatch
  exact ⟨s₄, hs₄, (((Seg.measure hA).trans hAB).trans (Seg.measure hC)).trans
    (hTail.trans hscan)⟩

end WalkScope
end LeanLLVM.Refinement
