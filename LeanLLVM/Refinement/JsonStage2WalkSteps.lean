/-
The dispatch's blocks, one step at a time.

`WalkLink` carries `step : step calls stage2Body s = .jump s'`, so a `WalkChain` names
every state it passes through — but a class's link lemma returns `∃ s', WalkLink … s'`
and its witness is built inside the proof.  This module states each block's step at
the state the invariant gives and identifies the link's witness with it, which is
what a chain threads.

The census is the pinned body's, computed below rather than transcribed:

* **class A** — one `icmp` into a fresh name and a `condbr` on it.  Sixty blocks of
  the 165; `LeafBlock99`'s instance is `WalkLink.LeafBlock99_at` in
  `JsonStage2WalkAssembly` (the shape's first instance, and the one that proved the
  pattern), and the fifty-nine here are the class's remainder — fifty-eight inside
  the dispatch's reach and `if.then485.i`, which the exit's tail reads;
* **class C** — the refusal store: a `gep` of the escape buffer's offset word, a
  `store` of the refusal position into it, and a `br` to the arm that records it.
  Eighteen blocks; the two in the exit's tail (`if.then488.i`, `if.then492.i`) have
  their steps in `JsonStage2WalkAssembly` as `walkIfThen488Step`/`walkIfThen492Step`,
  and the sixteen here are the reach's remainder, from one generic shape lemma
  (`walkRefusalStoreStep`) which also covers those two.

Each instance is its block's `find`/`term` pair, the operands' values and the class
step's own conclusion: by `Ctrl.jump.inj` the link's witness *is* the state the step
names, so the identification is the same comparison read twice.  Nothing about the
block's name enters the proof, which is why the class collapses to one shape plus an
enumeration.

The guards beside each class check the list against the census computed from
`stage2Body`: the class's total, that the instances are distinct members of it, and
that the only members without an instance are the ones the assembly module proves.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-! ### The census

The classes are read off the pinned body by shape, so the counts beside them are the
body's and not a list's.  `walkDispatchReach` is the dispatch's own reach (156 blocks,
`JsonStage2WalkAssembly`); the class lists are over all 165 blocks, because class A's
`if.then485.i` and class C's two arms lie past the merge and a chain still threads
them. -/

/-- **Class A's blocks**: one `icmp` into a fresh name and a `condbr` on it. -/
def walkIcmpBrBlocks : List String :=
  (stage2Body.blocks.filter fun b =>
    match b.instrs, b.term with
    | [Instr.icmp d _ _ _ _], Term.condbr (.reg d') _ _ => d == d'
    | _, _ => false).map Block.name

/-- **Class C's blocks**: the refusal store, from the escape buffer's offset word. -/
def walkRefusalBlocks : List String :=
  (stage2Body.blocks.filter fun b =>
    match b.instrs, b.term with
    | [Instr.gep off (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
       Instr.store (.int 64) (.reg _) (.reg p)], Term.br _ => off == p
    | _, _ => false).map Block.name

#guard walkIcmpBrBlocks.length = 60
#guard walkIcmpBrBlocks.eraseDups.length = walkIcmpBrBlocks.length
#guard walkRefusalBlocks.length = 18
#guard walkRefusalBlocks.eraseDups.length = walkRefusalBlocks.length

-- Class A is inside the dispatch's reach but for the exit's tail block; class C's
-- two tail arms are past the merge, so they are not.
#guard (walkIcmpBrBlocks.filter (fun n => !walkDispatchReach.contains n)) = ["if.then485.i"]
#guard (walkRefusalBlocks.filter (fun n => walkDispatchReach.contains n)).length = 16

/-! ### Class A's instances

*The fifty-nine.*  `LeafBlock99`'s is `WalkLink.LeafBlock99_at` in the assembly module.
-/

/-- **`NodeBlock21`'s target, named.**  `icmp slt i8 %8, 91`; the bit picks
`NodeBlock5` or `NodeBlock19`. -/
theorem WalkLink.NodeBlock21_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock21")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 91) = 1 then
            "NodeBlock5" else "NodeBlock19") } s' ∧
      s' = { (s.bind "%Pivot22"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 91)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 91) = 1 then
          "NodeBlock5" else "NodeBlock19")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock21 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock21) (d := "%Pivot22") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 91))))
    (t := "NodeBlock5") (f := "NodeBlock19") (x := x1) (y := (BitVec.ofNat 8 91))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock21_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock19`'s target, named.**  `icmp slt i8 %8, 123`; the bit picks
`NodeBlock11` or `NodeBlock17`. -/
theorem WalkLink.NodeBlock19_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock19")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 123) = 1 then
            "NodeBlock11" else "NodeBlock17") } s' ∧
      s' = { (s.bind "%Pivot20"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 123)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 123) = 1 then
          "NodeBlock11" else "NodeBlock17")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock19 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock19) (d := "%Pivot20") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 123))))
    (t := "NodeBlock11") (f := "NodeBlock17") (x := x1) (y := (BitVec.ofNat 8 123))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock19_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock17`'s target, named.**  `icmp slt i8 %8, 125`; the bit picks
`LeafBlock13` or `LeafBlock15`. -/
theorem WalkLink.NodeBlock17_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock17")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 125) = 1 then
            "LeafBlock13" else "LeafBlock15") } s' ∧
      s' = { (s.bind "%Pivot18"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 125)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 125) = 1 then
          "LeafBlock13" else "LeafBlock15")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock17 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock17) (d := "%Pivot18") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 125))))
    (t := "LeafBlock13") (f := "LeafBlock15") (x := x1) (y := (BitVec.ofNat 8 125))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock17_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock15`'s target, named.**  `icmp eq i8 %8, 125`; the bit picks
`if.then53.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock15_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock15")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 125) = 1 then
            "if.then53.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf16"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 125)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 125) = 1 then
          "if.then53.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock15 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock15) (d := "%SwitchLeaf16") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 125))))
    (t := "if.then53.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 125))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock15_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock13`'s target, named.**  `icmp eq i8 %8, 123`; the bit picks
`if.then.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock13_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock13")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 123) = 1 then
            "if.then.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf14"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 123)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 123) = 1 then
          "if.then.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock13 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock13) (d := "%SwitchLeaf14") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 123))))
    (t := "if.then.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 123))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock13_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock11`'s target, named.**  `icmp slt i8 %8, 93`; the bit picks
`LeafBlock7` or `LeafBlock9`. -/
theorem WalkLink.NodeBlock11_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock11")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 93) = 1 then
            "LeafBlock7" else "LeafBlock9") } s' ∧
      s' = { (s.bind "%Pivot12"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 93)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 93) = 1 then
          "LeafBlock7" else "LeafBlock9")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock11 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock11) (d := "%Pivot12") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 93))))
    (t := "LeafBlock7") (f := "LeafBlock9") (x := x1) (y := (BitVec.ofNat 8 93))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock11_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock9`'s target, named.**  `icmp eq i8 %8, 93`; the bit picks
`if.then53.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock9_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock9")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 93) = 1 then
            "if.then53.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf10"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 93)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 93) = 1 then
          "if.then53.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock9 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock9) (d := "%SwitchLeaf10") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 93))))
    (t := "if.then53.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 93))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock9_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock7`'s target, named.**  `icmp eq i8 %8, 91`; the bit picks
`if.then.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock7_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock7")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 91) = 1 then
            "if.then.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf8"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 91)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 91) = 1 then
          "if.then.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock7 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock7) (d := "%SwitchLeaf8") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 91))))
    (t := "if.then.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 91))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock7_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock5`'s target, named.**  `icmp slt i8 %8, 44`; the bit picks
`LeafBlock` or `NodeBlock`. -/
theorem WalkLink.NodeBlock5_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock5")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 44) = 1 then
            "LeafBlock" else "NodeBlock") } s' ∧
      s' = { (s.bind "%Pivot6"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 44)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 44) = 1 then
          "LeafBlock" else "NodeBlock")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock5 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock5) (d := "%Pivot6") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 44))))
    (t := "LeafBlock") (f := "NodeBlock") (x := x1) (y := (BitVec.ofNat 8 44))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock5_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock`'s target, named.**  `icmp slt i8 %8, 58`; the bit picks
`LeafBlock1` or `LeafBlock3`. -/
theorem WalkLink.NodeBlock_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 58) = 1 then
            "LeafBlock1" else "LeafBlock3") } s' ∧
      s' = { (s.bind "%Pivot"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 58)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 58) = 1 then
          "LeafBlock1" else "LeafBlock3")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock) (d := "%Pivot") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 58))))
    (t := "LeafBlock1") (f := "LeafBlock3") (x := x1) (y := (BitVec.ofNat 8 58))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock3`'s target, named.**  `icmp eq i8 %8, 58`; the bit picks
`if.then173.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock3_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock3")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 58) = 1 then
            "if.then173.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf4"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 58)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 58) = 1 then
          "if.then173.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock3 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock3) (d := "%SwitchLeaf4") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 58))))
    (t := "if.then173.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 58))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock3_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock1`'s target, named.**  `icmp eq i8 %8, 44`; the bit picks
`if.then127.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock1_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock1")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 44) = 1 then
            "if.then127.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf2"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 44)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 44) = 1 then
          "if.then127.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock1 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock1) (d := "%SwitchLeaf2") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 44))))
    (t := "if.then127.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 44))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock1_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock`'s target, named.**  `icmp eq i8 %8, 34`; the bit picks
`sw.bb202.i` or `sw.default.i`. -/
theorem WalkLink.LeafBlock_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 34) = 1 then
            "sw.bb202.i" else "sw.default.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 34)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 34) = 1 then
          "sw.bb202.i" else "sw.default.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock) (d := "%SwitchLeaf") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 34))))
    (t := "sw.bb202.i") (f := "sw.default.i") (x := x1) (y := (BitVec.ofNat 8 34))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.end.i`'s target, named.**  `icmp ugt i32 %sp.i.0248, 519`; the bit picks
`if.then21.i` or `if.end24.i`. -/
theorem WalkLink.if_end_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .ugt x1 (BitVec.ofNat 32 519) = 1 then
            "if.then21.i" else "if.end24.i") } s' ∧
      s' = { (s.bind "%cmp19.i"
          (.int 1 (evalICmp .ugt x1 (BitVec.ofNat 32 519)))) with
        pc := (if evalICmp .ugt x1 (BitVec.ofNat 32 519) = 1 then
          "if.then21.i" else "if.end24.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_end_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_end_i) (d := "%cmp19.i") (pred := IPred.ugt) (w := 32)
    (a₁ := (.reg "%sp.i.0248")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 519))))
    (t := "if.then21.i") (f := "if.end24.i") (x := x1) (y := (BitVec.ofNat 32 519))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_end_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then53.i`'s target, named.**  `icmp eq i32 %sp.i.0248, 0`; the bit picks
`if.then56.i` or `if.end59.i`. -/
theorem WalkLink.if_then53_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then53.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
            "if.then56.i" else "if.end59.i") } s' ∧
      s' = { (s.bind "%cmp54.i"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
          "if.then56.i" else "if.end59.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then53_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_then53_i) (d := "%cmp54.i") (pred := IPred.eq) (w := 32)
    (a₁ := (.reg "%sp.i.0248")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 0))))
    (t := "if.then56.i") (f := "if.end59.i") (x := x1) (y := (BitVec.ofNat 32 0))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_then53_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock27`'s target, named.**  `icmp slt i8 %15, 3`; the bit picks
`LeafBlock23` or `LeafBlock25`. -/
theorem WalkLink.NodeBlock27_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock27")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 3) = 1 then
            "LeafBlock23" else "LeafBlock25") } s' ∧
      s' = { (s.bind "%Pivot28"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 3)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 3) = 1 then
          "LeafBlock23" else "LeafBlock25")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock27 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock27) (d := "%Pivot28") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%15")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 3))))
    (t := "LeafBlock23") (f := "LeafBlock25") (x := x1) (y := (BitVec.ofNat 8 3))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock27_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock25`'s target, named.**  `icmp eq i8 %15, 3`; the bit picks
`if.then109.i` or `cleanup104.i`. -/
theorem WalkLink.LeafBlock25_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock25")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then
            "if.then109.i" else "cleanup104.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf26"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 3)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then
          "if.then109.i" else "cleanup104.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock25 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock25) (d := "%SwitchLeaf26") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%15")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 3))))
    (t := "if.then109.i") (f := "cleanup104.i") (x := x1) (y := (BitVec.ofNat 8 3))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock25_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock23`'s target, named.**  `icmp eq i8 %15, 0`; the bit picks
`if.then109.i` or `cleanup104.i`. -/
theorem WalkLink.LeafBlock23_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock23")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 0) = 1 then
            "if.then109.i" else "cleanup104.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf24"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 0)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 0) = 1 then
          "if.then109.i" else "cleanup104.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock23 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock23) (d := "%SwitchLeaf24") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%15")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 0))))
    (t := "if.then109.i") (f := "cleanup104.i") (x := x1) (y := (BitVec.ofNat 8 0))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock23_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`cond.end.i`'s target, named.**  `icmp ult i8 %15, 2`; the bit picks
`if.then109.i` or `cleanup104.i`. -/
theorem WalkLink.cond_end_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.end.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .ult x1 (BitVec.ofNat 8 2) = 1 then
            "if.then109.i" else "cleanup104.i") } s' ∧
      s' = { (s.bind "%16"
          (.int 1 (evalICmp .ult x1 (BitVec.ofNat 8 2)))) with
        pc := (if evalICmp .ult x1 (BitVec.ofNat 8 2) = 1 then
          "if.then109.i" else "cleanup104.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.cond_end_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkCond_end_i) (d := "%16") (pred := IPred.ult) (w := 8)
    (a₁ := (.reg "%15")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 2))))
    (t := "if.then109.i") (f := "cleanup104.i") (x := x1) (y := (BitVec.ofNat 8 2))
    (by rw [hInv.pc_eq, hblock]; exact walkCond_end_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then127.i`'s target, named.**  `icmp eq i32 %sp.i.0248, 0`; the bit picks
`if.then130.i` or `if.end133.i`. -/
theorem WalkLink.if_then127_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then127.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
            "if.then130.i" else "if.end133.i") } s' ∧
      s' = { (s.bind "%cmp128.i"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
          "if.then130.i" else "if.end133.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then127_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_then127_i) (d := "%cmp128.i") (pred := IPred.eq) (w := 32)
    (a₁ := (.reg "%sp.i.0248")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 0))))
    (t := "if.then130.i") (f := "if.end133.i") (x := x1) (y := (BitVec.ofNat 32 0))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_then127_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then141.i`'s target, named.**  `icmp eq i8 %22, 3`; the bit picks
`if.end150.i` or `if.then147.i`. -/
theorem WalkLink.if_then141_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then141.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then
            "if.end150.i" else "if.then147.i") } s' ∧
      s' = { (s.bind "%cmp145.not.i"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 3)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then
          "if.end150.i" else "if.then147.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then141_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_then141_i) (d := "%cmp145.not.i") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%22")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 3))))
    (t := "if.end150.i") (f := "if.then147.i") (x := x1) (y := (BitVec.ofNat 8 3))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_then141_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.else153.i`'s target, named.**  `icmp eq i8 %22, 1`; the bit picks
`if.end162.i` or `if.then159.i`. -/
theorem WalkLink.if_else153_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else153.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 1) = 1 then
            "if.end162.i" else "if.then159.i") } s' ∧
      s' = { (s.bind "%cmp157.not.i"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 1)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 1) = 1 then
          "if.end162.i" else "if.then159.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_else153_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_else153_i) (d := "%cmp157.not.i") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%22")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 1))))
    (t := "if.end162.i") (f := "if.then159.i") (x := x1) (y := (BitVec.ofNat 8 1))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_else153_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then173.i`'s target, named.**  `icmp eq i32 %sp.i.0248, 0`; the bit picks
`if.then176.i` or `if.end179.i`. -/
theorem WalkLink.if_then173_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then173.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
            "if.then176.i" else "if.end179.i") } s' ∧
      s' = { (s.bind "%cmp174.i"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
          "if.then176.i" else "if.end179.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then173_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_then173_i) (d := "%cmp174.i") (pred := IPred.eq) (w := 32)
    (a₁ := (.reg "%sp.i.0248")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 0))))
    (t := "if.then176.i") (f := "if.end179.i") (x := x1) (y := (BitVec.ofNat 32 0))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_then173_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`sw.bb202.i`'s target, named.**  `icmp ult i64 %inc.i, %nep`; the bit picks
`if.end207.i` or `if.then205.i`. -/
theorem WalkLink.sw_bb202_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.bb202.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .ult x1 x2 = 1 then
            "if.end207.i" else "if.then205.i") } s' ∧
      s' = { (s.bind "%cmp203.not.i"
          (.int 1 (evalICmp .ult x1 x2))) with
        pc := (if evalICmp .ult x1 x2 = 1 then
          "if.end207.i" else "if.then205.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.sw_bb202_i G C s hInv hblock h1 h2
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkSw_bb202_i) (d := "%cmp203.not.i") (pred := IPred.ult) (w := 64)
    (a₁ := (.reg "%inc.i")) (a₂ := (.reg "%nep"))
    (t := "if.end207.i") (f := "if.then205.i") (x := x1) (y := x2)
    (by rw [hInv.pc_eq, hblock]; exact walkSw_bb202_i_find) rfl rfl h1 h2
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock31`'s target, named.**  `icmp slt i32 %call272.i, 1`; the bit picks
`cleanup339.critedge.i` or `LeafBlock29`. -/
theorem WalkLink.NodeBlock31_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock31")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 32 1) = 1 then
            "cleanup339.critedge.i" else "LeafBlock29") } s' ∧
      s' = { (s.bind "%Pivot32"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 32 1)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 32 1) = 1 then
          "cleanup339.critedge.i" else "LeafBlock29")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock31 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock31) (d := "%Pivot32") (pred := IPred.slt) (w := 32)
    (a₁ := (.reg "%call272.i")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 1))))
    (t := "cleanup339.critedge.i") (f := "LeafBlock29") (x := x1) (y := (BitVec.ofNat 32 1))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock31_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock29`'s target, named.**  `icmp eq i32 %call272.i, 1`; the bit picks
`if.then281.i` or `if.else285.i`. -/
theorem WalkLink.LeafBlock29_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock29")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 32 1) = 1 then
            "if.then281.i" else "if.else285.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf30"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 32 1)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 32 1) = 1 then
          "if.then281.i" else "if.else285.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock29 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock29) (d := "%SwitchLeaf30") (pred := IPred.eq) (w := 32)
    (a₁ := (.reg "%call272.i")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 1))))
    (t := "if.then281.i") (f := "if.else285.i") (x := x1) (y := (BitVec.ofNat 32 1))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock29_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`sw.default.i`'s target, named.**  `icmp ult i64 %inc.i, %nep`; the bit picks
`cond.true345.i` or `cond.end349.i`. -/
theorem WalkLink.sw_default_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.default.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .ult x1 x2 = 1 then
            "cond.true345.i" else "cond.end349.i") } s' ∧
      s' = { (s.bind "%cmp343.i"
          (.int 1 (evalICmp .ult x1 x2))) with
        pc := (if evalICmp .ult x1 x2 = 1 then
          "cond.true345.i" else "cond.end349.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.sw_default_i G C s hInv hblock h1 h2
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkSw_default_i) (d := "%cmp343.i") (pred := IPred.ult) (w := 64)
    (a₁ := (.reg "%inc.i")) (a₂ := (.reg "%nep"))
    (t := "cond.true345.i") (f := "cond.end349.i") (x := x1) (y := x2)
    (by rw [hInv.pc_eq, hblock]; exact walkSw_default_i_find) rfl rfl h1 h2
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock41`'s target, named.**  `icmp slt i8 %35, 13`; the bit picks
`LeafBlock33` or `NodeBlock39`. -/
theorem WalkLink.NodeBlock41_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock41")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
            "LeafBlock33" else "NodeBlock39") } s' ∧
      s' = { (s.bind "%Pivot42"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
          "LeafBlock33" else "NodeBlock39")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock41 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock41) (d := "%Pivot42") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%35")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "LeafBlock33") (f := "NodeBlock39") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock41_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock39`'s target, named.**  `icmp slt i8 %35, 32`; the bit picks
`LeafBlock35` or `LeafBlock37`. -/
theorem WalkLink.NodeBlock39_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock39")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
            "LeafBlock35" else "LeafBlock37") } s' ∧
      s' = { (s.bind "%Pivot40"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
          "LeafBlock35" else "LeafBlock37")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock39 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock39) (d := "%Pivot40") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%35")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "LeafBlock35") (f := "LeafBlock37") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock39_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock37`'s target, named.**  `icmp eq i8 %35, 32`; the bit picks
`land.rhs.i.preheader` or `if.end372.i`. -/
theorem WalkLink.LeafBlock37_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock37")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
            "land.rhs.i.preheader" else "if.end372.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf38"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
          "land.rhs.i.preheader" else "if.end372.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock37 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock37) (d := "%SwitchLeaf38") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%35")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "land.rhs.i.preheader") (f := "if.end372.i") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock37_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock35`'s target, named.**  `icmp eq i8 %35, 13`; the bit picks
`land.rhs.i.preheader` or `if.end372.i`. -/
theorem WalkLink.LeafBlock35_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock35")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
            "land.rhs.i.preheader" else "if.end372.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf36"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
          "land.rhs.i.preheader" else "if.end372.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock35 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock35) (d := "%SwitchLeaf36") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%35")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "land.rhs.i.preheader") (f := "if.end372.i") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock35_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock52`'s target, named.**  `icmp slt i8 %36, 13`; the bit picks
`LeafBlock43` or `NodeBlock50`. -/
theorem WalkLink.NodeBlock52_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock52")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
            "LeafBlock43" else "NodeBlock50") } s' ∧
      s' = { (s.bind "%Pivot53"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
          "LeafBlock43" else "NodeBlock50")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock52 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock52) (d := "%Pivot53") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%36")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "LeafBlock43") (f := "NodeBlock50") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock52_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock50`'s target, named.**  `icmp slt i8 %36, 32`; the bit picks
`LeafBlock46` or `LeafBlock48`. -/
theorem WalkLink.NodeBlock50_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock50")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
            "LeafBlock46" else "LeafBlock48") } s' ∧
      s' = { (s.bind "%Pivot51"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
          "LeafBlock46" else "LeafBlock48")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock50 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock50) (d := "%Pivot51") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%36")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "LeafBlock46") (f := "LeafBlock48") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock50_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock48`'s target, named.**  `icmp eq i8 %36, 32`; the bit picks
`if.end372.i` or `while.body370.i`. -/
theorem WalkLink.LeafBlock48_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock48")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf49", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s
        with pc := "while.body370.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
            "if.end372.i" else "while.body370.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf49"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
          "if.end372.i" else "while.body370.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock48 G C s hInv hblock h1 hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock48) (d := "%SwitchLeaf49") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%36")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "if.end372.i") (f := "while.body370.i") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock48_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock46`'s target, named.**  `icmp eq i8 %36, 13`; the bit picks
`if.end372.i` or `while.body370.i`. -/
theorem WalkLink.LeafBlock46_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock46")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf47", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s
        with pc := "while.body370.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
            "if.end372.i" else "while.body370.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf47"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
          "if.end372.i" else "while.body370.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock46 G C s hInv hblock h1 hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock46) (d := "%SwitchLeaf47") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%36")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "if.end372.i") (f := "while.body370.i") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock46_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock62`'s target, named.**  `icmp slt i8 %8, 110`; the bit picks
`LeafBlock54` or `NodeBlock60`. -/
theorem WalkLink.NodeBlock62_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock62")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then
            "LeafBlock54" else "NodeBlock60") } s' ∧
      s' = { (s.bind "%Pivot63"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 110)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then
          "LeafBlock54" else "NodeBlock60")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock62 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock62) (d := "%Pivot63") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 110))))
    (t := "LeafBlock54") (f := "NodeBlock60") (x := x1) (y := (BitVec.ofNat 8 110))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock62_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock60`'s target, named.**  `icmp slt i8 %8, 116`; the bit picks
`LeafBlock56` or `LeafBlock58`. -/
theorem WalkLink.NodeBlock60_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock60")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then
            "LeafBlock56" else "LeafBlock58") } s' ∧
      s' = { (s.bind "%Pivot61"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 116)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then
          "LeafBlock56" else "LeafBlock58")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock60 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock60) (d := "%Pivot61") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 116))))
    (t := "LeafBlock56") (f := "LeafBlock58") (x := x1) (y := (BitVec.ofNat 8 116))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock60_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock58`'s target, named.**  `icmp eq i8 %8, 116`; the bit picks
`if.then413.i` or `if.else405.i`. -/
theorem WalkLink.LeafBlock58_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock58")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then
            "if.then413.i" else "if.else405.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf59"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 116)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then
          "if.then413.i" else "if.else405.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock58 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock58) (d := "%SwitchLeaf59") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 116))))
    (t := "if.then413.i") (f := "if.else405.i") (x := x1) (y := (BitVec.ofNat 8 116))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock58_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock56`'s target, named.**  `icmp eq i8 %8, 110`; the bit picks
`if.then403.i` or `if.else405.i`. -/
theorem WalkLink.LeafBlock56_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock56")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then
            "if.then403.i" else "if.else405.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf57"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 110)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then
          "if.then403.i" else "if.else405.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock56 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock56) (d := "%SwitchLeaf57") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 110))))
    (t := "if.then403.i") (f := "if.else405.i") (x := x1) (y := (BitVec.ofNat 8 110))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock56_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock54`'s target, named.**  `icmp eq i8 %8, 102`; the bit picks
`if.then397.i` or `if.else405.i`. -/
theorem WalkLink.LeafBlock54_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock54")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then
            "if.then397.i" else "if.else405.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf55"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 102)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then
          "if.then397.i" else "if.else405.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock54 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock54) (d := "%SwitchLeaf55") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%8")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 102))))
    (t := "if.then397.i") (f := "if.else405.i") (x := x1) (y := (BitVec.ofNat 8 102))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock54_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock73`'s target, named.**  `icmp slt i8 %40, 13`; the bit picks
`LeafBlock64` or `NodeBlock71`. -/
theorem WalkLink.NodeBlock73_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock73")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
            "LeafBlock64" else "NodeBlock71") } s' ∧
      s' = { (s.bind "%Pivot74"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
          "LeafBlock64" else "NodeBlock71")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock73 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock73) (d := "%Pivot74") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%40")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "LeafBlock64") (f := "NodeBlock71") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock73_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock71`'s target, named.**  `icmp slt i8 %40, 32`; the bit picks
`LeafBlock67` or `LeafBlock69`. -/
theorem WalkLink.NodeBlock71_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock71")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
            "LeafBlock67" else "LeafBlock69") } s' ∧
      s' = { (s.bind "%Pivot72"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
          "LeafBlock67" else "LeafBlock69")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock71 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock71) (d := "%Pivot72") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%40")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "LeafBlock67") (f := "LeafBlock69") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock71_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock69`'s target, named.**  `icmp eq i8 %40, 32`; the bit picks
`while.end.i` or `while.body.i104`. -/
theorem WalkLink.LeafBlock69_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock69")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf70", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s
        with pc := "while.body.i104", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
            "while.end.i" else "while.body.i104") } s' ∧
      s' = { (s.bind "%SwitchLeaf70"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
          "while.end.i" else "while.body.i104")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock69 G C s hInv hblock h1 hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock69) (d := "%SwitchLeaf70") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%40")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "while.end.i") (f := "while.body.i104") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock69_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock67`'s target, named.**  `icmp eq i8 %40, 13`; the bit picks
`while.end.i` or `while.body.i104`. -/
theorem WalkLink.LeafBlock67_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock67")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf68", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s
        with pc := "while.body.i104", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
            "while.end.i" else "while.body.i104") } s' ∧
      s' = { (s.bind "%SwitchLeaf68"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
          "while.end.i" else "while.body.i104")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock67 G C s hInv hblock h1 hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock67) (d := "%SwitchLeaf68") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%40")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "while.end.i") (f := "while.body.i104") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock67_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock83`'s target, named.**  `icmp slt i8 %41, 110`; the bit picks
`LeafBlock75` or `NodeBlock81`. -/
theorem WalkLink.NodeBlock83_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock83")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then
            "LeafBlock75" else "NodeBlock81") } s' ∧
      s' = { (s.bind "%Pivot84"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 110)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then
          "LeafBlock75" else "NodeBlock81")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock83 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock83) (d := "%Pivot84") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%41")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 110))))
    (t := "LeafBlock75") (f := "NodeBlock81") (x := x1) (y := (BitVec.ofNat 8 110))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock83_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock81`'s target, named.**  `icmp slt i8 %41, 116`; the bit picks
`LeafBlock77` or `LeafBlock79`. -/
theorem WalkLink.NodeBlock81_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock81")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then
            "LeafBlock77" else "LeafBlock79") } s' ∧
      s' = { (s.bind "%Pivot82"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 116)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then
          "LeafBlock77" else "LeafBlock79")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock81 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock81) (d := "%Pivot82") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%41")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 116))))
    (t := "LeafBlock77") (f := "LeafBlock79") (x := x1) (y := (BitVec.ofNat 8 116))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock81_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock79`'s target, named.**  `icmp eq i8 %41, 116`; the bit picks
`if.end48.i` or `if.else43.i`. -/
theorem WalkLink.LeafBlock79_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock79")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then
            "if.end48.i" else "if.else43.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf80"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 116)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then
          "if.end48.i" else "if.else43.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock79 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock79) (d := "%SwitchLeaf80") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%41")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 116))))
    (t := "if.end48.i") (f := "if.else43.i") (x := x1) (y := (BitVec.ofNat 8 116))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock79_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock77`'s target, named.**  `icmp eq i8 %41, 110`; the bit picks
`if.then42.i` or `if.else43.i`. -/
theorem WalkLink.LeafBlock77_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock77")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then
            "if.then42.i" else "if.else43.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf78"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 110)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then
          "if.then42.i" else "if.else43.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock77 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock77) (d := "%SwitchLeaf78") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%41")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 110))))
    (t := "if.then42.i") (f := "if.else43.i") (x := x1) (y := (BitVec.ofNat 8 110))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock77_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock75`'s target, named.**  `icmp eq i8 %41, 102`; the bit picks
`if.then37.i` or `if.else43.i`. -/
theorem WalkLink.LeafBlock75_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock75")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then
            "if.then37.i" else "if.else43.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf76"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 102)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then
          "if.then37.i" else "if.else43.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock75 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock75) (d := "%SwitchLeaf76") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%41")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 102))))
    (t := "if.then37.i") (f := "if.else43.i") (x := x1) (y := (BitVec.ofNat 8 102))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock75_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`for.end.i.i`'s target, named.**  `icmp eq i64 %sub54.i, %ln.0.i`; the bit picks
`if.end67.i` or `if.then57.i`. -/
theorem WalkLink.for_end_i_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.end.i.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%sub54.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%ln.0.i") = some (.int 64 x2))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 x2 = 1 then
            "if.end67.i" else "if.then57.i") } s' ∧
      s' = { (s.bind "%cmp11.not.i.i"
          (.int 1 (evalICmp .eq x1 x2))) with
        pc := (if evalICmp .eq x1 x2 = 1 then
          "if.end67.i" else "if.then57.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.for_end_i_i G C s hInv hblock h1 h2
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkFor_end_i_i) (d := "%cmp11.not.i.i") (pred := IPred.eq) (w := 64)
    (a₁ := (.reg "%sub54.i")) (a₂ := (.reg "%ln.0.i"))
    (t := "if.end67.i") (f := "if.then57.i") (x := x1) (y := x2)
    (by rw [hInv.pc_eq, hblock]; exact walkFor_end_i_i_find) rfl rfl h1 h2
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.end67.i`'s target, named.**  `icmp ult i64 %ee.0.lcssa.i, %cond.i`; the bit picks
`land.rhs71.i` or `while.end78.i`. -/
theorem WalkLink.if_end67_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end67.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%ee.0.lcssa.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%cond.i") = some (.int 64 x2))
    (hl : WalkLocal { C with block := "land.rhs71.i" }
      { stateAt (("%cmp6919.i", .int 1 (evalICmp .ult x1 x2)) :: s.env) s
        with pc := "land.rhs71.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .ult x1 x2 = 1 then
            "land.rhs71.i" else "while.end78.i") } s' ∧
      s' = { (s.bind "%cmp6919.i"
          (.int 1 (evalICmp .ult x1 x2))) with
        pc := (if evalICmp .ult x1 x2 = 1 then
          "land.rhs71.i" else "while.end78.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_end67_i G C s hInv hblock h1 h2 hl
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_end67_i) (d := "%cmp6919.i") (pred := IPred.ult) (w := 64)
    (a₁ := (.reg "%ee.0.lcssa.i")) (a₂ := (.reg "%cond.i"))
    (t := "land.rhs71.i") (f := "while.end78.i") (x := x1) (y := x2)
    (by rw [hInv.pc_eq, hblock]; exact walkIf_end67_i_find) rfl rfl h1 h2
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock94`'s target, named.**  `icmp slt i8 %46, 13`; the bit picks
`LeafBlock85` or `NodeBlock92`. -/
theorem WalkLink.NodeBlock94_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock94")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
            "LeafBlock85" else "NodeBlock92") } s' ∧
      s' = { (s.bind "%Pivot95"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
          "LeafBlock85" else "NodeBlock92")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock94 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock94) (d := "%Pivot95") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%46")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "LeafBlock85") (f := "NodeBlock92") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock94_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock92`'s target, named.**  `icmp slt i8 %46, 32`; the bit picks
`LeafBlock88` or `LeafBlock90`. -/
theorem WalkLink.NodeBlock92_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock92")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
            "LeafBlock88" else "LeafBlock90") } s' ∧
      s' = { (s.bind "%Pivot93"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
          "LeafBlock88" else "LeafBlock90")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock92 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock92) (d := "%Pivot93") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%46")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "LeafBlock88") (f := "LeafBlock90") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock92_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock90`'s target, named.**  `icmp eq i8 %46, 32`; the bit picks
`while.body76.i` or `while.end78.i`. -/
theorem WalkLink.LeafBlock90_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock90")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf91", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s
        with pc := "while.body76.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
            "while.body76.i" else "while.end78.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf91"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
          "while.body76.i" else "while.end78.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock90 G C s hInv hblock h1 hl
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock90) (d := "%SwitchLeaf91") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%46")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "while.body76.i") (f := "while.end78.i") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock90_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock88`'s target, named.**  `icmp eq i8 %46, 13`; the bit picks
`while.body76.i` or `while.end78.i`. -/
theorem WalkLink.LeafBlock88_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock88")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf89", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s
        with pc := "while.body76.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
            "while.body76.i" else "while.end78.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf89"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then
          "while.body76.i" else "while.end78.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock88 G C s hInv hblock h1 hl
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock88) (d := "%SwitchLeaf89") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%46")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "while.body76.i") (f := "while.end78.i") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock88_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock105`'s target, named.**  `icmp slt i8 %47, 13`; the bit picks
`LeafBlock96` or `NodeBlock103`. -/
theorem WalkLink.NodeBlock105_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock105")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
            "LeafBlock96" else "NodeBlock103") } s' ∧
      s' = { (s.bind "%Pivot106"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 13)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then
          "LeafBlock96" else "NodeBlock103")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock105 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock105) (d := "%Pivot106") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%47")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 13))))
    (t := "LeafBlock96") (f := "NodeBlock103") (x := x1) (y := (BitVec.ofNat 8 13))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock105_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`NodeBlock103`'s target, named.**  `icmp slt i8 %47, 32`; the bit picks
`LeafBlock99` or `LeafBlock101`. -/
theorem WalkLink.NodeBlock103_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock103")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
            "LeafBlock99" else "LeafBlock101") } s' ∧
      s' = { (s.bind "%Pivot104"
          (.int 1 (evalICmp .slt x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then
          "LeafBlock99" else "LeafBlock101")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.NodeBlock103 G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkNodeBlock103) (d := "%Pivot104") (pred := IPred.slt) (w := 8)
    (a₁ := (.reg "%47")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "LeafBlock99") (f := "LeafBlock101") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock103_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock101`'s target, named.**  `icmp eq i8 %47, 32`; the bit picks
`while.body462.i` or `if.then467.i`. -/
theorem WalkLink.LeafBlock101_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock101")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf102", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s
        with pc := "while.body462.i", pre := some s.pc })
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
            "while.body462.i" else "if.then467.i") } s' ∧
      s' = { (s.bind "%SwitchLeaf102"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then
          "while.body462.i" else "if.then467.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock101 G C s hInv hblock h1 hl
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkLeafBlock101) (d := "%SwitchLeaf102") (pred := IPred.eq) (w := 8)
    (a₁ := (.reg "%47")) (a₂ := (.imm (.int 8 (BitVec.ofNat 8 32))))
    (t := "while.body462.i") (f := "if.then467.i") (x := x1) (y := (BitVec.ofNat 8 32))
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock101_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then485.i`'s target, named.**  `icmp eq i32 %sp.i.1, 0`; the bit picks
`if.end490.i` or `if.then488.i`. -/
theorem WalkLink.if_then485_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then485.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.1") = some (.int 32 x1))
    : ∃ (s' : State), WalkLink calls G C s
        { C with
          block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
            "if.end490.i" else "if.then488.i") } s' ∧
      s' = { (s.bind "%48"
          (.int 1 (evalICmp .eq x1 (BitVec.ofNat 32 0)))) with
        pc := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then
          "if.end490.i" else "if.then488.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then485_i G C s hInv hblock h1
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s)
    (b := walkIf_then485_i) (d := "%48") (pred := IPred.eq) (w := 32)
    (a₁ := (.reg "%sp.i.1")) (a₂ := (.imm (.int 32 (BitVec.ofNat 32 0))))
    (t := "if.end490.i") (f := "if.then488.i") (x := x1) (y := (BitVec.ofNat 32 0))
    (by rw [hInv.pc_eq, hblock]; exact walkIf_then485_i_find) rfl rfl h1 rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- The class-A blocks this module states, in the census's order. -/
def walkStepsA : List String :=
  ["NodeBlock21",
   "NodeBlock19",
   "NodeBlock17",
   "LeafBlock15",
   "LeafBlock13",
   "NodeBlock11",
   "LeafBlock9",
   "LeafBlock7",
   "NodeBlock5",
   "NodeBlock",
   "LeafBlock3",
   "LeafBlock1",
   "LeafBlock",
   "if.end.i",
   "if.then53.i",
   "NodeBlock27",
   "LeafBlock25",
   "LeafBlock23",
   "cond.end.i",
   "if.then127.i",
   "if.then141.i",
   "if.else153.i",
   "if.then173.i",
   "sw.bb202.i",
   "NodeBlock31",
   "LeafBlock29",
   "sw.default.i",
   "NodeBlock41",
   "NodeBlock39",
   "LeafBlock37",
   "LeafBlock35",
   "NodeBlock52",
   "NodeBlock50",
   "LeafBlock48",
   "LeafBlock46",
   "NodeBlock62",
   "NodeBlock60",
   "LeafBlock58",
   "LeafBlock56",
   "LeafBlock54",
   "NodeBlock73",
   "NodeBlock71",
   "LeafBlock69",
   "LeafBlock67",
   "NodeBlock83",
   "NodeBlock81",
   "LeafBlock79",
   "LeafBlock77",
   "LeafBlock75",
   "for.end.i.i",
   "if.end67.i",
   "NodeBlock94",
   "NodeBlock92",
   "LeafBlock90",
   "LeafBlock88",
   "NodeBlock105",
   "NodeBlock103",
   "LeafBlock101",
   "if.then485.i"]

#guard walkStepsA.length = 59
#guard walkStepsA.eraseDups.length = walkStepsA.length
#guard walkStepsA.all walkIcmpBrBlocks.contains

-- The class's remainder, exactly: the instanced blocks are the census minus
-- `LeafBlock99`, which the assembly module proves.
#guard (walkIcmpBrBlocks.filter (fun n => !walkStepsA.contains n)) = ["LeafBlock99"]


/-! ### Class C's step shape -/
/-- **Class C: the refusal store.**  Eighteen of the walk's blocks are one shape: a
`gep` of the escape buffer's offset word, a `store` of the refusal position into it,
and a `br` to the arm that records the refusal.  The two existing concrete steps
(`walkIfThen488Step`, `walkIfThen492Step`) are instances of this at their own
`%off` names; stated generically, the class's remaining sixteen are its `find`/`term`
pair and the two register facts.

The offset register is a parameter because the register's number is the block's:
the store's destination is `%e + 8` and the word written is the position's. -/
theorem walkRefusalStoreStep {calls : Calls} (s : State) {b : Block} {off : String}
    {v : String} {dest : String} {e : Nat} {j : Nat}
    (hneq : off ≠ v)
    (hfind : stage2Body.findBlock s.pc = some b)
    (his : b.instrs = [Instr.gep off (.int 8) (.reg "%e") (.imm (.int 64 (BitVec.ofNat 64 8))),
                       Instr.store (.int 64) (.reg v) (.reg off)])
    (ht : b.term = Term.br dest)
    (he : lookupName s.env "%e" = some (.ptr e))
    (hv : lookupName s.env v = some (.int 64 (BitVec.ofNat 64 j)))
    (hj64 : j < 2 ^ 64) :
    step calls stage2Body s =
      .jump { { s with
          env := (off, .ptr (e + 8)) :: s.env
          mem := writeBytes s.mem (e + 8) (wordBytes 8 j) } with
        pc := dest, pre := some s.pc } := by
  have hden : denoteCode calls b.instrs s =
      some { s with
        env := (off, .ptr (e + 8)) :: s.env
        mem := writeBytes s.mem (e + 8) (wordBytes 8 j) } := by
    rw [his]
    conv_lhs => rw [← stateAt_self s]
    rw [LeanLLVM.Refinement.JsonScanLane.denoteCode_gep8_lit_w (calls := calls)
      (env := s.env) (s := s) (d := off) (base := "%e") (a := e)
      (w := 64) (n := BitVec.ofNat 64 8) (by simpa [lookupName] using he) (by decide)]
    simp only [show (BitVec.ofNat 64 8).signExtend 64 = BitVec.ofNat 64 8 from by decide,
      show (BitVec.ofNat 64 8).toNat = 8 from by decide]
    rw [denoteCode_store64_ofNat (calls := calls)
      (env := (off, .ptr (e + 8)) :: s.env) (s := s)
      (v := v) (p := off) (a := e + 8) (j := j)
      (by rw [lookupName_cons_ne _ _ hneq]; exact hv) hj64 (by simp [lookupName]) []]
    rfl
  simp only [step, hfind, hden, ht, execTerm]

/-! ### Class C's instances

*The sixteen.*  `if.then488.i` and `if.then492.i` are the shape at their own `%off`
names and have their steps in the assembly module.
-/

/-- **`if.then16.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then16_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then16.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then16_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then16_i)
    (off := "%off1.i.i") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then16_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then21.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then21_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then21.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i38", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then21_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then21_i)
    (off := "%off1.i.i38") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then21_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then56.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then56_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then56.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i41", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then56_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then56_i)
    (off := "%off1.i.i41") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then56_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then71.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then71_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then71.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i43", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then71_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then71_i)
    (off := "%off1.i.i43") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then71_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`cleanup104.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.cleanup104_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cleanup104.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i45", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.cleanup104_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkCleanup104_i)
    (off := "%off1.i.i45") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkCleanup104_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then130.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then130_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then130.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i66", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then130_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then130_i)
    (off := "%off1.i.i66") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then130_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then147.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then147_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then147.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i68", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then147_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then147_i)
    (off := "%off1.i.i68") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then147_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then159.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then159_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then159.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i70", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then159_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then159_i)
    (off := "%off1.i.i70") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then159_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then176.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then176_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then176.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i72", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then176_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then176_i)
    (off := "%off1.i.i72") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then176_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then192.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then192_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then192.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i74", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then192_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then192_i)
    (off := "%off1.i.i74") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then192_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then205.i`'s target, named.**  `gep %e, 8` and `store %4`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then205_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then205.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i76", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then205_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then205_i)
    (off := "%off1.i.i76") (v := "%4") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then205_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then214.i`'s target, named.**  `gep %e, 8` and `store %4`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then214_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then214.i")
    {j : Nat} (hv : evalOperand s (.reg "%4") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i78", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then214_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then214_i)
    (off := "%off1.i.i78") (v := "%4") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then214_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then249.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `if.then` with the offset recorded. -/
theorem WalkLink.if_then249_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then249.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "if.then", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i80", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then249_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then249_i)
    (off := "%off1.i.i80") (v := "%idxprom.i") (dest := "if.then") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then249_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then418.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `cleanup474.i` with the offset recorded. -/
theorem WalkLink.if_then418_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then418.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "cleanup474.i", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i91", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "cleanup474.i", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then418_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then418_i)
    (off := "%off1.i.i91") (v := "%idxprom.i") (dest := "cleanup474.i") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then418_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.else43.i`'s target, named.**  `gep %e, 8` and `store %idxprom.i`;
the branch takes `cleanup474.i` with the offset recorded. -/
theorem WalkLink.if_else43_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else43.i")
    {j : Nat} (hv : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "cleanup474.i", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i129.i", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "cleanup474.i", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_else43_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_else43_i)
    (off := "%off1.i129.i") (v := "%idxprom.i") (dest := "cleanup474.i") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_else43_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`if.then467.i`'s target, named.**  `gep %e, 8` and `store %q.0.i246`;
the branch takes `cleanup474.i` with the offset recorded. -/
theorem WalkLink.if_then467_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then467.i")
    {j : Nat} (hv : evalOperand s (.reg "%q.0.i246") = some (.int 64 (BitVec.ofNat 64 j)))
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    : ∃ (s' : State), WalkLink calls G C s
        { C with block := "cleanup474.i", eoff := j, refusal := true } s' ∧
      s' = { { s with
          env := ("%off1.i.i113", .ptr (C.stage.e + 8)) :: s.env
          mem := writeBytes s.mem (C.stage.e + 8) (wordBytes 8 j) } with
        pc := "cleanup474.i", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.if_then467_i G C s hInv hblock hv he hj hj64
  refine ⟨s', hlink, ?_⟩
  have hstep := walkRefusalStoreStep (calls := calls) (s := s) (b := walkIf_then467_i)
    (off := "%off1.i.i113") (v := "%q.0.i246") (dest := "cleanup474.i") (e := C.stage.e) (j := j)
    (by decide) (by rw [hInv.pc_eq, hblock]; exact walkIf_then467_i_find) rfl rfl he
    (by simpa only [evalOperand] using hv) hj64
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- The class-C blocks this module states, in the census's order. -/
def walkStepsC : List String :=
  ["if.then16.i",
   "if.then21.i",
   "if.then56.i",
   "if.then71.i",
   "cleanup104.i",
   "if.then130.i",
   "if.then147.i",
   "if.then159.i",
   "if.then176.i",
   "if.then192.i",
   "if.then205.i",
   "if.then214.i",
   "if.then249.i",
   "if.then418.i",
   "if.else43.i",
   "if.then467.i"]

#guard walkStepsC.length = 16
#guard walkStepsC.eraseDups.length = walkStepsC.length
#guard walkStepsC.all walkRefusalBlocks.contains

-- The class's remainder, exactly: the assembly module's two concrete steps and
-- nothing else.
#guard ((walkRefusalBlocks.filter (fun n => !walkStepsC.contains n)) =
  ["if.then488.i", "if.then492.i"])


/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkRefusalStoreStep
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock21_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock19_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock17_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock15_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock13_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock11_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock9_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock7_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock5_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock3_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock1_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then53_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock27_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock25_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock23_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_end_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then127_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then141_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_else153_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then173_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.sw_bb202_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock31_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock29_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.sw_default_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock41_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock39_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock37_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock35_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock52_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock50_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock48_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock46_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock62_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock60_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock58_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock56_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock54_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock73_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock71_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock69_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock67_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock83_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock81_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock79_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock77_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock75_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.for_end_i_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end67_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock94_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock92_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock90_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock88_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock105_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.NodeBlock103_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.LeafBlock101_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then485_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then16_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then21_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then56_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then71_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cleanup104_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then130_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then147_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then159_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then176_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then192_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then205_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then214_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then249_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then418_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_else43_i_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_then467_i_at

end WalkScope

end LeanLLVM.Refinement
