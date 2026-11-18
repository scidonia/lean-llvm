import LeanLLVM.Refinement.JsonStage2WalkScopeClassC

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval

/-! ### Class A's sixty instances

Each is the pinned body's own text, transcribed, with the `findBlock` proof beside
it: `#guard decide (firstFunction stage2Src = some stage2Body)` in
`JsonStage2IR` is what makes the transcription the body's block rather than a
paraphrase of the fixture.  The instances differ only in the comparison, its
width, and the two edges — the proof is one `WalkLink.icmpBr` application in each.

Eight of them branch into one of the ten scan blocks, where `WalkLocal` is not
`True`; those eight carry the block-local clause at that edge as a hypothesis,
because the reset that establishes it is the edge's own work and not this
block's. -/

/-- `NodeBlock21`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock21 : Block :=
  { name := "NodeBlock21",
    instrs := [Instr.icmp "%Pivot22" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 91)))],
    term := Term.condbr (.reg "%Pivot22") "NodeBlock5" "NodeBlock19" }

theorem walkNodeBlock21_find : stage2Body.findBlock "NodeBlock21" = some walkNodeBlock21 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock21]

theorem WalkLink.NodeBlock21 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock21")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 91) = 1 then "NodeBlock5" else "NodeBlock19") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock21_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock19`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock19 : Block :=
  { name := "NodeBlock19",
    instrs := [Instr.icmp "%Pivot20" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123)))],
    term := Term.condbr (.reg "%Pivot20") "NodeBlock11" "NodeBlock17" }

theorem walkNodeBlock19_find : stage2Body.findBlock "NodeBlock19" = some walkNodeBlock19 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock19]

theorem WalkLink.NodeBlock19 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock19")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 123) = 1 then "NodeBlock11" else "NodeBlock17") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock19_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock17`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock17 : Block :=
  { name := "NodeBlock17",
    instrs := [Instr.icmp "%Pivot18" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125)))],
    term := Term.condbr (.reg "%Pivot18") "LeafBlock13" "LeafBlock15" }

theorem walkNodeBlock17_find : stage2Body.findBlock "NodeBlock17" = some walkNodeBlock17 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock17]

theorem WalkLink.NodeBlock17 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock17")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 125) = 1 then "LeafBlock13" else "LeafBlock15") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock17_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock15`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock15 : Block :=
  { name := "LeafBlock15",
    instrs := [Instr.icmp "%SwitchLeaf16" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 125)))],
    term := Term.condbr (.reg "%SwitchLeaf16") "if.then53.i" "sw.default.i" }

theorem walkLeafBlock15_find : stage2Body.findBlock "LeafBlock15" = some walkLeafBlock15 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock15]

theorem WalkLink.LeafBlock15 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock15")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 125) = 1 then "if.then53.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock15_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock13`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock13 : Block :=
  { name := "LeafBlock13",
    instrs := [Instr.icmp "%SwitchLeaf14" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 123)))],
    term := Term.condbr (.reg "%SwitchLeaf14") "if.then.i" "sw.default.i" }

theorem walkLeafBlock13_find : stage2Body.findBlock "LeafBlock13" = some walkLeafBlock13 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock13]

theorem WalkLink.LeafBlock13 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock13")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 123) = 1 then "if.then.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock13_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock11`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock11 : Block :=
  { name := "NodeBlock11",
    instrs := [Instr.icmp "%Pivot12" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 93)))],
    term := Term.condbr (.reg "%Pivot12") "LeafBlock7" "LeafBlock9" }

theorem walkNodeBlock11_find : stage2Body.findBlock "NodeBlock11" = some walkNodeBlock11 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock11]

theorem WalkLink.NodeBlock11 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock11")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 93) = 1 then "LeafBlock7" else "LeafBlock9") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock11_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock9`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock9 : Block :=
  { name := "LeafBlock9",
    instrs := [Instr.icmp "%SwitchLeaf10" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 93)))],
    term := Term.condbr (.reg "%SwitchLeaf10") "if.then53.i" "sw.default.i" }

theorem walkLeafBlock9_find : stage2Body.findBlock "LeafBlock9" = some walkLeafBlock9 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock9]

theorem WalkLink.LeafBlock9 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock9")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 93) = 1 then "if.then53.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock9_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock7`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock7 : Block :=
  { name := "LeafBlock7",
    instrs := [Instr.icmp "%SwitchLeaf8" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 91)))],
    term := Term.condbr (.reg "%SwitchLeaf8") "if.then.i" "sw.default.i" }

theorem walkLeafBlock7_find : stage2Body.findBlock "LeafBlock7" = some walkLeafBlock7 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock7]

theorem WalkLink.LeafBlock7 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock7")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 91) = 1 then "if.then.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock7_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock5`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock5 : Block :=
  { name := "NodeBlock5",
    instrs := [Instr.icmp "%Pivot6" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 44)))],
    term := Term.condbr (.reg "%Pivot6") "LeafBlock" "NodeBlock" }

theorem walkNodeBlock5_find : stage2Body.findBlock "NodeBlock5" = some walkNodeBlock5 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock5]

theorem WalkLink.NodeBlock5 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock5")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 44) = 1 then "LeafBlock" else "NodeBlock") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock5_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock : Block :=
  { name := "NodeBlock",
    instrs := [Instr.icmp "%Pivot" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 58)))],
    term := Term.condbr (.reg "%Pivot") "LeafBlock1" "LeafBlock3" }

theorem walkNodeBlock_find : stage2Body.findBlock "NodeBlock" = some walkNodeBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock]

theorem WalkLink.NodeBlock {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 58) = 1 then "LeafBlock1" else "LeafBlock3") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock3`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock3 : Block :=
  { name := "LeafBlock3",
    instrs := [Instr.icmp "%SwitchLeaf4" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 58)))],
    term := Term.condbr (.reg "%SwitchLeaf4") "if.then173.i" "sw.default.i" }

theorem walkLeafBlock3_find : stage2Body.findBlock "LeafBlock3" = some walkLeafBlock3 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock3]

theorem WalkLink.LeafBlock3 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock3")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 58) = 1 then "if.then173.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock3_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock1`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock1 : Block :=
  { name := "LeafBlock1",
    instrs := [Instr.icmp "%SwitchLeaf2" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 44)))],
    term := Term.condbr (.reg "%SwitchLeaf2") "if.then127.i" "sw.default.i" }

theorem walkLeafBlock1_find : stage2Body.findBlock "LeafBlock1" = some walkLeafBlock1 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock1]

theorem WalkLink.LeafBlock1 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock1")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 44) = 1 then "if.then127.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock1_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock : Block :=
  { name := "LeafBlock",
    instrs := [Instr.icmp "%SwitchLeaf" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 34)))],
    term := Term.condbr (.reg "%SwitchLeaf") "sw.bb202.i" "sw.default.i" }

theorem walkLeafBlock_find : stage2Body.findBlock "LeafBlock" = some walkLeafBlock := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock]

theorem WalkLink.LeafBlock {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 34) = 1 then "sw.bb202.i" else "sw.default.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end.i`: the dispatch's comparison `icmp .ugt i32` and the edge its bit names. -/
def walkIf_end_i : Block :=
  { name := "if.end.i",
    instrs := [Instr.icmp "%cmp19.i" IPred.ugt 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 519)))],
    term := Term.condbr (.reg "%cmp19.i") "if.then21.i" "if.end24.i" }

theorem walkIf_end_i_find : stage2Body.findBlock "if.end.i" = some walkIf_end_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end_i]

theorem WalkLink.if_end_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt x1 (BitVec.ofNat 32 519) = 1 then "if.then21.i" else "if.end24.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_end_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then53.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then53_i : Block :=
  { name := "if.then53.i",
    instrs := [Instr.icmp "%cmp54.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp54.i") "if.then56.i" "if.end59.i" }

theorem walkIf_then53_i_find : stage2Body.findBlock "if.then53.i" = some walkIf_then53_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then53_i]

theorem WalkLink.if_then53_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then53.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then56.i" else "if.end59.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then53_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock27`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock27 : Block :=
  { name := "NodeBlock27",
    instrs := [Instr.icmp "%Pivot28" IPred.slt 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%Pivot28") "LeafBlock23" "LeafBlock25" }

theorem walkNodeBlock27_find : stage2Body.findBlock "NodeBlock27" = some walkNodeBlock27 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock27]

theorem WalkLink.NodeBlock27 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock27")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 3) = 1 then "LeafBlock23" else "LeafBlock25") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock27_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock25`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock25 : Block :=
  { name := "LeafBlock25",
    instrs := [Instr.icmp "%SwitchLeaf26" IPred.eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%SwitchLeaf26") "if.then109.i" "cleanup104.i" }

theorem walkLeafBlock25_find : stage2Body.findBlock "LeafBlock25" = some walkLeafBlock25 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock25]

theorem WalkLink.LeafBlock25 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock25")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock25_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock23`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock23 : Block :=
  { name := "LeafBlock23",
    instrs := [Instr.icmp "%SwitchLeaf24" IPred.eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 0)))],
    term := Term.condbr (.reg "%SwitchLeaf24") "if.then109.i" "cleanup104.i" }

theorem walkLeafBlock23_find : stage2Body.findBlock "LeafBlock23" = some walkLeafBlock23 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock23]

theorem WalkLink.LeafBlock23 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock23")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 0) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock23_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `cond.end.i`: the dispatch's comparison `icmp .ult i8` and the edge its bit names. -/
def walkCond_end_i : Block :=
  { name := "cond.end.i",
    instrs := [Instr.icmp "%16" IPred.ult 8 (.reg "%15") (.imm (.int 8 (BitVec.ofNat 8 2)))],
    term := Term.condbr (.reg "%16") "if.then109.i" "cleanup104.i" }

theorem walkCond_end_i_find : stage2Body.findBlock "cond.end.i" = some walkCond_end_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_end_i]

theorem WalkLink.cond_end_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.end.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%15") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 (BitVec.ofNat 8 2) = 1 then "if.then109.i" else "cleanup104.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkCond_end_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then127.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then127_i : Block :=
  { name := "if.then127.i",
    instrs := [Instr.icmp "%cmp128.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp128.i") "if.then130.i" "if.end133.i" }

theorem walkIf_then127_i_find : stage2Body.findBlock "if.then127.i" = some walkIf_then127_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then127_i]

theorem WalkLink.if_then127_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then127.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then130.i" else "if.end133.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then127_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then141.i`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkIf_then141_i : Block :=
  { name := "if.then141.i",
    instrs := [Instr.icmp "%cmp145.not.i" IPred.eq 8 (.reg "%22") (.imm (.int 8 (BitVec.ofNat 8 3)))],
    term := Term.condbr (.reg "%cmp145.not.i") "if.end150.i" "if.then147.i" }

theorem walkIf_then141_i_find : stage2Body.findBlock "if.then141.i" = some walkIf_then141_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then141_i]

theorem WalkLink.if_then141_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then141.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 3) = 1 then "if.end150.i" else "if.then147.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then141_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.else153.i`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkIf_else153_i : Block :=
  { name := "if.else153.i",
    instrs := [Instr.icmp "%cmp157.not.i" IPred.eq 8 (.reg "%22") (.imm (.int 8 (BitVec.ofNat 8 1)))],
    term := Term.condbr (.reg "%cmp157.not.i") "if.end162.i" "if.then159.i" }

theorem walkIf_else153_i_find : stage2Body.findBlock "if.else153.i" = some walkIf_else153_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else153_i]

theorem WalkLink.if_else153_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else153.i")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%22") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 1) = 1 then "if.end162.i" else "if.then159.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_else153_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.then173.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then173_i : Block :=
  { name := "if.then173.i",
    instrs := [Instr.icmp "%cmp174.i" IPred.eq 32 (.reg "%sp.i.0248") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%cmp174.i") "if.then176.i" "if.end179.i" }

theorem walkIf_then173_i_find : stage2Body.findBlock "if.then173.i" = some walkIf_then173_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then173_i]

theorem WalkLink.if_then173_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then173.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.0248") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.then176.i" else "if.end179.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then173_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `sw.bb202.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkSw_bb202_i : Block :=
  { name := "sw.bb202.i",
    instrs := [Instr.icmp "%cmp203.not.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")],
    term := Term.condbr (.reg "%cmp203.not.i") "if.end207.i" "if.then205.i" }

theorem walkSw_bb202_i_find : stage2Body.findBlock "sw.bb202.i" = some walkSw_bb202_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkSw_bb202_i]

theorem WalkLink.sw_bb202_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.bb202.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "if.end207.i" else "if.then205.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkSw_bb202_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock31`: the dispatch's comparison `icmp .slt i32` and the edge its bit names. -/
def walkNodeBlock31 : Block :=
  { name := "NodeBlock31",
    instrs := [Instr.icmp "%Pivot32" IPred.slt 32 (.reg "%call272.i") (.imm (.int 32 (BitVec.ofNat 32 1)))],
    term := Term.condbr (.reg "%Pivot32") "cleanup339.critedge.i" "LeafBlock29" }

theorem walkNodeBlock31_find : stage2Body.findBlock "NodeBlock31" = some walkNodeBlock31 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock31]

theorem WalkLink.NodeBlock31 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock31")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 32 1) = 1 then "cleanup339.critedge.i" else "LeafBlock29") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock31_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock29`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkLeafBlock29 : Block :=
  { name := "LeafBlock29",
    instrs := [Instr.icmp "%SwitchLeaf30" IPred.eq 32 (.reg "%call272.i") (.imm (.int 32 (BitVec.ofNat 32 1)))],
    term := Term.condbr (.reg "%SwitchLeaf30") "if.then281.i" "if.else285.i" }

theorem walkLeafBlock29_find : stage2Body.findBlock "LeafBlock29" = some walkLeafBlock29 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock29]

theorem WalkLink.LeafBlock29 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock29")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%call272.i") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 1) = 1 then "if.then281.i" else "if.else285.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock29_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `sw.default.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkSw_default_i : Block :=
  { name := "sw.default.i",
    instrs := [Instr.icmp "%cmp343.i" IPred.ult 64 (.reg "%inc.i") (.reg "%nep")],
    term := Term.condbr (.reg "%cmp343.i") "cond.true345.i" "cond.end349.i" }

theorem walkSw_default_i_find : stage2Body.findBlock "sw.default.i" = some walkSw_default_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkSw_default_i]

theorem WalkLink.sw_default_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "sw.default.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%inc.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%nep") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "cond.true345.i" else "cond.end349.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkSw_default_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock41`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock41 : Block :=
  { name := "NodeBlock41",
    instrs := [Instr.icmp "%Pivot42" IPred.slt 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot42") "LeafBlock33" "NodeBlock39" }

theorem walkNodeBlock41_find : stage2Body.findBlock "NodeBlock41" = some walkNodeBlock41 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock41]

theorem WalkLink.NodeBlock41 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock41")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock33" else "NodeBlock39") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock41_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock39`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock39 : Block :=
  { name := "NodeBlock39",
    instrs := [Instr.icmp "%Pivot40" IPred.slt 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot40") "LeafBlock35" "LeafBlock37" }

theorem walkNodeBlock39_find : stage2Body.findBlock "NodeBlock39" = some walkNodeBlock39 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock39]

theorem WalkLink.NodeBlock39 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock39")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock35" else "LeafBlock37") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock39_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock37`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock37 : Block :=
  { name := "LeafBlock37",
    instrs := [Instr.icmp "%SwitchLeaf38" IPred.eq 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf38") "land.rhs.i.preheader" "if.end372.i" }

theorem walkLeafBlock37_find : stage2Body.findBlock "LeafBlock37" = some walkLeafBlock37 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock37]

theorem WalkLink.LeafBlock37 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock37")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "land.rhs.i.preheader" else "if.end372.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock37_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock35`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock35 : Block :=
  { name := "LeafBlock35",
    instrs := [Instr.icmp "%SwitchLeaf36" IPred.eq 8 (.reg "%35") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf36") "land.rhs.i.preheader" "if.end372.i" }

theorem walkLeafBlock35_find : stage2Body.findBlock "LeafBlock35" = some walkLeafBlock35 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock35]

theorem WalkLink.LeafBlock35 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock35")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%35") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "land.rhs.i.preheader" else "if.end372.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock35_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock52`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock52 : Block :=
  { name := "NodeBlock52",
    instrs := [Instr.icmp "%Pivot53" IPred.slt 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot53") "LeafBlock43" "NodeBlock50" }

theorem walkNodeBlock52_find : stage2Body.findBlock "NodeBlock52" = some walkNodeBlock52 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock52]

theorem WalkLink.NodeBlock52 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock52")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock43" else "NodeBlock50") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock52_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock50`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock50 : Block :=
  { name := "NodeBlock50",
    instrs := [Instr.icmp "%Pivot51" IPred.slt 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot51") "LeafBlock46" "LeafBlock48" }

theorem walkNodeBlock50_find : stage2Body.findBlock "NodeBlock50" = some walkNodeBlock50 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock50]

theorem WalkLink.NodeBlock50 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock50")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock46" else "LeafBlock48") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock50_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock48`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock48 : Block :=
  { name := "LeafBlock48",
    instrs := [Instr.icmp "%SwitchLeaf49" IPred.eq 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf49") "if.end372.i" "while.body370.i" }

theorem walkLeafBlock48_find : stage2Body.findBlock "LeafBlock48" = some walkLeafBlock48 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock48]

theorem WalkLink.LeafBlock48 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock48")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf49", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body370.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "if.end372.i" else "while.body370.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock48_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `LeafBlock46`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock46 : Block :=
  { name := "LeafBlock46",
    instrs := [Instr.icmp "%SwitchLeaf47" IPred.eq 8 (.reg "%36") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf47") "if.end372.i" "while.body370.i" }

theorem walkLeafBlock46_find : stage2Body.findBlock "LeafBlock46" = some walkLeafBlock46 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock46]

theorem WalkLink.LeafBlock46 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock46")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%36") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body370.i" }
      { stateAt (("%SwitchLeaf47", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body370.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "if.end372.i" else "while.body370.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock46_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `NodeBlock62`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock62 : Block :=
  { name := "NodeBlock62",
    instrs := [Instr.icmp "%Pivot63" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%Pivot63") "LeafBlock54" "NodeBlock60" }

theorem walkNodeBlock62_find : stage2Body.findBlock "NodeBlock62" = some walkNodeBlock62 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock62]

theorem WalkLink.NodeBlock62 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock62")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock54" else "NodeBlock60") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock62_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock60`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock60 : Block :=
  { name := "NodeBlock60",
    instrs := [Instr.icmp "%Pivot61" IPred.slt 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%Pivot61") "LeafBlock56" "LeafBlock58" }

theorem walkNodeBlock60_find : stage2Body.findBlock "NodeBlock60" = some walkNodeBlock60 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock60]

theorem WalkLink.NodeBlock60 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock60")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock56" else "LeafBlock58") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock60_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock58`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock58 : Block :=
  { name := "LeafBlock58",
    instrs := [Instr.icmp "%SwitchLeaf59" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%SwitchLeaf59") "if.then413.i" "if.else405.i" }

theorem walkLeafBlock58_find : stage2Body.findBlock "LeafBlock58" = some walkLeafBlock58 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock58]

theorem WalkLink.LeafBlock58 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock58")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.then413.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock58_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock56`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock56 : Block :=
  { name := "LeafBlock56",
    instrs := [Instr.icmp "%SwitchLeaf57" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%SwitchLeaf57") "if.then403.i" "if.else405.i" }

theorem walkLeafBlock56_find : stage2Body.findBlock "LeafBlock56" = some walkLeafBlock56 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock56]

theorem WalkLink.LeafBlock56 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock56")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then "if.then403.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock56_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock54`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock54 : Block :=
  { name := "LeafBlock54",
    instrs := [Instr.icmp "%SwitchLeaf55" IPred.eq 8 (.reg "%8") (.imm (.int 8 (BitVec.ofNat 8 102)))],
    term := Term.condbr (.reg "%SwitchLeaf55") "if.then397.i" "if.else405.i" }

theorem walkLeafBlock54_find : stage2Body.findBlock "LeafBlock54" = some walkLeafBlock54 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock54]

theorem WalkLink.LeafBlock54 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock54")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%8") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then "if.then397.i" else "if.else405.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock54_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock73`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock73 : Block :=
  { name := "NodeBlock73",
    instrs := [Instr.icmp "%Pivot74" IPred.slt 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot74") "LeafBlock64" "NodeBlock71" }

theorem walkNodeBlock73_find : stage2Body.findBlock "NodeBlock73" = some walkNodeBlock73 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock73]

theorem WalkLink.NodeBlock73 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock73")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock64" else "NodeBlock71") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock73_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock71`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock71 : Block :=
  { name := "NodeBlock71",
    instrs := [Instr.icmp "%Pivot72" IPred.slt 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot72") "LeafBlock67" "LeafBlock69" }

theorem walkNodeBlock71_find : stage2Body.findBlock "NodeBlock71" = some walkNodeBlock71 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock71]

theorem WalkLink.NodeBlock71 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock71")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock67" else "LeafBlock69") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock71_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock69`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock69 : Block :=
  { name := "LeafBlock69",
    instrs := [Instr.icmp "%SwitchLeaf70" IPred.eq 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf70") "while.end.i" "while.body.i104" }

theorem walkLeafBlock69_find : stage2Body.findBlock "LeafBlock69" = some walkLeafBlock69 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock69]

theorem WalkLink.LeafBlock69 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock69")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf70", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body.i104", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock69_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `LeafBlock67`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock67 : Block :=
  { name := "LeafBlock67",
    instrs := [Instr.icmp "%SwitchLeaf68" IPred.eq 8 (.reg "%40") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf68") "while.end.i" "while.body.i104" }

theorem walkLeafBlock67_find : stage2Body.findBlock "LeafBlock67" = some walkLeafBlock67 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock67]

theorem WalkLink.LeafBlock67 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock67")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%40") = some (.int 8 x1))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf68", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body.i104", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock67_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) hf

/-- `NodeBlock83`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock83 : Block :=
  { name := "NodeBlock83",
    instrs := [Instr.icmp "%Pivot84" IPred.slt 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%Pivot84") "LeafBlock75" "NodeBlock81" }

theorem walkNodeBlock83_find : stage2Body.findBlock "NodeBlock83" = some walkNodeBlock83 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock83]

theorem WalkLink.NodeBlock83 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock83")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 110) = 1 then "LeafBlock75" else "NodeBlock81") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock83_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock81`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock81 : Block :=
  { name := "NodeBlock81",
    instrs := [Instr.icmp "%Pivot82" IPred.slt 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%Pivot82") "LeafBlock77" "LeafBlock79" }

theorem walkNodeBlock81_find : stage2Body.findBlock "NodeBlock81" = some walkNodeBlock81 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock81]

theorem WalkLink.NodeBlock81 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock81")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 116) = 1 then "LeafBlock77" else "LeafBlock79") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock81_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock79`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock79 : Block :=
  { name := "LeafBlock79",
    instrs := [Instr.icmp "%SwitchLeaf80" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 116)))],
    term := Term.condbr (.reg "%SwitchLeaf80") "if.end48.i" "if.else43.i" }

theorem walkLeafBlock79_find : stage2Body.findBlock "LeafBlock79" = some walkLeafBlock79 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock79]

theorem WalkLink.LeafBlock79 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock79")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 116) = 1 then "if.end48.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock79_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock77`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock77 : Block :=
  { name := "LeafBlock77",
    instrs := [Instr.icmp "%SwitchLeaf78" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 110)))],
    term := Term.condbr (.reg "%SwitchLeaf78") "if.then42.i" "if.else43.i" }

theorem walkLeafBlock77_find : stage2Body.findBlock "LeafBlock77" = some walkLeafBlock77 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock77]

theorem WalkLink.LeafBlock77 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock77")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 110) = 1 then "if.then42.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock77_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock75`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock75 : Block :=
  { name := "LeafBlock75",
    instrs := [Instr.icmp "%SwitchLeaf76" IPred.eq 8 (.reg "%41") (.imm (.int 8 (BitVec.ofNat 8 102)))],
    term := Term.condbr (.reg "%SwitchLeaf76") "if.then37.i" "if.else43.i" }

theorem walkLeafBlock75_find : stage2Body.findBlock "LeafBlock75" = some walkLeafBlock75 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock75]

theorem WalkLink.LeafBlock75 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock75")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%41") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 102) = 1 then "if.then37.i" else "if.else43.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock75_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `for.end.i.i`: the dispatch's comparison `icmp .eq i64` and the edge its bit names. -/
def walkFor_end_i_i : Block :=
  { name := "for.end.i.i",
    instrs := [Instr.icmp "%cmp11.not.i.i" IPred.eq 64 (.reg "%sub54.i") (.reg "%ln.0.i")],
    term := Term.condbr (.reg "%cmp11.not.i.i") "if.end67.i" "if.then57.i" }

theorem walkFor_end_i_i_find : stage2Body.findBlock "for.end.i.i" = some walkFor_end_i_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkFor_end_i_i]

theorem WalkLink.for_end_i_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "for.end.i.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%sub54.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%ln.0.i") = some (.int 64 x2))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 x2 = 1 then "if.end67.i" else "if.then57.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkFor_end_i_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `if.end67.i`: the dispatch's comparison `icmp .ult i64` and the edge its bit names. -/
def walkIf_end67_i : Block :=
  { name := "if.end67.i",
    instrs := [Instr.icmp "%cmp6919.i" IPred.ult 64 (.reg "%ee.0.lcssa.i") (.reg "%cond.i")],
    term := Term.condbr (.reg "%cmp6919.i") "land.rhs71.i" "while.end78.i" }

theorem walkIf_end67_i_find : stage2Body.findBlock "if.end67.i" = some walkIf_end67_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end67_i]

theorem WalkLink.if_end67_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end67.i")
    {x1 : BitVec 64} (h1 : evalOperand s (.reg "%ee.0.lcssa.i") = some (.int 64 x1))
    {x2 : BitVec 64} (h2 : evalOperand s (.reg "%cond.i") = some (.int 64 x2))
    (hl : WalkLocal { C with block := "land.rhs71.i" }
      { stateAt (("%cmp6919.i", .int 1 (evalICmp .ult x1 x2)) :: s.env) s with pc := "land.rhs71.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "land.rhs71.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_end67_i_find) rfl rfl h1 h2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `NodeBlock94`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock94 : Block :=
  { name := "NodeBlock94",
    instrs := [Instr.icmp "%Pivot95" IPred.slt 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot95") "LeafBlock85" "NodeBlock92" }

theorem walkNodeBlock94_find : stage2Body.findBlock "NodeBlock94" = some walkNodeBlock94 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock94]

theorem WalkLink.NodeBlock94 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock94")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock85" else "NodeBlock92") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock94_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock92`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock92 : Block :=
  { name := "NodeBlock92",
    instrs := [Instr.icmp "%Pivot93" IPred.slt 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot93") "LeafBlock88" "LeafBlock90" }

theorem walkNodeBlock92_find : stage2Body.findBlock "NodeBlock92" = some walkNodeBlock92 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock92]

theorem WalkLink.NodeBlock92 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock92")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock88" else "LeafBlock90") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock92_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock90`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock90 : Block :=
  { name := "LeafBlock90",
    instrs := [Instr.icmp "%SwitchLeaf91" IPred.eq 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf91") "while.body76.i" "while.end78.i" }

theorem walkLeafBlock90_find : stage2Body.findBlock "LeafBlock90" = some walkLeafBlock90 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock90]

theorem WalkLink.LeafBlock90 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock90")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf91", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body76.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.body76.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock90_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `LeafBlock88`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock88 : Block :=
  { name := "LeafBlock88",
    instrs := [Instr.icmp "%SwitchLeaf89" IPred.eq 8 (.reg "%46") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf89") "while.body76.i" "while.end78.i" }

theorem walkLeafBlock88_find : stage2Body.findBlock "LeafBlock88" = some walkLeafBlock88 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock88]

theorem WalkLink.LeafBlock88 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock88")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%46") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body76.i" }
      { stateAt (("%SwitchLeaf89", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body76.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.body76.i" else "while.end78.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock88_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `NodeBlock105`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock105 : Block :=
  { name := "NodeBlock105",
    instrs := [Instr.icmp "%Pivot106" IPred.slt 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%Pivot106") "LeafBlock96" "NodeBlock103" }

theorem walkNodeBlock105_find : stage2Body.findBlock "NodeBlock105" = some walkNodeBlock105 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock105]

theorem WalkLink.NodeBlock105 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock105")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 13) = 1 then "LeafBlock96" else "NodeBlock103") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock105_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `NodeBlock103`: the dispatch's comparison `icmp .slt i8` and the edge its bit names. -/
def walkNodeBlock103 : Block :=
  { name := "NodeBlock103",
    instrs := [Instr.icmp "%Pivot104" IPred.slt 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%Pivot104") "LeafBlock99" "LeafBlock101" }

theorem walkNodeBlock103_find : stage2Body.findBlock "NodeBlock103" = some walkNodeBlock103 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkNodeBlock103]

theorem WalkLink.NodeBlock103 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock103")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .slt x1 (BitVec.ofNat 8 32) = 1 then "LeafBlock99" else "LeafBlock101") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkNodeBlock103_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-- `LeafBlock101`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock101 : Block :=
  { name := "LeafBlock101",
    instrs := [Instr.icmp "%SwitchLeaf102" IPred.eq 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 32)))],
    term := Term.condbr (.reg "%SwitchLeaf102") "while.body462.i" "if.then467.i" }

theorem walkLeafBlock101_find : stage2Body.findBlock "LeafBlock101" = some walkLeafBlock101 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock101]

theorem WalkLink.LeafBlock101 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock101")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf102", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 32))) :: s.env) s with pc := "while.body462.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 32) = 1 then "while.body462.i" else "if.then467.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock101_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `LeafBlock99`: the dispatch's comparison `icmp .eq i8` and the edge its bit names. -/
def walkLeafBlock99 : Block :=
  { name := "LeafBlock99",
    instrs := [Instr.icmp "%SwitchLeaf100" IPred.eq 8 (.reg "%47") (.imm (.int 8 (BitVec.ofNat 8 13)))],
    term := Term.condbr (.reg "%SwitchLeaf100") "while.body462.i" "if.then467.i" }

theorem walkLeafBlock99_find : stage2Body.findBlock "LeafBlock99" = some walkLeafBlock99 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLeafBlock99]

theorem WalkLink.LeafBlock99 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock99")
    {x1 : BitVec 8} (h1 : evalOperand s (.reg "%47") = some (.int 8 x1))
    (hl : WalkLocal { C with block := "while.body462.i" }
      { stateAt (("%SwitchLeaf100", .int 1 (evalICmp .eq x1 (BitVec.ofNat 8 13))) :: s.env) s with pc := "while.body462.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 8 13) = 1 then "while.body462.i" else "if.then467.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkLeafBlock99_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hl (by simp [WalkLocal])

/-- `if.then485.i`: the dispatch's comparison `icmp .eq i32` and the edge its bit names. -/
def walkIf_then485_i : Block :=
  { name := "if.then485.i",
    instrs := [Instr.icmp "%48" IPred.eq 32 (.reg "%sp.i.1") (.imm (.int 32 (BitVec.ofNat 32 0)))],
    term := Term.condbr (.reg "%48") "if.end490.i" "if.then488.i" }

theorem walkIf_then485_i_find : stage2Body.findBlock "if.then485.i" = some walkIf_then485_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then485_i]

theorem WalkLink.if_then485_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then485.i")
    {x1 : BitVec 32} (h1 : evalOperand s (.reg "%sp.i.1") = some (.int 32 x1))
    : ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq x1 (BitVec.ofNat 32 0) = 1 then "if.end490.i" else "if.then488.i") } s' := by
  exact WalkLink.icmpBr (G := G) (C := C) (s := s) hInv (by rw [hblock]; exact walkIf_then485_i_find) rfl rfl h1 (by rfl) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by simp [WalkLocal]) (by simp [WalkLocal])

/-! ### Class B's ten instances -/

/-- `cond.true.i`: no instructions, and the edge it takes. -/
def walkCond_true_i : Block :=
  { name := "cond.true.i", instrs := [], term := Term.br "NodeBlock27" }

theorem walkCond_true_i_find : stage2Body.findBlock "cond.true.i" = some walkCond_true_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_true_i]

theorem WalkLink.cond_true_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.true.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock27" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkCond_true_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `land.rhs.i.preheader`: no instructions, and the edge it takes. -/
def walkLand_rhs_i_preheader : Block :=
  { name := "land.rhs.i.preheader", instrs := [], term := Term.br "land.rhs.i" }

theorem walkLand_rhs_i_preheader_find : stage2Body.findBlock "land.rhs.i.preheader" = some walkLand_rhs_i_preheader := by
  simp [stage2Body, Function.findBlock, findBlockList, walkLand_rhs_i_preheader]

theorem WalkLink.land_rhs_i_preheader {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i.preheader")
    (hloc : WalkLocal { C with block := "land.rhs.i" } { s with pc := "land.rhs.i", pre := some s.pc })
    : ∃ s', WalkLink calls G C s { C with block := "land.rhs.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkLand_rhs_i_preheader_find) rfl rfl hloc
    (hne := by rw [hblock]; decide)

/-- `if.else387.i`: no instructions, and the edge it takes. -/
def walkIf_else387_i : Block :=
  { name := "if.else387.i", instrs := [], term := Term.br "NodeBlock62" }

theorem walkIf_else387_i_find : stage2Body.findBlock "if.else387.i" = some walkIf_else387_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else387_i]

theorem WalkLink.if_else387_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else387.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock62" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else387_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then397.i`: no instructions, and the edge it takes. -/
def walkIf_then397_i : Block :=
  { name := "if.then397.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_then397_i_find : stage2Body.findBlock "if.then397.i" = some walkIf_then397_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then397_i]

theorem WalkLink.if_then397_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then397.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then397_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then403.i`: no instructions, and the edge it takes. -/
def walkIf_then403_i : Block :=
  { name := "if.then403.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_then403_i_find : stage2Body.findBlock "if.then403.i" = some walkIf_then403_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then403_i]

theorem WalkLink.if_then403_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then403.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then403_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.else405.i`: no instructions, and the edge it takes. -/
def walkIf_else405_i : Block :=
  { name := "if.else405.i", instrs := [], term := Term.br "if.then413.i" }

theorem walkIf_else405_i_find : stage2Body.findBlock "if.else405.i" = some walkIf_else405_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else405_i]

theorem WalkLink.if_else405_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else405.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.then413.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else405_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.else.i`: no instructions, and the edge it takes. -/
def walkIf_else_i : Block :=
  { name := "if.else.i", instrs := [], term := Term.br "NodeBlock83" }

theorem walkIf_else_i_find : stage2Body.findBlock "if.else.i" = some walkIf_else_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_else_i]

theorem WalkLink.if_else_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else.i")
    : ∃ s', WalkLink calls G C s { C with block := "NodeBlock83" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_else_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then37.i`: no instructions, and the edge it takes. -/
def walkIf_then37_i : Block :=
  { name := "if.then37.i", instrs := [], term := Term.br "if.end48.i" }

theorem walkIf_then37_i_find : stage2Body.findBlock "if.then37.i" = some walkIf_then37_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then37_i]

theorem WalkLink.if_then37_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then37.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.end48.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then37_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

/-- `if.then42.i`: no instructions, and the edge it takes. -/
def walkIf_then42_i : Block :=
  { name := "if.then42.i", instrs := [], term := Term.br "if.end48.i" }

theorem walkIf_then42_i_find : stage2Body.findBlock "if.then42.i" = some walkIf_then42_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_then42_i]

theorem WalkLink.if_then42_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.then42.i")
    : ∃ s', WalkLink calls G C s { C with block := "if.end48.i" } s' := by
  exact WalkLink.br (G := G) (C := C) (s := s) hInv
    (by rw [hblock]; exact walkIf_then42_i_find) rfl rfl (by simp [WalkLocal])
    (hne := by rw [hblock]; decide)

end LeanLLVM.Refinement
