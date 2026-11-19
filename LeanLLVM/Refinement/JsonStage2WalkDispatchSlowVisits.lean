/-
# The slow scan's visit states, named

`land.rhs.i103`'s visit is one landing, two dispatch pivots and one of three class
leaves, ending at `while.body.i104` (continue) or `while.end.i` (stop).  The individual
links already exist — `WalkLink.land_rhs_i103` (`JsonStage2WalkPhi`), `WalkLink.NodeBlock73`,
`WalkLink.NodeBlock71`, `WalkLink.LeafBlock64/67/69` (`JsonStage2WalkScopeClassAB`,
`JsonStage2WalkRest`), `WalkLink.while_end_i` and the class's exit chain — so this module
adds only the states a round proof must name and compares, and the landing's named target.

A state a proof compares, peels, or states a hypothesis at has to be a module-level name;
`landRhsI103OutAt` is `WalkLink.land_rhs_i103`'s successor, byte and all.
-/
import LeanLLVM.Refinement.JsonScanLane
import LeanLLVM.Refinement.JsonStage2WalkDispatchSlowScan

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-- The state `land.rhs.i103` leaves: the counter's selection, the byte's address and the
byte, at the dispatch's entry `NodeBlock73`. -/
def landRhsI103OutAt (s : State) (idx : BitVec 64) (a q : Nat) : State :=
  { stateAt (cells
      [("%40", .int 8 (BitVec.ofNat 8 q)),
       ("%arrayidx5.i", .ptr (a + (idx.signExtend 64).toNat))]
      (s.bindAll [("%ee.011.i", .int 64 idx)]).env)
      (s.bindAll [("%ee.011.i", .int 64 idx)]) with
    pc := "NodeBlock73"
    pre := some (s.bindAll [("%ee.011.i", .int 64 idx)]).pc }

/-- **`land.rhs.i103`'s target, named.**  Off `WalkLink.land_rhs_i103`: the counter's
`phi`, the address `%3 + counter` and the byte, at `NodeBlock73`. -/
theorem WalkLink.landRhsI103_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i103")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body.i104", (Operand.reg "%inc.i105")),
      ("cond.end.i96", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock73" } s' ∧
      s' = landRhsI103OutAt s e G.b b.toNat := by
  obtain ⟨s', hlink⟩ :=
    WalkLink.land_rhs_i103 G C s hInv hblock hpre hin hv hpos hread
  refine ⟨s', hlink, ?_⟩
  let specs : List PhiSpec :=
    [{ dst := "%ee.011.i", ty := Ty.int 64,
       incoming := [("while.body.i104", (Operand.reg "%inc.i105")),
         ("cond.end.i96", (Operand.reg "%idxprom.i"))] }]
  let vs : List (String × Value) := [("%ee.011.i", .int 64 e)]
  have hspan : PhiSelects s p specs vs := PhiSelects.cons hin hv PhiSelects.nil
  have hstep := walkPhiGepLoadBrStep (calls := calls) (s := s) (B := walkLand_rhs_i103)
    (specs := specs) (vs := vs) (p := p)
    (ap := "%arrayidx5.i") (ld := "%40") (base := "%3") (off := "%ee.011.i")
    (dest := "NodeBlock73") (a := G.b) (j := (e.signExtend 64).toNat) (b := b)
    (by rw [hInv.pc_eq, hblock]; exact walkLand_rhs_i103_find) rfl rfl hpre
    hspan hInv.ptrs.1
    (by
      dsimp only [vs]
      rw [show s.bindAll [("%ee.011.i", .int 64 e)] =
        stateAt (("%ee.011.i", .int 64 e) :: s.env) s from rfl]
      simp only [stateAt, lookupName_cons_self, BitVec.ofNat_toNat,
        BitVec.setWidth_eq, BitVec.signExtend_eq])
    hpos hread
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)


/-- `NodeBlock73`'s target, named: the first pivot's bit and the edge it names. -/
theorem WalkLink.nodeBlock73_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock73")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x)) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .slt x (BitVec.ofNat 8 13) = 1 then "LeafBlock64" else "NodeBlock71") } s' ∧
      s' = { s.bind "%Pivot74" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) with
        pc := (if evalICmp .slt x (BitVec.ofNat 8 13) = 1 then "LeafBlock64" else "NodeBlock71")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ :=
    WalkLink.NodeBlock73 G C s hInv hblock
      (evalOperand_reg_of s.env s "%40" (.int 8 x) h40)
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s) (b := walkNodeBlock73)
    (d := "%Pivot74") (pred := IPred.slt) (w := 8)
    (a₁ := .reg "%40") (a₂ := .imm (.int 8 (BitVec.ofNat 8 13)))
    (t := "LeafBlock64") (f := "NodeBlock71") (x := x) (y := BitVec.ofNat 8 13)
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock73_find) rfl rfl
    (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- `NodeBlock71`'s target, named: the second pivot's bit and the edge it names. -/
theorem WalkLink.nodeBlock71_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "NodeBlock71")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x)) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .slt x (BitVec.ofNat 8 32) = 1 then "LeafBlock67" else "LeafBlock69") } s' ∧
      s' = { s.bind "%Pivot72" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32))) with
        pc := (if evalICmp .slt x (BitVec.ofNat 8 32) = 1 then "LeafBlock67" else "LeafBlock69")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ :=
    WalkLink.NodeBlock71 G C s hInv hblock
      (evalOperand_reg_of s.env s "%40" (.int 8 x) h40)
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s) (b := walkNodeBlock71)
    (d := "%Pivot72") (pred := IPred.slt) (w := 8)
    (a₁ := .reg "%40") (a₂ := .imm (.int 8 (BitVec.ofNat 8 32)))
    (t := "LeafBlock67") (f := "LeafBlock69") (x := x) (y := BitVec.ofNat 8 32)
    (by rw [hInv.pc_eq, hblock]; exact walkNodeBlock71_find) rfl rfl
    (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- `LeafBlock64`'s target, named: the range leaf, stop or continue. -/
theorem WalkLink.leafBlock64_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock64")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (cells [("%SwitchLeaf66", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off65", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body.i104", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
            then "while.end.i" else "while.body.i104") } s' ∧
      s' = { stateAt (cells [("%SwitchLeaf66", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1))), ("%.off65", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "while.end.i" else "while.body.i104")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock64 G C s hInv hblock h40 hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkAddIcmpBrStep (calls := calls) (s := s) (b := walkLeafBlock64)
    (reg := "%40") (off := "%.off65") (d := "%SwitchLeaf66")
    (c := BitVec.ofNat 8 247) (one := BitVec.ofNat 8 1)
    (tl := "while.end.i") (fl := "while.body.i104") (x := x)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock64_find) rfl rfl h40
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- `LeafBlock67`'s target, named: the `13` leaf, stop or continue. -/
theorem WalkLink.leafBlock67_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock67")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf68", .int 1 (evalICmp .eq x (BitVec.ofNat 8 13))) :: s.env) s with
        pc := "while.body.i104", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .eq x (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104") } s' ∧
      s' = { s.bind "%SwitchLeaf68" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 13))) with
        pc := (if evalICmp .eq x (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock67 G C s hInv hblock
      (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s) (b := walkLeafBlock67)
    (d := "%SwitchLeaf68") (pred := IPred.eq) (w := 8)
    (a₁ := .reg "%40") (a₂ := .imm (.int 8 (BitVec.ofNat 8 13)))
    (t := "while.end.i") (f := "while.body.i104") (x := x) (y := BitVec.ofNat 8 13)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock67_find) rfl rfl
    (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- `LeafBlock69`'s target, named: the `32` leaf, stop or continue. -/
theorem WalkLink.leafBlock69_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock69")
    {x : BitVec 8} (h40 : lookupName s.env "%40" = some (.int 8 x))
    (hf : WalkLocal { C with block := "while.body.i104" }
      { stateAt (("%SwitchLeaf70", .int 1 (evalICmp .eq x (BitVec.ofNat 8 32))) :: s.env) s with
        pc := "while.body.i104", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .eq x (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104") } s' ∧
      s' = { s.bind "%SwitchLeaf70" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 32))) with
        pc := (if evalICmp .eq x (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock69 G C s hInv hblock
      (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) hf
  refine ⟨s', hlink, ?_⟩
  have hstep := walkIcmpBrStep (calls := calls) (s := s) (b := walkLeafBlock69)
    (d := "%SwitchLeaf70") (pred := IPred.eq) (w := 8)
    (a₁ := .reg "%40") (a₂ := .imm (.int 8 (BitVec.ofNat 8 32)))
    (t := "while.end.i") (f := "while.body.i104") (x := x) (y := BitVec.ofNat 8 32)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock69_find) rfl rfl
    (evalOperand_reg_of s.env s "%40" (.int 8 x) h40) rfl
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- The byte's value at the landing: `%40` is the loaded byte. -/
theorem landRhsI103OutAt_byte {m0 : Mem} {G : WalkGeom m0} (s : State) (e : BitVec 64) (b : UInt8) :
    lookupName (landRhsI103OutAt s e G.b b.toNat).env "%40" =
      some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
  simp [landRhsI103OutAt, stateAt, cells, lookupName_cons_self]


/-- The first dispatch node's state: `%Pivot74` and the class edge it names. -/
def landRhsI103Node73S (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) : State :=
  { (landRhsI103OutAt s e a b.toNat).bind "%Pivot74"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13))) with
    pc := (if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock64" else "NodeBlock71")
    pre := some (landRhsI103OutAt s e a b.toNat).pc }

/-- The second dispatch node's state: `%Pivot72` and the class edge it names. -/
def landRhsI103Node71S (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) : State :=
  { (landRhsI103Node73S s e a b).bind "%Pivot72"
      (.int 1 (evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32))) with
    pc := (if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
      then "LeafBlock67" else "LeafBlock69")
    pre := some (landRhsI103Node73S s e a b).pc }

/-- `LeafBlock64`'s state: the range leaf's bit and the edge it names. -/
def landRhsI103Leaf64S (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) : State :=
  { stateAt (cells [("%SwitchLeaf66", .int 1 (evalICmp .ule
        (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
      ("%.off65", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 247))]
      (landRhsI103Node73S s e a b).env) (landRhsI103Node73S s e a b) with
    pc := (if evalICmp .ule (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "while.end.i" else "while.body.i104")
    pre := some (landRhsI103Node73S s e a b).pc }

/-- `LeafBlock67`'s state: the `13` leaf's bit and the edge it names. -/
def landRhsI103Leaf67S (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) : State :=
  { stateAt (("%SwitchLeaf68", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat)
        (BitVec.ofNat 8 13))) :: (landRhsI103Node71S s e a b).env)
      (landRhsI103Node71S s e a b) with
    pc := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
      then "while.end.i" else "while.body.i104")
    pre := some (landRhsI103Node71S s e a b).pc }

/-- `LeafBlock69`'s state: the `32` leaf's bit and the edge it names. -/
def landRhsI103Leaf69S (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) : State :=
  { stateAt (("%SwitchLeaf70", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat)
        (BitVec.ofNat 8 32))) :: (landRhsI103Node71S s e a b).env)
      (landRhsI103Node71S s e a b) with
    pc := (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
      then "while.end.i" else "while.body.i104")
    pre := some (landRhsI103Node71S s e a b).pc }

/-- **The slow scan's dispatch, composed**: landing, both pivots and the class leaf, as one
`WalkSegment` of 3 (range leaf) or 4 steps, ending at `while.body.i104` (continue) or
`while.end.i` (stop).  The leaf's body arm takes the caller's `WalkLocal` at
`while.body.i104` — `ScanCount` with the budget `c - p ≤ C.inner` and `p < c`. -/
theorem walkScanLinksI103 {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i103")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body.i104", (Operand.reg "%inc.i105")),
      ("cond.end.i96", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b])
    (hf64 : WalkLocal { C with block := "while.body.i104" } (landRhsI103Leaf64S s e G.b b))
    (hf67 : WalkLocal { C with block := "while.body.i104" } (landRhsI103Leaf67S s e G.b b))
    (hf69 : WalkLocal { C with block := "while.body.i104" } (landRhsI103Leaf69S s e G.b b)) :
    ∃ (n : Nat) (s' : State), n ≤ 4 ∧
      WalkSegment calls G C s
        { C with block := (if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
            then (if evalICmp .ule (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 247)
              (BitVec.ofNat 8 1) = 1 then "while.end.i" else "while.body.i104")
            else if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
            then (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
              then "while.end.i" else "while.body.i104")
            else (if evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
              then "while.end.i" else "while.body.i104")) } s' n := by
  obtain ⟨s1, hl1, hs1⟩ :=
    WalkLink.landRhsI103_at (calls := calls) (G := G) (C := C) (s := s) hInv hblock hpre hin hv hpos hread
  rw [hs1] at hl1
  obtain ⟨s2, hl2, hs2⟩ :=
    WalkLink.nodeBlock73_at (calls := calls) (G := G) (C := { C with block := "NodeBlock73" })
      (s := landRhsI103OutAt s e G.b b.toNat) hl1.inv' rfl (landRhsI103OutAt_byte s e b)
  have hs2' : s2 = landRhsI103Node73S s e G.b b := by rw [hs2]; rfl
  have h40₂ : lookupName (landRhsI103Node73S s e G.b b).env "%40" =
      some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
    dsimp only [landRhsI103Node73S, State.bind]
    rw [lookupName_cons_ne (n := "%40") _ _ (by decide)]
    exact landRhsI103OutAt_byte s e b
  rw [hs2'] at hl2
  by_cases h13 : evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
  · rw [if_pos h13] at hl2
    obtain ⟨s3, hl3, hs3⟩ :=
      WalkLink.leafBlock64_at (calls := calls) (G := G) (C := { C with block := "LeafBlock64" })
        (s := landRhsI103Node73S s e G.b b) hl2.inv' rfl h40₂ hf64
    have hs3' : s3 = landRhsI103Leaf64S s e G.b b := by rw [hs3]; rfl
    have hseg := ((WalkSegment.of_link hl1).trans (WalkSegment.of_link hl2)).trans
      (WalkSegment.of_link hl3)
    rw [hs3'] at hseg
    refine ⟨3, s3, by omega, ?_⟩
    rw [hs3']
    simpa only [if_pos h13] using hseg
  · rw [if_neg h13] at hl2
    by_cases h32 : evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
    · obtain ⟨s3, hl3, hs3⟩ :=
        WalkLink.nodeBlock71_at (calls := calls) (G := G) (C := { C with block := "NodeBlock71" })
          (s := landRhsI103Node73S s e G.b b) hl2.inv' rfl h40₂
      have hs3' : s3 = landRhsI103Node71S s e G.b b := by rw [hs3]; rfl
      have h40₃ : lookupName (landRhsI103Node71S s e G.b b).env "%40" =
          some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
        dsimp only [landRhsI103Node71S, landRhsI103Node73S, State.bind]
        rw [lookupName_cons_ne (n := "%40") _ _ (by decide),
          lookupName_cons_ne (n := "%40") _ _ (by decide)]
        exact landRhsI103OutAt_byte s e b
      rw [hs3'] at hl3
      rw [if_pos h32] at hl3
      obtain ⟨s4, hl4, hs4⟩ :=
        WalkLink.leafBlock67_at (calls := calls) (G := G) (C := { C with block := "LeafBlock67" })
          (s := landRhsI103Node71S s e G.b b) hl3.inv' rfl h40₃ hf67
      have hs4' : s4 = landRhsI103Leaf67S s e G.b b := by rw [hs4]; rfl
      have hseg := (((WalkSegment.of_link hl1).trans (WalkSegment.of_link hl2)).trans
        (WalkSegment.of_link hl3)).trans (WalkSegment.of_link hl4)
      rw [hs4'] at hseg
      refine ⟨4, s4, by omega, ?_⟩
      rw [hs4']
      simpa only [if_neg h13, if_pos h32] using hseg
    · obtain ⟨s3, hl3, hs3⟩ :=
        WalkLink.nodeBlock71_at (calls := calls) (G := G) (C := { C with block := "NodeBlock71" })
          (s := landRhsI103Node73S s e G.b b) hl2.inv' rfl h40₂
      have hs3' : s3 = landRhsI103Node71S s e G.b b := by rw [hs3]; rfl
      have h40₃ : lookupName (landRhsI103Node71S s e G.b b).env "%40" =
          some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
        dsimp only [landRhsI103Node71S, landRhsI103Node73S, State.bind]
        rw [lookupName_cons_ne (n := "%40") _ _ (by decide),
          lookupName_cons_ne (n := "%40") _ _ (by decide)]
        exact landRhsI103OutAt_byte s e b
      rw [hs3'] at hl3
      rw [if_neg h32] at hl3
      obtain ⟨s4, hl4, hs4⟩ :=
        WalkLink.leafBlock69_at (calls := calls) (G := G) (C := { C with block := "LeafBlock69" })
          (s := landRhsI103Node71S s e G.b b) hl3.inv' rfl h40₃ hf69
      have hs4' : s4 = landRhsI103Leaf69S s e G.b b := by rw [hs4]; rfl
      have hseg := (((WalkSegment.of_link hl1).trans (WalkSegment.of_link hl2)).trans
        (WalkSegment.of_link hl3)).trans (WalkSegment.of_link hl4)
      rw [hs4'] at hseg
      refine ⟨4, s4, by omega, ?_⟩
      rw [hs4']
      simpa only [if_neg h13, if_neg h32] using hseg


/-! ### The stop visit's named states

`while.end.i`'s landing `phi` and the equality test, then (on the test's false arm) the
entry-byte test at `if.end.i97`, the jump at `if.else.i`, and the escape tree's three
pivots down the class's own route: `NodeBlock83` (false), `NodeBlock81` (false),
`LeafBlock79` (false), `if.else43.i`.  These are the states the stop visit's segment
threads, so each link's successor is a name. -/

/-- The state `while.end.i` leaves: the landing `phi` and its exit test. -/
def slowStopS (s : State) (e c : BitVec 64) : State :=
  { stateAt (cells [("%cmp6.i", .int 1 (evalICmp .eq e c)),
      ("%ee.0.lcssa.i", .int 64 e)] s.env) s with
    pc := (if evalICmp .eq e c = 1 then "cleanup474.i" else "if.end.i97")
    pre := some s.pc }

/-- The state `if.end.i97` leaves on the tag test's false arm: `%41` is the entry's byte,
and the walk leaves for `if.else.i`. -/
def slowIfEndS (s : State) (b : UInt8) : State :=
  { stateAt (cells
      [("%or.cond127.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
          evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
       ("%or.cond.i98", .int 1 (evalICmp .ult
          (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
       ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)),
       ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))),
       ("%41", .int 8 (BitVec.ofNat 8 b.toNat))] s.env) s with
    pc := "if.else.i"
    pre := some s.pc }

/-- The state `if.else.i` leaves: no instructions, the edge to `NodeBlock83`. -/
def slowElseS (s : State) : State :=
  { s with pc := "NodeBlock83", pre := some s.pc }

/-- The state `NodeBlock83` leaves on its false arm (`%41` is not below `110`). -/
def slowP83S (s : State) (x : BitVec 8) : State :=
  { s.bind "%Pivot84" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 110))) with
    pc := "NodeBlock81", pre := some s.pc }

/-- The state `NodeBlock81` leaves on its false arm (`%41` is not below `116`). -/
def slowP81S (s : State) (x : BitVec 8) : State :=
  { s.bind "%Pivot82" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 116))) with
    pc := "LeafBlock79", pre := some s.pc }

/-- The state `LeafBlock79` leaves on its false arm (`%41` is not `116`). -/
def slowL79S (s : State) (x : BitVec 8) : State :=
  { s.bind "%SwitchLeaf80" (.int 1 (evalICmp .eq x (BitVec.ofNat 8 116))) with
    pc := "if.else43.i", pre := some s.pc }

/-- **`while.end.i`'s target, named**: the landing `phi`, the exit test and the edge. -/
theorem WalkLink.while_end_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.end.i")
    {p : String} {op : Operand} {e c : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("cond.end.i96", (Operand.reg "%idxprom.i")),
      ("LeafBlock64", (Operand.reg "%ee.011.i")),
      ("LeafBlock67", (Operand.reg "%ee.011.i")),
      ("LeafBlock69", (Operand.reg "%ee.011.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 c)) :
    ∃ s', WalkLink calls G C s
        { C with block := (if evalICmp .eq e c = 1 then "cleanup474.i" else "if.end.i97") } s' ∧
      s' = slowStopS s e c := by
  obtain ⟨s', hl⟩ := WalkLink.while_end_i G C s hInv hblock hpre hin hv hcond
  refine ⟨s', hl, ?_⟩
  have hden : denoteCode calls walkWhile_end_i.instrs s =
      some (stateAt (("%cmp6.i", .int 1 (evalICmp .eq e c)) ::
        ("%ee.0.lcssa.i", .int 64 e) :: s.env) s) := by
    have hspecs : walkWhile_end_i.instrs =
        ([{ dst := "%ee.0.lcssa.i", ty := Ty.int 64,
            incoming := [("cond.end.i96", (Operand.reg "%idxprom.i")),
              ("LeafBlock64", (Operand.reg "%ee.011.i")),
              ("LeafBlock67", (Operand.reg "%ee.011.i")),
              ("LeafBlock69", (Operand.reg "%ee.011.i"))] }].map PhiSpec.instr) ++
          [Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%cond.i")] := by
      simp [walkWhile_end_i, PhiSpec.instr]
    rw [hspecs, denoteCode_phiRun
      (specs :=
        [{ dst := "%ee.0.lcssa.i", ty := Ty.int 64,
            incoming := [("cond.end.i96", (Operand.reg "%idxprom.i")),
          ("LeafBlock64", (Operand.reg "%ee.011.i")),
          ("LeafBlock67", (Operand.reg "%ee.011.i")),
          ("LeafBlock69", (Operand.reg "%ee.011.i"))] }])
      (vs := [("%ee.0.lcssa.i", .int 64 e)])
      (rest := [Instr.icmp "%cmp6.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i")
        (Operand.reg "%cond.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%ee.0.lcssa.i", .int 64 e)] =
      stateAt (("%ee.0.lcssa.i", .int 64 e) :: s.env) s from rfl]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%ee.0.lcssa.i", .int 64 e) :: s.env) (s := s)
      (d := "%cmp6.i") (a := "%ee.0.lcssa.i") (b := "%cond.i") IPred.eq 64
      (x := e) (y := c) (by exact walkLookup_cons_self "%ee.0.lcssa.i" (.int 64 e) s.env)
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hcond)]
    rfl
  have hstep : LeanLLVM.step calls stage2Body s =
      Ctrl.jump (slowStopS s e c) := by
    have hpc : s.pc = C.block := hInv.pc_eq
    have hfind : stage2Body.findBlock s.pc = some walkWhile_end_i := by
      rw [hpc, hblock]; exact walkWhile_end_i_find
    have hterm : walkWhile_end_i.term =
        Term.condbr (Operand.reg "%cmp6.i") "cleanup474.i" "if.end.i97" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%cmp6.i") (tl := "cleanup474.i") (fl := "if.end.i97")
      (bit := evalICmp .eq e c) (by simp only [stateAt, cells]; exact lookupName_cons_self _ _ _)]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.end.i97`'s target, named**: the entry byte's load, the tag test and the edge.
The load reads `%arrayidx10.i`'s byte `b`, and the tag test's two bits are `b`'s. -/
theorem WalkLink.if_end_i97_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end.i97")
    {a : Nat} {b : UInt8}
    (hd : lookupName s.env "%arrayidx10.i" = some (.ptr a))
    (hread : readBytes s.mem a 1 = some [b]) :
    ∃ s', WalkLink calls G C s
        { C with block := (if (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
          evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
          then "if.then19.i" else "if.else.i") } s' ∧
      s' = { slowIfEndS s b with
        pc := (if (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
          evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 1
          then "if.then19.i" else "if.else.i") } := by
  obtain ⟨s', hl⟩ := WalkLink.if_end_i97 G C s hInv hblock hd hread
  refine ⟨s', hl, ?_⟩
  have hden : denoteCode calls walkIf_end_i97.instrs s =
      some (stateAt (cells
        [("%or.cond127.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
            evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
         ("%or.cond.i98", .int 1 (evalICmp .ult
            (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))),
         ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)),
         ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))),
         ("%41", .int 8 (BitVec.ofNat 8 b.toNat))] s.env) s) := by
    simp only [walkIf_end_i97]
    conv_lhs => rw [← stateAt_self s]
    rw [denoteCode_load8_single (calls := calls) (env := s.env) (s := s)
      (d := "%41") (p := "%arrayidx10.i") (a := a) hd hread]
    rw [denoteCode_icmp_eq_imm_w (calls := calls)
      (env := ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%cmp11.i") (a := "%41") 8 (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 45) (by simp [lookupName])]
    rw [walkDenoteCode_add_imm_w (calls := calls)
      (env := ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%42") (a := "%41") (w := 8) (x := BitVec.ofNat 8 b.toNat)
      (c := BitVec.ofNat 8 208)
      (by
        rw [lookupName_cons_ne _ _ (by decide)]
        simp [lookupName])]
    rw [denoteCode_icmp_imm (calls := calls)
      (env := ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)) ::
        ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%or.cond.i98") (a := "%42") IPred.ult 8
      (x := BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (c := BitVec.ofNat 8 10)
      (by simp [lookupName])]
    rw [denoteCode_or_reg_w (calls := calls)
      (env := ("%or.cond.i98", .int 1 (evalICmp .ult
          (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))) ::
        ("%42", .int 8 (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)) ::
        ("%cmp11.i", .int 1 (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))) ::
        ("%41", .int 8 (BitVec.ofNat 8 b.toNat)) :: s.env) (s := s)
      (d := "%or.cond127.i") (a := "%cmp11.i") (b := "%or.cond.i98") (w := 1)
      (x := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45))
      (y := evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        simp [lookupName])
      (by simp [lookupName])]
    rfl
  have hbit : evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10) =
      ((evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10)) : BitVec 1) := rfl
  have hstep : LeanLLVM.step calls stage2Body s =
      Ctrl.jump ({ slowIfEndS s b with
        pc := (if (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
          evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)
            (BitVec.ofNat 8 10)) = 1 then "if.then19.i" else "if.else.i") } : State) := by
    have hpc : s.pc = C.block := hInv.pc_eq
    have hfind : stage2Body.findBlock s.pc = some walkIf_end_i97 := by
      rw [hpc, hblock]; exact walkIf_end_i97_find
    have hterm : walkIf_end_i97.term =
        Term.condbr (Operand.reg "%or.cond127.i") "if.then19.i" "if.else.i" := rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%or.cond127.i") (tl := "if.then19.i") (fl := "if.else.i")
      (bit := evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10))
      (by simp only [stateAt, cells]; exact lookupName_cons_self _ _ _)]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.else.i`'s target, named**: no instructions and the edge to `NodeBlock83`. -/
theorem WalkLink.if_else_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.else.i") :
    ∃ s', WalkLink calls G C s { C with block := "NodeBlock83" } s' ∧
      s' = slowElseS s := by
  obtain ⟨s', hl⟩ := WalkLink.if_else_i G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hpc : s.pc = C.block := hInv.pc_eq
  have hfind : stage2Body.findBlock s.pc = some walkIf_else_i := by
    rw [hpc, hblock]; exact walkIf_else_i_find
  have hterm : walkIf_else_i.term = Term.br "NodeBlock83" := rfl
  have hstep : LeanLLVM.step calls stage2Body s = Ctrl.jump (slowElseS s) := by
    simp only [LeanLLVM.step, hfind, hterm, execTerm, slowElseS]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)


/-- **`cleanup474.i`'s target, named**: the release is a `lifetime.end` and a branch, so
its target is the source's memory at the copy's block. -/
theorem cleanup474_i_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cleanup474.i")
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s { C with block := "if.then" } s' ∧
      s' = { stateAt s.env s with pc := "if.then", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.cleanup474_i G C s hInv hblock htok
  refine ⟨s', hl, ?_⟩
  have hpc : s.pc = C.block := hInv.pc_eq
  have hden : denoteCode (stage2Calls stage2SubCalls)
      [Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
         (Ty.ptr, Operand.reg "%t352.i")]] s = some (stateAt s.env s) := by
    change denoteCode (stage2Calls stage2SubCalls)
      [Instr.callVoid "llvm.lifetime.end.p0"
        [(Ty.int 64, Operand.imm (.int 64 (BitVec.ofNat 64 24))),
         (Ty.ptr, Operand.reg "%t352.i")]] (stateAt s.env s) = some (stateAt s.env s)
    rw [walkDenoteCode_lifetimeEnd (sub := stage2SubCalls) (env := s.env) (s := s)
      (size := 24) (obj := "%t352.i") htok ([] : List Instr)]
    rfl
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s =
      Ctrl.jump { stateAt s.env s with pc := "if.then", pre := some s.pc } := by
    simp only [LeanLLVM.step, hpc, hblock, walkCleanup474_find, hden, walkCleanup474,
      execTerm]
    have hpc' : (stateAt s.env s).pc = "cleanup474.i" := by
      show s.pc = "cleanup474.i"
      rw [hpc, hblock]
    rw [hpc']
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)


/-- The state `if.else43.i` leaves: the `%e + 8` store of the entry's index. -/
def slowStoreS (s : State) (e j : Nat) : State :=
  { { s with
      env := ("%off1.i129.i", .ptr (e + 8)) :: s.env
      mem := writeBytes s.mem (e + 8) (wordBytes 8 j) } with
    pc := "cleanup474.i", pre := some s.pc }

/-- **The stop visit, composed**: `while.end.i`'s landing and exit test, then the bound
exit to `cleanup474.i` or the escape tree's own route (`if.end.i97` with the tag bit clear,
`if.else.i`, `NodeBlock83` and `NodeBlock81` both below, `LeafBlock79` not `116`) to
`if.else43.i`'s refusal store and `cleanup474.i`.  Either arm ends at the copy, and the
count is at most nine: one step for `while.end.i` and, on the tree, seven more with the
release. -/
theorem slowVisit_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (hInv : WalkInv G C s) (hblock : C.block = "while.end.i")
    {p : String} {op : Operand} {e c : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("cond.end.i96", (Operand.reg "%idxprom.i")),
      ("LeafBlock64", (Operand.reg "%ee.011.i")),
      ("LeafBlock67", (Operand.reg "%ee.011.i")),
      ("LeafBlock69", (Operand.reg "%ee.011.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 c))
    {a : Nat} {b : UInt8}
    (hd : lookupName s.env "%arrayidx10.i" = some (.ptr a))
    (hread : readBytes s.mem a 1 = some [b])
    (hbit : (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 116) = 0)
    {j : Nat} (hidx : evalOperand s (.reg "%idxprom.i") = some (.int 64 (BitVec.ofNat 64 j)))
    (hj : j ≤ G.n) (hj64 : j < 2 ^ 64)
    (he : lookupName s.env "%e" = some (.ptr C.stage.e))
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (heoff : C.eoff ≤ G.n)
    {k : Nat} (hword : readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)) (hk : k ≤ G.n) :
    ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n ∧
      Cd.block = "if.then" ∧ n ≤ 9 ∧
      (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
      Cd.eoff ≤ G.n := by
  obtain ⟨s0, hl0, hs0⟩ := WalkLink.while_end_i_at (calls := stage2Calls stage2SubCalls)
    (G := G) (C := C) (s := s) hInv hblock hpre hin hv hcond
  rw [hs0] at hl0
  -- the stop state's surviving cells
  have hd0 : lookupName (slowStopS s e c).env "%arrayidx10.i" = some (.ptr a) := by
    dsimp only [slowStopS, stateAt, cells]
    rw [lookupName_cons_ne (n := "%arrayidx10.i") _ _ (by decide),
      lookupName_cons_ne (n := "%arrayidx10.i") _ _ (by decide)]
    exact hd
  have hread0 : readBytes (slowStopS s e c).mem a 1 = some [b] := by
    show readBytes s.mem a 1 = some [b]
    exact hread
  have htok0 : lookupName (slowStopS s e c).env "%t352.i" = some (.ptr C.stage.tok) := by
    dsimp only [slowStopS, stateAt, cells]
    rw [lookupName_cons_ne (n := "%t352.i") _ _ (by decide),
      lookupName_cons_ne (n := "%t352.i") _ _ (by decide)]
    exact htok
  have hword0 : readBytes (slowStopS s e c).mem (C.stage.e + 8) 8 = some (wordBytes 8 k) := by
    show readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)
    exact hword
  by_cases hcmp : evalICmp .eq e c = 1
  · -- the bound exit: `cleanup474.i` and the copy
    rw [if_pos hcmp] at hl0
    obtain ⟨s1, hl1, hs1⟩ := cleanup474_i_at (G := G) (C := { C with block := "cleanup474.i" })
      (s := slowStopS s e c) hl0.inv' rfl htok0
    have hseg := (WalkSegment.of_link hl0).trans (WalkSegment.of_link hl1)
    have hword1 : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k) := by
      rw [hs1]
      show readBytes (slowStopS s e c).mem (C.stage.e + 8) 8 = some (wordBytes 8 k)
      exact hword0
    refine ⟨{ C with block := "if.then" }, s1, 2, hseg, rfl, by omega,
      ⟨k, hk, hword1⟩, heoff⟩
  · -- the whitespace stop: the escape tree's own route
    rw [if_neg hcmp] at hl0
    have hbitNe : ¬ ((evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 b.toNat + BitVec.ofNat 8 208)
          (BitVec.ofNat 8 10)) = 1) := by
      rw [hbit]; decide
    obtain ⟨s1, hl1, hs1⟩ := WalkLink.if_end_i97_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "if.end.i97" }) (s := slowStopS s e c)
      hl0.inv' rfl hd0 hread0
    have hs1' : s1 = slowIfEndS (slowStopS s e c) b := by
      rw [hs1]; rw [if_neg hbitNe]; rfl
    rw [hs1'] at hl1
    rw [if_neg hbitNe] at hl1
    -- the tag test's state keeps `%41`
    have h41a : lookupName (slowIfEndS (slowStopS s e c) b).env "%41" =
        some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
      dsimp only [slowIfEndS, stateAt, cells]
      repeat rw [lookupName_cons_ne (n := "%41") _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    obtain ⟨s2, hl2, hs2⟩ := WalkLink.if_else_i_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "if.else.i" }) (s := slowIfEndS (slowStopS s e c) b)
      hl1.inv' rfl
    rw [hs2] at hl2
    have h41b : lookupName (slowElseS (slowIfEndS (slowStopS s e c) b)).env "%41" =
        some (.int 8 (BitVec.ofNat 8 b.toNat)) := h41a
    have h110Ne : ¬ (evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 110) = 1) := by
      rw [h110]; decide
    obtain ⟨s3, hl3, hs3⟩ := WalkLink.NodeBlock83_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "NodeBlock83" })
      (s := slowElseS (slowIfEndS (slowStopS s e c) b)) hl2.inv' rfl
      (evalOperand_reg_of _ (slowElseS (slowIfEndS (slowStopS s e c) b)) _ _ h41b)
    have hs3' : s3 = slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat) := by
      rw [hs3]; rw [if_neg h110Ne]; rfl
    rw [hs3'] at hl3
    rw [if_neg h110Ne] at hl3
    have h41c : lookupName (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)).env "%41" =
        some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
      dsimp only [slowP83S, State.bind]
      rw [lookupName_cons_ne (n := "%41") _ _ (by decide)]
      exact h41b
    have h116Ne : ¬ (evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 116) = 1) := by
      rw [h116]; decide
    obtain ⟨s4, hl4, hs4⟩ := WalkLink.NodeBlock81_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "NodeBlock81" })
      (s := slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) hl3.inv' rfl
      (evalOperand_reg_of _ (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat)) _ _ h41c)
    have hs4' : s4 = slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat) := by
      rw [hs4]; rw [if_neg h116Ne]; rfl
    rw [hs4'] at hl4
    rw [if_neg h116Ne] at hl4
    have h41d : lookupName (slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)).env "%41" =
        some (.int 8 (BitVec.ofNat 8 b.toNat)) := by
      dsimp only [slowP81S, State.bind]
      rw [lookupName_cons_ne (n := "%41") _ _ (by decide)]
      exact h41c
    have h116eqNe : ¬ (evalICmp .eq (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 116) = 1) := by
      rw [h116eq]; decide
    obtain ⟨s5, hl5, hs5⟩ := WalkLink.LeafBlock79_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "LeafBlock79" })
      (s := slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) hl4.inv' rfl
      (evalOperand_reg_of _ (slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) _ _ h41d)
    have hs5' : s5 = slowL79S (slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat) := by
      rw [hs5]; rw [if_neg h116eqNe]; rfl
    rw [hs5'] at hl5
    rw [if_neg h116eqNe] at hl5
    -- the cells the store reads survive the tree's three pivots
    have hidx5 : evalOperand (slowL79S (slowP81S (slowP83S
        (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) (.reg "%idxprom.i") =
        some (.int 64 (BitVec.ofNat 64 j)) := by
      have h : lookupName (slowL79S (slowP81S (slowP83S
          (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
          (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)).env "%idxprom.i" =
          some (.int 64 (BitVec.ofNat 64 j)) := by
        dsimp only [slowL79S, slowP81S, slowP83S, slowElseS, slowIfEndS, slowStopS,
          State.bind, stateAt, cells]
        repeat rw [lookupName_cons_ne (n := "%idxprom.i") _ _ (by decide)]
        exact lookupName_of_evalOperand_reg hidx
      simp only [evalOperand, h]
    have he5 : lookupName (slowL79S (slowP81S (slowP83S
        (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)).env "%e" =
        some (.ptr C.stage.e) := by
      dsimp only [slowL79S, slowP81S, slowP83S, slowElseS, slowIfEndS, slowStopS,
        State.bind, stateAt, cells]
      repeat rw [lookupName_cons_ne (n := "%e") _ _ (by decide)]
      exact he
    obtain ⟨s6, hl6, hs6⟩ := WalkLink.if_else43_i_at (calls := stage2Calls stage2SubCalls)
      (G := G) (C := { C with block := "if.else43.i" })
      (s := slowL79S (slowP81S (slowP83S (slowElseS (slowIfEndS (slowStopS s e c) b))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat))
      hl5.inv' rfl hidx5 he5 hj hj64
    have hs6' : s6 = slowStoreS (slowL79S (slowP81S (slowP83S
        (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) C.stage.e j := by
      rw [hs6]; rfl
    rw [hs6'] at hl6
    -- the release
    have htok6 : lookupName (slowStoreS (slowL79S (slowP81S (slowP83S
        (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) C.stage.e j).env "%t352.i" =
        some (.ptr C.stage.tok) := by
      dsimp only [slowStoreS, slowL79S, slowP81S, slowP83S, slowElseS, slowIfEndS,
        slowStopS, State.bind, stateAt, cells]
      repeat rw [lookupName_cons_ne (n := "%t352.i") _ _ (by decide)]
      exact htok
    obtain ⟨s7, hl7, hs7⟩ := cleanup474_i_at (G := G)
      (C := { { C with block := "if.else43.i", eoff := j, refusal := true } with
        block := "cleanup474.i" })
      (s := slowStoreS (slowL79S (slowP81S (slowP83S
        (slowElseS (slowIfEndS (slowStopS s e c) b)) (BitVec.ofNat 8 b.toNat))
        (BitVec.ofNat 8 b.toNat)) (BitVec.ofNat 8 b.toNat)) C.stage.e j) hl6.inv' rfl htok6
    have hseg := ((((((WalkSegment.of_link hl0).trans (WalkSegment.of_link hl1)).trans
      (WalkSegment.of_link hl2)).trans (WalkSegment.of_link hl3)).trans
      (WalkSegment.of_link hl4)).trans (WalkSegment.of_link hl5)).trans
      ((WalkSegment.of_link hl6).trans (WalkSegment.of_link hl7))
    have hword7 : readBytes s7.mem (C.stage.e + 8) 8 = some (wordBytes 8 j) := by
      rw [hs7]
      dsimp only [slowStoreS, stateAt]
      exact refuseSegment_word_of_store
    refine ⟨{ C with block := "if.then", eoff := j, refusal := true }, s7, 8, ?_, rfl,
      by omega, ⟨j, hj, hword7⟩, hj⟩
    simpa only [Nat.reduceAdd] using hseg

/-! **The composed dispatch is the next step, and it needs named successor states.**  The
first attempt stated the leaves' `WalkLocal` hypotheses at inline `s.bind`/`cells` states
and does not elaborate: `WalkLocal`'s `{m0} {G}` are not inferable from such a term, which
is why the `land.rhs457.i` precedent names every intermediate (`ScanS₉₆`, `Latch462S`,
`landRhs457OutAt`).  The fix is three `def`s (`landRhsI103Leaf64S`, `…67S`, `…69S`) and
the node states, then the four-link chain; the five `_at` lemmas above are the pieces it
composes. -/

#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.nodeBlock73_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.leafBlock64_at

end WalkScope
end LeanLLVM.Refinement
