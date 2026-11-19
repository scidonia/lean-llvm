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
import LeanLLVM.Refinement.JsonStage2WalkDispatchSlowScan

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

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
