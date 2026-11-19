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


#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.landRhsI103_at

end WalkScope
end LeanLLVM.Refinement
