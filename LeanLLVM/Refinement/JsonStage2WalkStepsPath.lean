/-
The head path's step instances.

`JsonStage2WalkSteps` names classes A and C.  The head path to the first latch also
crosses H1 (`LeafBlock33`, `LeafBlock43`), B (`land.rhs.i.preheader`) and E
(`land.rhs.i`, `while.body370.i`), whose shapes are `JsonStage2WalkAssembly`'s, so
their instances are the proven pattern: the block's link lemma gives
`∃ s', WalkLink … s'`, the shape gives the same `step` with the successor named, and
`Ctrl.jump`'s injectivity identifies the two.

Each instance states the target as the shape states it, so a chain's `def` for the
state is the instance's term and its state equality applies by `rfl`.

Two facts about the invariant and the registers that every later instance meets:
`WalkInv.ptrs` is a nested conjunction rather than a record, so `%3`'s clause is its
`.1` (the walk's pointer list starts at the arena's base register); and
`e.signExtend 64 = e` for a `BitVec 64` is `BitVec.signExtend_eq` with
`BitVec.setWidth_eq`, so a `phi`-selected 64-bit cell *is* the register's word and a
`gep` offset needs no normalisation.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkPhi
import LeanLLVM.Refinement.JsonStage2WalkSteps

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **`LeafBlock33`'s target, named.**  `%.off = %35 + 247`, `ule %.off, 1`. -/
theorem WalkLink.LeafBlock33_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock33")
    {x : BitVec 8} (h35 : lookupName s.env "%35" = some (.int 8 x)) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1) = 1 then "land.rhs.i.preheader" else "if.end372.i") } s' ∧
      s' = { stateAt (cells
          [("%SwitchLeaf34", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1))),
           ("%.off", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "land.rhs.i.preheader" else "if.end372.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock33 G C s hInv hblock h35
  refine ⟨s', hlink, ?_⟩
  have hstep := walkAddIcmpBrStep (calls := calls) (s := s) (b := walkLeafBlock33)
    (reg := "%35") (off := "%.off") (d := "%SwitchLeaf34")
    (c := BitVec.ofNat 8 247) (one := BitVec.ofNat 8 1)
    (tl := "land.rhs.i.preheader") (fl := "if.end372.i") (x := x)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock33_find) rfl rfl h35
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`LeafBlock43`'s target, named.**  The whitespace skip's own leaf, on `%36`. -/
theorem WalkLink.LeafBlock43_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "LeafBlock43")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hs : WalkLocal { C with block := "while.body370.i" }
      { stateAt (cells [("%SwitchLeaf45", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
          (BitVec.ofNat 8 1))), ("%.off44", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := "while.body370.i", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s
        { C with block := (if evalICmp .ule (x + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1) = 1 then "if.end372.i" else "while.body370.i") } s' ∧
      s' = { stateAt (cells
          [("%SwitchLeaf45", .int 1 (evalICmp .ule (x + BitVec.ofNat 8 247)
            (BitVec.ofNat 8 1))),
           ("%.off44", .int 8 (x + BitVec.ofNat 8 247))] s.env) s with
        pc := (if evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
          then "if.end372.i" else "while.body370.i")
        pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.LeafBlock43 G C s hInv hblock h36 hs
  refine ⟨s', hlink, ?_⟩
  have hstep := walkAddIcmpBrStep (calls := calls) (s := s) (b := walkLeafBlock43)
    (reg := "%36") (off := "%.off44") (d := "%SwitchLeaf45")
    (c := BitVec.ofNat 8 247) (one := BitVec.ofNat 8 1)
    (tl := "if.end372.i") (fl := "while.body370.i") (x := x)
    (by rw [hInv.pc_eq, hblock]; exact walkLeafBlock43_find) rfl rfl h36
    (walkBitVec1_zero_or_one _)
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`land.rhs.i.preheader`'s target, named.**  Class B: no instructions, `br`. -/
theorem WalkLink.land_rhs_i_preheader_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i.preheader")
    (hloc : WalkLocal { C with block := "land.rhs.i" }
      { s with pc := "land.rhs.i", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "land.rhs.i" } s' ∧
      s' = { s with pc := "land.rhs.i", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.land_rhs_i_preheader G C s hInv hblock hloc
  refine ⟨s', hlink, ?_⟩
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkLand_rhs_i_preheader)
    (dest := "land.rhs.i")
    (by rw [hInv.pc_eq, hblock]; exact walkLand_rhs_i_preheader_find) rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`land.lhs.true357.i`'s target, named.**  Off `walkGepLoadBrStep`: the instance is
the block's syntax, the two lookups, the offset's width and the byte's read — no
`denoteCode` of its own, which is what the shape being symbolic buys. -/
theorem WalkLink.land_lhs_true357_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.lhs.true357.i")
    {ig q : Nat} {b : UInt8}
    (hig : lookupName s.env "%invariant.gep" = some (.ptr ig))
    (hcond : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 q)))
    (hq63 : q < 2 ^ 63) (hread : readBytes s.mem (ig + q) 1 = some [b]) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock41" } s' ∧
      s' = { stateAt (cells [("%35", .int 8 (BitVec.ofNat 8 b.toNat)),
          ("%gep", .ptr (ig + q))] s.env) s with
        pc := "NodeBlock41", pre := some s.pc } := by
  obtain ⟨s', hlink⟩ := WalkLink.land_lhs_true357_i G C s hInv hblock hig hcond hq63 hread
  refine ⟨s', hlink, ?_⟩
  have hstep := walkGepLoadBrStep (calls := calls) (s := s) (B := walkLand_lhs_true357_i)
    (ap := "%gep") (ld := "%35") (base := "%invariant.gep") (off := "%cond350.i")
    (dest := "NodeBlock41") (a := ig) (j := q) (b := b)
    (by rw [hInv.pc_eq, hblock]; exact walkLand_lhs_true357_i_find) rfl rfl
    hig hcond hq63 hread
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`land.rhs.i`'s target, named.**  The scan's counter `phi`, the address it indexes
and the byte it loads.  Off `walkPhiGepLoadBrStep`: `PhiSelects` from the link's own
incoming pair and value, `%3`'s pointer peeled past the selected cell, and the
offset's width — the shape carries everything else. -/
theorem WalkLink.land_rhs_i_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i")
    {p : String} {op : Operand} {e : BitVec 64} {b : UInt8}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1 = some [b]) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock52" } s' ∧
      s' = { stateAt (cells [("%36", .int 8 (BitVec.ofNat 8 b.toNat)),
          ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
          (s.bindAll [("%ee.0.i238", .int 64 e)]).env)
          (s.bindAll [("%ee.0.i238", .int 64 e)]) with
        pc := "NodeBlock52"
        pre := some (s.bindAll [("%ee.0.i238", .int 64 e)]).pc } := by
  obtain ⟨s', hlink⟩ :=
    WalkLink.land_rhs_i G C s hInv hblock hpre hin hv hpos hread
  refine ⟨s', hlink, ?_⟩
  -- the selected environment's two lookups
  have hbase : lookupName (s.bind "%ee.0.i238" (.int 64 e)).env "%3"
      = some (.ptr G.b) := by
    simp only [State.bind, lookupName_cons_ne (k := "%ee.0.i238") (n := "%3") _ _
      (by decide)]
    exact hInv.ptrs.1
  have hoff : lookupName (s.bind "%ee.0.i238" (.int 64 e)).env "%ee.0.i238"
      = some (.int 64 (BitVec.ofNat 64 (e.signExtend 64).toNat)) := by
    simp only [State.bind, lookupName_cons_self, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, BitVec.signExtend_eq]
  let specs : List PhiSpec :=
    [{ dst := "%ee.0.i238", ty := Ty.int 64,
       incoming := [("while.body370.i", (Operand.reg "%inc371.i")),
         ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] }]
  let vs : List (String × Value) := [("%ee.0.i238", .int 64 e)]
  have hsel : PhiSelects s p specs vs := PhiSelects.cons hin hv PhiSelects.nil
  have hstep := walkPhiGepLoadBrStep (calls := calls) (s := s) (B := walkLand_rhs_i)
    (specs := specs) (vs := vs) (p := p)
    (ap := "%arrayidx367.i") (ld := "%36") (base := "%3") (off := "%ee.0.i238")
    (dest := "NodeBlock52") (a := G.b) (j := (e.signExtend 64).toNat) (b := b)
    (by rw [hInv.pc_eq, hblock]; exact walkLand_rhs_i_find) rfl rfl hpre
    hsel hbase hoff hpos hread
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- **`cond.end349.i`'s target, named.**  Off `walkCondEnd349Step`: the block's own
`denote` and the terminator's two arms come from the step, so the instance is the class's
hypotheses and the carries — nothing of the block's run. -/
theorem WalkLink.cond_end349_i_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "cond.end349.i")
    {c ix : BitVec 64} {reg p : String}
    (hpre : s.pre = some p)
    (hinc : phiIncoming p [("cond.true345.i", Operand.reg "%conv347.i"),
      ("sw.default.i", Operand.reg "%4")] = some (.reg reg))
    (hav : lookupName s.env reg = some (.int 64 c))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 ix))
    (htok : lookupName s.env "%t352.i" = some (.ptr C.stage.tok))
    (hgap : lookupName s.env "%gap.i" = some (.ptr (C.stage.tok + 20))) :
    ∃ (s' : State), WalkLink (stage2Calls stage2SubCalls) G C s
        { C with block := (if evalICmp .ugt c ix = 1
            then "land.lhs.true357.i" else "if.end372.i") } s' ∧
      s' = condEnd349OutAt s c ix C.stage.tok (C.stage.tok + 20) := by
  obtain ⟨s', hlink⟩ :=
    WalkLink.cond_end349_i G C s hInv hblock hpre hinc hav hidx htok hgap
  refine ⟨s', hlink, ?_⟩
  have hstep := walkCondEnd349Step (sub := stage2SubCalls) s
    (by rw [hInv.pc_eq, hblock]) hpre hinc hav htok hidx hgap
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)

/-- The state `land.rhs457.i` leaves: the counter's selection, the byte's address and
the byte, at the dispatch's entry `NodeBlock105`. -/
def landRhs457OutAt (s : State) (idx : BitVec 64) (a q : Nat) : State :=
  { stateAt (cells
      [("%47", .int 8 (BitVec.ofNat 8 q)),
       ("%arrayidx458.i", .ptr (a + (idx.signExtend 64).toNat)),
       ("%q.0.i246", .int 64 idx)] s.env) s with
    pc := "NodeBlock105", pre := some s.pc }

/-- **`land.rhs457.i`'s target, named.**  The scan's landing runs its `phi`, the byte's
address and the load, then takes the one edge to the dispatch's entry. -/
theorem WalkLink.landRhs457_at {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs457.i")
    {idx : BitVec 64} {a q : Nat} {bs : List UInt8}
    (hpre : s.pre = some "if.then447.i")
    (hinc : phiIncoming "if.then447.i"
      [("while.body462.i", (Operand.reg "%inc463.i")),
       ("if.then447.i", (Operand.reg "%ee.1.i"))] = some (Operand.reg "%ee.1.i"))
    (hop : evalOperand (stateAt s.env s) (.reg "%ee.1.i") = some (.int 64 idx))
    (h3 : lookupName s.env "%3" = some (.ptr a))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63)
    (hread : readBytes s.mem (a + (idx.signExtend 64).toNat) 1 = some bs)
    (hbs : bytesToNat bs = q)
    (hloc : WalkLocal { C with block := "NodeBlock105" }
      { landRhs457OutAt s idx a q with pc := "NodeBlock105", pre := some s.pc }) :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock105" } s' ∧
      s' = landRhs457OutAt s idx a q := by
  obtain ⟨s', hlink⟩ := WalkLink.pureJumpCore (G := G) (C := C) (s := s) hInv
    (B := walkLandRhs457) (by rw [hblock]; exact walkLandRhs457_find)
    (walkLandRhs457Step (calls := calls) (s := s) (idx := idx) (a := a) (q := q) (bs := bs)
      hpre hinc hop h3 hpos hread hbs)
    (by unfold walkCarried; decide) rfl rfl rfl hloc
  refine ⟨s', hlink, ?_⟩
  have hstep := walkLandRhs457Jump (calls := calls) (s := s) (idx := idx) (a := a) (q := q)
    (bs := bs) (by rw [hInv.pc_eq, hblock]) hpre hinc hop h3 hpos hread hbs
  exact Ctrl.jump.inj ((WalkLink.step hlink).symm.trans hstep)
