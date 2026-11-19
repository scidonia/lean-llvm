/-
# The slow scan's round

`walkScanLinksI103` composes one visit: the landing's `phi` and byte load, the two
dispatch pivots and the class leaf, ending at `while.body.i104` (continue) or
`while.end.i` (stop).  This module iterates it over `[entryPos G C.k, G.n)`: the
continue arm takes `while_body_i104`'s back edge, the stop arm takes
`slowVisit_at` (the escape tree's refusal store and `cleanup474.i`), and the bound
arm takes the latch's exit and `cleanup474.i`.  Both exits end at the copy, so the
round's statement is one segment to `if.then`, priced `5·(c − p) + 10`: five links a
visited byte (four for the visit on the range leaf, one for the latch) and ten for
the exit.

The classification is the byte's own: `%40`'s five pivots are `wsStop`'s, so the
scan stops exactly at the four whitespace bytes and continues everywhere else.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchSlowVisits

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- The counter operand `land.rhs.i103`'s `phi` selects from its predecessor: the
latch's increment on the back edge, the entry's index on the entry edge. -/
def slowOp (pre : Option String) : Operand :=
  if pre = some "while.body.i104" then .reg "%inc.i105" else .reg "%idxprom.i"

/-- The landing `phi` at the two predecessors the scan reaches. -/
theorem slowOp_in {p : String} (hp : p = "while.body.i104" ∨ p = "cond.end.i96") :
    phiIncoming p [("while.body.i104", (Operand.reg "%inc.i105")),
      ("cond.end.i96", (Operand.reg "%idxprom.i"))] = some (slowOp (some p)) := by
  rcases hp with rfl | rfl <;> decide

/-- The leaf state's counter cell: `%ee.011.i` is the landing's `phi` value. -/
theorem slowLeaf64_ee (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) :
    lookupName (landRhsI103Leaf64S s e a b).env "%ee.011.i" = some (.int 64 e) := by
  dsimp only [landRhsI103Leaf64S, landRhsI103Node73S, landRhsI103OutAt, stateAt,
    cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%ee.011.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The leaf state keeps the bound cell. -/
theorem slowLeaf64_cond {s : State} {e : BitVec 64} {a : Nat} {b : UInt8} {c : BitVec 64}
    (hc : lookupName s.env "%cond.i" = some (.int 64 c)) :
    lookupName (landRhsI103Leaf64S s e a b).env "%cond.i" = some (.int 64 c) := by
  dsimp only [landRhsI103Leaf64S, landRhsI103Node73S, landRhsI103OutAt, stateAt,
    cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%cond.i") _ _ (by decide)]
  exact hc

/-- **`land.rhs.i103`'s continuation fact at the range leaf.** -/
theorem slowLeafLocal64 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    {p c : Nat} (hc : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hpc : p < c) (hcw : c < 2 ^ 64) (hinner : c - p ≤ C.inner)
    {a : Nat} {b : UInt8} :
    WalkLocal { C with block := "while.body.i104" }
      (landRhsI103Leaf64S s (BitVec.ofNat 64 p) a b) := by
  rw [WalkLocal.stringScan rfl]
  refine ⟨p, c, hinner, hpc, hcw, ?_, slowLeaf64_cond hc⟩
  rw [slowLeaf64_ee]

/-- The second leaf state's counter cell. -/
theorem slowLeaf67_ee (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) :
    lookupName (landRhsI103Leaf67S s e a b).env "%ee.011.i" = some (.int 64 e) := by
  dsimp only [landRhsI103Leaf67S, landRhsI103Node71S, landRhsI103Node73S,
    landRhsI103OutAt, stateAt, cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%ee.011.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The second leaf state keeps the bound cell. -/
theorem slowLeaf67_cond {s : State} {e : BitVec 64} {a : Nat} {b : UInt8} {c : BitVec 64}
    (hc : lookupName s.env "%cond.i" = some (.int 64 c)) :
    lookupName (landRhsI103Leaf67S s e a b).env "%cond.i" = some (.int 64 c) := by
  dsimp only [landRhsI103Leaf67S, landRhsI103Node71S, landRhsI103Node73S,
    landRhsI103OutAt, stateAt, cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%cond.i") _ _ (by decide)]
  exact hc

/-- **`land.rhs.i103`'s continuation fact at the `13` leaf.** -/
theorem slowLeafLocal67 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    {p c : Nat} (hc : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hpc : p < c) (hcw : c < 2 ^ 64) (hinner : c - p ≤ C.inner)
    {a : Nat} {b : UInt8} :
    WalkLocal { C with block := "while.body.i104" }
      (landRhsI103Leaf67S s (BitVec.ofNat 64 p) a b) := by
  rw [WalkLocal.stringScan rfl]
  refine ⟨p, c, hinner, hpc, hcw, ?_, slowLeaf67_cond hc⟩
  rw [slowLeaf67_ee]

/-- The third leaf state's counter cell. -/
theorem slowLeaf69_ee (s : State) (e : BitVec 64) (a : Nat) (b : UInt8) :
    lookupName (landRhsI103Leaf69S s e a b).env "%ee.011.i" = some (.int 64 e) := by
  dsimp only [landRhsI103Leaf69S, landRhsI103Node71S, landRhsI103Node73S,
    landRhsI103OutAt, stateAt, cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%ee.011.i") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The third leaf state keeps the bound cell. -/
theorem slowLeaf69_cond {s : State} {e : BitVec 64} {a : Nat} {b : UInt8} {c : BitVec 64}
    (hc : lookupName s.env "%cond.i" = some (.int 64 c)) :
    lookupName (landRhsI103Leaf69S s e a b).env "%cond.i" = some (.int 64 c) := by
  dsimp only [landRhsI103Leaf69S, landRhsI103Node71S, landRhsI103Node73S,
    landRhsI103OutAt, stateAt, cells, State.bind, State.bindAll]
  repeat rw [lookupName_cons_ne (n := "%cond.i") _ _ (by decide)]
  exact hc

/-- **`land.rhs.i103`'s continuation fact at the `32` leaf.** -/
theorem slowLeafLocal69 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (s : State)
    {p c : Nat} (hc : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hpc : p < c) (hcw : c < 2 ^ 64) (hinner : c - p ≤ C.inner)
    {a : Nat} {b : UInt8} :
    WalkLocal { C with block := "while.body.i104" }
      (landRhsI103Leaf69S s (BitVec.ofNat 64 p) a b) := by
  rw [WalkLocal.stringScan rfl]
  refine ⟨p, c, hinner, hpc, hcw, ?_, slowLeaf69_cond hc⟩
  rw [slowLeaf69_ee]


/-! ### The visit's named endpoint

`walkScanLinksI103` composes the four links but leaves the endpoint existential.  The
round needs the endpoint's cells, so this restates it at the three leaf states the
dispatch can end at. -/

/-- **The visit's endpoint**: the class's own leaf state.  Its `pc` is the visit's
target and its `pre` the leaf's predecessor, so the class ifs are the same ones
`walkScanLinksI103`'s target carries. -/
def slowDispOutS {m0 : Mem} (G : WalkGeom m0) (s : State) (e : BitVec 64) (b : UInt8) : State :=
  if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 13) = 1
  then landRhsI103Leaf64S s e G.b b
  else if evalICmp .slt (BitVec.ofNat 8 b.toNat) (BitVec.ofNat 8 32) = 1
  then landRhsI103Leaf67S s e G.b b
  else landRhsI103Leaf69S s e G.b b

/-- **The visit's endpoint**, named: the same four-link segment, ending at the class
leaf's own state.  The target's block is `walkScanLinksI103`'s, so the two agree. -/
theorem walkScanLinksI103_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
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
              then "while.end.i" else "while.body.i104")) } s' n ∧
      s' = slowDispOutS G s e b := by
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
    refine ⟨3, s3, by omega, ?_, ?_⟩
    · rw [hs3']
      simpa only [if_pos h13] using hseg
    · rw [hs3']
      simp only [slowDispOutS, if_pos h13]
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
      refine ⟨4, s4, by omega, ?_, ?_⟩
      · rw [hs4']
        simpa only [if_neg h13, if_pos h32] using hseg
      · rw [hs4']
        simp only [slowDispOutS, if_neg h13, if_pos h32]
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
      refine ⟨4, s4, by omega, ?_, ?_⟩
      · rw [hs4']
        simpa only [if_neg h13, if_neg h32] using hseg
      · rw [hs4']
        simp only [slowDispOutS, if_neg h13, if_neg h32]

/-- The state the scan's latch leaves. -/
def slowLatchOut (s : State) (p c : Nat) : State :=
  { stateAt (cells
      [("%exitcond.not.i", .int 1 (evalICmp .eq
          (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
       ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s.env) s with
    pc := (if evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c) = 1
      then "cleanup474.i" else "land.rhs.i103")
    pre := some s.pc }

/-- **`while.body.i104`'s target, named**: the increment's cell, the exit test's and the
edge. -/
theorem WalkLink.while_body_i104_at {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i104") {p c : Nat}
    (hinc : lookupName s.env "%ee.011.i" = some (.int 64 (BitVec.ofNat 64 p)))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hl : WalkLocal { C with block := "cleanup474.i" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s with
        pc := "cleanup474.i", pre := some s.pc })
    (hf : WalkLocal { C with block := "land.rhs.i103" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s with
        pc := "land.rhs.i103", pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
          (BitVec.ofNat 64 c) = 1 then "cleanup474.i" else "land.rhs.i103") } s' ∧
      s' = slowLatchOut s p c := by
  obtain ⟨s', hl'⟩ := WalkLink.while_body_i104 (G := G) (C := C) (s := s) hInv hblock
    hinc hcond hl hf
  refine ⟨s', hl', ?_⟩
  have hstep : LeanLLVM.step (stage2Calls stage2SubCalls) stage2Body s = Ctrl.jump (slowLatchOut s p c) := by
    have hfind : stage2Body.findBlock s.pc = some walkWhileBodyI104 := by
      rw [hInv.pc_eq, hblock]; exact walkWhileBodyI104_find
    have hterm : walkWhileBodyI104.term =
        Term.condbr (Operand.reg "%exitcond.not.i") "cleanup474.i" "land.rhs.i103" := rfl
    have hden : denoteCode (stage2Calls stage2SubCalls) walkWhileBodyI104.instrs s =
        some (stateAt (("%exitcond.not.i",
            .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
              (BitVec.ofNat 64 c))) ::
          ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s) := by
      conv_lhs => rw [← stateAt_self s]
      simp only [walkWhileBodyI104]
      rw [denoteCode_cons_of (calls := stage2Calls stage2SubCalls)
        (i := Instr.binop "%inc.i105" BinOp.add 64 (.reg "%ee.011.i")
          (.imm (.int 64 (BitVec.ofNat 64 1))))
        (is := [Instr.icmp "%exitcond.not.i" IPred.eq 64 (.reg "%inc.i105") (.reg "%cond.i")])
        (s := stateAt s.env s)
        (s' := stateAt (("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))
          :: s.env) s)
        (step_add_imm (calls := stage2Calls stage2SubCalls) s.env s "%inc.i105" "%ee.011.i"
          (x := BitVec.ofNat 64 p) (c := BitVec.ofNat 64 1) hinc)]
      rw [walkDenoteCode_icmp (calls := stage2Calls stage2SubCalls)
        (env := ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env)
        (s := s) (d := "%exitcond.not.i") (w := 64) (p := IPred.eq)
        (oa := .reg "%inc.i105") (ob := .reg "%cond.i")
        (x := BitVec.ofNat 64 p + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
        (ha := evalOperand_reg_of _ _ _ _ (lookupName_cons_self _ _ _))
        (hb := evalOperand_reg_of _ _ _ _ ((lookupName_cons_ne _ _ (by decide)).trans hcond))
        (is := [])]
      rfl
    simp only [LeanLLVM.step, hfind, hden, hterm]
    rw [walkExecTerm_condbr (d := "%exitcond.not.i") (tl := "cleanup474.i")
      (fl := "land.rhs.i103")
      (bit := evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))
      (by simp only [stateAt, cells]; exact lookupName_cons_self _ _ _)]
    rfl
  exact Ctrl.jump.inj ((WalkLink.step hl').symm.trans hstep)


/-! ### The latch's cells and the counter's arithmetic -/

/-- The latch's increment word is the successor's `ofNat`. -/
theorem slowOfNat_add_one (p : Nat) :
    (BitVec.ofNat 64 p + BitVec.ofNat 64 1 : BitVec 64) = BitVec.ofNat 64 (p + 1) := by
  rw [BitVec.ofNat_add]

/-- The latch state's increment cell. -/
theorem slowLatchOut_inc (s : State) (p c : Nat) :
    lookupName (slowLatchOut s p c).env "%inc.i105" =
      some (.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) := by
  dsimp only [slowLatchOut, stateAt, cells]
  rw [lookupName_cons_ne (n := "%inc.i105") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The latch state keeps the bound cell. -/
theorem slowLatchOut_cond {s : State} {p c : Nat} {cv : BitVec 64}
    (hc : lookupName s.env "%cond.i" = some (.int 64 cv)) :
    lookupName (slowLatchOut s p c).env "%cond.i" = some (.int 64 cv) := by
  dsimp only [slowLatchOut, stateAt, cells]
  rw [lookupName_cons_ne (n := "%cond.i") _ _ (by decide),
    lookupName_cons_ne (n := "%cond.i") _ _ (by decide)]
  exact hc

/-- The latch preserves the memory. -/
theorem slowLatchOut_mem (s : State) (p c : Nat) : (slowLatchOut s p c).mem = s.mem := rfl

/-- The latch state's predecessor is the latch block, when it is entered from it. -/
theorem slowLatchOut_pre {s : State} (hpc : s.pc = "while.body.i104") (p c : Nat) :
    (slowLatchOut s p c).pre = some "while.body.i104" := by
  dsimp only [slowLatchOut]
  rw [hpc]

/-- The latch's exit bit is false below the bound. -/
theorem slowLatchBit_zero {p c : Nat} (h : p + 1 < c) (hcw : c < 2 ^ 64) :
    evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c) = 0 := by
  have hne : (BitVec.ofNat 64 p + BitVec.ofNat 64 1 : BitVec 64) ≠ BitVec.ofNat 64 c := by
    intro hh
    have ht := congrArg BitVec.toNat hh
    rw [slowOfNat_add_one, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at ht
    omega
  simp [evalICmp, hne]

/-- The latch's exit bit is true at the bound. -/
theorem slowLatchBit_one {p c : Nat} (h : p + 1 = c) (hcw : c < 2 ^ 64) :
    evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c) = 1 := by
  have he : (BitVec.ofNat 64 p + BitVec.ofNat 64 1 : BitVec 64) = BitVec.ofNat 64 c := by
    rw [slowOfNat_add_one, h]
  simp [evalICmp, he]

/-- The scan's context, as one carried argument. -/
structure SlowCtx {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State)
    (pred : String) (p c j k : Nat) : Prop where
  hpred : pred = "while.body.i104" ∨ pred = "cond.end.i96"
  hInv : WalkInv G C s
  hblock : C.block = "land.rhs.i103"
  hpre : s.pre = some pred
  hcnt : evalOperand s (slowOp (some pred)) = some (.int 64 (BitVec.ofNat 64 p))
  hcond : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c))
  hpc : p < c
  hcw : c < 2 ^ 64
  hcG : c ≤ G.n
  hinner : c - p ≤ C.inner
  hj : j = entryPos G C.k
  hqn : j < G.n
  hbit : (evalICmp .eq (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 45) |||
    evalICmp .ult (BitVec.ofNat 8 (G.bs.getD j 0).toNat + BitVec.ofNat 8 208)
      (BitVec.ofNat 8 10)) = 0
  h110 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 110) = 0
  h116 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 116) = 0
  h116eq : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 116) = 0
  halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve
  hevlen : C.evlen ≤ G.evcap
  hword : readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)
  hk : k ≤ G.n
  heoff : C.eoff ≤ G.n

/-- The stop visit's exit: the dispatch's segment to `while.end.i` and `slowVisit_at`'s
segment to the copy, priced inside the round's `5·(c − p) + 10`. -/
theorem slowStopStep {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s s1 : State)
    {n1 p c j k : Nat}
    (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s { C with block := "while.end.i" } s1 n1)
    (hn1 : n1 ≤ 4)
    (hInv1 : WalkInv G { C with block := "while.end.i" } s1)
    {leaf : String} (hpre : s1.pre = some leaf)
    (hin : phiIncoming leaf [("cond.end.i96", (Operand.reg "%idxprom.i")),
      ("LeafBlock64", (Operand.reg "%ee.011.i")),
      ("LeafBlock67", (Operand.reg "%ee.011.i")),
      ("LeafBlock69", (Operand.reg "%ee.011.i"))] = some (.reg "%ee.011.i"))
    (hv : evalOperand s1 (.reg "%ee.011.i") = some (.int 64 (BitVec.ofNat 64 p)))
    (hcond : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hd : lookupName s1.env "%arrayidx10.i" = some (.ptr (G.b + entryPos G C.k)))
    (hread : readBytes s1.mem (G.b + entryPos G C.k) 1 = some [G.bs.getD j 0])
    (hj : j = entryPos G C.k)
    (hbit : (evalICmp .eq (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 45) |||
      evalICmp .ult (BitVec.ofNat 8 (G.bs.getD j 0).toNat + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD j 0).toNat) (BitVec.ofNat 8 116) = 0)
    (hidx : evalOperand s1 (.reg "%idxprom.i")
      = some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))))
    (hqn : entryPos G C.k < G.n)
    (he : lookupName s1.env "%e" = some (.ptr C.stage.e))
    (htok : lookupName s1.env "%t352.i" = some (.ptr C.stage.tok))
    (heoff : C.eoff ≤ G.n)
    (hword : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k))
    (hk : k ≤ G.n) (hcp : 1 ≤ c - p) :
    ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n ∧
      Cd.block = "if.then" ∧ n ≤ 5 * (c - p) + 10 ∧
      (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
      Cd.eoff ≤ G.n := by
  obtain ⟨Cd, sd, nv, hsegv, hblk, hnv, hwordv, heoffv⟩ :=
    slowVisit_at (G := G) (C := { C with block := "while.end.i" }) (s := s1)
      hInv1 rfl hpre hin hv hcond hd hread
      (by simpa only [hj] using hbit) (by simpa only [hj] using h110)
      (by simpa only [hj] using h116) (by simpa only [hj] using h116eq)
      hidx (by omega) (by have h := G.maxDoc; simp only [stage2MaxDocument] at h; omega) he htok (by simpa only [hj] using heoff) hword hk
  exact ⟨Cd, sd, n1 + nv, hseg.trans hsegv, hblk, by omega, hwordv, heoffv⟩



/-- The latch's successor cell: the increment. -/
theorem slowCell_inc (s : State) (p c : Nat) :
    lookupName (cells
      [("%exitcond.not.i", Value.int 1 (evalICmp .eq
          (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
       ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s.env)
      "%inc.i105" = some (Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) := by
  dsimp only [cells]
  rw [lookupName_cons_ne (n := "%inc.i105") _ _ (by decide)]
  exact lookupName_cons_self _ _ _

/-- The latch's successor cell: the bound. -/
theorem slowCell_cond {s : State} {p c : Nat} {cv : BitVec 64}
    (hc : lookupName s.env "%cond.i" = some (.int 64 cv)) :
    lookupName (cells
      [("%exitcond.not.i", Value.int 1 (evalICmp .eq
          (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
       ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s.env)
      "%cond.i" = some (Value.int 64 cv) := by
  dsimp only [cells]
  rw [lookupName_cons_ne (n := "%cond.i") _ _ (by decide),
    lookupName_cons_ne (n := "%cond.i") _ _ (by decide)]
  exact hc

/-- The carry's inner budget is the source's. -/
theorem slowNested_inner {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) :
    ({ { C with block := "while.body.i104" } with block := "land.rhs.i103" } : WalkCarry G).inner
      = C.inner := rfl

/-- The carry's stage is the source's. -/
theorem slowNested_stage {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) (b : String) :
    ({ C with block := b } : WalkCarry G).stage = C.stage := rfl

/-- The continue arm: the latch's link and the round resumed at the landing it
returns to. -/
theorem slowContinueStep {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s s1 : State)
    {n1 p c j k r : Nat}
    (hseg : WalkSegment (stage2Calls stage2SubCalls) G C s
      { C with block := "while.body.i104" } s1 n1)
    (hn1 : n1 ≤ 4)
    (hInv1 : WalkInv G { C with block := "while.body.i104" } s1)
    (hpc1 : s1.pc = "while.body.i104")
    (hinc : lookupName s1.env "%ee.011.i" = some (.int 64 (BitVec.ofNat 64 p)))
    (hcond : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hword1 : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k))
    {pred : String} (ctx : SlowCtx G C s pred p c j k) (hr : c - p = r + 1)
    (ih : ∀ (C' : WalkCarry G) (s' : State) (pred' : String) (p' c' j' k' : Nat),
      c' - p' = r → SlowCtx G C' s' pred' p' c' j' k' →
      ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C' s' Cd sd n ∧
        Cd.block = "if.then" ∧ n ≤ 5 * (c' - p') + 10 ∧
        (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
        Cd.eoff ≤ G.n) :
    ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n ∧
      Cd.block = "if.then" ∧ n ≤ 5 * (c - p) + 10 ∧
      (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
      Cd.eoff ≤ G.n := by
  have hl : WalkLocal { { C with block := "while.body.i104" } with block := "cleanup474.i" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s1.env) s1 with
        pc := "cleanup474.i", pre := some s1.pc } := by
    simp [WalkLocal]
  have hf : WalkLocal { { C with block := "while.body.i104" } with block := "land.rhs.i103" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s1.env) s1 with
        pc := "land.rhs.i103", pre := some s1.pc } := by
    rw [WalkLocal.stringScanLanded rfl]
    by_cases hlt : p + 1 < c
    · refine Or.inl ⟨p + 1, c, ?_, hlt, ctx.hcw, ?_, ?_, ?_⟩
      · rw [slowNested_inner]
        have := ctx.hinner
        omega
      · show (some s1.pc) = some "while.body.i104"
        rw [hpc1]
      · show lookupName (cells
          [("%exitcond.not.i", Value.int 1 (evalICmp .eq
            (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
           ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s1.env)
          "%inc.i105" = some (Value.int 64 (BitVec.ofNat 64 (p + 1)))
        exact (slowCell_inc s1 p c).trans (by rw [slowOfNat_add_one])
      · show lookupName (cells
          [("%exitcond.not.i", Value.int 1 (evalICmp .eq
            (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
           ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s1.env)
          "%cond.i" = some (Value.int 64 (BitVec.ofNat 64 c))
        exact slowCell_cond hcond
    · have heq : p + 1 = c := by omega
      refine Or.inr (Or.inr ⟨c, ctx.hcw, ?_, ?_⟩)
      · show lookupName (cells
          [("%exitcond.not.i", Value.int 1 (evalICmp .eq
            (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
           ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s1.env)
          "%inc.i105" = some (Value.int 64 (BitVec.ofNat 64 c))
        exact (slowCell_inc s1 p c).trans (by rw [slowOfNat_add_one, heq])
      · show lookupName (cells
          [("%exitcond.not.i", Value.int 1 (evalICmp .eq
            (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))),
           ("%inc.i105", Value.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))] s1.env)
          "%cond.i" = some (Value.int 64 (BitVec.ofNat 64 c))
        exact slowCell_cond hcond
  obtain ⟨s2, hl2, hs2⟩ :=
    WalkLink.while_body_i104_at (G := G) (C := { C with block := "while.body.i104" })
      (s := s1) hInv1 rfl hinc hcond hl hf
  by_cases hlt : p + 1 < c
  · have hbit0 : evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 c) = 0 := slowLatchBit_zero hlt ctx.hcw
    rw [hs2] at hl2
    rw [hbit0] at hl2
    rw [if_neg (by decide)] at hl2
    let C' : WalkCarry G :=
      { { C with block := "while.body.i104" } with block := "land.rhs.i103" }
    let s' : State := slowLatchOut s1 p c
    have hinc' : lookupName s'.env "%inc.i105" =
        some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
      dsimp only [s']
      rw [slowLatchOut_inc, slowOfNat_add_one]
    have hcond' : lookupName s'.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
      dsimp only [s']
      exact slowLatchOut_cond hcond
    have hcnt' : evalOperand s' (slowOp (some "while.body.i104"))
        = some (.int 64 (BitVec.ofNat 64 (p + 1))) := by
      rw [show slowOp (some "while.body.i104") = .reg "%inc.i105" from rfl]
      exact evalOperand_reg_of _ s' _ _ hinc'
    have hblock' : C'.block = "land.rhs.i103" := rfl
    have hpre' : s'.pre = some "while.body.i104" := by
      dsimp only [s']; exact slowLatchOut_pre hpc1 p c
    have hword' : readBytes s'.mem (C'.stage.e + 8) 8 = some (wordBytes 8 k) := by
      dsimp only [s']
      rw [slowLatchOut_mem]
      exact hword1
    have hinner' : c - (p + 1) ≤ C'.inner := by
      rw [show C'.inner = C.inner from rfl]
      have := ctx.hinner
      omega
    have ctx' : SlowCtx G C' s' "while.body.i104" (p + 1) c j k :=
      { hpred := Or.inl rfl
        hInv := hl2.inv'
        hblock := hblock'
        hpre := hpre'
        hcnt := hcnt'
        hcond := hcond'
        hpc := hlt
        hcw := ctx.hcw
        hcG := ctx.hcG
        hinner := hinner'
        hj := ctx.hj
        hqn := ctx.hqn
        hbit := ctx.hbit
        h110 := ctx.h110
        h116 := ctx.h116
        h116eq := ctx.h116eq
        halen := ctx.halen
        hevlen := ctx.hevlen
        hword := hword'
        hk := ctx.hk
        heoff := ctx.heoff }
    obtain ⟨Cd, sd, n2, hseg2, hblk2, hn2, hword2, heoff2⟩ :=
      ih C' s' "while.body.i104" (p + 1) c j k (by omega) ctx'
    refine ⟨Cd, sd, n1 + 1 + n2, ?_, hblk2, by omega, hword2, heoff2⟩
    exact (hseg.trans (WalkSegment.of_link hl2)).trans hseg2
  · have heq : p + 1 = c := by omega
    have hbit1 : evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 c) = 1 := slowLatchBit_one heq ctx.hcw
    rw [hbit1] at hl2
    rw [if_pos (show ((1 : BitVec 1) = 1) from rfl)] at hl2
    have htok : lookupName s2.env "%t352.i" = some (.ptr C.stage.tok) := by
      have h := hl2.inv'.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
      simpa only using h
    obtain ⟨s3, hl3, hs3⟩ :=
      cleanup474_i_at (G := G) (C := { { C with block := "while.body.i104" } with
        block := "cleanup474.i" }) (s := s2) hl2.inv' rfl htok
    refine ⟨{ C with block := "if.then" }, s3, n1 + 1 + 1, ?_, rfl, by omega, ?_, ?_⟩
    · exact (hseg.trans (WalkSegment.of_link hl2)).trans (WalkSegment.of_link hl3)
    · refine ⟨k, ctx.hk, ?_⟩
      rw [hs3, hs2]
      dsimp only [slowLatchOut, stateAt]
      exact hword1
    · simpa only using ctx.heoff


/-- **The scan's round.**  One `walkScanLinksI103_at` per visited byte; the continue
arm takes the latch and resumes, the stop arm takes `slowStopStep`, and the bound arm
takes the latch's exit.  `n ≤ 5·(c − p) + 10` throughout. -/
theorem slowRun_go {m0 : Mem} (G : WalkGeom m0) :
    ∀ (r : Nat) (C : WalkCarry G) (s : State) (pred : String) (p c j k : Nat),
      c - p = r → SlowCtx G C s pred p c j k →
      ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
        WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n ∧
        Cd.block = "if.then" ∧ n ≤ 5 * (c - p) + 10 ∧
        (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
        Cd.eoff ≤ G.n := by
  intro r
  induction r with
  | zero =>
      intro C s pred p c j k hr ctx
      have := ctx.hpc
      omega
  | succ r ih =>
      intro C s pred p c j k hr ctx
      have hp63 : p < 2 ^ 63 := by
        have hm := G.maxDoc
        simp only [stage2MaxDocument] at hm
        have h1 := ctx.hpc
        have h2 := ctx.hcG
        omega
      have hpG : p < G.n := by
        have h1 := ctx.hpc
        have h2 := ctx.hcG
        omega
      have he_p : ((BitVec.ofNat 64 p).signExtend 64).toNat = p := by
        rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hpos : ((BitVec.ofNat 64 p).signExtend 64).toNat < 2 ^ 63 := by
        rw [he_p]; exact hp63
      have hread : readBytes s.mem (G.b + ((BitVec.ofNat 64 p).signExtend 64).toNat) 1
          = some [G.bs.getD p 0] := by
        rw [he_p]
        exact walkDoc_byte G C s ctx.hInv ctx.halen ctx.hevlen hpG
      have hf64 := slowLeafLocal64 (G := G) C s (a := G.b) (b := G.bs.getD p 0)
        ctx.hcond ctx.hpc ctx.hcw ctx.hinner
      have hf67 := slowLeafLocal67 (G := G) C s (a := G.b) (b := G.bs.getD p 0)
        ctx.hcond ctx.hpc ctx.hcw ctx.hinner
      have hf69 := slowLeafLocal69 (G := G) C s (a := G.b) (b := G.bs.getD p 0)
        ctx.hcond ctx.hpc ctx.hcw ctx.hinner
      have hin : phiIncoming pred [("while.body.i104", (Operand.reg "%inc.i105")),
          ("cond.end.i96", (Operand.reg "%idxprom.i"))] = some (slowOp (some pred)) :=
        slowOp_in ctx.hpred
      obtain ⟨n1, s1, hn1, hseg1, hs1⟩ :=
        walkScanLinksI103_at (calls := stage2Calls stage2SubCalls) (G := G) (C := C) (s := s)
          ctx.hInv ctx.hblock ctx.hpre hin ctx.hcnt hpos hread hf64 hf67 hf69
      have hd1 : lookupName s1.env "%arrayidx10.i" = some (.ptr (G.b + entryPos G C.k)) :=
        hseg1.inv'.iter.regarr
      have hread1 : readBytes s1.mem (G.b + entryPos G C.k) 1
          = some [G.bs.getD (entryPos G C.k) 0] :=
        walkDoc_byte G _ s1 hseg1.inv' ctx.halen ctx.hevlen (by
          have h := ctx.hqn; have hj := ctx.hj; omega)
      have hidx1 : evalOperand s1 (.reg "%idxprom.i")
          = some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))) :=
        evalOperand_reg_of _ s1 _ _ hseg1.inv'.idx_reg
      have he1 : lookupName s1.env "%e" = some (.ptr C.stage.e) :=
        hseg1.inv'.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs])
      have htok1 : lookupName s1.env "%t352.i" = some (.ptr C.stage.tok) :=
        hseg1.inv'.regs ("%t352.i", .ptr C.stage.tok) (by simp [walkStaticRegs])
      by_cases h13 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
          (BitVec.ofNat 8 13) = 1
      · have hs1a : s1 = landRhsI103Leaf64S s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0) := by
          rw [hs1]; simp only [slowDispOutS, if_pos h13]
        have hpre : s1.pre = some "LeafBlock64" := by
          rw [hs1a]
          dsimp only [landRhsI103Leaf64S, landRhsI103Node73S]
          rw [if_pos h13]
        have hv : evalOperand s1 (.reg "%ee.011.i") = some (.int 64 (BitVec.ofNat 64 p)) :=
          evalOperand_reg_of _ s1 _ _
            (by rw [hs1a]; exact slowLeaf64_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
        have hcond1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
          rw [hs1a]; exact slowLeaf64_cond ctx.hcond
        have hword1 : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k) := by
          rw [hs1a]; exact ctx.hword
        by_cases hws : evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
            + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
        · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
              (BitVec.ofNat 8 13) = 1
              then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                then "while.end.i" else "while.body.i104")
              else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 32) = 1
              then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
              else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
              = "while.end.i" := by rw [if_pos h13, if_pos hws]
          rw [hblk] at hseg1
          exact slowStopStep (G := G) (C := C) (s := s) (s1 := s1) (leaf := "LeafBlock64")
            hseg1 hn1 hseg1.inv' hpre (by decide) hv hcond1 hd1 hread1 rfl
            (by simpa only [ctx.hj] using ctx.hbit) (by simpa only [ctx.hj] using ctx.h110)
            (by simpa only [ctx.hj] using ctx.h116) (by simpa only [ctx.hj] using ctx.h116eq)
            hidx1 (by simpa only [ctx.hj] using ctx.hqn) he1 htok1 ctx.heoff hword1 ctx.hk
            (by omega)
        · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
              (BitVec.ofNat 8 13) = 1
              then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                then "while.end.i" else "while.body.i104")
              else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 32) = 1
              then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
              else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
              = "while.body.i104" := by rw [if_pos h13, if_neg hws]
          rw [hblk] at hseg1
          have hpc1 : s1.pc = "while.body.i104" := by
            rw [hs1a]
            dsimp only [landRhsI103Leaf64S]
            rw [if_neg hws]
          exact slowContinueStep (G := G) (C := C) (s := s) (s1 := s1) (p := p) (c := c)
            (j := j) (k := k) (r := r) hseg1 hn1 hseg1.inv' hpc1
            (by rw [hs1a]; exact slowLeaf64_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
            hcond1 hword1 ctx hr ih
      · by_cases h32 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
            (BitVec.ofNat 8 32) = 1
        · have hs1a : s1 = landRhsI103Leaf67S s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0) := by
            rw [hs1]; simp only [slowDispOutS, if_neg h13, if_pos h32]
          have hpre : s1.pre = some "LeafBlock67" := by
            rw [hs1a]
            dsimp only [landRhsI103Leaf67S, landRhsI103Node71S]
            rw [if_pos h32]
          have hv : evalOperand s1 (.reg "%ee.011.i") = some (.int 64 (BitVec.ofNat 64 p)) :=
            evalOperand_reg_of _ s1 _ _
              (by rw [hs1a]; exact slowLeaf67_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
          have hcond1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
            rw [hs1a]; exact slowLeaf67_cond ctx.hcond
          have hword1 : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k) := by
            rw [hs1a]; exact ctx.hword
          by_cases heq13 : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
              (BitVec.ofNat 8 13) = 1
          · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1
                then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                  + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                  then "while.end.i" else "while.body.i104")
                else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1
                then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
                else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
                = "while.end.i" := by rw [if_neg h13, if_pos h32, if_pos heq13]
            rw [hblk] at hseg1
            exact slowStopStep (G := G) (C := C) (s := s) (s1 := s1) (leaf := "LeafBlock67")
              hseg1 hn1 hseg1.inv' hpre (by decide) hv hcond1 hd1 hread1 rfl
              (by simpa only [ctx.hj] using ctx.hbit) (by simpa only [ctx.hj] using ctx.h110)
              (by simpa only [ctx.hj] using ctx.h116) (by simpa only [ctx.hj] using ctx.h116eq)
              hidx1 (by simpa only [ctx.hj] using ctx.hqn) he1 htok1 ctx.heoff hword1 ctx.hk
              (by omega)
          · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1
                then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                  + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                  then "while.end.i" else "while.body.i104")
                else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1
                then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
                else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
                = "while.body.i104" := by rw [if_neg h13, if_pos h32, if_neg heq13]
            rw [hblk] at hseg1
            have hpc1 : s1.pc = "while.body.i104" := by
              rw [hs1a]
              dsimp only [landRhsI103Leaf67S]
              rw [if_neg heq13]
            exact slowContinueStep (G := G) (C := C) (s := s) (s1 := s1) (p := p) (c := c)
              (j := j) (k := k) (r := r) hseg1 hn1 hseg1.inv' hpc1
              (by rw [hs1a]; exact slowLeaf67_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
              hcond1 hword1 ctx hr ih
        · have hs1a : s1 = landRhsI103Leaf69S s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0) := by
            rw [hs1]; simp only [slowDispOutS, if_neg h13, if_neg h32]
          have hpre : s1.pre = some "LeafBlock69" := by
            rw [hs1a]
            dsimp only [landRhsI103Leaf69S, landRhsI103Node71S]
            rw [if_neg h32]
          have hv : evalOperand s1 (.reg "%ee.011.i") = some (.int 64 (BitVec.ofNat 64 p)) :=
            evalOperand_reg_of _ s1 _ _
              (by rw [hs1a]; exact slowLeaf69_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
          have hcond1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
            rw [hs1a]; exact slowLeaf69_cond ctx.hcond
          have hword1 : readBytes s1.mem (C.stage.e + 8) 8 = some (wordBytes 8 k) := by
            rw [hs1a]; exact ctx.hword
          by_cases heq32 : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
              (BitVec.ofNat 8 32) = 1
          · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1
                then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                  + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                  then "while.end.i" else "while.body.i104")
                else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1
                then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
                else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
                = "while.end.i" := by rw [if_neg h13, if_neg h32, if_pos heq32]
            rw [hblk] at hseg1
            exact slowStopStep (G := G) (C := C) (s := s) (s1 := s1) (leaf := "LeafBlock69")
              hseg1 hn1 hseg1.inv' hpre (by decide) hv hcond1 hd1 hread1 rfl
              (by simpa only [ctx.hj] using ctx.hbit) (by simpa only [ctx.hj] using ctx.h110)
              (by simpa only [ctx.hj] using ctx.h116) (by simpa only [ctx.hj] using ctx.h116eq)
              hidx1 (by simpa only [ctx.hj] using ctx.hqn) he1 htok1 ctx.heoff hword1 ctx.hk
              (by omega)
          · have hblk : (if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                (BitVec.ofNat 8 13) = 1
                then (if evalICmp .ule (BitVec.ofNat 8 (G.bs.getD p 0).toNat
                  + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                  then "while.end.i" else "while.body.i104")
                else if evalICmp .slt (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1
                then (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 13) = 1 then "while.end.i" else "while.body.i104")
                else (if evalICmp .eq (BitVec.ofNat 8 (G.bs.getD p 0).toNat)
                  (BitVec.ofNat 8 32) = 1 then "while.end.i" else "while.body.i104"))
                = "while.body.i104" := by rw [if_neg h13, if_neg h32, if_neg heq32]
            rw [hblk] at hseg1
            have hpc1 : s1.pc = "while.body.i104" := by
              rw [hs1a]
              dsimp only [landRhsI103Leaf69S]
              rw [if_neg heq32]
            exact slowContinueStep (G := G) (C := C) (s := s) (s1 := s1) (p := p) (c := c)
              (j := j) (k := k) (r := r) hseg1 hn1 hseg1.inv' hpc1
              (by rw [hs1a]; exact slowLeaf69_ee s (BitVec.ofNat 64 p) G.b (G.bs.getD p 0))
              hcond1 hword1 ctx hr ih


/-- **The scan's run at the last entry**: from a landing state entered from
`cond.end.i96` with the entry's index and the stream's end as the counter and the bound,
to the refusal copy, priced inside `5·(G.n − entryPos G C.k) + 10`. -/
theorem slowRun {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) (s : State) (k : Nat)
    (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i103")
    (hpre : s.pre = some "cond.end.i96")
    (hcnt : evalOperand s (slowOp (some "cond.end.i96"))
      = some (.int 64 (BitVec.ofNat 64 (entryPos G C.k))))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 G.n)))
    (hqn : entryPos G C.k < G.n)
    (hbit : (evalICmp .eq (BitVec.ofNat 8 (G.bs.getD (entryPos G C.k) 0).toNat)
      (BitVec.ofNat 8 45) ||| evalICmp .ult
        (BitVec.ofNat 8 (G.bs.getD (entryPos G C.k) 0).toNat + BitVec.ofNat 8 208)
        (BitVec.ofNat 8 10)) = 0)
    (h110 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD (entryPos G C.k) 0).toNat)
      (BitVec.ofNat 8 110) = 0)
    (h116 : evalICmp .slt (BitVec.ofNat 8 (G.bs.getD (entryPos G C.k) 0).toNat)
      (BitVec.ofNat 8 116) = 0)
    (h116eq : evalICmp .eq (BitVec.ofNat 8 (G.bs.getD (entryPos G C.k) 0).toNat)
      (BitVec.ofNat 8 116) = 0)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hword : readBytes s.mem (C.stage.e + 8) 8 = some (wordBytes 8 k)) (hk : k ≤ G.n)
    (heoff : C.eoff ≤ G.n)
    (hinner : G.n - entryPos G C.k ≤ C.inner) :
    ∃ (Cd : WalkCarry G) (sd : State) (n : Nat),
      WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd n ∧
      Cd.block = "if.then" ∧ n ≤ 5 * (G.n - entryPos G C.k) + 10 ∧
      (∃ m, m ≤ G.n ∧ readBytes sd.mem (Cd.stage.e + 8) 8 = some (wordBytes 8 m)) ∧
      Cd.eoff ≤ G.n := by
  have hcw : G.n < 2 ^ 64 := by
    have hm := G.maxDoc
    simp only [stage2MaxDocument] at hm
    omega
  let ctx : SlowCtx G C s "cond.end.i96" (entryPos G C.k) G.n (entryPos G C.k) k :=
    { hpred := Or.inr rfl
      hInv := hInv
      hblock := hblock
      hpre := hpre
      hcnt := hcnt
      hcond := hcond
      hpc := hqn
      hcw := hcw
      hcG := le_rfl
      hinner := hinner
      hj := rfl
      hqn := hqn
      hbit := hbit
      h110 := h110
      h116 := h116
      h116eq := h116eq
      halen := halen
      hevlen := hevlen
      hword := hword
      hk := hk
      heoff := heoff }
  exact slowRun_go G (G.n - entryPos G C.k) C s "cond.end.i96" (entryPos G C.k) G.n
    (entryPos G C.k) k rfl ctx

/-- **The scan's price at the answer-`1` head**: the prefix and the seam's three links
plus the scan's run fit `32·(G.nep − C.k) + 8·(G.n − entryPos G C.k)`, the entry's own
thirty-two absorbing the fixed part and the byte term the run's `5·ΔA`. -/
theorem slowAnswerOnePrice {n1 n : Nat} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (hn1 : n1 ≤ 20) (hn : n ≤ 5 * (G.n - entryPos G C.k) + 10)
    (hΔ : 1 ≤ G.n - entryPos G C.k) (hk : C.k < G.nep) :
    (n1 + n) + 2 ≤ stage2EntryAllowance * (G.nep - C.k) +
      stage2ByteAllowance * (G.n - entryPos G C.k) := by
  have h1 : 1 ≤ G.nep - C.k := by omega
  have h2 : stage2EntryAllowance * 1 ≤ stage2EntryAllowance * (G.nep - C.k) :=
    Nat.mul_le_mul_left _ h1
  simp only [stage2EntryAllowance, stage2ByteAllowance] at h2 ⊢
  omega

#print axioms LeanLLVM.Refinement.WalkScope.slowRun
#print axioms LeanLLVM.Refinement.WalkScope.slowAnswerOnePrice
#print axioms LeanLLVM.Refinement.WalkScope.slowRun_go

#print axioms LeanLLVM.Refinement.WalkScope.walkScanLinksI103_at
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.while_body_i104_at

#print axioms LeanLLVM.Refinement.WalkScope.slowLeafLocal64

end WalkScope
end LeanLLVM.Refinement
