/-
The five scans' inductions.

`WalkScanInduction` (`JsonStage2WalkChain`) names what a scan owes the dispatch: the
visit, the exit and the increment.  This module proves them, at the five latches the
census's `walkScanStepSets` names — the literal comparison's and the four token scans'.

Three facts make it a proof rather than five arguments:

* **every latch is one block shape.**  `scanBlock` is the counter's `add`, the bound's
  `icmp eq` and the two-arm `condbr`, and each scan's latch is that shape at its own
  names (`forInc_find`, `scanWhitespace_find`, `scanString_find`, `scanEscape_find`,
  `scanExtraToken_find`).  So `scanBlock_step` is the latch's step for all five, and its
  two instructions' `denoteCode` is `denoteCode_add_one` and `denoteCode_icmp_eq` at the
  scan's names;
* **the visit is one link.**  The latch is a `condbr` block, so its `WalkLink` is
  `WalkLink.pureCore`'s: the invariant at the target is that core's, built from the
  block's `denoteCode` and the two arms' `WalkLocal` facts.  A `WalkSegment` of one step
  is `WalkSegment.of_link`, and `walkLink_runFuel` is its run;
* **the exit is the test's other arm.**  The latch's test is `%inc = %cond`, so the exit
  is `i + 1 = c` and the visit is `i + 1 < c`; both are the same computed bit, which is
  why the two fields are one equation apart.

The counter the induction needs is the one the invariant already carries: `ScanCount`
bounds `c - i` by the carry's `inner`, and `ScanCount.same` reads the caller's `i` and
`c` as that witness's, which is what the landing block's `WalkLocal` (the `ScanLanded`
disjunct) needs.
-/
import LeanLLVM.Refinement.JsonStage2WalkChain

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The counter the invariant carries

The latch's `WalkLocal` is a `ScanCount`, so the carry already holds the pair the
induction counts.  The step is stated at the pair the *caller* reads off the two
registers, so the two readings are the same one — which is the arithmetic below, not a
new hypothesis. -/

/-- **The scan count at the caller's pair.**  Two `ofNat 64` values that a register
read equates are equal (each is below `2 ^ 64`), so the invariant's bound is the
caller's. -/
theorem ScanCount.same {s : State} {phi cond : String} {inner : Nat}
    (h : ScanCount s phi cond inner) {i c : Nat}
    (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hic : i < c) : c - i ≤ inner := by
  obtain ⟨i₀, c₀, hsub, hlt, hcw₀, hi₀, hc₀⟩ := h
  have hB : BitVec.ofNat 64 c₀ = BitVec.ofNat 64 c := by
    injection Option.some.inj (hc₀.symm.trans hc)
  have hcEq : c₀ = c := by
    have hnat := congrArg BitVec.toNat hB
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hnat
    omega
  have hA : BitVec.ofNat 64 i₀ = BitVec.ofNat 64 i := by
    injection Option.some.inj (hi₀.symm.trans hi)
  have hiEq : i₀ = i := by
    have hnat := congrArg BitVec.toNat hA
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hnat
    omega
  rw [← hiEq, ← hcEq]
  exact hsub

/-! ### The latch's two instructions

`scanBlock`'s run: the counter's increment, then the bound's equality test.  Both are
`BlockEval`'s step shapes at the scan's own names, so the block's `denoteCode` is two
rewrites. -/

/-- **A scan latch's `denoteCode`**: the increment's cell and the test's cell, at the
environment the builder extends. -/
theorem scanBlock_den {calls : Calls} (s : State) {src inc phi test cond : String}
    {B : Block} (hfind : stage2Body.findBlock src = some B)
    (his : B.instrs = [Instr.binop inc BinOp.add 64 (.reg phi)
        (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp test IPred.eq 64 (.reg inc) (.reg cond)])
    (hne : inc ≠ cond)
    {i c : Nat} (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c))) :
    denoteCode calls B.instrs s = some (stateAt (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) s) := by
  have hadd : BitVec.ofNat 64 i + BitVec.ofNat 64 1 = BitVec.ofNat 64 (i + 1) := by
    rw [← BitVec.ofNat_add (n := 64) i 1]
  rw [his,
    denoteCode_add_one calls s inc phi (x := BitVec.ofNat 64 i) hi,
    denoteCode_icmp_eq calls (s.bind inc (.int 64 (BitVec.ofNat 64 i + BitVec.ofNat 64 1)))
      test inc cond (x := BitVec.ofNat 64 i + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (by simp only [State.bind, lookupName_cons_self])
      (by
        simp only [State.bind]
        rw [lookupName_cons_ne _ _ hne]
        exact hc),
    hadd]
  rfl

/-- **A scan latch's step, at the state it names.**  The test's bit picks the scan's
exit or its back edge, so one equation states both arms — the field's two cases. -/
theorem scanBlock_step {calls : Calls} (s : State) {src inc phi test cond exit land : String}
    {B : Block} (hpc : s.pc = src) (hfind : stage2Body.findBlock src = some B)
    (his : B.instrs = [Instr.binop inc BinOp.add 64 (.reg phi)
        (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp test IPred.eq 64 (.reg inc) (.reg cond)])
    (ht : B.term = Term.condbr (.reg test) exit land)
    (hne : inc ≠ cond)
    {i c : Nat} (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hbit : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 ∨
      evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1) :
    step calls stage2Body s =
      .jump { stateAt (cells
        [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) s with
        pc := (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
          then exit else land)
        pre := some s.pc } := by
  have hden := scanBlock_den (calls := calls) s hfind his hne hi hc
  simp only [step, hpc, hfind, hden, ht, execTerm]
  simp only [evalOperand, stateAt, cells, lookupName_cons_self]
  rcases hbit with h | h <;> simp [h, hpc]

/-- **A one-step segment.**  A link is a segment at its own count, and the run is
`walkLink_runFuel`'s — no `WalkChain` is needed to read it. -/
theorem WalkSegment.of_link {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (hl : WalkLink calls G C s C' s') :
    WalkSegment calls G C s C' s' 1 where
  run n := walkLink_runFuel hl n
  inv' := hl.inv'

/-! ### The visit

The latch's step is one link, so the induction's `step` field is a one-step segment.
Its target is the state `pureCore` names, written here as a `def` so the two
`WalkLocal` side conditions and the two re-pinned registers are stated once. -/

/-- The state a scan's latch leaves: the increment's cell and the test's cell, at the
edge's destination. -/
abbrev scanLatchOut (s : State) (inc test : String) (i c : Nat) (t : String) : State :=
  { stateAt (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) s with
    pc := t, pre := some s.pc }

/-- **A scan latch's visit.**  Short of the bound, the latch is one control step to its
landing block: the increment is written, the test is clear, and the invariant at the
landing block is `pureCore`'s — the block's `denoteCode` and the two arms' local facts
are all it reads. -/
theorem scanLatch_visit {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    {src inc phi test cond exit land : String} (hsrc : C.block = src)
    {B : Block} (hfind : stage2Body.findBlock src = some B)
    (his : B.instrs = [Instr.binop inc BinOp.add 64 (.reg phi)
        (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp test IPred.eq 64 (.reg inc) (.reg cond)])
    (ht : B.term = Term.condbr (.reg test) exit land)
    (hneIC : inc ≠ cond) (hneTI : test ≠ inc) (hneTC : test ≠ cond)
    (hfree : walkCarried B.instrs)
    {i c : Nat} (hi : lookupName s.env phi = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env cond = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hlt : i + 1 < c)
    (hexit : WalkLocal { C with block := exit } (scanLatchOut s inc test i c exit))
    (hland : WalkLocal { C with block := land } (scanLatchOut s inc test i c land)) :
    ∃ (C' : WalkCarry G) (s' : State), WalkSegment calls G C s C' s' 1 ∧
      C'.block = land ∧
      lookupName s'.env inc = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName s'.env cond = some (.int 64 (BitVec.ofNat 64 c)) := by
  have hpc : s.pc = src := by rw [hInv.pc_eq, hsrc]
  -- the test is clear at a visit, and set at the exit
  have hb0 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 0 := by
    rw [evalICmp_eq_zero_iff]
    intro heq
    have hnat := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega: c < 2 ^ 64)] at hnat
    omega
  have hden := scanBlock_den (calls := calls) s hfind his hneIC hi hc
  -- the link, from the block's run and its two arms
  obtain ⟨s', hl⟩ := WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := B) (hfind := by rw [hsrc]; exact hfind)
    (s₁ := stateAt (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) s)
    hden hfree rfl rfl ht
    (bit := evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))
    (hbit := by
      show lookupName (cells
        [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) test =
        some (.int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c)))
      simp only [cells]
      rw [lookupName_cons_self])
    (by simpa only [scanLatchOut] using hexit)
    (by simpa only [scanLatchOut] using hland)
  have hres : (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
      then exit else land) = land := if_neg (by rw [hb0]; decide)
  have hstepN := scanBlock_step (calls := calls) s hpc hfind his ht hneIC hi hc (Or.inl hb0)
  rw [hres] at hstepN
  have hse : s' = scanLatchOut s inc test i c land := by
    rw [hl.step] at hstepN
    simpa only [scanLatchOut] using Ctrl.jump.inj hstepN
  refine ⟨{ C with block := land }, scanLatchOut s inc test i c land, ?_, rfl, ?_, ?_⟩
  · rw [hse] at hl
    rw [hres] at hl
    exact WalkSegment.of_link hl
  · show lookupName (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) inc =
      some (.int 64 (BitVec.ofNat 64 (i + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ hneTI, lookupName_cons_self]
  · show lookupName (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) cond =
      some (.int 64 (BitVec.ofNat 64 c))
    simp only [cells]
    rw [lookupName_cons_ne _ _ hneTC, lookupName_cons_ne _ _ hneIC]
    exact hc

/-! ### The scan's way back

A visit's second half.  The whitespace scan's landing block jumps to `NodeBlock52`, which
compares the byte against `13`; the first arm is `LeafBlock43` (the path the head chain
already crosses) and the second is `NodeBlock50`'s second comparison against `32`, whose
two arms are `LeafBlock46` (the byte is `13`) and `LeafBlock48` (it is `32`).  Each leaf
takes the back edge to `while.body370.i` when its own equality is clear.

So the way back from `NodeBlock52` is three classes of byte, and each class is two links:
the pivot's and the leaf's.  The class facts are the caller's, exactly as the head
chain's pivots take theirs; what the leaves need beyond them is the latch's own local
fact, which is `WalkLocal.whitespace`'s at the counter the visit writes. -/

/-- The state `NodeBlock50` leaves at the class that takes its first arm. -/
abbrev scanNodeBlock50Out (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot51" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock46", pre := some s.pc }

/-- The state `LeafBlock46` leaves at the class that takes the back edge. -/
abbrev scanLeafBlock46Out (s : State) (x : BitVec 8) : State :=
  { stateAt ((("%SwitchLeaf47", .int 1 (evalICmp .eq x (BitVec.ofNat 8 13)))) :: s.env) s with
    pc := "while.body370.i", pre := some s.pc }

/-- The state `LeafBlock48` leaves at the class that takes the back edge. -/
abbrev scanLeafBlock48Out (s : State) (x : BitVec 8) : State :=
  { stateAt ((("%SwitchLeaf49", .int 1 (evalICmp .eq x (BitVec.ofNat 8 32)))) :: s.env) s with
    pc := "while.body370.i", pre := some s.pc }

/-- **The chain extended by `NodeBlock52`'s second arm.**  The byte is at or above `13`,
so the pivot reaches `NodeBlock50`. -/
theorem walkChain_extend_nodeBlock50 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock52")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hge13 : evalICmp .slt x (BitVec.ofNat 8 13) = 0) :
    WalkChain calls G C₀ s₀ { C with block := "NodeBlock50" }
      { (s.bind "%Pivot53" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))) with
        pc := "NodeBlock50", pre := some s.pc } := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "NodeBlock50" := if_neg (by rw [hge13]; decide)
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock52_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = { (s.bind "%Pivot53" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))) with
      pc := "NodeBlock50", pre := some s.pc } := by
    rw [hs]
    simp only [hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `NodeBlock50`'s first arm.**  The byte is below `32`, so the
second pivot reaches `LeafBlock46`. -/
theorem walkChain_extend_nodeBlock50Out {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock50")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hlt32 : evalICmp .slt x (BitVec.ofNat 8 32) = 1) :
    WalkChain calls G C₀ s₀ { C with block := "LeafBlock46" } (scanNodeBlock50Out s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 32) = 1
      then "LeafBlock46" else "LeafBlock48") = "LeafBlock46" := if_pos hlt32
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock50_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = scanNodeBlock50Out s x := by
    rw [hs]
    simp only [scanNodeBlock50Out, hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `NodeBlock50`'s second arm.**  The byte is at or above `32`,
so the second pivot reaches `LeafBlock48`. -/
theorem walkChain_extend_nodeBlock48 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock50")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hge32 : evalICmp .slt x (BitVec.ofNat 8 32) = 0) :
    WalkChain calls G C₀ s₀ { C with block := "LeafBlock48" }
      { (s.bind "%Pivot51" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))) with
        pc := "LeafBlock48", pre := some s.pc } := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 32) = 1
      then "LeafBlock46" else "LeafBlock48") = "LeafBlock48" := if_neg (by rw [hge32]; decide)
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock50_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = { (s.bind "%Pivot51" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))) with
      pc := "LeafBlock48", pre := some s.pc } := by
    rw [hs]
    simp only [hres]
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `LeafBlock46`'s back edge.**  The byte is not `13`, so the
leaf returns to the latch. -/
theorem walkChain_extend_leafBlock46 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "LeafBlock46")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hne13 : evalICmp .eq x (BitVec.ofNat 8 13) = 0)
    (hsc : ScanCount (scanLeafBlock46Out s x) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ { C with block := "while.body370.i" } (scanLeafBlock46Out s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .eq x (BitVec.ofNat 8 13) = 1
      then "if.end372.i" else "while.body370.i") = "while.body370.i" :=
    if_neg (by rw [hne13]; decide)
  have hloc : WalkLocal { C with block := "while.body370.i" } (scanLeafBlock46Out s x) := by
    rw [WalkLocal.whitespace (C := { C with block := "while.body370.i" })
      (s := scanLeafBlock46Out s x) rfl]
    exact hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.LeafBlock46_at G C s (WalkChain.inv_last hchain) hblock h1 hloc
  have hstep : s' = scanLeafBlock46Out s x := by
    rw [hs]
    simp only [scanLeafBlock46Out, hres]
    rfl
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-- **The chain extended by `LeafBlock48`'s back edge.**  The byte is not `32`, so the
leaf returns to the latch. -/
theorem walkChain_extend_leafBlock48 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "LeafBlock48")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hne32 : evalICmp .eq x (BitVec.ofNat 8 32) = 0)
    (hsc : ScanCount (scanLeafBlock48Out s x) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ { C with block := "while.body370.i" } (scanLeafBlock48Out s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .eq x (BitVec.ofNat 8 32) = 1
      then "if.end372.i" else "while.body370.i") = "while.body370.i" :=
    if_neg (by rw [hne32]; decide)
  have hloc : WalkLocal { C with block := "while.body370.i" } (scanLeafBlock48Out s x) := by
    rw [WalkLocal.whitespace (C := { C with block := "while.body370.i" })
      (s := scanLeafBlock48Out s x) rfl]
    exact hsc
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.LeafBlock48_at G C s (WalkChain.inv_last hchain) hblock h1 hloc
  have hstep : s' = scanLeafBlock48Out s x := by
    rw [hs]
    simp only [scanLeafBlock48Out, hres]
    rfl
  rw [hstep] at hl
  rw [hres] at hl
  exact hchain.append (WalkChain.tail hl (WalkChain.nil hl.inv'))

/-! ### The five inductions

Each instance is its latch's `find` and shape, the two disequalities its names give,
the block's `walkCarried`, and the two arms' `WalkLocal` facts — the exit's is `True`
at every scan's exit block, and the landing's is the `ScanLanded` disjunct, whose
witness is the counter the visit writes. -/

/-- **The whitespace skip's induction.** -/
theorem walkInductionWhitespace_holds {calls : Calls} {m0 : Mem} {G : WalkGeom m0} :
    walkInductionWhitespace calls G where
  step C s hInv hblock i c hi hc hcw hlt := by
    have hSC : ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
      have h := hInv.blockLocal
      rwa [WalkLocal.whitespace hblock] at h
    have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
    have hexit : WalkLocal { C with block := "if.end372.i" }
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "if.end372.i") := by
      simp [WalkLocal]
    have hpre : (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").pre =
        some "while.body370.i" := by
      show some s.pc = some "while.body370.i"
      rw [hInv.pc_eq, hblock]
    have hinc : lookupName
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").env "%inc371.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
      show lookupName (cells
        [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1))
            (BitVec.ofNat 64 c))),
         ("%inc371.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc371.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1)))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hcond : lookupName
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      show lookupName (cells
        [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1))
            (BitVec.ofNat 64 c))),
         ("%inc371.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 c))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have hland : WalkLocal { C with block := "land.rhs.i" }
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") := by
      rw [WalkLocal.whitespaceLanded rfl]
      exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
        hpre, hinc, hcond⟩
    obtain ⟨C', s', hseg, hlandBlock, hinc', hcond'⟩ :=
      scanLatch_visit (calls := calls) (G := G) (C := C) (s := s) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
    exact ⟨C', s', 1, hseg, hlandBlock, by simp [stage2ByteAllowance], hinc', hcond'⟩
  exitStep C s hInv hblock i c hi hc hcw hie := by
    have hpc : s.pc = "while.body370.i" := by rw [hInv.pc_eq, hblock]
    have hb1 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1 := by
      rw [hie]
      simp [evalICmp]
    refine ⟨_, scanBlock_step (calls := calls) s hpc scanWhitespace_find
      (inc := "%inc371.i") (phi := "%ee.0.i238") (test := "%exitcond.not")
      (cond := "%cond350.i") (exit := "if.end372.i") (land := "land.rhs.i")
      (i := i) (c := c)
      rfl rfl (by decide) hi hc (Or.inr hb1), ?_⟩
    show (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
      then "if.end372.i" else "land.rhs.i") = "if.end372.i"
    rw [hb1]
    rfl


/-- **The string scan's induction.** -/
theorem walkInductionString_holds {calls : Calls} {m0 : Mem} {G : WalkGeom m0} :
    walkInductionString calls G where
  step C s hInv hblock i c hi hc hcw hlt := by
    have hSC : ScanCount s "%ee.011.i" "%cond.i" C.inner := by
      have h := hInv.blockLocal
      rwa [WalkLocal.stringScan hblock] at h
    have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
    have hexit : WalkLocal { C with block := "cleanup474.i" }
        (scanLatchOut s "%inc.i105" "%exitcond.not.i" i c "cleanup474.i") := by
      simp [WalkLocal]
    have hpre : (scanLatchOut s "%inc.i105" "%exitcond.not.i" i c "land.rhs.i103").pre = some "while.body.i104" := by
      show some s.pc = some "while.body.i104"
      rw [hInv.pc_eq, hblock]
    have hinc : lookupName (scanLatchOut s "%inc.i105" "%exitcond.not.i" i c "land.rhs.i103").env "%inc.i105" =
        some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
      show lookupName (cells
        [("%exitcond.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc.i105", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc.i105" =
        some (.int 64 (BitVec.ofNat 64 (i + 1)))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hcond : lookupName (scanLatchOut s "%inc.i105" "%exitcond.not.i" i c "land.rhs.i103").env "%cond.i" =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      show lookupName (cells
        [("%exitcond.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc.i105", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%cond.i" =
        some (.int 64 (BitVec.ofNat 64 c))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have hland : WalkLocal { C with block := "land.rhs.i103" }
        (scanLatchOut s "%inc.i105" "%exitcond.not.i" i c "land.rhs.i103") := by
      rw [WalkLocal.stringScanLanded rfl]
      exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
        hpre, hinc, hcond⟩
    obtain ⟨C', s', hseg, hlandBlock, hinc', hcond'⟩ :=
      scanLatch_visit (calls := calls) (G := G) (C := C) (s := s) hInv hblock
        (src := "while.body.i104") (inc := "%inc.i105") (phi := "%ee.011.i") (test := "%exitcond.not.i")
        (cond := "%cond.i") (exit := "cleanup474.i") (land := "land.rhs.i103")
        (B := scanBlock "while.body.i104" "%inc.i105" "%ee.011.i" "%exitcond.not.i" "%cond.i" "cleanup474.i" "land.rhs.i103")
        scanString_find rfl rfl (by decide) (by decide) (by decide)
        (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
    exact ⟨C', s', 1, hseg, hlandBlock, by simp [stage2ByteAllowance], hinc', hcond'⟩
  exitStep C s hInv hblock i c hi hc hcw hie := by
    have hpc : s.pc = "while.body.i104" := by rw [hInv.pc_eq, hblock]
    have hb1 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1 := by
      rw [hie]
      simp [evalICmp]
    refine ⟨_, scanBlock_step (calls := calls) s hpc scanString_find
      (inc := "%inc.i105") (phi := "%ee.011.i") (test := "%exitcond.not.i") (cond := "%cond.i")
      (exit := "cleanup474.i") (land := "land.rhs.i103") (i := i) (c := c)
      rfl rfl (by decide) hi hc (Or.inr hb1), ?_⟩
    show (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
      then "cleanup474.i" else "land.rhs.i103") = "cleanup474.i"
    rw [hb1]
    rfl

/-- **The escape scan's induction.** -/
theorem walkInductionEscape_holds {calls : Calls} {m0 : Mem} {G : WalkGeom m0} :
    walkInductionEscape calls G where
  step C s hInv hblock i c hi hc hcw hlt := by
    have hSC : ScanCount s "%s2.020.i" "%cond.i" C.inner := by
      have h := hInv.blockLocal
      rwa [WalkLocal.escape hblock] at h
    have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
    have hexit : WalkLocal { C with block := "while.end78.i" }
        (scanLatchOut s "%inc77.i" "%exitcond24.not.i" i c "while.end78.i") := by
      simp [WalkLocal]
    have hpre : (scanLatchOut s "%inc77.i" "%exitcond24.not.i" i c "land.rhs71.i").pre = some "while.body76.i" := by
      show some s.pc = some "while.body76.i"
      rw [hInv.pc_eq, hblock]
    have hinc : lookupName (scanLatchOut s "%inc77.i" "%exitcond24.not.i" i c "land.rhs71.i").env "%inc77.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
      show lookupName (cells
        [("%exitcond24.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc77.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc77.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1)))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hcond : lookupName (scanLatchOut s "%inc77.i" "%exitcond24.not.i" i c "land.rhs71.i").env "%cond.i" =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      show lookupName (cells
        [("%exitcond24.not.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc77.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%cond.i" =
        some (.int 64 (BitVec.ofNat 64 c))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have hland : WalkLocal { C with block := "land.rhs71.i" }
        (scanLatchOut s "%inc77.i" "%exitcond24.not.i" i c "land.rhs71.i") := by
      rw [WalkLocal.escapeLanded rfl]
      exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
        hpre, hinc, hcond⟩
    obtain ⟨C', s', hseg, hlandBlock, hinc', hcond'⟩ :=
      scanLatch_visit (calls := calls) (G := G) (C := C) (s := s) hInv hblock
        (src := "while.body76.i") (inc := "%inc77.i") (phi := "%s2.020.i") (test := "%exitcond24.not.i")
        (cond := "%cond.i") (exit := "while.end78.i") (land := "land.rhs71.i")
        (B := scanBlock "while.body76.i" "%inc77.i" "%s2.020.i" "%exitcond24.not.i" "%cond.i" "while.end78.i" "land.rhs71.i")
        scanEscape_find rfl rfl (by decide) (by decide) (by decide)
        (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
    exact ⟨C', s', 1, hseg, hlandBlock, by simp [stage2ByteAllowance], hinc', hcond'⟩
  exitStep C s hInv hblock i c hi hc hcw hie := by
    have hpc : s.pc = "while.body76.i" := by rw [hInv.pc_eq, hblock]
    have hb1 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1 := by
      rw [hie]
      simp [evalICmp]
    refine ⟨_, scanBlock_step (calls := calls) s hpc scanEscape_find
      (inc := "%inc77.i") (phi := "%s2.020.i") (test := "%exitcond24.not.i") (cond := "%cond.i")
      (exit := "while.end78.i") (land := "land.rhs71.i") (i := i) (c := c)
      rfl rfl (by decide) hi hc (Or.inr hb1), ?_⟩
    show (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
      then "while.end78.i" else "land.rhs71.i") = "while.end78.i"
    rw [hb1]
    rfl

/-- **The extra-token scan's induction.** -/
theorem walkInductionExtraToken_holds {calls : Calls} {m0 : Mem} {G : WalkGeom m0} :
    walkInductionExtraToken calls G where
  step C s hInv hblock i c hi hc hcw hlt := by
    have hSC : ScanCount s "%q.0.i246" "%cond350.i" C.inner := by
      have h := hInv.blockLocal
      rwa [WalkLocal.extraToken hblock] at h
    have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
    have hexit : WalkLocal { C with block := "if.end473.i" }
        (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "if.end473.i") := by
      simp [WalkLocal]
    have hpre : (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i").pre = some "while.body462.i" := by
      show some s.pc = some "while.body462.i"
      rw [hInv.pc_eq, hblock]
    have hinc : lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i").env "%inc463.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
      show lookupName (cells
        [("%exitcond298.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc463.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc463.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1)))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hcond : lookupName (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i").env "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      show lookupName (cells
        [("%exitcond298.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
         ("%inc463.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%cond350.i" =
        some (.int 64 (BitVec.ofNat 64 c))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have hland : WalkLocal { C with block := "land.rhs457.i" }
        (scanLatchOut s "%inc463.i" "%exitcond298.not" i c "land.rhs457.i") := by
      rw [WalkLocal.extraTokenLanded rfl]
      exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
        hpre, hinc, hcond⟩
    obtain ⟨C', s', hseg, hlandBlock, hinc', hcond'⟩ :=
      scanLatch_visit (calls := calls) (G := G) (C := C) (s := s) hInv hblock
        (src := "while.body462.i") (inc := "%inc463.i") (phi := "%q.0.i246") (test := "%exitcond298.not")
        (cond := "%cond350.i") (exit := "if.end473.i") (land := "land.rhs457.i")
        (B := scanBlock "while.body462.i" "%inc463.i" "%q.0.i246" "%exitcond298.not" "%cond350.i" "if.end473.i" "land.rhs457.i")
        scanExtraToken_find rfl rfl (by decide) (by decide) (by decide)
        (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
    exact ⟨C', s', 1, hseg, hlandBlock, by simp [stage2ByteAllowance], hinc', hcond'⟩
  exitStep C s hInv hblock i c hi hc hcw hie := by
    have hpc : s.pc = "while.body462.i" := by rw [hInv.pc_eq, hblock]
    have hb1 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1 := by
      rw [hie]
      simp [evalICmp]
    refine ⟨_, scanBlock_step (calls := calls) s hpc scanExtraToken_find
      (inc := "%inc463.i") (phi := "%q.0.i246") (test := "%exitcond298.not") (cond := "%cond350.i")
      (exit := "if.end473.i") (land := "land.rhs457.i") (i := i) (c := c)
      rfl rfl (by decide) hi hc (Or.inr hb1), ?_⟩
    show (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
      then "if.end473.i" else "land.rhs457.i") = "if.end473.i"
    rw [hb1]
    rfl


/-- **The literal comparison's induction.**  Its latch is `for.inc.i.i` — the same
`scanBlock` shape as the token scans' — and its landing block's local fact is written
out, since the comparison's counter pair is the first branch of `WalkLocal` rather than
one of the four scans' `ScanLanded` forms. -/
theorem walkInductionLiteral_holds {calls : Calls} {m0 : Mem} {G : WalkGeom m0} :
    walkInductionLiteral calls G where
  step C s hInv hblock i c hi hc hcw hlt := by
    have hSC : ScanCount s "%i.029.i.i" "%cond.i.i" C.inner := by
      have h := hInv.blockLocal
      rwa [show WalkLocal C s = ScanCount s "%i.029.i.i" "%cond.i.i" C.inner from by
        simp [WalkLocal, ScanCount, hblock]] at h
    have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
    have hexit : WalkLocal { C with block := "for.end.i.i" }
        (scanLatchOut s "%inc.i.i" "%exitcond.not.i.i" i c "for.end.i.i") := by
      simp [WalkLocal]
    have hpre : (scanLatchOut s "%inc.i.i" "%exitcond.not.i.i" i c "for.body.i.i").pre =
        some "for.inc.i.i" := by
      show some s.pc = some "for.inc.i.i"
      rw [hInv.pc_eq, hblock]
    have hinc : lookupName
        (scanLatchOut s "%inc.i.i" "%exitcond.not.i.i" i c "for.body.i.i").env "%inc.i.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
      show lookupName (cells
        [("%exitcond.not.i.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1))
            (BitVec.ofNat 64 c))),
         ("%inc.i.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc.i.i" =
        some (.int 64 (BitVec.ofNat 64 (i + 1)))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    have hcond : lookupName
        (scanLatchOut s "%inc.i.i" "%exitcond.not.i.i" i c "for.body.i.i").env "%cond.i.i" =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      show lookupName (cells
        [("%exitcond.not.i.i", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1))
            (BitVec.ofNat 64 c))),
         ("%inc.i.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%cond.i.i" =
        some (.int 64 (BitVec.ofNat 64 c))
      simp only [cells]
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have hland : WalkLocal { C with block := "for.body.i.i" }
        (scanLatchOut s "%inc.i.i" "%exitcond.not.i.i" i c "for.body.i.i") := by
      simp only [WalkLocal]
      exact Or.inl ⟨i + 1, c, by show c - (i + 1) ≤ C.inner; omega, hlt, hcw,
        hpre, hinc, hcond⟩
    obtain ⟨C', s', hseg, hlandBlock, hinc', hcond'⟩ :=
      scanLatch_visit (calls := calls) (G := G) (C := C) (s := s) hInv hblock
        (src := "for.inc.i.i") (inc := "%inc.i.i") (phi := "%i.029.i.i")
        (test := "%exitcond.not.i.i") (cond := "%cond.i.i") (exit := "for.end.i.i")
        (land := "for.body.i.i")
        (B := scanBlock "for.inc.i.i" "%inc.i.i" "%i.029.i.i" "%exitcond.not.i.i"
          "%cond.i.i" "for.end.i.i" "for.body.i.i")
        forInc_find rfl rfl (by decide) (by decide) (by decide)
        (by unfold walkCarried scanBlock; decide) hi hc hcw hlt hexit hland
    exact ⟨C', s', 1, hseg, hlandBlock, by simp [stage2ByteAllowance], hinc', hcond'⟩
  exitStep C s hInv hblock i c hi hc hcw hie := by
    have hpc : s.pc = "for.inc.i.i" := by rw [hInv.pc_eq, hblock]
    have hb1 : evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1 := by
      rw [hie]
      simp [evalICmp]
    refine ⟨_, scanBlock_step (calls := calls) s hpc forInc_find
      (inc := "%inc.i.i") (phi := "%i.029.i.i") (test := "%exitcond.not.i.i")
      (cond := "%cond.i.i") (exit := "for.end.i.i") (land := "for.body.i.i")
      (i := i) (c := c)
      rfl rfl (by decide) hi hc (Or.inr hb1), ?_⟩
    rw [show (if evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c) = 1
        then "for.end.i.i" else "for.body.i.i") = "for.end.i.i" from by
      rw [hb1]
      rfl]

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.ScanCount.same
#print axioms LeanLLVM.Refinement.WalkScope.scanBlock_den
#print axioms LeanLLVM.Refinement.WalkScope.scanBlock_step
#print axioms LeanLLVM.Refinement.WalkScope.scanLatch_visit
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_nodeBlock50
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_nodeBlock50Out
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_nodeBlock48
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_leafBlock46
#print axioms LeanLLVM.Refinement.WalkScope.walkChain_extend_leafBlock48
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionLiteral_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionWhitespace_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionString_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionEscape_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionExtraToken_holds

end WalkScope

end LeanLLVM.Refinement
