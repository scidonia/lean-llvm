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
theorem scanLatch_link {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
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
    ∃ (s' : State), WalkLink calls G C s { C with block := land } s' ∧
      s' = scanLatchOut s inc test i c land ∧
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
  rw [hres] at hl
  refine ⟨s', hl, hse, ?_, ?_⟩
  · rw [hse]
    show lookupName (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) inc =
      some (.int 64 (BitVec.ofNat 64 (i + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ hneTI, lookupName_cons_self]
  · rw [hse]
    show lookupName (cells
      [(test, .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 c))),
       (inc, .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) cond =
      some (.int 64 (BitVec.ofNat 64 c))
    simp only [cells]
    rw [lookupName_cons_ne _ _ hneTC, lookupName_cons_ne _ _ hneIC]
    exact hc

/-- **A scan latch's visit**, as a segment: the link of `scanLatch_link` at its own count. -/
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
  obtain ⟨s', hl, _, hi', hc'⟩ :=
    scanLatch_link G C s hInv hsrc hfind his ht hneIC hneTI hneTC hfree hi hc hcw hlt hexit hland
  exact ⟨_, s', WalkSegment.of_link hl, rfl, hi', hc'⟩

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

/-- The carry the scan's second pivot leaves: `NodeBlock52`'s second arm. -/
def scanCarryNodeBlock50 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "NodeBlock50" }

/-- The carry `NodeBlock50` leaves at the class that takes its first arm. -/
def scanCarryLeafBlock46 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { scanCarryNodeBlock50 C with block := "LeafBlock46" }

/-- The carry `NodeBlock50` leaves at the class that takes its second arm.  A chain's
carry is an index, so the composition names it rather than writing the nest: two nests
that are equal are not thereby the same index. -/
def scanCarryLeafBlock48 {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { scanCarryNodeBlock50 C with block := "LeafBlock48" }

/-- The carry a leaf's back edge leaves: its own, at the latch. -/
def scanCarryLatchOf {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G) : WalkCarry G :=
  { C with block := "while.body370.i" }

/-- The state `NodeBlock52`'s second arm enters: the pivot's own cell, at `NodeBlock50`. -/
def scanNodeBlock50In (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot53" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))) with
    pc := "NodeBlock50", pre := some s.pc }

/-- The state `NodeBlock50` leaves at the class that takes its first arm. -/
abbrev scanNodeBlock50Out (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot51" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock46", pre := some s.pc }

/-- The state `NodeBlock50` leaves at the class that takes its second arm. -/
abbrev scanNodeBlock48Out (s : State) (x : BitVec 8) : State :=
  { (s.bind "%Pivot51" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))) with
    pc := "LeafBlock48", pre := some s.pc }

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
    WalkChain calls G C₀ s₀ (scanCarryNodeBlock50 C) (scanNodeBlock50In s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "NodeBlock50" := if_neg (by rw [hge13]; decide)
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock52_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = scanNodeBlock50In s x := by
    rw [hs]
    simp only [scanNodeBlock50In, hres]
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
    WalkChain calls G C₀ s₀ (scanCarryLeafBlock48 C) (scanNodeBlock48Out s x) := by
  have h1 : evalOperand s (.reg "%36") = some (.int 8 x) := h36
  have hres : (if evalICmp .slt x (BitVec.ofNat 8 32) = 1
      then "LeafBlock46" else "LeafBlock48") = "LeafBlock48" := if_neg (by rw [hge32]; decide)
  obtain ⟨s', hl, hs⟩ :=
    WalkLink.NodeBlock50_at G C s (WalkChain.inv_last hchain) hblock h1
  have hstep : s' = scanNodeBlock48Out s x := by
    rw [hs]
    simp only [scanNodeBlock48Out, hres]
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
    WalkChain calls G C₀ s₀ (scanCarryLatchOf C) (scanLeafBlock48Out s x) := by
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

/-! ### The way back, composed

The three classes of byte that continue the whitespace scan, each as one chain from the
latch's dispatch node back to the latch.  What the leaves need of the counter is the same
`ScanCount` the latch holds: no pivot between them binds `%ee.0.i238` or `%cond350.i`, so
the fact transfers across each cell as a lookup peel. -/

/-- **The scan count across a cell.**  A cell at another name moves neither of the two
registers the count reads. -/
theorem ScanCount.bind {s : State} {phi cond : String} {inner : Nat}
    (h : ScanCount s phi cond inner) {d : String} {v : Value}
    (hp : d ≠ phi) (hc : d ≠ cond) : ScanCount (s.bind d v) phi cond inner := by
  obtain ⟨i, c, hsub, hlt, hcw, hi, hc'⟩ := h
  refine ⟨i, c, hsub, hlt, hcw, ?_, ?_⟩
  · rw [show (s.bind d v).env = (d, v) :: s.env from rfl, lookupName_cons_ne _ _ hp]
    exact hi
  · rw [show (s.bind d v).env = (d, v) :: s.env from rfl, lookupName_cons_ne _ _ hc]
    exact hc'

/-- **The scan count across the environment builder.** -/
theorem ScanCount.stateAt_cells {s : State} {phi cond : String} {inner : Nat}
    (h : ScanCount s phi cond inner) (cs : List (String × Value))
    (hne : ∀ c ∈ cs, c.1 ≠ phi ∧ c.1 ≠ cond) :
    ScanCount (stateAt (cells cs s.env) s) phi cond inner := by
  obtain ⟨i, c, hsub, hlt, hcw, hi, hc'⟩ := h
  have go : ∀ cs : List (String × Value),
      (∀ c ∈ cs, c.1 ≠ phi ∧ c.1 ≠ cond) →
      lookupName (cells cs s.env) phi = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName (cells cs s.env) cond = some (.int 64 (BitVec.ofNat 64 c)) := by
    intro cs
    induction cs with
    | nil => intro _; exact ⟨hi, hc'⟩
    | cons hd tl ih =>
        intro hne'
        obtain ⟨k, v⟩ := hd
        obtain ⟨h1, h2⟩ := hne' (k, v) (by simp)
        obtain ⟨ih1, ih2⟩ := ih (fun c hc => hne' c (by simp [hc]))
        refine ⟨?_, ?_⟩
        · rw [show cells ((k, v) :: tl) s.env = (k, v) :: cells tl s.env from rfl,
            lookupName_cons_ne _ _ h1]
          exact ih1
        · rw [show cells ((k, v) :: tl) s.env = (k, v) :: cells tl s.env from rfl,
            lookupName_cons_ne _ _ h2]
          exact ih2
  obtain ⟨h1, h2⟩ := go cs hne
  exact ⟨i, c, hsub, hlt, hcw, by simpa only [stateAt] using h1,
    by simpa only [stateAt] using h2⟩

/-- **The way back through `LeafBlock43`.**  The byte is below `13` and its own test is
clear, so the pivot's first arm and the leaf's back edge return to the latch. -/
theorem walkWhiteScanBack43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock52")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hlt13 : evalICmp .slt x (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (x + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 0)
    (hsc : ScanCount s "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ (scanCarryLatchOf { C with block := "LeafBlock43" })
      (leafBlock43OutAt (nodeBlock52OutAt s x) x) := by
  have h₁ := walkChain_extend_nodeBlock52 (C₀ := C₀) (s₀ := s₀) hchain hblock h36 hlt13
  have h36' : lookupName (nodeBlock52OutAt s x).env "%36" = some (.int 8 x) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) :: s.env) "%36" = some (.int 8 x)
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h36
  have hsc' : ScanCount (nodeBlock52OutAt s x) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.bind (d := "%Pivot53") (v := .int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))
      hsc (by decide) (by decide) (inner := C.inner)
  exact walkChain_extend_leafBlock43 (C₀ := C₀) (s₀ := s₀)
    (C := { C with block := "LeafBlock43" }) (inner := C.inner) h₁ rfl h36' hws rfl hsc'

/-- **The way back through `LeafBlock46`.**  The byte is at or above `13`, below `32`, and
not `13`: the second pivot, its first arm, and the leaf's back edge. -/
theorem walkWhiteScanBack46 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock52")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hge13 : evalICmp .slt x (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt x (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq x (BitVec.ofNat 8 13) = 0)
    (hsc : ScanCount s "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ (scanCarryLatchOf (scanCarryLeafBlock46 C))
      (scanLeafBlock46Out (scanNodeBlock50Out (scanNodeBlock50In s x) x) x) := by
  have h₁ := walkChain_extend_nodeBlock50 (C₀ := C₀) (s₀ := s₀) hchain hblock h36 hge13
  have h36₁ : lookupName (scanNodeBlock50In s x).env "%36" = some (.int 8 x) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) :: s.env) "%36" = some (.int 8 x)
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h36
  have hsc₁ : ScanCount (scanNodeBlock50In s x) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.bind (d := "%Pivot53") (v := .int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))
      hsc (by decide) (by decide) (inner := C.inner)
  have h₂ := walkChain_extend_nodeBlock50Out (C₀ := C₀) (s₀ := s₀)
    (C := scanCarryNodeBlock50 C) h₁ rfl h36₁ hlt32
  have h36₂ : lookupName (scanNodeBlock50Out (scanNodeBlock50In s x) x).env "%36"
      = some (.int 8 x) := by
    show lookupName
      (("%Pivot51", .int 1 (evalICmp .slt x (BitVec.ofNat 8 32))) ::
       ("%Pivot53", .int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) :: s.env) "%36"
      = some (.int 8 x)
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h36
  have hsc₂ : ScanCount (scanNodeBlock50Out (scanNodeBlock50In s x) x)
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.bind (d := "%Pivot51") (v := .int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))
      hsc₁ (by decide) (by decide) (inner := C.inner)
  have hsc₃ : ScanCount (scanLeafBlock46Out (scanNodeBlock50Out (scanNodeBlock50In s x) x) x)
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc₂
      [("%SwitchLeaf47", .int 1 (evalICmp .eq x (BitVec.ofNat 8 13)))]
      (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨by simp, by simp⟩)
  exact walkChain_extend_leafBlock46 (C₀ := C₀) (s₀ := s₀)
    (C := scanCarryLeafBlock46 C) h₂ rfl h36₂ hne13 hsc₃

/-- **The way back through `LeafBlock48`.**  The byte is at or above `32` and not `32`:
the second pivot, its second arm, and the leaf's back edge. -/
theorem walkWhiteScanBack48 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "NodeBlock52")
    {x : BitVec 8} (h36 : lookupName s.env "%36" = some (.int 8 x))
    (hge13 : evalICmp .slt x (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt x (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq x (BitVec.ofNat 8 32) = 0)
    (hsc : ScanCount s "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀ (scanCarryLatchOf (scanCarryLeafBlock48 C))
      (scanLeafBlock48Out (scanNodeBlock48Out (scanNodeBlock50In s x) x) x) := by
  have h₁ := walkChain_extend_nodeBlock50 (C₀ := C₀) (s₀ := s₀) hchain hblock h36 hge13
  have h36₁ : lookupName (scanNodeBlock50In s x).env "%36" = some (.int 8 x) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) :: s.env) "%36" = some (.int 8 x)
    rw [lookupName_cons_ne _ _ (by decide)]
    exact h36
  have hsc₁ : ScanCount (scanNodeBlock50In s x) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.bind (d := "%Pivot53") (v := .int 1 (evalICmp .slt x (BitVec.ofNat 8 13)))
      hsc (by decide) (by decide) (inner := C.inner)
  have h₂ := walkChain_extend_nodeBlock48 (C₀ := C₀) (s₀ := s₀)
    (C := scanCarryNodeBlock50 C) h₁ rfl h36₁ hge32
  have h36₂ : lookupName (scanNodeBlock48Out (scanNodeBlock50In s x) x).env "%36"
      = some (.int 8 x) := by
    show lookupName
      (("%Pivot51", .int 1 (evalICmp .slt x (BitVec.ofNat 8 32))) ::
       ("%Pivot53", .int 1 (evalICmp .slt x (BitVec.ofNat 8 13))) :: s.env) "%36"
      = some (.int 8 x)
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h36
  have hsc₂ : ScanCount (scanNodeBlock48Out (scanNodeBlock50In s x) x)
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.bind (d := "%Pivot51") (v := .int 1 (evalICmp .slt x (BitVec.ofNat 8 32)))
      hsc₁ (by decide) (by decide) (inner := C.inner)
  have hsc₃ : ScanCount (scanLeafBlock48Out (scanNodeBlock48Out (scanNodeBlock50In s x) x) x)
      "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc₂
      [("%SwitchLeaf49", .int 1 (evalICmp .eq x (BitVec.ofNat 8 32)))]
      (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst hc
        exact ⟨by simp, by simp⟩)
  exact walkChain_extend_leafBlock48 (C₀ := C₀) (s₀ := s₀)
    (C := scanCarryLeafBlock48 C) h₂ rfl h36₂ hne32 hsc₃

/-! ### The visit, composed

The induction's `step` is the latch's own step, and the way back is a chain per byte
class.  A **visit** is the landing block's step and one of those chains: the landing
block's write is the byte the class splits on, so the two halves agree by construction. -/

/-- **One visit, through `LeafBlock43`.**  From the scan's landing block, short of the
bound and with the byte below `13`, the run returns to the latch. -/
theorem walkWhiteScanVisit43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀
      (scanCarryLatchOf { { C with block := "NodeBlock52" } with block := "LeafBlock43" })
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
  have h₁ := walkChain_extend_landRhsI (C₀ := C₀) (s₀ := s₀) hchain hblock hpre hin hv hpos
    hqn halen hevlen
  have h36 : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  exact walkWhiteScanBack43 (C₀ := C₀) (s₀ := s₀) (C := { C with block := "NodeBlock52" })
    h₁ rfl h36 hlt13 hws hsc

/-- **One visit, through `LeafBlock46`.**  The byte is at or above `13`, below `32`, and
not `13`. -/
theorem walkWhiteScanVisit46 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀
      (scanCarryLatchOf (scanCarryLeafBlock46 { C with block := "NodeBlock52" }))
      (scanLeafBlock46Out
        (scanNodeBlock50Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
  have h₁ := walkChain_extend_landRhsI (C₀ := C₀) (s₀ := s₀) hchain hblock hpre hin hv hpos
    hqn halen hevlen
  have h36 : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  exact walkWhiteScanBack46 (C₀ := C₀) (s₀ := s₀) (C := { C with block := "NodeBlock52" })
    h₁ rfl h36 hge13 hlt32 hne13 hsc

/-- **One visit, through `LeafBlock48`.**  The byte is at or above `32` and not `32`. -/
theorem walkWhiteScanVisit48 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    WalkChain calls G C₀ s₀
      (scanCarryLatchOf (scanCarryLeafBlock48 { C with block := "NodeBlock52" }))
      (scanLeafBlock48Out
        (scanNodeBlock48Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
  have h₁ := walkChain_extend_landRhsI (C₀ := C₀) (s₀ := s₀) hchain hblock hpre hin hv hpos
    hqn halen hevlen
  have h36 : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  exact walkWhiteScanBack48 (C₀ := C₀) (s₀ := s₀) (C := { C with block := "NodeBlock52" })
    h₁ rfl h36 hge13 hge32 hne32 hsc

/-! ### A visit as a segment

The closure of an induction is a recursion on the counter's remaining distance, and its
unit is a *segment*: `WalkSegment.of_chain` reads a chain as one, so each visit above is
a segment at its own count.  What a *price* needs beyond this is the count itself — a
`WalkChain` records none (it is a `Prop`, so a length is not definable) — which is the
`Seg` relation the next step introduces: a chain together with the number of links it is
made of, from which the price `n ≤ stage2ByteAllowance` follows link by link. -/

/-- **The visit through `LeafBlock43`, as a segment.** -/
theorem walkWhiteScanVisitSeg43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ j, WalkSegment calls G C₀ s₀
      (scanCarryLatchOf { { C with block := "NodeBlock52" } with block := "LeafBlock43" })
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) j :=
  WalkSegment.of_chain (walkWhiteScanVisit43 hchain hblock hpre hin hv hpos hqn halen hevlen
    hlt13 hws hsc)

/-- **The visit through `LeafBlock46`, as a segment.** -/
theorem walkWhiteScanVisitSeg46 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hlt32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 1)
    (hne13 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ j, WalkSegment calls G C₀ s₀
      (scanCarryLatchOf (scanCarryLeafBlock46 { C with block := "NodeBlock52" }))
      (scanLeafBlock46Out
        (scanNodeBlock50Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) j :=
  WalkSegment.of_chain (walkWhiteScanVisit46 hchain hblock hpre hin hv hpos hqn halen hevlen
    hge13 hlt32 hne13 hsc)

/-- **The visit through `LeafBlock48`, as a segment.** -/
theorem walkWhiteScanVisitSeg48 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C₀ : WalkCarry G} {s₀ : State} {C : WalkCarry G} {s : State}
    (hchain : WalkChain calls G C₀ s₀ C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hge13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 0)
    (hge32 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 0)
    (hne32 : evalICmp .eq (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 32) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ j, WalkSegment calls G C₀ s₀
      (scanCarryLatchOf (scanCarryLeafBlock48 { C with block := "NodeBlock52" }))
      (scanLeafBlock48Out
        (scanNodeBlock48Out
          (scanNodeBlock50In (landRhsIOutAt G s e (scanB G e))
            (BitVec.ofNat 8 (scanB G e).toNat))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) j :=
  WalkSegment.of_chain (walkWhiteScanVisit48 hchain hblock hpre hin hv hpos hqn halen hevlen
    hge13 hge32 hne32 hsc)

/-! ### The counted chain

`WalkChain` is a `Prop`, so no length is definable from it — a large elimination — and
`WalkChain.steps` is existential for that reason.  A price therefore cannot be read off a
chain however many links it visibly has, which is exactly why `WalkSegment` carries an
index.  This relation records the count beside the chain: the same constructors, with the
number of links an index, so a chain's price is a `Nat` the caller can compare.

It is the trace vocabulary's third form — `WalkChain` for chaining, `WalkSegment` for the
run, and `Seg` for reading one out of the other at a known count. -/
inductive Seg (calls : Calls) {m0 : Mem} (G : WalkGeom m0) :
    WalkCarry G → State → WalkCarry G → State → Nat → Prop
  | nil {C : WalkCarry G} {s : State} (h : WalkInv G C s) :
      Seg calls G C s C s 0
  | tail {C C' C'' : WalkCarry G} {s s' s'' : State} {n : Nat}
      (hl : WalkLink calls G C s C' s')
      (ht : Seg calls G C' s' C'' s'' n) :
      Seg calls G C s C'' s'' (n + 1)

/-- **A counted chain is a chain.** -/
theorem Seg.toChain {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} {n : Nat} (h : Seg calls G C s C' s' n) :
    WalkChain calls G C s C' s' := by
  induction h with
  | nil h => exact WalkChain.nil h
  | tail hl _ ih => exact WalkChain.tail hl ih

/-- **A counted chain is a segment at its own count** — the price, read off the count. -/
theorem Seg.measure {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} {n : Nat} (h : Seg calls G C s C' s' n) :
    WalkSegment calls G C s C' s' n := by
  induction h with
  | nil h =>
      refine ⟨fun k => ?_, h⟩
      simp only [Nat.zero_add]
  | @tail C C' C'' s s' s'' n hl _ ih =>
      have := WalkSegment.of_link hl |>.trans ih
      simpa only [Nat.one_add] using this

/-- **Every chain is counted.** -/
theorem WalkChain.seg {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (h : WalkChain calls G C s C' s') :
    ∃ n, Seg calls G C s C' s' n := by
  induction h with
  | nil h => exact ⟨0, Seg.nil h⟩
  | tail hl _ ih => obtain ⟨n, h'⟩ := ih; exact ⟨n + 1, Seg.tail hl h'⟩

/-- **A single link's price.**  One link is one fuel unit, inside the byte allowance. -/
theorem link_price {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C C' : WalkCarry G} {s s' : State} (hl : WalkLink calls G C s C' s') :
    ∃ (h : Seg calls G C s C' s' 1), 1 ≤ stage2ByteAllowance :=
  ⟨Seg.tail hl (Seg.nil hl.inv'), by decide⟩

/-! ### The counted visit

The three links of a visit, composed at the level `Seg` counts: the landing block's, the
pivot's and the leaf's.  Each is taken from its own `_at` helper at the state the previous
one leaves, so the count is the visible one — three — and `Seg.measure` turns it into a
segment at three steps.  With `scanLatch_visit`'s one-step segment the round is four
steps against the byte allowance. -/

/-- **The visit through `LeafBlock43`, counted: three links.** -/
theorem walkWhiteScanVisitSeg3_43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hblock : C.block = "land.rhs.i")
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand s op = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    (hsc : ScanCount (landRhsIOutAt G s e (scanB G e)) "%ee.0.i238" "%cond350.i" C.inner) :
    Seg calls G C s
      (scanCarryLatchOf { { C with block := "NodeBlock52" } with block := "LeafBlock43" })
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) 3 := by
  -- the landing block's link
  have hread : readBytes s.mem (G.b + (e.signExtend 64).toNat) 1
      = some [G.bs.getD (e.signExtend 64).toNat 0] :=
    walkDoc_byte G C s hInv halen hevlen hqn
  obtain ⟨s₁, hl₁, hs₁⟩ :=
    WalkLink.land_rhs_i_at G C s hInv hblock hpre hin hv hpos hread
  have hstep₁ : s₁ = landRhsIOutAt G s e (scanB G e) := by
    rw [hs₁]
    rfl
  rw [hstep₁] at hl₁
  -- the pivot's link
  have h36₁ : lookupName (landRhsIOutAt G s e (scanB G e)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName (cells
      [("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)),
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat))]
      ((s.bindAll [("%ee.0.i238", .int 64 e)]).env)) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    simp only [cells]
    rw [lookupName_cons_self]
  have h1 : evalOperand (landRhsIOutAt G s e (scanB G e)) (.reg "%36")
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := h36₁
  obtain ⟨s₂, hl₂, hs₂⟩ :=
    WalkLink.NodeBlock52_at G { C with block := "NodeBlock52" } (landRhsIOutAt G s e (scanB G e))
      hl₁.inv' rfl h1
  have hstep₂ : s₂ = nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₂]
    simp only [nodeBlock52OutAt, if_pos hlt13]
  rw [hstep₂] at hl₂
  rw [show (if evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1
      then "LeafBlock43" else "NodeBlock50") = "LeafBlock43" from if_pos hlt13] at hl₂
  -- the leaf's link
  have h36₂ : lookupName (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)).env "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat)) := by
    show lookupName
      (("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
       ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
       ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
       (s.bindAll [("%ee.0.i238", .int 64 e)]).env) "%36"
      = some (.int 8 (BitVec.ofNat 8 (scanB G e).toNat))
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hsc₃ : ScanCount
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) "%ee.0.i238" "%cond350.i" C.inner :=
    ScanCount.stateAt_cells (inner := C.inner) hsc
      [("%SwitchLeaf34", .int 1 (evalICmp .ule
          (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))),
       ("%.off", .int 8 (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247))]
      (by
        intro c hc
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl <;> exact ⟨by simp, by simp⟩)
  have hloc : WalkLocal { { C with block := "NodeBlock52" } with block := "while.body370.i" }
      (leafBlock43OutAt
        (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) := by
    rw [WalkLocal.whitespace rfl]
    exact hsc₃
  obtain ⟨s₃, hl₃, hs₃⟩ :=
    WalkLink.LeafBlock43_at G _
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      hl₂.inv' (by simp) h36₂ hloc
  have hres : (if evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 1 then "if.end372.i" else "while.body370.i") = "while.body370.i" :=
    if_neg (by rw [hws]; decide)
  have hstep₃ : s₃ = leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G s e (scanB G e)) (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat) := by
    rw [hs₃]
    simp only [leafBlock43OutAt, hres]
  rw [hstep₃] at hl₃
  rw [hres] at hl₃
  exact Seg.tail hl₁ (Seg.tail hl₂ (Seg.tail hl₃ (Seg.nil hl₃.inv')))

/-- **A round of the whitespace scan, counted: four steps.**  The latch's link and the
visit's three, `trans` at `1 + 3`, inside the byte allowance.  This is the unit the
dispatch's credit consumes: `c - i` rounds are `(c - i) · 4` steps against
`(c - i) · 8`. -/
theorem walkWhiteScanRound43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = "while.body370.i")
    {i c : Nat} (hi : lookupName s.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hlt : i + 1 < c)
    {op : Operand} {p : String} {e : BitVec 64}
    (hpre : (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").pre = some p)
    (hin : phiIncoming p [("while.body370.i", (Operand.reg "%inc371.i")),
      ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some op)
    (hv : evalOperand (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") op
      = some (.int 64 e))
    (hpos : (e.signExtend 64).toNat < 2 ^ 63)
    (hqn : (e.signExtend 64).toNat < G.n)
    (halen : C.alen ≤ G.ndst0 + G.n + stage2ArenaReserve)
    (hevlen : C.evlen ≤ G.evcap)
    (hlt13 : evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat) (BitVec.ofNat 8 13) = 1)
    (hws : evalICmp .ule (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)
      (BitVec.ofNat 8 1) = 0)
    (hsc : ScanCount
      (landRhsIOutAt G (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") e
        (scanB G e))
      "%ee.0.i238" "%cond350.i" C.inner) :
    ∃ (C' : WalkCarry G) (s' : State), WalkSegment calls G C s C' s' 4 ∧
      WalkInv G C' s' ∧ C'.block = "while.body370.i" ∧
      lookupName s'.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      4 ≤ stage2ByteAllowance := by
  -- the latch's own count, and the landing block's local fact it establishes
  have hSC : ScanCount s "%ee.0.i238" "%cond350.i" C.inner := by
    have h := hInv.blockLocal
    rwa [WalkLocal.whitespace hblock] at h
  have hsub : c - i ≤ C.inner := ScanCount.same hSC hi hc hcw (by omega)
  have hinc₁ : lookupName
      (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").env "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
    show lookupName (cells
      [("%exitcond.not", .int 1 (evalICmp .eq (BitVec.ofNat 64 (i + 1))
          (BitVec.ofNat 64 c))),
       ("%inc371.i", .int 64 (BitVec.ofNat 64 (i + 1)))] s.env) "%inc371.i" =
      some (.int 64 (BitVec.ofNat 64 (i + 1)))
    simp only [cells]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
  have hcond₁ : lookupName
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
      by show some s.pc = some "while.body370.i"; rw [hInv.pc_eq, hblock],
      hinc₁, hcond₁⟩
  obtain ⟨s₁, hl₁, hs₁, -, -⟩ :=
    scanLatch_link (G := G) (C := C) (s := s) hInv hblock
      (src := "while.body370.i") (inc := "%inc371.i") (phi := "%ee.0.i238")
      (test := "%exitcond.not") (cond := "%cond350.i") (exit := "if.end372.i")
      (land := "land.rhs.i")
      (B := scanBlock "while.body370.i" "%inc371.i" "%ee.0.i238" "%exitcond.not"
        "%cond350.i" "if.end372.i" "land.rhs.i")
      scanWhitespace_find rfl rfl (by decide) (by decide) (by decide)
      (by unfold walkCarried scanBlock; decide) hi hc hcw hlt
      (by simp [WalkLocal]) hland
  -- the counted visit, at the state the latch leaves
  have hseg₁ : WalkSegment calls G C s { C with block := "land.rhs.i" }
      (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") 1 := by
    rw [hs₁] at hl₁
    exact Seg.measure (Seg.tail hl₁ (Seg.nil hl₁.inv'))
  have hinv₁ : WalkInv G { C with block := "land.rhs.i" }
      (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") := by
    rw [← hs₁]
    exact hl₁.inv'
  have hseg₂ : WalkSegment calls G { C with block := "land.rhs.i" }
      (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i")
      (scanCarryLatchOf { { C with block := "land.rhs.i" } with block := "LeafBlock43" })
      (leafBlock43OutAt
        (nodeBlock52OutAt
          (landRhsIOutAt G (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") e
        (scanB G e))
          (BitVec.ofNat 8 (scanB G e).toNat))
        (BitVec.ofNat 8 (scanB G e).toNat)) 3 :=
    Seg.measure (walkWhiteScanVisitSeg3_43
      (s := scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i")
      hinv₁ rfl hpre hin hv hpos hqn halen hevlen hlt13 hws hsc)
  -- the landing block's `phi` is the latch's increment, so the counter it writes is `i + 1`
  have hp : p = "while.body370.i" := by
    have h : some p = some s.pc := by
      rw [← hpre]
    injection h with hp'
    rw [hp', hInv.pc_eq, hblock]
  have hphi : phiIncoming "while.body370.i"
      [("while.body370.i", (Operand.reg "%inc371.i")),
       ("land.rhs.i.preheader", (Operand.reg "%idxprom.i"))] = some (.reg "%inc371.i") := by
    simp [phiIncoming]
  have hop : op = .reg "%inc371.i" := by
    rw [hp] at hin
    rw [hphi] at hin
    exact (Option.some.inj hin).symm
  have heq : e = BitVec.ofNat 64 (i + 1) := by
    have h : lookupName (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").env
        "%inc371.i" = some (.int 64 e) := by
      rw [hop] at hv
      exact hv
    rw [hinc₁] at h
    exact heq_iff_eq.mp (Value.int.inj (Option.some.inj h)).2.symm
  -- the target's environment, named: what the visit's three blocks install
  have henv : (leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat))
      (BitVec.ofNat 8 (scanB G e).toNat)).env =
      ("%SwitchLeaf45", .int 1 (evalICmp .ule
          (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
      ("%.off44", .int 8 (BitVec.ofNat 8 (scanB G e).toNat + BitVec.ofNat 8 247)) ::
      ("%Pivot53", .int 1 (evalICmp .slt (BitVec.ofNat 8 (scanB G e).toNat)
        (BitVec.ofNat 8 13))) ::
      ("%36", .int 8 (BitVec.ofNat 8 (scanB G e).toNat)) ::
      ("%arrayidx367.i", .ptr (G.b + (e.signExtend 64).toNat)) ::
      ("%ee.0.i238", .int 64 e) ::
      (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i").env := by
    simp only [leafBlock43OutAt, nodeBlock52OutAt, landRhsIOutAt, stateAt, State.bind,
      State.bindAll, cells]
  have hee : lookupName (leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)).env
      "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
    rw [henv,
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
    rw [heq]
  have hcond₂ : lookupName (leafBlock43OutAt
      (nodeBlock52OutAt (landRhsIOutAt G
        (scanLatchOut s "%inc371.i" "%exitcond.not" i c "land.rhs.i") e (scanB G e))
        (BitVec.ofNat 8 (scanB G e).toNat)) (BitVec.ofNat 8 (scanB G e).toNat)).env
      "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
    rw [henv,
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hcond₁
  exact ⟨_, _, hseg₁.trans hseg₂, hseg₂.inv', rfl, hee, hcond₂,
    by simp [stage2ByteAllowance]⟩

/-! ### The counted traversal

A round is four steps and leaves the scan at its latch with the counter advanced, so the
positions still to visit are `c - 1 - i` and the traversal is that many rounds: `4` steps
each, inside `8` each.  The round's own hypotheses are about the byte at the counter and so
differ at every step; what the recursion consumes is only that a round exists at each
visiting counter, advances it by one, and leaves the invariant and the bound. -/

/-- **The whitespace scan's counted traversal.**  `4 · (c - 1 - i)` steps, inside
`8 · (c - 1 - i)` — the unit the dispatch's credit consumes. -/
theorem walkScanRounds43 {calls : Calls} {m0 : Mem} {G : WalkGeom m0} {i c : Nat}
    (hround : ∀ (C : WalkCarry G) (s : State) (p : Nat), WalkInv G C s →
      C.block = "while.body370.i" →
      lookupName s.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 p)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      c < 2 ^ 64 → p + 1 < c →
      ∃ (C' : WalkCarry G) (s' : State), WalkSegment calls G C s C' s' 4 ∧
        WalkInv G C' s' ∧ C'.block = "while.body370.i" ∧
        lookupName s'.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 (p + 1))) ∧
        lookupName s'.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = "while.body370.i")
    (hi : lookupName s.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 i)))
    (hc : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hcw : c < 2 ^ 64) (hic : i < c) :
    ∃ (C' : WalkCarry G) (s' : State),
      WalkSegment calls G C s C' s' (4 * (c - 1 - i)) ∧ WalkInv G C' s' ∧
      C'.block = "while.body370.i" ∧
      lookupName s'.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 (c - 1))) ∧
      4 * (c - 1 - i) ≤ 8 * (c - 1 - i) := by
  have go : ∀ r, ∀ (i : Nat) (C : WalkCarry G) (s : State), c - 1 - i = r →
      WalkInv G C s → C.block = "while.body370.i" →
      lookupName s.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)) →
      i < c →
      ∃ (C' : WalkCarry G) (s' : State),
        WalkSegment calls G C s C' s' (4 * r) ∧ WalkInv G C' s' ∧
        C'.block = "while.body370.i" ∧
        lookupName s'.env "%ee.0.i238" = some (.int 64 (BitVec.ofNat 64 (c - 1))) := by
    intro r
    induction r with
    | zero =>
        intro i C s _ hInv hblock hi _ hic
        have hie : i = c - 1 := by omega
        refine ⟨C, s, ?_, hInv, hblock, ?_⟩
        · refine ⟨fun k => ?_, hInv⟩
          rw [Nat.mul_zero, Nat.zero_add]
        · rw [← hie]
          exact hi
    | succ n ih =>
        intro i C s hr hInv hblock hi hc' hic
        have hlt : i + 1 < c := by omega
        obtain ⟨C₁, s₁, hseg, hinv, hb₁, hi₁, hc₁⟩ := hround C s i hInv hblock hi hc' hcw hlt
        obtain ⟨C₂, s₂, hseg₂, hinv₂, hb₂, hi₂⟩ :=
          ih (i + 1) C₁ s₁ (by omega) hinv hb₁ hi₁ hc₁ (by omega)
        refine ⟨C₂, s₂, ?_, hinv₂, hb₂, hi₂⟩
        have := hseg.trans hseg₂
        simpa only [Nat.mul_succ, Nat.add_comm] using this
  obtain ⟨C', s', hseg, hinv, hb, hi'⟩ := go (c - 1 - i) i C s rfl hInv hblock hi hc hic
  exact ⟨C', s', hseg, hinv, hb, hi', by omega⟩

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
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanBack43
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanBack46
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanBack48
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisit43
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisit46
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisit48
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisitSeg43
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisitSeg46
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisitSeg48
#print axioms LeanLLVM.Refinement.WalkScope.Seg.toChain
#print axioms LeanLLVM.Refinement.WalkScope.Seg.measure
#print axioms LeanLLVM.Refinement.WalkScope.WalkChain.seg
#print axioms LeanLLVM.Refinement.WalkScope.link_price
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanVisitSeg3_43
#print axioms LeanLLVM.Refinement.WalkScope.scanLatch_link
#print axioms LeanLLVM.Refinement.WalkScope.walkWhiteScanRound43
#print axioms LeanLLVM.Refinement.WalkScope.walkScanRounds43
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionLiteral_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionWhitespace_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionString_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionEscape_holds
#print axioms LeanLLVM.Refinement.WalkScope.walkInductionExtraToken_holds

end WalkScope

end LeanLLVM.Refinement
