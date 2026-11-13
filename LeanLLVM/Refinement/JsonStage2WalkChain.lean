/-
The walk's dispatch chain: the finite pieces of a revolution.

`WalkDispatch`'s interior is not one path.  A revolution is a finite path from the
loop head (`NodeBlock21`) to a scan's latch, one induction per scan over its counter,
and the token's post-scan blocks to the merge; `WalkSegment.trans` composes the three
and `WalkChain.append` the finite ones.  This module is the finite layer: `WalkChain`s
whose every carry and state is the one the step instances name
(`JsonStage2WalkSteps`), so a chain is `WalkChain.tail` at those terms and nothing is
re-derived.

A token class fixes the comparison bits, and the bits are what resolve each step's
`if`-shaped `pc`: the instances state their targets with the arm as an `if` on the
instruction's bit, and a class is the case that takes one arm at each branch.  So the
chains are stated per class, and the class is the hypothesis (`hlt`, `hge`, …) rather
than a branch inside the chain.

**The target terms are part of the work.**  Each instance's state is a literal nest
(`{ (s.bind a v).bind b w with … }`), so a chain's target is that nest applied k
times and its statement grows with the path — at twenty-two blocks it is unreadable,
and its `simp` goals are about the nest rather than the program.  A long path is
therefore written the way the shapes already are: each intermediate state takes a
`def` (the role `walkMarkerEnv` plays for a block), the chain states those defs, and
the instance lemmas bridge one def to the next.  The two lemmas below are the same
chain at both lengths — one link with the literal form, two links with the recursion
made explicit — which is where the literal form stops paying.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly
import LeanLLVM.Refinement.JsonStage2WalkSteps

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The chain, from the head

The dispatch's interior is not one path: a revolution is a finite path from the head
to a scan's latch, one induction per scan over its counter, and the token's
post-scan blocks to the merge.  These are the finite pieces, as `WalkChain`s, with
every carry and state the instances' own conclusions name — so a chain is
`WalkChain.tail` at those terms and nothing is re-derived.

A token class fixes the bits, and the bits are what resolve each step's `if`-shaped
`pc`.  The first piece is the head's opening comparison at the class whose first byte
is below `91`: `%Pivot22 = %8 < 91` is one, so the edge is `NodeBlock5` and the target
is the instance's state with that arm taken. -/
theorem walkHeadChain_lt91 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt : evalICmp .slt x (BitVec.ofNat 8 91) = 1) :
    ∃ (C₁ : WalkCarry G) (s₁ : State), WalkChain calls G C s C₁ s₁ ∧
      C₁ = { C with block := "NodeBlock5" } ∧
      s₁ = { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
        pc := "NodeBlock5", pre := some s.pc } := by
  obtain ⟨s₁, hlink, hs₁⟩ := WalkLink.NodeBlock21_at G C s hInv hhead h8
  refine ⟨_, s₁, WalkChain.tail hlink (WalkChain.nil hlink.inv'), ?_, ?_⟩
  · simp [hlt]
  · exact hs₁.trans (by simp [hlt])


/-- **The head's first two links.**  The switch's opening pivots on the first byte:
`%8 < 91` takes `NodeBlock5`, and there `%8 < 44` takes `LeafBlock`.  Two links, the
second at the state the first names — which is the whole threading question, and its
answer is the instances' own terms: the second reaches `%8` through the cell the first
bound, so its operand fact is the first's peeled past `%Pivot22`. -/
theorem walkHeadChain_lt91_lt44 {calls : Calls} {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s) (hhead : C.block = walkLoopHead)
    {x : BitVec 8} (h8 : evalOperand s (.reg "%8") = some (.int 8 x))
    (hlt91 : evalICmp .slt x (BitVec.ofNat 8 91) = 1)
    (hlt44 : evalICmp .slt x (BitVec.ofNat 8 44) = 1) :
    ∃ (C₂ : WalkCarry G) (s₂ : State), WalkChain calls G C s C₂ s₂ ∧
      C₂ = { C with block := "LeafBlock" } ∧
      s₂ = { ({ (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
          pc := "NodeBlock5", pre := some s.pc }).bind
          "%Pivot6" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 44))) with
        pc := "LeafBlock"
        pre := some "NodeBlock5" } := by
  obtain ⟨C₁, s₁, hchain₁, rfl, rfl⟩ := walkHeadChain_lt91 hInv hhead h8 hlt91
  have h8' : evalOperand
      { (s.bind "%Pivot22" (.int 1 (evalICmp .slt x (BitVec.ofNat 8 91)))) with
        pc := "NodeBlock5", pre := some s.pc } (.reg "%8") = some (.int 8 x) := by
    simpa only [evalOperand, State.bind,
      lookupName_cons_ne (k := "%Pivot22") (n := "%8") _ _ (by decide)] using h8
  obtain ⟨s₂, hlink₂, hs₂⟩ :=
    WalkLink.NodeBlock5_at G _ _ (WalkChain.inv_last hchain₁) rfl h8'
  refine ⟨_, s₂, hchain₁.append (WalkChain.tail hlink₂ (WalkChain.nil hlink₂.inv')), ?_, ?_⟩
  · simp [hlt44]
  · exact hs₂.trans (by simp [hlt44])

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91
#print axioms LeanLLVM.Refinement.WalkScope.walkHeadChain_lt91_lt44

end WalkScope

end LeanLLVM.Refinement
