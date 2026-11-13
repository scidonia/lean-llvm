import LeanLLVM.Refinement.JsonStage2WalkDispatchWitnessState

/-! # The `finish` alternative

`WalkDispatchThree.ofContinueAndLast`'s other terminal outcome: the dispatch consumed the
last entry and the merge at `cleanup478.i` selects the *terminal* index, `%k.2.i = %nep`.
The dispatch note's longest path is the twenty-two blocks from `while.body.i` to the merge,
and the refusal module's three instruments carry over unchanged — a named prefix per state,
peels stated in the form the elaborator reduces (`lookupName`, closed by `rfl`), and the
trace split into segments composed by `WalkSegment.trans`.

**What this file has so far.**  The path's empty-body blocks, whose step is one `br`: the
elaborator's `walkBrStep` gives the successor outright, and naming it costs only
`Ctrl.jump`'s injectivity.

**What the rest of the path owes, block by block.**  Eight of the twenty-two blocks have no
named step yet, and they are not alike:

* `cond.true345.i` — `gep %5, %inc.i`, load, `zext`, `br cond.end349.i`: a load-and-`zext`
  step, the `WalkLink.cond_true345_i` sharpened the way `walkIfEnd74_at` was.
* `if.end372.i` — a `phi` (eight predecessors), a store through `%end.i`, and the three
  comparisons that choose which of the number's helpers runs.  Its `_denote` is the
  `phi`-plus-`store` shape, so the step needs `walkPhiStore...`'s pattern.
* `if.then413.i` — `phi` `%.sink372`, a store through `%kind404.i`, a call to
  `s2_value_pos`, and the test on its result: the *call* is the premise, and its contract is
  the helper's.
* `if.then425.i` — a call to `od_scalar_value` and the test on its result.  This is the
  number conversion's own entry, so its step is a helper-contract consumer.
* `if.then447.i` — `s2_after_value`, then the scan's test `%ee.1.i ult %cond350.i`.
* `if.end473.i` — `llvm.lifetime.end.p0` on `%t352.i`, then `br cleanup478.i`.
* `cleanup478.i` itself — the two `phi`s `%sp.i.1` and `%k.2.i` over ten predecessors, whose
  incoming operands are what `WalkDispatchOutcome.finish`'s `kOp`/`spOp` read.  Its
  `cleanup478_denote` exists; the step's work is the `phi` selection at `if.end473.i`.

Each of the five that carries a helper call sits on a contract rather than on a block: the
number path is where the layer's `NumFast` and `s2_value_pos`/`od_scalar_value` obligations
are consumed, and no step for them can be written before those contracts are stated at the
call site.  That is why this file is sized rather than finished: the refusal side of
`hlast` is closed by the witness modules, and `finish`'s remaining work is the number path's
five contract blocks plus `cleanup478.i`'s two `phi`s. -/

namespace LeanLLVM.Refinement
namespace WalkScope

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

set_option autoImplicit false

/-- **`if.else387.i`'s target, named.**  An empty body and one `br`: the successor is the
state itself at `NodeBlock62`. -/
theorem walkIfElse387_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.else387.i") :
    ∃ (s' : State), WalkLink calls G C s { C with block := "NodeBlock62" } s' ∧
      s' = { s with pc := "NodeBlock62", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_else387_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_else387_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_else387_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_else387_i)
    (dest := "NodeBlock62") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.then403.i`'s target, named.**  An empty body and one `br`, at `if.then413.i`. -/
theorem walkIfThen403_at {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then403.i") :
    ∃ (s' : State), WalkLink calls G C s { C with block := "if.then413.i" } s' ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } := by
  obtain ⟨s', hl⟩ := WalkLink.if_then403_i (calls := calls) G C s hInv hblock
  refine ⟨s', hl, ?_⟩
  have hfind : stage2Body.findBlock s.pc = some walkIf_then403_i := by
    rw [hInv.pc_eq, hblock]; exact walkIf_then403_i_find
  have hstep := walkBrStep (calls := calls) (s := s) (b := walkIf_then403_i)
    (dest := "if.then413.i") hfind rfl rfl
  exact Ctrl.jump.inj ((WalkLink.step hl).symm.trans hstep)

/-- **`if.then403.i`'s step as a segment.**  One link is `WalkSegment.of_link`'s count, so
the path's empty blocks enter the algebra with no extra machinery: the segment carries the
successor's carry, state and invariant, which is what a composition consumes. -/
theorem walkIfThen403_seg {calls : Calls} {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "if.then403.i") :
    ∃ (C' : WalkCarry G) (s' : State), WalkSegment calls G C s C' s' 1 ∧
      C' = { C with block := "if.then413.i" } ∧
      s' = { s with pc := "if.then413.i", pre := some s.pc } ∧
      WalkInv G C' s' := by
  obtain ⟨s', hl, hs'⟩ := walkIfThen403_at (calls := calls) G C s hInv hblock
  exact ⟨_, s', WalkSegment.of_link hl, rfl, hs', hl.inv'⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkIfElse387_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen403_at
#print axioms LeanLLVM.Refinement.WalkScope.walkIfThen403_seg
