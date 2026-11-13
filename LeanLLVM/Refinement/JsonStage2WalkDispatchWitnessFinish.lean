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

**What the rest of the path owes, block by block.**  The pattern is the layer's where a
fact's producer is elsewhere (`walkIfThen_step`): the block's `denoteCode` is the caller's
hypothesis and the step names the successor.  Which core a block needs depends on whether
it touches memory, and on whether its call's result is a contract:

| block | core | the hypothesis it owes |
|---|---|---|
| `cond.true345.i` | `pureCore` (no store) | the entry stream's lane read at `%inc.i` — `%5 + %inc.i`'s 32-bit word, which the geometry's `entries` gives at the index |
| `if.end372.i` | store variant (`refusalStore`'s shape) | `denoteCode` **and** the frame for its store through `%end.i`; its `phi` over eight predecessors is `cleanup478_denote`'s sibling |
| `if.then413.i` | store variant + call | `denoteCode`, which consumes `s2_value_pos`'s contract at this call site, plus the frame for the `%kind404.i` store |
| `if.then425.i` | call consumer | **`od_scalar_value`'s contract at `(%c.i, %t352.i, %z)`**, then the frame for its writes |
| `if.then447.i` | call consumer | **`s2_after_value`'s contract** at the two stack pointers, then the scan's test |
| `if.end473.i` | `pureCore` (no store) | only `denoteCode`: `llvm.lifetime.end.p0` writes nothing, so `hmem` is `rfl` |
| `cleanup478.i` | `pureCore` (no store) | the two `phi`s' selection at `pre = some "if.end473.i"` — `cleanup478_denote` is exactly that, and `%cmp.i`'s bit picks `while.body.i` or `if.then485.i` |

Three of the seven therefore fit `pureCore`'s no-store shape and are one `denoteCode` away;
two need the store variant of the same pattern, where the frame is the extra obligation as it
was for `if.end59.i`'s nesting check; and two are *call* consumers, whose step is honest only
with the helper's contract named as its hypothesis — `s2_value_pos`, `od_scalar_value` and
`s2_after_value`, in the handoff's own names.

That is why this file is sized rather than finished: the refusal side of `hlast` is closed by
the witness modules, and `finish`'s remaining work is these seven blocks, four of which are
contract consumers rather than block arithmetic.-/

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
