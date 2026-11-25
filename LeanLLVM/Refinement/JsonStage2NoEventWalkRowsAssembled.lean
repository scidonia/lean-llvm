/-
The no-event walk's rows, assembled from the classes' two-armed producers.

`JsonStage2NoEventWalkRowsAssemble` states the consumer's contract,
`Stage2NoEventWalkRows`, and reaches it from one producer per head class
(`stage2NoEventWalkRows_of_ready`).  This module supplies the bracket and brace
producers from `JsonStage2NoEventWalkRowsReady`'s two-armed forms and states the
result at the record's own selection and fuel.

**What a caller supplies.**  The four producers, each at a premise the walk's
own routes select:

* the string class (`hstring`) and the value class (`hvalue`), unchanged from
  the assembly's contract — the value class is the assembly's own conditional
  parameter, as it has no producer at its whitespace/remainder arm;
* `hbracketPair` / `hbracketTerm` and `hbracePair` / `hbraceTerm`, the live pair
  arm's guard and the terminal arm's row (`…Ready_of_arms`).

Each is satisfiable and none quantifies over every head: the pair premises name
a head on the push branch (`sp ≠ 0`, `k + 3 < K.nep`) and are inhabited by a
`[…]`/`{…}` head at positive depth whose next entry is the closer; the terminal
premises name `sp = 0` or `k + 3 ≥ K.nep` and are inhabited at a seed head (whose
depth is zero) whose document opens with `[`/`{`, through
`stage2NoEventWalkBracketZeroRow`/`…BraceZeroRow` (the caller's
`hreportAcc`/`hboundAcc`/`hreportRef` are the only evidence the route cannot
supply).  The trailing-entry half of the terminal arm at non-zero depth has no
named producer in this tree yet.  Nothing here claims the premises hold; it
states what follows if they do.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkRowsReady

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option pp.maxSteps 200000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR

/-! ### The assembly at the record's selection

The four producers at the two-armed bracket and brace contracts; the string and
value producers are the assembly's own parameters. -/

/-- **The walk's rows at `stage2GapRecover` and fuel 27.**  The bracket and brace
producers are `…Ready_of_arms`'s: the live pair arm's guard and the terminal
arm's row, per class.  The string and value producers are the assembly's
parameters, the value class's conditional one included. -/
noncomputable def stage2NoEventWalkRows_assembled {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracketPair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBracketGuard K k s)
    (hbracketTerm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracePair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBraceGuard K k s)
    (hbraceTerm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkRows_of_ready hstring
    (stage2NoEventWalkBracketReady_of_arms hbracketPair hbracketTerm)
    (stage2NoEventWalkBraceReady_of_arms hbracePair hbraceTerm)
    hvalue

/-- **The walk's step at `stage2GapRecover` and fuel 27.**  The dispatch's own
corollary at the rows above: the trace each row takes is the step's. -/
theorem stage2NoEventWalkStep_assembled {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracketPair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBracketGuard K k s)
    (hbracketTerm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracePair : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      sp ≠ 0 → k + 3 < K.nep →
      Stage2NoEventWalkBraceGuard K k s)
    (hbraceTerm : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State) (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      (sp = 0 ∨ K.nep ≤ k + 3) →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkStep (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkStep_of_ready hstring
    (stage2NoEventWalkBracketReady_of_arms hbracketPair hbracketTerm)
    (stage2NoEventWalkBraceReady_of_arms hbracePair hbraceTerm)
    hvalue

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkRows_assembled
#print axioms stage2NoEventWalkStep_assembled

end LeanLLVM.Refinement
