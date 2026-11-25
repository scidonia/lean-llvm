/-
The no-event walk's rows, assembled from the classes' three-armed producers.

`JsonStage2NoEventWalkRowsAssemble` states the consumer's contract,
`Stage2NoEventWalkRows`, and reaches it from one producer per head class
(`stage2NoEventWalkRows_of_ready`).  This module supplies the bracket and brace
producers from `JsonStage2NoEventWalkRowsReady`'s three-armed forms and states
the result at the record's own selection and fuel.

**What a caller supplies.**  The class producers, each at a premise the walk's
own arms select.  The split is room first, byte second: no room at `k + 2` for
the pair's liveness (`K.nep ≤ k + 3`) is the trailing exit whatever the bytes;
with room, `if.end327.peel` (bracket) / `if.end303` (brace) test the byte at
`k + 1`, the closer arm taking the closer route and its failure (`if.end`) the
descend.

* the string class (`hstring`) and the value class (`hvalue`), unchanged from
  the assembly's contract — the value class is the assembly's own conditional
  parameter, as it has no producer at its whitespace/remainder arm;
* `hbracketCloser`/`hbraceCloser`, the closer arm's row at the closer byte
  (`93`/`125`).  At depth zero the tree produces it
  (`stage2NoEventWalkBracketZeroRow`/`…BraceZeroRow`, given the endpoint's
  `after_value` cells and the record's `hreportAcc`/`hboundAcc`/`hreportRef`);
  at positive depth its producer (`…BracketRow_of_head`/`…BraceRow_of_head`)
  additionally needs the pair's branch facts, notably the separator at `k + 2`.
  So the arm is inhabited in-tree only on the comma-continuation shape; an
  empty pair that is the last element of its parent is a **second missing
  route** beside the descend one;
* `hbracketDescend`/`hbraceDescend`, the descend arm's row at any other byte.
  **This is the missing route**: no term in this tree produces a row on
  `if.end`, so a caller supplies it from the descend route — the push at
  `sp ≠ 0` with `sp ≤ 519` and `fr ≠ 0`, the cycle to the next element's head,
  and the separator at `k + 2` — with that staging inside the caller's proof;
* `hbracketTrail`/`hbraceTrail`, the trailing exit (`K.nep ≤ k + 3`, which
  includes every head at `nep = k + 3`), whose `Stage2NoEventWalkExit` evidence
  is the caller's post.

Nothing here claims a premise holds; it states what follows if they do.  The
premises are byte-restricted to their arms, so none quantifies over every head of
the class — the form an earlier version took, refuted by a descend head.
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

The four producers at the three-armed bracket and brace contracts; the string
and value producers are the assembly's own parameters. -/

/-- **The walk's rows at `stage2GapRecover` and fuel 27.**  The bracket and brace
producers are `…Ready_of_routes`'s: the closer arm, the descend arm (the missing
route) and the trailing exit, per class.  The string and value producers are the
assembly's parameters, the value class's conditional one included. -/
noncomputable def stage2NoEventWalkRows_assembled {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracketCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracketDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 93 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracketTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkRows (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkRows_of_ready hstring
    (stage2NoEventWalkBracketReady_of_routes hbracketCloser hbracketDescend
      hbracketTrail)
    (stage2NoEventWalkBraceReady_of_routes hbraceCloser hbraceDescend hbraceTrail)
    hvalue

/-- **The walk's step at `stage2GapRecover` and fuel 27.**  The dispatch's own
corollary at the rows above: the trace each row takes is the step's. -/
theorem stage2NoEventWalkStep_assembled {mem : Mem}
    (hstring : Stage2NoEventWalkStringReady
      (stage2NoEventCalls stage2GapRecover) mem 27)
    (hbracketCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 93 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracketDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 93 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbracketTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBracketClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceCloser : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat = 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceDescend : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat) (next : Nat) (nextByte : UInt8),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.ent[k + 1]? = some next →
      K.bs[next]? = some nextByte →
      nextByte.toNat ≠ 125 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hbraceTrail : ∀ (K : Stage2NoEventWalkCarry) (k : Nat) (s : State)
        (sp : Nat),
      Stage2NoEventWalkHead K mem k s →
      Stage2NoEventWalkTrace K →
      Stage2NoEventWalkHeadBraceClass K k s →
      lookupName s.env "%sp.0.ph1403" = some (.int 32 (BitVec.ofNat 32 sp)) →
      K.nep ≤ k + 3 →
      Stage2NoEventWalkRow (stage2NoEventCalls stage2GapRecover) mem 27 K k s)
    (hvalue : Stage2NoEventWalkValueReady
      (stage2NoEventCalls stage2GapRecover) mem 27) :
    Stage2NoEventWalkStep (stage2NoEventCalls stage2GapRecover) mem 27 :=
  stage2NoEventWalkStep_of_ready hstring
    (stage2NoEventWalkBracketReady_of_routes hbracketCloser hbracketDescend
      hbracketTrail)
    (stage2NoEventWalkBraceReady_of_routes hbraceCloser hbraceDescend hbraceTrail)
    hvalue

/-! ### Axiom footprints -/

#print axioms stage2NoEventWalkRows_assembled
#print axioms stage2NoEventWalkStep_assembled

end LeanLLVM.Refinement
