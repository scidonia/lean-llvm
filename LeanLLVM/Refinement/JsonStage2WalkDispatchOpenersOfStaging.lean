/-
# The container openers, from the staging

`HcontArm.containerOpen` and `LastEntryArm.containerOpen` are `[` and `{` on the head: both
bytes enter `if.then.i`, and the four head links beside the tail's five reach the merge —
nine links (`containerOpenMerge_at`).  This module produces the arm at every state that
carries the invariant, at both levels, so the `…Domain` wrappers stop building the
constructor by hand out of a document's byte read.

## The class, and the two literals

The census class is one of two bytes, `91` and `123`, and each is an `eq` test on the
head's byte.  So there are two producers per level, one per literal: each takes the
class's own byte test and pins the value with `eq_bit_value`, and the arm's disjunction
`hopen : b = 91 ∨ b = 123` is then *filled* from the pinned byte (`Or.inl`/`Or.inr rfl`)
rather than supplied.  Two producers rather than one at a class disjunction is the shape
the dispatcher can call: `HcontClass`'s `.openBracket`/`.openBrace` constructors each hold
one equality bit, so the eventual consumer holds one of these two premises and not the
disjunction.

## What the arm reads, and what it does not

| cell | mark | how the producer has it |
|---|---|---|
| `h8` | **D** | `WalkInv.iter.reg8` is `%8`'s cell and `hlastByte G C` its witness (`cont_reg8`); the class's byte test pins the value (`eq_bit_value`) |
| `hopen` | **D** | the pinned byte: the disjunction's member is the literal the class test names |
| `hsp519` (`C.sp ≤ 519`) | **F-split/boundary** | a named premise.  `WalkInv.depth_cap` gives `C.sp ≤ stage2StackExtent = 520` only, and the block's own `ugt %sp.i, 519` sends `520` to `if.then21.i` instead of this route — a depth selector the invariant does not settle, and the census marks it as the boundary it is |
| `hrd` (the root slot's zero word) | **F** | a named premise.  `WalkInv.root_slot` is the slot's *presence* (`HasBytes`), not its value, so the zero word is the state's |
| `hpreV`, `r`, `hcall`, `hret` | (ii) | the callee's staging and answer: `s2ValuePosPre` at the arm's argument list, the outcome and its `ret`, exactly as the constructor carries them |

So a wrapper supplies the class, the depth boundary, the root word and the call; the byte,
its class bits and the disjunction are derived.  The census's row is confirmed with no
correction.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchRefusalsOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing level

Two producers, one per opener byte, and their dispatches. -/

/-- **The open bracket's arm on the continuing head, from the staging.**
`HcontArm.containerOpen` at every state that carries the invariant, the `519` boundary and
the call's own bundle: the byte is the class's value and the disjunction its first
member. -/
def hcontArm_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp519 hrd hpreV r hcall hret

/-- **The open brace's arm on the continuing head, from the staging.**  The same nine
links at `NodeBlock17 → LeafBlock13`, with the disjunction's second member. -/
def hcontArm_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp519 hrd hpreV r hcall hret

/-- **The open bracket's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpen91_of_staging C s hInv hclass hsp519 hrd hpreV r hcall hret)

/-- **The open brace's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_containerOpen123_of_staging C s hInv hclass hsp519 hrd hpreV r hcall hret)

/-! ### The last entry

The same nine links at the level whose count is exhausted: the arm is the continuing one's
term, and only the dispatch's hypothesis differs. -/

/-- **The open bracket's arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpen91_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 91)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp519 hrd hpreV r hcall hret

/-- **The open brace's arm at the last entry, from the staging.** -/
def lastEntryArm_containerOpen123_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .containerOpen (b := BitVec.ofNat 8 123)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp519 hrd hpreV r hcall hret

/-- **The open bracket's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen91_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 91) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpen91_of_staging C s hInv hclass hsp519 hrd hpreV r hcall hret)

/-- **The open brace's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_containerOpen123_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 123) = 1)
    (hsp519 : C.sp ≤ 519)
    (hrd : readBytes s.mem (G.next0 + 8) 4 = some (natToBytes 0 4))
    (hpreV : s2ValuePosPre
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next)
    (r : CallOutcome)
    (hcall : stage2Calls stage2SubCalls "s2_value_pos"
      [.int 32 (BitVec.ofNat 32 C.sp), .int 32 (BitVec.ofNat 32 0),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_containerOpen123_of_staging C s hInv hclass hsp519 hrd hpreV r hcall hret)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen91_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen123_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen91_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_containerOpen123_last_of_staging

end WalkScope
end LeanLLVM.Refinement
