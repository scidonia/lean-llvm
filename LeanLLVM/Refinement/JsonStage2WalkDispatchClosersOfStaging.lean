/-
# The closing delimiters above depth zero, from the staging

`HcontArm.closeWithOpen` and `LastEntryArm.closeWithOpen` are `]` and `}` at a positive
depth: both enter `if.then53.i`, and the nesting check's two stack bytes select the merge
or a refusal — `closeWithOpen_at`'s four sub-routes.  This module produces the arm at
every state that carries the invariant, at both levels, so the `…Domain` wrappers stop
building the constructor out of a reached carry's two maps.

## The class, and the two literals

The census class is one of two bytes, `93` and `125`, each an `eq` test on the head's
byte.  As with the openers there are two producers per level, one per literal: each takes
the class's own byte test, pins the value with `eq_bit_value`, and *fills* the arm's
`hv : v = 93 ∨ v = 125` from the pinned byte.  The dispatcher's eventual premise is one
of `HcontClass`'s `.closeBracket`/`.closeBrace` constructors, which each hold one equality
bit, so a producer keyed on one literal is what it can call.

## What the arm reads, and what it does not

| cell | mark | how the producer has it |
|---|---|---|
| `h8` | **D** | `WalkInv.iter.reg8` is `%8`'s cell and `hlastByte G C` its witness (`cont_reg8`); the class's byte test pins the value (`eq_bit_value`) |
| `hv` | **D** | the pinned byte's own member of the disjunction |
| `hmark`, `hstate` | **D** | the witnesses `C.tyMap (C.sp - 1)` and `C.stMap (C.sp - 1)`: the two fields are `rfl`, so no clause of `WalkInv` is consulted and no invariant clause is needed for them |
| `hvj` (`%idxprom.i`, its `j`) | **D** | `WalkInv.idx_reg`, so `j` is `entryPos G C.k` |
| `he` (`%e`) | **D** | `walkStaticRegs`' pair, through `WalkInv.regs` |
| `hj` (`j ≤ G.n`) | **D** | geometry alone: `entryPos_le` bounds the position at every index, with no hypothesis on `C.k` and none on the head's count |
| `hj64` (`j < 2 ^ 64`) | **D** | geometry alone: `entryPos_lt_64` |
| `C.sp ≠ 0` | **F-split** | a named premise: `WalkInv.depth_cap` bounds the depth above only |
| `hpreA` | (ii) | `s2AfterValuePre` at the pop's argument list: the callee's staging, exactly as the constructor carries it |

So a wrapper supplies the class, the depth split and the call; the byte, its class bits,
the two stack cells and the four position cells are derived.  Two of the census's rows
deserve their note: `hmark`/`hstate` are **D** by a carry projection that needs no
invariant clause at all, and `hj`/`hj64` are **D** at every index, so the producer's
bounds are weaker hypotheses than the head guard the by-hand wrappers used
(`entryPos_lt` at `C.k < G.nep`).  No row needed a correction.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchZeroOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The continuing level

Two producers, one per closing byte, and their dispatches. -/

/-- **The closing bracket's arm on the continuing head, from the staging.**
`HcontArm.closeWithOpen` at every state that carries the invariant, a positive depth and
the call's own bundle: the byte is the class's value, the disjunction its first member,
and the two stack cells are the carry's maps at `%sp - 1` — projections, not premises. -/
def hcontArm_closeWithOpen93_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .closeWithOpen (v := BitVec.ofNat 8 93) (b1 := C.tyMap (C.sp - 1))
    (b2 := C.stMap (C.sp - 1)) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp rfl rfl hpreA
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing brace's arm on the continuing head, from the staging.**  The same four
sub-routes at `LeafBlock15`, with the disjunction's second member. -/
def hcontArm_closeWithOpen125_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .closeWithOpen (v := BitVec.ofNat 8 125) (b1 := C.tyMap (C.sp - 1))
    (b2 := C.stMap (C.sp - 1)) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp rfl rfl hpreA
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing bracket's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_closeWithOpen93_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_closeWithOpen93_of_staging C s hInv hclass hsp hpreA)

/-- **The closing brace's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_closeWithOpen125_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_closeWithOpen125_of_staging C s hInv hclass hsp hpreA)

/-! ### The last entry

The same four sub-routes at the level whose count is exhausted. -/

/-- **The closing bracket's arm at the last entry, from the staging.** -/
def lastEntryArm_closeWithOpen93_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .closeWithOpen (v := BitVec.ofNat 8 93) (b1 := C.tyMap (C.sp - 1))
    (b2 := C.stMap (C.sp - 1)) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inl rfl) hsp rfl rfl hpreA
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing brace's arm at the last entry, from the staging.** -/
def lastEntryArm_closeWithOpen125_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .closeWithOpen (v := BitVec.ofNat 8 125) (b1 := C.tyMap (C.sp - 1))
    (b2 := C.stMap (C.sp - 1)) (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (Or.inr rfl) hsp rfl rfl hpreA
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing bracket's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_closeWithOpen93_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_closeWithOpen93_of_staging C s hInv hclass hsp hpreA)

/-- **The closing brace's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_closeWithOpen125_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp ≠ 0)
    (hpreA : s2AfterValuePre
      [.int 32 (BitVec.ofNat 32 C.sp + BitVec.ofNat 32 4294967295), .ptr (G.next0 + 8),
       .ptr C.stage.ctype, .ptr C.stage.cst] s.mem s.next) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_closeWithOpen125_of_staging C s hInv hclass hsp hpreA)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_closeWithOpen93_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_closeWithOpen125_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_closeWithOpen93_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_closeWithOpen125_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeWithOpen93_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeWithOpen125_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeWithOpen93_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeWithOpen125_last_of_staging

end WalkScope
end LeanLLVM.Refinement
