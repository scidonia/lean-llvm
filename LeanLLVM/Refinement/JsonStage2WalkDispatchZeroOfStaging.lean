/-
# The depth-zero refusals, from the staging

`HcontArm.commaZero`/`.colonZero` (`JsonStage2WalkDispatchHcontArms`) and
`LastEntryArm.commaZero`/`.colonZero` (`JsonStage2WalkDispatchArms`) are the comma and the
colon at depth zero: the head switch's `if.then127.i`/`if.then173.i`, the depth register
at `0`, the entry's position stored at `%e + 8`, and the refusal copy — six links
(`commaRefuse_at`, `colonRefuse_at`).  This module produces each arm at every state that
carries the invariant, which is the state family the loop's step quantifies over, and
composes it into the dispatch at both levels.  The only form the arms existed in was the
document-level one (`commaZero_last_arm` and its three twins, in
`JsonStage2WalkDispatchArmsDomain`), whose bodies read the arm's four cells off the seeded
head one at a time; the producer takes the state's own cells, so a wrapper supplies the
byte's class and the depth and nothing beside them.

## What the arm reads, and where each cell comes from

| cell | mark | how the producer has it |
|---|---|---|
| `h8` = `44` (comma) / `58` (colon) | **D** | `WalkInv.iter.reg8` is `%8`'s cell at every state and `hlastByte G C` its witness (`cont_reg8`); the class's byte test then pins the value (`eq_bit_value`) |
| `hv` (`%idxprom.i`, its `j`) | **D** | `WalkInv.idx_reg`, so `j` is `entryPos G C.k` — the entry stream's own position, not a number chosen at the wrapper |
| `he` (`%e`) | **D** | `WalkInv.regs` at the static name (`%e` is one of `walkStaticRegs`' pairs) |
| `hj` (`j ≤ G.n`) | **D** | geometry alone: below the stream the position is inside the document (`entryPos_lt`, `WalkGeom.inside`), and at or past it `entryPos` totalises to `0` (`entryPos_eq_zero_of_nep_le`).  `entryPos_le` states the two cases as one bound, with no hypothesis on `C.k` |
| `hj64` (`j < 2 ^ 64`) | **D** | geometry alone: `G.n < 2 ^ 64` (`WalkGeom.n_lt`, from `maxDoc`), so `entryPos_lt_64` bounds the position |
| `C.sp = 0` | **F-split** | a named premise.  `WalkInv.depth_cap` bounds the depth above only (`C.sp ≤ stage2StackExtent`), and a head state at any depth carries the same invariant, so zero-versus-positive is the document's rather than the state's |

Two premises in — the class's byte test and the depth split — and the arm out; the five
cells beside them are derived.  That is the row `JsonStage2WalkTerminalPrice` marks:
**D** `h8`; **D** the rest; **F-split** `C.sp = 0`, at both levels.

## The two levels, and the clause each needs

The two constructors hold the same six fields — the refusal chain is one path from
`NodeBlock21` to `if.then`, and the depth-zero store at `%e + 8` does not read the guard —
so the producers are the same term at both levels.  What differs is the *dispatch*:

* **`HcontArm`** is the continuing entry's arm, and `HcontArm.dispatch`'s guard is present:
  `hk : C.k + 1 < G.nep`, an entry still to be dispatched.  The refusal does not read it;
  the chain's own count test is `C.k < G.nep`, which `WalkInv.head_lt` gives at this block
  in both levels.
* **`LastEntryArm`** is the last entry's arm, and `LastEntryArm.dispatch`'s guard is
  negated: `hnot : ¬ (C.k + 1 < G.nep)`.  The count test is the same `WalkInv.head_lt`, so
  the two levels' only difference is which side of the count the dispatch's hypothesis
  states.

Both dispatches read `C.block = walkLoopHead` and the same geometry, so the document
bounds are the same derivation at both levels and neither supplies anything about the
document.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchAboveZeroOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The two document bounds the arm's count reads

`entryPos` is a stream read, so a bound on it holds at every index without a hypothesis on
`C.k`: below the stream the position is an entry the stream holds, and at or past it the
value is the totalisation's zero. -/

/-- **An entry position is inside the document at every index.**  Below the stream it is
an entry's own position (`entryPos_lt`); at and past the stream `entryPos` reads `0`
(`entryPos_eq_zero_of_nep_le`).  This is the shape the refusal's `j ≤ G.n` needs, because
the arm's count is read at the carried index, which the invariant bounds only by
`C.k ≤ G.nep`. -/
theorem entryPos_le {m0 : Mem} (G : WalkGeom m0) (k : Nat) : entryPos G k ≤ G.n := by
  by_cases hk : k < G.nep
  · exact le_of_lt (entryPos_lt G hk)
  · rw [entryPos_eq_zero_of_nep_le G (not_lt.mp hk)]
    exact Nat.zero_le _

/-- **An entry position is a word.**  The document's length is below `2 ^ 64`
(`WalkGeom.n_lt`, from the staging's `maxDoc`), so the position `entryPos_le` bounds is
too. -/
theorem entryPos_lt_64 {m0 : Mem} (G : WalkGeom m0) (k : Nat) : entryPos G k < 2 ^ 64 :=
  lt_of_le_of_lt (entryPos_le G k) (WalkGeom.n_lt G)

/-! ### The arms, at a state

Each producer takes the class's byte test and the depth split, and reads the byte, the
index, `%e` and the two document bounds off the invariant and the geometry. -/

/-- **The comma's refusal on the continuing head, from the staging.**  `HcontArm.commaZero`
at every state that carries the invariant and a zero depth: the byte is the invariant's
`%8` cell at the class's own value, `%idxprom.i` is `WalkInv.idx_reg`'s `entryPos G C.k`
and `%e` is a static name, so the arm's five derived cells are projections. -/
def hcontArm_commaZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp = 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .commaZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by simpa only [evalOperand] using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The colon's refusal on the continuing head, from the staging.**  The same six links
at `if.then173.i → if.then176.i`, and the same five derived cells. -/
def hcontArm_colonZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp = 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .colonZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by simpa only [evalOperand] using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The comma's refusal at the last entry, from the staging.**  The continuing entry's
arm at the last entry: the same fields, produced the same way.  Which side of the count
the state is on is the *dispatch's* hypothesis, not the arm's. -/
def lastEntryArm_commaZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp = 0) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .commaZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by simpa only [evalOperand] using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The colon's refusal at the last entry, from the staging.** -/
def lastEntryArm_colonZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp = 0) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .colonZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by simpa only [evalOperand] using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-! ### The dispatches

Each producer through its level's dispatch.  The continuing level supplies the guard and
the last entry supplies its negation; the refusal chain's count test is `WalkInv.head_lt`
in both. -/

/-- **The comma's continuing dispatch, from the staging.**  The producer through
`HcontArm.dispatch`, at the continuing entry's guard `C.k + 1 < G.nep`. -/
theorem walkDispatch_at_commaZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_commaZero_of_staging C s hInv hclass hsp)

/-- **The colon's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_colonZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_colonZero_of_staging C s hInv hclass hsp)

/-- **The comma's last-entry dispatch, from the staging.**  The producer through
`LastEntryArm.dispatch`, whose guard is the continuing one's negation. -/
theorem walkDispatch_at_commaZero_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 44) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_commaZero_of_staging C s hInv hclass hsp)

/-- **The colon's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_colonZero_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 58) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_colonZero_of_staging C s hInv hclass hsp)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.entryPos_le
#print axioms LeanLLVM.Refinement.WalkScope.entryPos_lt_64
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_commaZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_colonZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_commaZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_colonZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_commaZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_colonZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_commaZero_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_colonZero_last_of_staging

end WalkScope
end LeanLLVM.Refinement
