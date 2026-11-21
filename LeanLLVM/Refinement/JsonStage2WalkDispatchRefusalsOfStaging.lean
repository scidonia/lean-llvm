/-
# The byte-equality refusals, from the staging

Three arms of the census are refusals whose class is a single byte equality and which carry
no (ii) call and no (iii) traversal:

* `LastEntryArm.stringOpener` — the bare opener at the last entry: `sw.bb202.i`, the
  count's test `%inc.i uge %nep` and the five-link refusal at `if.then205.i`
  (`quoteRefuse_at`).
* `HcontArm.closeBracketZero` and `LastEntryArm.closingZero` — the closing bracket with
  nothing open: `if.then53.i` at depth zero and `bracketRefuse_at`'s six links.  The
  continuing level and the last entry share the arm (the head's guard is the only count
  premise, and a continuing entry has it), so there are two producers and two dispatches.
* `HcontArm.closeBraceZero` and `LastEntryArm.closeBraceZero` — the closing brace with
  nothing open: the same two blocks as the bracket's refusal at the byte's own pivots
  (`NodeBlock17 → LeafBlock15`, `closeBraceZero_at`'s six links).  Same count, same price,
  and the same two levels; the pivots are what separates it from the bracket's arm.

This module produces each at every state that carries the invariant, which is the state
family the loop's step quantifies over, so a wrapper supplies the class's byte test and
the arm's own free selector and nothing beside them.

## What each arm reads, and where each cell comes from

`stringOpener`, at the last entry:

| cell | mark | how the producer has it |
|---|---|---|
| `h8` = `34` | **D** | `WalkInv.iter.reg8` is `%8`'s cell and `hlastByte G C` its witness (`cont_reg8`); the class's byte test pins the value (`eq_bit_value`) |
| `hinc` (`%inc.i`) | **D** | `WalkInv.inc_reg`, so the value is `C.k + 1` — the header's own increment, not a number chosen at the wrapper |
| `hnep` (`%nep`) | **D** | `walkStaticRegs`' pair, through `WalkInv.regs` |
| `hge` (`inc uge nep`) | **D** | the last entry's `¬ (C.k + 1 < G.nep)` beside the two register readings and the geometry: `C.k ≤ G.nep` (`WalkInv.k_le`) and `G.nep ≤ stage2MaxDocument` make both operands words, so the negated order *is* the test's clear bit (`quoteCount_ge`) |
| `hv` (`%4`) | **D** | `walkStaticRegs`' pair, through `WalkInv.regs` |
| `he` (`%e`) | **D** | the same list's |
| `¬ (C.k + 1 < G.nep)` | **F-split** | a named premise, and the level's own selector: the seed state at a one-entry document is a last entry, so the split is the document's rather than the state's |

The census marked `hge` **D** "from the consumer's `¬(C.k+1<nep)` and the static cells",
and the producer confirms it: the negated count is the only thing taken, the test is
derived from it.  The `¬ (C.k + 1 < G.nep)` binder is not a residual of the arm — the
constructor does not carry it at either level — it is the level's selector, supplied by
the dispatch's own hypothesis at the call site.

`closeBracketZero`/`closingZero`, at both levels:

| cell | mark | how the producer has it |
|---|---|---|
| `h8` = `93` | **D** | as the quote's: `cont_reg8` beside `eq_bit_value` |
| `hv` (`%idxprom.i`, its `j`) | **D** | `WalkInv.idx_reg`, so `j` is `entryPos G C.k` |
| `he` (`%e`) | **D** | `walkStaticRegs`' pair, through `WalkInv.regs` |
| `hj` (`j ≤ G.n`) | **D** | geometry alone: `entryPos_le` bounds the position at every index, with no hypothesis on `C.k` |
| `hj64` (`j < 2 ^ 64`) | **D** | geometry alone: `WalkGeom.n_lt` beside `entryPos_lt_64` |
| `C.sp = 0` | **F-split** | a named premise: `WalkInv.depth_cap` bounds the depth above only, so zero-versus-positive is the document's |

`closeBraceZero`, at both levels: the same six cells as the bracket's row above, at the
byte `125` instead of `93`.  The byte's route to the two refusal blocks is the only thing
that differs — `%Pivot18` (`slt %8, 125`) and `%SwitchLeaf16` (`eq %8, 125`) in place of
`%Pivot12` and `%SwitchLeaf10` — so the class test is the byte's own and the five derived
cells are read exactly as at `93`.

Two premises in — the class's byte test and the depth split (the quote's: the class and
the level's count) — and the arm out; every other cell is the invariant's or the
geometry's.  That is the row the enumeration marks, with no correction: the census is
exact for these four arms.

## The three producers, five arm shapes

`stringOpener` exists only at the last entry: at the continuing level the byte `34` is
`.twoEntry`, whose evidence is the standalone string's residue and its accepting-arm
selector rather than a refusal, so it is not this module's.  `closeBracketZero`'s and
`closeBraceZero`'s two levels are the same six fields, because each refusal chain is one
path from `NodeBlock21` to `if.then` and the depth-zero store at `%e + 8` does not read the
count.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchZeroOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The count's test, cleared from the order

The quote's `if.then203.i` is `uge %inc.i, %nep` — the count's test in its complement's
form — so the arm asks for the test's clear bit at two 64-bit words.  The tree states the
generic fact already (`PipelineBodyStep.evalICmp_ult_zero`), but that module is the
pipeline body's and the walk layer does not import it, so the derivation is written at the
walk's two operands rather than as a second copy of the general lemma. -/

/-- **The quote's count test at the last entry is clear.**  `%inc.i` is the header's
`C.k + 1` and `%nep` the stream's count; both are words (`C.k ≤ G.nep` from
`WalkInv.k_le`, `G.nep ≤ G.n ≤ 2 ^ 32` from `WalkGeom.nep_le` and `maxDoc`), so the last
entry's `¬ (C.k + 1 < G.nep)` is exactly the `uge` test's clear bit.  This is the row the
census marks **D**: the test is a function of the count the level supplies, not a second
premise beside it. -/
theorem quoteCount_ge {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hnot : ¬ (C.k + 1 < G.nep)) :
    evalICmp .ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = 0 := by
  have hnep : G.nep ≤ stage2MaxDocument := le_trans G.nep_le G.maxDoc
  simp only [stage2MaxDocument] at hnep
  have hk : C.k + 1 ≤ G.nep + 1 := by
    have := hInv.k_le
    omega
  have hf : BitVec.ult (BitVec.ofNat 64 (C.k + 1)) (BitVec.ofNat 64 G.nep) = false := by
    rw [Bool.eq_false_iff]
    intro ht
    have hlt := (BitVec.ult_iff_toNat_lt).1 ht
    simp only [BitVec.toNat_ofNat] at hlt
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
    omega
  unfold evalICmp
  rw [hf]
  rfl

/-! ### The arms, at a state

The quote takes the class and the level's count; the two bracket refusals take the class
and the depth split, and read the position, `%e` and the two document bounds off the
invariant and the geometry. -/

/-- **The bare opener's refusal at the last entry, from the staging.**
`LastEntryArm.stringOpener` at every state that carries the invariant and the exhausted
count: `%8` is the invariant's cell at the class's own value, `%inc.i` and `%nep` are the
invariant's registers, and the count's clear bit is `quoteCount_ge`'s. -/
def lastEntryArm_stringOpener_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1)
    (hnot : ¬ (C.k + 1 < G.nep)) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .stringOpener (inc := BitVec.ofNat 64 (C.k + 1)) (nep := BitVec.ofNat 64 G.nep)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    (by walk_read using hInv.inc_reg)
    (by
      walk_read using
        hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep)) (by simp [walkStaticRegs]))
    (quoteCount_ge hInv hnot)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))

/-- **The closing bracket's refusal on the continuing head, from the staging.**
`HcontArm.closeBracketZero` at every state that carries the invariant and a zero depth:
the byte is the class's value, `%idxprom.i` is `entryPos G C.k` and `%e` a static name, so
the arm's five derived cells are projections. -/
def hcontArm_closeBracketZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp = 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .closeBracketZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing bracket's refusal at the last entry, from the staging.**  The continuing
entry's arm at the level whose count is exhausted: the same six fields, produced the same
way. -/
def lastEntryArm_closeBracketZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp = 0) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .closingZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing brace's refusal on the continuing head, from the staging.**
`HcontArm.closeBraceZero` at every state that carries the invariant and a zero depth: the
same six fields as the bracket's, at the byte `125`.  The byte's route to the depth test
is `NodeBlock17 → LeafBlock15` and the count is the bracket's, so the arm is the class's
test and the depth split and nothing else. -/
def hcontArm_closeBraceZero_of_staging {m0 : Mem} {G : WalkGeom m0} (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp = 0) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .closeBraceZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-- **The closing brace's refusal at the last entry, from the staging.**  The continuing
entry's arm at the level whose count is exhausted: the same six fields, produced the same
way. -/
def lastEntryArm_closeBraceZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp = 0) :
    LastEntryArm (stage2Calls stage2SubCalls) G C s :=
  .closeBraceZero (j := entryPos G C.k)
    (by
      rw [← eq_bit_value hclass]
      exact cont_reg8 hInv)
    hsp
    (by walk_read using hInv.idx_reg)
    (hInv.regs ("%e", .ptr C.stage.e) (by simp [walkStaticRegs]))
    (entryPos_le G C.k)
    (entryPos_lt_64 G C.k)

/-! ### The dispatches

Each producer through its level's dispatch.  The quote's takes the negated count and the
continuing bracket's the guard; the last entry's bracket takes the negation, as the
continuing entry's does at its own level. -/

/-- **The bare opener's dispatch, from the staging.** -/
theorem walkDispatch_at_stringOpener_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 34) = 1) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_stringOpener_of_staging C s hInv hclass hnot)

/-- **The closing bracket's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_closeBracketZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk (hcontArm_closeBracketZero_of_staging C s hInv hclass hsp)

/-- **The closing bracket's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_closeBracketZero_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 93) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_closeBracketZero_of_staging C s hInv hclass hsp)

/-- **The closing brace's continuing dispatch, from the staging.** -/
theorem walkDispatch_at_closeBraceZero_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk (hcontArm_closeBraceZero_of_staging C s hInv hclass hsp)

/-- **The closing brace's last-entry dispatch, from the staging.** -/
theorem walkDispatch_at_closeBraceZero_last_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hnot : ¬ (C.k + 1 < G.nep))
    (hclass : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 1)
    (hsp : C.sp = 0) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  LastEntryArm.dispatch hInv hblock hnot
    (lastEntryArm_closeBraceZero_of_staging C s hInv hclass hsp)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.quoteCount_ge
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_stringOpener_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_closeBracketZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_closeBracketZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_stringOpener_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeBracketZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeBracketZero_last_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_closeBraceZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.lastEntryArm_closeBraceZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeBraceZero_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_closeBraceZero_last_of_staging

end WalkScope
end LeanLLVM.Refinement
