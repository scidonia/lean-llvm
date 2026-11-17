/-
# The scan-free continuing entry, from the staging

`HcontArm.cleanup` (`JsonStage2WalkDispatchHcontArms`) is the high-byte route's no-run
class: the head's byte is `126` or `127`, the byte before the entry's end is not
whitespace, and the token ends at the entry's end — `if.end372.i`'s else arm, the class-C
span, the tail's three calls on their empty arm and the merge, with no scan entered.
`walkRevolutionMergeSeg` (`JsonStage2WalkRevolutionSeg`) composes it to the merge at the
class's own count (`p ≤ 21`), and its bundle is `HcontCleanupFacts`
(`JsonStage2WalkRevolution`).

This module produces that bundle at every state that carries the invariant, and the arm
and dispatch with it.

## What the producer derives, and what it takes

The bundle's fields fall into the three groups the terminal-price census names: the head
byte's class, the cells the walk's own blocks bind, and the document's content.  The
first two are the invariant's or arithmetic on the consumer's own hypothesis, so the
producer *derives* them:

| field | how |
|---|---|
| `x`, `h8` | `hlastByte G C` and `WalkInv.iter.reg8` (`evalOperand` of the cell) |
| `hlt91`, `hlt123` | `hlast_slt_zero_of_toInt_le` from `hlt125`: the signed order passes 91 and 123 before 125 |
| `inc`, `nep`, `hinc`, `hnep` | `hlastIncV C`/`hlastNepV G` at `headAS₄`'s peels (`headAS4_envInc`, `headAS4_envNep`); the cells are `WalkInv.inc_reg` and `%nep`'s `walkStaticRegs` row |
| `hnext` | `cont_ult_one` from the consumer's guard `C.k + 1 < G.nep` |
| `ep`, `h5` | `G.ep` and `WalkPtrs`'s positions pointer at the succeeding arm (`contAS5_env5`) |
| `hi63` | `cont_hi63`: `C.k + 1` is a document position |
| `ix`, `hidx5` | `WalkInv.idx_reg`'s cell, peeled to `contAS₅` |
| `htok5`, `hgap5` | `WalkInv.regs`'s `%t352.i` and `%gap.i` rows, peeled to `contAS₅` |
| `b35`, `hread35` | `contB35 G v`, and the read is `cont_hread35`'s: `cond.end349.i`'s two token-record stores are disjoint from the document's region, so the byte before the entry's end is `walkDoc_byte`'s |
| `b8`, `h8end` | the loop head's `%8` through `contLandS_env8`: none of the byte's pivots rebinds `%8` |
| `hend` | `%end.i`'s `walkStaticRegs` row through `contLandS_envEnd` |
| `hbit` | `hlast_bit6_of_class` at the two class bits: the seam's tag test is clear at `126`/`127` |
| `x1`, `h8c` | `%8` at the class's seam (`contSeamByte_env8`), the same cell |
| `hc110`, `hc116`, `hceq116` | the class bits again: the byte clears 110 and 116 and is not 116 |

The document's content stays a named premise, each with what supplies it:

| premise | what supplies it |
|---|---|
| `hlt125`, `hne125` | **the document's head byte**: `slt %8 125` and `eq %8 125` clear leave `126`/`127`, the arm's class (`HcontClass.defaultValueHigh`) |
| `v`, `hread` | **the next entry's lane word**: `%5`'s pointer is the invariant's, but the word at the next index is `G.ent`'s |
| `hspan` | **the entry stream's order**: the lane is at or below the next entry's position (`WalkGeom.order`/`inside`), which is what places the byte before the entry's end inside the document |
| `hugt` | **the entry's non-emptiness**: the lane's word is above this entry's index (`%idxprom.i`), a relation between the input's positions |
| `hb` | **the byte before the entry's end and its route**: the document's content at that index, whose three leaves the class records |
| `r₁`, `r₂`, `r₃`, `ev`, `cA`, `rdv`, `xA`, `hTail` | **the tail's three callees**: their preconditions and answers at the argument lists the walk stages (`consumerTailSegEmptyAt`) |

`hspan` is the one premise the bundle's *statement* does not carry: it is read only by the
derivation of `hread35`, because the byte before the entry's end is at `v - 1` and the
read is the document's only while that index is inside it.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLaneOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchHcontArms

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The bundle, from the entry's evidence.**  Produced at the loop's own witnesses: the
head's byte is `hlastByte G C`, the counts are `hlastIncV C`/`hlastNepV G`, the position
table is `G.ep`, and the byte before the entry's end is `contB35 G v`, whose class the
caller names.  Only the document's facts, the byte's route and the tail's staging enter as
premises; every cell the walk's own blocks bind is derived (this module's header names
each), and at each of the three routes they are the same cells: the byte's pivots and the
seam bind none of `%8`, `%end.i` or `%ee.1.i`. -/
def hcontCleanupFacts_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb : HcontByteRoute (cont35 (contB35 G v)))
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb)
      (TailCarryEnd (ContTailStartC C) ev)
      (contCleanupEndByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb r₁ r₂ r₃ cA rdv xA) 3) :
    HcontCleanupFacts G C s := by
  -- the lane is above the entry's index, so the byte before the entry's end is inside
  have hgt : entryPos G C.k < v.toNat := contLane_gt G C hk hugt
  have hv1 : 1 ≤ v.toNat := by omega
  have hread35 :
      readBytes (contEndS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
        (contIx G C)).mem ((G.b - 1) + v.toNat) 1 = some [contB35 G v] :=
    cont_hread35 (G := G) (C := C) (s := s) hInv hk (v := v) (k := v.toNat - 1)
      hspan (by omega)
  exact
    { x := hlastByte G C
      h8 := by
        show evalOperand s (.reg "%8") = some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        exact hInv.iter.reg8
      hlt91 := hlast_slt_zero_of_toInt_le (by decide) hlt125
      hlt123 := hlast_slt_zero_of_toInt_le (by decide) hlt125
      hlt125 := hlt125
      hne125 := hne125
      inc := hlastIncV C
      nep := hlastNepV G
      hinc := by
        show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%inc.i") =
          some (.int 64 (hlastIncV C))
        simp only [evalOperand]
        rw [headAS4_envInc s (hlastByte G C)]
        exact hInv.inc_reg
      hnep := by
        show evalOperand (headAS₄ s (hlastByte G C)) (.reg "%nep") =
          some (.int 64 (hlastNepV G))
        simp only [evalOperand]
        rw [headAS4_envNep s (hlastByte G C)]
        exact hInv.regs ("%nep", .int 64 (BitVec.ofNat 64 G.nep))
          (by simp [walkStaticRegs])
      hnext := cont_ult_one G C hk
      ep := G.ep
      v := v
      h5 := contAS5_env5 C s (hlastByte G C) (hlastIncV C) (hlastNepV G) hInv
      hi63 := cont_hi63 G C hk
      hread := hread
      ix := contIx G C
      hidx5 := contAS5_envIdx s (hlastByte G C) (hlastIncV C) (hlastNepV G) (contIx G C)
        hInv.idx_reg
      htok5 := contAS5_envTok C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (cont_static_tok hInv)
      hgap5 := contAS5_envGap C s (hlastByte G C) (hlastIncV C) (hlastNepV G)
        (hInv.regs ("%gap.i", .ptr (C.stage.tok + 20)) (by simp [walkStaticRegs]))
      hugt := hugt
      b35 := contB35 G v
      hread35 := hread35
      hb := hb
      b8 := hlastByte G C
      hend := by
        show lookupName (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
          (contIx G C) (contB35 G v)).env "%end.i" = some (.ptr (C.stage.tok + 8))
        rw [contLandS_envEnd]
        exact hInv.regs ("%end.i", .ptr (C.stage.tok + 8)) (by simp [walkStaticRegs])
      h8end := by
        show lookupName (contLandS C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v
          (contIx G C) (contB35 G v)).env "%8" = some (.int 8 (hlastByte G C))
        rw [contLandS_env8]
        exact hInv.iter.reg8
      hbit := by
        show (evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 45) |||
          evalICmp .ult (hlastByte G C + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0
        exact hlast_bit6_of_class hlt125 hne125
      x1 := hlastByte G C
      h8c := by
        show evalOperand (contSeamByte (contLandS C s (hlastByte G C) (hlastIncV C)
          (hlastNepV G) G.ep v (contIx G C) (contB35 G v)) v.toNat C.stage.tok
          (contB35 G v) (hlastByte G C) hb) (.reg "%8") = some (.int 8 (hlastByte G C))
        simp only [evalOperand]
        rw [contSeamByte_env8, contLandS_env8]
        exact hInv.iter.reg8
      hc110 := hlast_slt_zero_of_toInt_le (by decide) hlt125
      hc116 := hlast_slt_zero_of_toInt_le (by decide) hlt125
      hceq116 := hlast_eq_zero_of_slt_zero (by decide) hlt125
      r₁ := r₁
      r₂ := r₂
      r₃ := r₃
      ev := ev
      cA := cA
      rdv := rdv
      xA := xA
      hTail := hTail }

/-- **The scan-free arm, from the staging.**  `HcontArm.cleanup` at every state that
carries the invariant, its payload the producer above. -/
def hcontArm_cleanup_of_staging {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb : HcontByteRoute (cont35 (contB35 G v)))
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb)
      (TailCarryEnd (ContTailStartC C) ev)
      (contCleanupEndByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb r₁ r₂ r₃ cA rdv xA) 3) :
    HcontArm (stage2Calls stage2SubCalls) G C s :=
  .cleanup (hcontCleanupFacts_of_staging G C s hInv hk hlt125 hne125 hread hspan hugt
    hb r₁ r₂ r₃ ev (cA := cA) (rdv := rdv) (xA := xA) hTail)

/-- **The scan-free continuing dispatch, from the staging.**  The arm's own producer, and
`HcontArm.dispatch` at its composition. -/
theorem walkDispatch_at_cleanup_of_staging {m0 : Mem} {G : WalkGeom m0}
    {C : WalkCarry G} {s : State} (hInv : WalkInv G C s)
    (hblock : C.block = walkLoopHead) (hk : C.k + 1 < G.nep)
    (hlt125 : evalICmp .slt (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    (hne125 : evalICmp .eq (hlastByte G C) (BitVec.ofNat 8 125) = 0)
    {v : BitVec 32}
    (hread : readBytes (contAS₅ s (hlastByte G C) (hlastIncV C) (hlastNepV G)).mem
      (G.ep + (hlastIncV C).toNat * 4) 4 = some (natToBytes v.toNat 4))
    (hspan : v.toNat ≤ entryPos G (C.k + 1))
    (hugt : evalICmp .ugt (BitVec.ofNat 64 v.toNat)
      (BitVec.ofNat 64 (entryPos G C.k)) = 1)
    (hb : HcontByteRoute (cont35 (contB35 G v)))
    (r₁ r₂ r₃ : CallOutcome) (ev : EventRecord) {cA rdv xA : BitVec 32}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (ContTailStartC C)
      (contTailStartByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb)
      (TailCarryEnd (ContTailStartC C) ev)
      (contCleanupEndByte C s (hlastByte G C) (hlastIncV C) (hlastNepV G) G.ep v (contIx G C)
        (contB35 G v) (hlastByte G C) (hlastByte G C) hb r₁ r₂ r₃ cA rdv xA) 3) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G C s :=
  HcontArm.dispatch hInv hblock hk
    (hcontArm_cleanup_of_staging G C s hInv hk hlt125 hne125 hread hspan hugt hb
      r₁ r₂ r₃ ev (cA := cA) (rdv := rdv) (xA := xA) hTail)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.hcontCleanupFacts_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.hcontArm_cleanup_of_staging
#print axioms LeanLLVM.Refinement.WalkScope.walkDispatch_at_cleanup_of_staging

end WalkScope
end LeanLLVM.Refinement
