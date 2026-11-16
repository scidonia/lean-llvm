/-
The `'f'` leaf's domain, at staged documents.

## What is exhibited

`102` (`'f'`) is the byte `LeafBlock54`'s equality test singles out, so the staged
documents below take the `'f'` arm at both levels:

| document | head byte | `HcontClass` | level |
|---|---|---|---|
| `"f0"` | `102` | `defaultValueBracketHigh` | continuing |
| `"f"` | `102` | `defaultValueBracketHigh` | last entry |

The byte is read off the staged document (`WalkGeom.doc`, `WalkGeom.entries`,
`entryByte`/`entryPos`), and the state is the seed's own handoff
(`walkSeedInvariant_geometry`), so the class premises — the tag test clear, `slt %8 110 =
1` and `eq %8 102 = 1` — are facts about the input rather than about the arm.

The arm's two **segments** enter as hypotheses, exactly as they are fields of the arm: the
head's chain to `if.else387.i` (twelve links at a continuing entry, eleven at the last) and
the tail's three calls on their empty arm.  What the dispatch below exercises is what the
arm composes: `fSpan`'s four links, the merge, its three cells and its price.

## The negative control

The letters documents' byte `97` (`'a'`) satisfies the arm's first two premises — the tag
test is clear and `97 < 110` — but `eq 97 102` is `0`, so `LeafBlock54` takes its else arm
and the `'f'` arm's class premise fails there.  The control is one detector at one byte, so
the presence above is a claim about the byte rather than about the document being two long.

The same detector at a high byte (`200`) fails the other way — `200` is in the signed
order's low half, so its span is `lettersSpan`'s — which is why the `'f'` arm's third
premise is the one that separates the two leaves.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchFLetter

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head byte, at the two documents -/

/-- **`"f0"`'s head byte is `102`.**  The staged document's first entry is its first
byte. -/
theorem fHead_cont {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (102 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((102 : UInt8)).toNat = 102 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`"f"`'s head byte is `102`**, in the last entry's form. -/
theorem fHead_last {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (102 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)) := by
  have hreg := seed_reg8 G S s h hInv
  have ht : ((102 : UInt8)).toNat = 102 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-! ### The head class, and the arm's three class premises -/

/-- **`102`'s head class is `defaultValueBracketHigh`**: `91 ≤ 102 < 123`, `93 ≤ 102` and
`102 ≠ 93` — the `NodeBlock19 → NodeBlock11 → LeafBlock9 → sw.default.i` route. -/
theorem fClass_102 : HcontClass (BitVec.ofNat 8 102) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`102` takes the `'f'` arm's class**: the tag test is clear, `102 < 110` and
`102 = 102`. -/
theorem fPrem_102 :
    ((evalICmp .eq (BitVec.ofNat 8 102) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 102 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) ∧
      evalICmp .slt (BitVec.ofNat 8 102) (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .eq (BitVec.ofNat 8 102) (BitVec.ofNat 8 102) = 1 :=
  ⟨by decide, by decide, by decide⟩

/-! ### The arms at the documents -/

/-- **`"f0"`'s head takes the continuing `'f'` arm.**  The class is the document's; the
two segments are the arm's own fields, at their counts. -/
def fLetter_cont_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (102 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm (BitVec.ofNat 8 102)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .fLetter (fHead_cont G S s h hInv) (fPrem_102).1 (fPrem_102).2.1 (fPrem_102).2.2
    hHead hm hmk h8m hTail ht htk htok

/-- **`"f"`'s head takes the last entry's `'f'` arm.** -/
def fLetter_last_arm {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (102 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm (BitVec.ofNat 8 102)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .fLetter (fHead_last G S s h hInv) (fPrem_102).1 (fPrem_102).2.1 (fPrem_102).2.2
    hHead hm hmk h8m hTail ht htk htok

/-! ### The dispatch, through the real `.dispatch` -/

/-- **The dispatch at `"f0"`.**  `HcontArm.dispatch` at the seeded head: the continuing
guard is the document's `0 + 1 < 2`, and the result is the merge the `'f'` route's twenty
links reach. -/
theorem fLetter_cont_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (102 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm (BitVec.ofNat 8 102)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hk : (walkSeed G S).k + 1 < G.nep := by
    rw [h.count]
    show 0 + 1 < 2
    omega
  exact HcontArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hk
    (fLetter_cont_arm G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `"f"`.**  `LastEntryArm.dispatch` at the seeded head: the entry
stream is exhausted (`¬ (0 + 1 < 1)`), and the `'f'` route's nineteen links still reach
the merge. -/
theorem fLetter_last_dispatch {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (102 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 102)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (FC₄₁₃ Cm)
      (FS413 sm (BitVec.ofNat 8 102)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hn : 0 < G.nep := by rw [h.count]; decide
  have hnot : ¬ ((walkSeed G S).k + 1 < G.nep) := by
    rw [h.count]
    show ¬ (0 + 1 < 1)
    omega
  exact LastEntryArm.dispatch (seededInv (S := S) hargs hnext hn) (walkSeed_block G S) hnot
    (fLetter_last_arm G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-! ### The negative control -/

/-- **The letter `'a'` (`97`) is not the `'f'` class**: the tag test is clear and
`97 < 110`, but `eq 97 102` is `0`, so `LeafBlock54` takes its else arm and the `'f'`
arm's third premise fails.  This is the premise that separates this arm from `.letters`,
and the control is about it rather than about the span's pivot. -/
theorem aHead_not_f :
    ¬ (evalICmp .eq (BitVec.ofNat 8 97) (BitVec.ofNat 8 102) = 1) := by
  decide

/-- The same detector at the high byte `200`, which the letters route takes: `200 ≠ 102`,
so `LeafBlock54`'s else arm is the one there too. -/
theorem highHead_not_f :
    ¬ (evalICmp .eq (BitVec.ofNat 8 200) (BitVec.ofNat 8 102) = 1) := by
  decide

/-- **The `'f'` byte's own pivot is set, so the pair above is about the leaf rather than
about the pivot**: `slt 97 110` and `slt 200 110` are both `1`, exactly as `102`'s is. -/
theorem fControl_pivots :
    evalICmp .slt (BitVec.ofNat 8 97) (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .slt (BitVec.ofNat 8 200) (BitVec.ofNat 8 110) = 1 :=
  ⟨by decide, by decide⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.fHead_cont
#print axioms LeanLLVM.Refinement.WalkScope.fHead_last
#print axioms LeanLLVM.Refinement.WalkScope.fClass_102
#print axioms LeanLLVM.Refinement.WalkScope.fPrem_102
#print axioms LeanLLVM.Refinement.WalkScope.fLetter_cont_arm
#print axioms LeanLLVM.Refinement.WalkScope.fLetter_last_arm
#print axioms LeanLLVM.Refinement.WalkScope.fLetter_cont_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.fLetter_last_dispatch
#print axioms LeanLLVM.Refinement.WalkScope.aHead_not_f
#print axioms LeanLLVM.Refinement.WalkScope.highHead_not_f
#print axioms LeanLLVM.Refinement.WalkScope.fControl_pivots

end WalkScope
end LeanLLVM.Refinement
