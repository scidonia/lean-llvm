/-
The class-C leaves' domain, at staged documents.

## What is exhibited

The class-C span's four routes, each at a document whose head byte selects it:

| document | head byte | route below `if.else387.i` | span | kind |
|---|---|---|---|---|
| `"n0"` | `110` (`'n'`) | `LeafBlock56`'s eq set, `if.then403.i` | `c56TrueSpan` | `10` |
| `"o0"` | `111` (`'o'`) | `LeafBlock56`'s eq clear, `if.else405.i` | `c56ElseSpan` | `0` |
| `"t0"` | `116` (`'t'`) | `LeafBlock58`'s eq set, straight to `if.then413.i` | `c58TrueSpan` | `8` |
| `"u0"` | `117` (`'u'`) | `LeafBlock58`'s eq clear, `if.else405.i` | `c58ElseSpan` | `0` |

`"n"` and `"u"` are the last entry's level for the two leaves (`LastEntryArm.classC`); the
four continuing heads are `HcontArm.classC`'s.

Each arm's **span is proved at the document**, not assumed: the span field is the byte's
own theorem applied at the head segment's endpoint, whose invariant is the head's.  The
byte facts are read off the staged document (`WalkGeom.doc`, `WalkGeom.entries`,
`entryByte`/`entryPos`), so the class premises are facts about the input.  The two
segments the arm carries — the head's chain to `if.else387.i` and the tail's three calls on
their empty arm — enter as hypotheses, exactly as they are fields of the arm.

## The negative controls

Two, at the two ends of the class:

* the letter `'a'` (`97`) has `slt 97 110 = 1`, so the arm's first class premise fails —
  its span is `lettersSpan`'s, not the class-C span's;
* `126` has `slt 126 125 = 0` **and** `126 ≠ 125`, so the arm's upper premise fails — it
  is `.ws`/`.cleanup`'s byte, the preserved high-byte route.  This is the `126`/`127`
  exclusion stated at the arm's own bit rather than in prose.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchArmsDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchClassC

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The head bytes, at the documents -/

/-- **`110`'s head byte**, read off the two-entry document. -/
theorem cHead_110 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (110 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((110 : UInt8)).toNat = 110 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`111`'s head byte**. -/
theorem cHead_111 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (111 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 111)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((111 : UInt8)).toNat = 111 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`116`'s head byte**. -/
theorem cHead_116 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (116 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 116)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((116 : UInt8)).toNat = 116 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`117`'s head byte**. -/
theorem cHead_117 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (117 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((117 : UInt8)).toNat = 117 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`110`'s head byte at the last entry's document.** -/
theorem cHead_last_110 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (110 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)) := by
  have hreg := seed_reg8 G S s h hInv
  have ht : ((110 : UInt8)).toNat = 110 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-- **`117`'s head byte at the last entry's document.** -/
theorem cHead_last_117 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (117 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)) := by
  have hreg := seed_reg8 G S s h hInv
  have ht : ((117 : UInt8)).toNat = 117 := by decide
  rw [ht] at hreg
  simpa only [evalOperand] using hreg

/-! ### The head class, at the four bytes -/

/-- **`110`'s head class is `defaultValueBracketHigh`**: `91 ≤ 110 < 123`, `93 ≤ 110` and
`110 ≠ 93`. -/
theorem cClass_110 : HcontClass (BitVec.ofNat 8 110) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`111`'s head class is `defaultValueBracketHigh`.** -/
theorem cClass_111 : HcontClass (BitVec.ofNat 8 111) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`116`'s head class is `defaultValueBracketHigh`.** -/
theorem cClass_116 : HcontClass (BitVec.ofNat 8 116) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`117`'s head class is `defaultValueBracketHigh`.** -/
theorem cClass_117 : HcontClass (BitVec.ofNat 8 117) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-! ### The arms at the four continuing documents

Each arm's span is the byte's own theorem at the head segment's endpoint, and its three
class bits are the byte's. -/

/-- **`"n0"`'s head takes the continuing class-C arm**, on `LeafBlock56`'s true arm. -/
def classC_cont_arm_110 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (110 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ ClsC₄₀₃ Cm with block := "if.then413.i" }) (ClsS413T sm (BitVec.ofNat 8 110))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_110 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c56TrueSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-- **`"o0"`'s head takes the continuing class-C arm**, on `LeafBlock56`'s else arm. -/
def classC_cont_arm_111 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (111 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 111)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ClsC₄₀₅ Cm))
      (ClsS413F sm (BitVec.ofNat 8 111)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_111 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c56ElseSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-- **`"t0"`'s head takes the continuing class-C arm**, on `LeafBlock58`'s true arm. -/
def classC_cont_arm_116 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (116 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 116)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ HeadC₅₈ Cm with block := "if.then413.i" }) (ClsS58T sm (BitVec.ofNat 8 116))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_116 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c58TrueSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-- **`"u0"`'s head takes the continuing class-C arm**, on `LeafBlock58`'s else arm. -/
def classC_cont_arm_117 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : TwoEntryHeadDocument G (117 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ Cm)
      (HeadS413 sm (BitVec.ofNat 8 117)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_117 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c58ElseSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-! ### The dispatch, through the real `.dispatch` -/

/-- **The dispatch at `"n0"`**, through the real `HcontArm.dispatch`. -/
theorem classC_cont_dispatch_110 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (110 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ ClsC₄₀₃ Cm with block := "if.then413.i" }) (ClsS413T sm (BitVec.ofNat 8 110))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact HcontArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show 0 + 1 < 2; omega)
    (classC_cont_arm_110 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `"o0"`.** -/
theorem classC_cont_dispatch_111 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (111 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 111)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (ClsC₄₀₅ Cm))
      (ClsS413F sm (BitVec.ofNat 8 111)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact HcontArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show 0 + 1 < 2; omega)
    (classC_cont_arm_111 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `"t0"`.** -/
theorem classC_cont_dispatch_116 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (116 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 116)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ HeadC₅₈ Cm with block := "if.then413.i" }) (ClsS58T sm (BitVec.ofNat 8 116))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact HcontArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show 0 + 1 < 2; omega)
    (classC_cont_arm_116 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `"u0"`.** -/
theorem classC_cont_dispatch_117 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : TwoEntryHeadDocument G (117 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ Cm)
      (HeadS413 sm (BitVec.ofNat 8 117)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact HcontArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show 0 + 1 < 2; omega)
    (classC_cont_arm_117 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-! ### The last entry's arm, at the two leaves' documents -/

/-- **`"n"`'s head takes the last entry's class-C arm** (`LeafBlock56`'s true arm). -/
def classC_last_arm_110 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (110 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ ClsC₄₀₃ Cm with block := "if.then413.i" }) (ClsS413T sm (BitVec.ofNat 8 110))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_last_110 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c56TrueSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-- **`"u"`'s head takes the last entry's class-C arm** (`LeafBlock58`'s else arm). -/
def classC_last_arm_117 {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (117 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ Cm)
      (HeadS413 sm (BitVec.ofNat 8 117)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  .classC (cHead_last_117 G S s h hInv) (by decide) (Or.inl (by decide))
    hHead hm hmk h8m
    (c58ElseSpan G Cm sm hHead.inv' hm h8m (by decide) (by decide) (by decide))
    rfl (by decide) hTail ht htk htok

/-- **The dispatch at `"n"`**, through the real `LastEntryArm.dispatch`. -/
theorem classC_last_dispatch_110 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (110 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 110)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G
      ({ ClsC₄₀₃ Cm with block := "if.then413.i" }) (ClsS413T sm (BitVec.ofNat 8 110))
      Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact LastEntryArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show ¬ (0 + 1 < 1); omega)
    (classC_last_arm_110 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `"u"`.** -/
theorem classC_last_dispatch_117 {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (117 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 117)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ Cm)
      (HeadS413 sm (BitVec.ofNat 8 117)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    WalkDispatchResult (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) := by
  have hInv := seededInv (S := S) hargs hnext (by rw [h.count]; decide)
  exact LastEntryArm.dispatch hInv (walkSeed_block G S)
    (by rw [h.count]; show ¬ (0 + 1 < 1); omega)
    (classC_last_arm_117 G S _ h hInv hHead hm hmk h8m hTail ht htk htok)

/-! ### The negative controls -/

/-- **The letter `'a'` (`97`) is below the class**: `slt 97 110 = 1`, so the arm's first
premise fails and its span is `lettersSpan`'s rather than the class-C span's. -/
theorem aHead_not_classC :
    ¬ (evalICmp .slt (BitVec.ofNat 8 97) (BitVec.ofNat 8 110) = 0) := by
  decide

/-- **`126` is above the class**: `slt 126 125 = 0` and `126 ≠ 125`, so the arm's upper
premise fails.  That is the `126`/`127` exclusion — the bytes `.ws`/`.cleanup` carry —
stated at the arm's own bit. -/
theorem highByte_not_classC :
    ¬ (evalICmp .slt (BitVec.ofNat 8 126) (BitVec.ofNat 8 125) = 1 ∨
      evalICmp .eq (BitVec.ofNat 8 126) (BitVec.ofNat 8 125) = 1) := by
  decide

/-- **The class's own boundary bytes are in it**: `110` and `125` satisfy both premises,
so the control's two failures above are about the range rather than about one literal. -/
theorem classC_bounds :
    evalICmp .slt (BitVec.ofNat 8 110) (BitVec.ofNat 8 110) = 0 ∧
      (evalICmp .slt (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1 ∨
        evalICmp .eq (BitVec.ofNat 8 125) (BitVec.ofNat 8 125) = 1) :=
  ⟨by decide, Or.inr (by decide)⟩

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.cHead_110
#print axioms LeanLLVM.Refinement.WalkScope.cHead_111
#print axioms LeanLLVM.Refinement.WalkScope.cHead_116
#print axioms LeanLLVM.Refinement.WalkScope.cHead_117
#print axioms LeanLLVM.Refinement.WalkScope.cHead_last_110
#print axioms LeanLLVM.Refinement.WalkScope.cHead_last_117
#print axioms LeanLLVM.Refinement.WalkScope.cClass_110
#print axioms LeanLLVM.Refinement.WalkScope.cClass_111
#print axioms LeanLLVM.Refinement.WalkScope.cClass_116
#print axioms LeanLLVM.Refinement.WalkScope.cClass_117
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_arm_110
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_arm_111
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_arm_116
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_arm_117
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_dispatch_110
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_dispatch_111
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_dispatch_116
#print axioms LeanLLVM.Refinement.WalkScope.classC_cont_dispatch_117
#print axioms LeanLLVM.Refinement.WalkScope.classC_last_arm_110
#print axioms LeanLLVM.Refinement.WalkScope.classC_last_arm_117
#print axioms LeanLLVM.Refinement.WalkScope.classC_last_dispatch_110
#print axioms LeanLLVM.Refinement.WalkScope.classC_last_dispatch_117
#print axioms LeanLLVM.Refinement.WalkScope.aHead_not_classC
#print axioms LeanLLVM.Refinement.WalkScope.highByte_not_classC
#print axioms LeanLLVM.Refinement.WalkScope.classC_bounds

end WalkScope
end LeanLLVM.Refinement
