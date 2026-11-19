/-
The letters route's domain, at staged documents; and the continuing high-byte class.

## What is exhibited

Two documents whose head byte is a **letter** and a **high byte** — the two distinct head
switch classes the route's span sits under:

| document | head byte | `HcontClass` | route |
|---|---|---|---|
| `"a0"` | `97` (`'a'`) | `defaultValueBracketHigh` | `NodeBlock21 → NodeBlock19 → NodeBlock11 → LeafBlock9 → sw.default.i` |
| `\xC8 0` | `200` | `defaultValueLow` | `NodeBlock21 → NodeBlock5 → LeafBlock → sw.default.i` |

Both satisfy the arm's class premises — the tag test clear, `slt %8 110 = 1`, `%8 ≠ 102` —
and both take `lettersSpan`'s four links below `if.else387.i`.  The class is read off the
staged document (`WalkGeom.doc`, `WalkGeom.entries`, `entryByte`/`entryPos`) and the state
is the seed's own handoff (`walkSeedInvariant_geometry`), so the byte facts are facts about
the input.

The arm's two **segments** enter as hypotheses, exactly as they are fields of the arm: the
head's chain to `if.else387.i` (twelve links) and the tail's three calls.  They are the
per-class work — the head's four pivots pick different blocks for `97` and `200`, which is
why they are not one composition — and what the dispatch below exercises is everything the
arm composes: the span, the merge, its three cells and its price.

## The negative control

The same two documents' byte tests at a **digit** (`0x30`): `slt 48 110 = 1` and `48 ≠ 102`
hold, but the tag test is `1` — the plain-value arm's class — so the letters arm's class
premise fails there.  The control is one detector at one byte, so the presence above is a
claim about the byte rather than about the document being two long.

## The continuing high-byte class

`126` and `127` are `HcontClass.defaultValueHigh`, and the arm that carries them is
`HcontArm.cleanup` — the bundle's four class bits are `slt %8 91 = 0`,
`slt %8 123 = 0`, `slt %8 125 = 0` and `%8 ≠ 125`, which leave exactly those two bytes.
They are *not* the letters class: `slt 126 110 = 0`, so the span below `if.else387.i` is the
longer `NodeBlock60 → LeafBlock58` one and not `lettersSpan`.  The high-byte route is the
refusal's (`walkRevolutionMergeSeg`'s class); the old whitespace composition was retired
with that route, and what this module adds is the class evidence at a staged document.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchOpenersDomain
import LeanLLVM.Refinement.JsonStage2WalkDispatchSpansOfStaging
import LeanLLVM.Refinement.JsonStage2WalkDispatchLetters

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.JsonEntryIR (readLanes32)

namespace WalkScope

/-! ### The two staged documents -/

/-- **A two-entry document whose first byte is `c`**, the second a digit: the lanes are `0`
and `1`, so the first entry is the document's first byte and the stream has an entry left —
the continuing level's guard. -/
abbrev LettersDocument {m0 : Mem} (G : WalkGeom m0) (c : UInt8) : Prop :=
  TwoEntryHeadDocument G c

/-- The letter `'a'`'s document's head byte is `97`. -/
theorem lettersHead_a {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : LettersDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((97 : UInt8)).toNat = 97 := by decide
  rw [ht] at hreg
  walk_read using hreg

/-- The high byte `200`'s document's head byte is `200`. -/
theorem lettersHead_high {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : LettersDocument G (200 : UInt8)) (hInv : WalkInv G (walkSeed G S) s) :
    evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)) := by
  have hreg := seed_head_byte G S s (hc := h.entryByte_zero) hInv
  have ht : ((200 : UInt8)).toNat = 200 := by decide
  rw [ht] at hreg
  walk_read using hreg

/-! ### The two head classes -/

/-- **`'a'`'s head class is `defaultValueBracketHigh`**: `91 ≤ 97 < 123`, `93 ≤ 97` and
`97 ≠ 93` — the `NodeBlock19 → NodeBlock11 → LeafBlock9` route. -/
theorem lettersClass_a : HcontClass (BitVec.ofNat 8 97) :=
  .defaultValueBracketHigh (by decide) (by decide) (by decide) (by decide)

/-- **`200`'s head class is `defaultValueLow`**: `200` is negative in the signed order, so
`slt 200 91 = 1`, `slt 200 44 = 1` and `200 ≠ 34` — the `NodeBlock5 → LeafBlock` route. -/
theorem lettersClass_high : HcontClass (BitVec.ofNat 8 200) :=
  .defaultValueLow (by decide) (by decide) (by decide)

/-! ### The arm's class premises at the two documents -/

/-- **`'a'` takes the letters arm's class**: the tag test is clear, `97 < 110` and
`97 ≠ 102`. -/
theorem lettersPrem_a :
    ((evalICmp .eq (BitVec.ofNat 8 97) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 97 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) ∧
      evalICmp .slt (BitVec.ofNat 8 97) (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .eq (BitVec.ofNat 8 97) (BitVec.ofNat 8 102) = 0 :=
  ⟨by decide, by decide, by decide⟩

/-- **`200` takes the letters arm's class**, by the same three tests. -/
theorem lettersPrem_high :
    ((evalICmp .eq (BitVec.ofNat 8 200) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 200 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) ∧
      evalICmp .slt (BitVec.ofNat 8 200) (BitVec.ofNat 8 110) = 1 ∧
      evalICmp .eq (BitVec.ofNat 8 200) (BitVec.ofNat 8 102) = 0 :=
  ⟨by decide, by decide, by decide⟩

/-! ### The arms at the documents -/

/-- **`"a0"`'s head takes the continuing letters arm.**  The class is the document's; the
two segments are the arm's own fields, at their counts. -/
def letters_cont_arm_a {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : LettersDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 97)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  hcontArm_letters_of_staging (walkSeed G S) s hInv
    (hlastByte_of_reg8 hInv (lettersHead_a G S s h hInv))
    (lettersPrem_a).1 (lettersPrem_a).2.1 (lettersPrem_a).2.2
    hHead (by omega) hm hmk h8m hTail ht htk htok

/-- **`\xC8 0`'s head takes the continuing letters arm**, on the other head class.

**The class's route is eleven, and the segment is taken at it.**  `.defaultValueLow`
takes `NodeBlock5 → LeafBlock → sw.default.i` — three pivots, where
`.defaultValueBracketHigh` takes four — so the segment to `if.else387.i` is eleven links
(`contLowHeadSeg`, `JsonStage2WalkDispatchLettersHead`), and that is the hypothesis below.
The arm's field is the counted one (`nH` with `nH ≤ 12`), so the class's own chain feeds it
as `nH = 11`; the twelve belongs to the four-pivot classes and no such segment exists here.
`lettersCleanupMerge_at` and the constructor both take the pair, so nothing above the arm
supplies a count of its own. -/
def letters_cont_arm_high {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : LettersDocument G (200 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 200)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    HcontArm (stage2Calls stage2SubCalls) G (walkSeed G S) s :=
  hcontArm_letters_of_staging (walkSeed G S) s hInv
    (hlastByte_of_reg8 hInv (lettersHead_high G S s h hInv))
    (lettersPrem_high).1 (lettersPrem_high).2.1 (lettersPrem_high).2.2
    hHead (by omega) hm hmk h8m hTail ht htk htok

/-! ### The dispatch, through the real `.dispatch` -/

/-- **The dispatch at `"a0"`.**  `HcontArm.dispatch` at the seeded head: the continuing
guard is the document's `0 + 1 < 2`, and the result is the merge the letters route's
twenty links reach. -/
theorem letters_cont_dispatch_a {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : LettersDocument G (97 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 12)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 97)) Ct st 3)
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
    (letters_cont_arm_a G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at `\xC8 0`.**  The same arm at the high byte's route, whose head chain
is the other class's — eleven links, so that is the hypothesis. -/
theorem letters_cont_dispatch_high {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : LettersDocument G (200 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 200)) Ct st 3)
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
    (letters_cont_arm_high G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-! ### The negative control -/

/-- **The digit `48` is not the letters class**: its tag test is `1`, so the arm's first
class premise fails.  (Its `slt 110` bit is `1` and `48 ≠ 102`, so the control is about the
tag test rather than about the span's pivot.) -/
theorem digitHead_not_letters :
    ¬ ((evalICmp .eq (BitVec.ofNat 8 48) (BitVec.ofNat 8 45) |||
        evalICmp .ult (BitVec.ofNat 8 48 + BitVec.ofNat 8 208) (BitVec.ofNat 8 10)) = 0) := by
  decide

/-! ### The continuing high-byte class, at its staged documents -/

/-- **`126` and `127` are `defaultValueHigh`**: `91 ≤ %8`, `123 ≤ %8`, `125 ≤ %8` and
`%8 ≠ 125` in the signed order leave exactly those two bytes. -/
theorem highByteClass_126 : HcontClass (BitVec.ofNat 8 126) :=
  .defaultValueHigh (by decide) (by decide) (by decide) (by decide)

/-- The same class at `127`. -/
theorem highByteClass_127 : HcontClass (BitVec.ofNat 8 127) :=
  .defaultValueHigh (by decide) (by decide) (by decide) (by decide)

/-- **The four class bits the high-byte bundles carry hold at `126` and `127`.**  These are
`HcontFacts`'s `hlt91`/`hlt123`/`hlt125`/`hne125` and `HcontCleanupFacts`'s same four, so the
class the arms `ws`/`cleanup` dispatch is the class the census names. -/
theorem highByteBits_126 :
    evalICmp .slt (BitVec.ofNat 8 126) (BitVec.ofNat 8 91) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 126) (BitVec.ofNat 8 123) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 126) (BitVec.ofNat 8 125) = 0 ∧
      evalICmp .eq (BitVec.ofNat 8 126) (BitVec.ofNat 8 125) = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The same four bits at `127`. -/
theorem highByteBits_127 :
    evalICmp .slt (BitVec.ofNat 8 127) (BitVec.ofNat 8 91) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 127) (BitVec.ofNat 8 123) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 127) (BitVec.ofNat 8 125) = 0 ∧
      evalICmp .eq (BitVec.ofNat 8 127) (BitVec.ofNat 8 125) = 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- **The high-byte class is not the letters class**: `slt 126 110 = 0`, so the span below
`if.else387.i` is the longer `NodeBlock60` one and `lettersSpan` does not apply.  This is the
`not 126/127` the letters arm's docstring names. -/
theorem highByte_not_letters :
    evalICmp .slt (BitVec.ofNat 8 126) (BitVec.ofNat 8 110) = 0 ∧
      evalICmp .slt (BitVec.ofNat 8 127) (BitVec.ofNat 8 110) = 0 :=
  ⟨by decide, by decide⟩

/-! ### The last entry's arm, at the one-entry documents

`"a"` is `OneByteDocument G (97 : UInt8)` — the entry stream is exhausted after the
opener, so the level is the last entry's — and `\xC8` is the same document at the high
byte.  The arm's two segments are its own fields, at their counts; what the dispatch below
exercises is the span, the merge and its cells. -/

/-- **`"a"`'s head takes the last entry's letters arm.** -/
def letters_last_arm_a {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (97 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 97)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have hreg := seed_reg8 G S s h hInv
  have ht' : ((97 : UInt8)).toNat = 97 := by decide
  rw [ht'] at hreg
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)) := by
    walk_read using hreg
  exact lastEntryArm_letters_of_staging (walkSeed G S) s hInv
    (hlastByte_of_reg8 hInv h8) (lettersPrem_a).1 (lettersPrem_a).2.1 (lettersPrem_a).2.2
    hHead (by omega) hm hmk h8m hTail ht htk htok

/-- **The high byte's document takes the last entry's letters arm.** -/
def letters_last_arm_high {m0 : Mem} (G : WalkGeom m0) (S : WalkStage G) (s : State)
    (h : OneByteDocument G (200 : UInt8)) (hInv : WalkInv G (walkSeed G S) s)
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S) s Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 200)) Ct st 3)
    (ht : Ct.block = "if.end473.i") (htk : Ct.k = (walkSeed G S).k)
    (htok : lookupName st.env "%t352.i" = some (.ptr tok)) :
    LastEntryArm (stage2Calls stage2SubCalls) G (walkSeed G S) s := by
  have hreg := seed_reg8 G S s h hInv
  have ht' : ((200 : UInt8)).toNat = 200 := by decide
  rw [ht'] at hreg
  have h8 : evalOperand s (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)) := by
    walk_read using hreg
  exact lastEntryArm_letters_of_staging (walkSeed G S) s hInv
    (hlastByte_of_reg8 hInv h8) (lettersPrem_high).1 (lettersPrem_high).2.1
    (lettersPrem_high).2.2 hHead (by omega) hm hmk h8m hTail ht htk htok

/-- **The dispatch at `"a"`.**  `LastEntryArm.dispatch` at the seeded head: the entry
stream is exhausted (`¬ (0 + 1 < 1)`), and the letters route's nineteen links still reach
the merge. -/
theorem letters_last_dispatch_a {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (97 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 97)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 97)) Ct st 3)
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
    (letters_last_arm_a G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-- **The dispatch at the high byte's one-entry document.** -/
theorem letters_last_dispatch_high {args : List Value} {m0 : Mem} {next : Nat}
    {G : WalkGeom m0} {S : WalkStage G}
    (hargs : args = [.ptr G.b, .int 64 (BitVec.ofNat 64 G.n), .ptr G.ep,
      .int 64 (BitVec.ofNat 64 G.nep), .ptr G.xp, .int 64 (BitVec.ofNat 64 G.nxp),
      .ptr G.dst, .int 64 (BitVec.ofNat 64 G.dstcap), .ptr G.ndst, .ptr G.ev,
      .int 64 (BitVec.ofNat 64 G.evcap), .ptr G.nev, .ptr G.err])
    (hnext : G.next0 = next) (h : OneByteDocument G (200 : UInt8))
    {Cm : WalkCarry G} {sm : State}
    (hHead : WalkSegment (stage2Calls stage2SubCalls) G (walkSeed G S)
      (openerHead G S args next) Cm sm 11)
    (hm : Cm.block = "if.else387.i") (hmk : Cm.k = (walkSeed G S).k)
    (h8m : evalOperand sm (.reg "%8") = some (.int 8 (BitVec.ofNat 8 200)))
    {Ct : WalkCarry G} {st : State} {tok : Nat}
    (hTail : WalkSegment (stage2Calls stage2SubCalls) G (HeadC₄₁₃ (LetC₄₀₅ Cm))
      (LetS413 sm (BitVec.ofNat 8 200)) Ct st 3)
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
    (letters_last_arm_high G S _ h (seededInv (S := S) hargs hnext hn)
      hHead hm hmk h8m hTail ht htk htok)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.lettersHead_a
#print axioms LeanLLVM.Refinement.WalkScope.lettersHead_high
#print axioms LeanLLVM.Refinement.WalkScope.lettersClass_a
#print axioms LeanLLVM.Refinement.WalkScope.lettersClass_high
#print axioms LeanLLVM.Refinement.WalkScope.lettersPrem_a
#print axioms LeanLLVM.Refinement.WalkScope.lettersPrem_high
#print axioms LeanLLVM.Refinement.WalkScope.letters_cont_arm_a
#print axioms LeanLLVM.Refinement.WalkScope.letters_cont_arm_high
#print axioms LeanLLVM.Refinement.WalkScope.letters_cont_dispatch_a
#print axioms LeanLLVM.Refinement.WalkScope.letters_cont_dispatch_high
#print axioms LeanLLVM.Refinement.WalkScope.digitHead_not_letters
#print axioms LeanLLVM.Refinement.WalkScope.letters_last_arm_a
#print axioms LeanLLVM.Refinement.WalkScope.letters_last_arm_high
#print axioms LeanLLVM.Refinement.WalkScope.letters_last_dispatch_a
#print axioms LeanLLVM.Refinement.WalkScope.letters_last_dispatch_high
#print axioms LeanLLVM.Refinement.WalkScope.highByteClass_126
#print axioms LeanLLVM.Refinement.WalkScope.highByteClass_127
#print axioms LeanLLVM.Refinement.WalkScope.highByteBits_126
#print axioms LeanLLVM.Refinement.WalkScope.highByteBits_127
#print axioms LeanLLVM.Refinement.WalkScope.highByte_not_letters
#print axioms LeanLLVM.Refinement.WalkScope.lettersSpan
#print axioms LeanLLVM.Refinement.WalkScope.lettersCleanupMerge_at

end WalkScope
end LeanLLVM.Refinement
