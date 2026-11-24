/-
The model's six-row case table for `od_gap_recover`.

`JsonStage2HelperOdGap` states the rule (`gapRecoverWrite`) and a table of
witnesses that holds of it (`gapCases_sound`).  This module restates that table
as theorems about the rule at the model's own predicates, one row per site the
helper's text reaches, with the staging `stage2GapRecoverRule` reads as the
pre: the cursor's six words at `c`, the index selection that yields `ip`,
`pos ≤ ip`, and the document window `[0, ip)`.

Each row concludes the two things a caller observes: the rule's answer
(`some .unchanged` or `some (.wrote e off tag)`), and — for a write — the three
record words at `e`, `e + 8` and `e + 16` after the effect.  The no-write row
states the `Stage2GapRecoverPost` at the unchanged memory instead.

The rows are the model's.  Nothing here runs the emitted body, so the
transcription-to-instructions distance stays the trust row `docs/contract.md`
records for this helper.
-/
import LeanLLVM.Refinement.JsonStage2HelperOdGap

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace LeanLLVM.Refinement

open LeanLLVM

/-! ### The first-byte classes

`gapAfterLoop` spells its dispatch as tests on the token's first byte.  The
predicates below name those tests so a row states its hypothesis at the class
rather than at the comparison it expands to.
-/

/-- The number arm's first-byte test: `-` or a digit. -/
def gapNumStart (ch : UInt8) : Prop :=
  ch = 0x2D ∨ (0x30 ≤ ch ∧ ch ≤ 0x39)

/-- A literal arm's first-byte test, paired with the literal that arm compares. -/
def gapLitStart (ch : UInt8) (lit : List UInt8) : Prop :=
  (ch = 0x74 ∧ lit = gapTrueLit) ∨
    (ch = 0x66 ∧ lit = gapFalseLit) ∨
      (ch = 0x6E ∧ lit = gapNullLit)

/-- The scalar refusal's first-byte class: none of the four arms above. -/
def gapScalarStart (ch : UInt8) : Prop :=
  ¬ gapNumStart ch ∧ ch ≠ 0x74 ∧ ch ≠ 0x66 ∧ ch ≠ 0x6E

/-! ### The observable of a row

The rule's answer and, for a write, the record's three words after the effect.
`stage2ErrSetMsg` writes `ok = 0` at `e`, the offset at `e + 8` and the message
word at `e + 16`; `GapRecoverEffect.wrote` is that write.
-/

/-- A write's record words: the kind word, the offset and the tag. -/
theorem gapWrote_record (mem : Mem) (e off tag : Nat) :
    readBytes ((GapRecoverEffect.wrote e off tag).apply mem) e 4 = some (wordBytes 4 0) ∧
      readBytes ((GapRecoverEffect.wrote e off tag).apply mem) (e + 8) 8 =
        some (wordBytes 8 off) ∧
      readBytes ((GapRecoverEffect.wrote e off tag).apply mem) (e + 16) 8 =
        some (wordBytes 8 tag) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [GapRecoverEffect.apply] using stage2ErrSetMsg_ok_read mem e off tag
  · simpa only [GapRecoverEffect.apply] using stage2ErrSetMsg_off_read mem e off tag
  · simpa only [GapRecoverEffect.apply] using stage2ErrSetMsg_msg_read mem e off tag

/-- **A refusal row's observable**: the rule answers `some (.wrote e off tag)`
and the record reads back `(0, off, tag)` at its three words. -/
def GapRuleWrote (mem : Mem) (c pos e off tag : Nat) : Prop :=
  stage2GapRecoverRule mem c pos = some (.wrote e off tag) ∧
    readBytes ((GapRecoverEffect.wrote e off tag).apply mem) e 4 = some (wordBytes 4 0) ∧
      readBytes ((GapRecoverEffect.wrote e off tag).apply mem) (e + 8) 8 =
        some (wordBytes 8 off) ∧
      readBytes ((GapRecoverEffect.wrote e off tag).apply mem) (e + 16) 8 =
        some (wordBytes 8 tag)

/-- **The no-write row's observable**: the rule answers `some .unchanged`, the
memory comes back unchanged, and the call boundary's post holds at it. -/
def GapRuleUnchanged (mem : Mem) (next c pos : Nat) : Prop :=
  stage2GapRecoverRule mem c pos = some .unchanged ∧
    (GapRecoverEffect.unchanged).apply mem = mem ∧
      Stage2GapRecoverPost mem next c pos { ret := voidRet, mem := mem, next := next }

/-! ### The staging reduction

The definition is a match on the cursor's six words, the index selection and the
window.  The two lemmas below factor that reduction out of the rows: given the
staging and the rule's answer at the window, they return the rule's effect.
-/

/-- The staging reduction, no-write side. -/
theorem gapRule_stage_none {mem : Mem} {c pos ip b n ix nix k e : Nat} {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hw : gapRecoverWrite win ip pos = GapWrite.none) :
    stage2GapRecoverRule mem c pos = some .unchanged := by
  unfold stage2GapRecoverRule
  simp only [odGapCurN, odGapCurIx, odGapCurNix, odGapCurK, odGapCurE,
    hb, hn, hix, hnix, hk, he]
  by_cases hklt : k < nix
  · simp only [ite_eq_left hklt, hidx hklt, hbytes, hw]
  · simp only [ite_eq_right hklt, ← hnip (by omega), hbytes, hw]

/-- The staging reduction, write side. -/
theorem gapRule_stage_err {mem : Mem} {c pos ip b n ix nix k e off tag : Nat}
    {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hw : gapRecoverWrite win ip pos = GapWrite.err off tag) :
    stage2GapRecoverRule mem c pos = some (.wrote e off tag) := by
  unfold stage2GapRecoverRule
  simp only [odGapCurN, odGapCurIx, odGapCurNix, odGapCurK, odGapCurE,
    hb, hn, hix, hnix, hk, he]
  by_cases hklt : k < nix
  · simp only [ite_eq_left hklt, hidx hklt, hbytes, hw]
  · simp only [ite_eq_right hklt, ← hnip (by omega), hbytes, hw]

/-! ### The six rows -/

/-- **Row 1 — no write.**  The first scan reaches `ip` (`gapEe … = ip`), and the
helper returns with the caller's memory unchanged. -/
theorem gapRule_unchanged {mem : Mem} {next c pos ip b n ix nix k e : Nat}
    {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (h : gapEe win ip pos = ip) :
    GapRuleUnchanged mem next c pos := by
  have hw : gapRecoverWrite win ip pos = GapWrite.none := by
    simp [gapRecoverWrite, h]
  have hrule : stage2GapRecoverRule mem c pos = some .unchanged :=
    gapRule_stage_none hb hn hix hnix hk he hidx hnip hbytes hw
  unfold GapRuleUnchanged Stage2GapRecoverPost
  exact ⟨hrule, rfl, rfl, rfl, .unchanged, hrule, rfl⟩

/-- **Row 2 — the number refusal.**  The first scan stops at `ee` strictly
before `ip`, the token's first byte is a minus or a digit, and the lexeme is not
a valid number: the record is written at `pos + ei`, `ei` the lexical scan's
stop, with the number tag. -/
theorem gapRule_numberRefusal {mem : Mem} {c pos ip b n ix nix k e ee : Nat}
    {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (hch : gapNumStart (win.getD pos 0))
    (hnum : (numLexScan (gapSegment win pos ee)).2 = false)
    (hee : gapEe win ip pos = ee)
    (hlt : ee < ip) :
    GapRuleWrote mem c pos e (pos + (numLexScan (gapSegment win pos ee)).1)
      gapTagNumber := by
  have hw : gapRecoverWrite win ip pos =
      GapWrite.err (pos + (numLexScan (gapSegment win pos ee)).1) gapTagNumber := by
    unfold gapNumStart at hch
    simp only [gapRecoverWrite, hee]
    rw [ite_eq_right hlt.ne]
    simp only [gapAfterLoop]
    rw [ite_eq_left hch]
    simp [hnum]
  unfold GapRuleWrote
  exact ⟨gapRule_stage_err hb hn hix hnix hk he hidx hnip hbytes hw,
    gapWrote_record mem e (pos + (numLexScan (gapSegment win pos ee)).1) gapTagNumber⟩

/-- **Row 3 — the extra token after an accepted number.**  The lexeme is a valid
number, so the unconditional second-token refusal runs at `gapS2` with the extra
tag. -/
theorem gapRule_numberExtra {mem : Mem} {c pos ip b n ix nix k e ee : Nat}
    {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (hch : gapNumStart (win.getD pos 0))
    (hnum : (numLexScan (gapSegment win pos ee)).2 = true)
    (hee : gapEe win ip pos = ee)
    (hlt : ee < ip) :
    GapRuleWrote mem c pos e (gapS2 win ip ee) gapTagExtra := by
  have hw : gapRecoverWrite win ip pos = GapWrite.err (gapS2 win ip ee) gapTagExtra := by
    unfold gapNumStart at hch
    simp only [gapRecoverWrite, hee]
    rw [ite_eq_right hlt.ne]
    simp only [gapAfterLoop]
    rw [ite_eq_left hch]
    simp [hnum, gapExtraWrite]
  unfold GapRuleWrote
  exact ⟨gapRule_stage_err hb hn hix hnix hk he hidx hnip hbytes hw,
    gapWrote_record mem e (gapS2 win ip ee) gapTagExtra⟩

/-- **Row 4 — the literal refusal.**  A literal arm's first byte selects the
literal, and `litCheck` stops at `i`: the record is written at `pos + i` with
the literal tag. -/
theorem gapRule_literalRefusal {mem : Mem} {c pos ip b n ix nix k e ee i : Nat}
    {win : List UInt8} {lit : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (hch : gapLitStart (win.getD pos 0) lit)
    (hlit : litCheck (gapSegment win pos ee) lit = some i)
    (hee : gapEe win ip pos = ee)
    (hlt : ee < ip) :
    GapRuleWrote mem c pos e (pos + i) gapTagLiteral := by
  have hw : gapRecoverWrite win ip pos = GapWrite.err (pos + i) gapTagLiteral := by
    unfold gapLitStart at hch
    rcases hch with ⟨hch, hlit'⟩ | ⟨hch, hlit'⟩ | ⟨hch, hlit'⟩
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit]
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit]
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit]
  unfold GapRuleWrote
  exact ⟨gapRule_stage_err hb hn hix hnix hk he hidx hnip hbytes hw,
    gapWrote_record mem e (pos + i) gapTagLiteral⟩

/-- **Row 5 — the extra token after an accepted literal.**  The literal matches,
so the unconditional second-token refusal runs at `gapS2` with the extra tag. -/
theorem gapRule_literalExtra {mem : Mem} {c pos ip b n ix nix k e ee : Nat}
    {win : List UInt8} {lit : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (hch : gapLitStart (win.getD pos 0) lit)
    (hlit : litCheck (gapSegment win pos ee) lit = none)
    (hee : gapEe win ip pos = ee)
    (hlt : ee < ip) :
    GapRuleWrote mem c pos e (gapS2 win ip ee) gapTagExtra := by
  have hw : gapRecoverWrite win ip pos = GapWrite.err (gapS2 win ip ee) gapTagExtra := by
    unfold gapLitStart at hch
    rcases hch with ⟨hch, hlit'⟩ | ⟨hch, hlit'⟩ | ⟨hch, hlit'⟩
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit, gapExtraWrite]
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit, gapExtraWrite]
    · subst hlit'
      simp only [gapRecoverWrite, hee]
      rw [ite_eq_right hlt.ne]
      simp only [gapAfterLoop]
      rw [hch, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
      simp only [gapLiteralWrite, hlit, gapExtraWrite]
  unfold GapRuleWrote
  exact ⟨gapRule_stage_err hb hn hix hnix hk he hidx hnip hbytes hw,
    gapWrote_record mem e (gapS2 win ip ee) gapTagExtra⟩

/-- **Row 6 — the scalar refusal.**  The first byte selects no arm, so the record
is written at `pos` with the scalar tag. -/
theorem gapRule_scalarRefusal {mem : Mem} {c pos ip b n ix nix k e ee : Nat}
    {win : List UInt8}
    (hb : stage2ReadWord mem c 8 = some b)
    (hn : stage2ReadWord mem (c + 8) 8 = some n)
    (hix : stage2ReadWord mem (c + 16) 8 = some ix)
    (hnix : stage2ReadWord mem (c + 24) 8 = some nix)
    (hk : stage2ReadWord mem (c + 32) 8 = some k)
    (he : stage2ReadWord mem (c + 1112) 8 = some e)
    (hidx : ∀ (_ : k < nix), stage2ReadWord mem (ix + 4 * k) 4 = some ip)
    (hnip : nix ≤ k → ip = n)
    (hbytes : readBytes mem b ip = some win)
    (hpos : pos ≤ ip)
    (hch : gapScalarStart (win.getD pos 0))
    (hee : gapEe win ip pos = ee)
    (hlt : ee < ip) :
    GapRuleWrote mem c pos e pos gapTagScalar := by
  have hw : gapRecoverWrite win ip pos = GapWrite.err pos gapTagScalar := by
    unfold gapScalarStart gapNumStart at hch
    obtain ⟨hnum, htrue, hfalse, hnull⟩ := hch
    simp only [gapRecoverWrite, hee]
    rw [ite_eq_right hlt.ne]
    simp only [gapAfterLoop]
    rw [ite_eq_right hnum, ite_eq_right htrue, ite_eq_right hfalse, ite_eq_right hnull]
  unfold GapRuleWrote
  exact ⟨gapRule_stage_err hb hn hix hnix hk he hidx hnip hbytes hw,
    gapWrote_record mem e pos gapTagScalar⟩

/-! ### Axiom footprints -/

#print axioms gapWrote_record
#print axioms gapRule_stage_none
#print axioms gapRule_stage_err
#print axioms gapRule_unchanged
#print axioms gapRule_numberRefusal
#print axioms gapRule_numberExtra
#print axioms gapRule_literalRefusal
#print axioms gapRule_literalExtra
#print axioms gapRule_scalarRefusal

end LeanLLVM.Refinement
