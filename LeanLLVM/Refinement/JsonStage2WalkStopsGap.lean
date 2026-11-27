/-
The walk's stop is not an entry: what the stage-1 masks determine, and the
document clause the stop equation actually needs.

`NumberExtentAssumed`'s remaining field is `q = sp.stop` — the stage-2 scalar
scan's stop is the tape's number span's stop.  The recorded path for it was a
`WalkAlignStops` conjunct on `WalkAlign` (the next entry is the token's stop),
initialised from the stage-1 emitter that fills `WalkGeom.ent`.  This module
checks that path and finds it wrong in a way a proof cannot repair: the emitter's
model determines entry *positions*, and `WalkAlign` already forces every entry to
be a byte with a token class, so a whitespace stop can never be an entry.

## The masks yield positions, not extents

The emitter's Lean model is `JsonEntSpec.stage1Words`, built from `entryMask64`,
and the positions stream is `JsonEntSpec.positionsOf` mapping a mask's set lanes
to `base + lane`.  `entry_mask_eq` (`JsonEntSpec.lean`) is the whole content of
an entry bit: lane `k` is set exactly when the lane holds an unescaped quote, a
delimiter outside a string, or the first lane of a scalar run.  `stage1Word` is
that mask clamped to the document, and `stage1Words` is one word per block.  No
case of that definition mentions a run's last lane: a lane is an entry because of
the byte's class, never because a run ends there.

That is not an omission the model could be extended to fix: a scalar run ends on
a byte that is not a run start, and after a number the ending byte is a
delimiter, a quote, whitespace, or the end of the document.  The delimiter and
quote are entries *of the next token*, whitespace is no entry at all, and the
document's end is past the last entry.  So the successor entry equals the token's
stop only when the token ends on a structural byte, which is false for every
scalar followed by whitespace (`[1 ,2]` is the smallest valid witness: the
entry stream is `[0, 1, 3, 4, 5]`, the first number's stop is `2`, and its
successor entry is the comma at `3`).

## What the class clause already says

`WalkAlign`'s class clause is the forgotten fact that refutes the recorded path:
the byte at every entry announces the class of the token that starts there, and a
whitespace byte has no class (`classOfByte_eq_none_of_isSpace`).  Hence a
whitespace stop is never an entry.  `WalkAlign.not_stops_of_isSpace` states it,
and `WalkAlign.isSpace_false_of_stops` reads it as a constraint on the documents
the recorded clause could describe.

## The clause that does hold

The stop equation needs the document's own side: between a token's stop and the
walk's `%cond` bound the document is whitespace.  `StopToEntrySpace` is that
statement at one token, `WalkAlignGaps` is it at every token, and
`stop_eq_of_gap_loop` / `stop_eq_of_gap_direct` derive the scan's stop from it
and the two arms of `stage2NoEventWalkScalarSkip`.  `NumberExtentAssumed` then
follows (`numberExtentAssumed_of_gap_loop`, `numberExtentAssumed_of_gap_direct`).

Two of the scan's premises are now derived rather than assumed.  The number run's
bytes are non-whitespace, from `NumConstituent`'s six bytes
(`numRun_all_constituent`, `numConstituent_not_space`, `numRun_getD_not_space`,
`numRunFrom_take_not_space`), so `numberExtentAssumed_of_gap_loop` takes the
tape's run slice and bounds and derives the rest.  And the scan's answer is
re-exported in the document's vocabulary: `isSpaceB_iff_skipWs` is the class
bridge, `ScanArm` is `stage2NoEventWalkScalarSkip`'s conclusion at a lane with
`σ = bs.getD · 0`, and `ScanArm.of_scalarSkip` turns the emitted bits into it.
`NumberExtentAssumed.of_scanArm` composes the run, the gap and the scan's answer,
and `numberArmPremises_of_parse_scan` is the whole consumer: parse acceptance,
the alignment, the token, the lane's identity and `ScanArm` give the number arm's
five premises with no extent and no gap hypothesis.

## The production is closed

The gap's initialisation is the parser's tape, not the emitter's.  The stage-1
emitter cannot supply it: its mask is a byte classifier (above), it never reads a
tape, and its entry stream is a function of the document's bytes alone, so it
cannot know which byte a parse ended a number on.  `TokenGapsSpace` is the clause
stated over the tape, and `WalkAlignGaps.of_tokenGaps` shows that `WalkAlign`
plus `TokenGapsSpace` yields `WalkAlignGaps`.  `parseBytes_tokenGapsSpace` proves
the tape-level statement

`parseBytes l (ByteString.literal bs) = .ok t → TokenGapsSpace bs t.tokens bs.length`

from the decoder rather than from the parser's own recursion.  `decodeTape`
accepts a tape only when every separator token sits at `skipFrom` of the cursor
its predecessor stopped at, and each scalar guard pins its span to `⟨i, i + len⟩`
at the cursor the decode resumed from; so `gaps_of_decodeTape` reads a successful
decode's consumed prefix as a `Gaps` chain and extends it to the document's end
with the trailing `skipFrom` check.  `decodeTape_correct` carries that success
from `parseBytes`, `tokenGapsSpace_of_gaps` converts the chain at the tape's span
discipline (`checkSpans`) to `TokenGapsSpace`, and `WalkAlign.input` plus
`WalkGeom.doc`'s length identify the geometry's document with the parsed one.  No
premise is left: the number arm's premises follow from parse acceptance, the
alignment, the token's index, the lane's identity and the scan's answer alone.
-/
import LeanLLVM.JSON.Correct
import LeanLLVM.Refinement.JsonNumberExtentAssumed
import LeanLLVM.Refinement.JsonStage2NoEventWalkScalar

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine

/-! ### A whitespace byte names no token class -/

/-- **None of RFC 8259 §2's four whitespace bytes is a `classOfByte` branch.**
The parser's first-byte dispatch is `classOfByte`; the check is four `decide`s. -/
theorem classOfByte_eq_none_of_isSpace {b : UInt8} (h : IsSpaceB b = true) :
    classOfByte b = none := by
  unfold IsSpaceB at h
  have h' : b = 0x20 ∨ b = 0x09 ∨ b = 0x0A ∨ b = 0x0D := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] using h
  rcases h' with rfl | rfl | rfl | rfl <;> decide

/-! ### The successor entry is not a whitespace stop -/

/-- **The entry after a token cannot sit on a whitespace stop.**  `WalkAlign.at`
gives the successor entry a token whose start is that entry and a document byte
there; `WalkAlign.class` says the byte announces the token's class, which
`classOfByte_eq_none_of_isSpace` denies for whitespace. -/
theorem WalkAlign.entryPos_next_ne_stop_of_isSpace {m0 : Mem} {G : WalkGeom m0}
    {t : Tape} (h : WalkAlign G t) {k : Nat} (hk : k + 1 < G.nep)
    {tok : Token} {b : UInt8}
    (hbyte : G.bs[tok.span.stop]? = some b) (hspace : IsSpaceB b = true) :
    entryPos G (k + 1) ≠ tok.span.stop := by
  intro heq
  obtain ⟨tok', b', htok', -, hbyte'⟩ := h.at hk
  have hb : b' = b := by
    rw [heq] at hbyte'
    rw [hbyte'] at hbyte
    exact Option.some.inj hbyte
  have hcls : classOfByte b' = some (tokenClass tok') := h.class hk htok' hbyte'
  rw [hb, classOfByte_eq_none_of_isSpace hspace] at hcls
  cases hcls

/-- **The recorded stop clause is false, not merely unproved.**  A token whose
stop byte is whitespace — a scalar followed by a space — makes `WalkAlign` and
`WalkAlignStops` demand different bytes of the successor entry.  `[1 ,2]` is a
valid document at which `WalkAlign` holds and the clause fails. -/
theorem WalkAlign.not_stops_of_isSpace {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlign G t) {k : Nat} (hk : k + 1 < G.nep) {tok : Token}
    (htok : t.tokens[k]? = some tok) {b : UInt8}
    (hbyte : G.bs[tok.span.stop]? = some b) (hspace : IsSpaceB b = true) :
    ¬ WalkAlignStops G t := by
  intro hstops
  exact h.entryPos_next_ne_stop_of_isSpace hk hbyte hspace
    (hstops k tok htok hk)

/-- **The clause forces every token's stop byte to be non-whitespace.**  Read as
a constraint on documents: the intersection of `WalkAlign` and the recorded
clause contains no document with a scalar followed by whitespace. -/
theorem WalkAlign.isSpace_false_of_stops {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlign G t) (hstops : WalkAlignStops G t) {k : Nat}
    (hk : k + 1 < G.nep) {tok : Token} (htok : t.tokens[k]? = some tok)
    {b : UInt8} (hbyte : G.bs[tok.span.stop]? = some b) : IsSpaceB b = false := by
  by_contra hne
  have htrue : IsSpaceB b = true := by
    cases hb : IsSpaceB b with
    | true => rfl
    | false => exact absurd hb hne
  exact h.entryPos_next_ne_stop_of_isSpace hk hbyte htrue
    (hstops k tok htok hk)

/-! ### The clause that does hold: the gap to the next bound is whitespace -/

/-- **The document between a token's stop and the walk's `%cond` bound.**  The
successor bound is at or after the stop, and every lane in between is RFC 8259
whitespace.  This is the fact the masks do not carry and the parser's whitespace
skip does. -/
def StopToEntrySpace (bs : List UInt8) (stop cond : Nat) : Prop :=
  stop ≤ cond ∧ ∀ j, stop ≤ j → j < cond → IsSpaceB (bs.getD j 0) = true

/-- **The alignment's gap clause.**  At every token, the document restricts the
interval from the token's stop to the walk's bound — the next entry's position,
or the document's length at the last entry — to whitespace.  `WalkAlign`'s
successor clause names the bound; this clause names the stop's relation to it. -/
def WalkAlignGaps {m0 : Mem} (G : WalkGeom m0) (t : Tape) : Prop :=
  ∀ (k : Nat) (tok : Token), t.tokens[k]? = some tok →
    StopToEntrySpace G.bs tok.span.stop
      (if k + 1 < G.nep then entryPos G (k + 1) else G.n)

/-- The gap clause at one token. -/
theorem WalkAlignGaps.at {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (h : WalkAlignGaps G t) {k : Nat} {tok : Token} (htok : t.tokens[k]? = some tok) :
    StopToEntrySpace G.bs tok.span.stop
      (if k + 1 < G.nep then entryPos G (k + 1) else G.n) :=
  h k tok htok

/-! ### The clause's initialisation, as the tape-level clause

`WalkAlignGaps` is not a fact about the emitter; it is a fact about the
document's gaps.  Stated over the tape, `TokenGapsSpace` says every token's stop
is followed by whitespace up to the next token's start, or up to the document's
end at the last token.  Given `WalkAlign`, whose successor clause names the next
entry, that supplies `WalkAlignGaps`; `parseBytes_tokenGapsSpace` below proves
the tape-level statement from a `parseBytes` acceptance, so it is a theorem rather
than a premise. -/

/-- **The tape's inter-token gap is whitespace.**  `n` is the document's length,
used at the last token; the caller's `WalkGeom.n` is the value `WalkAlignGaps`
reads there. -/
def TokenGapsSpace (bs : List UInt8) (toks : List Token) (n : Nat) : Prop :=
  ∀ (k : Nat) (tok : Token), toks[k]? = some tok →
    StopToEntrySpace bs tok.span.stop
      (match toks[k + 1]? with
        | some next => next.span.start
        | none => n)

/-- **`WalkAlign` plus the tape's gaps initialises `WalkAlignGaps`.**  The
successor entry is the next token's start (`WalkAlign.next`), so the gap clause
at the tape is the gap clause at the entries; at the last token the bound is
`G.n`, which the tape gap supplies. -/
theorem WalkAlignGaps.of_tokenGaps {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (hal : WalkAlign G t) (hgaps : TokenGapsSpace G.bs t.tokens G.n) :
    WalkAlignGaps G t := by
  intro k tok htok
  have hlen : G.nep = t.tokens.length := hal.tokens_length
  by_cases hk : k + 1 < G.nep
  · rw [ite_eq_left hk]
    obtain ⟨next, hnext, hstart⟩ := hal.next hk
    have hgt := hgaps k tok htok
    rw [hnext] at hgt
    simpa [hstart] using hgt
  · rw [ite_eq_right hk]
    have hnone : t.tokens[k + 1]? = none := by
      apply List.getElem?_eq_none_iff.mpr
      omega
    have hgt := hgaps k tok htok
    rw [hnone] at hgt
    exact hgt

/-! ### The number run's bytes are not whitespace

`NumConstituent`'s six bytes are the digits, `.`, `e`, `E`, `+` and `-`; none is
one of RFC 8259 §2's four whitespace bytes.  `numRun` collects exactly the
constituents (`numRun_cons`), so every byte of `numRunFrom`'s run is
non-whitespace — the hypothesis the scan's stop equation consumes. -/

/-- **Every byte of a `numRun` is a number constituent.**  The list view's
induction is `numRun_cons`'s two cases. -/
theorem numRun_all_constituent (b : Bytes) :
    ∀ x ∈ numRun b, NumConstituent x = true := by
  induction b using ByteString.induction_on with
  | h0 => simp [numRun_empty]
  | hs a rest ih =>
      rw [numRun_cons]
      split
      · rename_i ha
        intro x hx
        simp only [ByteString.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact ih x hx
      · simp

/-- **A number constituent is not whitespace.**  The six cases are concrete
bytes, so each is a `decide` at the constituent's value. -/
theorem numConstituent_not_space {b : UInt8} (h : NumConstituent b = true) :
    IsSpaceB b = false := by
  have h20 : b ≠ 0x20 := by
    intro hb; subst hb
    have : NumConstituent (0x20 : UInt8) = false := by decide
    rw [this] at h; cases h
  have h09 : b ≠ 0x09 := by
    intro hb; subst hb
    have : NumConstituent (0x09 : UInt8) = false := by decide
    rw [this] at h; cases h
  have h0A : b ≠ 0x0A := by
    intro hb; subst hb
    have : NumConstituent (0x0A : UInt8) = false := by decide
    rw [this] at h; cases h
  have h0D : b ≠ 0x0D := by
    intro hb; subst hb
    have : NumConstituent (0x0D : UInt8) = false := by decide
    rw [this] at h; cases h
  unfold IsSpaceB
  simp [h20, h09, h0A, h0D]

/-- **A lane of a `numRun` is non-whitespace.** -/
theorem numRun_getD_not_space {b : Bytes} {k : Nat}
    (hk : k < (numRun b).data.toList.length) :
    IsSpaceB ((numRun b).data.toList.getD k 0) = false := by
  have hmem : (numRun b).data.toList[k] ∈ numRun b := by
    rw [ByteString.mem_def, ByteString.toList_eq_data_toList]
    exact List.getElem_mem hk
  have hconst : NumConstituent ((numRun b).data.toList[k]) = true :=
    numRun_all_constituent b _ hmem
  have hget : (numRun b).data.toList.getD k 0 = (numRun b).data.toList[k] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  rw [hget]
  exact numConstituent_not_space hconst

/-- **The document's bytes inside a number run are non-whitespace.**  The run's
slice is the span's bytes (`hslice`) and the span ends inside the document, so
each index before the stop reads a run constituent. -/
theorem numRunFrom_take_not_space {bs : List UInt8} {lane stop j : Nat}
    (hstop_le : stop ≤ bs.length)
    (hslice : (bs.drop lane).take (stop - lane) =
      (numRunFrom (ByteString.literal bs) lane).data.toList)
    (hlane : lane ≤ j) (hj : j < stop) :
    IsSpaceB (bs.getD j 0) = false := by
  have hslice' : (bs.drop lane).take (stop - lane) =
      (numRun ((ByteString.literal bs).drop lane)).data.toList := by
    rw [← numRunFrom_eq]
    exact hslice
  have hrunLen : (numRun ((ByteString.literal bs).drop lane)).data.toList.length
      = stop - lane := by
    have h := congrArg List.length hslice'
    rw [List.length_take, List.length_drop] at h
    have hle : stop - lane ≤ bs.length - lane := by omega
    rw [Nat.min_eq_left hle] at h
    exact h.symm
  have hdoc : bs.getD j 0 =
      (numRun ((ByteString.literal bs).drop lane)).data.toList.getD (j - lane) 0 := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    have h1 : bs[j]? = (bs.drop lane)[j - lane]? := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hlane]
    have h2 : (bs.drop lane)[j - lane]? =
        ((bs.drop lane).take (stop - lane))[j - lane]? := by
      rw [List.getElem?_take, ite_eq_left (by omega)]
    rw [h1, h2, hslice']
  rw [hdoc]
  exact numRun_getD_not_space (by rw [hrunLen]; omega)

/-! ### The scan's stop, from the gap

`JsonStage2NoEventWalkScalarSkip` has two arms.  On the loop arm the scan has
passed no whitespace in `[lane, q)` and stops at `q = cond` or at a whitespace
`q`.  On the direct arm it stops at `q = cond` with a non-whitespace byte at
`cond - 1`.  With `StopToEntrySpace` at the token and the number run's
constituents (which are not whitespace), both arms give `q = sp.stop`. -/

/-- **The loop arm's stop is the token's stop.**  The run's bytes are not
whitespace, the gap's are, and the scan's prefix is not whitespace, so the two
first-whitespace positions coincide. -/
theorem stop_eq_of_gap_loop {bs : List UInt8} {lane q cond stop : Nat}
    (hstop_le : lane ≤ stop) (hgap : StopToEntrySpace bs stop cond)
    (hrun : ∀ j, lane ≤ j → j < stop → IsSpaceB (bs.getD j 0) = false)
    (hle : lane ≤ q) (hqle : q ≤ cond)
    (hq : q = cond ∨ IsSpaceB (bs.getD q 0) = true)
    (hpre : ∀ j, lane ≤ j → j < q → IsSpaceB (bs.getD j 0) = false) :
    q = stop := by
  obtain ⟨hstop_cond, hgapall⟩ := hgap
  have hstop_le_q : stop ≤ q := by
    by_contra h
    have hqlt : q < stop := by omega
    have hnf : IsSpaceB (bs.getD q 0) = false := hrun q hle hqlt
    rcases hq with hqc | hqs
    · omega
    · rw [hnf] at hqs
      cases hqs
  have hq_le_stop : q ≤ stop := by
    by_contra h
    have hslt : stop < q := by omega
    have hsc : stop < cond := by omega
    have hsp : IsSpaceB (bs.getD stop 0) = true := hgapall stop le_rfl hsc
    have hnf : IsSpaceB (bs.getD stop 0) = false := hpre stop hstop_le hslt
    rw [hnf] at hsp
    cases hsp
  omega

/-- **The direct arm's stop is the token's stop.**  The arm stops at the bound
and reads a non-whitespace byte just before it; the gap is whitespace, so the
bound is the token's stop. -/
theorem stop_eq_of_gap_direct {bs : List UInt8} {q cond stop : Nat}
    (hqcond : q = cond) (hgap : StopToEntrySpace bs stop cond)
    (hne : IsSpaceB (bs.getD (cond - 1) 0) = false) :
    q = stop := by
  rw [hqcond]
  obtain ⟨hstop_cond, hgapall⟩ := hgap
  rcases Nat.lt_or_ge stop cond with hlt | hge
  · have hsp : IsSpaceB (bs.getD (cond - 1) 0) = true :=
      hgapall (cond - 1) (by omega) (by omega)
    rw [hne] at hsp
    cases hsp
  · omega

/-! ### The release theorem's assumption, from the clause -/

/-- **The loop arm plus the gap gives `NumberExtentAssumed`.**  `hlane` and
`hstart` place the scan's start and order the span; `hgap` is
`StopToEntrySpace` at the token; `hrun` is the number run's non-whitespace; the
rest is `JsonStage2NoEventWalkScalarSkip`'s loop-arm conclusion. -/
theorem numberExtentAssumed_of_gap_loop {bs : List UInt8} {sp : Span}
    {lane q cond : Nat} (hlane : lane = sp.start) (hstart : sp.start ≤ sp.stop)
    (hgap : StopToEntrySpace bs sp.stop cond)
    (hrun : ∀ j, lane ≤ j → j < sp.stop → IsSpaceB (bs.getD j 0) = false)
    (hle : lane ≤ q) (hqle : q ≤ cond)
    (hq : q = cond ∨ IsSpaceB (bs.getD q 0) = true)
    (hpre : ∀ j, lane ≤ j → j < q → IsSpaceB (bs.getD j 0) = false) :
    NumberExtentAssumed bs sp q :=
  ⟨stop_eq_of_gap_loop (lane := lane) (cond := cond) (stop := sp.stop) (q := q)
    (by omega) hgap hrun hle hqle hq hpre⟩

/-- **The direct arm plus the gap gives `NumberExtentAssumed`.** -/
theorem numberExtentAssumed_of_gap_direct {bs : List UInt8} {sp : Span}
    {q cond : Nat} (hqcond : q = cond) (hgap : StopToEntrySpace bs sp.stop cond)
    (hne : IsSpaceB (bs.getD (cond - 1) 0) = false) :
    NumberExtentAssumed bs sp q :=
  ⟨stop_eq_of_gap_direct (q := q) (stop := sp.stop) hqcond hgap hne⟩

/-! ### The scan's answer in the document's terms

`stage2NoEventWalkScalarSkip` reports the emitted class by its `stage2SkipWs` bit;
`isSpaceB_iff_skipWs` is the bridge.  `ScanArm` is the theorem's conclusion at a
lane with `σ = bs.getD · 0` and `u0 = bs.getD (cond - 1) 0`, and
`ScanArm.of_scalarSkip` re-exports it in that vocabulary — so a consumer takes the
scan's answer as one predicate at the token rather than restating its shape. -/

/-- **The emitted whitespace class is RFC 8259's.** -/
theorem isSpaceB_iff_skipWs (b : UInt8) :
    IsSpaceB b = true ↔ stage2SkipWs (BitVec.ofNat 8 b.toNat) = true := by
  rw [stage2SkipWs_iff]
  unfold IsSpaceB
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    rcases h with ((h | h) | h) | h <;> (rw [h]; decide)
  · intro h
    rcases h with h | h | h | h
    · have ht : b.toNat = 9 := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)] using h
      have hb : b = (0x09 : UInt8) := UInt8.toNat_inj.mp (by rw [ht]; decide)
      rw [hb]; decide
    · have ht : b.toNat = 10 := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)] using h
      have hb : b = (0x0A : UInt8) := UInt8.toNat_inj.mp (by rw [ht]; decide)
      rw [hb]; decide
    · have ht : b.toNat = 13 := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)] using h
      have hb : b = (0x0D : UInt8) := UInt8.toNat_inj.mp (by rw [ht]; decide)
      rw [hb]; decide
    · have ht : b.toNat = 32 := by
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt b)] using h
      have hb : b = (0x20 : UInt8) := UInt8.toNat_inj.mp (by rw [ht]; decide)
      rw [hb]; decide

/-- **The emitted class is false exactly when the document byte is not
whitespace.** -/
theorem isSpaceB_eq_false_iff (b : UInt8) :
    IsSpaceB b = false ↔ stage2SkipWs (BitVec.ofNat 8 b.toNat) = false := by
  constructor
  · intro h
    cases hs : stage2SkipWs (BitVec.ofNat 8 b.toNat) with
    | false => rfl
    | true => exact absurd ((isSpaceB_iff_skipWs b).mpr hs) (by rw [h]; simp)
  · intro h
    cases hb : IsSpaceB b with
    | false => rfl
    | true => exact absurd ((isSpaceB_iff_skipWs b).mp hb) (by rw [h]; simp)

/-- **The stage-2 scalar scan's answer at a number's lane**, in the document's
terms: the stop lies in `[lane, cond]`; it is `cond` or a whitespace byte; and
either the scan loop passed only non-whitespace (`[lane, q)`), or the direct arm
stopped at `cond` with a non-whitespace byte at `cond - 1`. -/
def ScanArm (bs : List UInt8) (lane q cond : Nat) : Prop :=
  lane ≤ q ∧ q ≤ cond ∧
    (q = cond ∨ IsSpaceB (bs.getD q 0) = true) ∧
      ((∀ j, lane ≤ j → j < q → IsSpaceB (bs.getD j 0) = false) ∨
        (q = cond ∧ IsSpaceB (bs.getD (cond - 1) 0) = false))

/-- **The scan's conclusion, re-exported at the lane.**  This is
`stage2NoEventWalkScalarSkip`'s answer with `σ = bs.getD · 0` and
`u0 = bs.getD (cond - 1) 0`, through the class bridge. -/
theorem ScanArm.of_scalarSkip {bs : List UInt8} {lane q cond : Nat}
    (hle : lane ≤ q) (hqle : q ≤ cond)
    (hq : q = cond ∨ stage2SkipWs (BitVec.ofNat 8 (bs.getD q 0).toNat) = true)
    (harm : (∀ j, lane ≤ j → j < q →
        stage2SkipWs (BitVec.ofNat 8 (bs.getD j 0).toNat) = false) ∨
      (q = cond ∧ stage2SkipWs (BitVec.ofNat 8 (bs.getD (cond - 1) 0).toNat) = false)) :
    ScanArm bs lane q cond := by
  refine ⟨hle, hqle, ?_, ?_⟩
  · rcases hq with h | h
    · exact Or.inl h
    · exact Or.inr ((isSpaceB_iff_skipWs _).mpr h)
  · rcases harm with h | ⟨hqc, hne⟩
    · left
      intro j hj hjq
      exact (isSpaceB_eq_false_iff _).mpr (h j hj hjq)
    · right
      exact ⟨hqc, (isSpaceB_eq_false_iff _).mpr hne⟩

/-- **The scan's answer and the document's run give the stop equation.**  The
run's bytes are the span's (`hslice`) and are non-whitespace; the gap to `cond` is
whitespace; and `ScanArm` is the scan's own answer.  No extent hypothesis is
used: this constructs `NumberExtentAssumed`. -/
theorem NumberExtentAssumed.of_scanArm {bs : List UInt8} {sp : Span}
    {lane q cond : Nat} (hlane : lane = sp.start) (hstart : sp.start ≤ sp.stop)
    (hstop_le : sp.stop ≤ bs.length)
    (hslice : (bs.drop sp.start).take (sp.stop - sp.start) =
      (numRunFrom (ByteString.literal bs) sp.start).data.toList)
    (hgap : StopToEntrySpace bs sp.stop cond)
    (hscan : ScanArm bs lane q cond) : NumberExtentAssumed bs sp q := by
  subst hlane
  obtain ⟨hle, hqle, hq, harm⟩ := hscan
  have hrun : ∀ j, sp.start ≤ j → j < sp.stop → IsSpaceB (bs.getD j 0) = false := by
    intro j hj hjstop
    exact numRunFrom_take_not_space hstop_le hslice hj hjstop
  rcases harm with hpre | ⟨hqc, hne⟩
  · exact ⟨stop_eq_of_gap_loop (lane := sp.start) (cond := cond) (stop := sp.stop)
      (q := q) hstart hgap hrun hle hqle hq hpre⟩
  · exact ⟨stop_eq_of_gap_direct (q := q) (stop := sp.stop) hqc hgap hne⟩


/-! ### The parser's tape has whitespace gaps

`TokenGapsSpace` is the initialiser the stop equation was missing, and a
`parseBytes` acceptance supplies it.  The proof is the decoder's rather than the
parser's own recursion.  `decodeTape` succeeds only when every separator token
sits at `skipFrom` of the cursor its predecessor stopped at (`decodeElemsTail`
and `decodeMembersTail` check the comma at `skipFrom bs j`; `decodeValue` checks
each container's opening delimiter, its key's colon and its closing delimiter at
the skipped positions), and every scalar guard pins its span to `⟨i, i + len⟩` at
the cursor the decode resumed from.  So a successful decode's consumed prefix is
a `Gaps` chain, and `decodeTape`'s trailing check
`skipFrom t.input d.cursor = t.input.length` extends the chain to the document's
end.  `decodeTape_correct` carries that success from `parseBytes`. -/

/-- A chain of tokens whose successive gaps are whitespace.  `Gaps bs a toks b`
holds when `bs[a, first start)` is whitespace, every token's stop is followed by
whitespace up to its successor's start, and the last token's stop is followed by
whitespace up to the chain's bound `b`.  The empty chain is the single range
`bs[a, b)`. -/
inductive Gaps (bs : Bytes) : Nat → List Token → Nat → Prop
  /-- The empty chain: one whitespace range. -/
  | nil {a b : Nat} (h : SpaceAt bs a b) : Gaps bs a [] b
  /-- A leading token, the whitespace to its start, and the rest of the chain. -/
  | cons {a b : Nat} (t : Token) (rest : List Token)
      (hstart : SpaceAt bs a t.span.start) (hrest : Gaps bs t.span.stop rest b) :
      Gaps bs a (t :: rest) b

/-- The empty range is whitespace. -/
theorem spaceAt_refl (bs : Bytes) (a : Nat) : SpaceAt bs a a :=
  ⟨le_rfl, by intro k b h1 h2; omega⟩

/-- Whitespace ranges compose. -/
theorem spaceAt_trans {bs : Bytes} {a b c : Nat}
    (h1 : SpaceAt bs a b) (h2 : SpaceAt bs b c) : SpaceAt bs a c := by
  refine ⟨le_trans h1.1 h2.1, ?_⟩
  intro k byte hak hkc hget
  by_cases hkb : k < b
  · exact h1.2 k byte hak hkb hget
  · exact h2.2 k byte (by omega) hkc hget

/-- The bound after the head of a list: the head's start, or `b` when the list is
empty. -/
def nextBound (b : Nat) : List Token → Nat
  | [] => b
  | t :: _ => t.span.start

/-- The whitespace from a chain's entry to its first token's start (or to its
bound when the chain is empty). -/
theorem Gaps.first_space {bs : Bytes} {a b : Nat} {toks : List Token}
    (h : Gaps bs a toks b) : SpaceAt bs a (nextBound b toks) := by
  cases h with
  | nil h0 => exact h0
  | cons t rest h0 _ => exact h0

/-- A chain shifted at its entry: only the leading range changes. -/
theorem Gaps.shift {bs : Bytes} {a a' b : Nat} {toks : List Token}
    (ha : SpaceAt bs a a') (h : Gaps bs a' toks b) : Gaps bs a toks b := by
  cases h with
  | nil h0 => exact Gaps.nil (spaceAt_trans ha h0)
  | cons t rest h0 hrest => exact Gaps.cons t rest (spaceAt_trans ha h0) hrest

/-- Chains append: the left chain's final range meets the right chain's entry. -/
theorem Gaps.append {bs : Bytes} {a b : Nat} {A : List Token}
    (hA : Gaps bs a A b) :
    ∀ {c : Nat} {B : List Token}, Gaps bs b B c → Gaps bs a (A ++ B) c := by
  induction hA with
  | nil h0 => intro c B hB; exact Gaps.shift h0 hB
  | cons t rest h0 hrest ih => intro c B hB; exact Gaps.cons t (rest ++ B) h0 (ih hB)

/-- Extending a chain's bound along a whitespace range. -/
theorem Gaps.end_space {bs : Bytes} {a b c : Nat} {toks : List Token}
    (h : Gaps bs a toks b) (hs : SpaceAt bs b c) : Gaps bs a toks c := by
  have := Gaps.append h (Gaps.nil hs)
  simpa using this

/-- `nextBound` at a drop is the lookup at the drop's index. -/
theorem nextBound_drop {b : Nat} (toks : List Token) (k : Nat) :
    nextBound b (toks.drop k) =
      (match toks[k]? with | some t => t.span.start | none => b) := by
  induction toks generalizing k with
  | nil => cases k <;> rfl
  | cons t rest ih =>
      cases k with
      | zero => rfl
      | succ k =>
          simp only [Nat.succ_eq_add_one, List.drop_succ_cons, List.getElem?_cons_succ]
          exact ih k

/-- **The gap after the token at an index.**  A chain gives, for `toks[k]`,
whitespace from its stop to the start of `toks[k+1]` — or to the chain's bound at
the last token. -/
theorem Gaps.get? {bs : Bytes} {a b : Nat} {toks : List Token}
    (h : Gaps bs a toks b) :
    ∀ (k : Nat) (tok : Token), toks[k]? = some tok →
      SpaceAt bs tok.span.stop (nextBound b (toks.drop (k + 1))) := by
  induction h with
  | nil h0 =>
      intro k tok htok
      simp at htok
  | cons t rest h0 hrest ih =>
      intro k tok htok
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at htok
          subst tok
          simpa only [List.drop_succ_cons, List.drop_zero] using Gaps.first_space hrest
      | succ k =>
          simp only [List.getElem?_cons_succ] at htok
          simpa only [List.drop_succ_cons] using ih k tok htok

/-- Whether the first token of a list is punctuation of a given kind.  The
decoder's own copy of this test is private to its module, so the chain proof
states the same test here; it is used only to split the decoder's two-token
container arms from the general ones. -/
private def headPunct : Punct → List Token → Bool
  | k, .punct k' _ :: _ => decide (k' = k)
  | _, _ => false

/-- **The decoder's token chain.**  A successful decode of a token list consumes a
prefix whose spans are a `Gaps` chain from the entry cursor.  The three mutually
recursive decoders are handled in one induction on the token count; the container
cases compose the decoded value's chain with the tail's. -/
private theorem decode_gaps_aux (bs : Bytes) :
    ∀ (n : Nat) (toks : List Token), toks.length = n →
      (∀ (i : Nat) (d : Decoded toks), decodeValue bs i toks = some d →
        ∃ pre : List Token, toks = pre ++ d.rest ∧ Gaps bs i pre d.cursor) ∧
      (∀ (j : Nat) (t : ElemsTail toks), decodeElemsTail bs j toks = some t →
        ∃ pre : List Token, toks = pre ++ t.rest ∧ Gaps bs j pre t.cursor) ∧
      (∀ (j : Nat) (t : MembersTail toks), decodeMembersTail bs j toks = some t →
        ∃ pre : List Token, toks = pre ++ t.rest ∧ Gaps bs j pre t.cursor) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro toks hlen
    refine ⟨?_, ?_, ?_⟩
    · -- decodeValue
      intro i d hdec
      cases toks with
      | nil => simp [decodeValue] at hdec
      | cons tok rest =>
        cases tok with
        | null s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · rename_i hcond
            obtain ⟨hs, -⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            injection hdec with hd
            subst hd
            refine ⟨[Token.null s], by simp, ?_⟩
            rw [hs]
            exact Gaps.cons _ [] (spaceAt_refl bs i) (Gaps.nil (spaceAt_refl bs _))
          · cases hdec
        | bool b s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · rename_i hbt
            subst hbt
            split at hdec
            · rename_i hcond
              obtain ⟨hs, -⟩ := by
                simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
              injection hdec with hd
              subst hd
              refine ⟨[Token.bool true s], by simp, ?_⟩
              rw [hs]
              exact Gaps.cons _ [] (spaceAt_refl bs i) (Gaps.nil (spaceAt_refl bs _))
            · cases hdec
          · rename_i hbf
            have hbfl : b = false := by cases b <;> simp_all
            subst hbfl
            split at hdec
            · rename_i hcond
              obtain ⟨hs, -⟩ := by
                simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
              injection hdec with hd
              subst hd
              refine ⟨[Token.bool false s], by simp, ?_⟩
              rw [hs]
              exact Gaps.cons _ [] (spaceAt_refl bs i) (Gaps.nil (spaceAt_refl bs _))
            · cases hdec
        | number s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · rename_i hcond
            obtain ⟨hs, -⟩ := by
              simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
            injection hdec with hd
            subst hd
            refine ⟨[Token.number s], by simp, ?_⟩
            rw [hs]
            exact Gaps.cons _ [] (spaceAt_refl bs i) (Gaps.nil (spaceAt_refl bs _))
          · cases hdec
        | string s =>
          rw [decodeValue] at hdec <;> (first | (intro c rest' heq; cases heq) | skip)
          split at hdec
          · cases hdec
          · rename_i cs stop hs
            split at hdec
            · rename_i hcond
              obtain ⟨-, hspan⟩ := by
                simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
              injection hdec with hd
              subst hd
              refine ⟨[Token.string s], by simp, ?_⟩
              rw [hspan]
              exact Gaps.cons _ [] (spaceAt_refl bs i) (Gaps.nil (spaceAt_refl bs _))
            · cases hdec
        | punct k s =>
          cases k with
          | openBracket =>
            cases rest with
            | nil => simp [decodeValue] at hdec
            | cons tok2 rest2 =>
              by_cases h : headPunct .closeBracket (tok2 :: rest2) = true
              · cases tok2 with
                | punct k2 s2 =>
                  cases k2 with
                  | closeBracket =>
                      rw [decodeValue] at hdec <;> (first | (intro a b hh; cases hh) | skip)
                      split at hdec
                      · rename_i hcond
                        simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, beq_iff_eq] at hcond
                        obtain ⟨hs, -, hc, -⟩ := hcond
                        injection hdec with hd
                        subst hd
                        refine ⟨[Token.punct .openBracket s, Token.punct .closeBracket s2],
                          by simp, ?_⟩
                        rw [hs, hc]
                        exact Gaps.cons _ _ (spaceAt_refl bs i)
                          (Gaps.cons _ [] (skipFrom_space bs (i + 1))
                            (Gaps.nil (spaceAt_refl bs _)))
                      · cases hdec
                  | openBracket => simp [headPunct] at h
                  | openBrace => simp [headPunct] at h
                  | closeBrace => simp [headPunct] at h
                  | comma => simp [headPunct] at h
                  | colon => simp [headPunct] at h
                | null s2 => simp [headPunct] at h
                | bool b2 s2 => simp [headPunct] at h
                | number s2 => simp [headPunct] at h
                | string s2 => simp [headPunct] at h
              · have hnot : ∀ (c : Span) (rest' : List Token),
                    ¬ (tok2 :: rest2 = .punct .closeBracket c :: rest') := by
                  intro c rest' heq
                  have h1 : headPunct .closeBracket (tok2 :: rest2) = true := by
                    rw [heq]; simp [headPunct]
                  exact h h1
                rw [decodeValue] at hdec <;> (first | exact hnot | skip)
                split at hdec
                · rename_i hcond
                  dsimp only at hdec
                  obtain ⟨hs, -⟩ := by
                    simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
                  cases hdv : decodeValue bs (skipFrom bs (i + 1)) (tok2 :: rest2) with
                  | none => rw [hdv] at hdec; cases hdec
                  | some d1 =>
                    rw [hdv] at hdec
                    dsimp only at hdec
                    cases hdt : decodeElemsTail bs d1.cursor d1.rest with
                    | none => rw [hdt] at hdec; cases hdec
                    | some t =>
                      rw [hdt] at hdec
                      dsimp only at hdec
                      split at hdec
                      · rename_i c rest' hC
                        split at hdec
                        · rename_i hcond2
                          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond2
                          obtain ⟨hc, -⟩ := hcond2
                          injection hdec with hd
                          subst hd
                          have hlen1 : (tok2 :: rest2).length < n := by
                            simp only [List.length_cons] at hlen ⊢
                            omega
                          obtain ⟨hV, -, -⟩ := ih (tok2 :: rest2).length hlen1 (tok2 :: rest2) rfl
                          have hlen2 : d1.rest.length < n := by
                            have hsh := d1.shrunk
                            simp only [List.length_cons] at hsh hlen1 ⊢
                            omega
                          obtain ⟨-, hE, -⟩ := ih d1.rest.length hlen2 d1.rest rfl
                          obtain ⟨preD, hsplitD, hgapsD⟩ := hV (skipFrom bs (i + 1)) d1 hdv
                          obtain ⟨preT, hsplitT, hgapsT⟩ := hE d1.cursor t hdt
                          refine ⟨Token.punct .openBracket s ::
                            (preD ++ preT ++ [Token.punct .closeBracket c]), ?_, ?_⟩
                          · rw [hC] at hsplitT
                            simp only [hsplitD, hsplitT, List.cons_append, List.append_assoc,
                              List.singleton_append, List.nil_append]
                          · show Gaps bs i
                              (Token.punct .openBracket s ::
                                (preD ++ preT ++ [Token.punct .closeBracket c])) (t.cursor + 1)
                            rw [hs, hc]
                            have hD : Gaps bs (i + 1) preD d1.cursor :=
                              Gaps.shift (skipFrom_space bs (i + 1)) hgapsD
                            have hDT : Gaps bs (i + 1) (preD ++ preT) t.cursor :=
                              Gaps.append hD hgapsT
                            have hCl : Gaps bs t.cursor
                                [Token.punct .closeBracket ⟨t.cursor, t.cursor + 1⟩]
                                (t.cursor + 1) :=
                              Gaps.cons _ [] (spaceAt_refl bs t.cursor)
                                (Gaps.nil (spaceAt_refl bs (t.cursor + 1)))
                            exact Gaps.cons _ _ (spaceAt_refl bs i) (Gaps.append hDT hCl)
                        · cases hdec
                      · cases hdec
                · cases hdec
          | closeBracket => simp [decodeValue] at hdec
          | openBrace =>
            cases rest with
            | nil => simp [decodeValue] at hdec
            | cons tok2 rest2 =>
              by_cases h : headPunct .closeBrace (tok2 :: rest2) = true
              · cases tok2 with
                | punct k2 s2 =>
                  cases k2 with
                  | closeBrace =>
                      rw [decodeValue] at hdec <;> (first | (intro a b hh; cases hh) | skip)
                      split at hdec
                      · rename_i hcond
                        simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, beq_iff_eq] at hcond
                        obtain ⟨hs, -, hc, -⟩ := hcond
                        injection hdec with hd
                        subst hd
                        refine ⟨[Token.punct .openBrace s, Token.punct .closeBrace s2],
                          by simp, ?_⟩
                        rw [hs, hc]
                        exact Gaps.cons _ _ (spaceAt_refl bs i)
                          (Gaps.cons _ [] (skipFrom_space bs (i + 1))
                            (Gaps.nil (spaceAt_refl bs _)))
                      · cases hdec
                  | openBracket => simp [headPunct] at h
                  | closeBracket => simp [headPunct] at h
                  | openBrace => simp [headPunct] at h
                  | comma => simp [headPunct] at h
                  | colon => simp [headPunct] at h
                | null s2 => simp [headPunct] at h
                | bool b2 s2 => simp [headPunct] at h
                | number s2 => simp [headPunct] at h
                | string s2 => simp [headPunct] at h
              · have hnot : ∀ (c : Span) (rest' : List Token),
                    ¬ (tok2 :: rest2 = .punct .closeBrace c :: rest') := by
                  intro c rest' heq
                  have h1 : headPunct .closeBrace (tok2 :: rest2) = true := by
                    rw [heq]; simp [headPunct]
                  exact h h1
                rw [decodeValue] at hdec <;> (first | exact hnot | skip)
                split at hdec
                · rename_i hcond
                  dsimp only at hdec
                  obtain ⟨hs, -⟩ := by
                    simpa only [Bool.and_eq_true, beq_iff_eq] using hcond
                  cases hkv : decodeValue bs (skipFrom bs (i + 1)) (tok2 :: rest2) with
                  | none => rw [hkv] at hdec; cases hdec
                  | some k =>
                    rw [hkv] at hdec
                    dsimp only at hdec
                    cases hkv2 : k.value with
                    | null => rw [hkv2] at hdec; cases hdec
                    | bool b2 => rw [hkv2] at hdec; cases hdec
                    | number l => rw [hkv2] at hdec; cases hdec
                    | array vs => rw [hkv2] at hdec; cases hdec
                    | object ms => rw [hkv2] at hdec; cases hdec
                    | string cs =>
                      rw [hkv2] at hdec
                      dsimp only at hdec
                      split at hdec
                      · rename_i sc rest1 hColon
                        split at hdec
                        · rename_i hcondC
                          simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcondC
                          obtain ⟨hsc, -⟩ := hcondC
                          subst hsc
                          cases hdv : decodeValue bs (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                          | none => rw [hdv] at hdec; cases hdec
                          | some d1 =>
                            rw [hdv] at hdec
                            dsimp only at hdec
                            cases hdt : decodeMembersTail bs d1.cursor d1.rest with
                            | none => rw [hdt] at hdec; cases hdec
                            | some t =>
                              rw [hdt] at hdec
                              dsimp only at hdec
                              split at hdec
                              · rename_i c rest' hC
                                split at hdec
                                · rename_i hcond2
                                  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond2
                                  obtain ⟨hc, -⟩ := hcond2
                                  injection hdec with hd
                                  subst hd
                                  have hlen1 : (tok2 :: rest2).length < n := by
                                    simp only [List.length_cons] at hlen ⊢
                                    omega
                                  obtain ⟨hV, -, -⟩ :=
                                    ih (tok2 :: rest2).length hlen1 (tok2 :: rest2) rfl
                                  obtain ⟨preK, hsplitK, hgapsK⟩ :=
                                    hV (skipFrom bs (i + 1)) k hkv
                                  have hklen : k.rest.length = rest1.length + 1 := by
                                    rw [hColon]; simp
                                  have hkl : (tok2 :: rest2).length =
                                      preK.length + k.rest.length := by
                                    simpa [List.length_append] using congrArg List.length hsplitK
                                  have hlenR1 : rest1.length < n := by
                                    simp only [List.length_cons] at hlen1 hklen hkl ⊢
                                    omega
                                  obtain ⟨hV1, -, -⟩ := ih rest1.length hlenR1 rest1 rfl
                                  obtain ⟨preD, hsplitD, hgapsD⟩ :=
                                    hV1 (skipFrom bs (skipFrom bs k.cursor + 1)) d1 hdv
                                  obtain ⟨-, -, hM2⟩ :=
                                    ih d1.rest.length (by have hsh := d1.shrunk; omega) d1.rest rfl
                                  obtain ⟨preT, hsplitT, hgapsT⟩ := hM2 d1.cursor t hdt
                                  refine ⟨Token.punct .openBrace s ::
                                    (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                        skipFrom bs k.cursor + 1⟩] ++ preD ++ preT ++
                                      [Token.punct .closeBrace c]), ?_, ?_⟩
                                  · rw [hC] at hsplitT
                                    simp only [hsplitK, hColon, hsplitD, hsplitT,
                                      List.cons_append, List.append_assoc, List.singleton_append,
                                      List.nil_append]
                                  · show Gaps bs i
                                      (Token.punct .openBrace s ::
                                        (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                            skipFrom bs k.cursor + 1⟩] ++ preD ++ preT ++
                                          [Token.punct .closeBrace c])) (t.cursor + 1)
                                    rw [hs, hc]
                                    have hK : Gaps bs (i + 1) preK k.cursor :=
                                      Gaps.shift (skipFrom_space bs (i + 1)) hgapsK
                                    have hKc : Gaps bs (i + 1)
                                        (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                          skipFrom bs k.cursor + 1⟩])
                                        (skipFrom bs k.cursor + 1) :=
                                      Gaps.append hK
                                        (Gaps.cons _ [] (skipFrom_space bs k.cursor)
                                          (Gaps.nil (spaceAt_refl bs (skipFrom bs k.cursor + 1))))
                                    have hD : Gaps bs (skipFrom bs k.cursor + 1) preD d1.cursor :=
                                      Gaps.shift (skipFrom_space bs (skipFrom bs k.cursor + 1)) hgapsD
                                    have hKcD : Gaps bs (i + 1)
                                        ((preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                          skipFrom bs k.cursor + 1⟩]) ++ preD) d1.cursor :=
                                      Gaps.append hKc hD
                                    have hDT : Gaps bs (i + 1)
                                        ((preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                          skipFrom bs k.cursor + 1⟩]) ++ preD ++ preT) t.cursor :=
                                      Gaps.append hKcD hgapsT
                                    have hCl : Gaps bs t.cursor
                                        [Token.punct .closeBrace ⟨t.cursor, t.cursor + 1⟩]
                                        (t.cursor + 1) :=
                                      Gaps.cons _ [] (spaceAt_refl bs t.cursor)
                                        (Gaps.nil (spaceAt_refl bs (t.cursor + 1)))
                                    exact Gaps.cons _ _ (spaceAt_refl bs i) (Gaps.append hDT hCl)
                                · cases hdec
                              · cases hdec
                        · cases hdec
                      · cases hdec
                · cases hdec
          | closeBrace => simp [decodeValue] at hdec
          | comma => simp [decodeValue] at hdec
          | colon => simp [decodeValue] at hdec
    · -- decodeElemsTail
      intro j t hdec
      cases toks with
      | nil =>
        rw [decodeElemsTail] at hdec <;> (first | (intro a b hh; cases hh) | skip)
        injection hdec with hd
        subst hd
        exact ⟨[], by simp, Gaps.nil (skipFrom_space bs j)⟩
      | cons tok rest =>
        by_cases hcm : headPunct .comma (tok :: rest) = true
        · cases tok with
          | punct k s =>
            cases k with
            | comma =>
              rw [decodeElemsTail] at hdec
              split at hdec
              · rename_i hcond
                obtain ⟨hs, -⟩ := by
                  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hcond
                dsimp only at hdec
                cases hdv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
                | none => rw [hdv] at hdec; cases hdec
                | some d =>
                  rw [hdv] at hdec
                  dsimp only at hdec
                  cases hdt : decodeElemsTail bs d.cursor d.rest with
                  | none => rw [hdt] at hdec; dsimp only at hdec; exact absurd hdec (by simp)
                  | some t =>
                    rw [hdt] at hdec
                    dsimp only at hdec
                    injection hdec with hd
                    subst hd
                    have hlen1 : rest.length < n := by
                      simp only [List.length_cons] at hlen
                      omega
                    obtain ⟨hV, -, -⟩ := ih rest.length hlen1 rest rfl
                    have hlen2 : d.rest.length < n := by
                      have := d.shrunk
                      omega
                    obtain ⟨-, hE2, -⟩ := ih d.rest.length hlen2 d.rest rfl
                    obtain ⟨preD, hsplitD, hgapsD⟩ :=
                      hV (skipFrom bs (skipFrom bs j + 1)) d hdv
                    obtain ⟨preT, hsplitT, hgapsT⟩ := hE2 d.cursor t hdt
                    refine ⟨Token.punct .comma s :: (preD ++ preT), ?_, ?_⟩
                    · simp only [hsplitD, hsplitT, List.cons_append, List.append_assoc,
                        List.singleton_append, List.nil_append]
                    · rw [hs]
                      refine Gaps.cons _ (preD ++ preT) (skipFrom_space bs j) ?_
                      exact Gaps.append
                        (Gaps.shift (skipFrom_space bs (skipFrom bs j + 1)) hgapsD) hgapsT
              · cases hdec
            | openBracket => simp [headPunct] at hcm
            | closeBracket => simp [headPunct] at hcm
            | openBrace => simp [headPunct] at hcm
            | closeBrace => simp [headPunct] at hcm
            | colon => simp [headPunct] at hcm
          | null s => simp [headPunct] at hcm
          | bool b s => simp [headPunct] at hcm
          | number s => simp [headPunct] at hcm
          | string s => simp [headPunct] at hcm
        · have hnot : ∀ (c : Span) (rest' : List Token),
              ¬ (tok :: rest = .punct .comma c :: rest') := by
            intro c rest' heq
            have h1 : headPunct .comma (tok :: rest) = true := by
              rw [heq]; simp [headPunct]
            exact hcm h1
          rw [decodeElemsTail] at hdec <;> (first | exact hnot | skip)
          injection hdec with hd
          subst hd
          exact ⟨[], by simp, Gaps.nil (skipFrom_space bs j)⟩
    · -- decodeMembersTail
      intro j t hdec
      cases toks with
      | nil =>
        rw [decodeMembersTail] at hdec <;> (first | (intro a b hh; cases hh) | skip)
        injection hdec with hd
        subst hd
        exact ⟨[], by simp, Gaps.nil (skipFrom_space bs j)⟩
      | cons tok rest =>
        by_cases hcm : headPunct .comma (tok :: rest) = true
        · cases tok with
          | punct k s =>
            cases k with
            | comma =>
              rw [decodeMembersTail] at hdec
              split at hdec
              · rename_i hcond
                obtain ⟨hs, -⟩ := by
                  simpa only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] using hcond
                dsimp only at hdec
                cases hkv : decodeValue bs (skipFrom bs (skipFrom bs j + 1)) rest with
                | none => rw [hkv] at hdec; cases hdec
                | some k =>
                  rw [hkv] at hdec
                  dsimp only at hdec
                  cases hkv2 : k.value with
                  | null => rw [hkv2] at hdec; cases hdec
                  | bool b2 => rw [hkv2] at hdec; cases hdec
                  | number l => rw [hkv2] at hdec; cases hdec
                  | array vs => rw [hkv2] at hdec; cases hdec
                  | object ms => rw [hkv2] at hdec; cases hdec
                  | string cs =>
                    rw [hkv2] at hdec
                    dsimp only at hdec
                    split at hdec
                    · rename_i sc rest1 hColon
                      split at hdec
                      · rename_i hcondC
                        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcondC
                        obtain ⟨hsc, -⟩ := hcondC
                        subst hsc
                        cases hdv : decodeValue bs (skipFrom bs (skipFrom bs k.cursor + 1)) rest1 with
                        | none => rw [hdv] at hdec; cases hdec
                        | some d =>
                          rw [hdv] at hdec
                          dsimp only at hdec
                          cases hdt : decodeMembersTail bs d.cursor d.rest with
                          | none => rw [hdt] at hdec; cases hdec
                          | some t =>
                            rw [hdt] at hdec
                            dsimp only at hdec
                            injection hdec with hd
                            subst hd
                            have hlen1 : rest.length < n := by
                              simp only [List.length_cons] at hlen
                              omega
                            obtain ⟨hV, -, -⟩ := ih rest.length hlen1 rest rfl
                            obtain ⟨preK, hsplitK, hgapsK⟩ :=
                              hV (skipFrom bs (skipFrom bs j + 1)) k hkv
                            have hklen : k.rest.length = rest1.length + 1 := by
                              rw [hColon]; simp
                            have hkl : rest.length = preK.length + k.rest.length := by
                              simpa [List.length_append] using congrArg List.length hsplitK
                            have hlenR1 : rest1.length < n := by
                              omega
                            obtain ⟨hV1, -, -⟩ := ih rest1.length hlenR1 rest1 rfl
                            obtain ⟨preD, hsplitD, hgapsD⟩ :=
                              hV1 (skipFrom bs (skipFrom bs k.cursor + 1)) d hdv
                            obtain ⟨-, -, hM2⟩ :=
                              ih d.rest.length (by have hsh := d.shrunk; omega) d.rest rfl
                            obtain ⟨preT, hsplitT, hgapsT⟩ := hM2 d.cursor t hdt
                            refine ⟨Token.punct .comma s ::
                              (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                  skipFrom bs k.cursor + 1⟩] ++ preD ++ preT), ?_, ?_⟩
                            · simp only [hsplitK, hColon, hsplitD, hsplitT, List.cons_append,
                                List.append_assoc, List.singleton_append, List.nil_append]
                            · rw [hs]
                              refine Gaps.cons _ (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                  skipFrom bs k.cursor + 1⟩] ++ preD ++ preT)
                                (skipFrom_space bs j) ?_
                              have hK : Gaps bs (skipFrom bs j + 1) preK k.cursor :=
                                Gaps.shift (skipFrom_space bs (skipFrom bs j + 1)) hgapsK
                              have hKc : Gaps bs (skipFrom bs j + 1)
                                  (preK ++ [Token.punct .colon ⟨skipFrom bs k.cursor,
                                    skipFrom bs k.cursor + 1⟩])
                                  (skipFrom bs k.cursor + 1) :=
                                Gaps.append hK
                                  (Gaps.cons _ [] (skipFrom_space bs k.cursor)
                                    (Gaps.nil (spaceAt_refl bs (skipFrom bs k.cursor + 1))))
                              have hD : Gaps bs (skipFrom bs k.cursor + 1) preD d.cursor :=
                                Gaps.shift (skipFrom_space bs (skipFrom bs k.cursor + 1)) hgapsD
                              exact Gaps.append (Gaps.append hKc hD) hgapsT
                      · cases hdec
                    · cases hdec
              · cases hdec
            | openBracket => simp [headPunct] at hcm
            | closeBracket => simp [headPunct] at hcm
            | openBrace => simp [headPunct] at hcm
            | closeBrace => simp [headPunct] at hcm
            | colon => simp [headPunct] at hcm
          | null s => simp [headPunct] at hcm
          | bool b s => simp [headPunct] at hcm
          | number s => simp [headPunct] at hcm
          | string s => simp [headPunct] at hcm
        · have hnot : ∀ (c : Span) (rest' : List Token),
              ¬ (tok :: rest = .punct .comma c :: rest') := by
            intro c rest' heq
            have h1 : headPunct .comma (tok :: rest) = true := by
              rw [heq]; simp [headPunct]
            exact hcm h1
          rw [decodeMembersTail] at hdec <;> (first | exact hnot | skip)
          injection hdec with hd
          subst hd
          exact ⟨[], by simp, Gaps.nil (skipFrom_space bs j)⟩

/-- **The chain a decoded tape's tokens form.**  `decodeTape`'s trailing
`skipFrom` check extends the decoded value's chain to the whole document. -/
theorem gaps_of_decodeTape {t : Tape} {v : JSON.Value}
    (hdec : decodeTape t = some v) :
    Gaps t.input (skipFrom t.input 0) t.tokens t.input.length := by
  unfold decodeTape at hdec
  split at hdec
  · rename_i d hdv
    split at hdec
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      obtain ⟨hrest, hskip⟩ := hcond
      obtain ⟨pre, hsplit, hgaps⟩ :=
        (decode_gaps_aux t.input t.tokens.length t.tokens rfl).1
          (skipFrom t.input 0) d hdv
      have htoks : t.tokens = pre := by
        rw [hrest, List.append_nil] at hsplit
        exact hsplit
      have hspace : SpaceAt t.input d.cursor t.input.length := by
        rw [← hskip]
        exact skipFrom_space t.input d.cursor
      rw [htoks]
      exact Gaps.end_space hgaps hspace
    · exact absurd hdec (by simp)
  · exact absurd hdec (by simp)

/-- **A whitespace range over a literal document is the tape's clause.**  For a
position inside the document the literal's lookup is the list's, so `SpaceAt`
reads as `StopToEntrySpace`. -/
theorem stopToEntrySpace_of_spaceAt {bl : List UInt8} {B : Bytes}
    (hB : B = ByteString.literal bl) {a b : Nat}
    (h : SpaceAt B a b) (hb : b ≤ bl.length) : StopToEntrySpace bl a b := by
  refine ⟨h.1, ?_⟩
  intro j hj hjb
  have hjl : j < bl.length := by omega
  have hget : B[j]? = some (bl.getD j 0) := by
    rw [hB, ByteString.getElem?_literal, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjl, Option.getD_some]
  exact h.2 j (bl.getD j 0) hj hjb hget

/-- **A gap chain is the tape's clause.**  The per-index range is `Gaps.get?`;
`checkSpans` places every successor's start inside the document, so the range's
end is in bounds and the conversion is `stopToEntrySpace_of_spaceAt`. -/
theorem tokenGapsSpace_of_gaps {bl : List UInt8} {B : Bytes}
    (hB : B = ByteString.literal bl) {a : Nat} {toks : List Token}
    (hgaps : Gaps B a toks B.length) (hspans : checkSpans B toks 0 = true) :
    TokenGapsSpace bl toks bl.length := by
  have hBlen : B.length = bl.length := by
    rw [hB, ByteString.length_eq_size, ByteString.size_literal]
  intro k tok htok
  have hsp := Gaps.get? hgaps k tok htok
  simp only [nextBound_drop, hBlen] at hsp
  have hbound : (match toks[k+1]? with
      | some next => next.span.start
      | none => bl.length) ≤ bl.length := by
    cases hk : toks[k+1]? with
    | none => exact Nat.le_refl _
    | some next =>
        obtain ⟨hlt, hle, -⟩ :=
          checkSpans_mem (prev := 0) hspans (List.mem_of_getElem? hk)
        show next.span.start ≤ bl.length
        omega
  exact stopToEntrySpace_of_spaceAt hB hsp hbound

/-- **A decoded tape's gaps are whitespace.**  `gaps_of_decodeTape` at the tape's
document and `tokenGapsSpace_of_gaps` at the tape's span discipline. -/
theorem tokenGapsSpace_of_decodeTape {t : Tape} {v : JSON.Value} {bl : List UInt8}
    (hdec : decodeTape t = some v) (hin : t.input = ByteString.literal bl) :
    TokenGapsSpace bl t.tokens bl.length := by
  have hspans : spansWellFormed t = true := (tape_valid t v hdec).1
  have hgaps := gaps_of_decodeTape hdec
  have hlenB : (ByteString.literal bl).length = bl.length := by
    rw [ByteString.length_eq_size, ByteString.size_literal]
  have hle : bl.length = t.input.length := by rw [hin, hlenB]
  have hgaps' : Gaps (ByteString.literal bl)
      (skipFrom (ByteString.literal bl) 0) t.tokens bl.length := by
    rw [← hin, hle]
    exact hgaps
  have hspans' : checkSpans (ByteString.literal bl) t.tokens 0 = true := by
    rw [← hin]
    simpa [spansWellFormed] using hspans
  exact tokenGapsSpace_of_gaps (B := ByteString.literal bl) rfl hgaps' hspans'

/-- **The production.**  A `parseBytes` acceptance's tape has whitespace in every
inter-token gap and after its last token: the decoder's chain
(`tokenGapsSpace_of_decodeTape`) at the tape `decodeTape_correct` produces. -/
theorem parseBytes_tokenGapsSpace {l : Limits} {bl : List UInt8} {t : Tape}
    (hparse : parseBytes l (ByteString.literal bl) = .ok t) :
    TokenGapsSpace bl t.tokens bl.length := by
  obtain ⟨v, hdec, hin, -⟩ := decodeTape_correct l (ByteString.literal bl) t hparse
  exact tokenGapsSpace_of_decodeTape hdec hin

/-- **The number arm's premises from a parse acceptance, the alignment and the
scan's answer.**  No `NumberExtentAssumed` and no gap hypothesis remain: the
parse's token list has whitespace gaps (`parseBytes_tokenGapsSpace`), the
alignment turns them into `WalkAlignGaps` (`WalkAlignGaps.of_tokenGaps`), and the
scan's own answer at the token's lane closes the stop equation
(`NumberExtentAssumed.of_scanArm`).  The tape, the token and `hparse` supply the
span's maximal run and its bounds.  The consequent is
`numberArmPremises_of_parseAssumed`'s five premises. -/
theorem numberArmPremises_of_parse_scan {l : Limits} {t : Tape}
    {bs : List UInt8} {sp : Span} {lane q : Nat} {m0 : Mem} {G : WalkGeom m0} {k : Nat}
    (hparse : parseBytes l (ByteString.literal bs) = .ok t)
    (hal : WalkAlign G t)
    (hk : t.tokens[k]? = some (Token.number sp))
    (hlane : lane = sp.start)
    (hscan : ScanArm bs lane q
      (if k + 1 < G.nep then entryPos G (k + 1) else G.n)) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop lane).take (q - lane) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            q = lane + lex.length ∧
              (numFastEmitted (ByteString.literal lex)).toBits =
                (strtodSpec d).toBits := by
  obtain ⟨v, hdec, hin, -⟩ := decodeTape_correct l (ByteString.literal bs) t hparse
  have htok : Token.number sp ∈ t.tokens := List.mem_of_getElem? hk
  have hstart : sp.start ≤ sp.stop := tape_number_start_le_stop hdec hin htok
  have hstop_le : sp.stop ≤ bs.length := by
    have hspans : checkSpans (ByteString.literal bs) t.tokens 0 = true := by
      simpa [spansWellFormed, hin] using (tape_valid t v hdec).1
    exact (checkSpans_mem (prev := 0) hspans htok).2.1
  have hslice : (bs.drop sp.start).take (sp.stop - sp.start) =
      (numRunFrom (ByteString.literal bs) sp.start).data.toList :=
    tape_number_maximal_run hdec hin htok
  -- the alignment's document is the parsed one
  have hGb : G.bs = bs := by
    have h1 : ByteString.literal G.bs = ByteString.literal bs := by
      rw [← hal.input, hin]
    have h2 := congrArg (fun b : ByteString => b.toList) h1
    simpa using h2
  have hlen : G.n = G.bs.length :=
    (JsonEntrySteps.readBytes_length m0 G.b G.n G.doc).symm
  have hlen' : G.n = bs.length := by rw [hlen, hGb]
  -- the parse's gaps, at the alignment's document
  have hgaps : TokenGapsSpace G.bs t.tokens G.n := by
    rw [hGb, hlen']
    exact parseBytes_tokenGapsSpace hparse
  have hwalk : WalkAlignGaps G t := WalkAlignGaps.of_tokenGaps hal hgaps
  have hgap : StopToEntrySpace bs sp.stop
      (if k + 1 < G.nep then entryPos G (k + 1) else G.n) := by
    have hthis := hwalk.at hk
    rw [hGb] at hthis
    exact hthis
  exact numberArmPremises_of_parseAssumed hparse htok
    (NumberExtentAssumed.of_scanArm hlane hstart hstop_le hslice hgap hscan) hlane

/-! ### Axiom footprints -/

#print axioms classOfByte_eq_none_of_isSpace
#print axioms WalkAlign.entryPos_next_ne_stop_of_isSpace
#print axioms WalkAlign.not_stops_of_isSpace
#print axioms WalkAlign.isSpace_false_of_stops
#print axioms WalkAlignGaps.at
#print axioms WalkAlignGaps.of_tokenGaps
#print axioms numRun_all_constituent
#print axioms numConstituent_not_space
#print axioms numRun_getD_not_space
#print axioms numRunFrom_take_not_space
#print axioms stop_eq_of_gap_loop
#print axioms stop_eq_of_gap_direct
#print axioms numberExtentAssumed_of_gap_loop
#print axioms numberExtentAssumed_of_gap_direct
#print axioms isSpaceB_iff_skipWs
#print axioms isSpaceB_eq_false_iff
#print axioms ScanArm.of_scalarSkip
#print axioms NumberExtentAssumed.of_scanArm
#print axioms numberArmPremises_of_parse_scan
#print axioms spaceAt_refl
#print axioms spaceAt_trans
#print axioms Gaps.first_space
#print axioms Gaps.shift
#print axioms Gaps.append
#print axioms Gaps.end_space
#print axioms nextBound_drop
#print axioms Gaps.get?
#print axioms gaps_of_decodeTape
#print axioms stopToEntrySpace_of_spaceAt
#print axioms tokenGapsSpace_of_gaps
#print axioms tokenGapsSpace_of_decodeTape
#print axioms parseBytes_tokenGapsSpace

end LeanLLVM.Refinement
