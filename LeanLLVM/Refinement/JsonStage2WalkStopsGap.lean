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

The residue is the clause's initialisation.  The stage-1 emitter cannot supply
it: its mask is a byte classifier (above), it never reads a tape, and its entry
stream is a function of the document's bytes alone, so it cannot know which byte
a parse ended a number on.  `TokenGapsSpace` is the clause stated over the tape,
and `WalkAlignGaps.of_tokenGaps` shows that `WalkAlign` plus `TokenGapsSpace`
yields `WalkAlignGaps` — so the residue is one tape-level statement, not a
property of the alignment.  What can supply it is the parser's whitespace skip —
`parseBytes` calls `parseValue` and then requires `skipFrom bs p.next =
bs.length`, and the tape's tokens are the parser's — but the tree records the
tape's spans only through `checkSpans` (`prev ≤ s.start`) and `TokenBytes` (each
token's own bytes), neither of which says anything about the bytes in a gap.  A
theorem `parseBytes_gaps_are_space` (parse acceptance implies `TokenGapsSpace`)
is therefore the exact missing premise; this module states the clause, proves
its initialiser and consumers, and leaves that one production open rather than
assuming the false `WalkAlignStops`.
-/
import LeanLLVM.Refinement.JsonNumberExtentAssumed

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

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

/-! ### The clause's initialisation, as the tape-level residue

`WalkAlignGaps` is not a fact about the emitter; it is a fact about the
document's gaps.  Stated over the tape, `TokenGapsSpace` says every token's stop
is followed by whitespace up to the next token's start, or up to the document's
end at the last token.  Given `WalkAlign`, whose successor clause names the next
entry, that supplies `WalkAlignGaps` — so the only premise left is
`TokenGapsSpace`, and the theorem that a parse acceptance supplies it. -/

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

/-! ### Axiom footprints -/

#print axioms classOfByte_eq_none_of_isSpace
#print axioms WalkAlign.entryPos_next_ne_stop_of_isSpace
#print axioms WalkAlign.not_stops_of_isSpace
#print axioms WalkAlign.isSpace_false_of_stops
#print axioms WalkAlignGaps.at
#print axioms WalkAlignGaps.of_tokenGaps
#print axioms stop_eq_of_gap_loop
#print axioms stop_eq_of_gap_direct
#print axioms numberExtentAssumed_of_gap_loop
#print axioms numberExtentAssumed_of_gap_direct

end LeanLLVM.Refinement
