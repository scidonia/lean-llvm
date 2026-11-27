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
and `numberArmPremises_of_parse_scan` is the whole consumer: parse acceptance, the
token, the lane's identity, the gap and `ScanArm` give the number arm's five
premises with no extent hypothesis anywhere.

## The residue

The one premise not produced here is the gap's initialisation from the parse.
The stage-1 emitter cannot supply it: its mask is a byte classifier (above), it
never reads a tape, and its entry stream is a function of the document's bytes
alone, so it cannot know which byte a parse ended a number on.  `TokenGapsSpace`
is the clause stated over the tape, and `WalkAlignGaps.of_tokenGaps` shows that
`WalkAlign` plus `TokenGapsSpace` yields `WalkAlignGaps` — so the residue is one
tape-level statement, not a property of the alignment.  What can supply it is the
parser's whitespace skip — `parseBytes` calls `parseValue` and then requires
`skipFrom bs p.next = bs.length`, and the tape's tokens are the parser's — but
the tree records the tape's spans only through `checkSpans` (`prev ≤ s.start`)
and `TokenBytes` (each token's own bytes), neither of which says anything about
the bytes in a gap.  The missing statement is

`parseBytes l (ByteString.literal bs) = .ok t → TokenGapsSpace bs t.tokens bs.length`

and it is a new invariant over `parseValue`/`parseElemsTail`/`parseMembersTail`'s
token lists (the `parse_all` induction's shape with a token-gap clause), not a
predicate the tree already carries.  This module states the clause, proves its
initialiser and its consumers including the scan re-export, and leaves that one
production open rather than assuming the false `WalkAlignStops`.
-/
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

/-- **The number arm's premises from a parse acceptance and the scan's answer.**
No `NumberExtentAssumed` remains as a hypothesis: the tape, the token and
`hparse` give the span's maximal run and its bounds, `hgap` is the document's
inter-token whitespace, and `hscan` is the scan's own answer at the token's lane.
The consequent is `numberArmPremises_of_parseAssumed`'s five premises. -/
theorem numberArmPremises_of_parse_scan {l : Limits} {t : Tape}
    {bs : List UInt8} {sp : Span} {lane q cond : Nat}
    (hparse : parseBytes l (ByteString.literal bs) = .ok t)
    (htok : Token.number sp ∈ t.tokens)
    (hlane : lane = sp.start) (hgap : StopToEntrySpace bs sp.stop cond)
    (hscan : ScanArm bs lane q cond) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop lane).take (q - lane) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            q = lane + lex.length ∧
              (numFastEmitted (ByteString.literal lex)).toBits =
                (strtodSpec d).toBits := by
  obtain ⟨v, hdec, hin, -⟩ := decodeTape_correct l (ByteString.literal bs) t hparse
  have hstart : sp.start ≤ sp.stop := tape_number_start_le_stop hdec hin htok
  have hstop_le : sp.stop ≤ bs.length := by
    have hspans : checkSpans (ByteString.literal bs) t.tokens 0 = true := by
      simpa [spansWellFormed, hin] using (tape_valid t v hdec).1
    exact (checkSpans_mem (prev := 0) hspans htok).2.1
  have hslice : (bs.drop sp.start).take (sp.stop - sp.start) =
      (numRunFrom (ByteString.literal bs) sp.start).data.toList :=
    tape_number_maximal_run hdec hin htok
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

end LeanLLVM.Refinement
