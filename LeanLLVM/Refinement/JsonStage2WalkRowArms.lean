/-
The payload rows at the arm: their `WalkSegment`s produced, not taken.

`JsonStage2WalkRowSteps` closes the payload documents with each payload arm's
`WalkSegment` to the merge among the row's premises.  That premise is the dispatch
layer's, and at the number's continuing route it is a theorem:
`walkRevolutionMergeSegScalar` runs the head's eight links, the byte's own route, the
tail's three calls and the merge, and ends at `scMergeC C f.ev` with the index kept
(`scMergeC_k`) and the arm's one record appended (the carry's `events` field).  So the
row's two segment premises, its two index facts and its two record facts are produced
here from the head's bundle, and `row_numberDocument` is called at them.

**What the row still takes.**  The row is about the *walk's* trace, so the facts that
name a run's state are premises and not derivable from the document: the tape's
acceptance and the alignment (`decodeTape`, `WalkAlign`), the seed's correspondence and
the opener's carry, the two head states' `WalkInv`s and their bundles
(`HcontScalarFacts`), and the arm's *payload* — the record the number scan appended,
`f.ev = EventRecord.number (strtodSpec d).toBits`.  The last is the numeral's read-back,
the number side's counterpart of a string's escape read-back: `JsonStage2Helpers`'
`s2ScalarValue_appended` shows the record is `numFastEmitted`'s bits of the memory
window the scan read, and tying that window to the token's span is the arm's premise,
not the row's.

**The string rows are not instantiable at this staging, and why.**  The ABI's entry
stream is "quote characters, the structural bytes and the first byte of every scalar"
(`kernel/json/stage2.h:60`), so `["ab","cd"]`'s entries are `[0,1,4,5,6,9,10]` — seven,
with one per quote.  `WalkAlign` instead states `G.nep = t.tokens.length` and a token
starting at every entry, which is the token-start stream `[0,1,5,6,10]` that
`row_stringPlainDocument` fixes.  The string arm reads the *next* lane as the closing
quote (`if.end207.i`'s `%5 + %inc.i`), forms the body extent `close - idxprom - 1`
(`%sub260.i`) and advances the index by two (`%inc208.i`), so at the token-start stream it
would read `close = 5` (body extent three, not two) and skip the comma.  A string row
therefore needs the quote-inclusive entry stream and an alignment keyed to the string
spans' stops, and the string arm's composition needs its appended record exposed:
`stringPath_seg` returns its endpoint existentially and states its block, index,
predecessor and registers, but not the trace that endpoint carries.  Neither is this
module's to change.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2WalkRowSteps
import LeanLLVM.Refinement.JsonStage2WalkHcontScalar

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.WalkScope

/-! ### The number arm's revolution

The arm's counted run from the loop head to the merge, its endpoint's two facts, and the
step the row takes from them.  The record is the one the arm appended; the payload
read-back names it. -/

/-- **The number arm's revolution.**  `walkRevolutionMergeSegScalar` produces the
segment to `scMergeC C f.ev`, its merge index and its block; the record it appended is
`f.ev`, so the revolution is the row's step at the arm's own carry rather than at a
supplied one.  `hev` is the numeral's read-back: the scan's record is `strtodSpec`'s
bits of the decomposition the row already proves from the document's bytes. -/
theorem payloadRevolution_number_arm {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {C : WalkCarry G} {s : State} (arena : List UInt8) (hal : WalkAlign G t)
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hcont : C.k + 1 < G.nep) {v : JSON.Value} (hdec : decodeTape t = some v)
    {b0 : UInt8} (hbyte : entryByte G C.k = b0) (hb : b0 = 0x2D ∨ IsDigitB b0 = true)
    {d : Decimal} (hwf : d.wellFormed)
    (hlex : ∀ sp : Span, t.tokens[C.k]? = some (.number sp) →
      d.lexeme.data.toList = (G.bs.drop sp.start).take (sp.stop - sp.start))
    (hpre : WalkTracePrefix G arena t C)
    (f : WalkScope.HcontScalarFacts G C s)
    (hev : f.ev = EventRecord.number (strtodSpec d).toBits) :
    WalkPayloadRevolution G arena t C s (WalkScope.scMergeC C f.ev) (WalkScope.scMergeF f)
      (((8 + WalkScope.hlastByteCount f.hb) + 3) + 1)
      (EventRecord.number (strtodSpec d).toBits) ∧
    (WalkScope.scMergeC C f.ev).block = "cleanup478.i" := by
  obtain ⟨hseg, -, hblockD, -, hkC, -, -, -⟩ :=
    WalkScope.walkRevolutionMergeSegScalar G C s hInv hblock hcont f
  have hklt : C.k < G.nep := by omega
  refine ⟨?_, hblockD⟩
  exact payloadRevolution_number (d := d) arena hal hInv hklt hdec hbyte hb hwf hlex hpre
    hseg hkC (by rw [← hev])

/-- **The number arm's segment, its index and its record.**  The three premises
`row_numberDocument` takes per payload, at the bundle the arm consumes: the segment is
the composed route, the index is the merge carry's kept one, and the record is the
arm's, named at the numeral's read-back.  `hcont` is the arm's own count guard; the
composition takes it and does not read it (`walkRevolutionMergeSegScalar`'s `_hk`), so
it is stated where the dispatch states it rather than dropped. -/
theorem numberArmSegment {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hInv : WalkInv G C s) (hblock : C.block = walkLoopHead)
    (hcont : C.k + 1 < G.nep)
    (f : WalkScope.HcontScalarFacts G C s) {d : Decimal}
    (hev : f.ev = EventRecord.number (strtodSpec d).toBits) :
    ∃ p : Nat,
      WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s (WalkScope.scMergeC C f.ev)
        (WalkScope.scMergeF f) p ∧
      (WalkScope.scMergeC C f.ev).k = C.k ∧
      (WalkScope.scMergeC C f.ev).events =
        C.events ++ [EventRecord.number (strtodSpec d).toBits] := by
  obtain ⟨hseg, -, -, -, hkC, -, -, -⟩ :=
    WalkScope.walkRevolutionMergeSegScalar G C s hInv hblock hcont f
  refine ⟨_, hseg, hkC, ?_⟩
  rw [← hev]

/-! ### The document `[1,2]`, its payload segments produced

`row_numberDocument`'s row, at the two head bundles: the segments, their merge indices
and their records are `numberArmSegment`'s, and everything else is the row's own
derivation from the document's bytes and the tape.  The heads' guards `C.k + 1 < G.nep`
are the document's: the row fixes the index at one and three and the stream at five. -/

/-- **The document `[1,2]`'s row from the two number arms.** -/
theorem row_numberDocument_arm {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₃ : WalkCarry G} {s₁ s₃ : State} {v : JSON.Value}
    (hal : WalkAlign G t) (hspans : spansWellFormed t = true)
    (hbs : G.bs = numberDocumentBytes) (hent : G.ent = [0, 1, 2, 3, 4])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .number ⟨1, 2⟩,
      .punct .comma ⟨2, 3⟩, .number ⟨3, 4⟩, .punct .closeBracket ⟨4, 5⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hInv₁ : WalkInv G C₁ s₁) (hblock₁ : C₁.block = walkLoopHead)
    (f₁ : WalkScope.HcontScalarFacts G C₁ s₁)
    (hev₁' : f₁.ev = EventRecord.number (strtodSpec decimalOne).toBits)
    (hk₃ : C₃.k = C₁.k + 2)
    (hev₃ : C₃.events = C₁.events ++ [EventRecord.number (strtodSpec decimalOne).toBits])
    (hInv₃ : WalkInv G C₃ s₃) (hblock₃ : C₃.block = walkLoopHead)
    (f₂ : WalkScope.HcontScalarFacts G C₃ s₃)
    (hev₂' : f₂.ev = EventRecord.number (strtodSpec decimalTwo).toBits) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.number (strtodSpec decimalOne).toBits,
        EventRecord.number (strtodSpec decimalTwo).toBits,
        EventRecord.tag 4] : List EventRecord) := by
  have hk5 : G.nep = 5 := by simp [hal.tokens_length, htokens]
  have hk₁v : C₁.k = 1 := by omega
  have hk₃v : C₃.k = 3 := by omega
  have hcont₁ : C₁.k + 1 < G.nep := by omega
  have hcont₃ : C₃.k + 1 < G.nep := by omega
  obtain ⟨p₁, hseg₁, hkc₁, hevc₁⟩ :=
    numberArmSegment hInv₁ hblock₁ hcont₁ f₁ hev₁'
  obtain ⟨p₂, hseg₂, hkc₂, hevc₂⟩ :=
    numberArmSegment hInv₃ hblock₃ hcont₃ f₂ hev₂'
  exact row_numberDocument (p₁ := p₁) (p₂ := p₂) (Cd₁ := WalkScope.scMergeC C₁ f₁.ev)
    (sd₁ := WalkScope.scMergeF f₁) (Cd₂ := WalkScope.scMergeC C₃ f₂.ev)
    (sd₂ := WalkScope.scMergeF f₂) hal hspans hbs hent htokens hdec hpre₀ hk₀ hk₁ hev₁
    hInv₁ hseg₁ hkc₁ hevc₁ hk₃ hev₃ hInv₃ hseg₂ hkc₂ hevc₂

/-! ### Axiom footprints

Each is the dispatch layer's ceiling rather than the row engine's: the composition's
branch selections carry `Classical.choice`, as `stringPath_seg`'s fifteen-link one does.
`payloadStep_of_segment`, which is the row's own step, stays at `propext`. -/

/-- info: 'LeanLLVM.Refinement.payloadRevolution_number_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms payloadRevolution_number_arm

/-- info: 'LeanLLVM.Refinement.numberArmSegment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms numberArmSegment

/-- info: 'LeanLLVM.Refinement.row_numberDocument_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_numberDocument_arm

end LeanLLVM.Refinement
