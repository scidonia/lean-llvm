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

**The string rows at the staged stream.**  The ABI's entry stream is "quote
characters, the structural bytes and the first byte of every scalar"
(`kernel/json/stage2.h:60`), so `["ab","cd"]`'s entries are `[0,1,4,5,6,9,10]` — seven,
one per quote — and not the token-start stream `[0,1,5,6,10]`.  `WalkAlignQuoted`
(`JsonStage2WalkAlignment`) states that staging, and
`WalkAlignQuoted.stringExtent` is the arm's reading of it: the lane after a string's
start lane is its closing quote, so `close = lane k + 1` is `span.stop - 1` and the
body extent `close - idxprom - 1` (`%sub260.i`) is the span's body.  The arm's
composition exposes the record it appends — `stringPath_seg` ends at the merge carry
with `∃ key len off, Cd.events = C.events ++ [str key len off]`, and at the literal
selector with that arm's own extent and span word — so `stringArmSegment` produces
the segment, the kept index and the record, and `row_stringPlainDocument_arm` calls
the plain row at the two lane heads.  The entry index moves by two at each string
(`%inc208.i`) and the token count by one.  The arena form's arm and the general
document's induction are what remain after this one.

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

/-! ### The string arm at the staged stream

`["ab","cd"]`'s two strings are at the staged stream's lanes one and four.  The arm's
composition is `stringPath_seg`: fifteen links from `NodeBlock21` to the merge, the
entry index kept and one record appended.  The record it appends is the *literal*
arm's when the body's answer is `1` — `%sub260.i`'s extent for the length and
`%or.i`'s position with the top bit set for the span — and that is the form
`row_stringPlainDocument` names.  `stringPath_seg` exposes the arm's record at that
selector; the two readings are converted at the document's lanes below.

**What the arm still takes.**  The bundle `HstringFacts` supplies the head's byte,
counts, call and body answer; `HstringResidue` carries nothing.  The literal
selector `f.y = 1` and the body's raw read-back are the arm's premises, as the
number row's `f.ev` read-back is its own.  The heads' blocks are the loop's
(`walkLoopHead` is `"NodeBlock21"`). -/

/-- **The literal arm's span word.**  `strOr` is the position's successor with the
top bit set; below `2 ^ 32` the successor does not wrap, so the word is
`plainSpan` of the next position. -/
theorem strOr_toNat_plainSpan {x : BitVec 32} (h32 : x.toNat + 1 < 2 ^ 32) :
    (strOr x).toNat = plainSpan (x.toNat + 1) := by
  have hlit : (9223372036854775808 : Nat) = 2 ^ 63 := by decide
  unfold strOr plainSpan
  rw [hlit]
  have h1 : (BitVec.ofNat 32 1).toNat = 1 := by decide
  have hx1 : (x + BitVec.ofNat 32 1).toNat = x.toNat + 1 := by
    rw [BitVec.toNat_add, h1]
    exact Nat.mod_eq_of_lt h32
  have hof : (BitVec.ofNat 64 (x + BitVec.ofNat 32 1).toNat).toNat = x.toNat + 1 := by
    rw [BitVec.toNat_ofNat, hx1]
    exact Nat.mod_eq_of_lt (by
      have hp : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
      omega)
  have hhi : (BitVec.ofNat 64 (2 ^ 63)).toNat = 2 ^ 63 := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by decide)
  rw [BitVec.toNat_or, hof, hhi]
  exact Nat.or_two_pow_eq_add_of_lt (by
    have hp : (2 : Nat) ^ 32 < 2 ^ 63 := by decide
    omega)

/-- **The literal string arm's segment, its index and its record.**  `stringPath_seg`
composes the fifteen links and keeps the entry index; its record is the literal
arm's, at the bundle's own extent and the position's successor.  The row's record
is this one read at the document's lanes. -/
theorem stringArmSegment {m0 : Mem} {G : WalkGeom m0} {C : WalkCarry G} {s : State}
    (hblock : C.block = walkLoopHead) (hInv : WalkInv G C s)
    (f : WalkScope.HstringFacts G C s) (hsp0 : C.sp = 0)
    (R : WalkScope.HstringResidue G C s f)
    (hR8 : evalICmp .slt f.y (BitVec.ofNat 32 1) = 0)
    (hy1 : evalICmp .eq f.y (BitVec.ofNat 32 1) = 1) :
    ∃ (Cd : WalkCarry G) (sd : State),
      WalkScope.WalkSegment (stage2Calls stage2SubCalls) G C s Cd sd 15 ∧
      Cd.k = C.k ∧
      Cd.events = C.events ++ [EventRecord.str false
        ((BitVec.ofNat 64 f.ext).toNat % 2 ^ 32)
        (strOr (BitVec.ofNat 32 (entryPos G C.k))).toNat] := by
  obtain ⟨Cd, sd, hseg, -, hk, -, -, -, -, -, hrec⟩ :=
    WalkScope.stringPath_seg G C s (by simpa [walkLoopHead] using hblock) hInv f hsp0 R hR8
  exact ⟨Cd, sd, hseg, hk, hrec hy1⟩

/-- **The document `["ab","cd"]`'s row from the two literal string arms.**  The heads
are at lanes one and four; the segments, their kept indices and their records are
`stringArmSegment`'s, and the records' raw readings are converted at the document's
lanes — the extent `4 - 1 - 1 = 2` and `9 - 6 - 1 = 2`, the spans `plainSpan 2` and
`plainSpan 7`.  The next carries after each merge (`%inc208.i`) and the comma's
silent advance stay the walk's premises, as they are for the number document. -/
theorem row_stringPlainDocument_arm {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    {arena : List UInt8} {C₀ C₁ C₂ C₃ C₄ C₅ : WalkCarry G}
    {s₁ s₃ : State} {v : JSON.Value}
    (hal : WalkAlignQuoted G t)
    (hbs : G.bs = stringDocumentBytes) (hent : G.ent = [0, 1, 4, 5, 6, 9, 10])
    (htokens : t.tokens = [.punct .openBracket ⟨0, 1⟩, .string ⟨1, 5⟩,
      .punct .comma ⟨5, 6⟩, .string ⟨6, 10⟩, .punct .closeBracket ⟨10, 11⟩])
    (hdec : decodeTape t = some v)
    (hpre₀ : WalkTracePrefix G arena t C₀) (hk₀ : C₀.k = 0)
    (hk₁ : C₁.k = C₀.k + 1) (hev₁ : C₁.events = C₀.events ++ [EventRecord.tag 3])
    (hInv₁ : WalkInv G C₁ s₁) (hblock₁ : C₁.block = walkLoopHead)
    (f₁ : WalkScope.HstringFacts G C₁ s₁) (hsp0₁ : C₁.sp = 0)
    (R₁ : WalkScope.HstringResidue G C₁ s₁ f₁)
    (hR8₁ : evalICmp .slt f₁.y (BitVec.ofNat 32 1) = 0)
    (hy1₁ : evalICmp .eq f₁.y (BitVec.ofNat 32 1) = 1)
    (hk₂ : C₂.k = C₁.k + 2)
    (hev₂ : C₂.events = C₁.events ++
      [EventRecord.str false (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1)
        (plainSpan (entryPos G C₁.k + 1))])
    (hbody₁ : ∀ (sp : Span) (cs : List Nat), bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((G.bs.drop (sp.start + 1)).take
        (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1)) = some cs)
    (hk₃ : C₃.k = C₂.k + 1) (hev₃ : C₃.events = C₂.events)
    (hInv₃ : WalkInv G C₃ s₃) (hblock₃ : C₃.block = walkLoopHead)
    (f₂ : WalkScope.HstringFacts G C₃ s₃) (hsp0₂ : C₃.sp = 0)
    (R₂ : WalkScope.HstringResidue G C₃ s₃ f₂)
    (hR8₂ : evalICmp .slt f₂.y (BitVec.ofNat 32 1) = 0)
    (hy1₂ : evalICmp .eq f₂.y (BitVec.ofNat 32 1) = 1)
    (hk₄ : C₄.k = C₃.k + 2)
    (hev₄ : C₄.events = C₃.events ++
      [EventRecord.str false (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1)
        (plainSpan (entryPos G C₃.k + 1))])
    (hbody₂ : ∀ (sp : Span) (cs : List Nat), bodyCodePoints G.bs sp = some cs →
      escapeCodePoints ((G.bs.drop (sp.start + 1)).take
        (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1)) = some cs)
    (hk₅ : C₅.k = C₄.k + 1) (hev₅ : C₅.events = C₄.events ++ [EventRecord.tag 4]) :
    WalkTraceRow G.bs arena t
      ([EventRecord.tag 3, EventRecord.str false 2 (plainSpan 2),
        EventRecord.str false 2 (plainSpan 7), EventRecord.tag 4] : List EventRecord) := by
  -- the heads' lanes
  have hk₁v : C₁.k = 1 := by omega
  have hk₃v : C₃.k = 4 := by omega
  have hp₁ : entryPos G C₁.k = 1 := by simp [entryPos, hk₁v, hent]
  have hp₁' : entryPos G (C₁.k + 1) = 4 := by
    have hk : C₁.k + 1 = 2 := by omega
    simp [entryPos, hk, hent]
  have hp₃ : entryPos G C₃.k = 6 := by simp [entryPos, hk₃v, hent]
  have hp₃' : entryPos G (C₃.k + 1) = 9 := by
    have hk : C₃.k + 1 = 5 := by omega
    simp [entryPos, hk, hent]
  -- the first string: the arm's segment, keep and record
  obtain ⟨Cd₁, sd₁, hseg₁, hkc₁, hevc₁raw⟩ :=
    stringArmSegment hblock₁ hInv₁ f₁ hsp0₁ R₁ hR8₁ hy1₁
  have hf₁ : f₁.ext = 2 := by
    have h := f₁.hext
    have hix := f₁.hixPos
    omega
  have hlen₁ : (BitVec.ofNat 64 f₁.ext).toNat % 2 ^ 32
      = entryPos G (C₁.k + 1) - entryPos G C₁.k - 1 := by
    rw [hf₁, hp₁', hp₁, BitVec.toNat_ofNat]
    decide
  have hoff₁ : (strOr (BitVec.ofNat 32 (entryPos G C₁.k))).toNat
      = plainSpan (entryPos G C₁.k + 1) := by
    have hx : (BitVec.ofNat 32 (entryPos G C₁.k)).toNat = entryPos G C₁.k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by rw [hp₁]; decide)
    simpa [hx] using strOr_toNat_plainSpan (x := BitVec.ofNat 32 (entryPos G C₁.k))
      (by rw [hx, hp₁]; decide)
  have hevc₁ : Cd₁.events = C₁.events ++
      [EventRecord.str false (entryPos G (C₁.k + 1) - entryPos G C₁.k - 1)
        (plainSpan (entryPos G C₁.k + 1))] := by
    rw [hevc₁raw, hlen₁, hoff₁]
  -- the second string
  obtain ⟨Cd₂, sd₂, hseg₂, hkc₂, hevc₂raw⟩ :=
    stringArmSegment hblock₃ hInv₃ f₂ hsp0₂ R₂ hR8₂ hy1₂
  have hf₂ : f₂.ext = 2 := by
    have h := f₂.hext
    have hix := f₂.hixPos
    omega
  have hlen₂ : (BitVec.ofNat 64 f₂.ext).toNat % 2 ^ 32
      = entryPos G (C₃.k + 1) - entryPos G C₃.k - 1 := by
    rw [hf₂, hp₃', hp₃, BitVec.toNat_ofNat]
    decide
  have hoff₂ : (strOr (BitVec.ofNat 32 (entryPos G C₃.k))).toNat
      = plainSpan (entryPos G C₃.k + 1) := by
    have hx : (BitVec.ofNat 32 (entryPos G C₃.k)).toNat = entryPos G C₃.k := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by rw [hp₃]; decide)
    simpa [hx] using strOr_toNat_plainSpan (x := BitVec.ofNat 32 (entryPos G C₃.k))
      (by rw [hx, hp₃]; decide)
  have hevc₂ : Cd₂.events = C₃.events ++
      [EventRecord.str false (entryPos G (C₃.k + 1) - entryPos G C₃.k - 1)
        (plainSpan (entryPos G C₃.k + 1))] := by
    rw [hevc₂raw, hlen₂, hoff₂]
  -- the next carries are the merge carries' own
  have hk₂' : C₂.k = Cd₁.k + 2 := by omega
  have hev₂' : C₂.events = Cd₁.events := by rw [hev₂, hevc₁]
  have hk₄' : C₄.k = Cd₂.k + 2 := by omega
  have hev₄' : C₄.events = Cd₂.events := by rw [hev₄, hevc₂]
  exact row_stringPlainDocument (Cd₁ := Cd₁) (Cd₂ := Cd₂) hal hbs hent htokens hdec
    hpre₀ hk₀ hk₁ hev₁ hevc₁ hkc₁ hk₂' hev₂' hbody₁ hk₃ hev₃ hevc₂ hkc₂ hk₄' hev₄'
    hbody₂ hk₅ hev₅

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

/-- info: 'LeanLLVM.Refinement.strOr_toNat_plainSpan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms strOr_toNat_plainSpan

/-- info: 'LeanLLVM.Refinement.stringArmSegment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stringArmSegment

/-- info: 'LeanLLVM.Refinement.row_stringPlainDocument_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_stringPlainDocument_arm

end LeanLLVM.Refinement
