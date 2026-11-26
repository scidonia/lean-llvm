/-
The release theorem's two number premises: the scanner's token extent and the
emitted accumulators' agreement with the reader's decimal.

The release target is one Lean call `valueOf doc` that terminates, returns the
reference parser's canonical value or its parse error, and is competitive with
native.  Its event route ends at
`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar`, whose `hrel :
Stage2Records bs arena rs toks` is built from the walk's number arm.  That arm's
number record has two premises that the walk does not derive: the span it hands
to `num_fast_el1` is the grammar token's extent, and the eight bytes it appends
are `strtodSpec`'s of the decimal the reader computes.  This module states each
premise, proves what the tree's definitions allow, and names the obstruction
that keeps the rest open.  It adds no `sorry`, `admit` or `native_decide`; the
axiom pins are at the end.

## Premise 1 — the scanner hands over the grammar token's extent

`docs/contract.md` (the `num_fast_el1` row and the paragraph after it) records
this as the scanner's token-extent obligation: a token the stage-1 scanner
classifies as a number must be exactly RFC 8259 §6's token, not merely a prefix
`numLexB` accepts.  The stage-2 body then scans the slice it is handed
(`numLexScan`, `JsonStage2Body.numLexScan_accepts_iff_numLexB`), so an accepted
prefix would convert a value where the reference token carries the rest of the
run.

The statement is `NumberTokenExtentAt bs sp q`: the scalar scan's stop `q` is
the tape token's `span.stop`, and the document slice at the span is the maximal
`NumConstituent` run `numRunFrom`.  The second conjunct is the maximality the
grammar token has and an accepted prefix lacks.

**Consumers.**

* no-event walk: `JsonStage2NoEventWalkDispatchValueArmsB.stage2NoEventWalkValueNumber`
  takes exactly `hlex : readBytes s.mem (K.b + lane) (q - lane) = some lex`,
  `hread : StrtodReader.reader (ByteString.literal lex) = some d`,
  `hwf : d.wellFormed`, `hstop : q = lane + lex.length` and
  `hslice : (K.bs.drop lane).take (q - lane) = lex`;
* event walk: `JsonStage2WalkRowArms.payloadRevolution_number_arm` through
  `JsonStage2WalkRowSteps.payloadRevolution_number`/`payloadStep_number` and
  `JsonStage2WalkRowSteps.headTokenRecord_number`, whose
  `tokenRecord_number_of_tape` supplies the record `WalkTraceRow` →
  `emittedStream_of_row` → `Stage2Records` consumes at
  `eventsOfBytes_valueOfEvents_events`.

**What is proved here.**  `numberPayload_at_tape_token` derives, from
`decodeTape` and the tape's token list alone, the slice, a reader witness, its
well-formedness, and the payload equality: the extent is orthogonal to the
payload.  `numberArmPremises_of_extent` adds the extent and produces the five
premises above as one existential.  `tokenRecord_number_of_tape_reader` is the
tape-side record restated at the document's own lexeme (a reader witness, not
`d.lexeme`), which is the form the event arm's `TokenRecord.number` constructor
already accepts.

**Obstruction.**  Neither conjunct is derivable from the tree's current
definitions.  `WalkAlign` (`JsonStage2WalkAlignment.lean:313`) pins each token's
*start* to `entryPos G k` and the next entry to the next token's start; it never
states that the next entry is the current token's *stop*.  `entryPos` is a lane
read of a staged table (`JsonStage2WalkScopeGeom.entryPos`,
`WalkGeom.entries : readLanes32 m0 ep nep = some ent`) — the stage-1 emitter
that fills those lanes has no Lean semantics anywhere in the tree.  The scalar
scan's stop `q` is a walk value, and `JsonStage2NoEventWalkValue` proves only
`lane ≤ q ≤ cond` and `q = cond ∨ stage2SkipWs` at `q`; the maximal-run side is
the decoder's own (`JSON/TapeCorrect.decodeValue`'s number guard, whose evidence
`decodeTokenBytes_aux` discards when it states `TokenBytes`).  So closing this
premise needs a *definition change* — a stop clause such as `WalkAlignStops`
below, added to the alignment the walk's invariant preserves (initialised from
the stage-1 emitter) — together with a *measurement or a body proof* of that
emitter's stop side: the mask classifier in the tree produces entry positions,
not extents.

## Premise 2 — the emitted accumulators are the reader's decimal fields

`JsonStage2Body`'s number section states the emitted dispatch's five locals —
`%ip`, `%fr`, `%idig`, `%fdig`, `%exp10` — and `StrtodReader`'s docstring says
the missing tie is "a per-local state equivalence over about ten variables, with
no arithmetic content".  The model `numFastEmitted` reads the lexeme through
`StrtodReader.reader`; `JsonStage2NumberPayload.numberPayload_of_reader` makes
the payload `strtodSpec`'s of that decimal whatever the spelling.  The premise
here is the link the payload lemma assumes: at the conversion the emitted body's
registers hold exactly those decimal fields.

The statement is `NumFastAccumulatorAgreement env d`: the five merge registers
are `expVal d`, `intDigits d`, `Decimal.digitsNat d.ip`,
`Decimal.digitsNat (d.fr.getD empty)` and `fracDigits d`.

**Consumers.**  The tree proves the register half at the conversion's merge:
`NumFastSeams.t1_intRun_tie` and `t1_fracRun_tie` hand the successor state's five
cells as the model's, `NumFastSeams.expSelect_tie`/`expExit_merge_back` tie
`%exp10.4` to `expVal d`, and `NumFastScanRun.ip_word_digitsNat`/
`fr_word_digitsNat` are the fold-to-`digitsNat` steps.  The statement those
pieces would discharge, and this premise's consumer on the body side, is
`JsonStage2NumFastArm.NumFastBodyArm` (`JsonStage2NumFastArm.lean:940`) — the
conversion arm's answer, `1` and `strtodSpec`'s eight bytes at `%out`.  The walk
selects its model for that slot (`JsonStage2Body.stage2Calls_num_fast_el1`),
which is why the model-level arms (`valueArms_numFast_model`,
`stage2NoEventWalkValueNumber`, `payloadRevolution_number_arm`'s `hev`) close
today; replacing the selection with the emitted body is what `NumFastBodyArm`
has to supply.

**What is proved here.**  `numFastAccumulatorAgreement_merge` shows the merge
environment `numFastGateAt` *is* the agreement (definitional), and
`numFastAccumulatorAgreement_intRun` derives the agreement from the tree's own
integer-edge seam `NumFastSeams.t1_intRun_tie` for the exponent-free,
fraction-free lexeme, with that seam's segmentation hypotheses.

**Obstruction.**  Two things are outside the tree's definitions, and neither is
a defect of the seams.  First, the seams take the emitted scan's *segmentation*
as hypotheses (`t1_intRun_tie`'s `hint`/`hshape`: the run consumed `d.ip`'s
bytes for `intDigits d` positions).  Tying those to `StrtodReader.reader` is the
emitted scan's reader agreement — including the eight-digit `num_d8_el1` fast
path and tier 3's `to_double` window (`JsonStage2NumFastToDouble` stops before
the main parse loop and the composition from `for.body.outer.i.i`).  Second, the
conversion leaves three callees out of line (`num_d8_el1`, `num_el_el1`,
`stk_mul_u64`); at the walk's own selection `s2HelperCalls` those sites are `ub`
(`JsonStage2NumFastArm.numFast_step_ifEnd268_ub` and its siblings), and
`JsonStage2NumFastCalls.numFastCalls` answers them from their *measured C text*,
not from refined LLVM bodies.  Closing this premise therefore needs a
compiler/ABI assumption or a further measurement for those three callees, plus
the tier-3 region's remaining blocks; it is a definition/body-proof obligation,
not an arithmetic one.
-/
import LeanLLVM.Refinement.JsonStage2NumberPayload
import LeanLLVM.Refinement.JsonStage2TraceRow
import LeanLLVM.Refinement.JsonStage2WalkAlignment
import LeanLLVM.Refinement.JsonStage2NumFastClass
import LeanLLVM.Refinement.JsonStage2NumFastSeams

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.StrtodRefine
open ByteString

/-! ### Premise 1: the scanner's token extent

The statement at one number token, and the bridge from it plus the tape to the
number arm's premise set.  The tape is the parser's (`decodeTape`), so its token
facts are `TapeCorrect`'s; the extent is the one thing the tape does not hand
over. -/

/-- **The scanner's token-extent obligation at one number token.**  `sp` is the
tape's number span, `q` the stage-1 scalar scan's stop for that token.  The stop
is the span's, and the span's bytes are the maximal number run from the span's
start: the grammar token's extent, not an accepted prefix. -/
def NumberTokenExtentAt (bs : List UInt8) (sp : Span) (q : Nat) : Prop :=
  sp.start ≤ sp.stop ∧
    q = sp.stop ∧
      (bs.drop sp.start).take (sp.stop - sp.start) =
        (numRunFrom (ByteString.literal bs) sp.start).data.toList

/-- The span is well formed. -/
theorem NumberTokenExtentAt.start_le_stop {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberTokenExtentAt bs sp q) : sp.start ≤ sp.stop := h.1

/-- The scan's stop is the token's. -/
theorem NumberTokenExtentAt.stop_eq {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberTokenExtentAt bs sp q) : q = sp.stop := h.2.1

/-- The span holds the maximal number run. -/
theorem NumberTokenExtentAt.slice {bs : List UInt8} {sp : Span} {q : Nat}
    (h : NumberTokenExtentAt bs sp q) :
    (bs.drop sp.start).take (sp.stop - sp.start) =
      (numRunFrom (ByteString.literal bs) sp.start).data.toList := h.2.2

/-- **The payload at a tape's number token, from the tape alone.**  The slice, a
reader witness at it, that decimal's well-formedness, and the eight bytes the
model conversion would write.  The extent is not used: the payload is a function
of the lexeme, not of where the scan stopped. -/
theorem numberPayload_at_tape_token {t : Tape} {v : JSON.Value} {bs : List UInt8}
    {sp : Span} (hdec : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    (htok : Token.number sp ∈ t.tokens) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop sp.start).take (sp.stop - sp.start) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            (numFastEmitted (ByteString.literal lex)).toBits =
              (strtodSpec d).toBits := by
  obtain ⟨lex, htake, -, hnum⟩ := tape_tokenBytes_number hdec hin htok
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (StrtodReader.reader_complete hnum)
  have hwf := StrtodReader.reader_wf hd
  exact ⟨lex, d, htake, hd, hwf, numberPayload_of_reader (d := d) hd hwf⟩

/-- **The number arm's premise set, from the tape and the extent.**  With the
extent at the token and the lane the walk carries, the arm's five premises hold
as one existential: the slice the walk reads, a reader witness, its
well-formedness, the stop equation `q = lane + lex.length`, and the payload
equality.  These are `stage2NoEventWalkValueNumber`'s `hlex`, `hread`, `hwf`,
`hstop`, `hslice`, and the event arm's span/lexeme and `hev` data. -/
theorem numberArmPremises_of_extent {t : Tape} {v : JSON.Value} {bs : List UInt8}
    {sp : Span} {q lane : Nat}
    (hdec : decodeTape t = some v) (hin : t.input = ByteString.literal bs)
    (htok : Token.number sp ∈ t.tokens) (hext : NumberTokenExtentAt bs sp q)
    (hlane : lane = sp.start) :
    ∃ (lex : List UInt8) (d : Decimal),
      (bs.drop lane).take (q - lane) = lex ∧
        StrtodReader.reader (ByteString.literal lex) = some d ∧
          d.wellFormed ∧
            q = lane + lex.length ∧
              (numFastEmitted (ByteString.literal lex)).toBits =
                (strtodSpec d).toBits := by
  obtain ⟨lex, htake, hlen, hnum⟩ := tape_tokenBytes_number hdec hin htok
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (StrtodReader.reader_complete hnum)
  have hwf := StrtodReader.reader_wf hd
  have hle : sp.start ≤ sp.stop := NumberTokenExtentAt.start_le_stop hext
  refine ⟨lex, d, ?_, hd, hwf, ?_, numberPayload_of_reader (d := d) hd hwf⟩
  · subst hlane
    rw [NumberTokenExtentAt.stop_eq hext]
    exact htake
  · subst hlane
    rw [NumberTokenExtentAt.stop_eq hext]
    omega

/-- **The tape's number record at the document's own lexeme.**  `TokenRecord`'s
number row takes any byte string the reader reads as some decimal
(`TokenRecord.number`), so the record needs no `Decimal` whose normal form spells
the document: the reader witness at the span's slice is the premise.  This is
`tokenRecord_number_of_tape` with its `d.lexeme` hypothesis replaced by the
reader, the form the spelling-invariance lemmas in `JsonStage2NumberPayload`
supply at `1E5` and `1e+5`. -/
theorem tokenRecord_number_of_tape_reader {t : Tape} {v : JSON.Value}
    {bs arena : List UInt8} (h : decodeTape t = some v)
    (hin : t.input = ByteString.literal bs) {s : Span}
    (htok : Token.number s ∈ t.tokens) {d : Decimal}
    (hread : StrtodReader.reader
      (ByteString.literal ((bs.drop s.start).take (s.stop - s.start))) = some d) :
    TokenRecord bs arena (.number (strtodSpec d).toBits) (.number s) := by
  obtain ⟨lex, htake, hlen, hnum⟩ := tape_tokenBytes_number h hin htok
  have hpos : 0 < lex.length := by
    simpa using rfcNumber_nonempty hnum
  have hle : s.start ≤ s.stop := by omega
  have hlen' : ((bs.drop s.start).take (s.stop - s.start)).length = s.stop - s.start := by
    rw [htake, hlen]
  refine TokenRecord.number
    (lex := ByteString.literal ((bs.drop s.start).take (s.stop - s.start))) hread ?_ ?_
  · rw [ByteString.length_eq_size, ByteString.size_literal, hlen']
    omega
  · rw [ByteString.data_toList_literal]

/-- **The clause `WalkAlign` is missing.**  For every token that has a
successor, the successor's entry is the token's stop.  `WalkAlign` names the
successor's *start* at the same position, so the two agree only when this clause
holds; adding it (and a proof of the stage-1 emitter's stops) is the definition
change Premise 1 needs.  The last token is outside the clause: its stop is the
scalar scan's `q`, which the walk obtains from the document, not from an entry. -/
def WalkAlignStops {m0 : Mem} (G : WalkGeom m0) (t : Tape) : Prop :=
  ∀ (k : Nat) (tok : Token), t.tokens[k]? = some tok → k + 1 < G.nep →
    entryPos G (k + 1) = tok.span.stop

/-- **The stop clause at a number token.**  With `WalkAlignStops`, a non-last
number token's next entry is its stop, so the walk's `%cond` is the tape's
`span.stop` and the extent premise's `q = sp.stop` is the scan's own equation. -/
theorem entryPos_next_of_number {m0 : Mem} {G : WalkGeom m0} {t : Tape}
    (hstop : WalkAlignStops G t) {k : Nat} {sp : Span}
    (htok : t.tokens[k]? = some (.number sp)) (hk : k + 1 < G.nep) :
    entryPos G (k + 1) = sp.stop :=
  hstop k (.number sp) htok hk

/-! ### Premise 2: the accumulators are the reader's decimal fields

The five merge registers, the environment the tree's ties build, and the
integer-edge seam's agreement. -/

/-- **The accumulator agreement at the conversion's merge.**  The emitted body's
five locals at `if.end230` are the reader's decimal fields: the exponent with its
sign at the saturating accumulator (`expVal`), the two counts, and the two digit
runs' values. -/
def NumFastAccumulatorAgreement (env : Env) (d : Decimal) : Prop :=
  lookupName env "%exp10.4731" = some (.int 64 (BitVec.ofInt 64 (expVal d))) ∧
    lookupName env "%idig.4709716730" =
      some (.int 64 (BitVec.ofNat 64 (intDigits d))) ∧
      lookupName env "%ip.5708717729" =
        some (.int 64 (BitVec.ofNat 64 (Decimal.digitsNat d.ip))) ∧
        lookupName env "%fr.5718728" = some (.int 64
          (BitVec.ofNat 64 (Decimal.digitsNat (d.fr.getD ByteString.empty)))) ∧
          lookupName env "%fdig.4719727" =
            some (.int 64 (BitVec.ofNat 64 (fracDigits d)))

/-- **The merge environment is the agreement.**  `numFastGateAt` is the block's
environment built from the model's five values, so the predicate is exactly that
construction. -/
theorem numFastAccumulatorAgreement_merge (env : Env) (d : Decimal) :
    NumFastAccumulatorAgreement
      (numFastGateAt env d (d.fr.getD ByteString.empty)) d := by
  unfold NumFastAccumulatorAgreement
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [numFastGateAt, NumFastTier1.t1GateEnv]; block_lk)

/-- **The agreement at the integer edge.**  For a lexeme with no fraction and no
exponent, the tree's own `t1_intRun_tie` hands the five cells as the model's with
the two empty parts zero; that is the agreement, from the seam's segmentation
hypotheses (`hint`, `hshape`) and the tier-1 digit bound. -/
theorem numFastAccumulatorAgreement_intRun {calls : Calls} {d : Decimal}
    {bs : List UInt8} {mem0 : Mem} {p n i0 d0 : Nat} {e : State}
    (hpc : e.pc = "if.end230") (he : intRunExit mem0 bs p n i0 d0 e)
    (hi0 : i0 ≤ n) (hbn : d0 + n < 2 ^ 64)
    (hint : intDigits d = d0 + (n - i0))
    (hshape : d.ip.data.toList = (bs.drop (i0 - d0)).take (d0 + (n - i0)))
    (hdig : digitCount d ≤ 15) (hfr : d.fr = none) (hex : d.ex = none) :
    ∃ o : State, o.pc = "if.then241" ∧ o.pre = some "if.end230" ∧ o.mem = e.mem ∧
      NumFastAccumulatorAgreement o.env d ∧
        ∀ k, runFuel calls (1 + k) numFastBody (stateAt e.env e) =
          runFuel calls k numFastBody o := by
  obtain ⟨o, hpc', hpre', hmem', hE, hI, hIP, hFR, hFD, hrun⟩ :=
    NumFastSeams.t1_intRun_tie (calls := calls) (d := d) (bs := bs) (mem0 := mem0)
      (p := p) (n := n) (i0 := i0) (d0 := d0) (e := e) hpc he hi0 hbn hint hshape hdig
  refine ⟨o, hpc', hpre', hmem', ?_, hrun⟩
  have hfs : (d.fr.getD ByteString.empty) = (ByteString.empty : Bytes) := by
    rw [hfr]; rfl
  refine ⟨?_, hI, hIP, ?_, ?_⟩
  · rw [hE]
    have he0 : expVal d = (0 : Int) := by simp [expVal, hex]
    rw [he0]
    simp
  · rw [hFR, hfs]
    have hdig0 : Decimal.digitsNat (ByteString.empty : Bytes) = 0 := by
      simp only [Decimal.digitsNat, ByteString.data_toList_empty]
      rfl
    rw [hdig0]
    simp
  · rw [hFD]
    have hfrac0 : fracDigits d = 0 := by
      unfold fracDigits
      rw [hfs]
      exact ByteString.length_empty
    rw [hfrac0]
    simp

/-! ### Axiom footprints -/

#print axioms NumberTokenExtentAt.start_le_stop
#print axioms NumberTokenExtentAt.stop_eq
#print axioms NumberTokenExtentAt.slice
#print axioms numberPayload_at_tape_token
#print axioms numberArmPremises_of_extent
#print axioms tokenRecord_number_of_tape_reader
#print axioms entryPos_next_of_number
#print axioms numFastAccumulatorAgreement_merge
#print axioms numFastAccumulatorAgreement_intRun

end LeanLLVM.Refinement
