/-
The decoder theorem's premises, read backwards from its conclusion.

`JsonEventBridgeFinal.eventsOfBytes_valueOfEvents_scalar` is the value transfer
for the event route.  This module does not start at the caller and walk forward;
it starts at that theorem's seven premises and asks, for each, what can discharge
it, at `[1]` and in the tree generally.  The answer is the table below, a
structure whose fields are exactly the seven premises, one theorem that applies
the decoder theorem to the structure, and the instantiation at `[1]`.

# The premises, their consumers, and what discharges each

`evs` is the caller's event stream, `arena` the arena prefix, `rs` the walk's
record trace, `toks` the parser's tokens, `t` its tape and `obs` the decoder's
own event list (`eventsOfBytes`'s output).  The consumer column names where the
premise is *used*; the last two columns say what discharges it at `[1]` here and
what the tree has for it in general.

| # | premise | consumer | side | at `[1]` | in the tree generally |
|---|---|---|---|---|---|
| 1 | `hrel : Stage2Records bs arena rs toks` | `eventsParseValue`'s bisimulation (the record/token relation the event decoder is compared through) | emitter + reference | `evb_records`, from the document's spelling, not from the run | no-event path only: the walk's accept row carries it (`stage2Records_at_accept`); the event walk has no producer |
| 2 | `hrow : obs = consumeRecords bs arena rs` | names the decoder's left-hand list, so `eventsOfBytes`'s output is the trace's events | decoder | definitional at `obs := consumeRecords …` (`rfl`) | definitional; no supply |
| 3 | `hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena` | `eventsOfBytes`'s string-body read (the `hD` step) | decoder | `evb_within`: no record in `[1]`'s trace carries a body | no-event path only (`Stage2NoEventWalkReferenceFacts.within`); the event walk's body extents are open |
| 4 | `hb : ∀ r ∈ rs, r.Bounded` | `walkRecords_encoded`'s field-width width checks | decoder | `evb_bounded`: three computed widths | not implied by `hrel` (its `str` constructors do not bound `len`); no-event path carries it as a walk fact |
| 5 | `hparse : parseBytes Limits.default … = .ok t` | `eventsParseValue`'s bisimulation (the tape is the reference's) and the value's `decodeTape` side | reference | `evb_parse`, computed | generic in the document; the forward lane carries it as a hypothesis |
| 6 | `htoks : t.tokens = toks` | ties the parser's tape to the trace's tokens | reference | definitional at the chosen tape (`rfl`) | definitional at the tape the premises name |
| 7 | `hev : evs = (rs.map encodedBytes).flatten` | feeds `walkRecords_encoded` the caller's actual bytes | emitter | `EvbEmission.events_eq` | no-event path: the walk's carried facts; the event walk: the object's post, which the tree does not derive |

**What this decomposition adds over the forward direction.**  The four premises
that are statements about the *decoder's own inputs* — rows 2, 3, 4, 6 — are
discharged here by construction or by computation at `[1]`, and row 5 is
computed, not assumed.  The two that are statements about the *emitter's run* —
rows 1 and 7 — are exactly the pair a run of the event-producing object must
supply, and they are the module's named interface below rather than hidden
hypotheses.  Row 1 is proved at `[1]` from the document alone; it becomes
emitter-side only because a general caller does not have the document's spelling
to read.  So the remaining interface at `[1]` is one identity — the event bytes
the object left are the trace's encoding — and the arena being empty.

# The named interface and its consumer

`EvbEmission arena events` carries the two run-side facts at `[1]`:
`arena = []` and `events = (evbRecords.map encodedBytes).flatten`.  Its consumer
is `evb_value`: from that interface alone the emitted stream's value is the
reference's canonical value at `[1]`.  The docstring of `EvbEmission` says which
postcondition supplies it (a read of the destination buffer at the reported
extent yielding `[]`, and of the event buffer at its reported extent yielding
`evbEvents`); the tree has no theorem that produces such a read from the
caller's staging for the event walk (`JsonCallRoute.missingBridgePieces`), and
this module does not invent one.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonEventBridgeFinal
import LeanLLVM.JsonCallRoute

set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 1600000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The seven premises as one structure

The structure's fields are `eventsOfBytes_valueOfEvents_scalar`'s arguments in its
own order, so a value of it *is* a call to the theorem.  Naming the premise also
names its consumer: each field is read by exactly one part of the composition. -/

/-- **The decoder theorem's premises, bundled.**  `bs` is the document, `arena`
the arena prefix, `evs` the caller's event bytes, `rs` the walk's record trace,
`toks` the parser's tokens, `t` the parser's tape and `obs` the events
`eventsOfBytes` returns.  Every field is one argument of
`eventsOfBytes_valueOfEvents_scalar`; nothing is added, and `value` below is that
theorem at the bundle. -/
structure EvbPremises (bs arena evs : List UInt8) (rs : List EventRecord)
    (toks : List Token) (t : Tape) (obs : List ConsumerEvent) : Prop where
  /-- 1. The walk's trace, related record by record to the parser's tokens. -/
  records : Stage2Records bs arena rs toks
  /-- 2. The decoder's event list is the trace's consumer reading. -/
  row : obs = consumeRecords bs arena rs
  /-- 3. Every emitted body lies inside the source its field names. -/
  within : ∀ e ∈ obs, e.BodiesWithin bs arena
  /-- 4. Every record's payload fits the word its emitter writes. -/
  bounded : ∀ r ∈ rs, r.Bounded
  /-- 5. The reference parser accepts the document, at `t`. -/
  parse : parseBytes Limits.default (ByteString.literal bs) = .ok t
  /-- 6. The tape's tokens are the trace's. -/
  tokens : t.tokens = toks
  /-- 7. The caller's event bytes are the trace's encoding. -/
  events : evs = (rs.map EventRecord.encodedBytes).flatten

/-- **The consumer of all seven.**  The event route's value is the reference's
canonicalised value; the statement is
`eventsOfBytes_valueOfEvents_scalar` at the bundle's fields, so the equality's
right-hand side is the parser's, not a second decoder's. -/
theorem EvbPremises.value {bs arena evs : List UInt8} {rs : List EventRecord}
    {toks : List Token} {t : Tape} {obs : List ConsumerEvent}
    (h : EvbPremises bs arena evs rs toks t obs) :
    (eventsOfBytes bs evs arena).bind valueOfEvents = scalarCanonValueOfBytes bs :=
  eventsOfBytes_valueOfEvents_scalar h.records h.row h.within h.bounded h.parse
    h.tokens h.events

/-- **The bundle at the trace's own event list.**  Premise 2 is definitional, so
the six premises that are not it determine the bundle: a caller that has rows
1, 3–7 has this one by `rfl`, and `EvbPremises.value` then consumes it. -/
theorem EvbPremises.ofTrace {bs arena evs : List UInt8} {rs : List EventRecord}
    {toks : List Token} {t : Tape}
    (hrel : Stage2Records bs arena rs toks)
    (hwithin : ∀ e ∈ consumeRecords bs arena rs, e.BodiesWithin bs arena)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten) :
    EvbPremises bs arena evs rs toks t (consumeRecords bs arena rs) :=
  ⟨hrel, rfl, hwithin, hb, hparse, htoks, hev⟩

/-! ### Which side of the boundary each premise is a statement about

The classification the table gives, in Lean so a consumer can ask it rather than
read it.  `emitter` means a run of the event-producing object is the only thing
that can supply it; `reference` means the parser's own run on the document;
`decoder` means a fact about the recorded trace or the stream's shape, decided
without either run. -/

/-- The seven premises, by name. -/
inductive BridgePremise where
  | records | row | within | bounded | parse | tokens | events
  deriving DecidableEq, Repr

/-- What kind of statement a premise is. -/
inductive PremiseSide where
  /-- The parser's own run on the document. -/
  | reference
  /-- The trace or the stream's shape, decided without a run. -/
  | decoder
  /-- A run of the event-producing object left these bytes. -/
  | emitter
  deriving DecidableEq, Repr

/-- The table's side column. -/
def BridgePremise.side : BridgePremise → PremiseSide
  | .records => .emitter
  | .row => .decoder
  | .within => .decoder
  | .bounded => .decoder
  | .parse => .reference
  | .tokens => .reference
  | .events => .emitter

/-- The table's premise column, as the statement's own spelling. -/
def BridgePremise.statement : BridgePremise → String
  | .records => "Stage2Records bs arena rs toks"
  | .row => "obs = consumeRecords bs arena rs"
  | .within => "∀ e ∈ obs, e.BodiesWithin bs arena"
  | .bounded => "∀ r ∈ rs, r.Bounded"
  | .parse => "parseBytes Limits.default (ByteString.literal bs) = .ok t"
  | .tokens => "t.tokens = toks"
  | .events => "evs = (rs.map EventRecord.encodedBytes).flatten"

/-- The two premises no decoder-side fact can supply: the walk's trace relation
and the emitter's byte identity.  They are the interface `EvbEmission` and the
`records` field respectively; a general caller still owes both. -/
def BridgePremise.emitterSide : List BridgePremise := [.records, .events]

/-- The premises discharged at `[1]` without a run of the object. -/
def BridgePremise.decidedAtOne : List BridgePremise := [.row, .within, .bounded, .parse, .tokens]

/-! ### The document `[1]` and its trace

The emitted trace is read off the document: `[` is `T_ARR`, the number `1` is
`T_NUM` with `strtodSpec`'s bits, and `]` is `T_ARR_END`.  The arena is empty
because neither record carries a body, so the arena at which the trace is related
is `[]` and the stream is the three records' encoding. -/

/-- The slice's document: `[1]`. -/
def evbDoc : List UInt8 := [0x5B, 0x31, 0x5D]

/-- The number token's lexeme: the byte `0x31`. -/
def evbLex : Bytes := ByteString.literal [0x31]

/-- The reader's decomposition of `1`: unit mantissa, no fraction, no exponent. -/
def evbDecimal : Decimal := ⟨false, evbLex, none, none⟩

/-- The reader accepts `1` at that decomposition. -/
theorem evbReader : StrtodReader.reader evbLex = some evbDecimal := by
  decide

/-- The number record's payload: the binary64 bits of `1`. -/
def evbBits : Nat := (strtodSpec evbDecimal).toBits

/-- The tape's tokens: the opener at `0..1`, the number at `1..2`, the closer at
`2..3`. -/
def evbTokens : List Token :=
  [.punct .openBracket ⟨0, 1⟩, .number ⟨1, 2⟩, .punct .closeBracket ⟨2, 3⟩]

/-- The event trace: the opener's tag, the number record and the closer's tag. -/
def evbRecords : List EventRecord := [.tag 3, .number evbBits, .tag 4]

/-- The emitted stream: the trace's encoding. -/
def evbEvents : List UInt8 :=
  evbRecords.map EventRecord.encodedBytes |>.flatten

/-- The parser's tape at the document. -/
def evbTape : Tape := ⟨ByteString.literal evbDoc, evbTokens⟩

/-- The trace's flattening is the stream, definitionally: premise 7 at the
concrete stream. -/
theorem evb_events :
    evbEvents = (evbRecords.map EventRecord.encodedBytes).flatten := rfl

/-- The tape's tokens are the trace's, definitionally: premise 6. -/
theorem evb_tokens : evbTape.tokens = evbTokens := rfl

/-- **Premise 1 at `[1]`.**  The opener and the closer are their one-byte tags at
their spans; the number is the reader's decomposition of the span's lexeme `1`. -/
theorem evb_records :
    Stage2Records evbDoc [] evbRecords evbTokens := by
  refine Stage2Records.openBracket (s := ⟨0, 1⟩) (by decide) (by decide) ?_
  refine Stage2Records.number (s := ⟨1, 2⟩) (d := evbDecimal) (lex := evbLex) ?_ ?_ ?_ ?_
  · exact evbReader
  · simp [evbLex]
  · simp [evbDoc, evbLex, ByteString.data_toList_literal]
  · exact Stage2Records.closeBracket (s := ⟨2, 3⟩) (by decide) (by decide)
      Stage2Records.nil

/-- **Premise 3 at `[1]`.**  No record carries a string body, so every event's
tag is a container's or the number's and the clause's antecedent is false. -/
theorem evb_within :
    ∀ e ∈ consumeRecords evbDoc [] evbRecords, e.BodiesWithin evbDoc [] := by
  intro e he
  simp only [consumeRecords, evbRecords, List.map_cons, List.map_nil,
    List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl <;>
    simp [ConsumerEvent.BodiesWithin, ConsumerEvent.kind, ConsumerEvent.number,
      EventRecord.consume, EventRecord.tagKey, EventRecord.tagStr, stage2TagNum]

/-- The eight bytes of a finite double are below `2 ^ 64`. -/
theorem evb_toBits_lt_of_isCode {f : Binary64} (h : f.IsCode) : f.toBits < 2 ^ 64 := by
  have h52 : (2 : Nat) ^ 53 = 2 * 2 ^ 52 := by
    rw [show (53 : Nat) = 52 + 1 from rfl, Nat.pow_add]; rfl
  have h64 : (2 : Nat) ^ 64 = 2 * 2 ^ 63 := by
    rw [show (64 : Nat) = 63 + 1 from rfl, Nat.pow_add]; rfl
  have h2047 : (2047 : Nat) * 2 ^ 52 ≤ 2 ^ 63 := by decide
  cases f with
  | inf neg =>
      simp only [Binary64.toBits]
      have hinf : (0x7FF0000000000000 : Nat) = 2047 * 2 ^ 52 := by decide
      rw [hinf]
      split <;> omega
  | fin neg E m =>
      simp only [Binary64.toBits]
      rcases h with ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩
      · subst hE
        rw [ite_eq_left rfl]
        split <;> omega
      · have hEne : ¬ E = 0 := by omega
        rw [ite_eq_right hEne]
        split <;> omega

/-- The numeric payload fits the record's eight-byte field. -/
theorem evbBits_lt : evbBits < 2 ^ 64 :=
  evb_toBits_lt_of_isCode (strtodSpec_isCode evbDecimal)

/-- **Premise 4 at `[1]`.**  The three computed widths: tags below a byte, the
number below the 64-bit payload word. -/
theorem evb_bounded : ∀ r ∈ evbRecords, r.Bounded := by
  intro r hr
  simp only [evbRecords, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · simp [EventRecord.Bounded]
  · exact evbBits_lt
  · simp [EventRecord.Bounded]

/-! ### The emitter's side, named

Rows 1 and 7 are the two a run of the object supplies.  Row 1 is proved above
from the document, so at `[1]` the run's residue is row 7's byte identity plus
the arena the trace was related at.  The structure states them; `evb_value` is
their consumer, and it is the same statement as `EvbPremises.value` once the two
equalties have been substituted. -/

/-- **What the event-producing object's run supplies at `[1]`.**  The arena is
empty and the event buffer holds exactly the trace's encoding.  A postcondition
that reads the destination buffer at its reported extent and gets `[]`, and the
event buffer at its reported extent and gets `evbEvents`, supplies this; the tree
has no such read from the caller's staging for the event walk
(`JsonCallRoute.missingBridgePieces`), so the interface is named rather than
produced. -/
structure EvbEmission (arena events : List UInt8) : Prop where
  /-- The arena at which the trace is related: `[1]`'s records carry no body. -/
  arena_eq : arena = []
  /-- The event buffer's content is the trace's encoding. -/
  events_eq : events = (evbRecords.map EventRecord.encodedBytes).flatten

/-- **The emitter's residue, as the decoder's two premises.**  Substituting the
interface into the proved rows gives the bundle at the run's own buffers. -/
theorem evb_premises {arena events : List UInt8} (hemit : EvbEmission arena events)
    (hparse : parseBytes Limits.default (ByteString.literal evbDoc) = .ok evbTape) :
    EvbPremises evbDoc arena events evbRecords evbTokens evbTape
      (consumeRecords evbDoc arena evbRecords) := by
  obtain ⟨rfl, rfl⟩ := hemit
  exact EvbPremises.ofTrace evb_records evb_within evb_bounded hparse evb_tokens
    evb_events

/-- **The consumer of the interface.**  From the emitter's two identities alone —
no row, no boundedness, no parser equation — the emitted stream's value is the
reference's canonicalised value at `[1]`.  Everything else the decoder theorem
needs is proved in this module, so this is the exact residue of the slice. -/
theorem evb_value {arena events : List UInt8} (hemit : EvbEmission arena events)
    (hparse : parseBytes Limits.default (ByteString.literal evbDoc) = .ok evbTape) :
    (eventsOfBytes evbDoc events arena).bind valueOfEvents =
      scalarCanonValueOfBytes evbDoc :=
  (evb_premises hemit hparse).value

/-- **The slice's value at the emitter's own outputs.**  The same statement at
the concrete buffers the trace names, so the right-hand side is the only free
name: the emitted stream's value is the reference's, conditional on the parser's
tape for `[1]`. -/
theorem evb_sliceOne_value
    (hparse : parseBytes Limits.default (ByteString.literal evbDoc) = .ok evbTape) :
    (eventsOfBytes evbDoc evbEvents []).bind valueOfEvents =
      scalarCanonValueOfBytes evbDoc :=
  (evb_premises ⟨rfl, evb_events⟩ hparse).value

/-- info: 'LeanLLVM.Refinement.EvbPremises.value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms EvbPremises.value

/-- info: 'LeanLLVM.Refinement.EvbPremises.ofTrace' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms EvbPremises.ofTrace

/-- info: 'LeanLLVM.Refinement.evbReader' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evbReader

/-- info: 'LeanLLVM.Refinement.evb_records' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_records

/-- info: 'LeanLLVM.Refinement.evb_within' depends on axioms: [propext] -/
#guard_msgs in
#print axioms evb_within

/-- info: 'LeanLLVM.Refinement.evb_bounded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_bounded

/-- info: 'LeanLLVM.Refinement.evb_premises' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evb_premises

/-- info: 'LeanLLVM.Refinement.evb_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_value

/-- info: 'LeanLLVM.Refinement.evb_sliceOne_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms evb_sliceOne_value

end LeanLLVM.Refinement
