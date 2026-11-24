/-
The no-event consumer's event stream read as a JSON value.

`JsonStage2NoEvent` projects the certified stage-2 trace onto the caller's
vocabulary: `consumeRecords` replaces each `EventRecord` by the `ConsumerEvent`
the consumer reads from it.  What that module states is the stream's *content* —
token and value counts, the arena byte sum, and the sum — and a refusal policy.
It names the decoded value only as `decodeTape t`, the reference tape's own
decoding, and leaves open what a consumer that wants a **value** reads from the
events.  The decoders are `JsonEventDecode` and the canonicalisation is
`JsonCanon`; this module states the transfer: `valueOfEvents_consumeRecords`
transfers `valueOfEvents` to the parser's value after canonicalising the
reference's number lexemes, conditionally on the two decoder bridges `hE` and
`hT` that the entry separates from the decoder itself.

# The number arm is lossy, and the accepted value is the canonicalised one

`LeanLLVM.JSON.Value.number` carries the document's **source lexeme**
(`Value.number (lexeme : Bytes)`), while `ConsumerEvent.number` carries only
`strtodSpec d`'s bits: the record's eight payload bytes are an IEEE 754 binary64,
not the bytes that spelled it.  Many lexemes denote one binary64 — `1.0` and
`1.00` are one value — so no decoder can recover the lexeme from the stream
alone, and an equality with `decodeTape t` cannot hold on every trace.

The decoder renders a number's payload canonically (`bitsLexeme`, the eight
payload bytes), and the transfer theorem concludes the equality *after*
canonicalising the reference's number lexemes: `canonValue` reads a lexeme with
`StrtodReader.reader`, converts it with `strtodSpec`, and renders the result with
`bitsLexeme`.  That is the fast path's accepted number behaviour: an accepted
number is its binary64 value, and the canonical rendering of that value is the
eight bytes the event carries.  This is not a uniqueness
claim over traces — many lexemes share one rendering, as they share one value —
and a lexeme the reader refuses has no rendering, so the canonicalisation is
`none` there and an accepted document whose number lexeme the reader refuses
cannot satisfy `hE`.

# The transfer is hypothesis application

`hE` carries the event decoder to the canonicalised token decoder at this
trace's own facts, `hT` carries the token decoder to `decodeTape`, and the
conclusion is those two rewritten in sequence.  No decoder is proved here, and
neither bridge is a vacuous premise: each relates two different decoders of the
same document, and the `hE`/`hT` split names where a proof of the bridge belongs.

# The canonicalisation's domain is a premise, not a fallback

`hcanon` names the domain the event-side bridge is stated under: every number
lexeme of the value `decodeTape t` returns is one `StrtodReader.reader` accepts,
so `canonValue` succeeds on that value.  It is a premise of the theorem and the
last premise `EventsParseValue` binds, so the transfer consumes it; it is not a
silent assumption.  Discharging it rests with the entry's own proof:
`decodeTape_correct` and the accepted
document's `ValidDocument` give the number grammar the reader reads, hence the
decoded value's number lexemes are readable.

A fallback — returning the lexeme unchanged where the reader refuses — would be
worse than a missing premise.  The event side renders `bitsLexeme bits`, the
reference side would keep the source bytes, and the equality would fail exactly
on the documents the fallback touched, silently.  The canonicalisation therefore
stays `Option`-valued, and the theorem states the condition under which it is
defined instead of manufacturing a value where there is none.

The decoder is `def`, not `noncomputable`: its recursion is fuelled, so no
`Classical.choice` enters the value or the theorem.  Its axiom footprint is
`[propext, Quot.sound]`; a future `noncomputable` edit would widen it, which is
why the pin records the narrower line.

There is no `sorry`, `admit` or `native_decide`; the axiom pin is in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonStage2NoEvent
import LeanLLVM.Refinement.JsonEventDecode
import LeanLLVM.Refinement.JsonCanon
import LeanLLVM.JSON

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The transfer theorem

The event stream's value is the tape's value, canonicalised, once the two decoders
are bridged: the event decoder agrees with the canonicalised token decoder
(`hE`), and the token decoder agrees with the tape's own recursive-descent
decoder (`hT`).  Those two are the module's named bridges; the theorem applies
them and rewrites, so the number arm's loss is accounted for by the
canonicalisation on the conclusion's right-hand side rather than by a premise. -/

/-- **The event-side bridge.**  At this trace, given the record relation, the
parse, the token-list tie and that the decoded value's number lexemes all have a
canonical rendering, the event decoder agrees with the token decoder after the
token decoder's number lexemes are canonicalised.  Stated at the trace's own
facts rather than as a bare function equality: the premises are arguments, so a
proof of it is a proof about this document, not a composition of two unrelated
functions. -/
def EventsParseValue (bs arena : List UInt8) (rs : List EventRecord)
    (toks : List JSON.Token) (t : JSON.Tape) : Prop :=
  Stage2Records bs arena rs toks →
  parseBytes Limits.default (ByteString.literal bs) = .ok t →
  t.tokens = toks →
  (∀ v, decodeTape t = some v → (canonValue v).isSome) →
  valueOfEvents (consumeRecords bs arena rs) = (parseValueT t).bind canonValue

/-- **The event stream projects to the parser's canonicalised value**, by
applying the two decoder bridges.  `hcanon` is the domain condition the
event-side bridge is stated under: every number lexeme of the value the tape
decodes is one the reader accepts.  `hE` is the event-side bridge over this
trace's facts and `hcanon`, and `hT` is the token decoder's agreement with
`decodeTape`; the conclusion's right-hand side canonicalises the reference
value's number lexemes with `canonValue`, which is where the number arm's lossy
rendering is accounted for.  Each premise is a statement about a different
object, and none is the conclusion. -/
theorem valueOfEvents_consumeRecords {bs : List UInt8} {arena : List UInt8}
    {rs : List EventRecord} {toks : List JSON.Token} {t : JSON.Tape}
    (hrec : Stage2Records bs arena rs toks)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hcanon : ∀ v, decodeTape t = some v → (canonValue v).isSome)
    (hE : EventsParseValue bs arena rs toks t)
    (hT : parseValueT t = decodeTape t) :
    valueOfEvents (consumeRecords bs arena rs) = (decodeTape t).bind canonValue := by
  rw [hE hrec hparse htoks hcanon, hT]

end LeanLLVM.Refinement
