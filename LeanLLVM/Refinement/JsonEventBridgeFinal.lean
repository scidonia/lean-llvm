import LeanLLVM.Refinement.JsonEventBridgeComposition
import LeanLLVM.Refinement.JsonEventBridgeEventsB

/-!
The event route's value at the run, with nothing left open.

`eventsOfBytes_valueOfEvents` states the composition with `hE` as its last
premise, and `eventsParseValue` proves that premise for every argument.  This
module applies the two together: the emitted route's value at a run's post
equals the token decoder's canonicalised value, from the run's own checkable
facts — the boundary row, the within-extent clause, the token parse, and the
event stream's definition.  The event bisimulation above it was proved against
the decoder that reads a member key by position.
-/

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- The composition's transfer with the event bisimulation discharged. -/
theorem eventsOfBytes_valueOfEvents_events {bs arena evs : List UInt8}
    {rs : List EventRecord} {toks : List Token} {t : Tape}
    {obs : List ConsumerEvent}
    (hrel : Stage2Records bs arena rs toks)
    (hrow : obs = consumeRecords bs arena rs)
    (hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten) :
    (eventsOfBytes bs evs arena).bind valueOfEvents =
      (decodeTape t).bind canonValue :=
  eventsOfBytes_valueOfEvents hrel hrow hwithin hb hparse htoks hev
    (eventsParseValue bs arena rs toks t)

/-! ### The same value read through the document

The theorem above names the tape `parseBytes` returned as a separate argument.
The reference parser's value is a function of the document alone: parse the
bytes, decode the tape, canonicalise the number lexemes.  `scalarCanonValueOfBytes`
names that function, and the corollary below states the run's value against it,
so the equality's right-hand side no longer mentions the tape the premises
introduce (the theorem's type still binds it, through `hparse` and `htoks`).

The refusal branch is definitional, not a claim: a document `parseBytes` refuses
leaves no tape to decode, so its value is `none`.  The other two `none` sources —
a tape that fails `decodeTape` and a value that fails `canonValue` — are
unreachable for a tape the parser returned (`decodeTape_correct`,
`canonValue_isSome_of_decodeTape`), so `none` is exactly the refusal.  The
theorem speaks only on the accepted branch, because the committed chain's premise
is that acceptance; it does not assert that an emitted stream accompanies a
refused parse. -/

/-- **The reference parser's value for a document, canonicalised.**  The tape
`parseBytes` returns, decoded by `decodeTape` and canonicalised by `canonValue`;
`none` exactly when the parser refuses the document.  It is the reference value
put into the comparison's normal form, not the reference value itself: the two
`none` sources below the refusal are unreachable for a parser tape, and the
canonicalisation is the same one the emitted stream's value is compared against,
because the route's number records carry the binary64 bits rather than the
source lexeme. -/
def scalarCanonValueOfBytes (bs : List UInt8) : Option JSON.Value :=
  match parseBytes Limits.default (ByteString.literal bs) with
  | .ok t => (decodeTape t).bind canonValue
  | .error _ => none

/-- **The route's value is the reference value, canonicalised, for the same
document.**  With the run's own facts, the emitted stream's value equals
`scalarCanonValueOfBytes` at the document — the parser's tape, decoded and
canonicalised, with the tape named only in the premises.  The statement is the
committed chain with its right-hand side rewritten through `parseBytes`; the
premises and the `hE` discharge are the committed theorem's, and nothing is
weakened or added. -/
theorem eventsOfBytes_valueOfEvents_scalar {bs arena evs : List UInt8}
    {rs : List EventRecord} {toks : List Token} {t : Tape}
    {obs : List ConsumerEvent}
    (hrel : Stage2Records bs arena rs toks)
    (hrow : obs = consumeRecords bs arena rs)
    (hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten) :
    (eventsOfBytes bs evs arena).bind valueOfEvents = scalarCanonValueOfBytes bs := by
  rw [scalarCanonValueOfBytes, hparse]
  exact eventsOfBytes_valueOfEvents_events hrel hrow hwithin hb hparse htoks hev

end LeanLLVM.Refinement
