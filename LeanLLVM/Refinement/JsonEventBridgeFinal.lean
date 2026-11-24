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

end LeanLLVM.Refinement
