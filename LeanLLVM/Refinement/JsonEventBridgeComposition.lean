/-
The event stream's value at a run's post.

`JsonEventValue` states the transfer `valueOfEvents_consumeRecords`: a related
record trace's consumer events decode to the token decoder's value once the
token decoder's numbers are canonicalised, given the event-side bridge `hE` and
the token decoder's agreement `hT`.  This module applies a run's own facts to
that transfer, so that only `hE` remains open:

* **`hD` at the run** — `eventsOfBytes_stage2Records` reads the emitted stream
  back as the trace's consumer events.  Its per-record body premise is
  `bodyReads_of_boundaryRow`'s: the boundary row identifies the events the
  used-extent clause is stated over with the trace's own;
* **`hT`** — `tokenDecoderAgrees_of_parse` at the parser's own tape.  The
  decoder equality is not claimed over arbitrary tapes: `hparse` names the tape
  the reference parser produced;
* **`hcanon`** — `canonValue_isSome_of_decodeTape`: every number lexeme of the
  value that tape decodes has a canonical rendering, so the conclusion's
  right-hand side is never a silent `none`;
* **`hE`** — a hypothesis, `EventsParseValue bs arena rs toks t`.  The theorem
  is therefore conditional on the event-side bisimulation and typechecks before
  it is proved; once it lands, the theorem is that hypothesis supplied.

# The stream read is option-valued

`eventsOfBytes` is partial: a truncated record or an unreadable string body
answers `none`.  The value therefore reads through the option bind —
`(eventsOfBytes bs evs arena).bind valueOfEvents` — and `hD` rewrites that bind
to `valueOfEvents` at the trace's own events.  Stating it as a bare application
would be ill-typed, since `valueOfEvents` reads a list of events.

# The premise set is the run's

The trace relation `Stage2Records bs arena rs toks` at the window, the boundary
row's second conjunct `obs = consumeRecords bs arena rs`, the used-extent clause
`∀ e ∈ obs, e.BodiesWithin bs arena`, the record widths `∀ r ∈ rs, r.Bounded`,
the parser's acceptance `hparse`, the token tie `t.tokens = toks`, and the
stream's identity `evs = (rs.map EventRecord.encodedBytes).flatten`.  `Tagged`
is not a separate premise: `eventsOfBytes_stage2Records` takes it from the
relation itself (`Stage2Records.tagged`).  `hcanon` is likewise derived from
`hparse`, not assumed, so the statement consumes the run's facts and nothing
stronger.

There is no `sorry`, `admit` or `native_decide`; the axiom pin is in
`LeanLLVMTest/Refinement.lean`.
-/
import LeanLLVM.Refinement.JsonEventBridgeBodies
import LeanLLVM.Refinement.JsonEventBridgeTokenB

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- **The emitted stream's value at a run's post.**  With the trace relation at
the window, the boundary row and the used-extent clause, the emitted stream's
bytes read back as the trace's events, whose value is the parser's value after
canonicalisation.  The record widths are `Bounded`; `Tagged` comes from the
relation.  The event-side bridge `hE` is a premise, so the statement is open at
exactly that one obligation. -/
theorem eventsOfBytes_valueOfEvents {bs arena evs : List UInt8}
    {rs : List EventRecord} {toks : List Token} {t : Tape}
    {obs : List ConsumerEvent}
    (hrel : Stage2Records bs arena rs toks)
    (hrow : obs = consumeRecords bs arena rs)
    (hwithin : ∀ e ∈ obs, e.BodiesWithin bs arena)
    (hb : ∀ r ∈ rs, r.Bounded)
    (hparse : parseBytes Limits.default (ByteString.literal bs) = .ok t)
    (htoks : t.tokens = toks)
    (hev : evs = (rs.map EventRecord.encodedBytes).flatten)
    (hE : EventsParseValue bs arena rs toks t) :
    (eventsOfBytes bs evs arena).bind valueOfEvents =
      (decodeTape t).bind canonValue := by
  have hr : ∀ r ∈ rs, r.BodyReads bs arena :=
    bodyReads_of_boundaryRow hrel hrow hwithin
  have hD : eventsOfBytes bs evs arena = some (consumeRecords bs arena rs) := by
    rw [hev]
    exact eventsOfBytes_stage2Records hrel hb hr
  have hcanon : ∀ v, decodeTape t = some v → (canonValue v).isSome :=
    fun v hv => canonValue_isSome_of_decodeTape t hv
  have hT : parseValueT t = decodeTape t := tokenDecoderAgrees_of_parse hparse
  have hV : valueOfEvents (consumeRecords bs arena rs) =
      (parseValueT t).bind canonValue := hE hrel hparse htoks hcanon
  rw [hD, Option.bind_some, hV, hT]

end LeanLLVM.Refinement
