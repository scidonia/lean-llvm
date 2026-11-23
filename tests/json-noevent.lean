/-
NE5: the no-event model's relation-level obstruction at its witnesses.

`noEvent_abi_obstruction` is stated over two documents whose related traces
carry the empty arena and whose consumer readings differ.  This file pins that
pair at the model: the two relation instances at the empty arena, their five
observations, and two controls showing the observations are not an artifact of
the test — the arena argument is read, and the two witnesses are distinct
inputs.

Tying either document's run to a view value — that it accepts, decodes nothing
and leaves `*err` untouched — is the current ABI post's claim, exercised by the
differential; it is not established here.

Every observation is a `#guard` or a theorem, so a failed one stops elaboration
with a nonzero exit status; no compiler, service, clock or network is reached.
Elaborated by `nix develop -c lake env lean tests/json-noevent.lean`.
-/
import LeanLLVM

namespace JsonNoEventScenario

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.JSON

/-! ### The witness pair: two documents, one empty arena, two readings -/

/-- The obstruction's first witness: the `null` document's related trace at the
empty arena — one event, and the parser's `null` token at its span. -/
theorem nullDoc_noEvent :
    Stage2NoEvent nullDoc [] [ConsumerEvent.kind 10] [.null ⟨0, 4⟩] :=
  Stage2NoEvent.nullTag (s := ⟨0, 4⟩) (by decide) (by decide) Stage2NoEvent.nil

/-- The obstruction's second witness: the `true` document's related trace at the
empty arena — one event, and the parser's `true` token at its span. -/
theorem trueDoc_noEvent :
    Stage2NoEvent trueDoc [] [ConsumerEvent.kind 8] [.bool true ⟨0, 4⟩] :=
  Stage2NoEvent.trueTag (s := ⟨0, 4⟩) (by decide) (by decide) Stage2NoEvent.nil

-- Each witness's event list folds to one token and one value, with the sums the
-- tags give.
#guard (noEventFold [] [ConsumerEvent.kind 10]).tokens = 1
#guard (noEventFold [] [ConsumerEvent.kind 8]).tokens = 1
#guard (noEventFold [] [ConsumerEvent.kind 10]).sum = 10
#guard (noEventFold [] [ConsumerEvent.kind 8]).sum = 8

-- The two readings differ.
#guard decide
  (noEventFold [] [ConsumerEvent.kind 10] ≠
    noEventFold [] [ConsumerEvent.kind 8])

/-! ### Controls -/

-- The arena argument is load-bearing: the witnesses' `[]` is a value the fold
-- reads, not an ignored parameter.
#guard decide
  (noEventFold [0x31] [ConsumerEvent.kind 10] ≠
    noEventFold [] [ConsumerEvent.kind 10])

-- The two witnesses are distinct documents, so the differing readings are not
-- one input read twice.
#guard decide (nullDoc ≠ trueDoc)

end JsonNoEventScenario
