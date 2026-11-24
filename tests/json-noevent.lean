/-
NE5: the no-event model's relation-level obstruction at its witnesses.
NE9: the gap model's case table.
NE10: the literal chain's case table.

`noEvent_abi_obstruction` is stated over two documents whose related traces
carry the empty arena and whose consumer readings differ.  This file pins that
pair at the model: the two relation instances at the empty arena, their five
observations, and two controls showing the observations are not an artifact of
the test — the arena argument is read, and the two witnesses are distinct
inputs.

NE9 reads `od_gap_recover`'s model at its call boundary: `gapRecoverWrite`, the
rule the helper's C text states, over the six document windows the text reaches,
each at its offset and message tag.  Two controls accompany the table — the
`ee == ip` no-write case taken through the post-loop decision, which answers on
the other side of the guard, and a one-word mutation of the last site (guarded
where the text is unconditional), which the `"true "` row fails while the other
five stay green.

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

/-! ### NE9 — the gap model's case table

The six sites `od_gap_recover`'s text reaches, one witness each, at the rule
boundary: `gapRecoverWrite` over the document window `[0, ip)` and the token's
`pos`.  An offset is the C text's (`pos + ei` for a refused number or literal,
`pos` for a scalar, `s2` for a second token), and a tag names which `err_set`
ran; the message word itself is a literal address the fragment does not model.

The first row is the no-write case: the first loop reaches `ip`, so the helper
returns before any `err_set`.
-/
#guard gapRecoverWrite [0x74, 0x72, 0x75, 0x65] 4 0 = GapWrite.none

-- Number refusal: "1e x" has a number's first byte and a lexeme that refuses at
-- its second byte; the whitespace inside the window does not make it a token.
#guard gapRecoverWrite [0x31, 0x65, 0x20, 0x78] 4 0 =
  GapWrite.err 2 gapTagNumber

-- Literal refusal: "tru x" stops at the literal's third byte.
#guard gapRecoverWrite [0x74, 0x72, 0x75, 0x20, 0x78] 4 0 =
  GapWrite.err 3 gapTagLiteral

-- Non-scalar first byte: "[" selects no arm, so the refusal is at the token's
-- start.
#guard gapRecoverWrite [0x5B, 0x20, 0x78] 3 0 = GapWrite.err 0 gapTagScalar

-- Extra token inside the gap: "12 3" accepts the number, and the whitespace
-- before "3" leaves a second token at 3.
#guard gapRecoverWrite [0x31, 0x32, 0x20, 0x33] 4 0 =
  GapWrite.err 3 gapTagExtra

-- Extra token at `ip`: "true " accepts the literal and the rest of the gap is
-- whitespace, so `s2 = ip`.  The text's last `err_set` is unconditional, so the
-- call still refuses, at `ip`, although the window holds no second token.
#guard gapRecoverWrite [0x74, 0x72, 0x75, 0x65, 0x20] 5 0 =
  GapWrite.err 5 gapTagExtra

/-- The `ee == ip` guard is load-bearing: the no-write row's `ee` taken through
the post-loop decision refuses the accepted literal as a second token at `ip`,
and the rule answers no write instead. -/
theorem gapNoWrite_row_differs :
    gapRecoverWrite [0x74, 0x72, 0x75, 0x65] 4 0 = GapWrite.none ∧
      gapAfterLoop [0x74, 0x72, 0x75, 0x65] 4 0 4 =
        GapWrite.err 4 gapTagExtra := by
  decide

/-- The one-word mutation the table exists to exclude: the last site guarded by
`s2 = ip` rather than written unconditionally.  It changes only an extra-token
write whose `s2` reaches `ip`, which is exactly the `"true "` row. -/
def gapGuardedWrite (bytes : List UInt8) (ip pos : Nat) : GapWrite :=
  match gapRecoverWrite bytes ip pos with
  | GapWrite.err off tag =>
      if tag = gapTagExtra ∧ off = ip then GapWrite.none else GapWrite.err off tag
  | GapWrite.none => GapWrite.none

-- Against the mutation the five other rows keep the rule's answers ...
#guard gapGuardedWrite [0x74, 0x72, 0x75, 0x65] 4 0 = GapWrite.none
#guard gapGuardedWrite [0x31, 0x65, 0x20, 0x78] 4 0 = GapWrite.err 2 gapTagNumber
#guard gapGuardedWrite [0x74, 0x72, 0x75, 0x20, 0x78] 4 0 = GapWrite.err 3 gapTagLiteral
#guard gapGuardedWrite [0x5B, 0x20, 0x78] 3 0 = GapWrite.err 0 gapTagScalar
#guard gapGuardedWrite [0x31, 0x32, 0x20, 0x33] 4 0 = GapWrite.err 3 gapTagExtra

-- ... and the last row fails: the guarded transcription answers no write where
-- the table pins the unconditional refusal at `ip`.
#guard gapGuardedWrite [0x74, 0x72, 0x75, 0x65, 0x20] 5 0 = GapWrite.none
#guard decide
  (gapGuardedWrite [0x74, 0x72, 0x75, 0x65, 0x20] 5 0 ≠
    GapWrite.err 5 gapTagExtra)

/-! ### NE10 — the literal chain's case table

`neLitCheck` is the rule the emitted compare computes, byte for byte:
`neLitCheck_eq_litCheck` identifies it with the certified `lit_check`, and
`stage2NoEventLitChain_run` is the body statement — from `if.end519` the pinned
chain reaches `if.then527` with the rule's offset, or `if.end545` with `none`,
and writes nothing.  The rows below read the rule at that boundary; the refusal
block's `%off` store and its `od_gap_recover` call are the walk's, so the table
stops at the offset the chain leaves for the phi.

The token is the document window the chain reads, `n = ee - idx` bytes from the
literal's start, and a refusing row's value is the C text's `pos + ei`.
-/
#check neLitCheck_eq_litCheck
#check stage2NoEventLitChain_run

-- The three accepted literals: the token equals the packed immediate.
#guard decide (neLitCheck [0x74, 0x72, 0x75, 0x65] (packBytes neLitTrue 4) = none)
#guard decide (neLitCheck [0x66, 0x61, 0x6C, 0x73, 0x65] (packBytes neLitFalse 5) = none)
#guard decide (neLitCheck [0x6E, 0x75, 0x6C, 0x6C] (packBytes neLitNull 4) = none)

-- `tru`: the token ends inside `true`, after the third byte.
#guard decide (neLitCheck [0x74, 0x72, 0x75] (packBytes neLitTrue 4) = some 3)

-- `truth`: the fourth byte differs (`t` against `e`), so the rule stops at 3.
#guard decide
  (neLitCheck [0x74, 0x72, 0x75, 0x74, 0x68] (packBytes neLitTrue 4) = some 3)

-- `truE`: the compare is case-sensitive, so the fourth byte differs.
#guard decide
  (neLitCheck [0x74, 0x72, 0x75, 0x45] (packBytes neLitTrue 4) = some 3)

-- `nul`: the token ends inside `null`, after the third byte.
#guard decide (neLitCheck [0x6E, 0x75, 0x6C] (packBytes neLitNull 4) = some 3)

-- `nullx`: the token runs past `null` with a matching prefix, so the refusal is
-- the literal's width.
#guard decide
  (neLitCheck [0x6E, 0x75, 0x6C, 0x6C, 0x78] (packBytes neLitNull 4) = some 4)

-- `fals`: the token ends inside `false`, after the fourth byte.
#guard decide
  (neLitCheck [0x66, 0x61, 0x6C, 0x73] (packBytes neLitFalse 5) = some 4)

-- `falsey`: the token runs past `false` with a matching prefix.
#guard decide
  (neLitCheck [0x66, 0x61, 0x6C, 0x73, 0x65, 0x79] (packBytes neLitFalse 5) = some 5)

-- A complete literal ending the document: `[true` carries the token `true`, so
-- the chain accepts it (the rule's `none`).  The document's refusal at `5` is
-- the end-of-stream rule at `n`, the walk's, not this chain's: the compare is
-- not what refuses this token.
#guard decide (neLitCheck [0x74, 0x72, 0x75, 0x65] (packBytes neLitTrue 4) = none)

/-- The first refusal row's expected value with its immediate changed, `3` to `4`
— the stale table a wrong transcription carries. -/
def neLitTruExpectedMutated : Option Nat := some 4

-- The rule answers the row's pinned value ...
#guard decide (neLitCheck [0x74, 0x72, 0x75] (packBytes neLitTrue 4) = some 3)

-- ... and not the changed immediate, so the expected values are load-bearing.
#guard decide
  (neLitCheck [0x74, 0x72, 0x75] (packBytes neLitTrue 4) ≠ neLitTruExpectedMutated)

-- The fixture side of the control: the IR pin's own mutant changes one immediate
-- in the body text, still parses, and is not the pinned body, so the rows are
-- about the committed text and a one-word change bites.
#guard decide
  (LeanLLVM.Refinement.JsonStage2NoEventIR.stage2NoEventSrcMutated ≠
    LeanLLVM.Refinement.JsonStage2NoEventIR.stage2NoEventSrc)
#guard decide
  (LeanLLVM.Refinement.JsonStage2NoEventIR.firstFunction
      LeanLLVM.Refinement.JsonStage2NoEventIR.stage2NoEventSrcMutated ≠
    some LeanLLVM.Refinement.JsonStage2NoEventIR.stage2NoEventBody)

end JsonNoEventScenario
