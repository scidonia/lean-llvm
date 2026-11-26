/-
# The flush route's refusal offset, at the parser, for the no-event entry

The no-event walk's refusal rows store an offset in the refusal record and copy it
to the caller's `*err`; what they still owe the consumer is the parser-side
statement that the parser's own refusal at that document carries the position the
route stored (`ParserRows`' third conjunct, `RefusalOffset` in `JsonPipelineSpec`).
This module settles that row for one route: the flush arm, the same class
`JsonStage2WalkRefusalOffset` settles for the certified walk.

## The route and its stored offset

At `K.nep = 0` the entry block's test takes its true arm straight to `if.then`
(`Stage2NoEventWalkSegment.flush`), and the flush arm writes the document's length
into the refusal record's offset field (`stage2NoEventFlush_denote`,
`flushInstrs`' `%n` store at `%err`) before the refusal copy writes the same word
to the caller.  So the flush route's refusal offset is the report's `h.n`, and the
row the caller reads is `RefusalOffset h.bs h.n`.

## The parser's answer at that document

`refusalOffset_allSpace` (`JsonStage2WalkRefusalOffset`) is the parser's own fact
for the document the empty entry stream stands for: a whitespace-only document at
a length inside the input bound is refused at its end, `.unexpectedEnd bs.length`,
whose `rejectPos` is the document's end — or at the byte-order mark, which carries
no position and leaves the clause vacuous.  The report's `h.n` is `h.bs.length` by
the staging's own read (`readBytes_length` at `h.doc`), so the two are the same
offset.

## Why the document hypothesis, and not `K.nep = 0`

The staging names an entry at every unescaped quote, at every delimiter outside a
string and at every scalar-run start, so the stream the flush route consumes at
`nep = 0` is the document with none of those bytes — the whitespace-only document.
That the staged `ent` *is* the emitter's lanes is the entry route's composition,
outside this tree; the geometry records only that the positions are ordered and
inside the document, so `nep = 0` alone constrains no byte of `bs`.  The document's
content is this route's parser-side hypothesis, as it is in the certified module.

## The report's equation, and the residue

`h.eoff` is the word the refusal arm read out of the offset field, so the flush
class's report satisfies `h.eoff = h.n` — the equation the flush arm's store
supplies.  The report alone gives only `h.offLe : h.eoff ≤ h.n`, and no other route
is claimed: the payload refusal arms store other words (the observed `%off`, the
token words), and their `RefusalOffset` rows are the other classes' work.  Nothing
here states a class the terminal rows do not produce.

There is no `sorry`, `admit` or `native_decide`; the axiom pins are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NoEventBody
import LeanLLVM.Refinement.JsonStage2WalkRefusalOffset
import LeanLLVM.Refinement.JsonEntrySteps

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-! ### The report's document length -/

/-- **The report's document read fixes its length.**  `h.n` is the byte count the
report's own `doc` read names, so the document's length and the report's offset
word are the same number. -/
theorem stage2NoEventRun_bs_length {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0) : h.bs.length = h.n :=
  JsonEntrySteps.readBytes_length mem h.b h.n h.doc

/-! ### The flush class -/

/-- **The flush route's refusal offset, at the run report.**  At a whitespace-only
document inside the input bound the parser refuses at the document's end
(`refusalOffset_allSpace`), and the report's `h.n` is that end
(`stage2NoEventRun_bs_length`).  This is the flush class only: the entry stream is
empty and the document carries no structural byte, so no other refusal route's
offset is claimed. -/
theorem stage2NoEventRefusalOffset_flush {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0)
    (hbound : h.bs.length ≤ Limits.default.maxInput)
    (hws : ∀ b ∈ h.bs, IsSpaceB b = true) :
    RefusalOffset h.bs h.n := by
  rw [← stage2NoEventRun_bs_length h]
  exact refusalOffset_allSpace hbound hws

/-- **The flush route's stored offset.**  The refusal arm reads its offset word out
of the record the flush arm wrote, and the flush arm wrote the document's length
there (`stage2NoEventFlush_denote`), so the flush class's report satisfies
`h.eoff = h.n`.  That equation is a hypothesis rather than a consequence of the
report: the report gives only `h.offLe : h.eoff ≤ h.n`, and the payload refusal
arms store other words. -/
theorem stage2NoEventRefusalOffset_flush_eoff {args : List Value} {mem m0 : Mem}
    (h : Stage2NoEventRun args mem m0)
    (hbound : h.bs.length ≤ Limits.default.maxInput)
    (hws : ∀ b ∈ h.bs, IsSpaceB b = true)
    (heoff : h.eoff = h.n) :
    RefusalOffset h.bs h.eoff := by
  rw [heoff]
  exact stage2NoEventRefusalOffset_flush h hbound hws

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.stage2NoEventRun_bs_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2NoEventRun_bs_length

/-- info: 'LeanLLVM.Refinement.stage2NoEventRefusalOffset_flush' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2NoEventRefusalOffset_flush

/-- info: 'LeanLLVM.Refinement.stage2NoEventRefusalOffset_flush_eoff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stage2NoEventRefusalOffset_flush_eoff

end LeanLLVM.Refinement
