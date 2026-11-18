/-
A small negative fixture for the write-set check, with its positive control.

`Path.lookupName` transports a name along a path whose admitted blocks write none
of it; the hypothesis is `PreservedAlong`, and `PathTransport` supplies the two
readings a caller usually has (`UnwrittenBy`, `WrittenOnlyAt`).  The check is a
`decide` over the pinned function's blocks, so a function that gains a write to
the claimed register must fail it.

The fixture is three blocks.  `fixtureBody false` copies nothing and writes no
`%r`; `fixtureBody true` is the same function with one write to `%r` in its middle
block — the "add a write to a claimed preserved register" mutation.  The pair of
`decide`s below is the check's discriminating power:

* `fixture_preserved_positive` passes, and `fixture_transport` spends it through
  `Path.lookupName`;
* `fixture_preserved_negative` fails on the mutated body, so the generic rule
  cannot be applied there.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.PathTransport

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-- The fixture: `b0 → b1 → b2`, with `%r` written in the middle block exactly
when `write` is set. -/
def fixtureBody (write : Bool) : Function where
  name := "fixture"
  retTy := .void
  params := []
  blocks :=
    [{ name := "b0", instrs := [], term := .br "b1" },
     { name := "b1",
       instrs :=
         if write then
           [.binop "%r" .add 64 (.reg "%r") (.imm (.int 64 1))]
         else [],
       term := .br "b2" },
     { name := "b2", instrs := [], term := .ret .void none }]

/-- The strong reading the positive fixture has: no block writes `%r`. -/
theorem fixture_unwritten_positive : UnwrittenBy (fixtureBody false) "%r" := by decide

/-- The narrow reading: only `b1` writes `%r`, and it does so in both variants —
so it says nothing about the mutated body's middle block being avoided. -/
theorem fixture_writtenOnlyAt_b1 : WrittenOnlyAt (fixtureBody true) "%r" "b1" := by decide

/-- **The positive control.**  The filter admits every block and no block of the
unmutated fixture writes `%r`: the generic side condition holds. -/
theorem fixture_preserved_positive :
    PreservedAlong (fixtureBody false) "%r" (fun _ => True) := by decide

/-- **The negative fixture.**  With the write added in `b1`, the same side
condition fails — `b1` is admitted and does write `%r`. -/
theorem fixture_preserved_negative :
    ¬ PreservedAlong (fixtureBody true) "%r" (fun _ => True) := by decide

/-- The mutated body, read through the strong form: it fails too. -/
theorem fixture_unwritten_negative : ¬ UnwrittenBy (fixtureBody true) "%r" := by decide

/-- The narrow form does not save a filter that admits the writer: excluding
`b0` still admits `b1`, which writes `%r` in the mutated body. -/
theorem fixture_writtenOnlyAt_admits_negative :
    ¬ PreservedAlong (fixtureBody true) "%r" (fun b => b ≠ "b0") := by decide

/-- **The positive control spent.**  The check feeds `Path.lookupName`: on the
unmutated fixture any path admits the transport.  On the mutated body there is no
such theorem, because `fixture_preserved_negative` denies its hypothesis. -/
theorem fixture_transport {s e : State}
    (h : Path noCalls (fixtureBody false) (fun _ => True) s e) :
    lookupName e.env "%r" = lookupName s.env "%r" :=
  Path.lookupName fixture_preserved_positive h

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.fixture_unwritten_positive' does not depend on any axioms -/
#guard_msgs in
#print axioms fixture_unwritten_positive

/-- info: 'LeanLLVM.Refinement.fixture_preserved_positive' does not depend on any axioms -/
#guard_msgs in
#print axioms fixture_preserved_positive

/-- info: 'LeanLLVM.Refinement.fixture_preserved_negative' does not depend on any axioms -/
#guard_msgs in
#print axioms fixture_preserved_negative

/-- info: 'LeanLLVM.Refinement.fixture_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fixture_transport

end LeanLLVM.Refinement
