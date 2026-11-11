/-
The caller-visible footprint of a call.

A `Calls` environment answers what a callee returned, and that answer carries the
callee's whole memory.  A caller's record about the region it did *not* hand over
therefore cannot be read off the call: the callee writes its own frame, the
returned memory contains those bytes, and the model has no fresh frame per call,
so the callee's private addresses are outside every region the caller names
(`JsonPipelineSpec.SigmaFrame`).

This module adds the one fact a caller needs and `Calls` cannot state: the
regions a callee may have written, as a function of what the caller already
holds — the symbol, the argument list, the memory handed over and the allocator
cursor.  It is a bundle *over* `Calls`: `Mem`, `State`, `CallOutcome` and `Calls`
are unchanged, so every existing record keeps its statement and every existing
environment keeps its definition, and a record gains a frame by being paired with
a footprint.

The footprint is the callee's declaration in the form its caller can evaluate:
`foot` is read before the call from the symbol, the arguments, the memory handed
over and the allocator cursor, and `framed` is the statement that the callee's
returned memory differs from the handed-over memory only inside it.  A caller
that knows an address is outside the footprint keeps that address's bytes
(`keeps_of_not_mem`), and a frame the callee proves over its own list is a frame
over the caller's view (`CallerView_of_framed`) because the view is the
concatenation and `UnchangedOutside.widen` widens membership alone.

`UnchangedOutside` and its `widen` lemma live here rather than in
`JsonEscapeSteps` because the bundle needs them and the four intrinsic
environments that instantiate it sit below that module in the import graph.  The
definition and the lemma are the ones that module stated; only the module that
holds them moved.
-/
import LeanLLVM.Semantics

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM

/-- Every byte outside `regions` reads as it did before the run.  A region is an
address and a length; the extent a run wrote is the list of regions it names, and a
byte the store reached is inside one of them. -/
def UnchangedOutside (mem m : Mem) (regions : List (Nat × Nat)) : Prop :=
  ∀ a, (∀ r ∈ regions, ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) → readByte m a = readByte mem a

/-- **A frame over a narrow region list implies one over a wider list**, when every
byte the wider list excludes is a byte the narrow list excludes.  The predicate
talks about the *union of the regions*, not about the list: a region list whose
covered set is larger is a weaker statement, and a run that kept silence over the
narrow covered set kept it over the larger one too.  `mono` is the special case
where the wider list's regions are literally members of the narrow list; this is
the case where they are the same region list's extents with different widths,
which no membership argument can express. -/
theorem UnchangedOutside.widen {m0 m : Mem} {R R' : List (Nat × Nat)}
    (h : UnchangedOutside m0 m R')
    (hsub : ∀ a, (∀ r ∈ R, ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) →
      ∀ r ∈ R', ¬ (r.1 ≤ a ∧ a < r.1 + r.2)) :
    UnchangedOutside m0 m R :=
  fun a ha => h a (hsub a ha)

/-- **The regions a call may have written, rolled over its environment.**

`foot sym args mem next` is evaluated from the values the caller holds before the
call — which is why it takes the argument list rather than the callee's
parameters — and `framed` is the frame fact at it: outside those regions the
returned memory reads as the handed-over memory did.

Stated over `Calls` as a parameter rather than a field so that a bundle is
*about* an environment: the same environment can be paired with a footprint, and
`CallsFootprint`'s projections do not hide which selection they describe. -/
structure CallsFootprint (calls : Calls) where
  /-- The regions of the callee's memory that may differ from the caller's, read
  from the symbol, the arguments, the caller's memory and the allocator cursor. -/
  foot : String → List Value → Mem → Nat → List (Nat × Nat)
  /-- The frame fact at `foot`: outside those regions the returned memory is the
  handed-over memory. -/
  framed : ∀ sym args mem next r, calls sym args mem next = some r →
    UnchangedOutside mem r.mem (foot sym args mem next)

/-- **A selection that returns the caller's memory unchanged has the empty
footprint.**  Every arm of such an environment answers with the memory it was
handed, so silence outside no regions is silence everywhere.  The hypotheses are
the environment's own readings, which is why this is a constructor rather than a
`framed` proof repeated per environment. -/
def CallsFootprint.pure (calls : Calls)
    (h : ∀ sym args mem next r, calls sym args mem next = some r → r.mem = mem) :
    CallsFootprint calls where
  foot := fun _ _ _ _ => []
  framed := by
    intro sym args mem next r hcall a _
    rw [h sym args mem next r hcall]

/-- **The environment in which no call resolves needs no footprint.**  It returns
no outcome, so its `framed` field is vacuous. -/
def noCallsFootprint : CallsFootprint noCalls where
  foot := fun _ _ _ _ => []
  framed := by
    intro sym args mem next r hcall
    simp only [noCalls] at hcall
    cases hcall

/-- **A byte outside the callee's footprint reads as it did before the call.**
The premise is membership in the footprint the callee declared, and the caller
supplies it from its own addresses: an object it staged at an address the
callee's list misses is byte-for-byte what it left.  This is the shape a frame
clause about a caller object takes once the callee's scratch is caller-visible;
the caller's own region list does not appear in it. -/
theorem keeps_of_not_mem {calls : Calls} {fc : CallsFootprint calls} {sym : String}
    {args : List Value} {mem : Mem} {next : Nat} {r : CallOutcome} {a : Nat}
    (hcall : calls sym args mem next = some r)
    (ha : ∀ q ∈ fc.foot sym args mem next, ¬ (q.1 ≤ a ∧ a < q.1 + q.2)) :
    readByte r.mem a = readByte mem a :=
  fc.framed sym args mem next r hcall a ha

/-- **The caller's view of a call**: the regions the caller names, extended by the
regions the callee declared.  It is `UnchangedOutside` at the concatenation, so
the tree's `widen` carries a fact between the two spellings and no second frame
predicate is introduced: the caller's list is the left summand and the callee's
the right one. -/
def CallerView (caller callee : List (Nat × Nat)) (mem m : Mem) : Prop :=
  UnchangedOutside mem m (caller ++ callee)

/-- **A frame the callee proves over its own list is a frame over the caller's
view.**  Membership in the footprint is membership in the concatenation's right
summand, so the callee's `UnchangedOutside` needs no weakening of its own and the
caller's regions never enter the proof. -/
theorem CallerView_of_framed {mem m : Mem} {caller callee : List (Nat × Nat)}
    (h : UnchangedOutside mem m callee) : CallerView caller callee mem m :=
  UnchangedOutside.widen h (fun _a ha r hr => ha r (List.mem_append_right _ hr))

/-! ### Axiom footprints

The bundle and its projections state what the environment's own frame fact says,
so nothing here adds a principle: the structure is data, the constructors supply
the empty footprint, and the theorems are projections and membership rewrites. -/

/-- info: 'LeanLLVM.Refinement.UnchangedOutside.widen' does not depend on any axioms -/
#guard_msgs in
#print axioms UnchangedOutside.widen

/-- info: 'LeanLLVM.Refinement.keeps_of_not_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms keeps_of_not_mem

/-- info: 'LeanLLVM.Refinement.CallerView_of_framed' does not depend on any axioms -/
#guard_msgs in
#print axioms CallerView_of_framed

/-- info: 'LeanLLVM.Refinement.UnchangedOutside' does not depend on any axioms -/
#guard_msgs in
#print axioms UnchangedOutside

/-- info: 'LeanLLVM.Refinement.CallsFootprint' does not depend on any axioms -/
#guard_msgs in
#print axioms CallsFootprint

/-- info: 'LeanLLVM.Refinement.CallsFootprint.pure' does not depend on any axioms -/
#guard_msgs in
#print axioms CallsFootprint.pure

/-- info: 'LeanLLVM.Refinement.noCallsFootprint' does not depend on any axioms -/
#guard_msgs in
#print axioms noCallsFootprint

/-- info: 'LeanLLVM.Refinement.CallerView' does not depend on any axioms -/
#guard_msgs in
#print axioms CallerView

end LeanLLVM.Refinement
