/-
A frame relation: two runs agree on every byte outside a footprint.

`Refines` compares whole `Outcome`s, so the returned memories must be equal for
a source to match a target.  That is the right contract for a transformation
that preserves memory exactly, and the wrong one for a replacement that
allocates privately: the loop's own two locals are not caller-visible, so
demanding their equality would reject a sound replacement.

This module states the finer relation.  A footprint is a predicate on
addresses; the one this development uses is read off the allocator state of an
execution (`AllocFrame`), not written as a constant interval.  Memory is
compared byte by byte, because the representation is an association list and
equality of the whole list is stronger than anything a caller can observe.

The lemmas are the one-sided write law (a store inside the frame on one side
does not disturb agreement outside it) and the union rule for two private
footprints.  A write outside the frame is not allowed to differ, which is what
makes the relation sound for caller-visible memory.  `RefinesWithin` also keeps
the direction of `ub`: a target that is undefined admits every outcome, so it
forces an undefined source, and a private allocation cannot hide that.
-/
import LeanLLVM.Memory

namespace LeanLLVM

/-! ### Agreement outside a footprint -/

/-- Two memories agree on every address outside `frame`. -/
def AgreesOutsideMem (m n : Mem) (frame : Nat → Prop) : Prop :=
  ∀ a, ¬ frame a → readByte m a = readByte n a

theorem AgreesOutsideMem.refl (m : Mem) (frame : Nat → Prop) :
    AgreesOutsideMem m m frame :=
  fun _ _ => rfl

theorem AgreesOutsideMem.symm {m n : Mem} {frame : Nat → Prop}
    (h : AgreesOutsideMem m n frame) : AgreesOutsideMem n m frame :=
  fun a ha => (h a ha).symm

theorem AgreesOutsideMem.trans {m n p : Mem} {frame : Nat → Prop}
    (hmn : AgreesOutsideMem m n frame) (hnp : AgreesOutsideMem n p frame) :
    AgreesOutsideMem m p frame :=
  fun a ha => (hmn a ha).trans (hnp a ha)

/-- A larger footprint is a weaker claim. -/
theorem AgreesOutsideMem.mono {m n : Mem} {frame frame' : Nat → Prop}
    (h : AgreesOutsideMem m n frame) (hsub : ∀ a, frame a → frame' a) :
    AgreesOutsideMem m n frame' :=
  fun a ha => h a (fun hf => ha (hsub a hf))

/-- A byte sequence written inside the frame on one side leaves agreement
outside the frame untouched.  The start and length are free and the other
memory is not written, so this covers a unit that writes to an allocation the
other unit does not have. -/
theorem AgreesOutsideMem.writeBytes_left {m n : Mem} {frame : Nat → Prop}
    (h : AgreesOutsideMem m n frame) {start : Nat} {bs : List UInt8}
    (hframe : ∀ k, k < bs.length → frame (start + k)) :
    AgreesOutsideMem (writeBytes m start bs) n frame := by
  intro a ha
  have hout : a < start ∨ start + bs.length ≤ a := by
    by_cases h1 : a < start
    · exact Or.inl h1
    · refine Or.inr ?_
      by_cases h2 : a < start + bs.length
      · exfalso
        have hk : a - start < bs.length := by omega
        have hf := hframe (a - start) hk
        rw [Nat.add_sub_of_le (by omega)] at hf
        exact ha hf
      · omega
  rw [readByte_writeBytes_outside m bs hout]
  exact h a ha

/-! ### Private footprints -/

/-- Nothing outside `frame` is present in the memory.  This is the property an
execution's own allocations establish, and the one a framed refinement may
ignore. -/
def MemPrivate (frame : Nat → Prop) (m : Mem) : Prop := AgreesOutsideMem m [] frame

theorem MemPrivate.nil (frame : Nat → Prop) : MemPrivate frame [] :=
  fun _ _ => rfl

theorem MemPrivate.writeBytes {frame : Nat → Prop} {m : Mem} {start : Nat}
    {bs : List UInt8} (h : MemPrivate frame m)
    (hframe : ∀ k, k < bs.length → frame (start + k)) :
    MemPrivate frame (writeBytes m start bs) :=
  AgreesOutsideMem.writeBytes_left h hframe

/-- Two memories, each private to its own footprint, agree outside the union of
the two footprints. -/
theorem AgreesOutsideMem.of_private {frameT frameS : Nat → Prop} {mT mS : Mem}
    (hT : MemPrivate frameT mT) (hS : MemPrivate frameS mS) :
    AgreesOutsideMem mT mS (fun a => frameT a ∨ frameS a) := by
  intro a ha
  rw [hT a (fun h => ha (Or.inl h)), hS a (fun h => ha (Or.inr h))]

/-! ### Footprints read off the allocator -/

/-- An address band. -/
def Band (lo hi : Nat) : Nat → Prop := fun a => lo ≤ a ∧ a < hi

/-- The band an execution's allocations cover: the allocator state before the
run to the allocator state after it.  Reading it off the states rather than a
literal interval means a unit that allocates nothing covers no address, and the
footprint of a unit that allocates is exactly what its `alloca`s handed out. -/
def AllocFrame (s₀ s₁ : State) : Nat → Prop := Band s₀.next s₁.next

/-- No bytes outside the band `[lo, hi)`. -/
def MemConfined (lo hi : Nat) (m : Mem) : Prop := MemPrivate (Band lo hi) m

/-- A write inside the band keeps the confinement: the recorded bounds are what
makes a store to a fresh allocation harmless outside it. -/
theorem MemConfined.writeBytes {lo hi : Nat} {m : Mem} {start : Nat}
    {bs : List UInt8} (h : MemConfined lo hi m) (hlen : start + bs.length ≤ hi)
    (hlo : lo ≤ start) : MemConfined lo hi (writeBytes m start bs) :=
  MemPrivate.writeBytes h (by intro k hk; exact ⟨by omega, by omega⟩)

/-! ### Behaviour-level refinement -/

/-- Two outcomes agree outside `frame`: both are `ub`, or both return the same
value and their memories agree outside `frame`.  A `ub` target is not matched by
a defined source, so memory agreement cannot hide undefined behaviour. -/
def Outcome.AgreesOutside (frame : Nat → Prop) : Outcome → Outcome → Prop
  | .ub, .ub => True
  | .ret v m, .ret w n => v = w ∧ AgreesOutsideMem m n frame
  | _, _ => False

theorem Outcome.agreesOutside_refl (o : Outcome) (frame : Nat → Prop) :
    o.AgreesOutside frame o := by
  cases o with
  | ub => trivial
  | ret v m => exact ⟨rfl, AgreesOutsideMem.refl m frame⟩

/-- Every target behaviour is matched by a source behaviour with the same
defined value and the same bytes outside `frame`. -/
def BehsWithin (target source : List Value → Outcome → Prop)
    (frame : Nat → Prop) : Prop :=
  ∀ args o, target args o → ∃ o', source args o' ∧ o.AgreesOutside frame o'

/-- Framed refinement of a function: `BehsWithin` on the two behaviour sets,
under a footprint derived from the executed allocations.  The direction of `ub`
and of divergence is `Refines`'s: a target that diverges (no behaviour) is
refined by anything, a source that diverges refines only a diverging target, and
a target that is undefined forces the source to be undefined. -/
def RefinesWithin (calls : Calls) (target source : Function)
    (frame : Nat → Prop) : Prop :=
  BehsWithin (Beh calls target) (Beh calls source) frame

/-- Exact refinement is framed refinement: an exact match agrees outside every
footprint.  Existing `Refines` theorems therefore keep their meaning and each
one yields a framed refinement; the framed relation is the weaker statement,
added beside them rather than in place of them. -/
theorem refinesWithin_of_refines {calls : Calls} {target source : Function}
    {frame : Nat → Prop} (h : Refines calls target source) :
    RefinesWithin calls target source frame :=
  fun args o ho => ⟨o, h args o ho, Outcome.agreesOutside_refl o frame⟩

end LeanLLVM
