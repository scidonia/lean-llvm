/-
Return-value refinement: comparing two bodies by the value they return,
ignoring the memory they leave behind.

`Refines` compares whole outcomes, and an outcome carries the final memory.  A
function that allocates locals therefore differs from an equivalent function
that does not, even when both return the same value.  For a pure seam that is a
spurious difference, so this module states the weaker relation explicitly:

* `BehVal calls f args v` — `f` can return `v`, with any final memory;
* `RefinesVal calls target source` — every value the target can return is one
  the source can return.

`Refines.toRefinesVal` shows the weaker relation follows from the stronger one,
so the existing refinement theorems compose.  The converse does not hold, and
the relation is only sound for a unit whose memory writes are to its own
allocations; a caller-visible write would be observable and is not forgotten
here.  The general heap relation is the M2 work this stands in for.
-/
import LeanLLVM.Semantics

namespace LeanLLVM

/-- `f` can return `v`, under any final memory. -/
def BehVal (calls : Calls) (f : Function) (args : List Value) (v : Value) : Prop :=
  ∃ mem, Beh calls f args (.ret (some v) mem)

/-- Every value the target can return is one the source can return. -/
def RefinesVal (calls : Calls) (target source : Function) : Prop :=
  ∀ args v, BehVal calls target args v → BehVal calls source args v

theorem Refines.toRefinesVal {calls : Calls} {t s : Function}
    (h : Refines calls t s) : RefinesVal calls t s :=
  fun args v ⟨mem, hb⟩ => ⟨mem, h args _ hb⟩

theorem RefinesVal.refl (calls : Calls) (f : Function) : RefinesVal calls f f :=
  fun _ _ h => h

theorem RefinesVal.trans {calls : Calls} {a b c : Function}
    (hab : RefinesVal calls a b) (hbc : RefinesVal calls b c) :
    RefinesVal calls a c :=
  fun args v h => hbc args v (hab args v h)

end LeanLLVM
