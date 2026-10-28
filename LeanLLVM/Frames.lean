/-
A frame relation: two states agree on every address outside a footprint.

`BehVal` forgets the whole memory, which is right for a unit whose writes are
its own allocations and wrong for a caller-visible write.  This module states
the finer relation the loop needs: agreement outside a set of addresses.  The
footprint is a predicate on addresses, so it can be the interval a unit
allocates, a set of abstract locations, or anything else.

The lemmas say what a write inside the footprint does to the relation: it may
differ between the two states and the relation outside is untouched.  Writes
outside the footprint are not allowed to differ, which is why the relation is
sound where `BehVal` is only sound for local-only writes.
-/
import LeanLLVM.Memory

namespace LeanLLVM

/-- The two states agree on every address outside `frame`. -/
def AgreesOutside (s t : State) (frame : Nat → Prop) : Prop :=
  ∀ a, ¬ frame a → readByte s.mem a = readByte t.mem a

theorem AgreesOutside.refl (s : State) (frame : Nat → Prop) :
    AgreesOutside s s frame :=
  fun _ _ => rfl

theorem AgreesOutside.symm {s t : State} {frame : Nat → Prop}
    (h : AgreesOutside s t frame) : AgreesOutside t s frame :=
  fun a ha => (h a ha).symm

theorem AgreesOutside.trans {s t u : State} {frame : Nat → Prop}
    (hst : AgreesOutside s t frame) (htu : AgreesOutside t u frame) :
    AgreesOutside s u frame :=
  fun a ha => (hst a ha).trans (htu a ha)

/-- A byte written inside the footprint may differ; agreement outside is
untouched. -/
theorem AgreesOutside.write_byte {s t : State} {frame : Nat → Prop}
    (h : AgreesOutside s t frame) {a : Nat} (ha : frame a) (b c : UInt8) :
    AgreesOutside { s with mem := writeByte s.mem a b }
      { t with mem := writeByte t.mem a c } frame := by
  intro x hx
  have hne : a ≠ x := fun hEq => hx (hEq ▸ ha)
  simp only [readByte_writeByte_other _ _ hne]
  exact h x hx

/-- A sequence written inside the footprint may differ; agreement outside is
untouched.  The two writes must cover the same addresses. -/
theorem AgreesOutside.write_bytes_aux :
    ∀ (bs cs : List UInt8) (start : Nat) {s t : State} {frame : Nat → Prop},
      bs.length = cs.length →
      (∀ k, k < bs.length → frame (start + k)) →
      AgreesOutside s t frame →
      AgreesOutside { s with mem := writeBytes s.mem start bs }
        { t with mem := writeBytes t.mem start cs } frame
  | [], [], _, _, _, _, _, _, h => by simpa [writeBytes] using h
  | [], _ :: _, _, _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _ => by simp at hlen
  | b :: bs, c :: cs, start, s, t, frame, hlen, hframe, h => by
      let s' : State := { s with mem := writeByte s.mem start b }
      let t' : State := { t with mem := writeByte t.mem start c }
      have hstep : AgreesOutside s' t' frame :=
        AgreesOutside.write_byte h (hframe 0 (by simp)) b c
      have hshift : ∀ k, k < bs.length → frame (start + 1 + k) := by
        intro k hk
        have := hframe (k + 1) (by simp [hk])
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      have htail := write_bytes_aux bs cs (start + 1)
        (by simpa using hlen) hshift hstep
      simpa [writeBytes, s', t'] using htail

theorem AgreesOutside.write_bytes {s t : State} {frame : Nat → Prop}
    (h : AgreesOutside s t frame) {start : Nat} {bs cs : List UInt8}
    (hlen : bs.length = cs.length)
    (hframe : ∀ k, k < bs.length → frame (start + k)) :
    AgreesOutside { s with mem := writeBytes s.mem start bs }
      { t with mem := writeBytes t.mem start cs } frame :=
  AgreesOutside.write_bytes_aux bs cs start hlen hframe h

end LeanLLVM
