/-
The word the list loop computes, read as the block's own position rule.

`ListLoopInv`'s first conjunct is about the residual word `w` — its set lanes are
the positions not yet emitted — and the word the loop leaves at `xl_lanes.exit` is
`setLanes` of the index list, so the invariant can only be established at the loop
head if the word the body forms *is* the position rule's list.  This module states
that identification, and nothing about the body's instructions: it is the lane
algebra between three mask words and `escapePositionsFrom`.

The body's word at `%and31.i` is `(ctl | e) & im`, where `e` is the run-start word
`specRunStarts` (`JsonEscapeListInvariant`).  Lane by lane the rule is
`IsEscapeLane` at the carry the lane was entered with, so the identification is

  `setLanes (specPositionWord bs ctl im odd0) = escapePositionsFrom (block64 lo hi) st`

under the record's three mask clauses and `st.oddRun = odd0`.  The halves are joined
by `classCarryAt_append` — the high half is entered with the carry the low half
left — and the run-start word's parity is `classCarryAt_oddRun`'s, so the two
readings of a lane are the same fold.  `isEscapeLane_eq_escapeWord` is the lane-level
comparison in `JsonScanSpec`'s vocabulary; the per-half assembly is here.
-/
import LeanLLVM.Refinement.JsonEscapeListInvariant
import LeanLLVM.Refinement.JsonEscapeListFixpoint
import LeanLLVM.Refinement.JsonEscapeSpec
import LeanLLVM.Refinement.JsonScanSpec
import LeanLLVM.Refinement.JsonS1MasksIR
import LeanLLVM.Refinement.BitLanes

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.BitLanes

/-! ### The block's bytes at a lane

The block is the two halves joined, so a lane below thirty-two reads the low half
and a lane at sixty-four minus thirty-two reads the high half.  Both are `ofFn`
lookups, which is what the masks' lane lemmas take. -/

/-- A lane below the halfway point reads the low half. -/
theorem block64_getElem?_lo {lo hi : Block32} {k : Nat} (hk : k < 32) :
    (block64 lo hi)[k]? = (List.ofFn lo)[k]? := by
  unfold block64
  rw [List.getElem?_append_left (by simpa using hk)]

/-- A lane at or above the halfway point reads the high half, shifted by 32. -/
theorem block64_getElem?_hi {lo hi : Block32} {j : Nat} (hj : j < 32) :
    (block64 lo hi)[j + 32]? = (List.ofFn hi)[j]? := by
  unfold block64
  rw [List.getElem?_append_right (by simp), List.length_ofFn,
    show j + 32 - 32 = j from by omega]

/-- The low-half lookup at a lane inside it. -/
theorem ofFn_getElem?_of_lt {lo : Block32} {k : Nat} (hk : k < 32) :
    (List.ofFn lo)[k]? = some (lo ⟨k, hk⟩) := by
  rw [List.getElem?_ofFn]
  simp [hk]

/-- The block's length is its sixty-four lanes. -/
theorem block64_length (lo hi : Block32) : (block64 lo hi).length = 64 := rfl

/-! ### The masks at a lane

Each mask is the joined halves, so a lane reads the half it falls in.  The
in-string mask's high half is entered with the carry the low half left, which is
`classMask64`'s own composition. -/

theorem specBackslash64_getLsbD_lo {lo hi : Block32} {st : ClassState} {k : Nat}
    (hk : k < 32) :
    (specBackslash64 lo hi st).getLsbD k = IsBackslashB (lo ⟨k, hk⟩) := by
  unfold specBackslash64
  rw [classMask64_getLsbD_lo backslashMask lo hi st hk,
    backslashMask_getLsbD hk (ofFn_getElem?_of_lt hk)]

theorem specBackslash64_getLsbD_hi {lo hi : Block32} {st : ClassState} {j : Nat}
    (hj : j < 32) :
    (specBackslash64 lo hi st).getLsbD (j + 32) = IsBackslashB (hi ⟨j, hj⟩) := by
  unfold specBackslash64
  rw [classMask64_getLsbD_hi backslashMask lo hi st hj,
    backslashMask_getLsbD hj (ofFn_getElem?_of_lt hj)]

theorem specControl64_getLsbD_lo {lo hi : Block32} {st : ClassState} {k : Nat}
    (hk : k < 32) :
    (specControl64 lo hi st).getLsbD k = IsControlB (lo ⟨k, hk⟩) := by
  unfold specControl64
  rw [classMask64_getLsbD_lo controlMask lo hi st hk, controlMask,
    maskOfListWith_getLsbD hk (ofFn_getElem?_of_lt hk)]

theorem specControl64_getLsbD_hi {lo hi : Block32} {st : ClassState} {j : Nat}
    (hj : j < 32) :
    (specControl64 lo hi st).getLsbD (j + 32) = IsControlB (hi ⟨j, hj⟩) := by
  unfold specControl64
  rw [classMask64_getLsbD_hi controlMask lo hi st hj, controlMask,
    maskOfListWith_getLsbD hj (ofFn_getElem?_of_lt hj)]

theorem specInString64_getLsbD_lo {lo hi : Block32} {st : ClassState} {k : Nat}
    (hk : k < 32) :
    (specInString64 lo hi st).getLsbD k =
      inStringAfter (classCarryAt (List.ofFn lo) st k) (lo ⟨k, hk⟩) := by
  unfold specInString64
  rw [classMask64_getLsbD_lo inStringMask lo hi st hk,
    inStringMask_getLsbD hk (ofFn_getElem?_of_lt hk)]

theorem specInString64_getLsbD_hi {lo hi : Block32} {st : ClassState} {j : Nat}
    (hj : j < 32) :
    (specInString64 lo hi st).getLsbD (j + 32) =
      inStringAfter (classCarryAt (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry) j)
        (hi ⟨j, hj⟩) := by
  unfold specInString64
  rw [classMask64_getLsbD_hi inStringMask lo hi st hj,
    inStringMask_getLsbD hj (ofFn_getElem?_of_lt hj)]

/-! ### The carries across the halfway point

The high half is entered with the carry the low half left, at both the fold and the
parity the run-start word reads. -/

/-- The carry at a lane of the low half is the low half's own fold. -/
theorem classCarryAt_block64_eq_lo {lo hi : Block32} (st : ClassState) {k : Nat}
    (hk : k ≤ 32) :
    classCarryAt (block64 lo hi) st k = classCarryAt (List.ofFn lo) st k := by
  unfold classCarryAt block64
  rw [List.take_append]
  rw [show (List.ofFn lo).length = 32 from List.length_ofFn]
  rw [show k - 32 = 0 from by omega, List.take_zero, List.append_nil]

/-- The carry at a lane of the high half is the high half's fold, entered with the
carry the low half left. -/
theorem classCarryAt_block64_eq_hi {lo hi : Block32} (st : ClassState) (j : Nat) :
    classCarryAt (block64 lo hi) st (j + 32) =
      classCarryAt (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry) j := by
  unfold block64
  rw [show j + 32 = (List.ofFn lo).length + j from by rw [List.length_ofFn]; omega,
    classCarryAt_append]
  congr 1

/-- The run-start word's parity is the block's own run parity, at every lane. -/
theorem parityBit_specBackslash64 (lo hi : Block32) (st : ClassState) (k : Nat)
    (hk : k ≤ 64) :
    parityBit (specBackslash64 lo hi st) st.oddRun k = parityAt (block64 lo hi) st.oddRun k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [parityBit_succ, parityAt]
      have hk64 : k < 64 := by omega
      have hih := ih (by omega)
      by_cases hk32 : k < 32
      · rw [specBackslash64_getLsbD_lo hk32, block64_getElem?_lo hk32,
          ofFn_getElem?_of_lt hk32]
        simp only
        by_cases hb : IsBackslashB (lo ⟨k, hk32⟩) <;> simp [hb, hih]
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 32 := ⟨k - 32, by omega⟩
        rw [specBackslash64_getLsbD_hi (by omega), block64_getElem?_hi (by omega),
          ofFn_getElem?_of_lt (by omega)]
        simp only
        by_cases hb : IsBackslashB (hi ⟨j, by omega⟩) <;> simp [hb, hih]

/-! ### The word at a lane

The body's word is `(e | ctl) & im` with `e` the run-start word, so a lane reads
the parity's run start or the control lane, restricted to the in-string lane.  The
low and high halves carry different folds, which is why the two lemmas are separate
rather than one with a case split inside. -/

theorem positionWord_lane_lo {lo hi : Block32} {st : ClassState} {k : Nat} (hk : k < 32) :
    (specPositionWord (specBackslash64 lo hi st) (specControl64 lo hi st)
        (specInString64 lo hi st) st.oddRun).getLsbD k =
      IsEscapeLane (classCarryAt (block64 lo hi) st k) (lo ⟨k, hk⟩) := by
  unfold specPositionWord
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or,
    specRunStarts_getLsbD (bs := specBackslash64 lo hi st) (odd0 := st.oddRun) (k := k)
      (by omega)]
  rw [specBackslash64_getLsbD_lo hk, specControl64_getLsbD_lo hk,
    specInString64_getLsbD_lo hk]
  have hpar : parityBit (specBackslash64 lo hi st) st.oddRun k =
      (classCarryAt (block64 lo hi) st k).oddRun := by
    rw [parityBit_specBackslash64 lo hi st k (by omega), ← classCarryAt_oddRun]
  rw [hpar, classCarryAt_block64_eq_lo st (by omega)]
  unfold IsEscapeLane
  simp only [Bool.and_comm, Bool.or_comm]

theorem positionWord_lane_hi {lo hi : Block32} {st : ClassState} {j : Nat} (hj : j < 32) :
    (specPositionWord (specBackslash64 lo hi st) (specControl64 lo hi st)
        (specInString64 lo hi st) st.oddRun).getLsbD (j + 32) =
      IsEscapeLane (classCarryAt (block64 lo hi) st (j + 32)) (hi ⟨j, hj⟩) := by
  unfold specPositionWord
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or,
    specRunStarts_getLsbD (bs := specBackslash64 lo hi st) (odd0 := st.oddRun) (k := j + 32)
      (by omega)]
  rw [specBackslash64_getLsbD_hi hj, specControl64_getLsbD_hi hj,
    specInString64_getLsbD_hi hj]
  have hpar : parityBit (specBackslash64 lo hi st) st.oddRun (j + 32) =
      (classCarryAt (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry) j).oddRun := by
    rw [parityBit_specBackslash64 lo hi st (j + 32) (by omega)]
    unfold block64
    rw [show j + 32 = (List.ofFn lo).length + j from by rw [List.length_ofFn]; omega,
      parityAt_append, List.length_ofFn]
    exact (classCarryAt_oddRun (List.ofFn hi) (classCarryAt (List.ofFn lo) st 32) j).symm
  rw [hpar, classCarryAt_block64_eq_hi st j]
  unfold IsEscapeLane
  simp only [Bool.and_comm, Bool.or_comm]

/-! ### The position list

`setLanes` filters the lane range by the word's lane; `escapePositionsFrom` filters
the same range by the rule at the block's byte.  The two lane lemmas are the
agreement, so the lists are equal. -/

/-- **The word the loop computes is the block's position list.**  The record's
three mask clauses and the parity the block is entered with identify
`specPositionWord`'s set lanes with `escapePositionsFrom`'s positions. -/
theorem setLanes_specPositionWord {lo hi : Block32} {st : ClassState} :
    setLanes (specPositionWord (specBackslash64 lo hi st) (specControl64 lo hi st)
        (specInString64 lo hi st) st.oddRun) =
      escapePositionsFrom (block64 lo hi) st := by
  unfold setLanes escapePositionsFrom
  rw [block64_length]
  apply List.filter_congr
  intro k hk
  rw [List.mem_range] at hk
  by_cases hk32 : k < 32
  · rw [positionWord_lane_lo (lo := lo) (hi := hi) (st := st) hk32,
      block64_getElem?_lo hk32, ofFn_getElem?_of_lt hk32]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 32 := ⟨k - 32, by omega⟩
    rw [positionWord_lane_hi (lo := lo) (hi := hi) (st := st) (j := j) (by omega),
      block64_getElem?_hi (by omega), ofFn_getElem?_of_lt (by omega)]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.setLanes_specPositionWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms setLanes_specPositionWord

/-- info: 'LeanLLVM.Refinement.parityBit_specBackslash64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms parityBit_specBackslash64

end LeanLLVM.Refinement
