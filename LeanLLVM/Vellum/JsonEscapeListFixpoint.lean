/-
The escape list's doubling map: the fixed point, and the bound at which it is
reached.

`escapeListFunction`'s `xl_lanes` closure runs the map
`e ↦ e | ((e << 2) & ((bs << 1) & bs))` from the word the entry blocks build, and
stops when the word stops changing.  The list record's `post` reads the result as
`specRunStarts bs (prevb && prevs)` — the lanes a backslash enters with even run
parity.  That the two are the same word is stated here in the two halves the record
needs:

* **the fixed point** (`stepWord_specRunStarts`): the rule's word is unchanged by
  the map, so no iteration can mark a lane the rule does not mark.  The one
  arithmetic fact is that a lane two above a marked lane is a backslash whose entry
  parity is even, because the lane between toggles it;
* **the reachability bound** (`stepN_escapeSeed_specRunStarts`): every lane the rule
  marks is reached from the seed within thirty-two iterations.  The map moves a
  lane by exactly two, and `spec_reach` carries the bound as a formula — lane `k`
  arrives at iteration `k / 2 + 1` at the latest — so `32` is the count the lane
  width forces (`63 / 2 + 1 = 32`) rather than a number the proof settled on.

Neither half suffices alone: the fixed point says the closure never overshoots the
rule, the bound says it never stops short of it.

The seed is the entry blocks' word: `%and.i = and %bs (xor (or %0 (shl %bs 1)) -1)`
for the run beginnings, with the `select` of `if.then.i` or'd in under that arm's
own gate for the lane-0/lane-1 boundary correction.  The lane forms those two words
reduce to are proved beside the seed, because the halves are statements about lanes.
-/
import LeanLLVM.Vellum.JsonEscapeListInvariant
import LeanLLVM.Vellum.JsonEscapeBatch
import LeanLLVM.Vellum.BitLanes

namespace LeanLLVM.Vellum

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEscapeIR
open LeanLLVM.Vellum.JsonS1MasksIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.JsonEscapeIntrinsics
open LeanLLVM.Vellum.BitLanes

def stepMask (bs : BitVec 64) : BitVec 64 := (bs <<< 1) &&& bs
def stepWord (bs : BitVec 64) (x : BitVec 64) : BitVec 64 := x ||| ((x <<< 2) &&& stepMask bs)

theorem parityBit_succ (bs : BitVec 64) (odd0 : Bool) (k : Nat) :
    parityBit bs odd0 (k + 1) = (if bs.getLsbD k then !parityBit bs odd0 k else false) := rfl

theorem parityBit_add_two (bs : BitVec 64) (odd0 : Bool) (j : Nat) :
    parityBit bs odd0 (j + 2) =
      (if bs.getLsbD (j + 1) then
        !(if bs.getLsbD j then !parityBit bs odd0 j else false) else false) := by
  rw [show j + 2 = (j + 1) + 1 from rfl, parityBit_succ, parityBit_succ]

theorem stepWord_specRunStarts (bs : BitVec 64) (odd0 : Bool) :
    stepWord bs (specRunStarts bs odd0) = specRunStarts bs odd0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [stepWord, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases hk2 : k < 2
  · rw [decide_eq_true hk, decide_eq_true hk2]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    rw [decide_eq_true (by omega : j + 2 < 64), decide_eq_false (by omega : ¬ j + 2 < 2)]
    simp only [Bool.true_and, Bool.not_false]
    have hj : j < 64 := by omega
    have hj2 : j + 2 < 64 := by omega
    unfold specRunStarts
    rw [show j + 2 - 2 = j from by omega]
    rw [ofLanes_getLsbD (fun i => bs.getLsbD i && !parityBit bs odd0 i) hj,
        ofLanes_getLsbD (fun i => bs.getLsbD i && !parityBit bs odd0 i) hj2]
    unfold stepMask
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    rw [decide_eq_true hj2, decide_eq_false (by omega : ¬ j + 2 < 1)]
    simp only [Bool.true_and, Bool.not_false]
    rw [parityBit_add_two bs odd0 j]
    cases hb0 : bs.getLsbD j <;> cases hb1 : bs.getLsbD (j + 1) <;>
      cases hb2 : bs.getLsbD (j + 2) <;> simp_all

/-- The 64-bit word a caller's carry flag reads as: `flagBytes` read back. -/
def prevBackslashWord (b : Bool) : BitVec 64 := if b then (1 : BitVec 64) else (0 : BitVec 64)

theorem prevBackslashWord_getLsbD_zero (b : Bool) : (prevBackslashWord b).getLsbD 0 = b := by
  cases b <;> simp [prevBackslashWord]

theorem prevBackslashWord_getLsbD_ne (b : Bool) {k : Nat} (hk : k ≠ 0) :
    (prevBackslashWord b).getLsbD k = false := by
  cases b
  · simp [prevBackslashWord, BitVec.getLsbD_zero]
  · change (1#64).getLsbD k = false
    rw [BitVec.getLsbD_one, decide_eq_true (by decide : 0 < 64), Bool.true_and,
      decide_eq_false hk]

theorem oneWord_getLsbD_zero : (1 : BitVec 64).getLsbD 0 = true := by
  change (1#64).getLsbD 0 = true
  rw [BitVec.getLsbD_one, decide_eq_true (by decide : 0 < 64), decide_eq_true rfl,
    Bool.true_and]

theorem oneWord_getLsbD {k : Nat} (hk : k ≠ 0) : (1 : BitVec 64).getLsbD k = false := by
  change (1#64).getLsbD k = false
  rw [BitVec.getLsbD_one, decide_eq_true (by decide : 0 < 64), Bool.true_and,
    decide_eq_false hk]

theorem twoWord_getLsbD (k : Nat) : (2 : BitVec 64).getLsbD k = decide (k = 1) := by
  change (BitVec.ofNat 64 2).getLsbD k = decide (k = 1)
  rw [BitVec.getLsbD_ofNat]
  by_cases hk : k < 64
  · rw [decide_eq_true hk, Bool.true_and]
    have h2 : (2 : Nat) = 2 ^ 1 := rfl
    rw [h2, Nat.testBit_two_pow]
    by_cases h : k = 1
    · subst h
      rfl
    · rw [decide_eq_false h, decide_eq_false (by omega : ¬ 1 = k)]
  · rw [decide_eq_false hk, Bool.false_and, decide_eq_false]
    omega

theorem twoWord_getLsbD_ne {k : Nat} (hk : k ≠ 1) : (2 : BitVec 64).getLsbD k = false := by
  rw [twoWord_getLsbD, decide_eq_false hk]

theorem shiftOne_getLsbD {bs : BitVec 64} {k : Nat} (hk1 : 1 ≤ k) (hk64 : k < 64) :
    ((bs <<< 1).getLsbD k) = bs.getLsbD (k - 1) := by
  rw [BitVec.getLsbD_shiftLeft, decide_eq_true hk64, decide_eq_false (by omega)]
  simp only [Bool.true_and, Bool.not_false]

/-- The body's `%e.0.i` seed: the first lane of each backslash run, corrected at
the block boundary by the carried pair. -/
def escapeSeed (bs : BitVec 64) (prevb prevs : Bool) : BitVec 64 :=
  let aw : BitVec 64 := prevBackslashWord prevb
  let andI := bs &&& ~~~((bs <<< 1) ||| aw)
  let and2 := (bs &&& (1 : BitVec 64)) &&& aw
  if and2 = (0 : BitVec 64) then andI
  else andI ||| (if prevs then (bs &&& (2 : BitVec 64)) else (1 : BitVec 64))

theorem escapeSeed_bit_ge_two {bs : BitVec 64} {prevb prevs : Bool} {k : Nat}
    (hk : 2 ≤ k) (hk64 : k < 64) :
    (escapeSeed bs prevb prevs).getLsbD k = (bs.getLsbD k && !bs.getLsbD (k - 1)) := by
  unfold escapeSeed
  have hshift : ((bs <<< 1).getLsbD k) = bs.getLsbD (k - 1) := shiftOne_getLsbD (by omega) hk64
  have hprev : (prevBackslashWord prevb).getLsbD k = false := prevBackslashWord_getLsbD_ne _ (by omega)
  have handI : (bs &&& ~~~((bs <<< 1) ||| prevBackslashWord prevb)).getLsbD k =
      (bs.getLsbD k && !bs.getLsbD (k - 1)) := by
    rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ hk64, BitVec.getLsbD_or, hshift, hprev]
    simp
  by_cases h0 : ((bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb) = (0 : BitVec 64)
  · rw [if_pos h0]
    exact handI
  · rw [if_neg h0, BitVec.getLsbD_or, handI]
    have hcorr : ((if prevs then (bs &&& (2 : BitVec 64)) else (1 : BitVec 64))).getLsbD k = false := by
      by_cases hp : prevs
      · rw [if_pos hp, BitVec.getLsbD_and, twoWord_getLsbD_ne (by omega)]
        simp
      · rw [if_neg hp]
        exact oneWord_getLsbD (by omega)
    rw [hcorr]
    simp

/-- The `if.then.i` mask has only lane 0 possible. -/
theorem and2_eq_lanes (bs : BitVec 64) (prevb : Bool) :
    (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb =
      ofLanes (fun i : Fin 64 => if i.val = 0 then (bs.getLsbD 0 && prevb) else false) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, ofLanes_getLsbD _ hk]
  by_cases hk0 : k = 0
  · subst hk0
    rw [oneWord_getLsbD_zero, prevBackslashWord_getLsbD_zero]
    simp
  · rw [oneWord_getLsbD hk0, prevBackslashWord_getLsbD_ne prevb hk0]
    simp [hk0]

/-- The `and2` test is zero when its lane-0 test is clear. -/
theorem and2_eq_zero_of (bs : BitVec 64) (prevb : Bool)
    (h : (bs.getLsbD 0 && prevb) = false) :
    (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb = (0 : BitVec 64) := by
  rw [and2_eq_lanes]
  have hf : (fun i : Fin 64 => if i.val = 0 then (bs.getLsbD 0 && prevb) else false)
      = (fun _ : Fin 64 => false) := by
    funext i
    by_cases hi : i.val = 0
    · rw [hi]
      cases hb0 : bs.getLsbD 0 <;> cases hpv : prevb <;> simp_all
    · simp [hi]
  rw [hf]
  simpa using (ofLanes_false (w := 64))

/-- The `and2` test is nonzero when its lane-0 test is set. -/
theorem and2_ne_zero_of (bs : BitVec 64) (prevb : Bool)
    (h : (bs.getLsbD 0 && prevb) = true) :
    (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb ≠ (0 : BitVec 64) := by
  intro hzero
  have h0 := congrArg (fun x => x.getLsbD 0) hzero
  rw [and2_eq_lanes, ofLanes_getLsbD _ (by decide : 0 < 64)] at h0
  simp only [Fin.val_zero, if_pos rfl] at h0
  rw [show (0 : BitVec 64).getLsbD 0 = false from by simp, h] at h0
  simp at h0

theorem andI_lane_zero (bs : BitVec 64) (prevb : Bool) :
    (bs &&& ~~~((bs <<< 1) ||| prevBackslashWord prevb)).getLsbD 0 = (bs.getLsbD 0 && !prevb) := by
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ (by decide : 0 < 64), BitVec.getLsbD_or,
    prevBackslashWord_getLsbD_zero]
  have hsh : (bs <<< 1).getLsbD 0 = false := by
    rw [BitVec.getLsbD_shiftLeft]
    simp
  rw [hsh]
  simp

theorem andI_lane_one (bs : BitVec 64) (prevb : Bool) :
    (bs &&& ~~~((bs <<< 1) ||| prevBackslashWord prevb)).getLsbD 1 = (bs.getLsbD 1 && !bs.getLsbD 0) := by
  rw [BitVec.getLsbD_and, getLsbD_not_of_lt _ (by decide : 1 < 64), BitVec.getLsbD_or,
    shiftOne_getLsbD (by decide : 1 ≤ 1) (by decide : 1 < 64),
    prevBackslashWord_getLsbD_ne prevb (by decide : (1 : Nat) ≠ 0)]
  simp

theorem escapeSeed_lane_zero (bs : BitVec 64) (prevb prevs : Bool) :
    (escapeSeed bs prevb prevs).getLsbD 0 = (bs.getLsbD 0 && !(prevb && prevs)) := by
  unfold escapeSeed
  by_cases hb : bs.getLsbD 0 = true
  · by_cases hp : prevb = true
    · have hne : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb ≠ (0 : BitVec 64) :=
        and2_ne_zero_of bs prevb (by rw [hb, hp]; simp)
      rw [if_neg hne, BitVec.getLsbD_or, andI_lane_zero]
      by_cases hs : prevs
      · rw [if_pos hs, BitVec.getLsbD_and, twoWord_getLsbD_ne (by decide : (0 : Nat) ≠ 1)]
        simp [hb, hp, hs]
      · rw [if_neg hs, oneWord_getLsbD_zero]
        simp [hb, hp, hs]
    · have hp' : prevb = false := by
        cases h : prevb
        · rfl
        · exact absurd h hp
      have hz : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb = (0 : BitVec 64) :=
        and2_eq_zero_of bs prevb (by rw [hb, hp']; simp)
      rw [if_pos hz, andI_lane_zero]
      by_cases hs : prevs <;> simp_all
  · have hb' : bs.getLsbD 0 = false := by
      cases h : bs.getLsbD 0
      · rfl
      · exact absurd h hb
    have hz : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb = (0 : BitVec 64) :=
      and2_eq_zero_of bs prevb (by rw [hb']; simp)
    rw [if_pos hz, andI_lane_zero]
    by_cases hp : prevb <;> by_cases hs : prevs <;> simp_all

theorem escapeSeed_lane_one (bs : BitVec 64) (prevb prevs : Bool) :
    (escapeSeed bs prevb prevs).getLsbD 1 =
      (bs.getLsbD 1 && (!bs.getLsbD 0 || (prevb && prevs))) := by
  unfold escapeSeed
  by_cases hb : bs.getLsbD 0 = true
  · by_cases hp : prevb = true
    · have hne : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb ≠ (0 : BitVec 64) :=
        and2_ne_zero_of bs prevb (by rw [hb, hp]; simp)
      rw [if_neg hne, BitVec.getLsbD_or, andI_lane_one]
      by_cases hs : prevs
      · rw [if_pos hs, BitVec.getLsbD_and, twoWord_getLsbD (1 : Nat)]
        by_cases hb1 : bs.getLsbD 1 <;> simp_all
      · rw [if_neg hs, oneWord_getLsbD (by decide : (1 : Nat) ≠ 0)]
        by_cases hb1 : bs.getLsbD 1 <;> simp_all
    · have hp' : prevb = false := by
        cases h : prevb
        · rfl
        · exact absurd h hp
      have hz : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb = (0 : BitVec 64) :=
        and2_eq_zero_of bs prevb (by rw [hb, hp']; simp)
      rw [if_pos hz, andI_lane_one]
      by_cases hs : prevs <;> by_cases hb1 : bs.getLsbD 1 <;> simp_all
  · have hb' : bs.getLsbD 0 = false := by
      cases h : bs.getLsbD 0
      · rfl
      · exact absurd h hb
    have hz : (bs &&& (1 : BitVec 64)) &&& prevBackslashWord prevb = (0 : BitVec 64) :=
      and2_eq_zero_of bs prevb (by rw [hb']; simp)
    rw [if_pos hz, andI_lane_one]
    by_cases hp : prevb <;> by_cases hs : prevs <;> by_cases hb1 : bs.getLsbD 1 <;>
      simp_all

theorem specRunStarts_getLsbD {bs : BitVec 64} {odd0 : Bool} {k : Nat} (hk : k < 64) :
    (specRunStarts bs odd0).getLsbD k = (bs.getLsbD k && !parityBit bs odd0 k) := by
  unfold specRunStarts
  rw [ofLanes_getLsbD _ hk]

/-- A lane of the fixed point that is not a seed lane is reached from two lanes
below: the parity it reads is the parity two lanes below, so the lane below two
is a run start and the pair mask covers the step. -/
theorem spec_seed_step {bs : BitVec 64} {prevb prevs : Bool} {j : Nat} (hj : j + 2 < 64)
    (hspec : (specRunStarts bs (prevb && prevs)).getLsbD (j + 2) = true) :
    (escapeSeed bs prevb prevs).getLsbD (j + 2) = true ∨
      ((specRunStarts bs (prevb && prevs)).getLsbD j = true ∧ (stepMask bs).getLsbD (j + 2) = true) := by
  have hspec' : (bs.getLsbD (j + 2) &&
      !(if bs.getLsbD (j + 1) then
        !(if bs.getLsbD j then !parityBit bs (prevb && prevs) j else false) else false)) = true := by
    have hs := hspec
    rw [specRunStarts_getLsbD (k := j + 2) (by omega)] at hs
    rw [parityBit_add_two bs (prevb && prevs) j] at hs
    exact hs
  have hstepMask : (stepMask bs).getLsbD (j + 2) = (bs.getLsbD (j + 2) && bs.getLsbD (j + 1)) := by
    unfold stepMask
    rw [BitVec.getLsbD_and, shiftOne_getLsbD (by omega) (by omega),
      show j + 2 - 1 = j + 1 from by omega]
    exact Bool.and_comm _ _
  have hseed : (escapeSeed bs prevb prevs).getLsbD (j + 2) =
      (bs.getLsbD (j + 2) && !bs.getLsbD (j + 1)) := by
    rw [escapeSeed_bit_ge_two (by omega) hj,
      show j + 2 - 1 = j + 1 from by omega]
  rw [hseed, hstepMask,
    specRunStarts_getLsbD (bs := bs) (odd0 := prevb && prevs) (k := j) (by omega)]
  cases hb0 : bs.getLsbD j <;> cases hb1 : bs.getLsbD (j + 1) <;>
    cases hb2 : bs.getLsbD (j + 2) <;> cases hpj : parityBit bs (prevb && prevs) j <;>
    simp_all

/-! ### The doubling closure reaches the run-start word -/

/-- One word is a lane-wise subset of another. -/
def LaneSub (x y : BitVec 64) : Prop := ∀ k, k < 64 → x.getLsbD k = true → y.getLsbD k = true

theorem LaneSub.trans {x y z : BitVec 64} (h1 : LaneSub x y) (h2 : LaneSub y z) : LaneSub x z :=
  fun k hk h => h2 k hk (h1 k hk h)

/-- The doubling step is increasing. -/
theorem stepWord_self (bs x : BitVec 64) : LaneSub x (stepWord bs x) := by
  intro k hk h
  rw [stepWord, BitVec.getLsbD_or, Bool.or_eq_true]
  exact Or.inl h

/-- The doubling step is monotone lane-wise. -/
theorem stepWord_mono {bs x y : BitVec 64} (h : LaneSub x y) : LaneSub (stepWord bs x) (stepWord bs y) := by
  intro k hk hk'
  rw [stepWord, BitVec.getLsbD_or, Bool.or_eq_true] at hk'
  rw [stepWord, BitVec.getLsbD_or, Bool.or_eq_true]
  rcases hk' with h1 | h1
  · exact Or.inl (h k hk h1)
  · right
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft] at h1
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    rw [Bool.and_eq_true] at h1
    obtain ⟨hinner, ha⟩ := h1
    rw [Bool.and_eq_true] at hinner
    obtain ⟨hd2, hx⟩ := hinner
    rw [Bool.and_eq_true] at hd2
    obtain ⟨h64, h2⟩ := hd2
    by_cases hk2 : 2 ≤ k
    · have hy : y.getLsbD (k - 2) = true := h (k - 2) (by omega) hx
      rw [decide_eq_true hk, decide_eq_false (by omega : ¬ k < 2)]
      simp only [Bool.true_and, Bool.not_false]
      rw [hy, ha]
      simp
    · have hlt : decide (k < 2) = true := decide_eq_true (by omega)
      rw [hlt] at h2
      simp at h2

/-- The doubling step adds lane `k` from lane `k - 2`. -/
theorem stepWord_getLsbD {bs x : BitVec 64} {k : Nat} (hk2 : 2 ≤ k) (hk64 : k < 64)
    (hx : x.getLsbD (k - 2) = true) (ha : (stepMask bs).getLsbD k = true) :
    (stepWord bs x).getLsbD k = true := by
  rw [stepWord, BitVec.getLsbD_or, Bool.or_eq_true]
  right
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  rw [decide_eq_true hk64, decide_eq_false (by omega : ¬ k < 2)]
  simp only [Bool.true_and, Bool.not_false]
  rw [hx, ha]
  simp

/-- `n` iterations of the doubling step. -/
def stepN (bs : BitVec 64) : Nat → BitVec 64 → BitVec 64
  | 0, x => x
  | n + 1, x => stepWord bs (stepN bs n x)

theorem stepN_zero (bs : BitVec 64) (x : BitVec 64) : stepN bs 0 x = x := rfl

theorem stepN_succ (bs : BitVec 64) (n : Nat) (x : BitVec 64) :
    stepN bs (n + 1) x = stepWord bs (stepN bs n x) := rfl

theorem specRunStarts_lane_one (bs : BitVec 64) (prevb prevs : Bool) :
    (specRunStarts bs (prevb && prevs)).getLsbD 1 =
      (bs.getLsbD 1 && (!bs.getLsbD 0 || (prevb && prevs))) := by
  rw [specRunStarts_getLsbD (by decide : 1 < 64), parityBit_succ]
  cases bs.getLsbD 0 <;> cases prevb <;> cases prevs <;> simp [parityBit]

theorem specRunStarts_not_parity_one (bs : BitVec 64) (prevb prevs : Bool) :
    Bool.not (parityBit bs (prevb && prevs) 1) =
      (Bool.not (bs.getLsbD 0) || (prevb && prevs)) := by
  rw [parityBit_succ]
  cases bs.getLsbD 0 <;> cases prevb <;> cases prevs <;> simp [parityBit]

/-- The seed's lanes are lanes of the fixed point. -/
theorem seed_subset_spec (bs : BitVec 64) (prevb prevs : Bool) :
    LaneSub (escapeSeed bs prevb prevs) (specRunStarts bs (prevb && prevs)) := by
  intro k hk h
  by_cases hk0 : k = 0
  · subst hk0
    rw [escapeSeed_lane_zero] at h
    rw [specRunStarts_getLsbD (k := 0) (by decide)]
    exact h
  · by_cases hk1 : k = 1
    · subst hk1
      rw [escapeSeed_lane_one] at h
      rw [specRunStarts_getLsbD (k := 1) (by decide), specRunStarts_not_parity_one]
      exact h
    · rw [escapeSeed_bit_ge_two (by omega) hk] at h
      rw [Bool.and_eq_true] at h
      obtain ⟨hbk, hbk1⟩ := h
      rw [specRunStarts_getLsbD hk]
      have hpar : parityBit bs (prevb && prevs) k = false := by
        rw [show k = (k - 1) + 1 from by omega, parityBit_succ]
        rw [show bs.getLsbD (k - 1) = false from by
          cases hh : bs.getLsbD (k - 1)
          · rfl
          · rw [hh] at hbk1; simp at hbk1]
        rfl
      rw [hbk, hpar]
      simp

/-- Every iterate of the seed stays inside the fixed point. -/
theorem stepN_spec_sub (bs : BitVec 64) (prevb prevs : Bool) (n : Nat) :
    LaneSub (stepN bs n (escapeSeed bs prevb prevs)) (specRunStarts bs (prevb && prevs)) := by
  induction n with
  | zero => exact seed_subset_spec bs prevb prevs
  | succ n ih =>
      have h := stepWord_mono (bs := bs) (x := stepN bs n (escapeSeed bs prevb prevs))
        (y := specRunStarts bs (prevb && prevs)) ih
      rw [stepWord_specRunStarts] at h
      exact h

theorem stepN_mono {bs : BitVec 64} {x y : BitVec 64} (h : LaneSub x y) (n : Nat) :
    LaneSub (stepN bs n x) (stepN bs n y) := by
  induction n with
  | zero => exact h
  | succ n ih =>
      rw [stepN_succ, stepN_succ]
      exact stepWord_mono ih

theorem stepN_self_sub (bs : BitVec 64) (x : BitVec 64) (n : Nat) :
    LaneSub x (stepN bs n x) := by
  induction n with
  | zero => intro k hk h; exact h
  | succ n ih =>
      rw [stepN_succ]
      exact LaneSub.trans ih (stepWord_self bs _)

theorem stepN_mono_le_add (bs : BitVec 64) (x : BitVec 64) (n : Nat) :
    ∀ d, LaneSub (stepN bs n x) (stepN bs (n + d) x)
  | 0 => fun k hk h => by simpa using h
  | d + 1 => by
      have hstep : LaneSub (stepN bs (n + d) x) (stepN bs (n + d + 1) x) := by
        rw [stepN_succ]
        exact stepWord_self bs _
      have h := LaneSub.trans (stepN_mono_le_add bs x n d) hstep
      simpa [Nat.add_assoc] using h

theorem stepN_mono_le {bs : BitVec 64} {x : BitVec 64} {n m : Nat} (h : n ≤ m) :
    LaneSub (stepN bs n x) (stepN bs m x) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  exact stepN_mono_le_add bs x n d

/-- Each lane of the fixed point is reached within `k / 2 + 1` steps; a lane
moves by two per iteration, so at most thirty-two steps reach every lane below
sixty-four. -/
theorem spec_reach {bs : BitVec 64} {prevb prevs : Bool} :
    ∀ k, k < 64 →
      (specRunStarts bs (prevb && prevs)).getLsbD k = true →
      (stepN bs (k / 2 + 1) (escapeSeed bs prevb prevs)).getLsbD k = true := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk64 hspec
    by_cases hk0 : k = 0
    · subst hk0
      have hspec0 := hspec
      rw [specRunStarts_getLsbD (k := 0) (by decide)] at hspec0
      have hseed : (escapeSeed bs prevb prevs).getLsbD 0 = true := by
        rw [escapeSeed_lane_zero]
        exact hspec0
      exact stepN_self_sub bs _ 1 0 hk64 hseed
    · by_cases hk1 : k = 1
      · subst hk1
        have hspec1 := hspec
        rw [specRunStarts_getLsbD (k := 1) (by decide)] at hspec1
        have hseed : (escapeSeed bs prevb prevs).getLsbD 1 = true := by
          rw [escapeSeed_lane_one]
          rw [specRunStarts_not_parity_one] at hspec1
          exact hspec1
        exact stepN_self_sub bs _ 1 1 hk64 hseed
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        rcases spec_seed_step hk64 hspec with hseed | ⟨hspecj, ha⟩
        · exact stepN_self_sub bs _ _ _ hk64 hseed
        · have hreach : (stepN bs (j / 2 + 1) (escapeSeed bs prevb prevs)).getLsbD j = true :=
            ih j (by omega) (by omega) hspecj
          have hstep : (stepN bs (j / 2 + 1 + 1) (escapeSeed bs prevb prevs)).getLsbD (j + 2) = true := by
            show (stepWord bs (stepN bs (j / 2 + 1) (escapeSeed bs prevb prevs))).getLsbD (j + 2) = true
            exact stepWord_getLsbD (by omega) hk64 hreach ha
          exact stepN_mono_le (by omega) (j + 2) hk64 hstep

/-- Thirty-two iterations of the doubling step started at the body's seed are the
run-start word of the block. -/
theorem stepN_escapeSeed_specRunStarts (bs : BitVec 64) (prevb prevs : Bool) :
    stepN bs 32 (escapeSeed bs prevb prevs) = specRunStarts bs (prevb && prevs) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hf : (stepN bs 32 (escapeSeed bs prevb prevs)).getLsbD k = true →
      (specRunStarts bs (prevb && prevs)).getLsbD k = true :=
    stepN_spec_sub bs prevb prevs 32 k hk
  have hg : (specRunStarts bs (prevb && prevs)).getLsbD k = true →
      (stepN bs 32 (escapeSeed bs prevb prevs)).getLsbD k = true := by
    intro h
    have h32 : k / 2 + 1 ≤ 32 := by omega
    exact stepN_mono_le h32 k hk (spec_reach k hk h)
  cases h1 : (stepN bs 32 (escapeSeed bs prevb prevs)).getLsbD k <;>
    cases h2 : (specRunStarts bs (prevb && prevs)).getLsbD k <;> simp_all


/-! ### The first fixed iterate is the rule's word

`do.body.i` leaves the loop on `%cmp24.not.i = icmp eq %or23.i, %e.1.i`: the first
iterate of the map that the map fixes.  The thirty-two-iteration equality bounds a
word and does not identify that exit word, and the difference is observable rather
than academic — a two-lane backslash run is already fixed after one iteration, so
most inputs leave the loop long before step thirty-two.  What identifies the exit
word is leastness: a fixed point above the seed contains every lane the rule marks,
so the first one is the rule's own word. -/

/-- **A fixed iterate contains the rule's word.**  By minimality on the first marked
lane it lacks: lane zero and one come from the seed, and a marked lane from two up
is either a seed lane or two above a marked lane, which the map would add — so a
fixed iterate cannot lack a marked lane. -/
theorem spec_sub_of_fixed {bs : BitVec 64} {prevb prevs : Bool} {i : Nat}
    (hfix : stepWord bs (stepN bs i (escapeSeed bs prevb prevs)) =
      stepN bs i (escapeSeed bs prevb prevs)) :
    LaneSub (specRunStarts bs (prevb && prevs)) (stepN bs i (escapeSeed bs prevb prevs)) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro hk64 hspec
    by_cases hk0 : k = 0
    · subst hk0
      have hs0 : (escapeSeed bs prevb prevs).getLsbD 0 = true := by
        rw [escapeSeed_lane_zero]
        rwa [specRunStarts_getLsbD (k := 0) (by decide)] at hspec
      exact stepN_self_sub bs _ i 0 hk64 hs0
    · by_cases hk1 : k = 1
      · subst hk1
        have hspec1 := hspec
        rw [specRunStarts_getLsbD (k := 1) (by decide)] at hspec1
        have hs1 : (escapeSeed bs prevb prevs).getLsbD 1 = true := by
          rw [escapeSeed_lane_one]
          rw [specRunStarts_not_parity_one] at hspec1
          exact hspec1
        exact stepN_self_sub bs _ i 1 hk64 hs1
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
        rcases spec_seed_step (j := j) (by omega) hspec with hseed | ⟨hspecj, ha⟩
        · exact stepN_self_sub bs _ i (j + 2) hk64 hseed
        · have hxj : (stepN bs i (escapeSeed bs prevb prevs)).getLsbD j = true :=
            ih j (by omega) (by omega) hspecj
          have hstep := stepWord_getLsbD (bs := bs)
            (x := stepN bs i (escapeSeed bs prevb prevs)) (k := j + 2)
            (by omega) hk64 hxj ha
          rwa [hfix] at hstep

/-- **The loop's exit word is the rule's word**, at whatever iterate the map first
fixes: the exit test is the map's own fixed-point test, so the word the loop leaves
is the rule's word whether it arrives early or at thirty-two. -/
theorem stepN_fixed_eq_specRunStarts (bs : BitVec 64) (prevb prevs : Bool) (i : Nat)
    (hfix : stepWord bs (stepN bs i (escapeSeed bs prevb prevs)) =
      stepN bs i (escapeSeed bs prevb prevs)) :
    stepN bs i (escapeSeed bs prevb prevs) = specRunStarts bs (prevb && prevs) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hsub := stepN_spec_sub bs prevb prevs i k hk
  have hsup := spec_sub_of_fixed hfix k hk
  cases h1 : (stepN bs i (escapeSeed bs prevb prevs)).getLsbD k <;>
    cases h2 : (specRunStarts bs (prevb && prevs)).getLsbD k <;> simp_all

/-- **The loop terminates within thirty-two iterations**: step thirty-two is a
fixed point, so the first fixed iterate exists and is no later than it.  Together
with `stepN_fixed_eq_specRunStarts` this is the pair the loop's exit needs: an iterate
that is fixed, and the identification of any such iterate with the rule's word. -/
theorem stepN_32_is_fixed (bs : BitVec 64) (prevb prevs : Bool) :
    stepWord bs (stepN bs 32 (escapeSeed bs prevb prevs)) =
      stepN bs 32 (escapeSeed bs prevb prevs) := by
  rw [stepN_escapeSeed_specRunStarts, stepWord_specRunStarts]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.stepWord_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepWord_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_escapeSeed_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepN_escapeSeed_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_fixed_eq_specRunStarts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepN_fixed_eq_specRunStarts

/-- info: 'LeanLLVM.Vellum.stepN_32_is_fixed' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepN_32_is_fixed

end LeanLLVM.Vellum
