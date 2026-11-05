/-
The bit intrinsics of the JSON index kernel, in lane vocabulary.

`tests/v16/ci2.ll`, the stage-1 index kernel, forms its masks with three
instructions the LLVM semantics has no model for: `llvm.x86.bmi.pext.64` twice,
`llvm.x86.bmi.pdep.64` and `llvm.ctlz.i64`.  `Pclmul` gives the fourth
(`llvm.x86.pclmulqdq`) its algebra; this module gives the other three their
lanes.

A word is read lane by lane with `BitVec.getLsbD`, and `ofLanes` packs a lane
function back into a word, so every definition below is a statement about lanes
rather than about a bit-twiddling sequence:

* `pext a m` gathers: lane `j` of the result is `a`'s lane at the `j`-th set
  lane of `m`, and clear at or past `m`'s population count.
* `pdep a m` scatters: lane `i` is `a`'s lane at `i`'s **rank** among `m`'s set
  lanes, and clear where `m` is clear.
* `ctlz x` is the number of clear lanes above `x`'s highest set lane — `w` for
  the zero word — and `trailingRun m` is the length of `m`'s maximal suffix of
  set lanes; `ctlz_not_eq_trailingRun` is `ctlz (~~~m) = trailingRun m`.

## The rank machinery

`setLanes m` is `m`'s set lanes in increasing order, and `rank m i` counts those
below `i`.  The facts a gather/scatter argument needs are all here:

* `setLanes_pairwise` — the lane list is strictly increasing, and
  `setLanes_length_le` — it has at most `w` entries;
* `rank_mono` — the rank does not decrease as the lane rises, and `rank_le` — it
  is bounded by the population count;
* `rank_setLanes_getElem` and `setLanes_getElem?_rank` — the two alignment facts,
  that the `j`-th set lane has rank exactly `j`, and that the rank of a set lane
  indexes that lane.  These are the whole of the correspondence between a mask's
  set lanes and their positions, and both come from the same `List` fact: in a
  strictly increasing list, the entries below the `j`-th entry are exactly its
  predecessors.

The Galois connection is therefore two statements, and only one of them is
unconditional: `pdep_pext` (`pdep (pext a m) m = a &&& m`) holds for every `a`,
because scattering a gather puts back exactly the lanes `m` selects; the round
trip `pext_pdep` (`pext (pdep a m) m = a`) holds when `a` is clear above `m`'s
population count, which is the side condition the gather necessarily has — its
lanes past the count are zero whatever was scattered into `m`.

Nothing here is an axiom, and nothing reaches `BitVec.allOnes`, whose lane lemma
carries `Classical.choice`; the module's footprint is `[propext, Quot.sound]`.
-/
import LeanLLVM.Semantics

namespace LeanLLVM.Vellum.BitLanes

open LeanLLVM

/-! ### Packing lanes

`ofLanes` is the inverse of the lane read: `lanesToNat` packs boolean lanes
little-endian, and `lanesToNat_testBit` reads a packed natural back lane by
lane.  The two together are what makes a definition below a lane statement. -/

/-- Pack a lane function into a word: lane `k` is `f k`. -/
def ofLanes {w : Nat} (f : Fin w → Bool) : BitVec w :=
  BitVec.ofNat w (lanesToNat (List.ofFn (fun i : Fin w => BitVec.ofBool (f i))))

/-- Lane `k` of a packed word is the function's value at `k`. -/
theorem ofLanes_getLsbD {w : Nat} (f : Fin w → Bool) {k : Nat} (hk : k < w) :
    (ofLanes f).getLsbD k = f ⟨k, hk⟩ := by
  unfold ofLanes
  rw [BitVec.getLsbD_ofNat, decide_eq_true hk, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  rw [lanesToNat_testBit, List.getElem?_ofFn, dite_eq_left hk]
  cases h : f ⟨k, hk⟩ <;> simp [BitVec.ofBool]

/-- Two lane functions that agree give the same word. -/
theorem ofLanes_congr {w : Nat} {f g : Fin w → Bool} (h : ∀ i, f i = g i) :
    ofLanes f = ofLanes g := by
  unfold ofLanes
  have hf : (fun i : Fin w => BitVec.ofBool (f i)) = (fun i : Fin w => BitVec.ofBool (g i)) := by
    ext i
    rw [h i]
  rw [hf]

/-- A word whose every lane is clear is zero. -/
theorem ofLanes_false {w : Nat} : ofLanes (fun _ => false) = 0#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [ofLanes_getLsbD _ hk, BitVec.getLsbD_zero]

/-- The lanes below a bound, as a mask. -/
def lowLanes (w n : Nat) : BitVec w := ofLanes (fun i => decide (i.val < n))

/-- Bit `k` of the lanes below `n` is the test `k < n`. -/
theorem lowLanes_getLsbD {w n : Nat} {k : Nat} (hk : k < w) :
    (lowLanes w n).getLsbD k = decide (k < n) :=
  ofLanes_getLsbD (fun i => decide (i.val < n)) hk

/-! ### The all-ones word and complement, lane by lane

`BitVec.getLsbD_allOnes` and `BitVec.getLsbD_not` both carry `Classical.choice` in
their proof terms.  The two lane facts are elementary, so they are proved here
instead, through `BitVec.xor_allOnes` (`x ^^^ allOnes w = ~~~x`) and the numeral
`2 ^ w - 1`; every theorem below then stays at the module's own footprint. -/

/-- Halving an all-ones word drops one lane. -/
private theorem two_pow_sub_one_div_two (n : Nat) : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
  have hval : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
    rw [Nat.two_pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hval, Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (by decide : 1 < 2)]
  omega

/-- A positive-length all-ones word is odd. -/
private theorem two_pow_sub_one_odd (n : Nat) : (2 ^ (n + 1) - 1) % 2 = 1 := by
  have hval : 2 ^ (n + 1) - 1 = 1 + 2 * (2 ^ n - 1) := by
    rw [Nat.two_pow_succ]
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide : 1 < 2)]

/-- Lane `i` of the numeral `2 ^ w - 1` is set while `i < w`. -/
private theorem testBit_two_pow_sub_one_of_lt :
    ∀ {w i : Nat}, i < w → (2 ^ w - 1).testBit i = true
  | 0, _, h => by omega
  | _ + 1, 0, _ => by rw [Nat.testBit_zero, two_pow_sub_one_odd, decide_eq_true rfl]
  | w + 1, i + 1, h => by
    rw [Nat.testBit_succ, two_pow_sub_one_div_two]
    exact testBit_two_pow_sub_one_of_lt (by omega)

/-- Lane `i` of an all-ones word is set while `i < w`, without the choice that
`BitVec.getLsbD_allOnes` carries. -/
theorem allOnes_getLsbD_of_lt {w i : Nat} (h : i < w) :
    (BitVec.allOnes w).getLsbD i = true := by
  have key : (BitVec.allOnes w).getLsbD i = (2 ^ w - 1).testBit i :=
    BitVec.getLsbD_ofNatLT (n := w) (2 ^ w - 1)
      (by have := Nat.two_pow_pos w; omega) i
  rw [key, testBit_two_pow_sub_one_of_lt h]

/-- Lane `i` of a complement is the complement of the lane, without the choice
that `BitVec.getLsbD_not` carries. -/
theorem getLsbD_not_of_lt {w : Nat} (x : BitVec w) {i : Nat} (hi : i < w) :
    (~~~x).getLsbD i = !x.getLsbD i := by
  have h : (~~~x) = (BitVec.allOnes w ^^^ x) := rfl
  rw [h, BitVec.getLsbD_xor, allOnes_getLsbD_of_lt hi]
  cases x.getLsbD i <;> rfl

/-! ### The set lanes and their rank -/

/-- A mask's set lanes, in increasing order. -/
def setLanes {w : Nat} (m : BitVec w) : List Nat :=
  (List.range w).filter (fun i => m.getLsbD i)

/-- A mask's set lanes are exactly the lanes it sets. -/
theorem mem_setLanes {w : Nat} {m : BitVec w} {i : Nat} :
    i ∈ setLanes m ↔ i < w ∧ m.getLsbD i = true := by
  rw [setLanes, List.mem_filter, List.mem_range]

/-- The natural numbers in order are strictly increasing. -/
theorem range_pairwise (n : Nat) : (List.range n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j _ _ hij
  simpa using hij

/-- A mask's set lanes are strictly increasing. -/
theorem setLanes_pairwise {w : Nat} (m : BitVec w) : (setLanes m).Pairwise (· < ·) :=
  List.Pairwise.filter (fun i => m.getLsbD i) (range_pairwise w)

/-- A mask has no more set lanes than it has lanes. -/
theorem setLanes_length_le {w : Nat} (m : BitVec w) : (setLanes m).length ≤ w := by
  have h := List.length_filter_le (fun i => m.getLsbD i) (List.range w)
  simpa [setLanes] using h

/-- Lane `j` of the set-lane list is a set lane. -/
theorem setLanes_getElem_true {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : m.getLsbD (setLanes m)[j] = true :=
  (mem_setLanes.mp (List.getElem_mem hj)).2

/-- Lane `j` of the set-lane list is inside the word. -/
theorem setLanes_getElem_lt {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : (setLanes m)[j] < w :=
  (mem_setLanes.mp (List.getElem_mem hj)).1

/-- The set-lane list read as a lookup. -/
theorem setLanes_getElem?_eq {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : (setLanes m)[j]? = some ((setLanes m)[j]'hj) :=
  List.getElem?_eq_getElem hj

/-- The rank of a lane: how many of the mask's set lanes lie below it. -/
def rank {w : Nat} (m : BitVec w) (i : Nat) : Nat :=
  ((setLanes m).filter (fun k => decide (k < i))).length

/-- The rank never exceeds the population count. -/
theorem rank_le {w : Nat} (m : BitVec w) (i : Nat) : rank m i ≤ (setLanes m).length :=
  List.length_filter_le (fun k => decide (k < i)) (setLanes m)

/-- Filtering by a weaker test is filtering again, so lengths compare. -/
theorem filter_implies_filter {l : List Nat} {p q : Nat → Bool}
    (h : ∀ a, p a = true → q a = true) : l.filter p = (l.filter q).filter p := by
  rw [List.filter_filter]
  exact List.filter_congr (fun a _ => by
    by_cases hp : p a = true
    · rw [hp, h a hp, Bool.and_self]
    · have hp' : p a = false := by simpa using hp
      rw [hp', Bool.false_and])

/-- **The rank is monotone in the lane.** -/
theorem rank_mono {w : Nat} (m : BitVec w) {i j : Nat} (h : i ≤ j) : rank m i ≤ rank m j := by
  have heq : (setLanes m).filter (fun k => decide (k < i))
      = ((setLanes m).filter (fun k => decide (k < j))).filter (fun k => decide (k < i)) :=
    filter_implies_filter (fun a ha => by
      rw [decide_eq_true_eq] at ha ⊢
      omega)
  unfold rank
  rw [heq]
  exact List.length_filter_le _ _

/-- A list all of whose entries fail a test filters to nothing, without the
choice that `List.filter_eq_nil_iff` carries. -/
theorem filter_eq_nil_of_all_false {l : List Nat} {p : Nat → Bool}
    (h : ∀ a, a ∈ l → p a = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    have hpa : ¬ p a = true := by rw [h a (List.mem_cons_self ..)]; simp
    rw [List.filter_cons, ite_eq_right hpa]
    exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- In a strictly increasing list, the entries below the `j`-th entry are its
first `j` entries. -/
theorem filter_lt_getElem_eq_take {l : List Nat} (hs : l.Pairwise (· < ·)) {j : Nat}
    (hj : j < l.length) : l.filter (fun k => decide (k < l[j])) = l.take j := by
  induction l generalizing j with
  | nil => exact absurd hj (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hall, hst⟩ := hs
    cases j with
    | zero =>
      rw [List.take_zero]
      refine filter_eq_nil_of_all_false (fun k hk => ?_)
      rw [List.mem_cons] at hk
      have hka : ¬ k < a := by
        rcases hk with hk | hk
        · rw [hk]; omega
        · have := hall k hk; omega
      rw [show (a :: t)[0] = a from rfl]
      simpa using hka
    | succ j =>
      have hj' : j < t.length := by simpa using hj
      have ha : decide (a < t[j]) = true := decide_eq_true (hall _ (List.getElem_mem hj'))
      rw [show (a :: t)[j + 1] = t[j] from List.getElem_cons_succ .., List.filter_cons,
        ite_eq_left ha, ih hst hj', List.take_succ_cons]

/-- In a strictly increasing list, the number of entries below the `j`-th entry
is `j`. -/
theorem filter_lt_getElem_eq_take_length {l : List Nat} (hs : l.Pairwise (· < ·))
    {j : Nat} (hj : j < l.length) :
    (l.filter (fun k => decide (k < l[j]))).length = j := by
  rw [filter_lt_getElem_eq_take hs hj, List.length_take,
    Nat.min_eq_left (Nat.le_of_lt hj)]

/-- In a strictly increasing list, an entry's own rank indexes it again. -/
theorem filter_lt_getElem?_mem {l : List Nat} (hs : l.Pairwise (· < ·)) {k : Nat}
    (hk : k ∈ l) : l[(l.filter (fun x => decide (x < k))).length]? = some k := by
  induction l with
  | nil => exact absurd hk (by simp)
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hall, hst⟩ := hs
    rw [List.mem_cons] at hk
    rcases hk with hk | hk
    · have hnil : (k :: t).filter (fun x => decide (x < k)) = [] := by
        refine filter_eq_nil_of_all_false (fun x hx => ?_)
        rw [List.mem_cons] at hx
        have hxk : ¬ x < k := by
          rcases hx with hx | hx
          · rw [hx]; omega
          · have hlt := hall x hx
            rw [← hk] at hlt
            omega
        simpa using hxk
      rw [← hk, hnil]
      rfl
    · have hlt : a < k := hall k hk
      rw [List.filter_cons, ite_eq_left (decide_eq_true hlt)]
      have hidx : (a :: t.filter (fun x => decide (x < k))).length
          = (t.filter (fun x => decide (x < k))).length + 1 := rfl
      rw [hidx, List.getElem?_cons_succ]
      exact ih hst hk

/-- **A set lane's rank is its own index.** -/
theorem rank_setLanes_getElem {w : Nat} (m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) : rank m (setLanes m)[j] = j :=
  filter_lt_getElem_eq_take_length (setLanes_pairwise m) hj

/-- **A set lane's rank indexes that lane.** -/
theorem setLanes_getElem?_rank {w : Nat} (m : BitVec w) {i : Nat} (hi : i < w)
    (hm : m.getLsbD i = true) : (setLanes m)[rank m i]? = some i :=
  filter_lt_getElem?_mem (setLanes_pairwise m) (mem_setLanes.mpr ⟨hi, hm⟩)

/-! ### Gather and scatter -/

/-- `pext a m`: lane `j` is `a`'s lane at the `j`-th set lane of `m`, and clear
at or past `m`'s population count.  This is `llvm.x86.bmi.pext.64`. -/
def pext {w : Nat} (a m : BitVec w) : BitVec w :=
  ofLanes (fun j => ((setLanes m)[j.val]?).map a.getLsbD |>.getD false)

/-- The gathered lane, read as a lookup past the mask's population count. -/
theorem pext_getLsbD {w : Nat} (a m : BitVec w) {j : Nat} (hj : j < w) :
    (pext a m).getLsbD j = (((setLanes m)[j]?).map a.getLsbD).getD false := by
  rw [pext, ofLanes_getLsbD _ hj]

/-- The gathered lane, as `a`'s lane at the `j`-th set lane. -/
theorem pext_getLsbD_of_lt {w : Nat} (a m : BitVec w) {j : Nat}
    (hj : j < (setLanes m).length) :
    (pext a m).getLsbD j = a.getLsbD ((setLanes m)[j]'hj) := by
  rw [pext_getLsbD (a := a) (m := m) (j := j)
      (hj := Nat.lt_of_lt_of_le hj (setLanes_length_le m)),
    List.getElem?_eq_getElem hj]
  rfl

/-- A gathered lane past the population count is clear. -/
theorem pext_getLsbD_of_ge {w : Nat} (a m : BitVec w) {j : Nat}
    (hj : (setLanes m).length ≤ j) (hjw : j < w) : (pext a m).getLsbD j = false := by
  rw [pext_getLsbD (a := a) (m := m) (j := j) (hj := hjw), List.getElem?_eq_none hj]
  rfl

/-- `pdep a m`: lane `i` is `a`'s lane at `i`'s rank among `m`'s set lanes, and
clear where `m` is clear.  This is `llvm.x86.bmi.pdep.64`. -/
def pdep {w : Nat} (a m : BitVec w) : BitVec w :=
  ofLanes (fun i => m.getLsbD i.val && a.getLsbD (rank m i.val))

/-- Lane `i` of a scatter. -/
theorem pdep_getLsbD {w : Nat} (a m : BitVec w) {i : Nat} (hi : i < w) :
    (pdep a m).getLsbD i = (m.getLsbD i && a.getLsbD (rank m i)) :=
  ofLanes_getLsbD _ hi

/-- **The Galois connection, unconditional side.**  Scattering a gather into `m`
puts back exactly the lanes `m` selects: `pdep (pext a m) m = a &&& m`. -/
theorem pdep_pext {w : Nat} (a m : BitVec w) : pdep (pext a m) m = a &&& m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [pdep_getLsbD (a := pext a m) (m := m) (i := i) (hi := hi), BitVec.getLsbD_and]
  cases hm : m.getLsbD i with
  | false => simp
  | true =>
    have hrank := setLanes_getElem?_rank m hi hm
    have hlt : rank m i < (setLanes m).length := by
      rcases List.getElem?_eq_some_iff.mp hrank with ⟨h, _⟩
      exact h
    rw [pext_getLsbD_of_lt (a := a) (m := m) (j := rank m i) (hj := hlt)]
    have hidx : (setLanes m)[rank m i]'hlt = i := by
      have := hrank
      rw [List.getElem?_eq_getElem hlt] at this
      exact Option.some.inj this
    rw [hidx]
    simp

/-- **The Galois connection, the round trip.**  Gathering a scatter returns `a`
on the lanes below `m`'s population count, and clears the lanes above it. -/
theorem pext_pdep {w : Nat} (a m : BitVec w) :
    pext (pdep a m) m = a &&& lowLanes w (setLanes m).length := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [pext_getLsbD (a := pdep a m) (m := m) (j := j) (hj := hj), BitVec.getLsbD_and,
    lowLanes_getLsbD hj]
  by_cases hlen : j < (setLanes m).length
  · rw [List.getElem?_eq_getElem hlen, decide_eq_true hlen]
    have hrank := rank_setLanes_getElem m hlen
    have hlt := setLanes_getElem_lt m hlen
    rw [Option.map_some, Option.getD_some,
      pdep_getLsbD (a := a) (m := m) (i := (setLanes m)[j]'hlen) (hi := hlt),
      setLanes_getElem_true m hlen, hrank]
    simp
  · rw [List.getElem?_eq_none (by omega), decide_eq_false (by omega)]
    simp

/-- **The Galois connection, stated as a round trip.**  When `a` is clear above
`m`'s population count, gathering a scatter returns `a` itself. -/
theorem pext_pdep_of_clear {w : Nat} (a m : BitVec w)
    (hclear : ∀ j, (setLanes m).length ≤ j → j < w → a.getLsbD j = false) :
    pext (pdep a m) m = a := by
  rw [pext_pdep]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_and, lowLanes_getLsbD hj]
  by_cases hlen : j < (setLanes m).length
  · rw [decide_eq_true hlen]; simp
  · rw [decide_eq_false (by omega), Bool.and_false, hclear j (by omega) hj]

/-! ### `ctlz` and the trailing run -/

/-- The leading-zero count above lane `i`: walk down from `i`, counting one for
each clear lane and stopping at the first set one. -/
def leadZerosAux {w : Nat} (x : BitVec w) : Nat → Nat
  | 0 => if x.getLsbD 0 then 0 else 1
  | i + 1 => if x.getLsbD (i + 1) then 0 else 1 + leadZerosAux x i

/-- `llvm.ctlz.i64`: the number of clear lanes above the highest set lane, and
the width for the zero word. -/
def ctlz {w : Nat} (x : BitVec w) : Nat :=
  match w with
  | 0 => 0
  | n + 1 => leadZerosAux x n

/-- A word's suffix run of set lanes: lane `n - 1` counted down while set. -/
def suffixRun {w : Nat} (m : BitVec w) : Nat → Nat
  | 0 => 0
  | n + 1 => if m.getLsbD n then suffixRun m n + 1 else 0

/-- The length of the maximal suffix of set lanes. -/
def trailingRun {w : Nat} (m : BitVec w) : Nat := suffixRun m w

/-- A suffix run is no longer than the lanes it counts. -/
theorem suffixRun_le {w : Nat} (m : BitVec w) : ∀ n, suffixRun m n ≤ n
  | 0 => by rw [suffixRun]; omega
  | n + 1 => by
    rw [suffixRun]
    split
    · have := suffixRun_le m n; omega
    · omega

/-- The trailing run is no longer than the word. -/
theorem trailingRun_le {w : Nat} (m : BitVec w) : trailingRun m ≤ w :=
  suffixRun_le m w

/-- The step shared by the two recursions: a clear lane stops the count, a set one
extends it. -/
theorem ite_not_add (b : Bool) (s : Nat) :
    (if (!b) = true then 0 else 1 + s) = (if b = true then s + 1 else 0) := by
  cases b <;> simp <;> omega

/-- **`ctlz` of the complement is the trailing run.**  The clear lanes of `~~~m`
above the highest set lane are exactly `m`'s suffix of set lanes. -/
theorem ctlz_not_eq_trailingRun {w : Nat} (m : BitVec w) : ctlz (~~~m) = trailingRun m := by
  cases w with
  | zero => simp [ctlz, trailingRun, suffixRun]
  | succ w' =>
    have key : ∀ i, i < w' + 1 → leadZerosAux (~~~m) i = suffixRun m (i + 1) := by
      intro i
      induction i with
      | zero =>
        intro _
        rw [leadZerosAux, suffixRun, getLsbD_not_of_lt m (by omega)]
        cases m.getLsbD 0 <;> rfl
      | succ i ih =>
        intro h
        have hnot : (~~~m).getLsbD (i + 1) = !m.getLsbD (i + 1) :=
          getLsbD_not_of_lt m h
        rw [leadZerosAux, suffixRun, hnot, ih (by omega)]
        exact ite_not_add (m.getLsbD (i + 1)) (suffixRun m (i + 1))
    rw [ctlz, trailingRun]
    exact key w' (by omega)

/-- The zero word has no set lane, so every lane is leading. -/
theorem ctlz_zero {w : Nat} : ctlz (0#w) = w := by
  cases w with
  | zero => rfl
  | succ w' =>
    have haux : ∀ i, leadZerosAux (0#(w' + 1)) i = i + 1 := by
      intro i
      induction i with
      | zero => rw [leadZerosAux, BitVec.getLsbD_zero]; rfl
      | succ i ih =>
        rw [leadZerosAux, BitVec.getLsbD_zero, ih]
        show 1 + (i + 1) = i + 1 + 1
        omega
    rw [ctlz, haux]

end LeanLLVM.Vellum.BitLanes
