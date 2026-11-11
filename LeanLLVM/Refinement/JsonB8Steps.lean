/-
The B8 kernel's step corpus.

`JsonEntryIR` pins the two emitted bodies in one text; `JsonEntrySteps` holds
the execution of POS8's block.  This module holds B8's: the slot chain that
clears the least set lane eight times, the partially unrolled tail, and the
statements `entry_b8_refines`, `entry_b8_undefined_of_no_read` and
`entry_pos8_b8_agree` that the block-layer specification asks for.

## Why the slot chain needs its own arithmetic

B8 reads the mask word and, for each slot, writes `base | cttz(c)` where `c` is
the word with the previous set lanes cleared by `c & (c - 1)`.  So the value a
slot holds is a position exactly when the slot is inside the population count,
and the whole words clause rests on one fact: clearing the least set lane `j`
times leaves a word whose set lanes are `w`'s set lanes from index `j` on.  That
fact is proved here (`setLanes_clearLow`), from a Nat-level lemma about
`n &&& (n - 1)`, so the proof never unfolds a 64-lane bit-blast.
-/
import LeanLLVM.Refinement.JsonEntrySteps

namespace LeanLLVM.Refinement.JsonB8Steps

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1MasksIR
  (evalInstr_load evalInstr_binop evalInstr_binopVec evalInstr_icmp evalInstr_zext
   evalInstr_store evalInstr_call evalOperands_cons vecLanes_self)

/-! ### Whether a number has a set bit below a bound -/

/-- `below n i`: whether `n` has a set bit below `i`.  This is the "some set
lane lies below" test the slot chain's `cttz` step needs, stated at the
bit level so that `n &&& (n - 1)` can be reasoned about without naming the
least set lane. -/
def below (n : Nat) : Nat → Bool
  | 0 => false
  | i + 1 => below n i || n.testBit i

theorem below_zero (n : Nat) : below n 0 = false := rfl

theorem below_succ (n i : Nat) : below n (i + 1) = (below n i || n.testBit i) := rfl

/-- `below n i` says exactly that some set bit lies below `i`. -/
theorem below_iff (n : Nat) : ∀ i, below n i = true ↔ ∃ k, k < i ∧ n.testBit k = true
  | 0 => by
      rw [below_zero]
      constructor
      · intro h; exact absurd h (by simp)
      · rintro ⟨k, hk, _⟩; omega
  | i + 1 => by
      rw [below_succ, Bool.or_eq_true, below_iff n i]
      constructor
      · rintro (⟨k, hk, hb⟩ | hb)
        · exact ⟨k, by omega, hb⟩
        · exact ⟨i, by omega, hb⟩
      · rintro ⟨k, hk, hb⟩
        rcases Nat.lt_or_ge k i with h | h
        · exact Or.inl ⟨k, h, hb⟩
        · exact Or.inr (by rw [show i = k from by omega]; exact hb)

theorem below_eq_decide (n i : Nat) :
    below n i = decide (∃ k, k < i ∧ n.testBit k = true) := by
  by_cases h : ∃ k, k < i ∧ n.testBit k = true
  · rw [decide_eq_true h, (below_iff n i).mpr h]
  · rw [decide_eq_false h]
    cases hb : below n i with
    | false => rfl
    | true => exact absurd ((below_iff n i).mp hb) h

theorem testBit_two_mul_zero (m : Nat) : (2 * m).testBit 0 = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : (2 * m) / 2 ^ 0 % 2 = 0 := by
    rw [show (2 : Nat) ^ 0 = 1 from rfl, Nat.div_one]
    omega
  rw [h]
  rfl

theorem testBit_two_mul_succ (m j : Nat) : (2 * m).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

theorem testBit_two_mul_one_zero (m : Nat) : (2 * m + 1).testBit 0 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h : (2 * m + 1) / 2 ^ 0 % 2 = 1 := by
    rw [show (2 : Nat) ^ 0 = 1 from rfl, Nat.div_one]
    omega
  rw [h]
  rfl

theorem testBit_two_mul_one_succ (m j : Nat) : (2 * m + 1).testBit (j + 1) = m.testBit j := by
  rw [Nat.testBit_succ]
  congr 1
  omega

/-- Halving pushes a `below` test one place down. -/
theorem below_two_mul_succ (m j : Nat) : below (2 * m) (j + 1) = below m j := by
  induction j with
  | zero => rw [below_succ, below_zero, testBit_two_mul_zero]; rfl
  | succ j ih => rw [below_succ, ih, testBit_two_mul_succ, below_succ]

/-- An odd number has bit 0 set, so every non-zero `below` test passes. -/
theorem below_two_mul_one_succ (m j : Nat) : below (2 * m + 1) (j + 1) = true := by
  induction j with
  | zero => rw [below_succ, below_zero, testBit_two_mul_one_zero]; rfl
  | succ j ih => rw [below_succ, ih]; rfl

/-! ### `n &&& (n - 1)` clears the least set bit -/

/-- An odd number clears its lowest bit, which is the one it has, so the chain's
first step subtracts one. -/
theorem clr_odd (m : Nat) : (2 * m + 1) &&& (2 * m + 1 - 1) = 2 * m := by
  rw [Nat.add_sub_cancel]
  apply Nat.eq_of_testBit_eq
  intro j
  cases j with
  | zero => rw [Nat.testBit_and, testBit_two_mul_one_zero, testBit_two_mul_zero]; rfl
  | succ j =>
      rw [Nat.testBit_and, testBit_two_mul_one_succ, testBit_two_mul_succ, Bool.and_self]

/-- An even number clears its lowest set bit one place further down, so the chain
commutes with halving. -/
theorem clr_even (k : Nat) (hk : 1 ≤ k) :
    (2 * k) &&& (2 * k - 1) = 2 * (k &&& (k - 1)) := by
  have hsub : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  cases j with
  | zero =>
      rw [hsub, Nat.testBit_and, testBit_two_mul_zero, testBit_two_mul_one_zero,
        testBit_two_mul_zero]
      rfl
  | succ j =>
      rw [hsub, Nat.testBit_and, testBit_two_mul_succ, testBit_two_mul_one_succ,
        testBit_two_mul_succ, Nat.testBit_and]

/-- **Subtracting one and masking clears the least set bit**, at the bit level:
the word keeps exactly its set bits that have a set bit below them. -/
theorem clr_testBit (n i : Nat) :
    (n &&& (n - 1)).testBit i = (n.testBit i && below n i) := by
  induction n using Nat.strongRecOn generalizing i with
  | ind n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [show (0 : Nat) - 1 = 0 from rfl, Nat.zero_and, Nat.zero_testBit]
      rfl
    · have hd := Nat.div_add_mod n 2
      rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
      · -- `n` is even: `n = 2 * (n / 2)` and the chain commutes with halving
        have hn' : n = 2 * (n / 2) := by rw [hpar] at hd; omega
        have hpos : 1 ≤ n / 2 := by omega
        conv => lhs; rw [hn']
        conv => rhs; rw [hn']
        rw [clr_even _ hpos]
        cases i with
        | zero => rw [testBit_two_mul_zero, below_zero]; simp
        | succ j =>
            simp only [testBit_two_mul_succ, below_two_mul_succ, ih (n / 2) (by omega) j]
      · -- `n` is odd: its lowest bit is set, so the search below is satisfied
        have hn' : n = 2 * (n / 2) + 1 := by rw [hpar] at hd; omega
        conv => lhs; rw [hn']
        conv => rhs; rw [hn']
        rw [clr_odd (n / 2)]
        cases i with
        | zero => rw [testBit_two_mul_zero, below_zero, testBit_two_mul_one_zero]; simp
        | succ j =>
            rw [testBit_two_mul_succ, testBit_two_mul_one_succ, below_two_mul_one_succ]
            simp

/-! ### `cttz` as the least set lane -/

/-- The zero word's lanes, stated at the width the bodies use. -/
theorem getLsbD_zero_64 (i : Nat) : (0 : BitVec 64).getLsbD i = false :=
  Nat.zero_testBit i


/-- A set lane lies inside the word. -/
theorem lt_width_of_getLsbD {w i : Nat} {x : BitVec w} (hb : x.getLsbD i = true) : i < w := by
  refine Nat.lt_of_not_le (fun hle => ?_)
  have hlt : x.toNat < 2 ^ i :=
    Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hle)
  have hfalse : x.getLsbD i = false := Nat.testBit_lt_two_pow hlt
  rw [hfalse] at hb
  exact absurd hb (by simp)

/-- A non-zero word has a set lane, so its set-lane list is not empty. -/
theorem setLanes_ne_nil {x : BitVec 64} (hx : x ≠ 0) : setLanes x ≠ [] := by
  intro h
  have hall : ∀ i, x.getLsbD i = false := by
    intro i
    by_cases hbits : x.getLsbD i = true
    · have hmem : i ∈ setLanes x := mem_setLanes.mpr ⟨lt_width_of_getLsbD hbits, hbits⟩
      rw [h] at hmem
      exact absurd hmem (by simp)
    · simpa using hbits
  apply hx
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  rw [hall i, getLsbD_zero_64]

/-- `cttz` is the head of the set-lane list. -/
theorem head?_setLanes {x : BitVec 64} (hx : x ≠ 0) : (setLanes x).head? = some (cttz x) := by
  have hne := setLanes_ne_nil hx
  rw [cttz_eq_head]
  cases hl : (setLanes x).head? with
  | none => exact absurd (List.head?_eq_none_iff.mp hl) hne
  | some a => simp

/-- The head of a strictly increasing list is no larger than any member. -/
theorem head?_le_of_pairwise {l : List Nat} {a k : Nat} (h : l.head? = some a)
    (hs : l.Pairwise (· < ·)) (hk : k ∈ l) : a ≤ k := by
  cases l with
  | nil => simp at h
  | cons b t =>
      rw [List.head?_cons] at h
      obtain rfl := Option.some.inj h
      rcases List.mem_cons.mp hk with rfl | hk
      · exact Nat.le_refl _
      · have := (List.pairwise_cons.mp hs).1 k hk
        omega

theorem cttz_mem {x : BitVec 64} (hx : x ≠ 0) : cttz x ∈ setLanes x := by
  have h := head?_setLanes hx
  rw [List.head?_eq_some_iff] at h
  obtain ⟨ys, hys⟩ := h
  rw [hys]
  exact List.mem_cons_self ..

theorem cttz_le_of_mem {x : BitVec 64} (hx : x ≠ 0) {k : Nat} (hk : k ∈ setLanes x) :
    cttz x ≤ k :=
  head?_le_of_pairwise (head?_setLanes hx) (setLanes_pairwise x) hk

theorem cttz_getLsbD {x : BitVec 64} (hx : x ≠ 0) : x.getLsbD (cttz x) = true :=
  (mem_setLanes.mp (cttz_mem hx)).2

/-- `cttz` is below `i` exactly when a set lane is. -/
theorem cttz_lt_iff {x : BitVec 64} (hx : x ≠ 0) (i : Nat) :
    cttz x < i ↔ ∃ k, k < i ∧ x.getLsbD k = true := by
  constructor
  · intro h
    exact ⟨cttz x, h, cttz_getLsbD hx⟩
  · rintro ⟨k, hk, hb⟩
    have := cttz_le_of_mem hx (mem_setLanes.mpr ⟨lt_width_of_getLsbD hb, hb⟩)
    omega

/-- The `below` test is the `cttz` comparison. -/
theorem below_cttz {x : BitVec 64} (hx : x ≠ 0) (i : Nat) :
    below x.toNat i = decide (cttz x < i) := by
  rw [below_eq_decide]
  have h := cttz_lt_iff hx i
  by_cases hc : cttz x < i
  · rw [decide_eq_true hc, decide_eq_true]
    exact h.mp hc
  · rw [decide_eq_false hc, decide_eq_false]
    intro hex
    exact hc (h.mpr hex)

/-- The rank is positive exactly when a set lane lies below the lane. -/
theorem rank_pos_iff {w : Nat} (m : BitVec w) (i : Nat) :
    0 < rank m i ↔ ∃ k, k < i ∧ m.getLsbD k = true := by
  unfold rank
  rw [List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨k, hk⟩
    rw [List.mem_filter] at hk
    obtain ⟨hmem, hlt⟩ := hk
    exact ⟨k, of_decide_eq_true hlt, (mem_setLanes.mp hmem).2⟩
  · rintro ⟨k, hk, hb⟩
    exact ⟨k, List.mem_filter.mpr ⟨mem_setLanes.mpr ⟨lt_width_of_getLsbD hb, hb⟩,
      decide_eq_true hk⟩⟩

/-- `cttz` below a bound is the rank being positive. -/
theorem cttz_lt_iff_rank {x : BitVec 64} (hx : x ≠ 0) (i : Nat) :
    cttz x < i ↔ 0 < rank x i :=
  (cttz_lt_iff hx i).trans (rank_pos_iff x i).symm

/-- In a strictly increasing list, filtering by "positive rank" drops the head. -/
theorem filter_rank_pos (l : List Nat) (hs : l.Pairwise (· < ·)) :
    l.filter (fun k => decide (0 < (l.filter (fun a => decide (a < k))).length)) = l.tail := by
  cases l with
  | nil => rfl
  | cons a t =>
      rw [List.filter_cons]
      have hnil : (a :: t).filter (fun b => decide (b < a)) = [] := by
        refine filter_eq_nil_of_all_false (fun k hk => ?_)
        rw [List.mem_cons] at hk
        rcases hk with rfl | hk
        · simp
        · have hlt := (List.pairwise_cons.mp hs).1 k hk
          rw [decide_eq_false (by omega)]
      rw [hnil]
      simp only [List.length_nil, Nat.not_lt_zero, decide_false, Bool.false_eq_true,
        ite_false]
      rw [show (a :: t).tail = t from rfl]
      rw [List.filter_eq_self]
      intro k hk
      have hlt : a < k := (List.pairwise_cons.mp hs).1 k hk
      refine decide_eq_true (List.length_pos_iff_exists_mem.mpr ⟨a, ?_⟩)
      exact List.mem_filter.mpr ⟨List.mem_cons_self, decide_eq_true hlt⟩

/-! ### The clearing chain -/

/-- One clearing step, as the kernel emits it: `c + (-1)` then `and c`. -/
def clearStep (c : BitVec 64) : BitVec 64 := (c + (-1)) &&& c

/-- The word the slot chain holds after `j` clearing steps. -/
def clearLow (w : BitVec 64) : Nat → BitVec 64
  | 0 => w
  | j + 1 => clearStep (clearLow w j)

theorem negOne_toNat : (-1 : BitVec 64).toNat = 2 ^ 64 - 1 := by decide

/-- The step's subtraction, read back as a number. -/
theorem toNat_add_neg_one (c : BitVec 64) :
    (c + (-1)).toNat = (c.toNat + 2 ^ 64 - 1) % 2 ^ 64 := by
  rw [BitVec.toNat_add, negOne_toNat]
  rw [show c.toNat + (2 ^ 64 - 1) = c.toNat + 2 ^ 64 - 1 from by
    have := Nat.two_pow_pos 64; omega]

/-- At a non-zero word the step subtracts one, without wrapping. -/
theorem toNat_add_neg_one_of_ne {c : BitVec 64} (hc : c ≠ 0) :
    (c + (-1)).toNat = c.toNat - 1 := by
  have hpos : 0 < c.toNat := by
    rcases Nat.eq_zero_or_pos c.toNat with h | h
    · exact absurd (BitVec.toNat_eq.mpr (by simpa using h) : c = 0) hc
    · exact h
  rw [toNat_add_neg_one]
  rw [show c.toNat + 2 ^ 64 - 1 = (c.toNat - 1) + 2 ^ 64 from by omega]
  rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- **The chain's step, at the word level**: a set lane survives exactly when a
set lane lies below it. -/
theorem clearStep_getLsbD (x : BitVec 64) (i : Nat) :
    (clearStep x).getLsbD i = (x.getLsbD i && decide (cttz x < i)) := by
  by_cases hx : x = 0
  · subst hx
    show (((0 : BitVec 64) + (-1)) &&& 0).getLsbD i
      = ((0 : BitVec 64).getLsbD i && decide (cttz 0 < i))
    rw [BitVec.getLsbD_and, getLsbD_zero_64]
    simp
  · show ((x + (-1)) &&& x).toNat.testBit i = _
    rw [BitVec.toNat_and, Nat.and_comm, toNat_add_neg_one_of_ne hx, clr_testBit,
      below_cttz hx]
    rfl

theorem setLanes_clearStep (x : BitVec 64) :
    setLanes (clearStep x) = (setLanes x).tail := by
  have hfilter : setLanes (clearStep x)
      = (List.range 64).filter (fun i => x.getLsbD i && decide (cttz x < i)) := by
    unfold setLanes
    apply List.filter_congr
    intro i _
    exact clearStep_getLsbD x i
  have hrank : (List.range 64).filter (fun i => x.getLsbD i && decide (cttz x < i))
      = (setLanes x).filter (fun k => decide (0 < rank x k)) := by
    rw [show (List.range 64).filter (fun i => x.getLsbD i && decide (cttz x < i))
        = (List.range 64).filter (fun i => decide (0 < rank x i) && x.getLsbD i) from by
      apply List.filter_congr
      intro i _
      by_cases hb : x.getLsbD i = true
      · rw [hb]
        simp only [Bool.true_and]
        have hxne : x ≠ 0 := by
          intro h0; rw [h0] at hb; simp at hb
        by_cases hc : cttz x < i
        · rw [decide_eq_true hc, decide_eq_true ((cttz_lt_iff_rank hxne i).mp hc)]
          rfl
        · rw [decide_eq_false hc, decide_eq_false (by
            intro hpos; exact hc ((cttz_lt_iff_rank hxne i).mpr hpos))]
          rfl
      · rw [show x.getLsbD i = false from by simpa using hb]
        simp]
    rw [show (List.range 64).filter (fun i => decide (0 < rank x i) && x.getLsbD i)
        = ((List.range 64).filter (fun i => x.getLsbD i)).filter
            (fun k => decide (0 < rank x k)) from by rw [List.filter_filter]]
    rfl
  rw [hfilter, hrank]
  rw [show (setLanes x).filter (fun k => decide (0 < rank x k))
      = (setLanes x).filter
          (fun k => decide (0 < ((setLanes x).filter (fun a => decide (a < k))).length))
      from rfl]
  rw [filter_rank_pos (setLanes x) (setLanes_pairwise x)]

/-- The chain's iterate, as a set-lane list: `j` clearing steps drop `j` lanes. -/
theorem setLanes_clearLow (w : BitVec 64) : ∀ j, setLanes (clearLow w j) = (setLanes w).drop j
  | 0 => rfl
  | j + 1 => by
      rw [clearLow, setLanes_clearStep, setLanes_clearLow w j]
      rw [← List.drop_drop (i := 1) (j := j) (l := setLanes w)]
      cases (setLanes w).drop j with
      | nil => rfl
      | cons a t => rfl

/-- A word with no set lanes is zero. -/
theorem eq_zero_of_setLanes_nil {x : BitVec 64} (h : setLanes x = []) : x = 0 := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i _
  rw [getLsbD_zero_64]
  by_cases hbits : x.getLsbD i = true
  · have hmem : i ∈ setLanes x := mem_setLanes.mpr ⟨lt_width_of_getLsbD hbits, hbits⟩
    rw [h] at hmem
    exact absurd hmem (by simp)
  · simpa using hbits

/-- The chain's population count: `j` clearing steps remove `j` set lanes. -/
theorem ctpop_clearLow (w : BitVec 64) (j : Nat) : ctpop (clearLow w j) = ctpop w - j := by
  rw [ctpop_eq_setLanes_length, ctpop_eq_setLanes_length, setLanes_clearLow, List.length_drop]

/-- The chain's trailing count is the `j`-th set lane. -/
theorem cttz_clearLow (w : BitVec 64) {j : Nat} (hj : j < ctpop w) :
    cttz (clearLow w j) = (setLanes w).getD j 0 := by
  have hlen : j < (setLanes w).length := by
    rwa [ctpop_eq_setLanes_length] at hj
  have hsome : (setLanes w)[j]? = some ((setLanes w)[j]'hlen) :=
    List.getElem?_eq_getElem hlen
  rw [cttz_eq_head, setLanes_clearLow w, List.head?_drop, hsome]
  rw [List.getD_eq_getElem?_getD, hsome]
  rfl

/-! ### The slots the body writes -/

/-- The value slot `j` stores: the block base with the cleared word's least set
lane or'd in, exactly as the emitted `or` writes it. -/
def slotVal (base : Nat) (w : BitVec 64) (j : Nat) : BitVec 32 :=
  BitVec.ofNat 32 base ||| BitVec.ofNat 32 (cttz (clearLow w j))

/-- The lanes a block's word writes: eight fixed slots, and one more for each
set lane past the eighth. -/
def slotCount (w : BitVec 64) : Nat := 8 + ctpop (clearLow w 8)

theorem ofNat32_toNat {x : Nat} (h : x < 2 ^ 32) : (BitVec.ofNat 32 x).toNat = x := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- Two numbers with disjoint low bits add under `lor`. -/
theorem lor_eq_add (base t : Nat) (hb : base % 64 = 0) (ht : t < 64) :
    base ||| t = base + t := by
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  rw [show (64 : Nat) = 2 ^ 6 from by decide]
  exact (Nat.two_pow_add_eq_or_of_lt (show t < 2 ^ 6 from by omega) a).symm

/-- Inside the population count, a slot holds the position it names. -/
theorem slotVal_toNat {w : BitVec 64} {base j : Nat}
    (hb : base % 64 = 0) (hcap : base + 64 < 2 ^ 32) (hj : j < ctpop w) :
    (slotVal base w j).toNat = base + (setLanes w).getD j 0 := by
  have hlen : j < (setLanes w).length := by rwa [ctpop_eq_setLanes_length] at hj
  have ht : (setLanes w).getD j 0 < 64 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    exact setLanes_getElem_lt w hlen
  show ((BitVec.ofNat 32 base) ||| (BitVec.ofNat 32 (cttz (clearLow w j)))).toNat = _
  rw [cttz_clearLow w hj, BitVec.toNat_or,
    ofNat32_toNat (by omega), ofNat32_toNat (by omega)]
  exact lor_eq_add base _ hb ht

/-- A four-byte word's bytes read back as the number they encode. -/
theorem bytesToNat_slot (v : Nat) (h : v < 2 ^ 32) : bytesToNat (natToBytes v 4) = v := by
  rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide, Nat.mod_eq_of_lt h]

/-- The block's memory: lanes `j … j+len-1` written in increasing order, each
four bytes at `o + 4 * k + 4 * (j + t)`.  The length is the recursion's argument
so a loop whose trip count is a variable still unfolds. -/
def b8Lanes (o : Nat) (w : BitVec 64) (base k : Nat) (j : Nat) : Nat → Mem → Mem
  | 0, mem => mem
  | len + 1, mem =>
      writeBytes (b8Lanes o w base k j len mem) (o + 4 * k + 4 * (j + len))
        (natToBytes (slotVal base w (j + len)).toNat 4)

theorem b8Lanes_zero (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    b8Lanes o w base k j 0 mem = mem := rfl

theorem b8Lanes_succ (o : Nat) (w : BitVec 64) (base k j len : Nat) (mem : Mem) :
    b8Lanes o w base k j (len + 1) mem
      = writeBytes (b8Lanes o w base k j len mem) (o + 4 * k + 4 * (j + len))
          (natToBytes (slotVal base w (j + len)).toNat 4) := rfl

/-- Concatenating lane ranges is composing their folds. -/
theorem b8Lanes_split (o : Nat) (w : BitVec 64) (base k j a : Nat) :
    ∀ (b : Nat) (mem : Mem),
      b8Lanes o w base k j (a + b) mem
        = b8Lanes o w base k (j + a) b (b8Lanes o w base k j a mem)
  | 0, mem => rfl
  | b + 1, mem => by
      rw [show a + (b + 1) = (a + b) + 1 from by omega, b8Lanes_succ, b8Lanes_split o w base k j a b,
        b8Lanes_succ, ← Nat.add_assoc]

/-- Reading one lane after the fold sees the write that made it. -/
theorem b8Lanes_lane (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    ∀ (len t : Nat), t < len →
      readBytes (b8Lanes o w base k j len mem) (o + 4 * k + 4 * (j + t)) 4
        = some (natToBytes (slotVal base w (j + t)).toNat 4) := by
  intro len
  induction len with
  | zero =>
      intro t ht
      omega
  | succ m ih =>
      intro t ht
      rw [b8Lanes_succ]
      rcases Nat.lt_or_ge t m with h | h
      · rw [readBytes_writeBytes_below (b8Lanes o w base k j m mem)
          (natToBytes (slotVal base w (j + m)).toNat 4) 4
          (o + 4 * k + 4 * (j + t)) (o + 4 * k + 4 * (j + m)) (by omega)]
        exact ih t h
      · have hte : m = t := by omega
        subst hte
        rw [readBytes_writeBytes_seg (b8Lanes o w base k j m mem)
          (natToBytes (slotVal base w (j + m)).toNat 4) (o + 4 * k + 4 * (j + m))
          (o + 4 * k + 4 * (j + m)) 4 (Nat.le_refl _)
          (by rw [natToBytes_length]; omega)]
        rw [Nat.sub_self, List.drop_zero]
        exact congrArg some (List.take_of_length_le
          (l := natToBytes (slotVal base w (j + m)).toNat 4) (i := 4)
          (by rw [natToBytes_length]; exact Nat.le_refl 4))

/-- The lanes the block wrote, read back in order. -/
theorem b8Lanes_readLanes (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    ∀ len, readLanes32 (b8Lanes o w base k j len mem) (o + 4 * k + 4 * j) len
      = some ((List.range len).map (fun t => (slotVal base w (j + t)).toNat)) := by
  intro len
  induction len with
  | zero => rfl
  | succ n ih =>
      have h1 : readLanes32 (b8Lanes o w base k j (n + 1) mem) (o + 4 * k + 4 * j) n
          = some ((List.range n).map (fun t => (slotVal base w (j + t)).toNat)) := by
        rw [readLanes32_congr (b8Lanes o w base k j n mem) (b8Lanes o w base k j (n + 1) mem)
          (o + 4 * k + 4 * j) n
          (by
            intro t ht
            show readBytes (writeBytes (b8Lanes o w base k j n mem)
              (o + 4 * k + 4 * (j + n)) (natToBytes (slotVal base w (j + n)).toNat 4))
              (o + 4 * k + 4 * j + 4 * t) 4 = _
            rw [readBytes_writeBytes_below (b8Lanes o w base k j n mem)
              (natToBytes (slotVal base w (j + n)).toNat 4) 4
              (o + 4 * k + 4 * j + 4 * t) (o + 4 * k + 4 * (j + n)) (by omega)])]
        exact ih
      have h2 : readLanes32 (b8Lanes o w base k j (n + 1) mem)
          (o + 4 * k + 4 * j + 4 * n) 1 = some [(slotVal base w (j + n)).toNat] := by
        rw [show o + 4 * k + 4 * j + 4 * n = o + 4 * k + 4 * (j + n) from by omega]
        simp only [readLanes32]
        rw [b8Lanes_lane o w base k j mem (n + 1) n (by omega)]
        simp only [Option.bind_some, Option.map_some]
        rw [bytesToNat_slot _ (slotVal base w (j + n)).isLt]
      rw [readLanes32_add (b8Lanes o w base k j (n + 1) mem) n (o + 4 * k + 4 * j)
        ((List.range n).map (fun t => (slotVal base w (j + t)).toNat)) 1
        [(slotVal base w (j + n)).toNat] h1 h2]
      rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- A read outside the fold's span is unchanged. -/
theorem b8Lanes_frame (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    ∀ (len p n : Nat),
      (p + n ≤ o + 4 * k + 4 * j ∨ o + 4 * k + 4 * (j + len) ≤ p) →
      readBytes (b8Lanes o w base k j len mem) p n = readBytes mem p n := by
  intro len
  induction len with
  | zero =>
      intro p n h
      rfl
  | succ m ih =>
      intro p n h
      rw [b8Lanes_succ]
      have hstep : readBytes (writeBytes (b8Lanes o w base k j m mem)
          (o + 4 * k + 4 * (j + m)) (natToBytes (slotVal base w (j + m)).toNat 4)) p n
          = readBytes (b8Lanes o w base k j m mem) p n := by
        rcases h with h | h
        · exact readBytes_writeBytes_below (b8Lanes o w base k j m mem)
            (natToBytes (slotVal base w (j + m)).toNat 4) n p _ (by omega)
        · exact readBytes_writeBytes_above (b8Lanes o w base k j m mem)
            (natToBytes (slotVal base w (j + m)).toNat 4) n p _ (by rw [natToBytes_length]; omega)
      rw [hstep]
      refine ih p n ?_
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)

/-- Reading `n` slots of a list gives the list back. -/
theorem range_getD (l : List Nat) : (List.range l.length).map (fun j => l.getD j 0) = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
      rw [show (List.range t.length).map ((fun j => (a :: t).getD j 0) ∘ Nat.succ)
          = (List.range t.length).map (fun j => t.getD j 0) from by
        apply List.map_congr_left
        intro j _
        simp]
      rw [ih]
      simp

/-- The block's lanes, as the positions they name. -/
theorem b8WordPositions (w : BitVec 64) (base : Nat)
    (hb : base % 64 = 0) (hcap : base + 64 < 2 ^ 32) :
    (List.range (ctpop w)).map (fun j => (slotVal base w j).toNat)
      = (setLanes w).map (fun k => base + k) := by
  rw [show ctpop w = (setLanes w).length from ctpop_eq_setLanes_length w]
  rw [show (List.range (setLanes w).length).map (fun j => (slotVal base w j).toNat)
      = (List.range (setLanes w).length).map (fun j => base + (setLanes w).getD j 0) from by
    apply List.map_congr_left
    intro j hj
    exact slotVal_toNat hb hcap (by
      rw [ctpop_eq_setLanes_length]; exact List.mem_range.mp hj)]
  rw [show (fun j => base + (setLanes w).getD j 0)
      = (fun k => base + k) ∘ (fun j => (setLanes w).getD j 0) from rfl]
  rw [← List.map_map, range_getD]

/-! ### The instruction shapes POS8 does not use -/

/-- `%d = and <w> %a, %b`, at two registers. -/
theorem b8_step_and_reg (env : Env) (s : State) (d a b : String) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr entryCalls (withEnv env s) (.binop d .and w (.reg a) (.reg b)) =
      some (withEnv ((d, .int w (x &&& y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = or <w> %a, %b`, at two registers. -/
theorem b8_step_or_reg (env : Env) (s : State) (d a b : String) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr entryCalls (withEnv env s) (.binop d .or w (.reg a) (.reg b)) =
      some (withEnv ((d, .int w (x ||| y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = icmp ult i64 %src, <c>`. -/
theorem b8_step_icmp_ult_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.icmp d .ult w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (BitVec.ult x c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = call i64 @llvm.cttz.i64(i64 %src, i1 true)`. -/
theorem b8_step_call_cttz (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (flag : BitVec 1) (h : lookupName env src = some (.int 64 x)) :
    evalInstr entryCalls (withEnv env s)
        (.call d (.int 64) "llvm.cttz.i64" [((.int 64), (.reg src)), ((.int 1), (.imm (.int 1 flag)))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (cttz x))) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [((.int 64), (.reg src)), ((.int 1), (.imm (.int 1 flag)))]
      = some [.int 64 x, .int 1 flag] := by
    rw [evalOperands_cons (by exact evalOperand_reg_of env s src (.int 64 x) h)
      (evalOperands_cons (evalOperand_lit_of _ 1 flag) rfl)]
  rw [evalInstr_call ha (entryCalls_cttz x flag s.mem s.next)]
  simp [withEnv, State.bind]

/-- `store i32 %v, ptr %p`: four bytes at the pointer. -/
theorem b8_step_store32 (env : Env) (s : State) (v p : String) (x : BitVec 32) (a : Nat)
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr entryCalls (withEnv env s) (.store (.int 32) (.reg v) (.reg p)) =
      some (withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  rw [evalInstr_store (s := withEnv env s) (vv := .int 32 x)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (hv := evalOperand_reg_of env s v (.int 32 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hs := by
      show (if (32 : Nat) = 32 then some { (withEnv env s) with
        mem := writeBytes (withEnv env s).mem a (natToBytes x.toNat ((32 + 7) / 8)) }
        else none) = _
      rw [if_pos rfl]
      rfl)]

/-- `%d = getelementptr <elem>, ptr %base, i64 <c>`, at an index below `2 ^ 63`. -/
theorem b8_step_gep_imm (env : Env) (s : State) (d base : String) (elem : Ty)
    (a : Nat) (idx : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr entryCalls (withEnv env s) (.gep d elem (.reg base) (.imm (.int 64 idx))) =
      some (withEnv ((d, .ptr (a + idx.toNat * elem.sizeBytes)) :: env) s) := by
  have ho := evalOperand_lit_of (withEnv env s) 64 idx
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb) (ho := ho)
    (hpos := by simpa using hpos)]
  simp only [withEnv, State.bind, BitVec.signExtend_eq]

/-! ### The jump chain

The tail's trip count depends on the mask word, so a block's run is a chain whose
length is a variable.  `Jumps` records such a chain: every step is a jump, and
the count is carried symbolically, which is what lets a loop's iteration be
stated at `8 * t` without unfolding a fold at that index. -/

inductive Jumps (f : Function) : Nat → State → State → Prop where
  | zero (s : State) : Jumps f 0 s s
  | succ {n : Nat} {s s' s'' : State} :
      step entryCalls f s = .jump s' → Jumps f n s' s'' → Jumps f (n + 1) s s''

/-- Chains compose. -/
theorem Jumps.comp {f : Function} :
    ∀ {a : Nat} {s t u : State}, Jumps f a s t → Jumps f b t u → Jumps f (a + b) s u
  | 0, s, t, u, h1, h2 => by
      cases h1 with
      | zero => simpa using h2
  | a + 1, s, t, u, h1, h2 => by
      cases h1 with
      | succ hstep hrest =>
          rw [show a + 1 + b = (a + b) + 1 from by omega]
          exact Jumps.succ hstep (Jumps.comp hrest h2)

/-- A chain of jumps is a `runFuel` prefix. -/
theorem runFuel_of_Jumps {f : Function} {m : Nat} :
    ∀ {n : Nat} {s s' : State}, Jumps f n s s' →
      runFuel entryCalls (n + m) f s = runFuel entryCalls m f s'
  | 0, s, s', h => by
      cases h with
      | zero => rw [Nat.zero_add]
  | n + 1, s, s', h => by
      cases h with
      | succ hstep hrest =>
          rw [show n + 1 + m = (n + m) + 1 from by omega]
          rw [runFuel]
          rw [hstep]
          exact runFuel_of_Jumps hrest

theorem Jumps.one {f : Function} {s s' : State} (h : step entryCalls f s = .jump s') :
    Jumps f 1 s s' := by
  have := Jumps.succ (n := 0) h (Jumps.zero s')
  simpa using this

/-! ### One lane of the chain -/

/-- `cttz` never exceeds its word's width. -/
theorem cttz_le {w : Nat} (x : BitVec w) : cttz x ≤ w := by
  rw [cttz_eq_head]
  cases hl : (setLanes x).head? with
  | none => exact Nat.le_refl w
  | some a =>
      rw [show ((some a : Option Nat)).getD w = a from rfl]
      obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hl
      have hmem : a ∈ setLanes x := by rw [hys]; exact List.mem_cons_self
      exact Nat.le_of_lt (mem_setLanes.mp hmem).1

/-- The slot's trailing count, truncated to the lane width the body stores. -/
theorem trunc_cttz (x : BitVec 64) :
    BitVec.ofNat 32 ((BitVec.ofNat 64 (cttz x)).toNat % 2 ^ 32) = BitVec.ofNat 32 (cttz x) := by
  rw [toNat_ofNat64 _ (by have := cttz_le x; omega),
    Nat.mod_eq_of_lt (by have := cttz_le x; omega)]

/-- The `if.end` block: eight fixed slots, then the test that decides whether the
tail runs.  The eight stores are unconditional, which is why a block's last
written lane for a short word is `k + 7`. -/
theorem b8Kernel_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i)) :
    ∃ env', denoteCode entryCalls b8Kernel.instrs (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k 0 8 s.mem }) ∧
      lookupName env' "%1" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) ∧
      lookupName env' "%and31.i" = some (.int 64 (clearLow w 7)) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%add.ptr" = some (.ptr (o + 4 * k)) ∧
      lookupName env' "%cmp.i"
        = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9)))) := by
  refine ⟨?env', ?hrun, ?h1', ?hand', ?hconv', ?hptr', ?hcmp⟩
  case hrun =>
    simp only [b8Kernel, reg, lit]
    -- the block's base
    ent_step (step_add_reg _ _ "%add" "%i.010" "%blk0" 64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 blk0) (by ent_auto) (by ent_auto))
    ent_step (step_trunc _ _ "%add.tr" "%add" 64 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0) (by ent_auto))
    ent_step (step_shl_imm _ _ "%conv" "%add.tr" 32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32)) (BitVec.ofInt 32 6) (by ent_auto))
    rw [show (BitVec.ofInt 32 6).toNat = 6 from by decide, hconv]
    -- the output pointer and the counts
    ent_step (step_gep64 _ _ "%add.ptr" "%out" "%k.addr.011" (.int 32) o (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 k (by omega)]; omega))
    rw [show o + (BitVec.ofNat 64 k).toNat * (Ty.int 32).sizeBytes = o + 4 * k from by
      rw [toNat_ofNat64 k (by omega), show (Ty.int 32).sizeBytes = 4 from rfl]; omega]
    ent_step (step_call_ctpop64 _ _ "%1" "%0" w (by ent_auto))
    ent_step (b8_step_call_cttz _ _ "%2" "%0" w (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast1.i" "%2" 64 32 (BitVec.ofNat 64 (cttz w)) (by ent_auto))
    rw [trunc_cttz w]
    -- slot 0
    ent_step (b8_step_or_reg _ _ "%add.i" "%conv" "%cast1.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz w)) (by ent_auto) (by ent_auto))
    ent_step (b8_step_store32 _ _ "%add.i" "%add.ptr" (slotVal (posBase blk0 i) w 0) (o + 4 * k + 4 * 0) (by ent_auto) (by ent_auto))
    -- slot 1
    ent_step (step_add_imm _ _ "%sub.i" "%0" 64 (w) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and.i" "%sub.i" "%0" 64 (w + (-1)) (w) (by ent_auto) (by ent_auto))
    rw [show (w + (-1)) &&& (w) = clearLow w 1 from rfl]
    ent_step (b8_step_call_cttz _ _ "%3" "%and.i" (clearLow w 1) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast2.i" "%3" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 1))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add3.i" "%conv" "%cast2.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 1))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx4.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 4) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 4).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 1) from by
      simp [show (BitVec.ofInt 64 4).toNat = 4 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add3.i" "%arrayidx4.i" (slotVal (posBase blk0 i) w 1) (o + 4 * k + 4 * (0 + 1)) (by ent_auto) (by ent_auto))
    -- slot 2
    ent_step (step_add_imm _ _ "%sub5.i" "%and.i" 64 (clearLow w 1) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and6.i" "%sub5.i" "%and.i" 64 (clearLow w 1 + (-1)) (clearLow w 1) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 1 + (-1)) &&& (clearLow w 1) = clearLow w 2 from rfl]
    ent_step (b8_step_call_cttz _ _ "%4" "%and6.i" (clearLow w 2) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast7.i" "%4" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 2))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add8.i" "%conv" "%cast7.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 2))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx9.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 8) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 8).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 2) from by
      simp [show (BitVec.ofInt 64 8).toNat = 8 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add8.i" "%arrayidx9.i" (slotVal (posBase blk0 i) w 2) (o + 4 * k + 4 * (0 + 2)) (by ent_auto) (by ent_auto))
    -- slot 3
    ent_step (step_add_imm _ _ "%sub10.i" "%and6.i" 64 (clearLow w 2) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and11.i" "%sub10.i" "%and6.i" 64 (clearLow w 2 + (-1)) (clearLow w 2) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 2 + (-1)) &&& (clearLow w 2) = clearLow w 3 from rfl]
    ent_step (b8_step_call_cttz _ _ "%5" "%and11.i" (clearLow w 3) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast12.i" "%5" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 3))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add13.i" "%conv" "%cast12.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 3))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx14.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 12) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 12).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 3) from by
      simp [show (BitVec.ofInt 64 12).toNat = 12 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add13.i" "%arrayidx14.i" (slotVal (posBase blk0 i) w 3) (o + 4 * k + 4 * (0 + 3)) (by ent_auto) (by ent_auto))
    -- slot 4
    ent_step (step_add_imm _ _ "%sub15.i" "%and11.i" 64 (clearLow w 3) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and16.i" "%sub15.i" "%and11.i" 64 (clearLow w 3 + (-1)) (clearLow w 3) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 3 + (-1)) &&& (clearLow w 3) = clearLow w 4 from rfl]
    ent_step (b8_step_call_cttz _ _ "%6" "%and16.i" (clearLow w 4) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast17.i" "%6" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 4))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add18.i" "%conv" "%cast17.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 4))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx19.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 16) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 16).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 4) from by
      simp [show (BitVec.ofInt 64 16).toNat = 16 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add18.i" "%arrayidx19.i" (slotVal (posBase blk0 i) w 4) (o + 4 * k + 4 * (0 + 4)) (by ent_auto) (by ent_auto))
    -- slot 5
    ent_step (step_add_imm _ _ "%sub20.i" "%and16.i" 64 (clearLow w 4) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and21.i" "%sub20.i" "%and16.i" 64 (clearLow w 4 + (-1)) (clearLow w 4) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 4 + (-1)) &&& (clearLow w 4) = clearLow w 5 from rfl]
    ent_step (b8_step_call_cttz _ _ "%7" "%and21.i" (clearLow w 5) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast22.i" "%7" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 5))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add23.i" "%conv" "%cast22.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 5))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx24.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 20) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 20).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 5) from by
      simp [show (BitVec.ofInt 64 20).toNat = 20 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add23.i" "%arrayidx24.i" (slotVal (posBase blk0 i) w 5) (o + 4 * k + 4 * (0 + 5)) (by ent_auto) (by ent_auto))
    -- slot 6
    ent_step (step_add_imm _ _ "%sub25.i" "%and21.i" 64 (clearLow w 5) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and26.i" "%sub25.i" "%and21.i" 64 (clearLow w 5 + (-1)) (clearLow w 5) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 5 + (-1)) &&& (clearLow w 5) = clearLow w 6 from rfl]
    ent_step (b8_step_call_cttz _ _ "%8" "%and26.i" (clearLow w 6) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast27.i" "%8" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 6))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add28.i" "%conv" "%cast27.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 6))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx29.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 24) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 24).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 6) from by
      simp [show (BitVec.ofInt 64 24).toNat = 24 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add28.i" "%arrayidx29.i" (slotVal (posBase blk0 i) w 6) (o + 4 * k + 4 * (0 + 6)) (by ent_auto) (by ent_auto))
    -- slot 7
    ent_step (step_add_imm _ _ "%sub30.i" "%and26.i" 64 (clearLow w 6) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and31.i" "%sub30.i" "%and26.i" 64 (clearLow w 6 + (-1)) (clearLow w 6) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 6 + (-1)) &&& (clearLow w 6) = clearLow w 7 from rfl]
    ent_step (b8_step_call_cttz _ _ "%9" "%and31.i" (clearLow w 7) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast32.i" "%9" 64 32 (BitVec.ofNat 64 (cttz (clearLow w 7))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add33.i" "%conv" "%cast32.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w 7))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%arrayidx34.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 28) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 28).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 4 * (0 + 7) from by
      simp [show (BitVec.ofInt 64 28).toNat = 28 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (b8_step_store32 _ _ "%add33.i" "%arrayidx34.i" (slotVal (posBase blk0 i) w 7) (o + 4 * k + 4 * (0 + 7)) (by ent_auto) (by ent_auto))
    -- the test the block branches on
    ent_step (b8_step_icmp_ult_imm _ _ "%cmp.i" "%1" 64 (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case h1' => ent_auto
  case hand' => ent_auto
  case hconv' => ent_auto
  case hptr' => ent_auto
  case hcmp => ent_auto
/-! ### The tail's blocks -/

theorem findBlock_b8Kernel :
    entryB8Function.findBlock "if.end" = some b8Kernel := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8TailGuard :
    entryB8Function.findBlock "if.end39.i" = some b8TailGuard := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8TailPreheader :
    entryB8Function.findBlock "while.body.preheader.i" = some b8TailPreheader := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8TailUnrolled :
    entryB8Function.findBlock "while.body.preheader.i.new" = some b8TailUnrolled := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8TailLoop :
    entryB8Function.findBlock "while.body.i" = some b8TailLoop := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8RemainderGuard :
    entryB8Function.findBlock "s1f_ke_b8.exit.loopexit.unr-lcssa" = some b8TailRemainderGuard := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8Remainder :
    entryB8Function.findBlock "while.body.i.epil" = some b8TailRemainder := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8Join :
    entryB8Function.findBlock "s1f_ke_b8.exit" = some b8Join := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem b8_step_of (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : entryB8Function.findBlock name = some b)
    (hbody : denoteCode entryCalls b.instrs s = some s') :
    step entryCalls entryB8Function s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

/-- The incoming lists of the tail's three phis. -/
def b8IncomingC : List (String × Operand) :=
  [("while.body.preheader.i.new", reg "%and36.i"), ("while.body.i", reg "%and44.i.7")]

def b8IncomingO : List (String × Operand) :=
  [("while.body.preheader.i.new", reg "%add.ptr.i"), ("while.body.i", reg "%incdec.ptr.i.7")]

def b8IncomingN : List (String × Operand) :=
  [("while.body.preheader.i.new", lit 64 0), ("while.body.i", reg "%niter.next.7")]

def b8IncomingCu : List (String × Operand) :=
  [("while.body.preheader.i", reg "%and36.i"), ("while.body.i", reg "%and44.i.7")]

def b8IncomingOu : List (String × Operand) :=
  [("while.body.preheader.i", reg "%add.ptr.i"), ("while.body.i", reg "%incdec.ptr.i.7")]

def b8IncomingCe : List (String × Operand) :=
  [("while.body.i.epil", reg "%and44.i.epil"), ("s1f_ke_b8.exit.loopexit.unr-lcssa", reg "%c.096.i.unr")]

def b8IncomingOe : List (String × Operand) :=
  [("while.body.i.epil", reg "%incdec.ptr.i.epil"), ("s1f_ke_b8.exit.loopexit.unr-lcssa", reg "%o.addr.095.i.unr")]

def b8IncomingIe : List (String × Operand) :=
  [("while.body.i.epil", reg "%epil.iter.next"), ("s1f_ke_b8.exit.loopexit.unr-lcssa", lit 64 0)]

def b8IncomingR : List (String × Operand) :=
  [("if.end", reg "%1"), ("if.end39.i", lit 64 8), ("while.body.i.epil", reg "%11"),
   ("s1f_ke_b8.exit.loopexit.unr-lcssa", reg "%11")]

/-! ### The tail's blocks -/

/-- A long word's tail count is its population count. -/
theorem b8_tail_count (w : BitVec 64) (hpop : 9 ≤ ctpop w) :
    BitVec.ofNat 64 (ctpop (clearLow w 8)) + BitVec.ofNat 64 8 = BitVec.ofNat 64 (ctpop w) := by
  have hsum : ctpop (clearLow w 8) + 8 = ctpop w := by
    have h := ctpop_clearLow w 8
    omega
  have hb : ctpop (clearLow w 8) + 8 < 2 ^ 64 := by
    have := ctpop_le w
    omega
  rw [ofNat64_add_ofNat _ _ hb, hsum]

/-- The guard before the unrolled loop.  It is reached only when the word has more
than eight set lanes, so the word it clears is non-zero and the edge straight to
the join is not taken. -/
theorem b8TailGuard_run (env : Env) (s : State) (w : BitVec 64)
    (hand : lookupName env "%and31.i" = some (.int 64 (clearLow w 7))) :
    ∃ env', denoteCode entryCalls b8TailGuard.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))) ∧
      lookupName env' "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) + BitVec.ofNat 64 8)) ∧
      lookupName env' "%and36.i" = some (.int 64 (clearLow w 8)) ∧
      lookupName env' "%12" = some (.int 1 (BitVec.ofBool (clearLow w 8 = 0))) := by
  refine ⟨?env', ?hrun, ?h10, ?h11, ?hand36, ?h12⟩
  case hrun =>
    simp only [b8TailGuard, reg, lit]
    ent_step (step_add_imm _ _ "%sub35.i" "%and31.i" 64 (clearLow w 7) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and36.i" "%sub35.i" "%and31.i" 64 (clearLow w 7 + (-1)) (clearLow w 7) (by ent_auto) (by ent_auto))
    rw [show (clearLow w 7 + (-1)) &&& (clearLow w 7) = clearLow w 8 from rfl]
    ent_step (step_call_ctpop64 _ _ "%10" "%and36.i" (clearLow w 8) (by ent_auto))
    ent_step (step_add_imm _ _ "%11" "%10" 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8) (by ent_auto))
    rw [show BitVec.ofInt 64 8 = BitVec.ofNat 64 8 from by decide]
    ent_step (step_icmp_eq_imm _ _ "%12" "%and36.i" 64 (clearLow w 8) (BitVec.ofInt 64 0) (by ent_auto))
    rw [ofInt64_zero]
    simp only [denoteCode, Option.bind]
    rfl
  case h10 => ent_auto
  case h11 => ent_auto
  case hand36 => ent_auto
  case h12 => ent_auto

theorem b8TailGuard_step (env : Env) (s : State) (w : BitVec 64)
    (hpc : s.pc = "if.end39.i")
    (hand : lookupName env "%and31.i" = some (.int 64 (clearLow w 7)))
    (hpop : 9 ≤ ctpop w) :
    ∃ env', step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "while.body.preheader.i", pre := some "if.end39.i" }) ∧
      lookupName env' "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))) ∧
      lookupName env' "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) ∧
      lookupName env' "%and36.i" = some (.int 64 (clearLow w 8)) ∧
      lookupName env' "%12" = some (.int 1 0) := by
  obtain ⟨env', hbody, h10, h11, hand36, h12⟩ := b8TailGuard_run env s w hand
  have hne : clearLow w 8 ≠ 0 := by
    intro h0
    have h1 : ctpop (clearLow w 8) = 0 := by rw [h0, ctpop_zero64]
    rw [ctpop_clearLow] at h1
    omega
  have h11' : lookupName env' "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) := by
    rw [h11, b8_tail_count w hpop]
  have h12' : lookupName env' "%12" = some (.int 1 0) := by
    rw [h12]
    rw [show BitVec.ofBool (clearLow w 8 = 0) = (0 : BitVec 1) from by
      rw [show decide (clearLow w 8 = 0) = false from decide_eq_false hne]; rfl]
  refine ⟨env', ?_, h10, h11', hand36, h12'⟩
  rw [b8_step_of (withEnv env s) "if.end39.i" b8TailGuard (withEnv env' s) hpc
    findBlock_b8TailGuard hbody]
  show execTerm (withEnv env' s)
    (.condbr (.reg "%12") "s1f_ke_b8.exit" "while.body.preheader.i")
    = .jump (withEnv env' { s with pc := "while.body.preheader.i", pre := some "if.end39.i" })
  rw [execTerm_condbr_false (c := .reg "%12") (t := "s1f_ke_b8.exit")
    (f := "while.body.preheader.i") (evalOperand_reg_of env' s "%12" (.int 1 0) h12') rfl]
  rw [show (withEnv env' s).pc = "if.end39.i" from hpc]
  rfl

/-- The preheader, when the epilogue's counter is below eight: straight to the
join's predecessor. -/
theorem b8TailPreheader_run (env : Env) (s : State) (w : BitVec 64) (k o : Nat)
    (ptr : BitVec 1)
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))))) :
    ∃ env', denoteCode entryCalls b8TailPreheader.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * k + 32)) ∧
      lookupName env' "%xtraiter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 7)) ∧
      lookupName env' "%13" = some (.int 1 (BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8)))) := by
  refine ⟨?env', ?hrun, ?hptr', ?hxtra, ?h13⟩
  case hrun =>
    simp only [b8TailPreheader, reg, lit]
    ent_step (b8_step_gep_imm _ _ "%add.ptr.i" "%add.ptr" (.int 8) (o + 4 * k) (BitVec.ofInt 64 32) (by ent_auto) (by decide))
    rw [show (o + 4 * k) + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes = o + 4 * k + 32 from by
      simp [show (BitVec.ofInt 64 32).toNat = 32 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]]
    ent_step (step_and_imm _ _ "%xtraiter" "%10" 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 7) (by ent_auto))
    ent_step (b8_step_icmp_ult_imm _ _ "%13" "%10" 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hptr' => ent_auto
  case hxtra => ent_auto
  case h13 => ent_auto

theorem b8TailPreheader_step (env : Env) (s : State) (w : BitVec 64) (k o : Nat)
    (hpc : s.pc = "while.body.preheader.i")
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))))
    (hlt : BitVec.ult (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8) = true) :
    ∃ env', step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := ("s1f_ke_b8.exit.loopexit.unr-lcssa"), pre := (some "while.body.preheader.i") }) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * k + 32)) ∧
      lookupName env' "%xtraiter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 7)) ∧
      lookupName env' "%13" = some (.int 1 1) := by
  obtain ⟨env', hbody, hptr', hxtra, h13⟩ := b8TailPreheader_run env s w k o 1 hptr h10
  have h13' : lookupName env' "%13" = some (.int 1 1) := by
    rw [h13, show BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8)) = (1 : BitVec 1) from by rw [hlt]; rfl]
  refine ⟨env', ?_, hptr', hxtra, h13'⟩
  rw [b8_step_of (withEnv env s) "while.body.preheader.i" b8TailPreheader (withEnv env' s) hpc
    findBlock_b8TailPreheader hbody]
  show execTerm (withEnv env' s)
    (.condbr (.reg "%13") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.preheader.i.new")
    = .jump (withEnv env' { s with pc := ("s1f_ke_b8.exit.loopexit.unr-lcssa"), pre := (some "while.body.preheader.i") })
  rw [execTerm_condbr_true (c := .reg "%13") (t := "s1f_ke_b8.exit.loopexit.unr-lcssa")
    (f := "while.body.preheader.i.new")
    (evalOperand_reg_of env' s "%13" (.int 1 1) h13') rfl]
  rw [show (withEnv env' s).pc = "while.body.preheader.i" from hpc]
  rfl

theorem b8TailPreheader_step_long (env : Env) (s : State) (w : BitVec 64) (k o : Nat)
    (hpc : s.pc = "while.body.preheader.i")
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))))
    (hge : BitVec.ult (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8) = false) :
    ∃ env', step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := ("while.body.preheader.i.new"), pre := (some "while.body.preheader.i") }) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * k + 32)) ∧
      lookupName env' "%xtraiter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 7)) ∧
      lookupName env' "%13" = some (.int 1 0) := by
  obtain ⟨env', hbody, hptr', hxtra, h13⟩ := b8TailPreheader_run env s w k o 0 hptr h10
  have h13' : lookupName env' "%13" = some (.int 1 0) := by
    rw [h13, show BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 8)) = (0 : BitVec 1) from by rw [hge]; rfl]
  refine ⟨env', ?_, hptr', hxtra, h13'⟩
  rw [b8_step_of (withEnv env s) "while.body.preheader.i" b8TailPreheader (withEnv env' s) hpc
    findBlock_b8TailPreheader hbody]
  show execTerm (withEnv env' s)
    (.condbr (.reg "%13") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.preheader.i.new")
    = .jump (withEnv env' { s with pc := ("while.body.preheader.i.new"), pre := (some "while.body.preheader.i") })
  rw [execTerm_condbr_false (c := .reg "%13") (t := "s1f_ke_b8.exit.loopexit.unr-lcssa")
    (f := "while.body.preheader.i.new")
    (evalOperand_reg_of env' s "%13" (.int 1 0) h13') rfl]
  rw [show (withEnv env' s).pc = "while.body.preheader.i" from hpc]
  rfl

/-- The unrolled loop's preheader. -/
theorem b8TailUnrolled_run (env : Env) (s : State) (w : BitVec 64)
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))))) :
    ∃ env', denoteCode entryCalls b8TailUnrolled.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
  refine ⟨?env', ?hrun, ?hu⟩
  case hrun =>
    simp only [b8TailUnrolled, reg, lit]
    ent_step (step_and_imm _ _ "%unroll_iter" "%10" 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))) (BitVec.ofInt 64 56) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hu => ent_auto

theorem b8TailUnrolled_step (env : Env) (s : State) (w : BitVec 64)
    (hpc : s.pc = "while.body.preheader.i.new")
    (h10 : lookupName env "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8))))) :
    ∃ env', step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "while.body.i", pre := some "while.body.preheader.i.new" }) ∧
      lookupName env' "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
  obtain ⟨env', hbody, hu⟩ := b8TailUnrolled_run env s w h10
  refine ⟨env', ?_, hu⟩
  rw [b8_step_of (withEnv env s) "while.body.preheader.i.new" b8TailUnrolled (withEnv env' s) hpc
    findBlock_b8TailUnrolled hbody]
  show execTerm (withEnv env' s) (.br "while.body.i")
    = .jump (withEnv env' { s with pc := "while.body.i", pre := some "while.body.preheader.i.new" })
  rw [execTerm_br]
  rw [show (withEnv env' s).pc = "while.body.preheader.i.new" from hpc]
  rfl

/-- Clearing `j` then `i` lanes is clearing `j + i`. -/
theorem clearLow_add (w : BitVec 64) (j : Nat) : ∀ i, clearLow (clearLow w j) i = clearLow w (j + i)
  | 0 => by rw [Nat.add_zero]; rfl
  | i + 1 => by
      show clearStep (clearLow (clearLow w j) i) = clearLow w (j + (i + 1))
      rw [clearLow_add w j i,
        show j + (i + 1) = j + i + 1 from by omega]
      rfl

/-- Stage 1 of the unrolled loop, as its instruction list. -/
def b8Stage1 : List Instr :=
  [.call "%14" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%c.096.i")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i" 64 32 (reg "%14"),
   .binop "%add42.i" .or 32 (reg "%conv") (reg "%cast41.i"),
   .gep "%incdec.ptr.i" (.int 8) (reg "%o.addr.095.i") (lit 64 4),
   .store (.int 32) (reg "%add42.i") (reg "%o.addr.095.i"),
   .binop "%sub43.i" .add 64 (reg "%c.096.i") (lit 64 (-1)),
   .binop "%and44.i" .and 64 (reg "%sub43.i") (reg "%c.096.i")]
/-- Stage 2 of the unrolled loop, as its instruction list. -/
def b8Stage2 : List Instr :=
  [.call "%15" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.1" 64 32 (reg "%15"),
   .binop "%add42.i.1" .or 32 (reg "%conv") (reg "%cast41.i.1"),
   .gep "%incdec.ptr.i.1" (.int 8) (reg "%o.addr.095.i") (lit 64 8),
   .store (.int 32) (reg "%add42.i.1") (reg "%incdec.ptr.i"),
   .binop "%sub43.i.1" .add 64 (reg "%and44.i") (lit 64 (-1)),
   .binop "%and44.i.1" .and 64 (reg "%sub43.i.1") (reg "%and44.i")]
/-- Stage 3 of the unrolled loop, as its instruction list. -/
def b8Stage3 : List Instr :=
  [.call "%16" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.1")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.2" 64 32 (reg "%16"),
   .binop "%add42.i.2" .or 32 (reg "%conv") (reg "%cast41.i.2"),
   .gep "%incdec.ptr.i.2" (.int 8) (reg "%o.addr.095.i") (lit 64 12),
   .store (.int 32) (reg "%add42.i.2") (reg "%incdec.ptr.i.1"),
   .binop "%sub43.i.2" .add 64 (reg "%and44.i.1") (lit 64 (-1)),
   .binop "%and44.i.2" .and 64 (reg "%sub43.i.2") (reg "%and44.i.1")]
/-- Stage 4 of the unrolled loop, as its instruction list. -/
def b8Stage4 : List Instr :=
  [.call "%17" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.2")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.3" 64 32 (reg "%17"),
   .binop "%add42.i.3" .or 32 (reg "%conv") (reg "%cast41.i.3"),
   .gep "%incdec.ptr.i.3" (.int 8) (reg "%o.addr.095.i") (lit 64 16),
   .store (.int 32) (reg "%add42.i.3") (reg "%incdec.ptr.i.2"),
   .binop "%sub43.i.3" .add 64 (reg "%and44.i.2") (lit 64 (-1)),
   .binop "%and44.i.3" .and 64 (reg "%sub43.i.3") (reg "%and44.i.2")]
/-- Stage 5 of the unrolled loop, as its instruction list. -/
def b8Stage5 : List Instr :=
  [.call "%18" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.3")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.4" 64 32 (reg "%18"),
   .binop "%add42.i.4" .or 32 (reg "%conv") (reg "%cast41.i.4"),
   .gep "%incdec.ptr.i.4" (.int 8) (reg "%o.addr.095.i") (lit 64 20),
   .store (.int 32) (reg "%add42.i.4") (reg "%incdec.ptr.i.3"),
   .binop "%sub43.i.4" .add 64 (reg "%and44.i.3") (lit 64 (-1)),
   .binop "%and44.i.4" .and 64 (reg "%sub43.i.4") (reg "%and44.i.3")]
/-- Stage 6 of the unrolled loop, as its instruction list. -/
def b8Stage6 : List Instr :=
  [.call "%19" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.4")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.5" 64 32 (reg "%19"),
   .binop "%add42.i.5" .or 32 (reg "%conv") (reg "%cast41.i.5"),
   .gep "%incdec.ptr.i.5" (.int 8) (reg "%o.addr.095.i") (lit 64 24),
   .store (.int 32) (reg "%add42.i.5") (reg "%incdec.ptr.i.4"),
   .binop "%sub43.i.5" .add 64 (reg "%and44.i.4") (lit 64 (-1)),
   .binop "%and44.i.5" .and 64 (reg "%sub43.i.5") (reg "%and44.i.4")]
/-- Stage 7 of the unrolled loop, as its instruction list. -/
def b8Stage7 : List Instr :=
  [.call "%20" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.5")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.6" 64 32 (reg "%20"),
   .binop "%add42.i.6" .or 32 (reg "%conv") (reg "%cast41.i.6"),
   .gep "%incdec.ptr.i.6" (.int 8) (reg "%o.addr.095.i") (lit 64 28),
   .store (.int 32) (reg "%add42.i.6") (reg "%incdec.ptr.i.5"),
   .binop "%sub43.i.6" .add 64 (reg "%and44.i.5") (lit 64 (-1)),
   .binop "%and44.i.6" .and 64 (reg "%sub43.i.6") (reg "%and44.i.5")]
/-- Stage 8 of the unrolled loop, as its instruction list. -/
def b8Stage8 : List Instr :=
  [.call "%21" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.6")), ((.int 1), (lit 1 (-1)))],
   .trunc "%cast41.i.7" 64 32 (reg "%21"),
   .binop "%add42.i.7" .or 32 (reg "%conv") (reg "%cast41.i.7"),
   .gep "%incdec.ptr.i.7" (.int 8) (reg "%o.addr.095.i") (lit 64 32),
   .store (.int 32) (reg "%add42.i.7") (reg "%incdec.ptr.i.6"),
   .binop "%sub43.i.7" .add 64 (reg "%and44.i.6") (lit 64 (-1)),
   .binop "%and44.i.7" .and 64 (reg "%sub43.i.7") (reg "%and44.i.6")]

theorem b8TailLoop_instrs_split :
    b8TailLoop.instrs =
      [.phi "%c.096.i" (.int 64) [("while.body.preheader.i.new", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
       .phi "%o.addr.095.i" .ptr [("while.body.preheader.i.new", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
       .phi "%niter" (.int 64) [("while.body.preheader.i.new", (lit 64 0)), ("while.body.i", (reg "%niter.next.7"))]] ++
      (b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ (b8Stage4 ++ (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ (b8Stage8 ++
        [.binop "%niter.next.7" .add 64 (reg "%niter") (lit 64 8),
         .icmp "%niter.ncmp.7" .eq 64 (reg "%niter.next.7") (reg "%unroll_iter")])))))))) := by
  simp only [b8TailLoop, b8Stage1, b8Stage2, b8Stage3, b8Stage4, b8Stage5, b8Stage6, b8Stage7,
    b8Stage8]
  rfl

/-- Stage 1 of the unrolled loop. -/
theorem b8LoopStage1 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 0 mem)
    (hc : lookupName env "%c.096.i" = some (.int 64 (clearLow w (j + 0))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * (j + 0))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage1
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 1 mem }) ∧
      lookupName env' "%add42.i" = some (.int 32 (slotVal (posBase blk0 i) w (j + 0))) ∧
      lookupName env' "%incdec.ptr.i" = some (.ptr (o + 4 * k + 4 * (j + 1))) ∧
      lookupName env' "%and44.i" = some (.int 64 (clearLow w (j + 1))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage1, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%14" "%c.096.i" (clearLow w (j + 0)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i" "%14" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 0)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i" "%conv" "%cast41.i" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 0)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 4) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 4).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 1) from by
      simp [show (BitVec.ofInt 64 4).toNat = 4 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i" "%o.addr.095.i" (slotVal (posBase blk0 i) w (j + 0)) (o + 4 * k + 4 * (j + 0)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 0)) (natToBytes (slotVal (posBase blk0 i) w (j + 0)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 1 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i" "%c.096.i" 64 (clearLow w (j + 0)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i" "%sub43.i" "%c.096.i" 64 (clearLow w (j + 0) + (-1)) (clearLow w (j + 0)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 0) + (-1)) &&& (clearLow w (j + 0)) = clearLow w (j + 1) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 2 of the unrolled loop. -/
theorem b8LoopStage2 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 1 mem)
    (hc : lookupName env "%and44.i" = some (.int 64 (clearLow w (j + 1))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i" = some (.ptr (o + 4 * k + 4 * (j + 1))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage2
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 2 mem }) ∧
      lookupName env' "%add42.i.1" = some (.int 32 (slotVal (posBase blk0 i) w (j + 1))) ∧
      lookupName env' "%incdec.ptr.i.1" = some (.ptr (o + 4 * k + 4 * (j + 2))) ∧
      lookupName env' "%and44.i.1" = some (.int 64 (clearLow w (j + 2))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage2, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%15" "%and44.i" (clearLow w (j + 1)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.1" "%15" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 1)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.1" "%conv" "%cast41.i.1" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 1)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.1" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 8) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 8).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 2) from by
      simp [show (BitVec.ofInt 64 8).toNat = 8 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.1" "%incdec.ptr.i" (slotVal (posBase blk0 i) w (j + 1)) (o + 4 * k + 4 * (j + 1)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 1)) (natToBytes (slotVal (posBase blk0 i) w (j + 1)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 2 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.1" "%and44.i" 64 (clearLow w (j + 1)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.1" "%sub43.i.1" "%and44.i" 64 (clearLow w (j + 1) + (-1)) (clearLow w (j + 1)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 1) + (-1)) &&& (clearLow w (j + 1)) = clearLow w (j + 2) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 3 of the unrolled loop. -/
theorem b8LoopStage3 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 2 mem)
    (hc : lookupName env "%and44.i.1" = some (.int 64 (clearLow w (j + 2))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.1" = some (.ptr (o + 4 * k + 4 * (j + 2))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage3
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 3 mem }) ∧
      lookupName env' "%add42.i.2" = some (.int 32 (slotVal (posBase blk0 i) w (j + 2))) ∧
      lookupName env' "%incdec.ptr.i.2" = some (.ptr (o + 4 * k + 4 * (j + 3))) ∧
      lookupName env' "%and44.i.2" = some (.int 64 (clearLow w (j + 3))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage3, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%16" "%and44.i.1" (clearLow w (j + 2)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.2" "%16" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 2)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.2" "%conv" "%cast41.i.2" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 2)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.2" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 12) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 12).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 3) from by
      simp [show (BitVec.ofInt 64 12).toNat = 12 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.2" "%incdec.ptr.i.1" (slotVal (posBase blk0 i) w (j + 2)) (o + 4 * k + 4 * (j + 2)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 2)) (natToBytes (slotVal (posBase blk0 i) w (j + 2)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 3 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.2" "%and44.i.1" 64 (clearLow w (j + 2)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.2" "%sub43.i.2" "%and44.i.1" 64 (clearLow w (j + 2) + (-1)) (clearLow w (j + 2)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 2) + (-1)) &&& (clearLow w (j + 2)) = clearLow w (j + 3) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 4 of the unrolled loop. -/
theorem b8LoopStage4 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 3 mem)
    (hc : lookupName env "%and44.i.2" = some (.int 64 (clearLow w (j + 3))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.2" = some (.ptr (o + 4 * k + 4 * (j + 3))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage4
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 4 mem }) ∧
      lookupName env' "%add42.i.3" = some (.int 32 (slotVal (posBase blk0 i) w (j + 3))) ∧
      lookupName env' "%incdec.ptr.i.3" = some (.ptr (o + 4 * k + 4 * (j + 4))) ∧
      lookupName env' "%and44.i.3" = some (.int 64 (clearLow w (j + 4))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage4, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%17" "%and44.i.2" (clearLow w (j + 3)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.3" "%17" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 3)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.3" "%conv" "%cast41.i.3" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 3)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.3" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 16) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 16).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 4) from by
      simp [show (BitVec.ofInt 64 16).toNat = 16 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.3" "%incdec.ptr.i.2" (slotVal (posBase blk0 i) w (j + 3)) (o + 4 * k + 4 * (j + 3)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 3)) (natToBytes (slotVal (posBase blk0 i) w (j + 3)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 4 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.3" "%and44.i.2" 64 (clearLow w (j + 3)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.3" "%sub43.i.3" "%and44.i.2" 64 (clearLow w (j + 3) + (-1)) (clearLow w (j + 3)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 3) + (-1)) &&& (clearLow w (j + 3)) = clearLow w (j + 4) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 5 of the unrolled loop. -/
theorem b8LoopStage5 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 4 mem)
    (hc : lookupName env "%and44.i.3" = some (.int 64 (clearLow w (j + 4))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.3" = some (.ptr (o + 4 * k + 4 * (j + 4))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage5
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem }) ∧
      lookupName env' "%add42.i.4" = some (.int 32 (slotVal (posBase blk0 i) w (j + 4))) ∧
      lookupName env' "%incdec.ptr.i.4" = some (.ptr (o + 4 * k + 4 * (j + 5))) ∧
      lookupName env' "%and44.i.4" = some (.int 64 (clearLow w (j + 5))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage5, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%18" "%and44.i.3" (clearLow w (j + 4)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.4" "%18" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 4)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.4" "%conv" "%cast41.i.4" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 4)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.4" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 20) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 20).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 5) from by
      simp [show (BitVec.ofInt 64 20).toNat = 20 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.4" "%incdec.ptr.i.3" (slotVal (posBase blk0 i) w (j + 4)) (o + 4 * k + 4 * (j + 4)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 4)) (natToBytes (slotVal (posBase blk0 i) w (j + 4)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 5 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.4" "%and44.i.3" 64 (clearLow w (j + 4)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.4" "%sub43.i.4" "%and44.i.3" 64 (clearLow w (j + 4) + (-1)) (clearLow w (j + 4)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 4) + (-1)) &&& (clearLow w (j + 4)) = clearLow w (j + 5) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 6 of the unrolled loop. -/
theorem b8LoopStage6 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 5 mem)
    (hc : lookupName env "%and44.i.4" = some (.int 64 (clearLow w (j + 5))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.4" = some (.ptr (o + 4 * k + 4 * (j + 5))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage6
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem }) ∧
      lookupName env' "%add42.i.5" = some (.int 32 (slotVal (posBase blk0 i) w (j + 5))) ∧
      lookupName env' "%incdec.ptr.i.5" = some (.ptr (o + 4 * k + 4 * (j + 6))) ∧
      lookupName env' "%and44.i.5" = some (.int 64 (clearLow w (j + 6))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage6, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%19" "%and44.i.4" (clearLow w (j + 5)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.5" "%19" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 5)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.5" "%conv" "%cast41.i.5" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 5)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.5" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 24) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 24).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 6) from by
      simp [show (BitVec.ofInt 64 24).toNat = 24 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.5" "%incdec.ptr.i.4" (slotVal (posBase blk0 i) w (j + 5)) (o + 4 * k + 4 * (j + 5)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 5)) (natToBytes (slotVal (posBase blk0 i) w (j + 5)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 6 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.5" "%and44.i.4" 64 (clearLow w (j + 5)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.5" "%sub43.i.5" "%and44.i.4" 64 (clearLow w (j + 5) + (-1)) (clearLow w (j + 5)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 5) + (-1)) &&& (clearLow w (j + 5)) = clearLow w (j + 6) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 7 of the unrolled loop. -/
theorem b8LoopStage7 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 6 mem)
    (hc : lookupName env "%and44.i.5" = some (.int 64 (clearLow w (j + 6))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.5" = some (.ptr (o + 4 * k + 4 * (j + 6))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage7
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 7 mem }) ∧
      lookupName env' "%add42.i.6" = some (.int 32 (slotVal (posBase blk0 i) w (j + 6))) ∧
      lookupName env' "%incdec.ptr.i.6" = some (.ptr (o + 4 * k + 4 * (j + 7))) ∧
      lookupName env' "%and44.i.6" = some (.int 64 (clearLow w (j + 7))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage7, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%20" "%and44.i.5" (clearLow w (j + 6)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.6" "%20" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 6)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.6" "%conv" "%cast41.i.6" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 6)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.6" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 28) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 28).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 7) from by
      simp [show (BitVec.ofInt 64 28).toNat = 28 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.6" "%incdec.ptr.i.5" (slotVal (posBase blk0 i) w (j + 6)) (o + 4 * k + 4 * (j + 6)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 6)) (natToBytes (slotVal (posBase blk0 i) w (j + 6)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 7 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.6" "%and44.i.5" 64 (clearLow w (j + 6)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.6" "%sub43.i.6" "%and44.i.5" 64 (clearLow w (j + 6) + (-1)) (clearLow w (j + 6)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 6) + (-1)) &&& (clearLow w (j + 6)) = clearLow w (j + 7) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- Stage 8 of the unrolled loop. -/
theorem b8LoopStage8 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat) (mem : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 7 mem)
    (hc : lookupName env "%and44.i.6" = some (.int 64 (clearLow w (j + 7))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.6" = some (.ptr (o + 4 * k + 4 * (j + 7))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ env', denoteCode entryCalls b8Stage8
        (withEnv env s)
        = some (withEnv env' { s with mem := b8Lanes o w (posBase blk0 i) k j 8 mem }) ∧
      lookupName env' "%add42.i.7" = some (.int 32 (slotVal (posBase blk0 i) w (j + 7))) ∧
      lookupName env' "%incdec.ptr.i.7" = some (.ptr (o + 4 * k + 4 * (j + 8))) ∧
      lookupName env' "%and44.i.7" = some (.int 64 (clearLow w (j + 8))) := by
  refine ⟨?env', ?hrun, ?hor, ?hgep, ?hand⟩
  case hrun =>
    simp only [b8Stage8, reg, lit]
    ent_step (b8_step_call_cttz _ _ "%21" "%and44.i.6" (clearLow w (j + 7)) (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.7" "%21" 64 32 (BitVec.ofNat 64 (cttz (clearLow w (j + 7)))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.7" "%conv" "%cast41.i.7" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w (j + 7)))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.7" "%o.addr.095.i" (.int 8) (o + 4 * k + 4 * j) (BitVec.ofInt 64 32) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * j) + (BitVec.ofInt 64 32).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (j + 8) from by
      simp [show (BitVec.ofInt 64 32).toNat = 32 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.7" "%incdec.ptr.i.6" (slotVal (posBase blk0 i) w (j + 7)) (o + 4 * k + 4 * (j + 7)) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * (j + 7)) (natToBytes (slotVal (posBase blk0 i) w (j + 7)).toNat 4)
        = b8Lanes o w (posBase blk0 i) k j 8 mem from by rw [hs]; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.7" "%and44.i.6" 64 (clearLow w (j + 7)) (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.7" "%sub43.i.7" "%and44.i.6" 64 (clearLow w (j + 7) + (-1)) (clearLow w (j + 7)) (by ent_auto) (by ent_auto))
    rw [show (clearLow w (j + 7) + (-1)) &&& (clearLow w (j + 7)) = clearLow w (j + 8) from rfl]
    rfl
  case hor => ent_auto
  case hgep => ent_auto
  case hand => ent_auto

/-- The unrolled loop's three phis. -/
theorem b8TailLoop_phis (env : Env) (s : State) (w : BitVec 64) (k o j : Nat) (p : String)
    (opc opo opn : Operand) (niter : Nat)
    (hpre : s.pre = some p)
    (hopc : phiIncoming p b8IncomingC = some opc)
    (hopo : phiIncoming p b8IncomingO = some opo)
    (hopn : phiIncoming p b8IncomingN = some opn)
    (hc : evalOperand (withEnv env s) opc = some (.int 64 (clearLow w j)))
    (ho : evalOperand (withEnv (("%c.096.i", .int 64 (clearLow w j)) :: env) s) opo
            = some (.ptr (o + 4 * k + 4 * j)))
    (hn : evalOperand (withEnv (("%o.addr.095.i", .ptr (o + 4 * k + 4 * j)) ::
            ("%c.096.i", .int 64 (clearLow w j)) :: env) s) opn
            = some (.int 64 (BitVec.ofNat 64 niter))) :
    denoteCode entryCalls
        [.phi "%c.096.i" (.int 64) [("while.body.preheader.i.new", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
         .phi "%o.addr.095.i" .ptr [("while.body.preheader.i.new", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
         .phi "%niter" (.int 64) [("while.body.preheader.i.new", (lit 64 0)), ("while.body.i", (reg "%niter.next.7"))]]
        (withEnv env s)
      = some (withEnv (("%niter", .int 64 (BitVec.ofNat 64 niter)) ::
          ("%o.addr.095.i", .ptr (o + 4 * k + 4 * j)) ::
          ("%c.096.i", .int 64 (clearLow w j)) :: env) s) := by
  simp only [denoteCode, reg, lit, b8IncomingC, b8IncomingO, b8IncomingN]
  have hopc' : phiIncoming p
      [("while.body.preheader.i.new", Operand.reg "%and36.i"),
       ("while.body.i", Operand.reg "%and44.i.7")] = some opc := hopc
  have hopo' : phiIncoming p
      [("while.body.preheader.i.new", Operand.reg "%add.ptr.i"),
       ("while.body.i", Operand.reg "%incdec.ptr.i.7")] = some opo := hopo
  have hopn' : phiIncoming p
      [("while.body.preheader.i.new", Operand.imm (Const.int 64 (BitVec.ofInt 64 0))),
       ("while.body.i", Operand.reg "%niter.next.7")] = some opn := hopn
  rw [phi_step env s "%c.096.i" (.int 64) _ p opc _ hpre hopc' hc]
  simp only [denoteCode, Option.bind]
  rw [phi_step (("%c.096.i", .int 64 (clearLow w j)) :: env) s
    "%o.addr.095.i" .ptr _ p opo _ hpre hopo' ho]
  simp only [denoteCode, Option.bind]
  rw [phi_step (("%o.addr.095.i", .ptr (o + 4 * k + 4 * j)) :: ("%c.096.i", .int 64 (clearLow w j)) :: env) s
    "%niter" (.int 64) _ p opn _ hpre hopn' hn]

/-- Stages 1 to 4 of the unrolled loop. -/
theorem b8Stages_run4 (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat)
    (hc : lookupName env "%c.096.i" = some (.int 64 (clearLow w j)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * (j))))
    (hunroll : lookupName env "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56))) :
    ∃ e, denoteCode entryCalls (b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ (b8Stage4)))) (withEnv env s)
        = some (withEnv e { s with mem := b8Lanes o w (posBase blk0 i) k j 4 s.mem }) ∧
      lookupName e "%and44.i.3" = some (.int 64 (clearLow w (j + 4))) ∧
      lookupName e "%incdec.ptr.i.3" = some (.ptr (o + 4 * k + 4 * (j + 4))) ∧
      lookupName e "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName e "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * (j))) ∧
      lookupName e "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
  obtain ⟨e1, h1, hor1, hgep1, hand1⟩ :=
    b8LoopStage1 env (s) w i blk0 k o j s.mem rfl
      (by ent_lk hc) (by ent_lk hconv) (by ent_lk hbase) (by ent_lk hbase)
  have hconv1 : lookupName e1 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage1 "%conv" (by decide)
      (withEnv env s) (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) h1
    exact h.trans hconv
  have hbase1 : lookupName e1 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage1 "%o.addr.095.i" (by decide)
      (withEnv env s) (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) h1
    exact h.trans hbase
  have hunroll1 : lookupName e1 "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    have h := denoteCode_lookupName entryCalls b8Stage1 "%unroll_iter" (by decide)
      (withEnv env s) (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) h1
    exact h.trans hunroll
  obtain ⟨e2, h2, hor2, hgep2, hand2⟩ :=
    b8LoopStage2 e1 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) w i blk0 k o j s.mem rfl
      (by ent_lk hand1) (by ent_lk hconv1) (by ent_lk hgep1) (by ent_lk hbase1)
  have hconv2 : lookupName e2 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage2 "%conv" (by decide)
      (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) h2
    exact h.trans hconv1
  have hbase2 : lookupName e2 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage2 "%o.addr.095.i" (by decide)
      (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) h2
    exact h.trans hbase1
  have hunroll2 : lookupName e2 "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    have h := denoteCode_lookupName entryCalls b8Stage2 "%unroll_iter" (by decide)
      (withEnv e1 { s with mem := b8Lanes o w (posBase blk0 i) k j 1 s.mem }) (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) h2
    exact h.trans hunroll1
  obtain ⟨e3, h3, hor3, hgep3, hand3⟩ :=
    b8LoopStage3 e2 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) w i blk0 k o j s.mem rfl
      (by ent_lk hand2) (by ent_lk hconv2) (by ent_lk hgep2) (by ent_lk hbase2)
  have hconv3 : lookupName e3 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage3 "%conv" (by decide)
      (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) h3
    exact h.trans hconv2
  have hbase3 : lookupName e3 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage3 "%o.addr.095.i" (by decide)
      (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) h3
    exact h.trans hbase2
  have hunroll3 : lookupName e3 "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    have h := denoteCode_lookupName entryCalls b8Stage3 "%unroll_iter" (by decide)
      (withEnv e2 { s with mem := b8Lanes o w (posBase blk0 i) k j 2 s.mem }) (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) h3
    exact h.trans hunroll2
  obtain ⟨e4, h4, hor4, hgep4, hand4⟩ :=
    b8LoopStage4 e3 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) w i blk0 k o j s.mem rfl
      (by ent_lk hand3) (by ent_lk hconv3) (by ent_lk hgep3) (by ent_lk hbase3)
  have hconv4 : lookupName e4 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage4 "%conv" (by decide)
      (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) (withEnv e4 { s with mem := b8Lanes o w (posBase blk0 i) k j 4 s.mem }) h4
    exact h.trans hconv3
  have hbase4 : lookupName e4 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage4 "%o.addr.095.i" (by decide)
      (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) (withEnv e4 { s with mem := b8Lanes o w (posBase blk0 i) k j 4 s.mem }) h4
    exact h.trans hbase3
  have hunroll4 : lookupName e4 "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    have h := denoteCode_lookupName entryCalls b8Stage4 "%unroll_iter" (by decide)
      (withEnv e3 { s with mem := b8Lanes o w (posBase blk0 i) k j 3 s.mem }) (withEnv e4 { s with mem := b8Lanes o w (posBase blk0 i) k j 4 s.mem }) h4
    exact h.trans hunroll3
  refine ⟨e4, ?_, hand4, hgep4, hconv4, hbase4, hunroll4⟩
  simp only [denoteCode_append, h1, h2, h3, h4, Option.bind_some]

/-- Splitting a straight-line sequence at a point whose state is already known:
the second half runs from it.  Stated so the composition never puts a state under
a `bind`. -/
theorem denoteCode_append_apply {calls : Calls} {a b : List Instr} {s s' : State}
    (h : denoteCode calls a s = some s') :
    denoteCode calls (a ++ b) s = denoteCode calls b s' := by
  rw [denoteCode_append, h]
  rfl

/-- A second memory update replaces the first: the fields the outer update keeps
are the ones the inner update never touches. -/
theorem state_update_update (s : State) (m1 m2 : Mem) :
    ({ { s with mem := m1 } with mem := m2 } : State) = { s with mem := m2 } := rfl

/-- Stages 5 to 8 of the unrolled loop.  The three names the iteration carries
across its stages are threaded once, at the loop body that composes this half
with the first, rather than re-derived per stage.  The half's memory is named as
a variable, so composing it with the first never asks the elaborator to reduce a
lane fold. -/
theorem b8Stages_run4B (env : Env) (s t : State) (w : BitVec 64) (i blk0 k o j : Nat)
    (mem M8 : Mem)
    (hs : s.mem = b8Lanes o w (posBase blk0 i) k j 4 mem)
    (ht : t = { s with mem := M8 })
    (hM8 : M8 = b8Lanes o w (posBase blk0 i) k j 8 mem)
    (hc : lookupName env "%and44.i.3" = some (.int 64 (clearLow w (j + 4))))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%incdec.ptr.i.3" = some (.ptr (o + 4 * k + 4 * (j + 4))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j))) :
    ∃ e, denoteCode entryCalls (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8))) (withEnv env s)
        = some (withEnv e t) ∧
      lookupName e "%and44.i.7" = some (.int 64 (clearLow w (j + 8))) ∧
      lookupName e "%incdec.ptr.i.7" = some (.ptr (o + 4 * k + 4 * (j + 8))) ∧
      lookupName e "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
  obtain ⟨e5, h5, hor5, hgep5, hand5⟩ :=
    b8LoopStage5 env s w i blk0 k o j mem hs hc hconv hptr hbase
  have hconv5 : lookupName e5 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage5 "%conv" (by decide)
      (withEnv env s) (withEnv e5 { s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem }) h5
    exact h.trans hconv
  have hbase5 : lookupName e5 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage5 "%o.addr.095.i" (by decide)
      (withEnv env s) (withEnv e5 { s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem }) h5
    exact h.trans hbase
  obtain ⟨e6, h6, hor6, hgep6, hand6⟩ :=
    b8LoopStage6 e5 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem }) w i blk0 k o j mem
      (state_mem_update _ _) (by ent_lk hand5) (by ent_lk hconv5) (by ent_lk hgep5) hbase5
  have hconv6 : lookupName e6 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage6 "%conv" (by decide)
      (withEnv e5 { s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem })
      (withEnv e6 { s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem }) h6
    exact h.trans hconv5
  have hbase6 : lookupName e6 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage6 "%o.addr.095.i" (by decide)
      (withEnv e5 { s with mem := b8Lanes o w (posBase blk0 i) k j 5 mem })
      (withEnv e6 { s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem }) h6
    exact h.trans hbase5
  obtain ⟨e7, h7, hor7, hgep7, hand7⟩ :=
    b8LoopStage7 e6 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem }) w i blk0 k o j mem
      (state_mem_update _ _) (by ent_lk hand6) (by ent_lk hconv6) (by ent_lk hgep6) hbase6
  have hconv7 : lookupName e7 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage7 "%conv" (by decide)
      (withEnv e6 { s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem })
      (withEnv e7 { s with mem := b8Lanes o w (posBase blk0 i) k j 7 mem }) h7
    exact h.trans hconv6
  have hbase7 : lookupName e7 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls b8Stage7 "%o.addr.095.i" (by decide)
      (withEnv e6 { s with mem := b8Lanes o w (posBase blk0 i) k j 6 mem })
      (withEnv e7 { s with mem := b8Lanes o w (posBase blk0 i) k j 7 mem }) h7
    exact h.trans hbase6
  obtain ⟨e8, h8, hor8, hgep8, hand8⟩ :=
    b8LoopStage8 e7 ({ s with mem := b8Lanes o w (posBase blk0 i) k j 7 mem }) w i blk0 k o j mem
      (state_mem_update _ _) (by ent_lk hand7) (by ent_lk hconv7) (by ent_lk hgep7) hbase7
  have hconv8 : lookupName e8 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    have h := denoteCode_lookupName entryCalls b8Stage8 "%conv" (by decide)
      (withEnv e7 { s with mem := b8Lanes o w (posBase blk0 i) k j 7 mem })
      (withEnv e8 { s with mem := b8Lanes o w (posBase blk0 i) k j 8 mem }) h8
    exact h.trans hconv7
  refine ⟨e8, ?_, hand8, hgep8, hconv8⟩
  rw [denoteCode_append, h5]
  simp only [Option.bind_some]
  rw [denoteCode_append, h6]
  simp only [Option.bind_some]
  rw [denoteCode_append, h7]
  simp only [Option.bind_some]
  rw [h8]
  simp only [Option.bind_some]
  rw [ht, hM8]

/-- The block's written lanes: at least its eight fixed slots, and its count once
that is larger than eight. -/
theorem ctpop_le_slotCount (w : BitVec 64) : ctpop w ≤ slotCount w := by
  have h := ctpop_clearLow w 8
  unfold slotCount
  by_cases h8 : ctpop w ≤ 8
  · rw [h, Nat.sub_eq_zero_of_le h8]; omega
  · rw [h, Nat.add_sub_cancel' (by omega)]; omega

/-- A non-zero word has a set lane, so its count is at least one. -/
theorem ctpop_pos_of_ne {w : BitVec 64} (hw : w ≠ 0) : 1 ≤ ctpop w := by
  rcases Nat.eq_zero_or_pos (ctpop w) with h0 | hpos
  · exfalso
    apply hw
    apply eq_zero_of_setLanes_nil
    have hlen := ctpop_eq_setLanes_length w
    rw [h0] at hlen
    exact List.length_eq_zero_iff.mp hlen.symm
  · exact hpos

theorem slotCount_le {w : BitVec 64} (hw : w ≠ 0) : slotCount w ≤ ctpop w + 7 := by
  have h := ctpop_clearLow w 8
  have hpos := ctpop_pos_of_ne hw
  unfold slotCount
  by_cases h8 : ctpop w ≤ 8
  · rw [h, Nat.sub_eq_zero_of_le h8]; omega
  · rw [h, Nat.add_sub_cancel' (by omega)]; omega

/-- The block's lanes as a fold: `b8BlockStore` chains one block's writes over
the stream, so a prefix of blocks is one fold and its cursor is the stream's
population count.  One block's stores:  A zero word stores nothing; otherwise the eight fixed
slots, and, for a long word, one further slot per set lane past the eighth. -/
def b8BlockStore (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) : Mem :=
  if w = 0 then mem else b8Lanes o w base k 0 (slotCount w) mem

theorem b8BlockStore_zero (o : Nat) (base k : Nat) (mem : Mem) :
    b8BlockStore o 0 base k mem = mem := by
  unfold b8BlockStore
  simp

theorem b8BlockStore_of_ne (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (h : w ≠ 0) :
    b8BlockStore o w base k mem = b8Lanes o w base k 0 (slotCount w) mem := by
  unfold b8BlockStore
  split
  · exact absurd ‹w = 0› h
  · rfl

/-- The stream's blocks, each written at its own base and cursor. -/
def b8MemFold (o : Nat) : Nat → Nat → List (BitVec 64) → Mem → Mem
  | _, _, [], mem => mem
  | base, k, w :: ws, mem =>
      b8MemFold o (base + 64) (k + ctpop w) ws (b8BlockStore o w base k mem)

theorem b8MemFold_append (o base k : Nat) (a b : List (BitVec 64)) (mem : Mem) :
    b8MemFold o base k (a ++ b) mem =
      b8MemFold o (base + 64 * a.length) (pos8Cursor a k) b (b8MemFold o base k a mem) := by
  induction a generalizing base k mem with
  | nil =>
      show b8MemFold o base k b mem =
        b8MemFold o (base + 64 * ([] : List (BitVec 64)).length) (pos8Cursor [] k) b mem
      rw [pos8Cursor]
      rfl
  | cons w ws ih =>
      show b8MemFold o (base + 64) (k + ctpop w) (ws ++ b) (b8BlockStore o w base k mem) =
        b8MemFold o (base + 64 * (ws.length + 1)) (pos8Cursor ws (k + ctpop w)) b
          (b8MemFold o (base + 64) (k + ctpop w) ws (b8BlockStore o w base k mem))
      rw [ih (base + 64) (k + ctpop w) (b8BlockStore o w base k mem)]
      rw [show base + 64 * (ws.length + 1) = (base + 64) + 64 * ws.length from by omega]

/-- The first half of the stages, at a memory variable: the composition that
joins it to the second half never asks the elaborator to reduce a lane fold. -/
theorem b8Stages_run4v (env : Env) (s : State) (w : BitVec 64) (i blk0 k o j : Nat)
    (M0 M4 : Mem)
    (hM0 : s.mem = M0)
    (hM4 : M4 = b8Lanes o w (posBase blk0 i) k j 4 M0)
    (hc : lookupName env "%c.096.i" = some (.int 64 (clearLow w j)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hbase : lookupName env "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)))
    (hunroll : lookupName env "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56))) :
    ∃ e, denoteCode entryCalls (b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4)))
        (withEnv env s) = some (withEnv e { s with mem := M4 }) ∧
      lookupName e "%and44.i.3" = some (.int 64 (clearLow w (j + 4))) ∧
      lookupName e "%incdec.ptr.i.3" = some (.ptr (o + 4 * k + 4 * (j + 4))) ∧
      lookupName e "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName e "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * (j))) ∧
      lookupName e "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
  obtain ⟨e4, h4, hand4, hgep4, hconv4, hbase4, hunroll4⟩ :=
    b8Stages_run4 env s w i blk0 k o j hc hconv hbase hunroll
  refine ⟨e4, ?_, hand4, hgep4, hconv4, hbase4, hunroll4⟩
  rw [h4, hM4, hM0]

/-- The loop body's instructions, grouped as the composition consumes them. -/
theorem b8TailLoop_instrs_grouped :
    b8TailLoop.instrs =
      [.phi "%c.096.i" (.int 64) [("while.body.preheader.i.new", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
       .phi "%o.addr.095.i" .ptr [("while.body.preheader.i.new", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
       .phi "%niter" (.int 64) [("while.body.preheader.i.new", (lit 64 0)), ("while.body.i", (reg "%niter.next.7"))]] ++
      ((b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4))) ++
       ((b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8))) ++
        [.binop "%niter.next.7" .add 64 (reg "%niter") (lit 64 8),
         .icmp "%niter.ncmp.7" .eq 64 (reg "%niter.next.7") (reg "%unroll_iter")])) := by
  rw [b8TailLoop_instrs_split]
  simp only [List.append_assoc]

/-- The loop body's counter instructions. -/
def b8CounterInstrs : List Instr :=
  [.binop "%niter.next.7" .add 64 (reg "%niter") (lit 64 8),
   .icmp "%niter.ncmp.7" .eq 64 (reg "%niter.next.7") (reg "%unroll_iter")]

/-- The loop body's counter: `%niter` steps by eight and the exit test compares it
with `%unroll_iter`. -/
theorem b8Counter_run (env : Env) (s : State) (niter : Nat) (u : BitVec 64)
    (hN : lookupName env "%niter" = some (.int 64 (BitVec.ofNat 64 niter)))
    (hU : lookupName env "%unroll_iter" = some (.int 64 u))
    (hniter : niter + 8 < 2 ^ 64) :
    ∃ e, denoteCode entryCalls
        [.binop "%niter.next.7" .add 64 (reg "%niter") (lit 64 8),
         .icmp "%niter.ncmp.7" .eq 64 (reg "%niter.next.7") (reg "%unroll_iter")]
        (withEnv env s) = some (withEnv e s) ∧
      lookupName e "%niter.next.7" = some (.int 64 (BitVec.ofNat 64 (niter + 8))) ∧
      lookupName e "%niter.ncmp.7"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (niter + 8) = u))) := by
  refine ⟨?e, ?hrun, ?hnext, ?hcmp⟩
  case hrun =>
    simp only [reg, lit]
    ent_step (step_add_imm _ _ "%niter.next.7" "%niter" 64 (BitVec.ofNat 64 niter)
      (BitVec.ofInt 64 8) hN)
    rw [show (BitVec.ofInt 64 8 : BitVec 64) = BitVec.ofNat 64 8 from by decide,
      ofNat64_add_ofNat niter 8 hniter]
    ent_step (step_icmp_eq_reg _ _ "%niter.ncmp.7" "%niter.next.7" "%unroll_iter" 64
      (BitVec.ofNat 64 (niter + 8)) u (by ent_auto) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hnext => ent_auto
  case hcmp => ent_auto

/-- The unrolled tail loop's iteration: three phis, the eight stages in two
composed halves, and the counter.  Its memory and its exit state are named as
variables, so chaining iterations never asks the elaborator to reduce a fold or a
record update. -/
theorem b8LoopBody_run (env : Env) (s t : State) (w : BitVec 64) (i blk0 k o j niter : Nat)
    (p : String) (opc opo opn : Operand) (M0 M4 M8 : Mem)
    (hpre : s.pre = some p)
    (hopc : phiIncoming p b8IncomingC = some opc)
    (hopo : phiIncoming p b8IncomingO = some opo)
    (hopn : phiIncoming p b8IncomingN = some opn)
    (hc : evalOperand (withEnv env s) opc = some (.int 64 (clearLow w j)))
    (ho : evalOperand (withEnv (("%c.096.i", .int 64 (clearLow w j)) :: env) s) opo
            = some (.ptr (o + 4 * k + 4 * j)))
    (hn : evalOperand (withEnv (("%o.addr.095.i", .ptr (o + 4 * k + 4 * j)) ::
            ("%c.096.i", .int 64 (clearLow w j)) :: env) s) opn
            = some (.int 64 (BitVec.ofNat 64 niter)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hunroll : lookupName env "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)))
    (hniter : niter + 8 < 2 ^ 64)
    (hM0 : s.mem = M0)
    (hM4 : M4 = b8Lanes o w (posBase blk0 i) k j 4 M0)
    (hM8 : M8 = b8Lanes o w (posBase blk0 i) k j 8 M0)
    (ht : t = { { s with mem := M4 } with mem := M8 }) :
    ∃ e, denoteCode entryCalls b8TailLoop.instrs (withEnv env s)
        = some (withEnv e t) ∧
      lookupName e "%and44.i.7" = some (.int 64 (clearLow w (j + 8))) ∧
      lookupName e "%incdec.ptr.i.7" = some (.ptr (o + 4 * k + 4 * (j + 8))) ∧
      lookupName e "%niter.next.7" = some (.int 64 (BitVec.ofNat 64 (niter + 8))) ∧
      lookupName e "%niter.ncmp.7"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (niter + 8)
            = (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)))) ∧
      lookupName e "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName e "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) ∧
      lookupName e "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
  let env₃ : Env := ("%niter", .int 64 (BitVec.ofNat 64 niter)) ::
    ("%o.addr.095.i", .ptr (o + 4 * k + 4 * j)) ::
    ("%c.096.i", .int 64 (clearLow w j)) :: env
  have hphis := b8TailLoop_phis env s w k o j p opc opo opn niter hpre hopc hopo hopn hc ho hn
  have hc3 : lookupName env₃ "%c.096.i" = some (.int 64 (clearLow w j)) := by
    show lookupName (("%niter", Value.int 64 (BitVec.ofNat 64 niter)) ::
      ("%o.addr.095.i", Value.ptr (o + 4 * k + 4 * j)) ::
      ("%c.096.i", Value.int 64 (clearLow w j)) :: env) "%c.096.i" = _
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    rfl
  have hconv3 : lookupName env₃ "%conv"
      = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) := by
    show lookupName (("%niter", Value.int 64 (BitVec.ofNat 64 niter)) ::
      ("%o.addr.095.i", Value.ptr (o + 4 * k + 4 * j)) ::
      ("%c.096.i", Value.int 64 (clearLow w j)) :: env) "%conv" = _
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hconv
  have hbase3 : lookupName env₃ "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    show lookupName (("%niter", Value.int 64 (BitVec.ofNat 64 niter)) ::
      ("%o.addr.095.i", Value.ptr (o + 4 * k + 4 * j)) ::
      ("%c.096.i", Value.int 64 (clearLow w j)) :: env) "%o.addr.095.i" = _
    rw [lookupName_cons_ne _ _ (by decide)]
    rfl
  have hN3 : lookupName env₃ "%niter" = some (.int 64 (BitVec.ofNat 64 niter)) := by
    show lookupName (("%niter", Value.int 64 (BitVec.ofNat 64 niter)) :: _) "%niter" = _
    rfl
  have hunroll3 : lookupName env₃ "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    show lookupName (("%niter", Value.int 64 (BitVec.ofNat 64 niter)) ::
      ("%o.addr.095.i", Value.ptr (o + 4 * k + 4 * j)) ::
      ("%c.096.i", Value.int 64 (clearLow w j)) :: env) "%unroll_iter" = _
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]
    exact hunroll
  obtain ⟨e4, h4, hand4, hgep4, hconv4, hbase4, hunroll4⟩ :=
    b8Stages_run4v env₃ s w i blk0 k o j M0 M4 hM0 hM4 hc3 hconv3 hbase3 hunroll3
  have hphis' : denoteCode entryCalls
      [.phi "%c.096.i" (.int 64) [("while.body.preheader.i.new", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
       .phi "%o.addr.095.i" .ptr [("while.body.preheader.i.new", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
       .phi "%niter" (.int 64) [("while.body.preheader.i.new", (lit 64 0)), ("while.body.i", (reg "%niter.next.7"))]]
      (withEnv env s) = some (withEnv env₃ s) := hphis
  obtain ⟨e8, h8, hand8, hgep8, hconv8⟩ :=
    b8Stages_run4B e4 ({ s with mem := M4 }) t w i blk0 k o j M0 M8
      ((state_mem_update _ _).trans hM4) ht hM8 hand4 hconv4 hgep4 hbase4
  have hstages : denoteCode entryCalls
      ((b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4))) ++
       (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8)))) (withEnv env₃ s)
      = some (withEnv e8 t) := by
    rw [denoteCode_append_apply h4]
    exact h8
  have hN8 : lookupName e8 "%niter" = some (.int 64 (BitVec.ofNat 64 niter)) := by
    have h := denoteCode_lookupName entryCalls
      ((b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4))) ++
       (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8)))) "%niter" (by decide)
      (withEnv env₃ s) (withEnv e8 t) hstages
    exact h.trans hN3
  have hunroll8 : lookupName e8 "%unroll_iter"
      = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
    have h := denoteCode_lookupName entryCalls
      ((b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4))) ++
       (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8)))) "%unroll_iter" (by decide)
      (withEnv env₃ s) (withEnv e8 t) hstages
    exact h.trans hunroll3
  have hbase8 : lookupName e8 "%o.addr.095.i" = some (.ptr (o + 4 * k + 4 * j)) := by
    have h := denoteCode_lookupName entryCalls
      ((b8Stage1 ++ (b8Stage2 ++ (b8Stage3 ++ b8Stage4))) ++
       (b8Stage5 ++ (b8Stage6 ++ (b8Stage7 ++ b8Stage8)))) "%o.addr.095.i" (by decide)
      (withEnv env₃ s) (withEnv e8 t) hstages
    exact h.trans hbase3
  obtain ⟨e', hcnt, hnext, hcmp⟩ := b8Counter_run e8 t niter
    (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56) hN8 hunroll8 hniter
  have hfull : denoteCode entryCalls b8TailLoop.instrs (withEnv env s) = some (withEnv e' t) := by
    rw [b8TailLoop_instrs_grouped]
    rw [denoteCode_append_apply hphis']
    rw [denoteCode_append_apply h4]
    rw [denoteCode_append_apply h8]
    rw [hcnt]
  have hkeep : ∀ (n : String) (v : Value), n ≠ "%niter.next.7" → n ≠ "%niter.ncmp.7" →
      lookupName e8 n = some v → lookupName e' n = some v := by
    intro n v h1 h2 h
    have hpres := denoteCode_lookupName entryCalls b8CounterInstrs n
      (by
        intro i hi
        simp only [b8CounterInstrs, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · intro hd
          exact h1 (Option.some.inj hd).symm
        · intro hd
          exact h2 (Option.some.inj hd).symm)
      (withEnv e8 t) (withEnv e' t) hcnt
    exact hpres.trans h
  exact ⟨e', hfull, hkeep _ _ (by decide) (by decide) hand8,
    hkeep _ _ (by decide) (by decide) hgep8, hnext, hcmp,
    hkeep _ _ (by decide) (by decide) hconv8, hkeep _ _ (by decide) (by decide) hbase8,
    hkeep _ _ (by decide) (by decide) hunroll8⟩

theorem findBlock_b8Advance :
    entryB8Function.findBlock "cleanup" = some b8Advance := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_b8Exit :
    entryB8Function.findBlock "for.cond.cleanup" = some b8LoopExit := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

/-! ### The epilogue's iteration

One iteration of the scalar tail: `cttz` of the cleared word, its slot store, the
next clearing step, and the trip counter. -/

theorem b8EpilBody_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o jj e : Nat)
    (p : String) (opcc opco opci : Operand) (M M' : Mem) (u : BitVec 64)
    (hpre : s.pre = some p)
    (hopc : phiIncoming p b8IncomingCe = some opcc)
    (hopo : phiIncoming p b8IncomingOe = some opco)
    (hopi : phiIncoming p b8IncomingIe = some opci)
    (hc : evalOperand (withEnv env s) opcc = some (.int 64 (clearLow w jj)))
    (ho : evalOperand (withEnv (("%c.096.i.epil", .int 64 (clearLow w jj)) :: env) s) opco
            = some (.ptr (o + 4 * k + 4 * jj)))
    (hi : evalOperand (withEnv (("%o.addr.095.i.epil", .ptr (o + 4 * k + 4 * jj)) ::
            ("%c.096.i.epil", .int 64 (clearLow w jj)) :: env) s) opci
            = some (.int 64 (BitVec.ofNat 64 e)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hxtra : lookupName env "%xtraiter" = some (.int 64 u))
    (he64 : e + 1 < 2 ^ 64)
    (hm : s.mem = M)
    (hM' : M' = b8Lanes o w (posBase blk0 i) k jj 1 M) :
    ∃ e', denoteCode entryCalls b8TailRemainder.instrs (withEnv env s)
        = some (withEnv e' { s with mem := M' }) ∧
      lookupName e' "%and44.i.epil" = some (.int 64 (clearLow w (jj + 1))) ∧
      lookupName e' "%incdec.ptr.i.epil" = some (.ptr (o + 4 * k + 4 * (jj + 1))) ∧
      lookupName e' "%epil.iter.next" = some (.int 64 (BitVec.ofNat 64 (e + 1))) ∧
      lookupName e' "%epil.iter.cmp.not"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (e + 1) = u))) ∧
      lookupName e' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName e' "%xtraiter" = some (.int 64 u) := by
  refine ⟨?e', ?hrun, ?hand, ?hgep, ?hnext, ?hcmp, ?hconv', ?hxtra'⟩
  case hrun =>
    simp only [b8TailRemainder, reg, lit, b8IncomingCe, b8IncomingOe, b8IncomingIe]
    ent_step (phi_step env s "%c.096.i.epil" (.int 64) _ p opcc _
      hpre (by assumption) hc)
    ent_step (phi_step (("%c.096.i.epil", .int 64 (clearLow w jj)) :: env) s
      "%o.addr.095.i.epil" .ptr _ p opco _ hpre (by assumption) ho)
    ent_step (phi_step (("%o.addr.095.i.epil", .ptr (o + 4 * k + 4 * jj)) ::
      ("%c.096.i.epil", .int 64 (clearLow w jj)) :: env) s
      "%epil.iter" (.int 64) _ p opci _ hpre (by assumption) hi)
    ent_step (b8_step_call_cttz _ _ "%22" "%c.096.i.epil" (clearLow w jj)
      (BitVec.ofInt 1 (-1)) (by ent_auto))
    ent_step (step_trunc _ _ "%cast41.i.epil" "%22" 64 32
      (BitVec.ofNat 64 (cttz (clearLow w jj))) (by ent_auto))
    rw [trunc_cttz _]
    ent_step (b8_step_or_reg _ _ "%add42.i.epil" "%conv" "%cast41.i.epil" 32
      (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofNat 32 (cttz (clearLow w jj))) (by ent_auto) (by ent_auto))
    ent_step (b8_step_gep_imm _ _ "%incdec.ptr.i.epil" "%o.addr.095.i.epil" (.int 8)
      (o + 4 * k + 4 * jj) (BitVec.ofInt 64 4) (by ent_auto) (by decide))
    rw [show (o + 4 * k + 4 * jj) + (BitVec.ofInt 64 4).toNat * (Ty.int 8).sizeBytes
        = o + 4 * k + 4 * (jj + 1) from by
      simp [show (BitVec.ofInt 64 4).toNat = 4 from by decide,
        show (Ty.int 8).sizeBytes = 1 from rfl]
      omega]
    ent_step (b8_step_store32 _ _ "%add42.i.epil" "%o.addr.095.i.epil"
      (slotVal (posBase blk0 i) w jj) (o + 4 * k + 4 * jj) (by ent_auto) (by ent_auto))
    rw [show writeBytes s.mem (o + 4 * k + 4 * jj)
        (natToBytes (slotVal (posBase blk0 i) w jj).toNat 4)
        = M' from by rw [hm, hM']; rfl]
    ent_step (step_add_imm _ _ "%sub43.i.epil" "%c.096.i.epil" 64 (clearLow w jj)
      (BitVec.ofInt 64 (-1)) (by ent_auto))
    ent_step (b8_step_and_reg _ _ "%and44.i.epil" "%sub43.i.epil" "%c.096.i.epil" 64
      (clearLow w jj + (-1)) (clearLow w jj) (by ent_auto) (by ent_auto))
    rw [show (clearLow w jj + (-1)) &&& (clearLow w jj) = clearLow w (jj + 1) from rfl]
    ent_step (step_add_imm _ _ "%epil.iter.next" "%epil.iter" 64
      (BitVec.ofNat 64 e) (BitVec.ofInt 64 1) (by ent_auto))
    rw [ofInt64_one, ofNat64_add_one e he64]
    ent_step (step_icmp_eq_reg _ _ "%epil.iter.cmp.not" "%epil.iter.next" "%xtraiter" 64
      (BitVec.ofNat 64 (e + 1)) u (by ent_auto) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hand => ent_auto
  case hgep => ent_auto
  case hnext => ent_auto
  case hcmp => ent_auto
  case hconv' => ent_auto
  case hxtra' => ent_auto

/-! ### `for.body`, `cleanup` and `for.cond.cleanup`

B8's three outer blocks are the same instructions as POS8's, so their bodies are
the same terms; only the function the step is taken in differs. -/

theorem b8Body_body (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63) :
    ∃ env', denoteCode entryCalls b8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 (BitVec.ofBool (w = 0))) :=
  pos8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63

theorem b8Body_step_zero (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w = 0) :
    ∃ env', denoteCode entryCalls b8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    b8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (1 : BitVec 1) := by
    rw [show decide (w = 0) = true from decide_eq_true hw]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [b8_step_of (withEnv env s) "for.body" b8Body (withEnv env' s) hpc
      findBlock_b8Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" })
    rw [execTerm_condbr_true (c := .reg "%tobool.not") (t := "cleanup") (f := "if.end")
      (evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4) hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

theorem b8Body_step_pos (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w ≠ 0) :
    ∃ env', denoteCode entryCalls b8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    b8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (0 : BitVec 1) := by
    rw [show decide (w = 0) = false from decide_eq_false hw]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [b8_step_of (withEnv env s) "for.body" b8Body (withEnv env' s) hpc
      findBlock_b8Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" })
    rw [execTerm_condbr_false (c := .reg "%tobool.not") (t := "cleanup") (f := "if.end")
      (evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4) hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

/-- `cleanup`'s phi, whose first edge comes from B8's join. -/
def b8IncomingCl : List (String × Operand) :=
  [("s1f_ke_b8.exit", reg "%add1"), ("for.body", reg "%k.addr.011")]

/-- `cleanup`: the cursor phi, the block counter, and the exit test. -/
theorem b8Advance_body (env : Env) (s : State) (i k nblk : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64) :
    ∃ env', denoteCode entryCalls b8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) := by
  refine ⟨?env', ?hrun, ?hk, ?hinc, ?hx⟩
  case hrun =>
    simp only [b8Advance, reg, lit, b8IncomingCl]
    ent_step (phi_step env s "%k.addr.1" (.int 64) _ p opk _ hpre (by assumption) hvk)
    ent_step (step_add_imm _ _ "%inc" "%i.010" 64 (BitVec.ofNat 64 i) (BitVec.ofInt 64 1)
      (by ent_auto))
    rw [ofInt64_one, ofNat64_add_one i hi64]
    ent_step (step_icmp_eq_reg _ _ "%exitcond.not" "%inc" "%nblk" 64
      (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 nblk) (by ent_auto) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hk => ent_auto
  case hinc => ent_auto
  case hx => ent_auto

/-- `cleanup`: the cursor phi, the block counter, and the exit test. -/
theorem b8Advance_step_more (env : Env) (s : State) (i k nblk : Nat) (p : String)
    (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls b8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, hk, hinc, hxx⟩ :=
    b8Advance_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hx' : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (0 : BitVec 1) := by
    rw [show decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = false from
      decide_eq_false hx]
    rfl
  refine ⟨env', hbody, ?_, hk, hinc, ?_⟩
  · rw [b8_step_of (withEnv env s) "cleanup" b8Advance (withEnv env' s) hpc
      findBlock_b8Advance hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" })
    rw [execTerm_condbr_false (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body")
      (evalOperand_reg_of env' s "%exitcond.not"
        (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) hxx) hx']
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hx'] at hxx

theorem b8Advance_step_last (env : Env) (s : State) (i k nblk : Nat) (p : String)
    (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p b8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls b8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, hk, hinc, hxx⟩ :=
    b8Advance_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hx' : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (1 : BitVec 1) := by
    rw [show decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = true from
      decide_eq_true hx]
    rfl
  refine ⟨env', hbody, ?_, hk, hinc, ?_⟩
  · rw [b8_step_of (withEnv env s) "cleanup" b8Advance (withEnv env' s) hpc
      findBlock_b8Advance hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" })
    rw [execTerm_condbr_true (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body")
      (evalOperand_reg_of env' s "%exitcond.not"
        (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) hxx) hx']
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hx'] at hxx

/-- `for.cond.cleanup`: the cursor phi and the return. -/
theorem b8Exit_run (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls b8LoopExit.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) :=
  pos8Exit_body env s k p opk hpre hopk hvk

theorem b8Exit_step (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpc : s.pc = "for.cond.cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls b8LoopExit.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨env', hbody, hk⟩ := b8Exit_run env s k p opk hpre hopk hvk
  refine ⟨env', hbody, ?_, hk⟩
  rw [b8_step_of (withEnv env s) "for.cond.cleanup" b8LoopExit (withEnv env' s) hpc
    findBlock_b8Exit hbody]
  show execTerm (withEnv env' s) (.ret (.int 64) (some (.reg "%k.addr.0.lcssa")))
    = .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s)
  rw [execTerm_ret_reg (s := withEnv env' s) (d := "%k.addr.0.lcssa")
    (v := .int 64 (BitVec.ofNat 64 k)) (evalOperand_reg_of env' s "%k.addr.0.lcssa"
      (.int 64 (BitVec.ofNat 64 k)) hk)]

/-- The join: the per-block count phi and the cursor addition. -/
theorem b8Join_run (env : Env) (s : State) (rv k : Nat) (p : String) (opr : Operand)
    (hpre : s.pre = some p)
    (hopr : phiIncoming p b8IncomingR = some opr)
    (hrv : evalOperand (withEnv env s) opr = some (.int 64 (BitVec.ofNat 64 rv)))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hsum : rv + k < 2 ^ 64) :
    ∃ e, denoteCode entryCalls b8Join.instrs (withEnv env s) = some (withEnv e s) ∧
      lookupName e "%add1" = some (.int 64 (BitVec.ofNat 64 (rv + k))) := by
  refine ⟨?e, ?hrun, ?hadd⟩
  case hrun =>
    simp only [b8Join, reg, lit, b8IncomingR]
    ent_step (phi_step env s "%retval.0.i" (.int 64) _ p opr _ hpre (by assumption) hrv)
    ent_step (step_add_reg _ _ "%add1" "%retval.0.i" "%k.addr.011" 64
      (BitVec.ofNat 64 rv) (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto))
    rw [ofNat64_add_ofNat rv k hsum]
    simp only [denoteCode, Option.bind]
    rfl
  case hadd => ent_auto

/-- The remainder guard: the two `-lcssa` phis and the trip-count test. -/
theorem b8RemainderGuard_run (env : Env) (s : State) (w : BitVec 64) (k o jj : Nat)
    (p : String) (opc opo : Operand) (u : BitVec 64)
    (hpre : s.pre = some p)
    (hopc : phiIncoming p b8IncomingCu = some opc)
    (hopo : phiIncoming p b8IncomingOu = some opo)
    (hc : evalOperand (withEnv env s) opc = some (.int 64 (clearLow w jj)))
    (ho : evalOperand (withEnv (("%c.096.i.unr", .int 64 (clearLow w jj)) :: env) s) opo
            = some (.ptr (o + 4 * k + 4 * jj)))
    (hx : lookupName env "%xtraiter" = some (.int 64 u)) :
    ∃ e, denoteCode entryCalls b8TailRemainderGuard.instrs (withEnv env s)
        = some (withEnv e s) ∧
      lookupName e "%c.096.i.unr" = some (.int 64 (clearLow w jj)) ∧
      lookupName e "%o.addr.095.i.unr" = some (.ptr (o + 4 * k + 4 * jj)) ∧
      lookupName e "%lcmp.mod.not" = some (.int 1 (BitVec.ofBool (u = BitVec.ofInt 64 0))) := by
  refine ⟨?e, ?hrun, ?hc, ?ho, ?hx⟩
  case hrun =>
    simp only [b8TailRemainderGuard, reg, lit, b8IncomingCu, b8IncomingOu]
    ent_step (phi_step env s "%c.096.i.unr" (.int 64) _ p opc _ hpre (by assumption) hc)
    ent_step (phi_step (("%c.096.i.unr", .int 64 (clearLow w jj)) :: env) s
      "%o.addr.095.i.unr" .ptr _ p opo _ hpre (by assumption) ho)
    ent_step (step_icmp_eq_imm _ _ "%lcmp.mod.not" "%xtraiter" 64 u
      (BitVec.ofInt 64 0) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hc => ent_auto
  case ho => ent_auto
  case hx => ent_auto


/-! ### The unrolled loop's trip count

`%unroll_iter` is `%10 &&& 56`: the tail count with its low three lanes cleared,
which is eight times the integer quotient by eight.  That identity is what makes
the loop's exit test decidable against the iteration counter. -/

theorem land56 (a : Nat) (ha : a < 64) : a &&& 56 = 8 * (a / 8) := by
  apply Nat.eq_of_testBit_eq
  intro n
  rw [Nat.testBit_and]
  have h8a : a / 8 < 8 := by omega
  rcases Nat.lt_or_ge n 3 with hn | hn
  · rcases n with _ | _ | _ | n3
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      rw [show (56 : Nat) / 2 ^ 0 % 2 = 0 from by decide,
        show (8 * (a / 8)) / 2 ^ 0 % 2 = 0 from by omega]
      rw [show decide (0 = 1) = false from rfl, Bool.and_false]
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      rw [show (56 : Nat) / 2 ^ 1 % 2 = 0 from by decide,
        show (8 * (a / 8)) / 2 ^ 1 % 2 = 0 from by omega]
      rw [show decide (0 = 1) = false from rfl, Bool.and_false]
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      rw [show (56 : Nat) / 2 ^ 2 % 2 = 0 from by decide,
        show (8 * (a / 8)) / 2 ^ 2 % 2 = 0 from by omega]
      rw [show decide (0 = 1) = false from rfl, Bool.and_false]
    · omega
  · obtain ⟨j, hj⟩ : ∃ j, n = 3 + j := ⟨n - 3, by omega⟩
    subst hj
    have h56 : (56 : Nat).testBit (3 + j) = decide (j < 3) := by
      rw [show 3 + j = j + 3 from by omega, ← Nat.testBit_div_two_pow]
      rw [show (56 : Nat) / 2 ^ 3 = 7 from by decide]
      exact Nat.testBit_two_pow_sub_one 3 j
    have hleft : a.testBit (3 + j) = (a / 8).testBit j := by
      rw [show 3 + j = j + 3 from by omega, ← Nat.testBit_div_two_pow]
    have hright : (8 * (a / 8)).testBit (3 + j) = (a / 8).testBit j := by
      rw [show 3 + j = j + 3 from by omega, ← Nat.testBit_div_two_pow]
      rw [show (2 : Nat) ^ 3 = 8 from by decide, Nat.mul_div_right _ (by decide : 0 < 8)]
    rw [h56, hleft, hright]
    by_cases hj3 : j < 3
    · rw [show decide (j < 3) = true from decide_eq_true hj3, Bool.and_true]
    · rw [show decide (j < 3) = false from decide_eq_false hj3, Bool.and_false]
      exact (Nat.testBit_lt_two_pow (x := a / 8) (i := j)
        (by have h1 : (8 : Nat) ≤ 2 ^ j := by
              have h2 : (2 : Nat) ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
              simpa using h2
            omega)).symm

theorem and56_bit (a : Nat) (ha : a < 64) :
    BitVec.ofNat 64 a &&& BitVec.ofInt 64 56 = BitVec.ofNat 64 (8 * (a / 8)) := by
  rw [show (BitVec.ofInt 64 56 : BitVec 64) = BitVec.ofNat 64 56 from by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [show (56 : Nat) % 2 ^ 64 = 56 from Nat.mod_eq_of_lt (by decide),
    show a % 2 ^ 64 = a from Nat.mod_eq_of_lt (by omega),
    show 8 * (a / 8) % 2 ^ 64 = 8 * (a / 8) from Nat.mod_eq_of_lt (by omega)]
  exact land56 a ha

/-- The unrolled loop's counter value, as eight times the tail count's quotient. -/
theorem unroll_val (w : BitVec 64) :
    (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)
      = BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8)) := by
  have hlt : ctpop (clearLow w 8) < 64 := by
    have h1 := ctpop_le w
    rw [ctpop_clearLow]
    omega
  exact and56_bit _ hlt

/-- Clearing eight lanes at the fold's current cursor continues the same fold. -/
theorem b8Lanes_step8 (o : Nat) (w : BitVec 64) (base k jm : Nat) (mem : Mem) :
    b8Lanes o w base k (8 + 8 * jm) 8 (b8Lanes o w base k 8 (8 * jm) mem)
      = b8Lanes o w base k 8 (8 * jm + 8) mem :=
  (b8Lanes_split o w base k 8 (8 * jm) 8 mem).symm

/-- One lane past the fold's end continues the same fold. -/
theorem b8Lanes_step1 (o : Nat) (w : BitVec 64) (base k jz e : Nat) (mem : Mem) :
    b8Lanes o w base k (jz + e) 1 (b8Lanes o w base k jz e mem)
      = b8Lanes o w base k jz (e + 1) mem :=
  (b8Lanes_split o w base k jz e 1 mem).symm


/-! ### The names a block carries

Every block of the B8 body reads a few registers the rest of the block, and the
next block, depend on.  Bundling them keeps a composition's hypothesis list and
its conclusion constant in size, and one preservation lemma serves every block. -/

/-- The registers a block carries unchanged: the entry array, its base and length,
the output pointer, the block index, and the cursor. -/
def B8Ctx (env : Env) (e o : Nat) (blk0 nblk ii kk : Nat) : Prop :=
  lookupName env "%ent" = some (.ptr e) ∧
  lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) ∧
  lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) ∧
  lookupName env "%out" = some (.ptr o) ∧
  lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 ii)) ∧
  lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk))

/-- The carried names, as the list the preservation lemma quantifies over. -/
def b8CtxNames : List String :=
  ["%ent", "%blk0", "%nblk", "%out", "%i.010", "%k.addr.011"]

theorem B8Ctx.ent {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%ent" = some (.ptr e) := h.1

theorem B8Ctx.blk0 {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) := h.2.1

theorem B8Ctx.nblk {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) := h.2.2.1

theorem B8Ctx.out {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%out" = some (.ptr o) := h.2.2.2.1

theorem B8Ctx.i010 {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 ii)) := h.2.2.2.2.1

theorem B8Ctx.k011 {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk)) := h.2.2.2.2.2

/-- The four names every block reads and no block writes.  A block entry has
only these: the cursor and the block index are what its own `phi`s bind, so the
bundle a block needs is the frame, not the six-name context the body then
carries. -/
def B8Frame (env : Env) (e o : Nat) (blk0 nblk : Nat) : Prop :=
  lookupName env "%ent" = some (.ptr e) ∧
  lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) ∧
  lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) ∧
  lookupName env "%out" = some (.ptr o)

theorem B8Frame.ent {env : Env} {e o blk0 nblk : Nat} (h : B8Frame env e o blk0 nblk) :
    lookupName env "%ent" = some (.ptr e) := h.1

theorem B8Frame.blk0 {env : Env} {e o blk0 nblk : Nat} (h : B8Frame env e o blk0 nblk) :
    lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) := h.2.1

theorem B8Frame.nblk {env : Env} {e o blk0 nblk : Nat} (h : B8Frame env e o blk0 nblk) :
    lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) := h.2.2.1

theorem B8Frame.out {env : Env} {e o blk0 nblk : Nat} (h : B8Frame env e o blk0 nblk) :
    lookupName env "%out" = some (.ptr o) := h.2.2.2

theorem B8Frame.ctx {env : Env} {e o blk0 nblk : Nat} (h : B8Frame env e o blk0 nblk)
    {env' : Env} {ii kk : Nat}
    (hEnt : lookupName env' "%ent" = lookupName env "%ent")
    (hBlk : lookupName env' "%blk0" = lookupName env "%blk0")
    (hNb : lookupName env' "%nblk" = lookupName env "%nblk")
    (hOut : lookupName env' "%out" = lookupName env "%out")
    (hi : lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 ii)))
    (hk : lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk))) :
    B8Ctx env' e o blk0 nblk ii kk :=
  ⟨hEnt.trans h.ent, hBlk.trans h.blk0, hNb.trans h.nblk, hOut.trans h.out, hi, hk⟩

theorem B8Frame.of_preserved {env env' : Env} {e o blk0 nblk : Nat}
    (h : B8Frame env e o blk0 nblk)
    (hEnt : lookupName env' "%ent" = lookupName env "%ent")
    (hBlk : lookupName env' "%blk0" = lookupName env "%blk0")
    (hNb : lookupName env' "%nblk" = lookupName env "%nblk")
    (hOut : lookupName env' "%out" = lookupName env "%out") :
    B8Frame env' e o blk0 nblk :=
  ⟨hEnt.trans h.ent, hBlk.trans h.blk0, hNb.trans h.nblk, hOut.trans h.out⟩

theorem B8Ctx.frame {env : Env} {e o blk0 nblk ii kk : Nat} (h : B8Ctx env e o blk0 nblk ii kk) :
    B8Frame env e o blk0 nblk := ⟨h.ent, h.blk0, h.nblk, h.out⟩

/-- A block that writes none of the carried names leaves all of them alone. -/
theorem b8_keep (instrs : List Instr)
    (hn : ∀ i ∈ instrs, i.dst? ∉ b8CtxNames.map some) (s s' : State)
    (h : denoteCode entryCalls instrs s = some s') :
    ∀ n ∈ b8CtxNames, lookupName s'.env n = lookupName s.env n := by
  intro n hmem
  exact denoteCode_lookupName entryCalls instrs n
    (fun i hi hd => hn i hi (hd.symm ▸ List.mem_map_of_mem (f := some) hmem)) s s' h

/-- Carrying the bundle across a block. -/
theorem B8Ctx.transfer {env env' : Env} {e o blk0 nblk ii kk : Nat}
    (h : B8Ctx env e o blk0 nblk ii kk)
    (hkeep : ∀ n ∈ b8CtxNames, lookupName env' n = lookupName env n) :
    B8Ctx env' e o blk0 nblk ii kk := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkeep _ (by decide)]; exact h1
  · rw [hkeep _ (by decide)]; exact h2
  · rw [hkeep _ (by decide)]; exact h3
  · rw [hkeep _ (by decide)]; exact h4
  · rw [hkeep _ (by decide)]; exact h5
  · rw [hkeep _ (by decide)]; exact h6

/-- The bundle with two entries replaced, from a state's own lookups. -/
theorem B8Ctx.step {env : Env} {e o blk0 nblk ii kk ii' kk' : Nat}
    (h : B8Ctx env e o blk0 nblk ii kk)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 ii')))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk'))) :
    B8Ctx env e o blk0 nblk ii' kk' := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := h
  exact ⟨h1, h2, h3, h4, hi, hk⟩

/-- The state a finished tail hands the remainder guard. -/
def b8GuardState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "s1f_ke_b8.exit.loopexit.unr-lcssa", pre := some "while.body.i" }

/-- The state an iteration hands the next one. -/
def b8LoopState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "while.body.i", pre := some "while.body.i" }

/-- Composing the resets: the memory the guard state carries is the last one. -/
theorem b8GuardState_nested (s : State) (m1 m2 : Mem) :
    ({ ({ { s with mem := m1 } with mem := m2 }) with
        pc := "s1f_ke_b8.exit.loopexit.unr-lcssa", pre := some "while.body.i" } : State)
      = b8GuardState s m2 := rfl

theorem b8LoopState_nested (s : State) (m1 m2 : Mem) :
    ({ ({ { s with mem := m1 } with mem := m2 }) with pc := "while.body.i", pre := some "while.body.i" } : State)
      = b8LoopState s m2 := rfl

theorem b8GuardState_loop (s : State) (m1 m2 : Mem) :
    b8GuardState (b8LoopState s m1) m2 = b8GuardState s m2 := rfl

/-- Replacing a state's jump fields under an environment is replacing them inside. -/
theorem withEnv_jump (env' : Env) (s : State) (pc : String) (pre : Option String) :
    ({ (withEnv env' s) with pc := pc, pre := pre }) = withEnv env' { s with pc := pc, pre := pre } := rfl

/-- The unrolled tail loop's run, from the preheader's state to the remainder
guard's; `r` iterations remain at lane offset `jm`.  The lanes written are eight
per iteration from the same fold, and the four names the rest of the block reads
are carried through unchanged. -/
theorem b8TailMainLoop_run (w : BitVec 64) (e i blk0 k o : Nat) :
    ∀ (r : Nat), 1 ≤ r → ∀ (jm : Nat), jm + r = ctpop (clearLow w 8) / 8 →
    ∀ (env : Env) (s : State) (p : String) (opc opo opn : Operand) (mem0 : Mem)
      (kk ii nblk : Nat) (u : BitVec 64) (u11 : BitVec 64),
      s.pc = "while.body.i" →
      s.pre = some p →
      phiIncoming p b8IncomingC = some opc →
      phiIncoming p b8IncomingO = some opo →
      phiIncoming p b8IncomingN = some opn →
      evalOperand (withEnv env s) opc = some (.int 64 (clearLow w (8 + 8 * jm))) →
      evalOperand (withEnv (("%c.096.i", .int 64 (clearLow w (8 + 8 * jm))) :: env) s) opo
        = some (.ptr (o + 4 * k + 4 * (8 + 8 * jm))) →
      evalOperand (withEnv (("%o.addr.095.i", .ptr (o + 4 * k + 4 * (8 + 8 * jm))) ::
          ("%c.096.i", .int 64 (clearLow w (8 + 8 * jm))) :: env) s) opn
        = some (.int 64 (BitVec.ofNat 64 (8 * jm))) →
      lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) →
      lookupName env "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8)))) →
      8 * (ctpop (clearLow w 8) / 8) < 2 ^ 64 →
      s.mem = b8Lanes o w (posBase blk0 i) k 8 (8 * jm) mem0 →
      lookupName env "%xtraiter" = some (.int 64 u) →
      lookupName env "%11" = some (.int 64 u11) →
      B8Ctx env e o blk0 nblk ii kk →
      ∃ (env' : Env) (t' : State), Jumps entryB8Function r (withEnv env s) (withEnv env' t') ∧
        t' = b8GuardState s (b8Lanes o w (posBase blk0 i) k 8 (8 * (ctpop (clearLow w 8) / 8)) mem0) ∧
        lookupName env' "%and44.i.7" = some (.int 64 (clearLow w (8 + 8 * (ctpop (clearLow w 8) / 8)))) ∧
        lookupName env' "%incdec.ptr.i.7" = some (.ptr (o + 4 * k + 4 * (8 + 8 * (ctpop (clearLow w 8) / 8)))) ∧
        lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
        lookupName env' "%xtraiter" = some (.int 64 u) ∧
        lookupName env' "%11" = some (.int 64 u11) ∧
        B8Ctx env' e o blk0 nblk ii kk := by
  intro r
  induction r with
  | zero => intro h1; omega
  | succ r' ih =>
    intro hr jm hjm env s p opc opo opn mem0 kk ii nblk u u11 hpc hpre hopc hopo hopn
      hc ho hn hconv hunroll h64 hmem hxtra h11u hctx
    obtain ⟨M0, hM0def⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k 8 (8 * jm) mem0 :=
      ⟨_, rfl⟩
    obtain ⟨M4, hM4def⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k (8 + 8 * jm) 4 M0 :=
      ⟨_, rfl⟩
    obtain ⟨M8, hM8def⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k (8 + 8 * jm) 8 M0 :=
      ⟨_, rfl⟩
    obtain ⟨sB, hsBdef⟩ : ∃ s' : State, s' = { { s with mem := M4 } with mem := M8 } :=
      ⟨_, rfl⟩
    have hpcB : sB.pc = "while.body.i" := by rw [hsBdef]; exact hpc
    have hunroll' : lookupName env "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) := by
      rw [hunroll, unroll_val]
    obtain ⟨e1, hrun1, hand1, hgep1, hnext1, hcmp1, hconv1, hbase1, hunroll1⟩ :=
      b8LoopBody_run env s sB w i blk0 k o (8 + 8 * jm) (8 * jm) p opc opo opn
        M0 M4 M8 hpre hopc hopo hopn hc ho hn hconv hunroll' (by omega)
        (hmem.trans hM0def.symm) hM4def hM8def hsBdef
    have hstep := b8_step_of (withEnv env s) "while.body.i" b8TailLoop
      (withEnv e1 sB) hpc findBlock_b8TailLoop hrun1
    have hctx1 : B8Ctx e1 e o blk0 nblk ii kk :=
      hctx.transfer (b8_keep b8TailLoop.instrs (by decide) _ _ hrun1)
    have hxtra1 : lookupName e1 "%xtraiter" = some (.int 64 u) :=
      (denoteCode_lookupName entryCalls b8TailLoop.instrs "%xtraiter" (by decide)
        (withEnv env s) (withEnv e1 sB) hrun1).trans hxtra
    have h11u1 : lookupName e1 "%11" = some (.int 64 u11) :=
      (denoteCode_lookupName entryCalls b8TailLoop.instrs "%11" (by decide)
        (withEnv env s) (withEnv e1 sB) hrun1).trans h11u
    have hmem8 : M8 = b8Lanes o w (posBase blk0 i) k 8 (8 * jm + 8) mem0 := by
      rw [hM8def, hM0def]
      exact b8Lanes_step8 o w (posBase blk0 i) k jm mem0
    rcases Nat.eq_zero_or_pos r' with hr0 | hrpos
    · subst hr0
      have hidx : 8 * jm + 8 = 8 * (ctpop (clearLow w 8) / 8) := by omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (8 * jm + 8)
          = (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) = (1 : BitVec 1) := by
        rw [unroll_val, hidx]
        simp
      have hsB_guard : ({ sB with pc := "s1f_ke_b8.exit.loopexit.unr-lcssa", pre := some "while.body.i" }) = b8GuardState s M8 := by
        rw [hsBdef]
        exact b8GuardState_nested s M4 M8
      have hjump : step entryCalls entryB8Function (withEnv env s)
          = .jump (withEnv e1 (b8GuardState s M8)) := by
        rw [hstep]
        show execTerm (withEnv e1 sB) (.condbr (.reg "%niter.ncmp.7")
          "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.i") = _
        rw [execTerm_condbr_true (c := .reg "%niter.ncmp.7")
          (t := "s1f_ke_b8.exit.loopexit.unr-lcssa") (f := "while.body.i")
          (evalOperand_reg_of e1 sB "%niter.ncmp.7" (.int 1 _) hcmp1) hbit]
        have hpcW : (withEnv e1 sB).pc = "while.body.i" := hpcB
        rw [hpcW, withEnv_jump, hsB_guard]
      have hidx2 : 8 + 8 * jm + 8 = 8 + 8 * (ctpop (clearLow w 8) / 8) := by omega
      refine ⟨e1, b8GuardState s M8, Jumps.one hjump, ?_, ?_, ?_, hconv1, hxtra1, h11u1, hctx1⟩
      · rw [hM8def, hM0def, b8Lanes_step8, hidx]
      · simpa [hidx2] using hand1
      · simpa [hidx2] using hgep1
    · have hne : BitVec.ofNat 64 (8 * jm + 8) ≠ BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8)) := by
        intro hcon
        have := ofNat64_inj (a := 8 * jm + 8) (b := 8 * (ctpop (clearLow w 8) / 8))
          (by omega) (by omega) hcon
        omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (8 * jm + 8)
          = (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56)) = (0 : BitVec 1) := by
        rw [unroll_val,
          show decide (BitVec.ofNat 64 (8 * jm + 8)
            = BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8))) = false from decide_eq_false hne]
        rfl
      have hsB_loop : ({ sB with pc := "while.body.i", pre := some "while.body.i" }) = b8LoopState s M8 := by
        rw [hsBdef]
        exact b8LoopState_nested s M4 M8
      have hjump : step entryCalls entryB8Function (withEnv env s)
          = .jump (withEnv e1 (b8LoopState s M8)) := by
        rw [hstep]
        show execTerm (withEnv e1 sB) (.condbr (.reg "%niter.ncmp.7")
          "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.i") = _
        rw [execTerm_condbr_false (c := .reg "%niter.ncmp.7")
          (t := "s1f_ke_b8.exit.loopexit.unr-lcssa") (f := "while.body.i")
          (evalOperand_reg_of e1 sB "%niter.ncmp.7" (.int 1 _) hcmp1) hbit]
        have hpcW : (withEnv e1 sB).pc = "while.body.i" := hpcB
        rw [hpcW, withEnv_jump, hsB_loop]
      have hjm' : (jm + 1) + r' = ctpop (clearLow w 8) / 8 := by omega
      obtain ⟨e2, t2, hjumps, ht2, hand2, hgep2, hconv2, hxtra2, h11u2, hctx2⟩ :=
        ih hrpos (jm + 1) hjm' e1 (b8LoopState s M8)
          "while.body.i" (reg "%and44.i.7") (reg "%incdec.ptr.i.7") (reg "%niter.next.7")
          mem0 kk ii nblk u u11
          (by simp [b8LoopState]) (by simp [b8LoopState])
          (by simp [b8IncomingC, phiIncoming]) (by simp [b8IncomingO, phiIncoming])
          (by simp [b8IncomingN, phiIncoming])
          (evalOperand_reg_of e1 (b8LoopState s M8) "%and44.i.7"
            (.int 64 (clearLow w (8 + 8 * (jm + 1)))) (by
              rw [show 8 + 8 * (jm + 1) = 8 + 8 * jm + 8 from by omega]
              ent_auto))
          (evalOperand_reg_of (("%c.096.i", .int 64 (clearLow w (8 + 8 * (jm + 1)))) :: e1)
            (b8LoopState s M8) "%incdec.ptr.i.7"
            (.ptr (o + 4 * k + 4 * (8 + 8 * (jm + 1)))) (by
              rw [show 8 + 8 * (jm + 1) = 8 + 8 * jm + 8 from by omega]
              ent_auto))
          (evalOperand_reg_of (("%o.addr.095.i", .ptr (o + 4 * k + 4 * (8 + 8 * (jm + 1)))) ::
              ("%c.096.i", .int 64 (clearLow w (8 + 8 * (jm + 1)))) :: e1) (b8LoopState s M8)
            "%niter.next.7" (.int 64 (BitVec.ofNat 64 (8 * (jm + 1)))) (by
              rw [show 8 * (jm + 1) = 8 * jm + 8 from by omega]
              ent_auto))
          hconv1 (by rw [hunroll1, unroll_val]) h64
          (by rw [b8LoopState, show 8 * (jm + 1) = 8 * jm + 8 from by omega,
            hM8def, hM0def, b8Lanes_step8])
          hxtra1 h11u1 hctx1
      refine ⟨e2, t2, ?_, ?_, hand2, hgep2, hconv2, hxtra2, h11u2, hctx2⟩
      · rw [ht2, b8GuardState_loop]
        have h2 : Jumps entryB8Function r' (withEnv e1 (b8LoopState s M8))
            (withEnv e2 (b8GuardState s (b8Lanes o w (posBase blk0 i) k 8 (8 * (ctpop (clearLow w 8) / 8)) mem0))) := by
          rw [ht2, b8GuardState_loop] at hjumps
          exact hjumps
        have hc := Jumps.comp (Jumps.one hjump) h2
        simpa [Nat.add_comm] using hc
      · rw [ht2, b8GuardState_loop]

/-- The state a finished epilogue hands the join. -/
def b8JoinState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "s1f_ke_b8.exit", pre := some "while.body.i.epil" }

/-- The state an epilogue iteration hands the next one. -/
def b8EpilState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "while.body.i.epil", pre := some "while.body.i.epil" }

theorem b8JoinState_nested (s : State) (m m' : Mem) :
    ({ { s with mem := m } with mem := m', pc := "s1f_ke_b8.exit", pre := some "while.body.i.epil" })
      = b8JoinState s m' := rfl

theorem b8EpilState_nested (s : State) (m m' : Mem) :
    ({ { s with mem := m } with mem := m', pc := "while.body.i.epil", pre := some "while.body.i.epil" })
      = b8EpilState s m' := rfl

theorem b8JoinState_epil (s : State) (m1 m2 : Mem) :
    b8JoinState (b8EpilState s m1) m2 = b8JoinState s m2 := rfl

/-- The scalar epilogue's run: `r` iterations remain at tail index `e`, one lane
each, stopping when the trip counter reaches `%xtraiter = u`. -/
theorem b8TailEpilogue_run (w : BitVec 64) (ee oo : Nat) (i blk0 k jz : Nat) :
    ∀ (r : Nat), 1 ≤ r → ∀ (e u : Nat), e + r = u →
    ∀ (env : Env) (s : State) (p : String) (opcc opco opci : Operand) (mem0 : Mem)
      (kk ii nblk : Nat) (u11 : BitVec 64),
      s.pc = "while.body.i.epil" →
      s.pre = some p →
      phiIncoming p b8IncomingCe = some opcc →
      phiIncoming p b8IncomingOe = some opco →
      phiIncoming p b8IncomingIe = some opci →
      evalOperand (withEnv env s) opcc = some (.int 64 (clearLow w (jz + e))) →
      evalOperand (withEnv (("%c.096.i.epil", .int 64 (clearLow w (jz + e))) :: env) s) opco
        = some (.ptr (o + 4 * k + 4 * (jz + e))) →
      evalOperand (withEnv (("%o.addr.095.i.epil", .ptr (o + 4 * k + 4 * (jz + e))) ::
          ("%c.096.i.epil", .int 64 (clearLow w (jz + e))) :: env) s) opci
        = some (.int 64 (BitVec.ofNat 64 e)) →
      lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) →
      lookupName env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 u)) →
      u < 2 ^ 64 →
      s.mem = b8Lanes o w (posBase blk0 i) k jz e mem0 →
      lookupName env "%11" = some (.int 64 u11) →
      B8Ctx env ee oo blk0 nblk ii kk →
      ∃ (env' : Env) (t' : State),
        Jumps entryB8Function r (withEnv env s) (withEnv env' t') ∧
        t' = b8JoinState s (b8Lanes o w (posBase blk0 i) k jz u mem0) ∧
        lookupName env' "%11" = some (.int 64 u11) ∧
        B8Ctx env' ee oo blk0 nblk ii kk := by
  intro r
  induction r with
  | zero => intro h1; omega
  | succ r' ih =>
    intro hr e u heu env s p opcc opco opci mem0 kk ii nblk u11 hpc hpre hopc hopo hopi
      hc ho hi hconv hxtra hu64 hmem h11u hctx
    obtain ⟨M, hMdef⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k jz e mem0 := ⟨_, rfl⟩
    obtain ⟨M', hM'def⟩ : ∃ M' : Mem, M' = b8Lanes o w (posBase blk0 i) k (jz + e) 1 M := ⟨_, rfl⟩
    obtain ⟨sB, hsBdef⟩ : ∃ s' : State, s' = { s with mem := M' } := ⟨_, rfl⟩
    have hpcB : sB.pc = "while.body.i.epil" := by rw [hsBdef]; exact hpc
    have he64 : e + 1 < 2 ^ 64 := by
      have h1 : e + 1 ≤ u := by omega
      omega
    obtain ⟨e1, hrun1, hand1, hgep1, hnext1, hcmp1, hconv1, hxtra1⟩ :=
      b8EpilBody_run env s w i blk0 k o (jz + e) e p opcc opco opci M M'
        (BitVec.ofNat 64 u) hpre hopc hopo hopi hc ho hi hconv hxtra he64
        (hmem.trans hMdef.symm) hM'def
    rw [← hsBdef] at hrun1
    have hctx1 : B8Ctx e1 ee oo blk0 nblk ii kk :=
      hctx.transfer (b8_keep b8TailRemainder.instrs (by decide) _ _ hrun1)
    have h11u1 : lookupName e1 "%11" = some (.int 64 u11) :=
      (denoteCode_lookupName entryCalls b8TailRemainder.instrs "%11" (by decide)
        (withEnv env s) (withEnv e1 sB) hrun1).trans h11u
    have hstep := b8_step_of (withEnv env s) "while.body.i.epil" b8TailRemainder
      (withEnv e1 sB) hpc (by simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel,
        b8TailGuard, b8TailPreheader, b8TailUnrolled, b8TailLoop, b8TailRemainderGuard,
        b8TailRemainder, b8Join, b8Advance, Function.findBlock, findBlockList]) hrun1
    have hM' : M' = b8Lanes o w (posBase blk0 i) k jz (e + 1) mem0 := by
      rw [hM'def, hMdef]
      exact b8Lanes_step1 o w (posBase blk0 i) k jz e mem0
    rcases Nat.eq_zero_or_pos r' with hr0 | hrpos
    · subst hr0
      have heu : e + 1 = u := by omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (e + 1) = BitVec.ofNat 64 u) = (1 : BitVec 1) := by
        rw [heu]; simp
      have hsB_join : ({ sB with pc := "s1f_ke_b8.exit", pre := some "while.body.i.epil" }) = b8JoinState s M' := by
        rw [hsBdef]
        exact b8JoinState_nested s M M'
      have hjump : step entryCalls entryB8Function (withEnv env s)
          = .jump (withEnv e1 (b8JoinState s M')) := by
        rw [hstep]
        show execTerm (withEnv e1 sB) (.condbr (.reg "%epil.iter.cmp.not")
          "s1f_ke_b8.exit" "while.body.i.epil") = _
        rw [execTerm_condbr_true (c := .reg "%epil.iter.cmp.not")
          (t := "s1f_ke_b8.exit") (f := "while.body.i.epil")
          (evalOperand_reg_of e1 sB "%epil.iter.cmp.not" (.int 1 _) hcmp1) hbit]
        have hpcW : (withEnv e1 sB).pc = "while.body.i.epil" := hpcB
        rw [hpcW, withEnv_jump, hsB_join]
      refine ⟨e1, b8JoinState s M', Jumps.one hjump, ?_, h11u1, hctx1⟩
      rw [hM'def, hMdef, b8Lanes_step1, heu]
    · have hne : BitVec.ofNat 64 (e + 1) ≠ BitVec.ofNat 64 u := by
        intro hcon
        have := ofNat64_inj (a := e + 1) (b := u) (by omega) (by omega) hcon
        omega
      have hbit : BitVec.ofBool (BitVec.ofNat 64 (e + 1) = BitVec.ofNat 64 u) = (0 : BitVec 1) := by
        rw [show decide (BitVec.ofNat 64 (e + 1) = BitVec.ofNat 64 u) = false from decide_eq_false hne]
        rfl
      have hsB_epil : ({ sB with pc := "while.body.i.epil", pre := some "while.body.i.epil" }) = b8EpilState s M' := by
        rw [hsBdef]
        exact b8EpilState_nested s M M'
      have hjump : step entryCalls entryB8Function (withEnv env s)
          = .jump (withEnv e1 (b8EpilState s M')) := by
        rw [hstep]
        show execTerm (withEnv e1 sB) (.condbr (.reg "%epil.iter.cmp.not")
          "s1f_ke_b8.exit" "while.body.i.epil") = _
        rw [execTerm_condbr_false (c := .reg "%epil.iter.cmp.not")
          (t := "s1f_ke_b8.exit") (f := "while.body.i.epil")
          (evalOperand_reg_of e1 sB "%epil.iter.cmp.not" (.int 1 _) hcmp1) hbit]
        have hpcW : (withEnv e1 sB).pc = "while.body.i.epil" := hpcB
        rw [hpcW, withEnv_jump, hsB_epil]
      have heu' : (e + 1) + r' = u := by omega
      obtain ⟨e2, t2, hjumps, ht2, h11u2, hctx2⟩ :=
        ih hrpos (e + 1) u heu' e1 (b8EpilState s M') "while.body.i.epil"
          (reg "%and44.i.epil") (reg "%incdec.ptr.i.epil") (reg "%epil.iter.next") mem0
          kk ii nblk u11
          (by simp [b8EpilState]) (by simp [b8EpilState])
          (by simp [b8IncomingCe, phiIncoming]) (by simp [b8IncomingOe, phiIncoming])
          (by simp [b8IncomingIe, phiIncoming])
          (evalOperand_reg_of e1 (b8EpilState s M') "%and44.i.epil"
            (.int 64 (clearLow w (jz + (e + 1)))) (by
              rw [show jz + (e + 1) = jz + e + 1 from by omega]
              ent_auto))
          (evalOperand_reg_of (("%c.096.i.epil", .int 64 (clearLow w (jz + (e + 1)))) :: e1)
            (b8EpilState s M') "%incdec.ptr.i.epil"
            (.ptr (o + 4 * k + 4 * (jz + (e + 1)))) (by
              rw [show jz + (e + 1) = jz + e + 1 from by omega]
              ent_auto))
          (evalOperand_reg_of (("%o.addr.095.i.epil", .ptr (o + 4 * k + 4 * (jz + (e + 1)))) ::
              ("%c.096.i.epil", .int 64 (clearLow w (jz + (e + 1)))) :: e1) (b8EpilState s M')
            "%epil.iter.next" (.int 64 (BitVec.ofNat 64 (e + 1))) (by
              rw [show e + 1 = e + 1 from rfl]
              ent_auto))
          hconv1 hxtra1 hu64
          (by rw [b8EpilState]; exact hM')
          h11u1 hctx1
      refine ⟨e2, t2, ?_, ?_, h11u2, hctx2⟩
      · rw [ht2, b8JoinState_epil]
        have h2 : Jumps entryB8Function r' (withEnv e1 (b8EpilState s M'))
            (withEnv e2 (b8JoinState s (b8Lanes o w (posBase blk0 i) k jz u mem0))) := by
          rw [ht2, b8JoinState_epil] at hjumps
          exact hjumps
        have hc := Jumps.comp (Jumps.one hjump) h2
        simpa [Nat.add_comm] using hc
      · rw [ht2, b8JoinState_epil]


/-- The state a block hands `cleanup`. -/
def b8CleanupState (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "cleanup", pre := some "s1f_ke_b8.exit" }

theorem b8CleanupState_of (s : State) (m m' : Mem) :
    ({ b8JoinState s m with mem := m', pc := "cleanup", pre := some "s1f_ke_b8.exit" })
      = b8CleanupState s m' := rfl

/-- The eight fixed slots and the tail's lanes are one fold from the cursor. -/
theorem b8Tail_mem (o : Nat) (w : BitVec 64) (base k : Nat) (M : Mem) :
    b8Lanes o w base k 8 (ctpop (clearLow w 8)) (b8Lanes o w base k 0 8 M)
      = b8Lanes o w base k 0 (slotCount w) M := by
  rw [show slotCount w = 8 + ctpop (clearLow w 8) from rfl,
    ← b8Lanes_split o w base k 0 8 (ctpop (clearLow w 8)) M]




/-- The state entering the epilogue, from a named predecessor. -/
def b8EpilStart (s : State) (pred : String) : State :=
  { s with pc := "while.body.i.epil", pre := some pred }

/-- The state entering the join, from a named predecessor. -/
def b8JoinStart (s : State) (pred : String) : State :=
  { s with pc := "s1f_ke_b8.exit", pre := some pred }

theorem b8CleanupState_of_joinState (s : State) (M : Mem) :
    ({ b8JoinState s M with pc := "cleanup", pre := some "s1f_ke_b8.exit" })
      = b8CleanupState s M := rfl

theorem b8CleanupState_epilStart (s : State) (M : Mem) (pred : String) :
    b8CleanupState (b8EpilStart s pred) M = b8CleanupState s M := rfl

theorem b8CleanupState_of_joinStart (s : State) (pred : String) :
    ({ b8JoinStart s pred with pc := "cleanup", pre := some "s1f_ke_b8.exit" })
      = b8CleanupState s s.mem := rfl

theorem b8GuardState_pc (s : State) (M : Mem) :
    (b8GuardState s M).pc = "s1f_ke_b8.exit.loopexit.unr-lcssa" := rfl

theorem b8GuardState_pre (s : State) (M : Mem) : (b8GuardState s M).pre = some "while.body.i" := rfl

theorem b8CleanupState_guard (s : State) (M M' : Mem) :
    b8CleanupState (b8GuardState s M) M' = b8CleanupState s M' := rfl

/-- `%xtraiter`'s mask, read back: the low three lanes of the tail count. -/
theorem and7_ofNat (n : Nat) :
    BitVec.ofNat 64 n &&& BitVec.ofInt 64 7 = BitVec.ofNat 64 (n % 8) := by
  rw [show (BitVec.ofInt 64 7 : BitVec 64) = BitVec.ofNat 64 7 from by decide, ← BitVec.ofNat_and,
    show (n &&& 7) = n % 8 from by
      rw [show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]]

/-- The preheader's `%13 < 8` test, taken as the branch it selects. -/
theorem ult8_true (n : Nat) (hn : n < 2 ^ 64) (h : n < 8) :
    BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofInt 64 8) = true := by
  rw [show (BitVec.ofInt 64 8 : BitVec 64) = BitVec.ofNat 64 8 from by decide]
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show 8 < 2^64 by decide)]
  exact decide_eq_true h

theorem ult8_false (n : Nat) (hn : n < 2 ^ 64) (h : 8 ≤ n) :
    BitVec.ult (BitVec.ofNat 64 n) (BitVec.ofInt 64 8) = false := by
  rw [show (BitVec.ofInt 64 8 : BitVec 64) = BitVec.ofNat 64 8 from by decide]
  rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (show 8 < 2^64 by decide)]
  exact decide_eq_false (by omega)

/-- The remainder guard and the scalar epilogue, from the guard's state to
`cleanup`: `u` lanes from tail offset `jz`, and the last `jz + u` lanes of the
block are exactly its `slotCount`. -/
theorem b8Tail_rest (w : BitVec 64) (ee i blk0 k o jz : Nat) (env : Env) (s : State)
    (M0 : Mem) (nblk ii kk : Nat) (p : String) (opc opo : Operand) (u : Nat)
    (hpc : s.pc = "s1f_ke_b8.exit.loopexit.unr-lcssa")
    (hpre : s.pre = some p)
    (hopc : phiIncoming p b8IncomingCu = some opc)
    (hopo : phiIncoming p b8IncomingOu = some opo)
    (hc : evalOperand (withEnv env s) opc = some (.int 64 (clearLow w jz)))
    (ho : evalOperand (withEnv (("%c.096.i.unr", .int 64 (clearLow w jz)) :: env) s) opo
            = some (.ptr (o + 4 * k + 4 * jz)))
    (hxtra : lookupName env "%xtraiter" = some (.int 64 (BitVec.ofNat 64 u)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hu64 : u < 2 ^ 64)
    (hsum : ctpop w + kk < 2 ^ 64)
    (hjzu : jz + u = slotCount w)
    (hm : s.mem = b8Lanes o w (posBase blk0 i) k 0 jz M0)
    (h11env : lookupName env "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))))
    (hctx : B8Ctx env ee o blk0 nblk ii kk) :
    ∃ (env' : Env),
      Jumps entryB8Function (2 + u) (withEnv env s)
        (withEnv env' (b8CleanupState s (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0))) ∧
      lookupName env' "%add1" = some (.int 64 (BitVec.ofNat 64 (ctpop w + kk))) ∧
      B8Ctx env' ee o blk0 nblk ii kk := by
  obtain ⟨e1, hbody1, hc1, ho1, hlcm⟩ := b8RemainderGuard_run env s w k o jz p opc opo
    (BitVec.ofNat 64 u) hpre hopc hopo hc ho hxtra
  have hctx1 : B8Ctx e1 ee o blk0 nblk ii kk :=
    hctx.transfer (b8_keep _ (by decide) _ _ hbody1)
  have h11e1 : lookupName e1 "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) :=
    (denoteCode_lookupName entryCalls b8TailRemainderGuard.instrs "%11" (by decide)
      (withEnv env s) (withEnv e1 s) hbody1).trans h11env
  have hconv1 : lookupName e1 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
    (denoteCode_lookupName entryCalls b8TailRemainderGuard.instrs "%conv" (by decide)
      (withEnv env s) (withEnv e1 s) hbody1).trans hconv
  have hxtra1 : lookupName e1 "%xtraiter" = some (.int 64 (BitVec.ofNat 64 u)) :=
    (denoteCode_lookupName entryCalls b8TailRemainderGuard.instrs "%xtraiter" (by decide)
      (withEnv env s) (withEnv e1 s) hbody1).trans hxtra
  have hstep1 := b8_step_of (withEnv env s) "s1f_ke_b8.exit.loopexit.unr-lcssa"
    b8TailRemainderGuard (withEnv e1 s) hpc findBlock_b8RemainderGuard hbody1
  by_cases hu0 : u = 0
  · -- no epilogue: the guard jumps straight to the join
    subst hu0
    have hbit : BitVec.ofBool (BitVec.ofNat 64 0 = BitVec.ofInt 64 0) = (1 : BitVec 1) := by
      rw [ofInt64_zero]
      rfl
    have hjump1 : step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) := by
      rw [hstep1]
      show execTerm (withEnv e1 s) (.condbr (.reg "%lcmp.mod.not") "s1f_ke_b8.exit" "while.body.i.epil") = _
      rw [execTerm_condbr_true (c := .reg "%lcmp.mod.not") (t := "s1f_ke_b8.exit")
        (f := "while.body.i.epil")
        (evalOperand_reg_of e1 s "%lcmp.mod.not" (.int 1 _) hlcm) hbit]
      rw [show (withEnv e1 s).pc = "s1f_ke_b8.exit.loopexit.unr-lcssa" from hpc]
      rw [withEnv_jump]
      rfl
    obtain ⟨e2, hjoin2, hadd1⟩ := b8Join_run e1
      (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa") (ctpop w) kk
      "s1f_ke_b8.exit.loopexit.unr-lcssa" (reg "%11") rfl
      (by simp [b8IncomingR, phiIncoming])
      (evalOperand_reg_of e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa") "%11"
        (.int 64 (BitVec.ofNat 64 (ctpop w))) h11e1)
      (by show lookupName e1 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk))
          exact hctx1.2.2.2.2.2)
      hsum
    have hctx2 : B8Ctx e2 ee o blk0 nblk ii kk :=
      hctx1.transfer (b8_keep _ (by decide) _ _ hjoin2)
    have hstep2 := b8_step_of (withEnv e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa"))
      "s1f_ke_b8.exit" b8Join (withEnv e2 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) rfl
      findBlock_b8Join hjoin2
    have hjump2 : step entryCalls entryB8Function (withEnv e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa"))
        = .jump (withEnv e2 (b8CleanupState s s.mem)) := by
      rw [hstep2]
      show execTerm (withEnv e2 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) (.br "cleanup") = _
      rw [execTerm_br]
      rw [withEnv_jump]
      rfl
    refine ⟨e2, ?_, hadd1, hctx2⟩
    have hJ1 : Jumps entryB8Function 1 (withEnv env s)
        (withEnv e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) :=
      Jumps.one hjump1
    have hJ2 : Jumps entryB8Function 1 (withEnv e1 (b8JoinStart s "s1f_ke_b8.exit.loopexit.unr-lcssa"))
        (withEnv e2 (b8CleanupState s s.mem)) := Jumps.one hjump2
    have hB := Jumps.comp hJ1 hJ2
    have hmem : s.mem = b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0 := by
      rw [hm, ← hjzu]
      rfl
    rw [hmem] at hB
    simpa using hB
  · -- the epilogue runs `u` times
    have hupos : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr hu0
    have hbit : BitVec.ofBool (BitVec.ofNat 64 u = BitVec.ofInt 64 0) = (0 : BitVec 1) := by
      rw [ofInt64_zero]
      rw [show decide (BitVec.ofNat 64 u = 0) = false from
        decide_eq_false (by
          intro hcon
          have h2 : u = 0 := by
            have h3 := congrArg BitVec.toNat hcon
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu64] at h3
            simpa using h3
          omega)]
      rfl
    have hjump1 : step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv e1 (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) := by
      rw [hstep1]
      show execTerm (withEnv e1 s) (.condbr (.reg "%lcmp.mod.not") "s1f_ke_b8.exit" "while.body.i.epil") = _
      rw [execTerm_condbr_false (c := .reg "%lcmp.mod.not") (t := "s1f_ke_b8.exit")
        (f := "while.body.i.epil")
        (evalOperand_reg_of e1 s "%lcmp.mod.not" (.int 1 _) hlcm) hbit]
      rw [show (withEnv e1 s).pc = "s1f_ke_b8.exit.loopexit.unr-lcssa" from hpc]
      rw [withEnv_jump]
      rfl
    obtain ⟨e2, t2, hjumps2, ht2, h11e2, hctx2⟩ :=
      b8TailEpilogue_run w ee o i blk0 k jz u hupos 0 u (by omega) e1
        (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")
        "s1f_ke_b8.exit.loopexit.unr-lcssa" (reg "%c.096.i.unr") (reg "%o.addr.095.i.unr")
        (lit 64 0) (b8Lanes o w (posBase blk0 i) k 0 jz M0) kk ii nblk
        (BitVec.ofNat 64 (ctpop w))
        rfl rfl
        (by simp [b8IncomingCe, phiIncoming]) (by simp [b8IncomingOe, phiIncoming])
        (by simp [b8IncomingIe, phiIncoming])
        (by
          show evalOperand (withEnv e1 (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) (reg "%c.096.i.unr")
            = some (.int 64 (clearLow w (jz + 0)))
          rw [show jz + 0 = jz from rfl]
          exact evalOperand_reg_of e1 s "%c.096.i.unr" (.int 64 (clearLow w jz)) hc1)
        (by
          show evalOperand (withEnv (("%c.096.i.unr", .int 64 (clearLow w jz)) :: e1)
            (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) (reg "%o.addr.095.i.unr")
            = some (.ptr (o + 4 * k + 4 * (jz + 0)))
          rw [show jz + 0 = jz from rfl]
          exact evalOperand_reg_of (("%c.096.i.unr", .int 64 (clearLow w jz)) :: e1) s
            "%o.addr.095.i.unr" (.ptr (o + 4 * k + 4 * jz))
            (by rw [lookupName_cons_ne _ _ (by decide)]; exact ho1))
        (by rfl)
        hconv1 hxtra1 hu64
        (by
          show s.mem = b8Lanes o w (posBase blk0 i) k jz 0 (b8Lanes o w (posBase blk0 i) k 0 jz M0)
          rw [hm]
          rfl)
        h11e1 hctx1
    obtain ⟨M1, hM1⟩ : ∃ M : Mem,
        M = b8Lanes o w (posBase blk0 i) k jz u (b8Lanes o w (posBase blk0 i) k 0 jz M0) := ⟨_, rfl⟩
    obtain ⟨MF, hMF⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0 := ⟨_, rfl⟩
    have ht2' : t2 = b8JoinState (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa") M1 := by
      rw [ht2, hM1]
    have hsplit : M1 = MF := by
      rw [hM1, hMF]
      have h1 := b8Lanes_split o w (posBase blk0 i) k 0 jz u M0
      rw [show (0 + jz) = jz from Nat.zero_add jz] at h1
      rw [← h1, hjzu]
    obtain ⟨e3, hjoin3, hadd1⟩ := b8Join_run e2 t2 (ctpop w) kk "while.body.i.epil" (reg "%11")
      (by rw [ht2']; rfl) (by simp [b8IncomingR, phiIncoming])
      (evalOperand_reg_of e2 t2 "%11" (.int 64 (BitVec.ofNat 64 (ctpop w))) h11e2)
      (by show lookupName e2 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk))
          exact hctx2.2.2.2.2.2)
      hsum
    have hctx3 : B8Ctx e3 ee o blk0 nblk ii kk :=
      hctx2.transfer (b8_keep _ (by decide) _ _ hjoin3)
    have hstep3 := b8_step_of (withEnv e2 t2) "s1f_ke_b8.exit" b8Join (withEnv e3 t2)
      (by rw [ht2']; rfl) findBlock_b8Join hjoin3
    have hMF1 : b8CleanupState s M1 = b8CleanupState s MF := by rw [hsplit]
    have hjump3 : step entryCalls entryB8Function (withEnv e2 t2)
        = .jump (withEnv e3 (b8CleanupState s MF)) := by
      rw [hstep3]
      show execTerm (withEnv e3 t2) (.br "cleanup") = _
      rw [execTerm_br]
      rw [show (withEnv e3 t2).pc = "s1f_ke_b8.exit" from by rw [ht2']; rfl]
      rw [withEnv_jump]
      rw [show ({ t2 with pc := "cleanup", pre := some "s1f_ke_b8.exit" } : State)
        = b8CleanupState s MF from by
        rw [ht2', b8CleanupState_of_joinState, b8CleanupState_epilStart, hMF1]]
    refine ⟨e3, ?_, hadd1, hctx3⟩
    have hJ1 : Jumps entryB8Function 1 (withEnv env s)
        (withEnv e1 (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) :=
      Jumps.one hjump1
    have hJ2 : Jumps entryB8Function u
        (withEnv e1 (b8EpilStart s "s1f_ke_b8.exit.loopexit.unr-lcssa")) (withEnv e2 t2) := hjumps2
    have hJ3 : Jumps entryB8Function 1 (withEnv e2 t2) (withEnv e3 (b8CleanupState s MF)) :=
      Jumps.one hjump3
    have hA := Jumps.comp hJ1 hJ2
    have hB := Jumps.comp hA hJ3
    rw [hMF] at hB
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hB

/-- The preheader's entry state. -/
def b8PreState (s : State) : State :=
  { s with pc := "while.body.preheader.i", pre := some "if.end39.i" }

/-- The unrolled preheader's entry state. -/
def b8UnrState (s : State) : State :=
  { s with pc := "while.body.preheader.i.new", pre := some "while.body.preheader.i" }

/-- The unrolled loop's entry state. -/
def b8MainState (s : State) : State :=
  { s with pc := "while.body.i", pre := some "while.body.preheader.i.new" }

theorem b8CleanupState_mainState (s : State) (M : Mem) :
    b8CleanupState (b8MainState s) M = b8CleanupState s M := rfl

/-- The remainder guard's entry state, from the preheader. -/
def b8RemPreState (s : State) : State :=
  { s with pc := "s1f_ke_b8.exit.loopexit.unr-lcssa", pre := some "while.body.preheader.i" }

/-- The tail's step count: the guard and preheader, then either the epilogue
alone or the unrolled loop and the epilogue's remainder. -/
def b8TailSteps (w : BitVec 64) : Nat :=
  if ctpop (clearLow w 8) / 8 = 0 then 4 + ctpop (clearLow w 8)
  else 5 + ctpop (clearLow w 8) / 8 + ctpop (clearLow w 8) % 8

theorem b8TailSteps_short (w : BitVec 64) (h : ctpop (clearLow w 8) / 8 = 0) :
    b8TailSteps w = 4 + ctpop (clearLow w 8) := by
  unfold b8TailSteps
  rw [ite_eq_left h]

theorem b8TailSteps_long (w : BitVec 64) (h : ¬ ctpop (clearLow w 8) / 8 = 0) :
    b8TailSteps w = 5 + ctpop (clearLow w 8) / 8 + ctpop (clearLow w 8) % 8 := by
  unfold b8TailSteps
  rw [ite_eq_right h]

/-- **The tail of a long word.**  From the guard's state to `cleanup`: the
unrolled loop writes eight lanes an iteration and the epilogue one, so the block
ends with exactly its `slotCount` lanes written and the cursor advanced by the
word's population count. -/
theorem b8Tail_run (w : BitVec 64) (ee i blk0 k o : Nat) (env : Env) (s : State)
    (M0 : Mem) (nblk ii kk : Nat)
    (hpc : s.pc = "if.end39.i")
    (hpop : 9 ≤ ctpop w)
    (hand : lookupName env "%and31.i" = some (.int 64 (clearLow w 7)))
    (hptr : lookupName env "%add.ptr" = some (.ptr (o + 4 * k)))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hsum : ctpop w + kk < 2 ^ 64)
    (hm : s.mem = b8Lanes o w (posBase blk0 i) k 0 8 M0)
    (hctx : B8Ctx env ee o blk0 nblk ii kk) :
    ∃ (env' : Env),
      Jumps entryB8Function (b8TailSteps w) (withEnv env s)
        (withEnv env' (b8CleanupState s (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0))) ∧
      lookupName env' "%add1" = some (.int 64 (BitVec.ofNat 64 (ctpop w + kk))) ∧
      B8Ctx env' ee o blk0 nblk ii kk := by
  have hn64 : ctpop (clearLow w 8) < 2 ^ 64 := by
    have := ctpop_le (clearLow w 8); omega
  have hne : clearLow w 8 ≠ 0 := by
    intro h0
    have h1 : ctpop (clearLow w 8) = 0 := by rw [h0, ctpop_zero64]
    rw [ctpop_clearLow] at h1
    omega
  -- the guard
  obtain ⟨e1, hbody1, h10, h11, hand36, h12⟩ := b8TailGuard_run env s w hand
  have h11e : lookupName e1 "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) := by
    rw [h11, b8_tail_count w hpop]
  have hctx1 : B8Ctx e1 ee o blk0 nblk ii kk :=
    hctx.transfer (b8_keep _ (by decide) _ _ hbody1)
  have hptr1 : lookupName e1 "%add.ptr" = some (.ptr (o + 4 * k)) :=
    (denoteCode_lookupName entryCalls b8TailGuard.instrs "%add.ptr" (by decide)
      (withEnv env s) (withEnv e1 s) hbody1).trans hptr
  have hconv1 : lookupName e1 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
    (denoteCode_lookupName entryCalls b8TailGuard.instrs "%conv" (by decide)
      (withEnv env s) (withEnv e1 s) hbody1).trans hconv
  have h12' : lookupName e1 "%12" = some (.int 1 0) := by
    rw [h12]
    rw [show BitVec.ofBool (clearLow w 8 = 0) = (0 : BitVec 1) from by
      rw [show decide (clearLow w 8 = 0) = false from decide_eq_false hne]; rfl]
  have hjump1 : step entryCalls entryB8Function (withEnv env s)
      = .jump (withEnv e1 (b8PreState s)) := by
    rw [b8_step_of (withEnv env s) "if.end39.i" b8TailGuard (withEnv e1 s) hpc
      findBlock_b8TailGuard hbody1]
    show execTerm (withEnv e1 s) (.condbr (.reg "%12") "s1f_ke_b8.exit" "while.body.preheader.i") = _
    rw [execTerm_condbr_false (c := .reg "%12") (t := "s1f_ke_b8.exit")
      (f := "while.body.preheader.i")
      (evalOperand_reg_of e1 s "%12" (.int 1 0) h12') rfl]
    rw [withEnv_jump, show (withEnv e1 s).pc = "if.end39.i" from hpc]
    rfl
  by_cases hlt8 : ctpop (clearLow w 8) < 8
  · -- the tail fits below eight lanes: the epilogue alone
    have hult := ult8_true (ctpop (clearLow w 8)) hn64 hlt8
    obtain ⟨e2, hbody2, hptri, hxtra, h13⟩ :=
      b8TailPreheader_run e1 (b8PreState s) w k o 1 hptr1 h10
    have hctx2 : B8Ctx e2 ee o blk0 nblk ii kk :=
      hctx1.transfer (b8_keep _ (by decide) _ _ hbody2)
    have hconv2 : lookupName e2 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%conv" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans hconv1
    have h11e2 : lookupName e2 "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%11" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans h11e
    have hjump2 : step entryCalls entryB8Function (withEnv e1 (b8PreState s))
        = .jump (withEnv e2 (b8RemPreState s)) := by
      rw [b8_step_of (withEnv e1 (b8PreState s)) "while.body.preheader.i" b8TailPreheader
        (withEnv e2 (b8PreState s)) rfl findBlock_b8TailPreheader hbody2]
      show execTerm (withEnv e2 (b8PreState s))
        (.condbr (.reg "%13") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.preheader.i.new") = _
      rw [execTerm_condbr_true (c := .reg "%13") (t := "s1f_ke_b8.exit.loopexit.unr-lcssa")
        (f := "while.body.preheader.i.new")
        (evalOperand_reg_of e2 (b8PreState s) "%13" (.int 1 1) (by
          show lookupName e2 "%13" = some (.int 1 1)
          rw [h13, hult]; rfl)) rfl]
      rw [withEnv_jump]
      rfl
    have hxtra' : lookupName e2 "%xtraiter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))) := by
      rw [hxtra, and7_ofNat, Nat.mod_eq_of_lt hlt8]
    obtain ⟨e3, hJumps3, hadd1, hctx3⟩ :=
      b8Tail_rest w ee i blk0 k o 8 e2 (b8RemPreState s) M0 nblk ii kk
        "while.body.preheader.i" (reg "%and36.i") (reg "%add.ptr.i") (ctpop (clearLow w 8))
        rfl rfl
        (by simp [b8IncomingCu, phiIncoming]) (by simp [b8IncomingOu, phiIncoming])
        (evalOperand_reg_of e2 (b8RemPreState s) "%and36.i" (.int 64 (clearLow w 8))
          ((denoteCode_lookupName entryCalls b8TailPreheader.instrs "%and36.i" (by decide)
            (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans hand36))
        (by
          show evalOperand (withEnv (("%c.096.i.unr", .int 64 (clearLow w 8)) :: e2)
            (b8RemPreState s)) (reg "%add.ptr.i") = some (.ptr (o + 4 * k + 4 * 8))
          rw [show 4 * 8 = 32 from rfl]
          exact evalOperand_reg_of (("%c.096.i.unr", .int 64 (clearLow w 8)) :: e2) s
            "%add.ptr.i" (.ptr (o + 4 * k + 32))
            (by rw [lookupName_cons_ne _ _ (by decide)]; exact hptri))
        hxtra' hconv2 (by omega) hsum
        (by rw [show slotCount w = 8 + ctpop (clearLow w 8) from rfl])
        (by show s.mem = b8Lanes o w (posBase blk0 i) k 0 8 M0; exact hm)
        h11e2 hctx2
    refine ⟨e3, ?_, hadd1, hctx3⟩
    have hA := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
    have hB := Jumps.comp hA hJumps3
    rw [b8TailSteps_short w (by omega)]
    have hcnt : 1 + 1 + (2 + ctpop (clearLow w 8)) = 4 + ctpop (clearLow w 8) := by omega
    rw [hcnt] at hB
    exact hB
  · -- the unrolled loop runs, then the epilogue's remainder
    have hge8 : 8 ≤ ctpop (clearLow w 8) := by omega
    have hult := ult8_false (ctpop (clearLow w 8)) hn64 hge8
    obtain ⟨e2, hbody2, hptri, hxtra, h13⟩ :=
      b8TailPreheader_run e1 (b8PreState s) w k o 0 hptr1 h10
    have h11e2 : lookupName e2 "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%11" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans h11e
    have hctx2 : B8Ctx e2 ee o blk0 nblk ii kk :=
      hctx1.transfer (b8_keep _ (by decide) _ _ hbody2)
    have hconv2 : lookupName e2 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%conv" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans hconv1
    have hptr2 : lookupName e2 "%add.ptr.i" = some (.ptr (o + 4 * k + 32)) := hptri
    have h10_2 : lookupName e2 "%10" = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)))) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%10" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans h10
    have hand36_2 : lookupName e2 "%and36.i" = some (.int 64 (clearLow w 8)) :=
      (denoteCode_lookupName entryCalls b8TailPreheader.instrs "%and36.i" (by decide)
        (withEnv e1 (b8PreState s)) (withEnv e2 (b8PreState s)) hbody2).trans hand36
    have hjump2 : step entryCalls entryB8Function (withEnv e1 (b8PreState s))
        = .jump (withEnv e2 (b8UnrState s)) := by
      rw [b8_step_of (withEnv e1 (b8PreState s)) "while.body.preheader.i" b8TailPreheader
        (withEnv e2 (b8PreState s)) rfl findBlock_b8TailPreheader hbody2]
      show execTerm (withEnv e2 (b8PreState s))
        (.condbr (.reg "%13") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.preheader.i.new") = _
      rw [execTerm_condbr_false (c := .reg "%13") (t := "s1f_ke_b8.exit.loopexit.unr-lcssa")
        (f := "while.body.preheader.i.new")
        (evalOperand_reg_of e2 (b8PreState s) "%13" (.int 1 0) (by
          show lookupName e2 "%13" = some (.int 1 0)
          rw [h13, hult]; rfl)) rfl]
      rw [withEnv_jump]
      rfl
    -- the unrolled preheader
    obtain ⟨e3, hbody3, hunroll⟩ := b8TailUnrolled_run e2 (b8UnrState s) w h10_2
    have h11e3 : lookupName e3 "%11" = some (.int 64 (BitVec.ofNat 64 (ctpop w))) :=
      (denoteCode_lookupName entryCalls b8TailUnrolled.instrs "%11" (by decide)
        (withEnv e2 (b8UnrState s)) (withEnv e3 (b8UnrState s)) hbody3).trans h11e2
    have hctx3 : B8Ctx e3 ee o blk0 nblk ii kk :=
      hctx2.transfer (b8_keep _ (by decide) _ _ hbody3)
    have hconv3 : lookupName e3 "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) :=
      (denoteCode_lookupName entryCalls b8TailUnrolled.instrs "%conv" (by decide)
        (withEnv e2 (b8UnrState s)) (withEnv e3 (b8UnrState s)) hbody3).trans hconv2
    have hjump3 : step entryCalls entryB8Function (withEnv e2 (b8UnrState s))
        = .jump (withEnv e3 (b8MainState s)) := by
      rw [b8_step_of (withEnv e2 (b8UnrState s)) "while.body.preheader.i.new" b8TailUnrolled
        (withEnv e3 (b8UnrState s)) rfl findBlock_b8TailUnrolled hbody3]
      show execTerm (withEnv e3 (b8UnrState s)) (.br "while.body.i") = _
      rw [execTerm_br]
      rw [withEnv_jump]
      rfl
    -- the unrolled loop
    have hunroll' : lookupName e3 "%unroll_iter"
        = some (.int 64 (BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8)))) := by
      have h : BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 56
          = BitVec.ofNat 64 (8 * (ctpop (clearLow w 8) / 8)) := by
        have hlt : ctpop (clearLow w 8) < 64 := by rw [ctpop_clearLow]; have := ctpop_le w; omega
        rw [show (BitVec.ofInt 64 56 : BitVec 64) = BitVec.ofNat 64 56 from by decide,
          ← BitVec.ofNat_and, land56 (ctpop (clearLow w 8)) hlt]
      rw [hunroll, h]
    obtain ⟨e4, t4, hJumps4, ht4, hand4, hgep4, hconv4, hxtra4raw, h11e4, hctx4⟩ :=
      b8TailMainLoop_run w ee i blk0 k o (ctpop (clearLow w 8) / 8) (by omega) 0
        (by rw [Nat.zero_add])
        e3 (b8MainState s) "while.body.preheader.i.new"
        (reg "%and36.i") (reg "%add.ptr.i") (lit 64 0)
        (b8Lanes o w (posBase blk0 i) k 0 8 M0) kk ii nblk
        (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 7)
        (BitVec.ofNat 64 (ctpop w))
        rfl rfl
        (by simp [b8IncomingC, phiIncoming]) (by simp [b8IncomingO, phiIncoming])
        (by simp [b8IncomingN, phiIncoming])
        (evalOperand_reg_of e3 (b8MainState s) "%and36.i" (.int 64 (clearLow w 8)) (by
          rw [show lookupName e3 "%and36.i" = lookupName e2 "%and36.i" from
            denoteCode_lookupName entryCalls b8TailUnrolled.instrs "%and36.i" (by decide)
              (withEnv e2 (b8UnrState s)) (withEnv e3 (b8UnrState s)) hbody3]
          exact hand36_2))
        (by
          show evalOperand (withEnv (("%c.096.i", .int 64 (clearLow w 8)) :: e3) (b8MainState s))
            (reg "%add.ptr.i") = some (.ptr (o + 4 * k + 4 * (8 + 8 * 0)))
          rw [show 8 + 8 * 0 = 8 from rfl, show 4 * 8 = 32 from rfl]
          exact evalOperand_reg_of (("%c.096.i", .int 64 (clearLow w 8)) :: e3) s
            "%add.ptr.i" (.ptr (o + 4 * k + 32))
            (by rw [lookupName_cons_ne _ _ (by decide)]
                rw [show lookupName e3 "%add.ptr.i" = some (.ptr (o + 4 * k + 32)) from by
                  rw [show lookupName e3 "%add.ptr.i" = lookupName e2 "%add.ptr.i" from
                    denoteCode_lookupName entryCalls b8TailUnrolled.instrs "%add.ptr.i" (by decide)
                      (withEnv e2 (b8UnrState s)) (withEnv e3 (b8UnrState s)) hbody3]
                  exact hptr2]))
        (by
          show evalOperand (withEnv _ (b8MainState s)) (.imm (.int 64 (BitVec.ofInt 64 0)))
            = some (.int 64 (BitVec.ofNat 64 0))
          rw [ofInt64_zero]
          rfl)
        hconv3 hunroll' (by omega)
        (by show s.mem = b8Lanes o w (posBase blk0 i) k 8 0 (b8Lanes o w (posBase blk0 i) k 0 8 M0)
            rw [hm]; rfl)
        (by
          show lookupName e3 "%xtraiter"
            = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8)) &&& BitVec.ofInt 64 7))
          exact (denoteCode_lookupName entryCalls b8TailUnrolled.instrs "%xtraiter" (by decide)
            (withEnv e2 (b8UnrState s)) (withEnv e3 (b8UnrState s)) hbody3).trans hxtra)
        h11e3 hctx3
    -- the remainder guard and the epilogue
    obtain ⟨MF, hMF⟩ : ∃ M : Mem, M = b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0 := ⟨_, rfl⟩
    have hxtra4 : lookupName e4 "%xtraiter"
        = some (.int 64 (BitVec.ofNat 64 (ctpop (clearLow w 8) % 8))) := by
      rw [hxtra4raw, and7_ofNat]
    have hmem4 : t4.mem
        = b8Lanes o w (posBase blk0 i) k 0 (8 + 8 * (ctpop (clearLow w 8) / 8)) M0 := by
      rw [ht4]
      exact (b8Lanes_split o w (posBase blk0 i) k 0 8 (8 * (ctpop (clearLow w 8) / 8)) M0).symm
    have hjzu4 : 8 + 8 * (ctpop (clearLow w 8) / 8) + ctpop (clearLow w 8) % 8 = slotCount w := by
      rw [show slotCount w = 8 + ctpop (clearLow w 8) from rfl]
      have h := Nat.mod_add_div (ctpop (clearLow w 8)) 8
      omega
    obtain ⟨e5, hJumps5, hadd1, hctx5⟩ :=
      b8Tail_rest w ee i blk0 k o (8 + 8 * (ctpop (clearLow w 8) / 8)) e4 t4 M0 nblk ii kk
        "while.body.i" (reg "%and44.i.7") (reg "%incdec.ptr.i.7") (ctpop (clearLow w 8) % 8)
        (by rw [ht4]; exact b8GuardState_pc _ _) (by rw [ht4]; exact b8GuardState_pre _ _)
        (by simp [b8IncomingCu, phiIncoming]) (by simp [b8IncomingOu, phiIncoming])
        (by exact evalOperand_reg_of e4 t4 "%and44.i.7" (.int 64 (clearLow w (8 + 8 * (ctpop (clearLow w 8) / 8)))) hand4)
        (by
          show evalOperand (withEnv (("%c.096.i.unr", .int 64 (clearLow w (8 + 8 * (ctpop (clearLow w 8) / 8)))) :: e4) t4)
            (reg "%incdec.ptr.i.7")
            = some (.ptr (o + 4 * k + 4 * (8 + 8 * (ctpop (clearLow w 8) / 8))))
          exact evalOperand_reg_of _ _ "%incdec.ptr.i.7" _
            (by rw [lookupName_cons_ne _ _ (by decide)]; exact hgep4))
        hxtra4 hconv4 (by omega) hsum hjzu4 hmem4 h11e4 hctx4
    refine ⟨e5, ?_, hadd1, hctx5⟩
    have hA := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
    have hA2 := Jumps.comp hA (Jumps.one hjump3)
    have hB := Jumps.comp hA2 hJumps4
    have hC := Jumps.comp hB hJumps5
    rw [b8TailSteps_long w (by omega)]
    have hfin : b8CleanupState t4 (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0)
        = b8CleanupState s (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) M0) := by
      rw [ht4, b8CleanupState_guard, b8CleanupState_mainState]
    rw [hfin] at hC
    have hcnt : 1 + 1 + 1 + ctpop (clearLow w 8) / 8 + (2 + ctpop (clearLow w 8) % 8)
        = 5 + ctpop (clearLow w 8) / 8 + ctpop (clearLow w 8) % 8 := by omega
    rw [hcnt] at hC
    exact hC



/-! ### The stream's fold: its frame, its own lanes as the model's positions

The block layer's statement is about a stream, so the loop's memory is the
fold of one block store per word.  This section gives that fold a frame, the
read-back of each block's own lanes, and the positions a whole prefix holds. -/

/-- The positions the B8 body emits over a block stream, block after block. -/
def b8Stream : List (BitVec 64) → Nat → List Nat
  | [], _ => []
  | w :: ws, base => positionsOf w base ++ b8Stream ws (base + 64)

/-- The recursive stream is the model's `mapIdx` flattening: index `i` carries
the block base `base + 64 * i`. -/
theorem b8Stream_eq_mapIdx (ent : List (BitVec 64)) (base : Nat) :
    b8Stream ent base = (ent.mapIdx fun i w => positionsOf w (base + 64 * i)).flatten := by
  induction ent generalizing base with
  | nil => rfl
  | cons w ws ih =>
      show positionsOf w base ++ b8Stream ws (base + 64) = _
      rw [ih (base + 64), List.mapIdx_cons, List.flatten_cons]
      congr 1
      exact congrArg List.flatten (mapIdx_congr (fun i a _ => by
        rw [show base + 64 + 64 * i = base + 64 * (i + 1) from by omega]))

/-- The cursor never moves backwards. -/
theorem pos8Cursor_self_le (ent : List (BitVec 64)) (k : Nat) : k ≤ pos8Cursor ent k := by
  rw [pos8Cursor_eq_sum]
  omega

/-- One block's store leaves every read outside its own lanes alone. -/
theorem b8BlockStore_frame (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (k + slotCount w) ≤ p) :
    readBytes (b8BlockStore o w base k mem) p n = readBytes mem p n := by
  unfold b8BlockStore
  split
  · rfl
  · exact b8Lanes_frame o w base k 0 mem (slotCount w) p n (by
      rcases hdisj with h | h
      · left; omega
      · right; omega)

/-- The fold of a block stream leaves every read outside its span alone: a
non-zero block writes lanes `k … k + slotCount w - 1` with
`slotCount w ≤ ctpop w + 7`, a zero block writes nothing, so the last lane any
block writes is at most seven past the stream's final cursor. -/
theorem b8MemFold_frame (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (pos8Cursor ent k + 7) ≤ p) :
    readBytes (b8MemFold o base k ent mem) p n = readBytes mem p n := by
  induction ent generalizing base k mem with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 0
      · subst hw
        rw [show b8MemFold o base k ((0 : BitVec 64) :: ws) mem
            = b8MemFold o (base + 64) k ws mem from by
          show b8MemFold o (base + 64) (k + ctpop 0) ws (b8BlockStore o 0 base k mem)
            = b8MemFold o (base + 64) k ws mem
          rw [b8BlockStore_zero, ctpop_zero64]
          rfl]
        refine ih (base + 64) k mem ?_
        have hcur : pos8Cursor ((0 : BitVec 64) :: ws) k = pos8Cursor ws k := by
          show pos8Cursor ws (k + ctpop 0) = pos8Cursor ws k
          rw [ctpop_zero64]
          rfl
        rw [hcur] at hdisj
        exact hdisj
      · rw [show b8MemFold o base k (w :: ws) mem
            = b8MemFold o (base + 64) (k + ctpop w) ws (b8BlockStore o w base k mem) from rfl]
        have h1 : readBytes (b8MemFold o (base + 64) (k + ctpop w) ws
            (b8BlockStore o w base k mem)) p n = readBytes (b8BlockStore o w base k mem) p n := by
          refine ih (base + 64) (k + ctpop w) (b8BlockStore o w base k mem) ?_
          rcases hdisj with h | h
          · left; omega
          · exact Or.inr h
        rw [h1]
        refine b8BlockStore_frame o w base k mem p n ?_
        rcases hdisj with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          have h2 : k + slotCount w ≤ pos8Cursor ws (k + ctpop w) + 7 := by
            have hsc : slotCount w ≤ ctpop w + 7 := slotCount_le hw
            have hcur : k + ctpop w ≤ pos8Cursor ws (k + ctpop w) := pos8Cursor_self_le ws _
            omega
          calc o + 4 * (k + slotCount w)
              ≤ o + 4 * (pos8Cursor ws (k + ctpop w) + 7) := by
                have hm := Nat.mul_le_mul_left 4 h2
                omega
            _ ≤ p := h

/-- One slot of the lane fold reads back its value. -/
theorem b8Lanes_lane0 (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) :
    ∀ (len t : Nat), t < len →
      readBytes (b8Lanes o w base k 0 len mem) (o + 4 * k + 4 * t) 4
        = some (natToBytes (slotVal base w t).toNat 4) := by
  intro len t ht
  have h := b8Lanes_lane o w base k 0 mem len t ht
  simpa only [Nat.zero_add] using h

/-- A block's own lanes, read back: the first `ctpop w` of its slots hold exactly
the model's positions for the block. -/
theorem b8Lanes_read_ctpop (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem)
    (hb : base % 64 = 0) (hcap : base + 64 < 2 ^ 32) :
    readLanes32 (b8Lanes o w base k 0 (slotCount w) mem) (o + 4 * k) (ctpop w)
      = some (positionsOf w base) := by
  have hcongr : readLanes32 (b8Lanes o w base k 0 (slotCount w) mem) (o + 4 * k) (ctpop w)
      = readLanes32 (b8Lanes o w base k 0 (ctpop w) mem) (o + 4 * k) (ctpop w) := by
    apply readLanes32_congr
    intro t ht
    rw [b8Lanes_lane0 o w base k mem (slotCount w) t (Nat.lt_of_lt_of_le ht (ctpop_le_slotCount w)),
      b8Lanes_lane0 o w base k mem (ctpop w) t ht]
  have hpos : readLanes32 (b8Lanes o w base k 0 (ctpop w) mem) (o + 4 * k) (ctpop w)
      = some ((List.range (ctpop w)).map (fun t => (slotVal base w t).toNat)) := by
    have h := b8Lanes_readLanes o w base k 0 mem (ctpop w)
    simpa only [Nat.zero_add, Nat.mul_zero, Nat.add_zero] using h
  exact hcongr.trans (hpos.trans (congrArg some (b8WordPositions w base hb hcap)))

/-- The fold's own lanes, read from the start cursor, are the model's stream: the
positions clause of the block-layer statement. -/
theorem b8MemFold_read (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem)
    (hb : base % 64 = 0) (hcap : base + 64 * ent.length < 2 ^ 32) :
    readLanes32 (b8MemFold o base k ent mem) (o + 4 * k) ((ent.map ctpop).sum)
      = some (b8Stream ent base) := by
  induction ent generalizing base k mem with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 0
      · subst hw
        rw [show b8MemFold o base k ((0 : BitVec 64) :: ws) mem
            = b8MemFold o (base + 64) k ws mem from by
          show b8MemFold o (base + 64) (k + ctpop 0) ws (b8BlockStore o 0 base k mem)
            = b8MemFold o (base + 64) k ws mem
          rw [b8BlockStore_zero, ctpop_zero64]
          rfl]
        rw [show (((0 : BitVec 64) :: ws).map ctpop).sum = (ws.map ctpop).sum from by
          rw [List.map_cons, ctpop_zero64, List.sum_cons, Nat.zero_add]]
        rw [show b8Stream ((0 : BitVec 64) :: ws) base = b8Stream ws (base + 64) from by
          show positionsOf 0 base ++ b8Stream ws (base + 64) = _
          rw [show positionsOf (0 : BitVec 64) base = [] from by
            show (setLanes (0 : BitVec 64)).map (fun k => base + k) = []
            rw [setLanes_zero]; rfl]
          rfl]
        refine ih (base + 64) k mem ?_ ?_
        · rw [Nat.add_mod, show (64 : Nat) % 64 = 0 from by decide, hb, Nat.zero_add,
            Nat.zero_mod]
        · rw [List.length_cons, Nat.mul_add, Nat.mul_one] at hcap; omega
      · have hcd : ((w :: ws).map ctpop).sum = ctpop w + (ws.map ctpop).sum := by
          rw [List.map_cons, List.sum_cons]
        rw [hcd]
        have hfold : b8MemFold o base k (w :: ws) mem
            = b8MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (slotCount w) mem) := by
          show b8MemFold o (base + 64) (k + ctpop w) ws (b8BlockStore o w base k mem) = _
          rw [b8BlockStore_of_ne o w base k mem hw]
        rw [hfold]
        have hbelow : readLanes32 (b8MemFold o (base + 64) (k + ctpop w) ws
              (b8Lanes o w base k 0 (slotCount w) mem)) (o + 4 * k) (ctpop w)
            = some (positionsOf w base) := by
          have hcongr := readLanes32_congr
            (b8Lanes o w base k 0 (slotCount w) mem)
            (b8MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (slotCount w) mem))
            (o + 4 * k) (ctpop w) (fun j hj => by
              exact b8MemFold_frame o (base + 64) (k + ctpop w) ws
                (b8Lanes o w base k 0 (slotCount w) mem) (o + 4 * k + 4 * j) 4
                (Or.inl (by omega)))
          rw [hcongr]
          exact b8Lanes_read_ctpop o w base k mem hb (by rw [List.length_cons] at hcap; omega)
        have habove : readLanes32 (b8MemFold o (base + 64) (k + ctpop w) ws
              (b8Lanes o w base k 0 (slotCount w) mem)) (o + 4 * k + 4 * ctpop w)
              ((ws.map ctpop).sum)
            = some (b8Stream ws (base + 64)) := by
          rw [show o + 4 * k + 4 * ctpop w = o + 4 * (k + ctpop w) from by omega]
          refine ih (base + 64) (k + ctpop w) (b8Lanes o w base k 0 (slotCount w) mem) ?_ ?_
          · rw [Nat.add_mod, show (64 : Nat) % 64 = 0 from by decide, hb, Nat.zero_add,
              Nat.zero_mod]
          · rw [List.length_cons, Nat.mul_add, Nat.mul_one] at hcap; omega
        have hadd := readLanes32_add
          (b8MemFold o (base + 64) (k + ctpop w) ws (b8Lanes o w base k 0 (slotCount w) mem))
          (ctpop w) (o + 4 * k) (positionsOf w base) ((ws.map ctpop).sum)
          (b8Stream ws (base + 64)) hbelow habove
        rw [hadd]
        rfl

/-! ### One block

A block's run is at most twenty-two steps: the body, the eight fixed slots, the
tail when the word is long, and the join.  Its memory gains exactly its
`slotCount` lanes from the cursor. -/

/-- The `cleanup` state, from a named predecessor. -/
def b8AdvanceAt (s : State) (M : Mem) (pred : String) : State :=
  { s with mem := M, pc := "cleanup", pre := some pred }

theorem b8AdvanceAt_of (s : State) (M : Mem) (pred : String) :
    ({ s with mem := M, pc := "cleanup", pre := some pred }) = b8AdvanceAt s M pred := rfl

theorem b8CleanupState_eq_advanceAt (s : State) (M : Mem) :
    b8CleanupState s M = b8AdvanceAt s M "s1f_ke_b8.exit" := rfl

theorem b8_preserved (instrs : List Instr) (names : List String)
    (hn : ∀ i ∈ instrs, i.dst? ∉ names.map some) (s s' : State)
    (h : denoteCode entryCalls instrs s = some s') :
    ∀ n ∈ names, lookupName s'.env n = lookupName s.env n :=
  fun n hmem => denoteCode_lookupName entryCalls instrs n
    (fun i hi hd => hn i hi (hd.symm ▸ List.mem_map_of_mem (f := some) hmem)) s s' h

/-- The bundle after a block whose `phi`s rebind the counter and the cursor. -/
theorem B8Ctx.of_phi {env env' : Env} {e o blk0 nblk ii kk ii' kk' : Nat}
    (h : B8Ctx env e o blk0 nblk ii kk)
    (hEnt : lookupName env' "%ent" = lookupName env "%ent")
    (hBlk : lookupName env' "%blk0" = lookupName env "%blk0")
    (hNb : lookupName env' "%nblk" = lookupName env "%nblk")
    (hOut : lookupName env' "%out" = lookupName env "%out")
    (hi : lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 ii')))
    (hk : lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 kk'))) :
    B8Ctx env' e o blk0 nblk ii' kk' := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := h
  exact ⟨hEnt.trans h1, hBlk.trans h2, hNb.trans h3, hOut.trans h4, hi, hk⟩

/-- The tail guard's entry state. -/
def b8GuardEntry (s : State) (M : Mem) : State :=
  { s with mem := M, pc := "if.end39.i", pre := some "if.end" }

/-- A zero word: `for.body` takes the `continue` edge to `cleanup`, and the
memory is unchanged. -/
theorem b8Block_zero_run (env : Env) (s : State) (i k nblk e o blk0 : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hframe : B8Frame env e o blk0 nblk)
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (0 : BitVec 64).toNat 8))
    (hi63 : i < 2 ^ 63) :
    ∃ (env' : Env),
      Jumps entryB8Function 1 (withEnv env s) (withEnv env' (b8AdvanceAt s s.mem "for.body")) ∧
      B8Frame env' e o blk0 nblk ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨e1, hbody1, hjump1, hi1, hk1, h0, hb1⟩ :=
    b8Body_step_zero env s 0 i k e p opk opi hpc hpre hopk hopi hvk hvi hframe.ent hread hi63 rfl
  have hpr := b8_preserved b8Body.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
    (withEnv env s) (withEnv e1 s) hbody1
  have hE : lookupName e1 "%ent" = lookupName env "%ent" := by
    have h := hpr "%ent" (by decide); simpa only [withEnv] using h
  have hB : lookupName e1 "%blk0" = lookupName env "%blk0" := by
    have h := hpr "%blk0" (by decide); simpa only [withEnv] using h
  have hN : lookupName e1 "%nblk" = lookupName env "%nblk" := by
    have h := hpr "%nblk" (by decide); simpa only [withEnv] using h
  have hO : lookupName e1 "%out" = lookupName env "%out" := by
    have h := hpr "%out" (by decide); simpa only [withEnv] using h
  exact ⟨e1, Jumps.one hjump1, hframe.of_preserved hE hB hN hO, hi1, hk1⟩

theorem b8TailSteps_le (w : BitVec 64) : b8TailSteps w ≤ 18 := by
  have hn : ctpop (clearLow w 8) ≤ 56 := by rw [ctpop_clearLow]; have := ctpop_le w; omega
  have hm : ctpop (clearLow w 8) % 8 ≤ 7 := by
    have := Nat.mod_lt (ctpop (clearLow w 8)) (by decide : 0 < 8); omega
  by_cases h : ctpop (clearLow w 8) / 8 = 0
  · rw [b8TailSteps_short w h]; omega
  · rw [b8TailSteps_long w h]
    have h1 : ctpop (clearLow w 8) / 8 ≤ 7 := by omega
    omega

/-- The steps a nonzero block takes: `for.body`, the kernel, its test, the tail
when the word is long, and the join's branch to `cleanup`. -/
def b8BlockSteps (w : BitVec 64) : Nat :=
  if ctpop (clearLow w 8) = 0 then 3 else 2 + b8TailSteps w

theorem b8BlockSteps_le (w : BitVec 64) : b8BlockSteps w ≤ 22 := by
  by_cases h : ctpop (clearLow w 8) = 0
  · rw [b8BlockSteps, ite_eq_left h]; omega
  · rw [b8BlockSteps, ite_eq_right h]
    have := b8TailSteps_le w; omega

/-- A non-zero word's block, up to `cleanup`: the eight fixed slots, the tail
when the word is long, and the join's cursor addition.  The memory gains exactly
`slotCount` lanes from the cursor. -/
theorem b8Block_pos_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o : Nat)
    (nblk : Nat) (p : String) (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hw : w ≠ 0)
    (hi63 : i < 2 ^ 63)
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hsum : ctpop w + k < 2 ^ 64)
    (hframe : B8Frame env e o blk0 nblk) :
    ∃ (env' : Env) (M' : Mem),
      Jumps entryB8Function (b8BlockSteps w) (withEnv env s)
        (withEnv env' (b8AdvanceAt s M' "s1f_ke_b8.exit")) ∧
      b8BlockSteps w ≤ 22 ∧
      B8Frame env' e o blk0 nblk ∧
      lookupName env' "%add1" = some (.int 64 (BitVec.ofNat 64 (ctpop w + k))) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      M' = b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem := by
  obtain ⟨e1, hbody1, hjump1, hi1, hk1, h0, hb1⟩ :=
    b8Body_step_pos env s w i k e p opk opi hpc hpre hopk hopi hvk hvi hent hread hi63 hw
  have hpr := b8_preserved b8Body.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
    (withEnv env s) (withEnv e1 s) hbody1
  have hE : lookupName e1 "%ent" = lookupName env "%ent" := by
    have h := hpr "%ent" (by decide); simpa only [withEnv] using h
  have hB : lookupName e1 "%blk0" = lookupName env "%blk0" := by
    have h := hpr "%blk0" (by decide); simpa only [withEnv] using h
  have hN : lookupName e1 "%nblk" = lookupName env "%nblk" := by
    have h := hpr "%nblk" (by decide); simpa only [withEnv] using h
  have hO : lookupName e1 "%out" = lookupName env "%out" := by
    have h := hpr "%out" (by decide); simpa only [withEnv] using h
  have hBk1 : lookupName e1 "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) := hB.trans hframe.blk0
  have hOu1 : lookupName e1 "%out" = some (.ptr o) := hO.trans hframe.out
  have hctx1 : B8Ctx e1 e o blk0 nblk i k := hframe.ctx hE hB hN hO hi1 hk1
  obtain ⟨sK, hsK⟩ : ∃ t : State, t = { s with pc := "if.end", pre := some "for.body" } := ⟨_, rfl⟩
  have hpcK : sK.pc = "if.end" := by rw [hsK]
  obtain ⟨e2, hbody2, h1, hand, hconv2, hptr, hcmp⟩ :=
    b8Kernel_run e1 sK w i blk0 k o hi1 hBk1 hOu1 hk1 h0 hk63 hblk hconv
  have hctx2 : B8Ctx e2 e o blk0 nblk i k :=
    hctx1.transfer (b8_keep b8Kernel.instrs (by decide) _ _ hbody2)
  obtain ⟨sK', hsK'⟩ : ∃ t : State, t = { sK with mem := b8Lanes o w (posBase blk0 i) k 0 8 sK.mem } := ⟨_, rfl⟩
  have hbody2' : denoteCode entryCalls b8Kernel.instrs (withEnv e1 sK) = some (withEnv e2 sK') := by
    rw [hsK']; exact hbody2
  have hsk : sK.mem = s.mem := by rw [hsK]
  have hnextK : sK.next = s.next := by rw [hsK]
  have henvK : sK.env = s.env := by rw [hsK]
  have hpreK : (withEnv e2 sK').pc = "if.end" := by rw [hsK']; exact hpcK
  rw [← hsK] at hjump1
  by_cases hlong : ctpop (clearLow w 8) = 0
  · -- at most eight set lanes: the kernel's eight slots are the whole block
    have hle : ctpop w ≤ 8 := by
      have hnot : ¬ 9 ≤ ctpop w := by
        intro h8
        have h2 : 1 ≤ ctpop (clearLow w 8) := by rw [ctpop_clearLow]; omega
        omega
      omega
    have hlt9 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9) = true := by
      rw [show (BitVec.ofInt 64 9 : BitVec 64) = BitVec.ofNat 64 9 from by decide]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
      exact decide_eq_true (show ctpop w < 9 by omega)
    have hbit : BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9))
        = (1 : BitVec 1) := by rw [hlt9]; rfl
    obtain ⟨sJ, hsJ⟩ : ∃ t : State, t = { sK with mem := b8Lanes o w (posBase blk0 i) k 0 8 sK.mem, pc := "s1f_ke_b8.exit", pre := some "if.end" } := ⟨_, rfl⟩
    have hSJ : ({ sK' with pc := "s1f_ke_b8.exit", pre := some "if.end" } : State) = sJ := by
      rw [hsK', hsJ, hsk]
    have hjump2 : step entryCalls entryB8Function (withEnv e1 sK) = .jump (withEnv e2 sJ) := by
      rw [b8_step_of (withEnv e1 sK) "if.end" b8Kernel (withEnv e2 sK') hpcK findBlock_b8Kernel hbody2']
      show execTerm (withEnv e2 sK') (.condbr (.reg "%cmp.i") "s1f_ke_b8.exit" "if.end39.i") = _
      rw [execTerm_condbr_true (c := .reg "%cmp.i") (t := "s1f_ke_b8.exit") (f := "if.end39.i")
        (evalOperand_reg_of e2 sK' "%cmp.i" (.int 1 _) hcmp) hbit]
      rw [hpreK, withEnv_jump, hSJ]
    obtain ⟨e3, hjoin3, hadd1⟩ := b8Join_run e2 sJ (ctpop w) k "if.end" (reg "%1") (by rw [hsJ])
      (by simp [b8IncomingR, phiIncoming])
      (evalOperand_reg_of e2 sJ "%1" (.int 64 (BitVec.ofNat 64 (ctpop w))) h1)
      (by show lookupName e2 "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k))
          exact hctx2.k011)
      hsum
    have hctx3 : B8Ctx e3 e o blk0 nblk i k :=
      hctx2.transfer (b8_keep b8Join.instrs (by decide) _ _ hjoin3)
    have hii3 : lookupName e3 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
      (denoteCode_lookupName entryCalls b8Join.instrs "%i.010" (by decide) _ _ hjoin3).trans hctx2.i010
    obtain ⟨sA, hsA⟩ : ∃ t : State, t = b8AdvanceAt s (b8Lanes o w (posBase blk0 i) k 0 8 sK.mem) "s1f_ke_b8.exit" := ⟨_, rfl⟩
    have hSA : ({ sJ with pc := "cleanup", pre := some "s1f_ke_b8.exit" } : State) = sA := by
      rw [hsJ, hsA, hnextK, henvK, hsk]
      simp only [b8AdvanceAt]
    have hjump3 : step entryCalls entryB8Function (withEnv e2 sJ) = .jump (withEnv e3 sA) := by
      rw [b8_step_of (withEnv e2 sJ) "s1f_ke_b8.exit" b8Join (withEnv e3 sJ) (by rw [hsJ]; rfl) findBlock_b8Join hjoin3]
      show execTerm (withEnv e3 sJ) (.br "cleanup") = _
      rw [execTerm_br]
      rw [show (withEnv e3 sJ).pc = "s1f_ke_b8.exit" from by rw [hsJ]; rfl]
      rw [withEnv_jump, hSA]
    refine ⟨e3, b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem, ?_, ?_, hctx3.frame,
      hadd1, hii3, rfl⟩
    · rw [show b8BlockSteps w = 3 from by rw [b8BlockSteps, ite_eq_left hlong]]
      have hJ := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
      have hJ2 := Jumps.comp hJ (Jumps.one hjump3)
      have hsl : b8Lanes o w (posBase blk0 i) k 0 8 sK.mem
          = b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem := by
        rw [hsk, show slotCount w = 8 from by rw [slotCount, hlong, Nat.add_zero]]
      rw [hsA] at hJ2
      rw [hsl] at hJ2
      exact hJ2
    · rw [show b8BlockSteps w = 3 from by rw [b8BlockSteps, ite_eq_left hlong]]; omega
  · -- a long word: the kernel's test reaches the tail's guard
    have hge : 9 ≤ ctpop w := by
      have hnot : ¬ ctpop w ≤ 8 := by
        intro hle8
        have h2 : ctpop (clearLow w 8) = 0 := by rw [ctpop_clearLow]; omega
        omega
      omega
    have hlt9 : BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9) = false := by
      rw [show (BitVec.ofInt 64 9 : BitVec 64) = BitVec.ofNat 64 9 from by decide]
      rw [BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := ctpop_le w; omega), Nat.mod_eq_of_lt (by decide)]
      exact decide_eq_false (show ¬ ctpop w < 9 by omega)
    have hbit : BitVec.ofBool (BitVec.ult (BitVec.ofNat 64 (ctpop w)) (BitVec.ofInt 64 9))
        = (0 : BitVec 1) := by rw [hlt9]; rfl
    obtain ⟨sG, hsG⟩ : ∃ t : State, t = b8GuardEntry s (b8Lanes o w (posBase blk0 i) k 0 8 s.mem) := ⟨_, rfl⟩
    have hSG : ({ sK' with pc := "if.end39.i", pre := some "if.end" } : State) = sG := by
      rw [hsK', hsG, hsk, hnextK, henvK]
      simp only [b8GuardEntry]
    have hjump2 : step entryCalls entryB8Function (withEnv e1 sK) = .jump (withEnv e2 sG) := by
      rw [b8_step_of (withEnv e1 sK) "if.end" b8Kernel (withEnv e2 sK') hpcK findBlock_b8Kernel hbody2']
      show execTerm (withEnv e2 sK') (.condbr (.reg "%cmp.i") "s1f_ke_b8.exit" "if.end39.i") = _
      rw [execTerm_condbr_false (c := .reg "%cmp.i") (t := "s1f_ke_b8.exit") (f := "if.end39.i")
        (evalOperand_reg_of e2 sK' "%cmp.i" (.int 1 _) hcmp) hbit]
      rw [hpreK, withEnv_jump, hSG]
    have hpcG : sG.pc = "if.end39.i" := by rw [hsG]; rfl
    have hgm : sG.mem = b8Lanes o w (posBase blk0 i) k 0 8 s.mem := by
      rw [hsG]; simp only [b8GuardEntry]
    obtain ⟨e4, hJumps4, hadd1, hctx4⟩ :=
      b8Tail_run w e i blk0 k o e2 sG s.mem nblk i k hpcG hge hand hptr hconv2 hsum hgm hctx2
    obtain ⟨sT, hsT⟩ : ∃ t : State, t = b8AdvanceAt s (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem) "s1f_ke_b8.exit" := ⟨_, rfl⟩
    have hcs : b8CleanupState sG (b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem) = sT := by
      rw [hsG, hsT]
      simp only [b8CleanupState, b8AdvanceAt, b8GuardEntry]
    refine ⟨e4, b8Lanes o w (posBase blk0 i) k 0 (slotCount w) s.mem, ?_, ?_, hctx4.frame,
      hadd1, hctx4.i010, rfl⟩
    · rw [show b8BlockSteps w = 2 + b8TailSteps w from by rw [b8BlockSteps, ite_eq_right hlong]]
      have hJ := Jumps.comp (Jumps.one hjump1) (Jumps.one hjump2)
      have hJ2 := Jumps.comp hJ hJumps4
      rw [hcs] at hJ2
      rw [hsT] at hJ2
      exact hJ2
    · rw [show b8BlockSteps w = 2 + b8TailSteps w from by rw [b8BlockSteps, ite_eq_right hlong]]
      have := b8TailSteps_le w; omega



/-! ### The block loop

Each block's own run is bounded by `b8BlockSteps`; the loop adds one `cleanup` step
per block and one exit, so its fuel is the stream's step count plus the block
count plus one. -/

/-- The B8 function's own jump and return steps. -/
theorem b8_runFuel_jump {s s' : State} {n : Nat}
    (h : step entryCalls entryB8Function s = .jump s') :
    runFuel entryCalls (n + 1) entryB8Function s = runFuel entryCalls n entryB8Function s' := by
  simp [runFuel, h]

theorem b8_runFuel_ret {s s' : State} {v : Option Value} {n : Nat}
    (h : step entryCalls entryB8Function s = .ret v s') :
    runFuel entryCalls (n + 1) entryB8Function s = some (.ret v s'.mem) := by
  simp [runFuel, h]

theorem findBlock_b8Entry :
    entryB8Function.findBlock "entry" = some b8Entry := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

/-- The initial state's five parameter cells and its block. -/
theorem b8_init (blk0 nblk k : Nat) (mem : Mem) (e o : Nat) :
    let S0 : State := { (initState entryB8Function
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
    S0.pc = "entry" ∧
      lookupName S0.env "%ent" = some (.ptr e) ∧
      lookupName S0.env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) ∧
      lookupName S0.env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) ∧
      lookupName S0.env "%out" = some (.ptr o) ∧
      lookupName S0.env "%k" = some (.int 64 (BitVec.ofNat 64 k)) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initState, entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard,
      b8TailPreheader, b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder,
      b8Join, b8Advance, List.zip, List.map, lookupName]

theorem b8Entry_body (env : Env) (s : State) (nblk : Nat)
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk))) :
    ∃ env', denoteCode entryCalls b8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%cmp9.not" = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) := by
  refine ⟨?env', ?hrun, ?hnot⟩
  case hrun =>
    simp only [b8Entry, reg, lit]
    ent_step (step_icmp_eq_imm env s "%cmp9.not" "%nblk" 64 (BitVec.ofNat 64 nblk)
      (BitVec.ofInt 64 0) (by ent_auto))
    rw [ofInt64_zero]
    simp only [denoteCode, Option.bind]
    rfl
  case hnot => ent_auto

theorem b8Entry_step_zero (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (h0 : nblk = 0) :
    ∃ env', denoteCode entryCalls b8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, hnot⟩ := b8Entry_body env s nblk hnblk
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (1 : BitVec 1) := by
    subst h0
    rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [b8_step_of (withEnv env s) "entry" b8Entry (withEnv env' s) hpc findBlock_b8Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" })
    have hop := evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_true (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

theorem b8Entry_step_pos (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hnblk64 : nblk < 2 ^ 64)
    (h0 : nblk ≠ 0) :
    ∃ env', denoteCode entryCalls b8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryB8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, hnot⟩ := b8Entry_body env s nblk hnblk
  have hne : ¬ (BitVec.ofNat 64 nblk = 0) := by
    intro h
    have h1 : (BitVec.ofNat 64 nblk).toNat = nblk := toNat_ofNat64 nblk hnblk64
    rw [h] at h1
    simp at h1
    omega
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (0 : BitVec 1) := by
    have hd : decide (BitVec.ofNat 64 nblk = 0) = false := decide_eq_false hne
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [b8_step_of (withEnv env s) "entry" b8Entry (withEnv env' s) hpc findBlock_b8Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" })
    have hop := evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_false (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

/-- The stream's fold, one element further: the next block's store at its own
base and cursor. -/
theorem b8MemFold_succ (ent : List (BitVec 64)) (blk0 k0 o i : Nat) (mem0 : Mem)
    (hi : i < ent.length) :
    b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
      = b8BlockStore o (ent.get ⟨i, hi⟩) (posBase blk0 i) (pos8Cursor (ent.take i) k0)
          (b8MemFold o (64 * blk0) k0 (ent.take i) mem0) := by
  rw [pos8_take_succ ent i hi, b8MemFold_append]
  rw [pos8_take_length ent i (by omega)]
  rw [show 64 * blk0 + 64 * i = posBase blk0 i from by rw [posBase]; omega]
  rfl

/-- The mask word a block's iteration reads, out of the stream's fold. -/
theorem b8_read_word (ent : List (BitVec 64)) (blk0 k0 o e i : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hi : i < ent.length) :
    readBytes (b8MemFold o (64 * blk0) k0 (ent.take i) mem0) (e + 8 * i) 8
      = some (natToBytes (ent.get ⟨i, hi⟩).toNat 8) := by
  have h0 := readBytes_wordsOf mem0 e ent hwords i hi
  have hfr := b8MemFold_frame o (64 * blk0) k0 (ent.take i) mem0 (e + 8 * i) 8 (by
    rcases hdisj with h | h
    · left; omega
    · right
      have hc : pos8Cursor (ent.take i) k0 ≤ k0 + 64 * i := by
        have h1 := pos8Cursor_le (ent.take i) k0
        rwa [pos8_take_length ent i (by omega)] at h1
      omega)
  rw [hfr]; exact h0

/-- The steps the remaining blocks take, block after block. -/
def b8RunSteps : List (BitVec 64) → Nat
  | [] => 0
  | w :: ws => b8BlockSteps w + b8RunSteps ws

theorem b8RunSteps_drop_succ (ent : List (BitVec 64)) (i : Nat) (hi : i < ent.length) :
    b8RunSteps (ent.drop i) = b8BlockSteps (ent.get ⟨i, hi⟩) + b8RunSteps (ent.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem b8BlockSteps_zero : b8BlockSteps (0 : BitVec 64) = 3 := by
  rw [b8BlockSteps]
  rw [ite_eq_left (by decide)]

/-- One block's own run takes at least two steps: the body, and the branch it
takes. -/
theorem b8BlockSteps_two (w : BitVec 64) : 2 ≤ b8BlockSteps w := by
  rw [b8BlockSteps]
  split
  · omega
  · have := b8TailSteps_le w; omega

/-- **The block loop.**  From `for.body` with `r` blocks left, the loop runs to
the exit and returns the stream's cursor, with the fold of every block's stores
as its memory.  Each block's own run is bounded by `b8BlockSteps`, and its
`cleanup` step is the one that follows. -/
theorem b8_loop_run (ent : List (BitVec 64)) (blk0 nblk k0 o e : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * ent.length + 9 < 2 ^ 63)
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hnblk : nblk = ent.length) :
    ∀ (r i k : Nat) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = nblk → s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      B8Frame env e o blk0 nblk →
      k = pos8Cursor (ent.take i) k0 →
      s.mem = b8MemFold o (64 * blk0) k0 (ent.take i) mem0 →
      ∃ (env' : Env) (mem' : Mem),
        runFuel entryCalls (b8RunSteps (ent.drop i) + r + 1) entryB8Function (withEnv env s)
          = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop i) k)))) mem') ∧
        mem' = b8MemFold o (64 * blk0) k0 ent mem0 := by
  intro r
  induction r with
  | zero => intro i k env s p opk opi hr _; exact absurd hr (by simp)
  | succ r' ih =>
    intro i k env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hframe hk hmem
    have hilen : i < ent.length := by omega
    have hnblkpos : 1 ≤ nblk := by omega
    have hkle : k ≤ k0 + 64 * i := by
      rw [hk]
      have hc := pos8Cursor_le (ent.take i) k0
      rwa [pos8_take_length ent i (by omega)] at hc
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hword : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (ent.get ⟨i, hilen⟩).toNat 8) := by
      rw [hmem]; exact b8_read_word ent blk0 k0 o e i mem0 hwords hdisj hilen
    have hxeq : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk ↔ i + 1 = nblk :=
      ⟨fun h => ofNat64_inj (by omega) (by omega) h, fun h => by rw [h]⟩
    have hent_eq : ∀ _ : i + 1 = nblk, ent = ent.take (i + 1) := fun hlast => by
      have h1 : ent.take (i + 1) = ent.take nblk := by rw [hlast]
      rw [h1, hnblk, List.take_length]
    have hkNext : k + ctpop (ent.get ⟨i, hilen⟩) = pos8Cursor (ent.take (i + 1)) k0 := by
      rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm
    by_cases hw : ent.get ⟨i, hilen⟩ = 0
    · -- the word is zero: the body takes the `continue` edge, and nothing is stored
      obtain ⟨e1, hjump1, hframe1, hi1, hk1⟩ :=
        b8Block_zero_run env s i k nblk e o blk0 p opk opi hpc hpre hopk hopi hvk hvi hframe
          (by rw [hword, hw]) hi63
      have hmem1 : s.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
        rw [hmem, b8MemFold_succ ent blk0 k0 o i mem0 hilen, hw, b8BlockStore_zero]
      obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s s.mem "for.body" := ⟨_, rfl⟩
      rw [← hsC] at hjump1
      by_cases hlast : i + 1 = nblk
      · -- the last block: `cleanup` branches to the exit, which returns the cursor
        have hr0 : r' = 0 := by omega
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_last e1 sC i k nblk "for.body" (reg "%k.addr.011") (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hk1) hi1 hframe1.nblk hi64 (hxeq.mpr hlast)
        obtain ⟨sX, hsX⟩ : ∃ t : State, t = { sC with pc := "for.cond.cleanup", pre := some "cleanup" } := ⟨_, rfl⟩
        obtain ⟨e3, hbody3, hjump3, hk3⟩ :=
          b8Exit_step e2 sX k "cleanup" (reg "%k.addr.1") (by rw [hsX]) (by rw [hsX]) rfl
            (evalOperand_reg_of e2 _ _ _ hk2)
        rw [← hsX] at hjump2
        have hJ : Jumps entryB8Function 2 (withEnv env s) (withEnv e2 sX) :=
          Jumps.comp hjump1 (Jumps.one hjump2)
        have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
        have hnil : b8RunSteps ([] : List (BitVec 64)) = 0 := rfl
        have hmemE : s.mem = b8MemFold o (64 * blk0) k0 ent mem0 :=
          hmem1.trans (congrArg (fun l => b8MemFold o (64 * blk0) k0 l mem0) (hent_eq hlast)).symm
        have hmemX : (withEnv e3 sX).mem = s.mem := by
          show sX.mem = s.mem
          rw [hsX]
          show sC.mem = s.mem
          rw [hsC]
          rfl
        refine ⟨e3, (withEnv e3 sX).mem, ?_, ?_⟩
        · refine runFuel_mono_le (n := 3) ?_ ?_
          · rw [b8RunSteps_drop_succ ent i hilen, hw, b8BlockSteps_zero, hr0, hdrop, hnil]; omega
          · rw [pos8Cursor_drop_succ ent k i hilen]
            show runFuel entryCalls 3 entryB8Function (withEnv env s)
              = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop (i + 1)) (k + ctpop (ent.get ⟨i, hilen⟩)))))) (withEnv e3 sX).mem)
            rw [hdrop, hw, ctpop_zero64, Nat.add_zero]
            rw [show pos8Cursor ([] : List (BitVec 64)) k = k from rfl]
            rw [show (3 : Nat) = 2 + 1 from rfl]
            rw [runFuel_of_Jumps hJ]
            exact b8_runFuel_ret (n := 0) hjump3
        · rw [hmemX]
          exact hmemE
      · -- the loop continues: `cleanup` branches back to `for.body`
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_more e1 sC i k nblk "for.body" (reg "%k.addr.011") (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hk1) hi1 hframe1.nblk hi64
            (fun hcon => hlast (hxeq.mp hcon))
        have hprA := b8_preserved b8Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hvk2 : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
          simp only [reg]
          rw [evalOperand_reg_of e2 sC "%k.addr.1" (.int 64 (BitVec.ofNat 64 k)) hk2]
          rw [hw, ctpop_zero64, Nat.add_zero]
        have hvi2 : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC) (reg "%inc")
            = some (.int 64 (BitVec.ofNat 64 (i + 1))) :=
          evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        obtain ⟨e3, mem3, hrun3, hmem3⟩ :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl hvk2 hvi2 hframe2 hkNext hmem2
        refine ⟨e3, mem3, ?_, hmem3⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        refine runFuel_mono_le (n := 2 + (b8RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b8RunSteps_drop_succ ent i hilen, hw, b8BlockSteps_zero]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjump1 (Jumps.one hjump2))]
          exact hrun3
    · -- a non-zero word: the eight fixed slots and, for a long word, the tail
      have hwne : ent.get ⟨i, hilen⟩ ≠ 0 := hw
      have hk63' : k + 64 ≤ 2 ^ 63 := by omega
      have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
        have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
          have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
          calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
            _ ≤ 64 * (blk0 + nblk) := by omega
        rw [posBase_eq]
        omega
      have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
          = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
      have hsum : ctpop (ent.get ⟨i, hilen⟩) + k < 2 ^ 64 := by
        have h1 := ctpop_le (ent.get ⟨i, hilen⟩)
        omega
      obtain ⟨e1, Mk, hjumps1, hsteps1le, hframe1, hadd1, hi1', hMk⟩ :=
        b8Block_pos_run env s (ent.get ⟨i, hilen⟩) i blk0 k o nblk p opk opi hpc hpre hopk hopi hvk hvi
          hframe.ent hword hwne hi63 hk63' hblk' hconv hsum hframe
      have hcomm : ctpop (ent.get ⟨i, hilen⟩) + k = k + ctpop (ent.get ⟨i, hilen⟩) := Nat.add_comm _ _
      have hadd1' : lookupName e1 "%add1"
          = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
        rw [hadd1, hcomm]
      have hmem1 : Mk = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
        rw [hMk, hmem, b8MemFold_succ ent blk0 k0 o i mem0 hilen, hk,
          b8BlockStore_of_ne o (ent.get ⟨i, hilen⟩) (posBase blk0 i) (pos8Cursor (ent.take i) k0) _ hwne]
      obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s Mk "s1f_ke_b8.exit" := ⟨_, rfl⟩
      rw [← hsC] at hjumps1
      by_cases hlast : i + 1 = nblk
      · have hr0 : r' = 0 := by omega
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_last e1 sC i (k + ctpop (ent.get ⟨i, hilen⟩)) nblk "s1f_ke_b8.exit" (reg "%add1")
            (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hadd1') hi1' hframe1.nblk hi64 (hxeq.mpr hlast)
        obtain ⟨sX, hsX⟩ : ∃ t : State, t = { sC with pc := "for.cond.cleanup", pre := some "cleanup" } := ⟨_, rfl⟩
        obtain ⟨e3, hbody3, hjump3, hk3⟩ :=
          b8Exit_step e2 sX (k + ctpop (ent.get ⟨i, hilen⟩)) "cleanup" (reg "%k.addr.1") (by rw [hsX]) (by rw [hsX]) rfl
            (evalOperand_reg_of e2 _ _ _ hk2)
        rw [← hsX] at hjump2
        have hJ : Jumps entryB8Function (b8BlockSteps (ent.get ⟨i, hilen⟩) + 1) (withEnv env s) (withEnv e2 sX) :=
          Jumps.comp hjumps1 (Jumps.one hjump2)
        have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
        have hnil : b8RunSteps ([] : List (BitVec 64)) = 0 := rfl
        have hmemE : Mk = b8MemFold o (64 * blk0) k0 ent mem0 :=
          hmem1.trans (congrArg (fun l => b8MemFold o (64 * blk0) k0 l mem0) (hent_eq hlast)).symm
        have hmemX : (withEnv e3 sX).mem = Mk := by
          show sX.mem = Mk
          rw [hsX]
          show sC.mem = Mk
          rw [hsC]
          rfl
        refine ⟨e3, (withEnv e3 sX).mem, ?_, ?_⟩
        · refine runFuel_mono_le (n := (b8BlockSteps (ent.get ⟨i, hilen⟩) + 1) + 1) ?_ ?_
          · rw [b8RunSteps_drop_succ ent i hilen, hr0, hdrop, hnil]; omega
          · rw [pos8Cursor_drop_succ ent k i hilen]
            show runFuel entryCalls ((b8BlockSteps (ent.get ⟨i, hilen⟩) + 1) + 1) entryB8Function (withEnv env s)
              = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop (i + 1)) (k + ctpop (ent.get ⟨i, hilen⟩)))))) (withEnv e3 sX).mem)
            rw [hdrop]
            rw [show pos8Cursor ([] : List (BitVec 64)) (k + ctpop (ent.get ⟨i, hilen⟩)) = (k + ctpop (ent.get ⟨i, hilen⟩)) from rfl]
            rw [runFuel_of_Jumps hJ]
            exact b8_runFuel_ret (n := 0) hjump3
        · rw [hmemX]
          exact hmemE
      · obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_more e1 sC i (k + ctpop (ent.get ⟨i, hilen⟩)) nblk "s1f_ke_b8.exit" (reg "%add1")
            (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hadd1') hi1' hframe1.nblk hi64
            (fun hcon => hlast (hxeq.mp hcon))
        have hprA := b8_preserved b8Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hvk2 : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :=
          evalOperand_reg_of e2 sC "%k.addr.1" (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) hk2
        have hvi2 : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC) (reg "%inc")
            = some (.int 64 (BitVec.ofNat 64 (i + 1))) :=
          evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        obtain ⟨e3, mem3, hrun3, hmem3⟩ :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl hvk2 hvi2 hframe2 hkNext hmem2
        refine ⟨e3, mem3, ?_, hmem3⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        refine runFuel_mono_le
          (n := b8BlockSteps (ent.get ⟨i, hilen⟩) + 1 + (b8RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b8RunSteps_drop_succ ent i hilen]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjumps1 (Jumps.one hjump2))]
          exact hrun3

/-- **The loop, when a word is unreadable.**  From a loop state with `r` blocks
left before the failing one, the run is `ub`: each earlier block's body runs and
hands its successor on, and the failing block's own load is the instruction that
fails.  The memory is the stream's fold, so every earlier block reads its own
word and costs its own step count. -/
theorem b8_loop_run_ub (ent : List (BitVec 64)) (blk0 nblk k0 o e : Nat) (mem0 : Mem)
    (jj : Nat)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * ent.length + 9 < 2 ^ 63)
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hnblk : nblk = ent.length)
    (hj : jj < nblk)
    (hfail : readBytes (b8MemFold o (64 * blk0) k0 (ent.take jj) mem0) (e + 8 * jj) 8 = none) :
    ∀ (r i k : Nat) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = jj + 1 → s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      B8Frame env e o blk0 nblk →
      k = pos8Cursor (ent.take i) k0 →
      s.mem = b8MemFold o (64 * blk0) k0 (ent.take i) mem0 →
      runFuel entryCalls (b8RunSteps (ent.drop i) + r + 1) entryB8Function (withEnv env s)
        = some .ub := by
  intro r
  induction r with
  | zero => intro i k env s p opk opi hr; exact absurd hr (by omega)
  | succ r' ih =>
    intro i k env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hframe hk hmem
    have hilen : i < ent.length := by omega
    have hkle : k ≤ k0 + 64 * i := by
      rw [hk]
      have hc := pos8Cursor_le (ent.take i) k0
      rwa [pos8_take_length ent i (by omega)] at hc
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hword : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (ent.get ⟨i, hilen⟩).toNat 8) := by
      rw [hmem]; exact b8_read_word ent blk0 k0 o e i mem0 hwords hdisj hilen
    have hle2 : 2 ≤ b8RunSteps (ent.drop i) + (r' + 1) + 1 := by
      rw [b8RunSteps_drop_succ ent i hilen]
      have h1 := b8BlockSteps_two (ent.get ⟨i, hilen⟩)
      omega
    by_cases hnow : i = jj
    · -- the failing block is this one
      have hno : readBytes s.mem (e + 8 * i) 8 = none := by
        rw [hmem, hnow]; exact hfail
      exact runFuel_mono_le hle2
        (b8Body_ub_of_no_read env s i k e p opk opi hpc hpre hopk hopi hvk hvi hframe.ent hi63 hno)
    · have hne : i + 1 ≠ nblk := by omega
      have hxeq : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk ↔ i + 1 = nblk :=
        ⟨fun h => ofNat64_inj (by omega) (by omega) h, fun h => by rw [h]⟩
      have hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk := fun hcon => hne (hxeq.mp hcon)
      by_cases hw : ent.get ⟨i, hilen⟩ = 0
      · -- the word is zero: `cleanup`, then the next block; nothing is stored
        obtain ⟨e1, hjump1, hframe1, hi1, hk1⟩ :=
          b8Block_zero_run env s i k nblk e o blk0 p opk opi hpc hpre hopk hopi hvk hvi hframe
            (by rw [hword, hw]) hi63
        obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s s.mem "for.body" := ⟨_, rfl⟩
        rw [← hsC] at hjump1
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_more e1 sC i k nblk "for.body" (reg "%k.addr.011")
            (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hk1) hi1 hframe1.nblk hi64 hx
        have hprA := b8_preserved b8Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hcz : ctpop (ent.get ⟨i, hilen⟩) = 0 := by rw [hw, ctpop_zero64]
        have hkNext : k + ctpop (ent.get ⟨i, hilen⟩) = pos8Cursor (ent.take (i + 1)) k0 := by
          rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm
        have hmem1 : s.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          rw [hmem, b8MemFold_succ ent blk0 k0 o i mem0 hilen, hw, b8BlockStore_zero]
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        have hvkz : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
          rw [hcz, Nat.add_zero]
          exact evalOperand_reg_of e2 sC "%k.addr.1" (.int 64 (BitVec.ofNat 64 k)) hk2
        have hviz : evalOperand (withEnv (("%k.addr.011",
              .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC)
              (reg "%inc") = some (.int 64 (BitVec.ofNat 64 (i + 1))) := by
          rw [hcz, Nat.add_zero]
          exact evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hr1 : 1 ≤ r' := by omega
        have hr2 : (i + 1) + r' = jj + 1 := by omega
        have hrec : runFuel entryCalls (b8RunSteps (ent.drop (i + 1)) + r' + 1) entryB8Function
            (withEnv e2 ({ sC with pc := "for.body", pre := some "cleanup" } : State)) = some .ub :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            hr1 hr2 rfl rfl rfl rfl hvkz hviz hframe2 hkNext hmem2
        refine runFuel_mono_le (n := 2 + (b8RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b8RunSteps_drop_succ ent i hilen, hw, b8BlockSteps_zero]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjump1 (Jumps.one hjump2))]
          exact hrec
      · -- the word is not zero: the block's slots and tail, then `cleanup`
        have hwne : ent.get ⟨i, hilen⟩ ≠ 0 := hw
        have hk63' : k + 64 ≤ 2 ^ 63 := by omega
        have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
          have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
            have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
            calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
              _ ≤ 64 * (blk0 + nblk) := by omega
          rw [posBase_eq]
          omega
        have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
            = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
        have hsum : ctpop (ent.get ⟨i, hilen⟩) + k < 2 ^ 64 := by
          have h1 := ctpop_le (ent.get ⟨i, hilen⟩)
          omega
        obtain ⟨e1, Mk, hjumps1, hsteps1le, hframe1, hadd1, hi1', hMk⟩ :=
          b8Block_pos_run env s (ent.get ⟨i, hilen⟩) i blk0 k o nblk p opk opi hpc hpre hopk hopi
            hvk hvi hframe.ent hword hwne hi63 hk63' hblk' hconv hsum hframe
        have hcomm : ctpop (ent.get ⟨i, hilen⟩) + k = k + ctpop (ent.get ⟨i, hilen⟩) :=
          Nat.add_comm _ _
        have hadd1' : lookupName e1 "%add1"
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) := by
          rw [hadd1, hcomm]
        have hmem1 : Mk = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          rw [hMk, hmem, b8MemFold_succ ent blk0 k0 o i mem0 hilen, hk,
            b8BlockStore_of_ne o (ent.get ⟨i, hilen⟩) (posBase blk0 i) (pos8Cursor (ent.take i) k0) _
            hwne]
        obtain ⟨sC, hsC⟩ : ∃ t : State, t = b8AdvanceAt s Mk "s1f_ke_b8.exit" := ⟨_, rfl⟩
        rw [← hsC] at hjumps1
        obtain ⟨e2, hbody2, hjump2, hk2, hinc2, hx2⟩ :=
          b8Advance_step_more e1 sC i (k + ctpop (ent.get ⟨i, hilen⟩)) nblk "s1f_ke_b8.exit"
            (reg "%add1") (by rw [hsC]; rfl) (by rw [hsC]; rfl) rfl
            (evalOperand_reg_of e1 _ _ _ hadd1') hi1' hframe1.nblk hi64 hx
        have hprA := b8_preserved b8Advance.instrs ["%ent", "%blk0", "%nblk", "%out"] (by decide)
          (withEnv e1 sC) (withEnv e2 sC) hbody2
        have hE2 : lookupName e2 "%ent" = lookupName e1 "%ent" := by
          have h := hprA "%ent" (by decide); simpa only [withEnv] using h
        have hB2 : lookupName e2 "%blk0" = lookupName e1 "%blk0" := by
          have h := hprA "%blk0" (by decide); simpa only [withEnv] using h
        have hN2 : lookupName e2 "%nblk" = lookupName e1 "%nblk" := by
          have h := hprA "%nblk" (by decide); simpa only [withEnv] using h
        have hO2 : lookupName e2 "%out" = lookupName e1 "%out" := by
          have h := hprA "%out" (by decide); simpa only [withEnv] using h
        have hframe2 : B8Frame e2 e o blk0 nblk := hframe1.of_preserved hE2 hB2 hN2 hO2
        have hkNext : k + ctpop (ent.get ⟨i, hilen⟩) = pos8Cursor (ent.take (i + 1)) k0 := by
          rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm
        have hmem2 : ({ sC with pc := "for.body", pre := some "cleanup" } : State).mem
            = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          show sC.mem = b8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
          rw [hsC]
          exact hmem1
        have hvkp : evalOperand (withEnv e2 sC) (reg "%k.addr.1")
            = some (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :=
          evalOperand_reg_of e2 sC "%k.addr.1"
            (.int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) hk2
        have hvip : evalOperand (withEnv (("%k.addr.011",
              .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2) sC)
              (reg "%inc") = some (.int 64 (BitVec.ofNat 64 (i + 1))) :=
          evalOperand_reg_of (("%k.addr.011",
              .int 64 (BitVec.ofNat 64 (k + ctpop (ent.get ⟨i, hilen⟩)))) :: e2)
            sC "%inc" (.int 64 (BitVec.ofNat 64 (i + 1)))
            ((lookupName_cons_ne _ _ (by decide)).trans hinc2)
        have hr1p : 1 ≤ r' := by omega
        have hr2p : (i + 1) + r' = jj + 1 := by omega
        have hrec :=
          ih (i + 1) (k + ctpop (ent.get ⟨i, hilen⟩)) e2
            { sC with pc := "for.body", pre := some "cleanup" }
            "cleanup" (reg "%k.addr.1") (reg "%inc")
            hr1p hr2p rfl rfl rfl rfl hvkp hvip hframe2 hkNext hmem2
        refine runFuel_mono_le
          (n := (b8BlockSteps (ent.get ⟨i, hilen⟩) + 1) + (b8RunSteps (ent.drop (i + 1)) + r' + 1)) ?_ ?_
        · rw [b8RunSteps_drop_succ ent i hilen]; omega
        · rw [runFuel_of_Jumps (Jumps.comp hjumps1 (Jumps.one hjump2))]
          exact hrec


/-! ### The entry stream

From the initial state: the entry test, the block loop, and the statement the
block layer asks for. -/

/-- **The entry stream, in the block kernel.**  The run from the initial state
returns the stream's cursor and the fold of every block's stores; the lanes up to
the cursor hold the model's positions, and every read outside the output span is
unchanged. -/
theorem entry_b8_refines (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (mem' : Mem),
      runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
        { (initState entryB8Function [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 mem' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk ∧
      -- the frame starts at the *written* extent's base, not at the buffer's: the
      -- lanes the call appends are written from `o + 4 * k`, so the prefix written
      -- by an earlier call is untouched.  `b8MemFold_frame` proves exactly this
      -- hypothesis (`p + n ≤ o + 4 * k ∨ …`), so the statement is the fold's own.
      (∀ a, a < o + 4 * k ∨ o + 4 * (k' + 7) ≤ a → readByte mem' a = readByte mem a) := by
  let S0 : State := { (initState entryB8Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0⟩ := b8_init blk0 nblk k mem e o
  by_cases hz : nblk = 0
  · -- no block runs: the entry test branches straight to `for.cond.cleanup`
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      b8Entry_step_zero S0.env S0 nblk hpc0 hNb hz
    have hk1 : lookupName e1 "%k" = some (.int 64 (BitVec.ofNat 64 k)) := by
      have h := b8_preserved b8Entry.instrs ["%k"] (by decide)
        (withEnv S0.env S0) (withEnv e1 S0) hrun1 "%k" (by decide)
      have h' : lookupName e1 "%k" = lookupName S0.env "%k" := by simpa only [withEnv] using h
      exact h'.trans hk0
    obtain ⟨e2, hbody2, hstep2, hk2⟩ :=
      b8Exit_step e1 { S0 with pc := "for.cond.cleanup", pre := some "entry" } k
        "entry" (.reg "%k") rfl rfl rfl (evalOperand_reg_of e1 _ _ _ hk1)
    have he : ent = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hfuel : b8RunSteps ent + nblk + 2 = 2 := by
      rw [he, hz]; rfl
    refine ⟨k, mem, ?_, ?_, ?_, ?_⟩
    · show runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k))) mem)
      rw [hfuel]
      exact (b8_runFuel_jump hstep1).trans (b8_runFuel_ret (n := 0) hstep2)
    · rw [he]; simp
    · rw [he]; simp [streamPrefix, readLanes32]
    · intro a ha
      rfl
  · -- the loop runs: `entry` falls into `for.body` with the parameter cells
    have hpos : 1 ≤ nblk := by omega
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      b8Entry_step_pos S0.env S0 nblk hpc0 hNb (by omega) hz
    have hfr : ∀ n ∈ ["%ent", "%blk0", "%nblk", "%out", "%k"],
        lookupName e1 n = lookupName S0.env n := by
      intro n hn
      have h := b8_preserved b8Entry.instrs ["%ent", "%blk0", "%nblk", "%out", "%k"] (by decide)
        (withEnv S0.env S0) (withEnv e1 S0) hrun1 n hn
      simpa only [withEnv] using h
    have hframe1 : B8Frame e1 e o blk0 nblk :=
      ⟨(hfr "%ent" (by decide)).trans hent0, (hfr "%blk0" (by decide)).trans hblk0,
        (hfr "%nblk" (by decide)).trans hNb, (hfr "%out" (by decide)).trans hout0⟩
    obtain ⟨e2, mem2, hrun2, hmem2⟩ :=
      b8_loop_run ent blk0 nblk k o e mem hent hblk hk63 hdisj hnblk
        nblk 0 k e1 { S0 with pc := "for.body", pre := some "entry" }
        "entry" (.reg "%k") (lit 64 0)
        hpos (by omega) rfl rfl rfl rfl
        (evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
        (by
          show evalOperand _ (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
          rw [ofInt64_zero]
          rfl)
        hframe1 rfl rfl
    refine ⟨pos8Cursor ent k, mem2, ?_, ?_, ?_, ?_⟩
    · -- one entry step, then the loop's own run
      show runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor ent k)))) mem2)
      rw [show b8RunSteps ent + nblk + 2 = (b8RunSteps ent + nblk + 1) + 1 from by omega]
      rw [b8_runFuel_jump hstep1]
      exact hrun2
    · -- the count
      rw [pos8Cursor_eq_sum]
    · -- the words
      rw [hmem2]
      have hcap : 64 * blk0 + 64 * ent.length < 2 ^ 32 := by
        rw [← hnblk]; omega
      have hb : (64 * blk0) % 64 = 0 := Nat.mul_mod_right 64 blk0
      have hlen : pos8Cursor ent k - k = (ent.map ctpop).sum := by
        rw [pos8Cursor_eq_sum]; omega
      rw [hlen]
      rw [show readLanes32 (b8MemFold o (64 * blk0) k ent mem) (o + 4 * k) ((ent.map ctpop).sum)
          = some (b8Stream ent (64 * blk0)) from b8MemFold_read o (64 * blk0) k ent mem hb hcap]
      rw [b8Stream_eq_mapIdx, pos8Stream_eq_streamPrefix, hnblk]
    · -- the frame
      intro a ha
      rw [hmem2]
      exact readByte_congr_of_readBytes_one _ _ a
        (b8MemFold_frame (o := o) (base := 64 * blk0) (k := k) (ent := ent)
          (mem := mem) a 1 (by
            rcases ha with h | h
            · left; omega
            · right
              have hc : pos8Cursor ent k ≤ k + 64 * ent.length := by
                have h1 := pos8Cursor_le ent k
                omega
              omega))

/-- **The entry stream's `ub`.**  If the fold's mask word at block `j` cannot be
read, the run from the initial state is `ub`: the entry test and every earlier
block step, and the failing block's own load is the instruction that fails. -/
theorem entry_b8_undefined_of_no_read (ent : List (BitVec 64)) (blk0 nblk k : Nat)
    (mem : Mem) (e o : Nat) (j : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hj : j < nblk)
    (hfail : readBytes (b8MemFold o (64 * blk0) k (ent.take j) mem) (e + 8 * j) 8 = none)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
        { (initState entryB8Function [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
      = some .ub := by
  let S0 : State := { (initState entryB8Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0⟩ := b8_init blk0 nblk k mem e o
  have hpos : 1 ≤ nblk := by omega
  obtain ⟨e1, hrun1, hstep1, _⟩ :=
    b8Entry_step_pos S0.env S0 nblk hpc0 hNb (by omega) (by omega)
  have hfr : ∀ n ∈ ["%ent", "%blk0", "%nblk", "%out", "%k"],
      lookupName e1 n = lookupName S0.env n := by
    intro n hn
    have h := b8_preserved b8Entry.instrs ["%ent", "%blk0", "%nblk", "%out", "%k"] (by decide)
      (withEnv S0.env S0) (withEnv e1 S0) hrun1 n hn
    simpa only [withEnv] using h
  have hframe1 : B8Frame e1 e o blk0 nblk :=
    ⟨(hfr "%ent" (by decide)).trans hent0, (hfr "%blk0" (by decide)).trans hblk0,
      (hfr "%nblk" (by decide)).trans hNb, (hfr "%out" (by decide)).trans hout0⟩
  -- the loop stops at the failing block: `j + 1` blocks of `for.body` remain
  have hrun2 :
      runFuel entryCalls (b8RunSteps (ent.drop 0) + (j + 1) + 1) entryB8Function
          (withEnv e1 ({ S0 with pc := "for.body", pre := some "entry" } : State)) = some .ub :=
    b8_loop_run_ub ent blk0 nblk k o e mem j hent hblk hk63 hdisj hnblk hj hfail
      (j + 1) 0 k e1 { S0 with pc := "for.body", pre := some "entry" }
      "entry" (.reg "%k") (lit 64 0)
      (by omega) (by omega) rfl rfl rfl rfl
      (evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
      (by
        show evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: e1)
            ({ S0 with pc := "for.body", pre := some "entry" } : State))
          (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
        rw [ofInt64_zero]
        rfl)
      hframe1 rfl rfl
  have hmn : b8RunSteps (ent.drop 0) + (j + 1) + 1 ≤ b8RunSteps ent + nblk + 1 := by
    rw [show ent.drop 0 = ent from rfl]
    omega
  show runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function (withEnv S0.env S0) = some .ub
  rw [show b8RunSteps ent + nblk + 2 = (b8RunSteps ent + nblk + 1) + 1 from by omega]
  rw [b8_runFuel_jump hstep1]
  exact runFuel_mono_le hmn hrun2

/-- **The two kernels emit the same stream.**  Run from their own initial states
with the same document, block base, output base and cursor, POS8 and B8 return the
same cursor, and the lanes each wrote from its own memory are the same word for
word: both are the stream's prefix up to that cursor.  The comparison is at each
side's own frame, because the two runs end holding different memories. -/
theorem entry_pos8_b8_agree (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab outCap : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hdisjP : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
              (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hdisjB : e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e)
    (hcap : k + 64 * ent.length + 9 ≤ outCap)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (kP kB : Nat) (mP mB : Mem),
      runFuel entryCalls (3 * nblk + 3) entryPos8Function
          { (initState entryPos8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 kP))) mP) ∧
      runFuel entryCalls (b8RunSteps ent + nblk + 2) entryB8Function
          { (initState entryB8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k]) with mem := mem }
        = some (.ret (some (.int 64 (BitVec.ofNat 64 kB))) mB) ∧
      kP = kB ∧
      readLanes32 mP (o + 4 * k) (kP - k) = readLanes32 mB (o + 4 * k) (kB - k) := by
  obtain ⟨kP, mP, hrunP, hkP, hlanesP, _⟩ :=
    entry_pos8_refines ent blk0 nblk k mem e o tab outCap hnblk hblk hent htab hdisjP hcap hk63
  obtain ⟨kB, mB, hrunB, hkB, hlanesB, _⟩ :=
    entry_b8_refines ent blk0 nblk k mem e o hnblk hblk hent hdisjB hk63
  exact ⟨kP, kB, mP, mB, hrunP, hrunB, hkP.trans hkB.symm, hlanesP.trans hlanesB.symm⟩

end LeanLLVM.Refinement.JsonB8Steps
