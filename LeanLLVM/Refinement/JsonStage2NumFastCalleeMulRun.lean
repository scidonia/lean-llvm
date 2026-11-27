/-
`stk_mul_u64`'s group loop, and the run it carries.

`JsonStage2NumFastCalleeMul` pins `for.body.i` and proves its four limb steps one
at a time; `JsonStage2NumFastCalleeMulStep` composes them into a single control
step at an arbitrary state the block wrote; `JsonStage2NumFastCalleeMulArith` reads
the emitted `i128` words as the model's `Nat` fold.  What none of them states is
the loop: one visit of `for.body.i` is one step, and the loop is a budget over
visits.  This module is that budget, as a `LoopFuel.BoundLoop` instance, and the
run it yields.

**The measure is the group count.**  A visit carries `%indvars.iv.i` (the limb
index) and `%niter` (the same number, counted by four), and leaves the loop when
`%niter + 4 = %unroll_iter`, i.e. when `c + 1 = G` groups are done.  The instance
therefore takes the counter `c` as its measure, `G - 1` as its bound and `1` as the
per-visit cost, so its whole budget is `G` control steps where `G = limbs.length /
4` is a term of the body's arguments and not of any particular run's trip count.

**The invariant carries the fold, not the indices.**  `stkMulFold` is a function of
a `Nat` list, so the memory is stated as the written prefix of `limbs.take (4 * c)`
— `pre limbs mw c` below — and the reads a visit makes are stated once, of the
memory the loop started from, over the unconsumed suffix `limbs.drop (4 * c)`.  A
visit appends its four words to the prefix and moves the carry to `car limbs mw (c +
1)`, so no visit re-derives a limb's word.  Both are named rather than spelled out
because every goal of the induction mentions them: a statement that carried the
`stkMulFold` term would make each rewrite re-check a term four carries deep.

**The reads of the original memory are the frame, and they are a hypothesis.**
A visit reads the four limbs it multiplies out of the memory, but the invariant's
prefix covers only the limbs already written.  The reads are therefore stated of
the *original* memory over the whole remaining suffix — `hreads` below — and each
visit's four reads follow from `readBytes_stkWriteLimbs_above`: the prefix's end is
`a + 8 * (4 * c)`, and every limb a visit reads is at or above it.  Without that
premise the invariant would have to know each unwritten limb from the state, which
is the one thing the emitted block does not leave there.

**The two arms are one control step each.**  Each is the block's denotation
(`stkMulGrp_denote` at the invariant's own terms) and the branch's bit
(`stkMulGrp_step_taken` / `stkMulGrp_step_loop`), with the invariant's next
instance read off the visit's cells.  The test's bit is a function of the counter
alone, because both operands are `BitVec.ofNat` of a small multiple of four.

There is no `sorry`, `admit`, `native_decide`, `bv_decide` or `umax` below; the
`Classical.choice` the block's denotation brings is named in the pins at the end.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalleeMulArith
import LeanLLVM.Refinement.LoopFuel

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

namespace StkMulLoop

/-! ### Small numerals, and the emitted index law

A visit's four addresses are `%indvars.iv.i` and its three `or`-ed successors.
Since `%indvars.iv.i` is a multiple of four, each `or` adds its small index; the
tree's `Nat` exports resolve a mask of the form `2 ^ n - 1`, and `2` — which is not
of that form — is read off `Nat.testBit`. -/

/-- A multiple of four has bit one clear. -/
theorem and_two_of_four (k : Nat) : 4 * k &&& 2 = 0 := by
  show Nat.bitwise and (4 * k) 2 = 0
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.zero_testBit, Nat.testBit_bitwise (f := and) (by decide) (4 * k) 2 j]
  have h2 : (2 : Nat).testBit j = decide (1 = j) := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl]
    exact Nat.testBit_two_pow
  have h4 : (4 * k).testBit j = (decide (j ≥ 2) && k.testBit (j - 2)) := by
    rw [show 4 * k = 2 ^ 2 * k from by omega]
    exact Nat.testBit_two_pow_mul
  rw [h2, h4]
  by_cases h : decide (1 = j) = true
  · have hj : j = 1 := (of_decide_eq_true h).symm
    subst hj
    simp
  · rw [show decide (1 = j) = false from by simpa using h]
    simp

/-- A multiple of four has its low two bits clear, at any mask below four. -/
theorem and_lt_four (k i : Nat) (hi1 : 1 ≤ i) (hi4 : i < 4) : 4 * k &&& i = 0 := by
  have h1 : 4 * k &&& 1 = 0 := by
    rw [show 1 = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have h3 : 4 * k &&& 3 = 0 := by
    rw [show 3 = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hcases with rfl | rfl | rfl
  · exact h1
  · exact and_two_of_four k
  · exact h3

/-- `or`-ing a small index into a multiple of four adds it. -/
theorem or_small_of_four (k i : Nat) (hi1 : 1 ≤ i) (hi4 : i < 4) :
    4 * k ||| i = 4 * k + i :=
  Nat.lor_eq_add_of_and_eq_zero _ _ (and_lt_four k i hi1 hi4)

/-- The emitted index at `Nat`: `%indvars.iv.i ||| i` is the limb position. -/
theorem or_idx_toNat (k i : Nat) (hi1 : 1 ≤ i) (hi4 : i < 4)
    (hk : 4 * k < 2 ^ 64) :
    ((BitVec.ofNat 64 (4 * k) ||| BitVec.ofNat 64 i)).toNat = 4 * k + i := by
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64)]
  exact or_small_of_four k i hi1 hi4

/-- A small `Nat` at `i64`, read back. -/
theorem ofNat64_val (n : Nat) (hn : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- A small `Nat` at `i128`, read back. -/
theorem ofNat128_val (n : Nat) (hn : n < 2 ^ 128) : (BitVec.ofNat 128 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The counter's step: `%niter + 4` is the next visit's count. -/
theorem count_step (c : Nat) (hc : 4 * c < 2 ^ 63) :
    BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64 =
      BitVec.ofNat 64 (4 * (c + 1)) := by
  apply BitVec.toNat_inj.mp
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 4 * c < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (4 : Nat) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * c + 4 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * (c + 1) < 2 ^ 64)]
  omega

/-- `evalICmp .eq` at equal operands is one. -/
theorem cmp_eq_true {w : Nat} {a b : BitVec w} (h : a = b) :
    evalICmp .eq a b = 0x0000000000000001#1 := by
  simp [evalICmp, h]

/-- `evalICmp .eq` at unequal operands is zero. -/
theorem cmp_eq_false {w : Nat} {a b : BitVec w} (h : a ≠ b) :
    evalICmp .eq a b = 0x0000000000000000#1 := by
  simp [evalICmp, h]

/-! ### The fold: its length, and one group's advance -/

/-- The words a fold keeps are as many as the limbs it consumes. -/
theorem fold_length (l : List Nat) (m c : Nat) :
    (stkMulFold l m c).1.length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons w ws ih =>
      rw [stkMulFold_cons]
      simp only [List.length_cons, ih]

/-- One limb's fold step, read at the word the emitted store writes and the carry
the emitted shift leaves. -/
theorem fold_emit_cons (x : BitVec 64) (mw cv : BitVec 128) (ws : List Nat)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    stkMulFold (x.toNat :: ws) mw.toNat cv.toNat =
      ((BitVec.ofNat 64
          ((BitVec.ofNat 128 x.toNat * mw + cv).toNat % 2 ^ 64)).toNat ::
          (stkMulFold ws mw.toNat (stkMulCarry x mw cv).toNat).1,
        (stkMulFold ws mw.toNat (stkMulCarry x mw cv).toNat).2) := by
  rw [stkMulFold_cons, stkMulWord_toNat x mw cv hmw hcv,
    stkMulCarry_toNat x mw cv hmw hcv]

/-- One group: four fold steps at the four words the limb stores write and the
carry the fourth leaves. -/
theorem fold_emit_four (x0 x1 x2 x3 : BitVec 64) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    stkMulFold [x0.toNat, x1.toNat, x2.toNat, x3.toNat] mw.toNat cv.toNat =
      ([(BitVec.ofNat 64
          ((BitVec.ofNat 128 x0.toNat * mw + cv).toNat % 2 ^ 64)).toNat,
        (BitVec.ofNat 64
          ((BitVec.ofNat 128 x1.toNat * mw + stkMulCarry x0 mw cv).toNat % 2 ^ 64)).toNat,
        (BitVec.ofNat 64
          ((BitVec.ofNat 128 x2.toNat * mw +
            stkMulCarry x1 mw (stkMulCarry x0 mw cv)).toNat % 2 ^ 64)).toNat,
        (BitVec.ofNat 64
          ((BitVec.ofNat 128 x3.toNat * mw +
            stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))).toNat
              % 2 ^ 64)).toNat],
       (stkMulCarry x3 mw
          (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)))).toNat) := by
  have h1 := stkMulCarry_lt x0 mw cv hmw hcv
  have h2 := stkMulCarry_lt x1 mw (stkMulCarry x0 mw cv) hmw h1
  have h3 := stkMulCarry_lt x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)) hmw h2
  rw [fold_emit_cons x0 mw cv _ hmw hcv,
    fold_emit_cons x1 mw (stkMulCarry x0 mw cv) _ hmw h1,
    fold_emit_cons x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)) _ hmw h2,
    fold_emit_cons x3 mw
      (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))) [] hmw h3]
  rfl

/-- **One visit's fold advance.**  Appending a group's four limbs moves the fold
four words on, with the fourth limb's carry. -/
theorem fold_emit_group (cons : List Nat) (x0 x1 x2 x3 : BitVec 64) (m : Nat)
    (mw cv : BitVec 128) (hmw : mw.toNat = m) (hmwlt : mw.toNat < 2 ^ 64)
    (hcv : cv.toNat < 2 ^ 64) (hfold : (stkMulFold cons m 0).2 = cv.toNat) :
    stkMulFold (cons ++ [x0.toNat, x1.toNat, x2.toNat, x3.toNat]) m 0 =
      ((stkMulFold cons m 0).1 ++
        [(BitVec.ofNat 64
            ((BitVec.ofNat 128 x0.toNat * mw + cv).toNat % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 x1.toNat * mw + stkMulCarry x0 mw cv).toNat
              % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 x2.toNat * mw +
              stkMulCarry x1 mw (stkMulCarry x0 mw cv)).toNat % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 x3.toNat * mw +
              stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))).toNat
                % 2 ^ 64)).toNat],
       (stkMulCarry x3 mw
          (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)))).toNat) := by
  rw [stkMulFold_append, hfold, show m = mw.toNat from hmw.symm,
    fold_emit_four x0 x1 x2 x3 mw cv hmwlt hcv]

/-! ### Lists: reads past a prefix, and a group's four -/

/-- A read four places along a list is the remainder's read. -/
theorem getD_drop_offset (l : List Nat) (n j : Nat) :
    (l.drop n).getD j 0 = l.getD (n + j) 0 := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n => simp [ih, Nat.succ_add]

/-- Splitting a prefix off a list at a sum. -/
theorem take_split (l : List Nat) (n m : Nat) :
    l.take (n + m) = l.take n ++ (l.drop n).take m := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp
      | succ n =>
          cases m with
          | zero => simp
          | succ m =>
              have h : n + 1 + (m + 1) = (n + (m + 1)) + 1 := by omega
              rw [h, List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons, ih,
                List.cons_append]

/-- A read off the end of a four-word append is the last word. -/
theorem getD_append_four (l : List Nat) (a b c d : Nat) :
    (l ++ [a, b, c, d]).getD (l.length + 3) 0 = d := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.cons_append, List.length_cons, List.getD_cons_succ]
      exact ih

/-- A list with four elements is its first four and the rest. -/
theorem four_cons_drop (rest : List Nat) (h : 4 ≤ rest.length) :
    rest = rest.getD 0 0 :: rest.getD 1 0 :: rest.getD 2 0 :: rest.getD 3 0 ::
      rest.drop 4 := by
  match rest, h with
  | a :: b :: c :: d :: tl, _ => rfl

/-- A list's `take` at or past its length is the list. -/
theorem take_eq_self (l : List Nat) (n : Nat) (h : l.length ≤ n) : l.take n = l := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
      cases n with
      | zero => simp at h
      | succ n =>
          have hlen : xs.length ≤ n := by simp only [List.length_cons] at h; omega
          rw [List.take_succ_cons, ih n hlen]

/-- A group's carry after four limbs is below `2 ^ 64`. -/
theorem carry_four_lt (w0 w1 w2 w3 : Nat) (mw cv : BitVec 128)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    (stkMulCarry (BitVec.ofNat 64 w3) mw
      (stkMulCarry (BitVec.ofNat 64 w2) mw
        (stkMulCarry (BitVec.ofNat 64 w1) mw
          (stkMulCarry (BitVec.ofNat 64 w0) mw cv)))).toNat < 2 ^ 64 := by
  have h1 : (stkMulCarry (BitVec.ofNat 64 w0) mw cv).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw hcv
  have h2 : (stkMulCarry (BitVec.ofNat 64 w1) mw
      (stkMulCarry (BitVec.ofNat 64 w0) mw cv)).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw h1
  have h3 : (stkMulCarry (BitVec.ofNat 64 w2) mw
      (stkMulCarry (BitVec.ofNat 64 w1) mw
        (stkMulCarry (BitVec.ofNat 64 w0) mw cv))).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw h2
  exact stkMulCarry_lt _ mw _ hmw h3

/-- The four limbs a visit is about to multiply are below `2 ^ 64`: they are the
suffix's first four, and the caller bounds every limb. -/
theorem group_limbs_lt (limbs : List Nat) (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64)
    (c : Nat) (w0 w1 w2 w3 : Nat) (rest : List Nat)
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest) :
    w0 < 2 ^ 64 ∧ w1 < 2 ^ 64 ∧ w2 < 2 ^ 64 ∧ w3 < 2 ^ 64 := by
  have h0 := hlimbslt (4 * c + 0)
  rw [← getD_drop_offset limbs (4 * c) 0, hdrop, List.getD_cons_zero] at h0
  have h1 := hlimbslt (4 * c + 1)
  rw [← getD_drop_offset limbs (4 * c) 1, hdrop, List.getD_cons_succ,
    List.getD_cons_zero] at h1
  have h2 := hlimbslt (4 * c + 2)
  rw [← getD_drop_offset limbs (4 * c) 2, hdrop, List.getD_cons_succ,
    List.getD_cons_succ, List.getD_cons_zero] at h2
  have h3 := hlimbslt (4 * c + 3)
  rw [← getD_drop_offset limbs (4 * c) 3, hdrop, List.getD_cons_succ,
    List.getD_cons_succ, List.getD_cons_succ, List.getD_cons_zero] at h3
  exact ⟨h0, h1, h2, h3⟩

/-! ### The fold's two accumulators, named

`pre limbs mw c` is the prefix the loop has written after `c` groups and `car limbs
mw c` the carry it carries into the next one.  Every statement below is about these
two rather than about `stkMulFold`; the two differ only in the four-carries-deep
term the fold's definition spells, and naming it keeps each goal small enough to
rewrite without re-elaborating that term. -/

/-- The fold's written prefix after `c` groups. -/
def pre (limbs : List Nat) (mw : BitVec 128) (c : Nat) : List Nat :=
  (stkMulFold (limbs.take (4 * c)) mw.toNat 0).1

/-- The fold's carry after `c` groups. -/
def car (limbs : List Nat) (mw : BitVec 128) (c : Nat) : Nat :=
  (stkMulFold (limbs.take (4 * c)) mw.toNat 0).2

/-- The prefix is as long as the limbs it consumed. -/
theorem pre_length (limbs : List Nat) (mw : BitVec 128) (c : Nat)
    (h : 4 * c ≤ limbs.length) : (pre limbs mw c).length = 4 * c := by
  unfold pre
  rw [fold_length, List.length_take, Nat.min_eq_left h]

/-- The next visit's `take` is this visit's plus the group it multiplies. -/
theorem take_succ_eq (limbs : List Nat) (w0 w1 w2 w3 : Nat) (rest : List Nat) (c : Nat)
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest)
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) (hw2 : w2 < 2 ^ 64) (hw3 : w3 < 2 ^ 64) :
    limbs.take (4 * (c + 1)) =
      limbs.take (4 * c) ++ [(BitVec.ofNat 64 w0).toNat, (BitVec.ofNat 64 w1).toNat,
        (BitVec.ofNat 64 w2).toNat, (BitVec.ofNat 64 w3).toNat] := by
  have h4 : (w0 :: w1 :: w2 :: w3 :: rest).take 4 = [w0, w1, w2, w3] := rfl
  rw [show 4 * (c + 1) = 4 * c + 4 by omega, take_split, hdrop, h4]
  simp only [ofNat64_val _ hw0, ofNat64_val _ hw1, ofNat64_val _ hw2,
    ofNat64_val _ hw3]

/-- The prefix after a visit: the four words the block's stores wrote, appended. -/
theorem pre_succ_eq (limbs : List Nat) (mw : BitVec 128) (c : Nat)
    (w0 w1 w2 w3 : Nat) (rest : List Nat) (hmw : mw.toNat < 2 ^ 64)
    (hfoldlt : car limbs mw c < 2 ^ 64)
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest)
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) (hw2 : w2 < 2 ^ 64) (hw3 : w3 < 2 ^ 64) :
    pre limbs mw (c + 1) =
      pre limbs mw c ++
        [(BitVec.ofNat 64
            ((BitVec.ofNat 128 (BitVec.ofNat 64 w0).toNat * mw +
              (BitVec.ofNat 128 (car limbs mw c))).toNat % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 (BitVec.ofNat 64 w1).toNat * mw +
              stkMulCarry (BitVec.ofNat 64 w0) mw
                (BitVec.ofNat 128 (car limbs mw c))).toNat % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 (BitVec.ofNat 64 w2).toNat * mw +
              stkMulCarry (BitVec.ofNat 64 w1) mw
                (stkMulCarry (BitVec.ofNat 64 w0) mw
                  (BitVec.ofNat 128 (car limbs mw c)))).toNat % 2 ^ 64)).toNat,
          (BitVec.ofNat 64
            ((BitVec.ofNat 128 (BitVec.ofNat 64 w3).toNat * mw +
              stkMulCarry (BitVec.ofNat 64 w2) mw
                (stkMulCarry (BitVec.ofNat 64 w1) mw
                  (stkMulCarry (BitVec.ofNat 64 w0) mw
                    (BitVec.ofNat 128 (car limbs mw c))))).toNat % 2 ^ 64)).toNat] := by
  have hcvlt : (BitVec.ofNat 128 (car limbs mw c)).toNat < 2 ^ 64 := by
    rw [ofNat128_val _ (by omega)]
    exact hfoldlt
  have hcv : (BitVec.ofNat 128 (car limbs mw c)).toNat = car limbs mw c :=
    ofNat128_val _ (by omega)
  have hfold : (stkMulFold (limbs.take (4 * c)) mw.toNat 0).2 =
      (BitVec.ofNat 128 (car limbs mw c)).toNat := hcv.symm
  unfold pre
  rw [take_succ_eq limbs w0 w1 w2 w3 rest c hdrop hw0 hw1 hw2 hw3]
  exact congrArg Prod.fst (fold_emit_group (limbs.take (4 * c))
    (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2) (BitVec.ofNat 64 w3)
    mw.toNat mw (BitVec.ofNat 128 (car limbs mw c)) rfl hmw hcvlt hfold)

/-- The carry after a visit: the fourth limb's carry out. -/
theorem car_succ_eq (limbs : List Nat) (mw : BitVec 128) (c : Nat)
    (w0 w1 w2 w3 : Nat) (rest : List Nat) (hmw : mw.toNat < 2 ^ 64)
    (hfoldlt : car limbs mw c < 2 ^ 64)
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest)
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) (hw2 : w2 < 2 ^ 64) (hw3 : w3 < 2 ^ 64) :
    car limbs mw (c + 1) =
      (stkMulCarry (BitVec.ofNat 64 w3) mw
        (stkMulCarry (BitVec.ofNat 64 w2) mw
          (stkMulCarry (BitVec.ofNat 64 w1) mw
            (stkMulCarry (BitVec.ofNat 64 w0) mw
              (BitVec.ofNat 128 (car limbs mw c)))))).toNat := by
  have hcvlt : (BitVec.ofNat 128 (car limbs mw c)).toNat < 2 ^ 64 := by
    rw [ofNat128_val _ (by omega)]
    exact hfoldlt
  have hcv : (BitVec.ofNat 128 (car limbs mw c)).toNat = car limbs mw c :=
    ofNat128_val _ (by omega)
  have hfold : (stkMulFold (limbs.take (4 * c)) mw.toNat 0).2 =
      (BitVec.ofNat 128 (car limbs mw c)).toNat := hcv.symm
  unfold car
  rw [take_succ_eq limbs w0 w1 w2 w3 rest c hdrop hw0 hw1 hw2 hw3]
  exact congrArg Prod.snd (fold_emit_group (limbs.take (4 * c))
    (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2) (BitVec.ofNat 64 w3)
    mw.toNat mw (BitVec.ofNat 128 (car limbs mw c)) rfl hmw hcvlt hfold)

/-! ### The memory a visit leaves

`stkMulGrpMem` writes four words at the four emitted addresses; `stkWriteLimbs`
writes four words at `a + 8 * (4c)`, `+ 8`, `+ 16`, `+ 24`.  The two are the same
memory; the lemma states it with the addresses already reduced to the second form,
so the loop never rewrites inside a `writeBytes`. -/

/-- The four writes of a visit are the prefix append, at the four words the fold
appends. -/
theorem grpMem_eq_writeLimbs (mem : Mem) (a : Nat) (iv : BitVec 64) (cv mw : BitVec 128)
    (x0 x1 x2 x3 : BitVec 64) (c : Nat) (w0 w1 w2 w3 : Nat)
    (hiv : iv.toNat = 4 * c)
    (h1 : (iv ||| 0x0000000000000001#64).toNat = 4 * c + 1)
    (h2 : (iv ||| 0x0000000000000002#64).toNat = 4 * c + 2)
    (h3 : (iv ||| 0x0000000000000003#64).toNat = 4 * c + 3)
    (hw0 : w0 = (BitVec.ofNat 64
      ((BitVec.ofNat 128 x0.toNat * mw + cv).toNat % 2 ^ 64)).toNat)
    (hw1 : w1 = (BitVec.ofNat 64
      ((BitVec.ofNat 128 x1.toNat * mw + stkMulCarry x0 mw cv).toNat % 2 ^ 64)).toNat)
    (hw2 : w2 = (BitVec.ofNat 64
      ((BitVec.ofNat 128 x2.toNat * mw +
        stkMulCarry x1 mw (stkMulCarry x0 mw cv)).toNat % 2 ^ 64)).toNat)
    (hw3 : w3 = (BitVec.ofNat 64
      ((BitVec.ofNat 128 x3.toNat * mw +
        stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))).toNat
          % 2 ^ 64)).toNat)
    (hmw : mw.toNat < 2 ^ 64) (hcv : cv.toNat < 2 ^ 64) :
    stkMulGrpMem mem a iv cv mw x0 x1 x2 x3 =
      stkWriteLimbs mem (a + 8 * (4 * c)) [w0, w1, w2, w3] := by
  have h1c := stkMulCarry_lt x0 mw cv hmw hcv
  have h2c := stkMulCarry_lt x1 mw (stkMulCarry x0 mw cv) hmw h1c
  have h3c := stkMulCarry_lt x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)) hmw h2c
  have h8 : (Ty.int 64).sizeBytes = 8 := rfl
  have e0 : a + (4 * c) * 8 = a + 8 * (4 * c) := by rw [Nat.mul_comm]
  have e1 : a + (4 * c + 1) * 8 = a + 8 * (4 * c) + 8 := by omega
  have e2 : a + (4 * c + 2) * 8 = a + 8 * (4 * c) + 8 + 8 := by omega
  have e3 : a + (4 * c + 3) * 8 = a + 8 * (4 * c) + 8 + 8 + 8 := by omega
  rw [hw0, hw1, hw2, hw3]
  simp only [stkMulGrpMem, stkWriteLimbs, h8, hiv, h1, h2, h3,
    List.length_cons, List.length_nil]
  rw [stkMulWord_toNat x0 mw cv hmw hcv,
    stkMulWord_toNat x1 mw (stkMulCarry x0 mw cv) hmw h1c,
    stkMulWord_toNat x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv)) hmw h2c,
    stkMulWord_toNat x3 mw
      (stkMulCarry x2 mw (stkMulCarry x1 mw (stkMulCarry x0 mw cv))) hmw h3c]
  simp only [Nat.mod_mod, e0, e1, e2, e3]

/-- A cell of the `phi` run's three-entry edge, for a name the run does not bind. -/
theorem lookupName_phi_triple_ne (a3 b3 c3 : Value) (env : Env) (n : String)
    (h1 : "%niter" ≠ n) (h2 : "%carry.029.i" ≠ n) (h3 : "%indvars.iv.i" ≠ n) :
    lookupName (("%niter", a3) :: ("%carry.029.i", b3) :: ("%indvars.iv.i", c3) ::
      env) n = lookupName env n := by
  rw [lookupName_cons_ne _ _ h1, lookupName_cons_ne _ _ h2,
    lookupName_cons_ne _ _ h3]

/-! ### The four reads a visit makes

The invariant states the reads once, of the memory the loop started from, over the
whole unconsumed suffix.  A visit reads its four limbs at the four emitted
addresses, which are the suffix's first four positions; the prefix's end is
`a + 8 * (4 * c)`, so every one of them is above it and
`readBytes_stkWriteLimbs_above` hands the read back to the original memory. -/

/-- A visit's four reads, at the four addresses its limb steps form. -/
theorem group_reads (mem0 : Mem) (a : Nat) (mw : BitVec 128) (limbs : List Nat)
    (c : Nat) (s : State) (w0 w1 w2 w3 : Nat) (rest : List Nat)
    (x0 x1 x2 x3 : BitVec 64)
    (hprefix : (pre limbs mw c).length = 4 * c)
    (hmem : s.mem = stkWriteLimbs mem0 a (pre limbs mw c))
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest)
    (hreads : ∀ j, readBytes mem0 (a + 8 * (4 * c + j)) 8 =
      some (natToBytes ((limbs.drop (4 * c)).getD j 0) 8))
    (h4c : 4 * c < 2 ^ 64)
    (hx0 : x0.toNat = w0) (hx1 : x1.toNat = w1)
    (hx2 : x2.toNat = w2) (hx3 : x3.toNat = w3) :
    readBytes s.mem (a + (BitVec.ofNat 64 (4 * c)).toNat * (Ty.int 64).sizeBytes) 8 =
        some (natToBytes x0.toNat 8) ∧
      readBytes s.mem
          (a + (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000001#64).toNat *
            (Ty.int 64).sizeBytes) 8 = some (natToBytes x1.toNat 8) ∧
      readBytes s.mem
          (a + (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000002#64).toNat *
            (Ty.int 64).sizeBytes) 8 = some (natToBytes x2.toNat 8) ∧
      readBytes s.mem
          (a + (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000003#64).toNat *
            (Ty.int 64).sizeBytes) 8 = some (natToBytes x3.toNat 8) := by
  have h8 : (Ty.int 64).sizeBytes = 8 := rfl
  have haddr0 : a + (BitVec.ofNat 64 (4 * c)).toNat * (Ty.int 64).sizeBytes =
      a + 8 * (4 * c + 0) := by
    rw [ofNat64_val (4 * c) h4c, h8]
    omega
  have haddr : ∀ i, 1 ≤ i → i < 4 →
      a + (BitVec.ofNat 64 (4 * c) ||| BitVec.ofNat 64 i).toNat *
          (Ty.int 64).sizeBytes = a + 8 * (4 * c + i) := by
    intro i hi1 hi4
    rw [or_idx_toNat c i hi1 hi4 h4c, h8]
    omega
  have habove : ∀ q : Nat, a + 8 * (4 * c) ≤ q →
      readBytes (stkWriteLimbs mem0 a (pre limbs mw c)) q 8 = readBytes mem0 q 8 := by
    intro q hq
    exact readBytes_stkWriteLimbs_above mem0 _ a q 8 (by rw [hprefix]; exact hq)
  have hget : ∀ j, j < 4 →
      (limbs.drop (4 * c)).getD j 0 = (w0 :: w1 :: w2 :: w3 :: rest).getD j 0 := by
    intro j _
    rw [hdrop]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hmem, haddr0, habove (a + 8 * (4 * c + 0)) (by omega)]
    rw [hreads 0, hget 0 (by omega)]
    simp only [List.getD_cons_zero, hx0]
  · rw [hmem, haddr 1 (by omega) (by omega),
      habove (a + 8 * (4 * c + 1)) (by omega)]
    rw [hreads 1, hget 1 (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hx1]
  · rw [hmem, haddr 2 (by omega) (by omega),
      habove (a + 8 * (4 * c + 2)) (by omega)]
    rw [hreads 2, hget 2 (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hx2]
  · rw [hmem, haddr 3 (by omega) (by omega),
      habove (a + 8 * (4 * c + 3)) (by omega)]
    rw [hreads 3, hget 3 (by omega)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, hx3]

/-! ### The invariant

`c` groups are done.  The state is at the loop's head, the memory is the fold's
written prefix of `limbs.take (4 * c)`, and the unconsumed suffix begins with the
group the next visit multiplies.  `r` is the budget the caller has accounted for;
`c + r + 1 = G` turns it into the distance to the bound.

`Sel` is the disjunction over the two ways a state can arrive at the head: from
the loop's back edge its three `next` cells hold the visit's index, carry and
count; from the preheader the leading `phi` run takes its literals, so the three
values are zero.  It is a `Prop` rather than a computed selector so the arms can
case on it without reducing a dependent match. -/

/-- The head's cells on the back edge: the three values the leading `phi` run
selects, as the previous visit left them. -/
def AtLoopHead (s : State) (iv : BitVec 64) (cv : BitVec 128) (n : BitVec 64) : Prop :=
  s.pre = some "for.body.i" ∧
  lookupName s.env "%indvars.iv.next.i.3" = some (.int 64 iv) ∧
  lookupName s.env "%shr.i.3" = some (.int 128 cv) ∧
  lookupName s.env "%niter.next.3" = some (.int 64 n)

/-- The head's cells on the preheader's edge: the `phi` run takes its literals. -/
def AtLoopEntry (s : State) : Prop :=
  s.pre = some "for.body.lr.ph.i.new"

/-- The three values the leading `phi` run will select at the head. -/
def Sel (s : State) (iv : BitVec 64) (cv : BitVec 128) (n : BitVec 64) : Prop :=
  AtLoopHead s iv cv n ∨ (AtLoopEntry s ∧ iv = 0 ∧ cv = 0 ∧ n = 0)

/-- The group loop's invariant. -/
def Inv (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "for.body.i" ∧
  Sel s (BitVec.ofNat 64 (4 * c))
    (BitVec.ofNat 128 (car limbs mw c))
    (BitVec.ofNat 64 (4 * c)) ∧
  lookupName s.env "%a" = some (.ptr a) ∧
  lookupName s.env "%conv3.i" = some (.int 128 mw) ∧
  lookupName s.env "%unroll_iter" = some (.int 64 (BitVec.ofNat 64 (4 * G))) ∧
  s.mem = stkWriteLimbs mem0 a (pre limbs mw c) ∧
  (∃ (w0 w1 w2 w3 : Nat) (rest : List Nat),
      limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest ∧
      rest.length = 4 * r) ∧
  (∀ j, readBytes mem0 (a + 8 * (4 * c + j)) 8 =
    some (natToBytes ((limbs.drop (4 * c)).getD j 0) 8)) ∧
  car limbs mw c < 2 ^ 64 ∧
  c + r + 1 = G

/-- The head's exit test: `%niter + 4 = %unroll_iter` at the carried counter. -/
def AtBound (G : Nat) : State → Nat → Bool := fun _ c => decide (c + 1 = G)

/-- The memory a visit leaves, at the invariant's own terms: the four writes of
the group at `c`. -/
def stepMem (mem : Mem) (a : Nat) (mw : BitVec 128) (limbs : List Nat) (c : Nat)
    (w0 w1 w2 w3 : Nat) : Mem :=
  stkMulGrpMem mem a (BitVec.ofNat 64 (4 * c))
    (BitVec.ofNat 128 (car limbs mw c)) mw
    (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2) (BitVec.ofNat 64 w3)

/-- `stepMem` is the block's own four writes. -/
theorem stepMem_eq (mem : Mem) (a : Nat) (mw : BitVec 128) (limbs : List Nat) (c : Nat)
    (w0 w1 w2 w3 : Nat) :
    stepMem mem a mw limbs c w0 w1 w2 w3 =
      stkMulGrpMem mem a (BitVec.ofNat 64 (4 * c)) (BitVec.ofNat 128 (car limbs mw c)) mw
        (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2)
        (BitVec.ofNat 64 w3) := rfl

/-- The sum `%add4.i.3` carries: the last written word and the exit carry, read
back as one `i128`.  The store's chain forms `limb * m + carry` below `2 ^ 128`,
so the sum's `Nat` value is its low half plus `2 ^ 64` times its high half — the
fold's last word and the fold's exit carry.  It is stated at `toNat` because that
is the form the emitted sum is read back in. -/
def ExitSumHolds (limbs : List Nat) (mw : BitVec 128) (sum : BitVec 128) : Prop :=
  sum.toNat = (stkMulFold limbs mw.toNat 0).1.getD (limbs.length - 1) 0 +
    2 ^ 64 * (stkMulFold limbs mw.toNat 0).2

/-- What the exit carries. -/
def ExitWord (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (s : State) : Prop :=
  s.mem = stkWriteLimbs mem0 a (stkMulFold limbs mw.toNat 0).1 ∧
  lookupName s.env "%shr.i.3" = some (.int 128
    (BitVec.ofNat 128 (stkMulFold limbs mw.toNat 0).2)) ∧
  lookupName s.env "%indvars.iv.next.i.3" =
    some (.int 64 (BitVec.ofNat 64 (4 * G))) ∧
  lookupName s.env "%a" = some (.ptr a) ∧
  lookupName s.env "%conv3.i" = some (.int 128 mw) ∧
  lookupName s.env "%unroll_iter" =
    some (.int 64 (BitVec.ofNat 64 (4 * G))) ∧
  (∃ sum : BitVec 128, lookupName s.env "%add4.i.3" = some (.int 128 sum) ∧
    ExitSumHolds limbs mw sum)

/-! ### The leading `phi` run at the head

`Sel` says which three values the run will select; this is its denotation.  The
two edges land on the same three cells, so every later statement sees one shape. -/

/-- The three cells the leading `phi` run binds at the head, whatever edge the
state arrived on. -/
theorem phis_of_sel {s : State} {iv : BitVec 64} {cv : BitVec 128} {n : BitVec 64}
    (h : Sel s iv cv n) :
    ∃ q, denoteCode stkMulCalls stkMulGroupPhisInstrs (stateAt s.env s) =
        some (stateAt q s) ∧
      lookupName q "%indvars.iv.i" = some (.int 64 iv) ∧
      lookupName q "%carry.029.i" = some (.int 128 cv) ∧
      lookupName q "%niter" = some (.int 64 n) ∧
      lookupName q "%a" = lookupName s.env "%a" ∧
      lookupName q "%conv3.i" = lookupName s.env "%conv3.i" ∧
      lookupName q "%unroll_iter" = lookupName s.env "%unroll_iter" := by
  rcases h with ⟨hpre, hiv, hcv, hn⟩ | ⟨hpre, rfl, rfl, rfl⟩
  · refine ⟨("%niter", .int 64 n) :: ("%carry.029.i", .int 128 cv) ::
        ("%indvars.iv.i", .int 64 iv) :: s.env, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact stkMul_groupPhis_denote hpre
        (evalOperand_reg_of _ _ _ _ hiv) (evalOperand_reg_of _ _ _ _ hcv)
        (evalOperand_reg_of _ _ _ _ hn)
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    · rw [lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    · exact lookupName_cons_self _ _ _
    all_goals exact lookupName_phi_triple_ne _ _ _ _ _ (by decide) (by decide) (by decide)
  · refine ⟨("%niter", .int 64 0) :: ("%carry.029.i", .int 128 0) ::
        ("%indvars.iv.i", .int 64 0) :: s.env, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact stkMulGrp_phis_entry (calls := stkMulCalls)
        (env := s.env) (s := s) hpre
    · rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    · rw [lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self _ _ _
    · exact lookupName_cons_self _ _ _
    all_goals exact lookupName_phi_triple_ne _ _ _ _ _ (by decide) (by decide) (by decide)

/-! ### The head's test

The block's test is `evalICmp .eq (%niter + 4) %unroll_iter`, and both operands are
`BitVec.ofNat` of a small multiple of four, so the test's value is `AtBound`'s. -/

/-- The emitted test below the bound is zero. -/
theorem bound_test_false {G c : Nat}
    (h4c : 4 * c < 2 ^ 63) (h4c' : 4 * (c + 1) < 2 ^ 64) (h4G : 4 * G < 2 ^ 64)
    (hne : c + 1 ≠ G) :
    evalICmp .eq (BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64)
      (BitVec.ofNat 64 (4 * G)) = 0x0000000000000000#1 := by
  rw [count_step c h4c]
  refine cmp_eq_false ?_
  intro h
  have h2 : 4 * (c + 1) = 4 * G := by
    have := congrArg BitVec.toNat h
    rwa [ofNat64_val _ h4c', ofNat64_val _ h4G] at this
  omega

/-- The emitted test at the bound is one. -/
theorem bound_test_true {G c : Nat}
    (h4c : 4 * c < 2 ^ 63) (h4c' : 4 * (c + 1) < 2 ^ 64) (h4G : 4 * G < 2 ^ 64)
    (heq : c + 1 = G) :
    evalICmp .eq (BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64)
      (BitVec.ofNat 64 (4 * G)) = 0x0000000000000001#1 := by
  rw [count_step c h4c, heq]
  exact cmp_eq_true rfl

/-! ### The block's denotation from the invariant -/

/-- A visit's denotation, read off the invariant: the four limb words are the
suffix's first four, the cells are the block's, and the memory is the four writes.
Both arms consume this one statement. -/
theorem visit_denote {calls : Calls} {mem0 : Mem} {a : Nat} {mw : BitVec 128}
    {G : Nat} {limbs : List Nat} {r : Nat} {s : State} {c : Nat}
    (hG : 4 * G ≤ 96) (hmw : mw.toNat < 2 ^ 64)
    (hlimbs : limbs.length = 4 * G)
    (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64)
    (hinv : Inv mem0 a mw G limbs r s c) :
    ∃ (q' : Env) (w0 w1 w2 w3 : Nat) (rest : List Nat),
      limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest ∧ rest.length = 4 * r ∧
      denoteCode calls stkMulForBodyIInstrs (stateAt s.env s) =
        some (stateAt q' { s with mem := stepMem s.mem a mw limbs c w0 w1 w2 w3 }) ∧
      lookupName q' "%niter.ncmp.3" = some (.int 1 (evalICmp .eq
        (BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64)
        (BitVec.ofNat 64 (4 * G)))) ∧
      lookupName q' "%indvars.iv.next.i.3" =
        some (.int 64 (BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64)) ∧
      lookupName q' "%niter.next.3" =
        some (.int 64 (BitVec.ofNat 64 (4 * c) + 0x0000000000000004#64)) ∧
      lookupName q' "%shr.i.3" = some (.int 128
        (stkMulCarry (BitVec.ofNat 64 w3) mw
          (stkMulCarry (BitVec.ofNat 64 w2) mw
            (stkMulCarry (BitVec.ofNat 64 w1) mw
              (stkMulCarry (BitVec.ofNat 64 w0) mw
                (BitVec.ofNat 128 (car limbs mw c))))))) ∧
      lookupName q' "%add4.i.3" = some (.int 128
        (BitVec.ofNat 128 (BitVec.ofNat 64 w3).toNat * mw +
          stkMulCarry (BitVec.ofNat 64 w2) mw
            (stkMulCarry (BitVec.ofNat 64 w1) mw
              (stkMulCarry (BitVec.ofNat 64 w0) mw
                (BitVec.ofNat 128 (car limbs mw c)))))) ∧
      lookupName q' "%a" = some (.ptr a) ∧
      lookupName q' "%conv3.i" = some (.int 128 mw) ∧
      lookupName q' "%unroll_iter" = some (.int 64 (BitVec.ofNat 64 (4 * G))) := by
  obtain ⟨hpc, hsel, ha, hconv, hunr, hmem, ⟨w0, w1, w2, w3, rest, hdrop, hrest⟩,
    hreads, hfoldlt, hbudget⟩ := hinv
  obtain ⟨q, hphis, hiv, hcv, hn, hqa, hqconv, hqunr⟩ := phis_of_sel hsel
  have ha' : lookupName q "%a" = some (.ptr a) := by rw [hqa]; exact ha
  have hconv' : lookupName q "%conv3.i" = some (.int 128 mw) := by
    rw [hqconv]; exact hconv
  have hunr' : lookupName q "%unroll_iter" = some (.int 64 (BitVec.ofNat 64 (4 * G))) := by
    rw [hqunr]; exact hunr
  have h4c : 4 * c < 2 ^ 64 := by omega
  have hprefix : (pre limbs mw c).length = 4 * c := pre_length limbs mw c (by omega)
  obtain ⟨hw0, hw1, hw2, hw3⟩ := group_limbs_lt limbs hlimbslt c w0 w1 w2 w3 rest hdrop
  have hr := group_reads mem0 a mw limbs c s w0 w1 w2 w3 rest
    (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2) (BitVec.ofNat 64 w3)
    hprefix hmem hdrop hreads h4c (ofNat64_val w0 hw0) (ofNat64_val w1 hw1)
    (ofNat64_val w2 hw2) (ofNat64_val w3 hw3)
  have hpos0 : (BitVec.ofNat 64 (4 * c)).toNat < 2 ^ 63 := by
    rw [ofNat64_val _ (by omega)]; omega
  have hv1 : ((BitVec.ofNat 64 (4 * c) ||| 0x0000000000000001#64)).toNat = 4 * c + 1 :=
    or_idx_toNat c 1 (by decide) (by decide) h4c
  have hv2 : ((BitVec.ofNat 64 (4 * c) ||| 0x0000000000000002#64)).toNat = 4 * c + 2 :=
    or_idx_toNat c 2 (by decide) (by decide) h4c
  have hv3 : ((BitVec.ofNat 64 (4 * c) ||| 0x0000000000000003#64)).toNat = 4 * c + 3 :=
    or_idx_toNat c 3 (by decide) (by decide) h4c
  have hpos1 : (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000001#64).toNat < 2 ^ 63 := by
    rw [hv1]; omega
  have hpos2 : (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000002#64).toNat < 2 ^ 63 := by
    rw [hv2]; omega
  have hpos3 : (BitVec.ofNat 64 (4 * c) ||| 0x0000000000000003#64).toNat < 2 ^ 63 := by
    rw [hv3]; omega
  obtain ⟨q', hden, hnc, hni, hiv3, hshr3, hadd3, hq'a, hq'mw, hq'u⟩ :=
    stkMulGrp_denote (calls := calls) (env := s.env) (q := q) (s := s)
      (a := a) (iv := BitVec.ofNat 64 (4 * c)) (niter := BitVec.ofNat 64 (4 * c))
      (unroll := BitVec.ofNat 64 (4 * G))
      (cv := BitVec.ofNat 128 (car limbs mw c)) (mw := mw)
      (x0 := BitVec.ofNat 64 w0) (x1 := BitVec.ofNat 64 w1)
      (x2 := BitVec.ofNat 64 w2) (x3 := BitVec.ofNat 64 w3)
      hphis ha' hconv' hunr' hiv hcv hn hpos0
      (by rw [ofNat64_val _ (by omega), hv1])
      hpos1
      (by rw [hv1, hv2])
      hpos2
      (by rw [hv2, hv3])
      hpos3 hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  exact ⟨q', w0, w1, w2, w3, rest, hdrop, hrest, hden, hnc, hiv3, hni, hshr3,
    hadd3, hq'a, hq'mw, hq'u⟩

/-- The memory a visit leaves is the fold's next prefix. -/
theorem mem_after_visit (mem0 : Mem) (a : Nat) (mw : BitVec 128) (limbs : List Nat)
    (w0 w1 w2 w3 : Nat) (rest : List Nat) (c : Nat)
    (hmw : mw.toNat < 2 ^ 64)
    (hfoldlt : car limbs mw c < 2 ^ 64)
    (hprefix : (pre limbs mw c).length = 4 * c)
    (hdrop : limbs.drop (4 * c) = w0 :: w1 :: w2 :: w3 :: rest)
    (h4c : 4 * c < 2 ^ 63)
    (hw0 : w0 < 2 ^ 64) (hw1 : w1 < 2 ^ 64) (hw2 : w2 < 2 ^ 64) (hw3 : w3 < 2 ^ 64) :
    stkMulGrpMem
        (stkWriteLimbs mem0 a (pre limbs mw c)) a
        (BitVec.ofNat 64 (4 * c))
        (BitVec.ofNat 128 (car limbs mw c)) mw
        (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2)
        (BitVec.ofNat 64 w3) =
      stkWriteLimbs mem0 a (pre limbs mw (c + 1)) := by
  have hv : (BitVec.ofNat 64 (4 * c)).toNat = 4 * c := ofNat64_val _ (by omega)
  have h1 : ((BitVec.ofNat 64 (4 * c)) ||| 0x0000000000000001#64).toNat = 4 * c + 1 :=
    or_idx_toNat c 1 (by decide) (by decide) (by omega)
  have h2 : ((BitVec.ofNat 64 (4 * c)) ||| 0x0000000000000002#64).toNat = 4 * c + 2 :=
    or_idx_toNat c 2 (by decide) (by decide) (by omega)
  have h3 : ((BitVec.ofNat 64 (4 * c)) ||| 0x0000000000000003#64).toNat = 4 * c + 3 :=
    or_idx_toNat c 3 (by decide) (by decide) (by omega)
  have hcvlt : (BitVec.ofNat 128 (car limbs mw c)).toNat < 2 ^ 64 := by
    rw [ofNat128_val _ (by omega)]
    exact hfoldlt
  have hA := grpMem_eq_writeLimbs
    (stkWriteLimbs mem0 a (pre limbs mw c)) a
    (BitVec.ofNat 64 (4 * c))
    (BitVec.ofNat 128 (car limbs mw c)) mw
    (BitVec.ofNat 64 w0) (BitVec.ofNat 64 w1) (BitVec.ofNat 64 w2) (BitVec.ofNat 64 w3)
    c
    (BitVec.ofNat 64
      ((BitVec.ofNat 128 (BitVec.ofNat 64 w0).toNat * mw +
        (BitVec.ofNat 128 (car limbs mw c))).toNat % 2 ^ 64)).toNat
    (BitVec.ofNat 64
      ((BitVec.ofNat 128 (BitVec.ofNat 64 w1).toNat * mw +
        stkMulCarry (BitVec.ofNat 64 w0) mw
          (BitVec.ofNat 128 (car limbs mw c))).toNat % 2 ^ 64)).toNat
    (BitVec.ofNat 64
      ((BitVec.ofNat 128 (BitVec.ofNat 64 w2).toNat * mw +
        stkMulCarry (BitVec.ofNat 64 w1) mw
          (stkMulCarry (BitVec.ofNat 64 w0) mw
            (BitVec.ofNat 128 (car limbs mw c)))).toNat % 2 ^ 64)).toNat
    (BitVec.ofNat 64
      ((BitVec.ofNat 128 (BitVec.ofNat 64 w3).toNat * mw +
        stkMulCarry (BitVec.ofNat 64 w2) mw
          (stkMulCarry (BitVec.ofNat 64 w1) mw
            (stkMulCarry (BitVec.ofNat 64 w0) mw
              (BitVec.ofNat 128 (car limbs mw c))))).toNat % 2 ^ 64)).toNat
    hv h1 h2 h3 rfl rfl rfl rfl hmw hcvlt
  rw [hA]
  rw [pre_succ_eq limbs mw c w0 w1 w2 w3 rest hmw hfoldlt hdrop hw0 hw1 hw2 hw3,
    stkWriteLimbs_append, hprefix]

/-! ### The two arms -/

/-- The exit arm: at the bound the block's test is one, and the visit leaves for
the join with the whole prefix, the last carry, the index and the last sum. -/
theorem loop_exit (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (hG : 4 * G ≤ 96) (hmw : mw.toNat < 2 ^ 64) (hlimbs : limbs.length = 4 * G)
    (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64) :
    ∀ (r : Nat) (s : State) (c : Nat), Inv mem0 a mw G limbs r s c →
      AtBound G s c = true →
      ∃ (e : State) (j : Nat), j ≤ 1 ∧
        e.pc = "while.cond.preheader.i.unr-lcssa.loopexit" ∧
        ExitWord mem0 a mw G limbs e ∧
        ∀ k, runFuel stkMulCalls (j + k) stkMulBody s =
          runFuel stkMulCalls k stkMulBody e := by
  intro r s c hinv hb
  obtain ⟨q', w0', w1', w2', w3', rest', hdrop', hrest', hden, hnc, hiv3, hni, hshr3,
    hadd3, hqa, hqmw, hqu⟩ := visit_denote hG hmw hlimbs hlimbslt hinv
  obtain ⟨hpc, hsel, ha, hconv, hunr, hmem, ⟨w0, w1, w2, w3, rest, hdrop, hrest⟩,
    hreads, hfoldlt, hbudget⟩ := hinv
  have hdrop0 : limbs.drop (4 * c) = w0' :: w1' :: w2' :: w3' :: rest' := hdrop'
  obtain ⟨hw0, hw1, hw2, hw3⟩ := group_limbs_lt limbs hlimbslt c w0' w1' w2' w3' rest' hdrop0
  have heq : c + 1 = G := of_decide_eq_true hb
  have h4c63 : 4 * c < 2 ^ 63 := by omega
  have h4c' : 4 * (c + 1) < 2 ^ 64 := by omega
  have h4G : 4 * G < 2 ^ 64 := by omega
  have hprefix : (pre limbs mw c).length = 4 * c := pre_length limbs mw c (by omega)
  have htest := bound_test_true h4c63 h4c' h4G heq
  have hstep := stkMulGrp_step_taken (calls := stkMulCalls) (env := s.env) (q' := q')
    (niter := BitVec.ofNat 64 (4 * c)) (unroll := BitVec.ofNat 64 (4 * G))
    hpc hden hnc htest
  have hmem' := mem_after_visit mem0 a mw limbs w0' w1' w2' w3' rest' c hmw hfoldlt hprefix
    hdrop0 h4c63 hw0 hw1 hw2 hw3
  rw [← hmem] at hmem'
  have htakeG : limbs.take (4 * (c + 1)) = limbs :=
    take_eq_self limbs (4 * (c + 1)) (by rw [hlimbs, heq])
  have hpreG : pre limbs mw (c + 1) = (stkMulFold limbs mw.toNat 0).1 := by
    unfold pre; rw [htakeG]
  have hcarG : car limbs mw (c + 1) = (stkMulFold limbs mw.toNat 0).2 := by
    unfold car; rw [htakeG]
  have hcvlt : (BitVec.ofNat 128 (car limbs mw c)).toNat < 2 ^ 64 := by
    rw [ofNat128_val _ (by omega)]
    exact hfoldlt
  have hc1 : (stkMulCarry (BitVec.ofNat 64 w0') mw
      (BitVec.ofNat 128 (car limbs mw c))).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw hcvlt
  have hc2 : (stkMulCarry (BitVec.ofNat 64 w1') mw
      (stkMulCarry (BitVec.ofNat 64 w0') mw
        (BitVec.ofNat 128 (car limbs mw c)))).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw hc1
  have hc3 : (stkMulCarry (BitVec.ofNat 64 w2') mw
      (stkMulCarry (BitVec.ofNat 64 w1') mw
        (stkMulCarry (BitVec.ofNat 64 w0') mw
          (BitVec.ofNat 128 (car limbs mw c))))).toNat < 2 ^ 64 :=
    stkMulCarry_lt _ mw _ hmw hc2
  refine ⟨State.mk q' (stepMem s.mem a mw limbs c w0' w1' w2' w3') s.next
    "while.cond.preheader.i.unr-lcssa.loopexit" (some "for.body.i"),
    1, le_rfl, rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [stepMem_eq, hmem', hpreG]
    · rw [hshr3]
      refine congrArg some (congrArg (Value.int 128) ?_)
      rw [← hcarG, car_succ_eq limbs mw c w0' w1' w2' w3' rest' hmw hfoldlt hdrop0
          hw0 hw1 hw2 hw3]
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hiv3, count_step c h4c63, heq]
    · simpa only [hqa] using ha
    · simpa only [hqmw] using hconv
    · rw [hqu]
    · refine ⟨_, hadd3, ?_⟩
      show (BitVec.ofNat 128 (BitVec.ofNat 64 w3').toNat * mw +
          stkMulCarry (BitVec.ofNat 64 w2') mw
            (stkMulCarry (BitVec.ofNat 64 w1') mw
              (stkMulCarry (BitVec.ofNat 64 w0') mw
                (BitVec.ofNat 128 (car limbs mw c))))).toNat =
        (stkMulFold limbs mw.toNat 0).1.getD (limbs.length - 1) 0 +
          2 ^ 64 * (stkMulFold limbs mw.toNat 0).2
      rw [← hpreG, ← hcarG,
        pre_succ_eq limbs mw c w0' w1' w2' w3' rest' hmw hfoldlt hdrop0
          hw0 hw1 hw2 hw3,
        car_succ_eq limbs mw c w0' w1' w2' w3' rest' hmw hfoldlt hdrop0
          hw0 hw1 hw2 hw3]
      have hidx : limbs.length - 1 = (pre limbs mw c).length + 3 := by
        rw [hlimbs, ← heq, hprefix]
        omega
      rw [hidx, getD_append_four]
      rw [stkMulWide_toNat (BitVec.ofNat 64 w3') mw
        (stkMulCarry (BitVec.ofNat 64 w2') mw
          (stkMulCarry (BitVec.ofNat 64 w1') mw
            (stkMulCarry (BitVec.ofNat 64 w0') mw
              (BitVec.ofNat 128 (car limbs mw c)))))
        hmw (stkMulCarry_lt _ mw _ hmw (stkMulCarry_lt _ mw _ hmw
          (stkMulCarry_lt _ mw _ hmw hcvlt)))]
      rw [stkMulCarry_toNat (BitVec.ofNat 64 w3') mw
        (stkMulCarry (BitVec.ofNat 64 w2') mw
          (stkMulCarry (BitVec.ofNat 64 w1') mw
            (stkMulCarry (BitVec.ofNat 64 w0') mw
              (BitVec.ofNat 128 (car limbs mw c)))))
        hmw hc3]
      simp only [BitVec.toNat_ofNat, Nat.mod_mod]
      exact (Nat.mod_add_div _ (2 ^ 64)).symm
  · intro k
    have hst : stateAt s.env s = s := rfl
    simpa only [hst, hpc] using runFuel_jump_prefix hstep k

/-- The back edge: below the bound the block's test is zero, and the visit
re-enters the head with one more group and one less budget. -/
theorem loop_step (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (hG : 4 * G ≤ 96) (hmw : mw.toNat < 2 ^ 64) (hlimbs : limbs.length = 4 * G)
    (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64) :
    ∀ (r : Nat) (s : State) (c : Nat), Inv mem0 a mw G limbs (r + 1) s c →
      AtBound G s c = false →
      ∃ (e : State) (c' : Nat) (j : Nat), j ≤ 1 ∧ e.pc = "for.body.i" ∧ c < c' ∧
        Inv mem0 a mw G limbs r e c' ∧
        ∀ k, runFuel stkMulCalls (j + k) stkMulBody s =
          runFuel stkMulCalls k stkMulBody e := by
  intro r s c hinv hb
  obtain ⟨q', w0, w1, w2, w3, rest, hdrop, hrest, hden, hnc, hiv3, hni, hshr3, hadd3,
    hqa, hqmw, hqu⟩ := visit_denote hG hmw hlimbs hlimbslt hinv
  obtain ⟨hpc, hsel, ha, hconv, hunr, hmem, ⟨_, _, _, _, _, _, _⟩, hreads, hfoldlt,
    hbudget⟩ := hinv
  obtain ⟨hw0, hw1, hw2, hw3⟩ := group_limbs_lt limbs hlimbslt c w0 w1 w2 w3 rest hdrop
  have hne : c + 1 ≠ G := by
    intro h
    have hb' : AtBound G s c = true := by simp only [AtBound, h, decide_true]
    rw [hb] at hb'
    exact absurd hb' (by decide)
  have h4c63 : 4 * c < 2 ^ 63 := by omega
  have h4c : 4 * c < 2 ^ 64 := by omega
  have h4G : 4 * G < 2 ^ 64 := by omega
  have h4c' : 4 * (c + 1) < 2 ^ 64 := by omega
  have hprefix : (pre limbs mw c).length = 4 * c := pre_length limbs mw c (by omega)
  have htest := bound_test_false h4c63 h4c' h4G hne
  have hstep := stkMulGrp_step_loop (calls := stkMulCalls) (env := s.env) (q' := q')
    (niter := BitVec.ofNat 64 (4 * c)) (unroll := BitVec.ofNat 64 (4 * G))
    hpc hden hnc htest
  have hmem' := mem_after_visit mem0 a mw limbs w0 w1 w2 w3 rest c hmw hfoldlt hprefix hdrop
    h4c63 hw0 hw1 hw2 hw3
  rw [← hmem] at hmem'
  have hcvlt : (BitVec.ofNat 128 (car limbs mw c)).toNat < 2 ^ 64 := by
    rw [ofNat128_val _ (by omega)]
    exact hfoldlt
  have hcarrylt := carry_four_lt w0 w1 w2 w3 mw
    (BitVec.ofNat 128 (car limbs mw c)) hmw hcvlt
  have hrest4 : 4 ≤ rest.length := by rw [hrest]; omega
  have hdrop1 : limbs.drop (4 * (c + 1)) =
      rest.getD 0 0 :: rest.getD 1 0 :: rest.getD 2 0 :: rest.getD 3 0 :: rest.drop 4 := by
    have h : 4 * (c + 1) = 4 * c + 4 := by omega
    rw [h, ← List.drop_drop, hdrop]
    exact four_cons_drop rest hrest4
  have hrest1 : (rest.drop 4).length = 4 * r := by
    rw [List.length_drop, hrest]
    omega
  refine ⟨State.mk q' (stepMem s.mem a mw limbs c w0 w1 w2 w3) s.next "for.body.i"
    (some "for.body.i"), c + 1, 1, le_rfl, rfl, by omega, ?_, ?_⟩
  · refine ⟨rfl, Or.inl ⟨rfl, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_,
      ⟨rest.getD 0 0, rest.getD 1 0, rest.getD 2 0, rest.getD 3 0, rest.drop 4,
        hdrop1, hrest1⟩, ?_, ?_, by omega⟩
    · rw [hiv3, count_step c h4c63]
    · rw [hshr3]
      refine congrArg some (congrArg (Value.int 128) ?_)
      rw [car_succ_eq limbs mw c w0 w1 w2 w3 rest hmw hfoldlt hdrop hw0 hw1 hw2 hw3]
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [hni, count_step c h4c63]
    · simpa only [hqa] using ha
    · simpa only [hqmw] using hconv
    · rw [hqu]
    · rw [stepMem_eq, hmem']
    · intro j
      rw [show 4 * (c + 1) + j = 4 * c + (4 + j) by omega]
      rw [hreads (4 + j), getD_drop_offset, getD_drop_offset]
      rw [show 4 * c + (4 + j) = 4 * (c + 1) + j by omega]
    · rw [car_succ_eq limbs mw c w0 w1 w2 w3 rest hmw hfoldlt hdrop hw0 hw1 hw2 hw3]
      exact hcarrylt
  · intro k
    have hst : stateAt s.env s = s := rfl
    simpa only [hst, hpc] using runFuel_jump_prefix hstep k

/-! ### The loop, and the run

The instance names the head, the join it leaves for, the bound `G - 1` and the
per-visit cost `1`; its two arms are the lemmas above.  `BoundLoop.run_at` then
turns an invariant state into a completed outcome at fuel `G + k` — a term of the
body's arguments, because `G` is the limb count's quarters.

The caller enters at `c = 0`; `inv_entry` says what it must supply besides the
memory: the count's widened value, the address, and the read premise over the
whole limb list. -/

/-- **The multiply's group loop.** -/
def loop (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (hG : 4 * G ≤ 96) (hmw : mw.toNat < 2 ^ 64) (hlimbs : limbs.length = 4 * G)
    (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64) :
    BoundLoop stkMulCalls stkMulBody where
  head := "for.body.i"
  exitBlock := "while.cond.preheader.i.unr-lcssa.loopexit"
  N := G - 1
  cost := 1
  Inv := Inv mem0 a mw G limbs
  atBound := AtBound G
  ExitWord := ExitWord mem0 a mw G limbs
  step_exit := loop_exit mem0 a mw G limbs hG hmw hlimbs hlimbslt
  step_loop := loop_step mem0 a mw G limbs hG hmw hlimbs hlimbslt
  exit_at_zero := by
    intro s c h
    obtain ⟨_, _, _, _, _, _, _, _, _, hb⟩ := h
    exact decide_eq_true (by omega)
  budget := by
    intro r s c h
    obtain ⟨_, _, _, _, _, _, _, _, _, hb⟩ := h
    exact ⟨by omega, by omega⟩

/-- **The loop's run.**  From an invariant state at the whole bound, the run
reaches the join within `G` control steps, and a completed continuation from the
join lifts to the head. -/
theorem loop_run_at (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (hG : 4 * G ≤ 96) (hmw : mw.toNat < 2 ^ 64) (hlimbs : limbs.length = 4 * G)
    (hlimbslt : ∀ j, limbs.getD j 0 < 2 ^ 64)
    (s : State) (c : Nat) (h : Inv mem0 a mw G limbs (G - 1) s c) (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), e.pc = "while.cond.preheader.i.unr-lcssa.loopexit" →
      ExitWord mem0 a mw G limbs e → runFuel stkMulCalls k stkMulBody e = some o) :
    runFuel stkMulCalls ((G - 1 + 1) * 1 + k) stkMulBody s = some o :=
  (loop mem0 a mw G limbs hG hmw hlimbs hlimbslt).run_at s c h k hcont

/-- **The invariant at the entry.**  A state at the head, arriving from the
preheader's `for.body.lr.ph.i.new`, with no limb written and the whole limb list
readable, is the loop's seed at `c = 0`. -/
theorem inv_entry (mem0 : Mem) (a : Nat) (mw : BitVec 128) (G : Nat) (limbs : List Nat)
    (hG1 : 1 ≤ G) (hlimbs : limbs.length = 4 * G)
    (s : State) (hpc : s.pc = "for.body.i")
    (hpre : s.pre = some "for.body.lr.ph.i.new")
    (ha : lookupName s.env "%a" = some (.ptr a))
    (hconv : lookupName s.env "%conv3.i" = some (.int 128 mw))
    (hunr : lookupName s.env "%unroll_iter" =
      some (.int 64 (BitVec.ofNat 64 (4 * G))))
    (hmem : s.mem = mem0)
    (hreads : ∀ j, readBytes mem0 (a + 8 * j) 8 =
      some (natToBytes (limbs.getD j 0) 8)) :
    Inv mem0 a mw G limbs (G - 1) s 0 := by
  have hlen : 4 ≤ limbs.length := by rw [hlimbs]; omega
  have hdec := four_cons_drop limbs hlen
  refine ⟨hpc, ?_, ha, hconv, hunr, ?_, ?_, ?_, ?_, ?_⟩
  · refine Or.inr ⟨hpre, rfl, rfl, rfl⟩
  · show s.mem = stkWriteLimbs mem0 a (pre limbs mw 0)
    rw [hmem]
    rfl
  · exact ⟨limbs.getD 0 0, limbs.getD 1 0, limbs.getD 2 0, limbs.getD 3 0,
      limbs.drop 4, hdec, by rw [List.length_drop, hlimbs]; omega⟩
  · intro j
    simpa only [Nat.mul_zero, Nat.zero_add, List.drop_zero] using hreads j
  · have h0 : (stkMulFold (limbs.take (4 * 0)) mw.toNat 0).2 = 0 := by
      simp [stkMulFold]
    show car limbs mw 0 < 2 ^ 64
    unfold car
    rw [h0]
    decide
  · omega

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.StkMulLoop.loop_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_exit

/-- info: 'LeanLLVM.Refinement.StkMulLoop.loop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_step

/-- info: 'LeanLLVM.Refinement.StkMulLoop.loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop

/-- info: 'LeanLLVM.Refinement.StkMulLoop.loop_run_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loop_run_at

/-- info: 'LeanLLVM.Refinement.StkMulLoop.inv_entry' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms inv_entry

end StkMulLoop

end LeanLLVM.Refinement
