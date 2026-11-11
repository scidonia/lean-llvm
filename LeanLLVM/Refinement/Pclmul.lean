/-
Carry-less multiplication as the truncated polynomial product, the all-ones
instance as prefix parity, and the identity that puts the JSON classifier's
in-string mask in the kernel's arithmetic.

## What this module proves

`clmul a b` is the polynomial product of `a` and `b` over GF(2), truncated to `w`
bits, written as the fold of shifted XORs that `pclmulqdq` performs — for `w = 64`
the low half, which is the imm `0`, element `0` instance the kernel emits.  With no
axiom beyond Lean's own `propext` and `Quot.sound`, the module proves:

* `clmul_allOnes_eq_fold` — the all-ones multiplier selects every shift, so the
  fold's per-lane test disappears.
* `clmul_allOnes_self` — **the product is the prefix parity**: the all-ones
  product `p` of `a` solves `p ⊕ (p << 1) = a`, because the interior terms of the
  shift-XOR telescope away.
* `clmul_allOnes_unique` — that solution is unique: any `p` with
  `p ⊕ (p << 1) = q` *is* the all-ones product of `q`.  Prefix parity is pinned
  by its difference and its lane zero, not merely exhibited.
* `inStringMask_eq_clmul` and `specInString64_eq_clmul` — **the mask identity**:
  over a **full** thirty-two-lane window, and over the joined sixty-four-lane
  block the kernel stores, the specification's in-string mask is the all-ones
  carry-less product of the unescaped-quote mask, XOR the carry word.  A short
  final window is not covered and does not hold: the fold leaves lanes past the
  data clear while the product would set them, which is the same shape as the
  trailing-lane question the owed list records.
* `specInString64_outgoing_carry` — **the outgoing carry**: the carry the next
  block inherits is bit 63 of the joined mask.

Nothing here is a new axiom: `clmul` is a fold of shifts and XORs, and every fact
below is proved from the BitVec XOR group and `List` induction.

## What this module does not prove

The identity above takes `specQuote64` — the kernel's unescaped-quote mask — as the
specification defines it; how the kernel *computes* it is
`LeanLLVM/Refinement/QuoteDerive.lean`'s subject, not this module's.  There
`kernelQuote64` proves the kernel's `%qmc2 = %qrawc2 & ~%escc2` over a
sixty-four-lane block — the raw quote mask filtered by a `pext`/`pdep` escape
mask — is the `specQuote64` this module's identity is stated over, and `BitLanes`
models the three intrinsics that expression is built from.

This module states the arithmetic the kernel's masks satisfy, over the
specification's own definitions; a relation to the *compiled* kernel is not stated
here.  For the extracted stage-1 mask unit it is stated above this module:
`s1Calls` (`LeanLLVM/Refinement/JsonS1MasksIR.lean`) binds `@llvm.x86.pclmulqdq` to
`clmul`, and `s1_masks_refines` (`LeanLLVM/Refinement/JsonS1MasksSteps.lean`) reads the
resulting word back at the emitted body's own register.  For any other body the
relation stays open, and `QuoteDerive` records the same split for its derivation,
beside the transcription gap it carries on its own.
-/
import LeanLLVM.Refinement.JsonScanSpec

namespace LeanLLVM.Refinement.Pclmul

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanSpec

/-! ### The all-ones lane

`BitVec.getLsbD_allOnes` — the core library's statement that an all-ones word's
lane `i < w` is set — carries `Classical.choice` in its proof term.  The lane
fact is elementary, so it is proved here instead: the arithmetic lemmas it needs
(`Nat.testBit_succ`, `Nat.testBit_zero`, `Nat.mul_add_div`,
`Nat.add_mul_mod_self_left`) are all choice-free, and every theorem below then
stays at the module's own footprint. -/

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

/-- Lane `i` of an all-ones word is set while `i < w`, at the module's own
footprint: `BitVec.getLsbD_allOnes` states the same fact and carries
`Classical.choice`, so the proof goes through `BitVec.getLsbD_ofNatLT` and the
numeral above instead. -/
private theorem allOnes_getLsbD_of_lt {w i : Nat} (h : i < w) :
    (BitVec.allOnes w).getLsbD i = true := by
  have key : (BitVec.allOnes w).getLsbD i = (2 ^ w - 1).testBit i :=
    BitVec.getLsbD_ofNatLT (n := w) (2 ^ w - 1)
      (by have := Nat.two_pow_pos w; omega) i
  rw [key, testBit_two_pow_sub_one_of_lt h]

/-! ### XOR and Bool normal forms

`BitVec` has `xor_assoc` and `xor_comm` but not `xor_left_comm`; these are the
facts the folds need.  Note that `^^^` binds looser than `=`, so the right-hand
sides below are parenthesised. -/

theorem xor_left_comm {w : Nat} (a b c : BitVec w) : a ^^^ (b ^^^ c) = b ^^^ (a ^^^ c) := by
  rw [← BitVec.xor_assoc, BitVec.xor_comm a b, BitVec.xor_assoc]

theorem xor_self_right {w : Nat} (a b : BitVec w) : (a ^^^ b) ^^^ b = a := by
  rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- In the Bool XOR group, solving for the left summand: cancelling an addend is
XOR-ing it back. -/
theorem xor_eq_iff {x y z : Bool} : ((x ^^ y) = z) ↔ (x = (z ^^ y)) := by
  cases x <;> cases y <;> cases z <;> simp

/-! ### Carry-less multiplication

`clmul a b` is the polynomial product of `a` and `b` over `GF(2)`, truncated to
`w` bits: lane `k` of the result is the parity of the pairs `(i, j)` with
`i + j = k` and both lanes set.  Written as a fold, `b`'s set lanes select
shifted copies of `a` and XOR them together — the arithmetic `pclmulqdq` performs.
-/

def clmul {w : Nat} (a b : BitVec w) : BitVec w :=
  (List.range w).foldl
    (fun acc j => if b.getLsbD j then acc ^^^ (a <<< j) else acc) (0#w)

/-- The all-ones multiplier selects every shift, so the fold drops its test. -/
private theorem foldl_allOnes_true {w : Nat} (a : BitVec w) (l : List Nat) (c : BitVec w)
    (h : ∀ j ∈ l, j < w) :
    l.foldl (fun acc j => if (BitVec.allOnes w).getLsbD j then acc ^^^ (a <<< j) else acc) c
      = l.foldl (fun acc j => acc ^^^ (a <<< j)) c := by
  induction l generalizing c with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [show (BitVec.allOnes w).getLsbD j = true from
      allOnes_getLsbD_of_lt (h j (List.mem_cons_self ..))]
    simp only [ite_true]
    exact ih _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- `pclmul(a, all-ones)` is the XOR of every left shift of `a`: the geometric
series `1 + x + … + x^(w-1)` selects all of them. -/
theorem clmul_allOnes_eq_fold {w : Nat} (a : BitVec w) :
    clmul a (BitVec.allOnes w) =
      (List.range w).foldl (fun acc j => acc ^^^ (a <<< j)) 0#w :=
  foldl_allOnes_true a (List.range w) 0#w (fun _ hj => List.mem_range.mp hj)

/-! ### The fold's two algebraic lemmas -/

/-- Shifting a fold is folding the shifted summands. -/
private theorem fold_shift_gen {w : Nat} (l : List Nat) (a c : BitVec w) (n : Nat) :
    (l.foldl (fun acc j => acc ^^^ (a <<< j)) c) <<< n
      = l.foldl (fun acc j => acc ^^^ (a <<< (j + n))) (c <<< n) := by
  induction l generalizing c with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [ih, BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]

/-- Two folds with the same summands merge into one fold whose summands are the
XOR of the two. -/
private theorem fold_xor_merge {w : Nat} (l : List Nat) (f g : Nat → BitVec w)
    (c d : BitVec w) :
    l.foldl (fun acc j => acc ^^^ f j) c ^^^ l.foldl (fun acc j => acc ^^^ g j) d
      = l.foldl (fun acc j => acc ^^^ f j ^^^ g j) (c ^^^ d) := by
  induction l generalizing c d with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [ih (c ^^^ f j) (d ^^^ g j)]
    congr 1
    simp [BitVec.xor_comm, xor_left_comm]

/-- **The telescoping identity.**  Consecutive shifts XOR to zero in the interior,
leaving only the ends. -/
private theorem telescope {w : Nat} (a : BitVec w) (m : Nat) :
    (List.range m).foldl (fun acc j => acc ^^^ (a <<< j) ^^^ (a <<< (j + 1))) 0#w
      = (a <<< 0) ^^^ (a <<< m) := by
  induction m with
  | zero => rw [List.range_zero, List.foldl_nil, BitVec.xor_self]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih]
    show ((a <<< 0) ^^^ (a <<< m)) ^^^ (a <<< m) ^^^ (a <<< (m + 1)) =
      (a <<< 0) ^^^ (a <<< (m + 1))
    rw [xor_self_right]

/-- **The prefix-parity identity.**  The all-ones carry-less product `p` of `a`
solves `p ⊕ (p << 1) = a`: XOR-ing it with its own shift cancels every interior
term, so the difference operator `1 + x` inverts to the prefix sum.  No axiom is
involved — the polynomial product is a fold of shifts and the cancellation is the
XOR group. -/
theorem clmul_allOnes_self {w : Nat} (a : BitVec w) :
    clmul a (BitVec.allOnes w) ^^^ (clmul a (BitVec.allOnes w) <<< 1) = a := by
  rw [clmul_allOnes_eq_fold]
  rw [fold_shift_gen (l := List.range w) (a := a) (c := 0#w) (n := 1)]
  rw [BitVec.zero_shiftLeft]
  rw [fold_xor_merge]
  rw [BitVec.xor_self]
  rw [telescope]
  rw [BitVec.shiftLeft_zero, BitVec.shiftLeft_eq_zero (Nat.le_refl w), BitVec.xor_zero]

/-! ### The seed word

The kernel's carry is the all-ones or zero word derived from the previous block's
top in-string bit. -/

/-- The carry word: all ones inside a string, zero outside. -/
def seedVec (w : Nat) (seed : Bool) : BitVec w :=
  match seed with
  | true => BitVec.allOnes w
  | false => 0#w

theorem seedVec_getLsbD {w : Nat} {seed : Bool} {k : Nat} (hk : k < w) :
    (seedVec w seed).getLsbD k = seed := by
  cases seed
  · rw [seedVec, BitVec.getLsbD_zero]
  · rw [seedVec, allOnes_getLsbD_of_lt hk]

/-! ### From the algebraic identity to the lane recurrence -/

/-- Lane zero of the all-ones product is lane zero of `a`: the shift into it is
empty. -/
theorem clmul_allOnes_getLsbD_zero {w : Nat} (a : BitVec w) :
    (clmul a (BitVec.allOnes w)).getLsbD 0 = a.getLsbD 0 := by
  have h := congrArg (fun x : BitVec w => x.getLsbD 0) (clmul_allOnes_self a)
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft] at h
  rw [show decide (0 < 1) = true from decide_eq_true Nat.zero_lt_one, Bool.not_true,
    Bool.and_false, Bool.false_and, Bool.xor_false] at h
  exact h

/-- The lane step `p_k = a_k ⊕ p_{k-1}`: the prefix-XOR recurrence, read off the
telescoping identity at one lane. -/
theorem clmul_allOnes_getLsbD_succ {w : Nat} {a : BitVec w} {k : Nat} (hk : k + 1 < w) :
    (clmul a (BitVec.allOnes w)).getLsbD (k + 1)
      = (a.getLsbD (k + 1) ^^ (clmul a (BitVec.allOnes w)).getLsbD k) := by
  have h := congrArg (fun x : BitVec w => x.getLsbD (k + 1)) (clmul_allOnes_self a)
  have h1 : decide (k + 1 < 1) = false :=
    decide_eq_false (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le k)))
  rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, h1, Bool.not_false,
    Bool.and_true, show decide (k + 1 < w) = true from decide_eq_true hk, Bool.true_and,
    show k + 1 - 1 = k from Nat.succ_sub_one k] at h
  exact xor_eq_iff.mp h

/-- **Two lane sequences with the same difference and seed are the same.**  If `m`
and `c ⊕ seed` both start at `a₀ ⊕ seed` and both take the step `x ↦ aₖ ⊕ x`,
they agree at every lane: prefix parity is pinned by its difference and its seed. -/
theorem eq_clmul_of_recur {w : Nat} (a c m : BitVec w) (seed : Bool)
    (hc0 : c.getLsbD 0 = a.getLsbD 0)
    (hc : ∀ k, k + 1 < w → c.getLsbD (k + 1) = (a.getLsbD (k + 1) ^^ c.getLsbD k))
    (hm0 : m.getLsbD 0 = (a.getLsbD 0 ^^ seed))
    (hm : ∀ k, k + 1 < w → m.getLsbD (k + 1) = (a.getLsbD (k + 1) ^^ m.getLsbD k)) :
    m = c ^^^ seedVec w seed := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hbit : m.getLsbD k = (c.getLsbD k ^^ seed) := by
    induction k with
    | zero => rw [hm0, hc0]
    | succ k ih =>
      rw [hm k hk, ih (by omega), hc k hk, ← Bool.xor_assoc]
  rw [hbit, BitVec.getLsbD_xor, seedVec_getLsbD hk]

/-! ### The prefix-parity characterisation

`p ⊕ (p << 1) = q` is the lane recurrence `p_k = q_k ⊕ p_{k-1}`, so the all-ones
product is the *unique* word with that difference and lane zero `q_0` — the prefix
XOR of `q`.  This is the property the kernel relies on; it is a theorem here, not
an assumption. -/

theorem clmul_allOnes_unique {w : Nat} {p q : BitVec w} (h : p ^^^ (p <<< 1) = q) :
    p = clmul q (BitVec.allOnes w) := by
  have hmain := eq_clmul_of_recur (a := q) (c := clmul q (BitVec.allOnes w)) (m := p)
    (seed := false) (clmul_allOnes_getLsbD_zero q)
    (fun k hk => clmul_allOnes_getLsbD_succ hk) ?_ ?_
  · simpa [seedVec] using hmain
  · have h0 := congrArg (fun x : BitVec w => x.getLsbD 0) h
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft] at h0
    rw [show decide (0 < 1) = true from decide_eq_true Nat.zero_lt_one, Bool.not_true,
      Bool.and_false, Bool.false_and, Bool.xor_false] at h0
    rw [h0, Bool.xor_false]
  · intro k hk
    have hk' := congrArg (fun x : BitVec w => x.getLsbD (k + 1)) h
    have h1 : decide (k + 1 < 1) = false :=
      decide_eq_false (Nat.not_lt_of_le (Nat.succ_le_succ (Nat.zero_le k)))
    rw [BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft, h1, Bool.not_false,
      Bool.and_true, show decide (k + 1 < w) = true from decide_eq_true hk,
      Bool.true_and, show k + 1 - 1 = k from Nat.succ_sub_one k] at hk'
    exact xor_eq_iff.mp hk'

/-! ### The 32-lane window

`JsonScanSpec.inStringMask` is defined by the fold, and `inStringMask_getLsbD`
reads one lane: bit `k` is the state after byte `k`.  The two lemmas below turn
that into the prefix-parity recurrence `x_k = q_k ⊕ x_{k-1}`. -/

theorem inStringAfter_apply (s : ClassState) (b : UInt8) :
    inStringAfter s b = (s.inside ^^ isUnescapedQuote s b) := rfl

theorem inStringAfter_classStep (s : ClassState) (b b' : UInt8) :
    inStringAfter (classStep s b) b'
      = (inStringAfter s b ^^ isUnescapedQuote (classStep s b) b') := rfl

/-- The fold at index zero is the incoming state. -/
theorem classCarryAt_zero (bs : List UInt8) (st : ClassState) :
    classCarryAt bs st 0 = st := by
  show (bs.take 0).foldl classStep st = st
  rw [List.take_zero, List.foldl_nil]

/-- Lane zero of the in-string mask: the seed, flipped by the first byte. -/
theorem inStringMask_zero {bs : List UInt8} {st : ClassState} {b : UInt8}
    (hb : bs[0]? = some b) :
    (inStringMask bs st).getLsbD 0 = ((quoteMask bs st).getLsbD 0 ^^ st.inside) := by
  rw [inStringMask_getLsbD (by decide : 0 < 32) hb,
    quoteMask_getLsbD (by decide : 0 < 32) hb,
    classCarryAt_zero, inStringAfter_apply, Bool.xor_comm]

/-- The lane step of the in-string mask: `x_{k+1} = q_{k+1} ⊕ x_k`. -/
theorem inStringMask_recur {bs : List UInt8} {st : ClassState} {i : Nat} {b b' : UInt8}
    (hi : i + 1 < 32) (hbi : bs[i]? = some b) (hbi1 : bs[i + 1]? = some b') :
    (inStringMask bs st).getLsbD (i + 1)
      = ((quoteMask bs st).getLsbD (i + 1) ^^ (inStringMask bs st).getLsbD i) := by
  rw [inStringMask_getLsbD hi hbi1, quoteMask_getLsbD hi hbi1,
    inStringMask_getLsbD (Nat.lt_of_succ_lt hi) hbi, classCarryAt_succ bs st i, hbi,
    inStringAfter_classStep, Bool.xor_comm]

/-- **The in-string mask is the all-ones carry-less product of the unescaped-quote
mask, XOR the carry**, over a **full** thirty-two-lane window.  This is the
specification module's `inStringMask` stated in the kernel's arithmetic:
`m = pclmul(q, all-ones) ⊕ carry`.  The `hlen` hypothesis is not cosmetic: on a
short window the fold leaves the lanes past the data clear while the product would
set them, so the two disagree. -/
theorem inStringMask_eq_clmul (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    inStringMask bs st =
      clmul (quoteMask bs st) (BitVec.allOnes 32) ^^^ seedVec 32 st.inside := by
  refine eq_clmul_of_recur (a := quoteMask bs st)
    (c := clmul (quoteMask bs st) (BitVec.allOnes 32)) (m := inStringMask bs st)
    (seed := st.inside) ?_ ?_ ?_ ?_
  · exact clmul_allOnes_getLsbD_zero _
  · intro k hk
    exact clmul_allOnes_getLsbD_succ hk
  · exact inStringMask_zero (List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (by decide : 0 < 32) hlen))
  · intro k hk
    exact inStringMask_recur hk
      (List.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hk) hlen))
      (List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hk hlen))

/-! ### The sixty-four-lane block

The kernel reads a block as two halves and joins their masks; the high half is
entered with the carry the low half leaves.  The per-lane lemmas read the joined
mask back apart. -/

theorem ofFn_getElem? {lo : Block32} {k : Nat} (hk : k < 32) :
    (List.ofFn lo)[k]? = some (lo ⟨k, hk⟩) := by
  rw [List.getElem?_ofFn, dite_eq_left hk]

/-- Bit `k` of the joined in-string mask, below the halfway point. -/
theorem specInString64_bit_lo {lo hi : Block32} {st : ClassState} {k : Nat} (hk : k < 32) :
    (specInString64 lo hi st).getLsbD k = (inStringMask (List.ofFn lo) st).getLsbD k := by
  unfold specInString64
  exact classMask64_getLsbD_lo inStringMask lo hi st hk

/-- Bit `m + 32` of the joined in-string mask, above the halfway point. -/
theorem specInString64_bit_hi {lo hi : Block32} {st : ClassState} {m : Nat} (hm : m < 32) :
    (specInString64 lo hi st).getLsbD (m + 32) =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD m := by
  unfold specInString64
  exact classMask64_getLsbD_hi inStringMask lo hi st hm

/-- Bit `j` of the joined in-string mask, above the halfway point, indexed by the
block lane. -/
theorem specInString64_bit_hi' {lo hi : Block32} {st : ClassState} {j : Nat}
    (h32 : 32 ≤ j) (hj : j < 64) :
    (specInString64 lo hi st).getLsbD j =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD (j - 32) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 32 := ⟨j - 32, by omega⟩
  rw [show (m + 32) - 32 = m from Nat.add_sub_cancel m 32]
  exact specInString64_bit_hi (m := m) (by omega)

/-- Bit `k` of the joined unescaped-quote mask, below the halfway point. -/
theorem specQuote64_bit_lo {lo hi : Block32} {st : ClassState} {k : Nat} (hk : k < 32) :
    (specQuote64 lo hi st).getLsbD k = (quoteMask (List.ofFn lo) st).getLsbD k := by
  unfold specQuote64
  exact classMask64_getLsbD_lo quoteMask lo hi st hk

/-- Bit `m + 32` of the joined unescaped-quote mask, above the halfway point. -/
theorem specQuote64_bit_hi {lo hi : Block32} {st : ClassState} {m : Nat} (hm : m < 32) :
    (specQuote64 lo hi st).getLsbD (m + 32) =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD m := by
  unfold specQuote64
  exact classMask64_getLsbD_hi quoteMask lo hi st hm

/-- Bit `j` of the joined unescaped-quote mask, above the halfway point, indexed by
the block lane. -/
theorem specQuote64_bit_hi' {lo hi : Block32} {st : ClassState} {j : Nat}
    (h32 : 32 ≤ j) (hj : j < 64) :
    (specQuote64 lo hi st).getLsbD j =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD (j - 32) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 32 := ⟨j - 32, by omega⟩
  rw [show (m + 32) - 32 = m from Nat.add_sub_cancel m 32]
  exact specQuote64_bit_hi (m := m) (by omega)

/-- Bit `32`, the first lane of the high half. -/
theorem specInString64_bit_32 {lo hi : Block32} {st : ClassState} :
    (specInString64 lo hi st).getLsbD 32 =
      (inStringMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD 0 :=
  specInString64_bit_hi (m := 0) (by decide : 0 < 32)

/-- Bit `32` of the joined unescaped-quote mask. -/
theorem specQuote64_bit_32 {lo hi : Block32} {st : ClassState} :
    (specQuote64 lo hi st).getLsbD 32 =
      (quoteMask (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).getLsbD 0 :=
  specQuote64_bit_hi (m := 0) (by decide : 0 < 32)

/-- The state the high half is entered with is the in-string bit of the low half's
last lane: the carry crosses the boundary as the mask's top bit.  The window is
full here — as for `inStringMask_eq_clmul`, a short window leaves the trailing
lanes clear and the top bit is then not the state the next block inherits. -/
theorem classWindow_carry_inside (bs : List UInt8) (st : ClassState) (hlen : 32 ≤ bs.length) :
    (classWindow bs st).carry.inside = (inStringMask bs st).getLsbD 31 := by
  have h31 : 31 < bs.length := Nat.lt_of_lt_of_le (by decide : 31 < 32) hlen
  rw [classWindow_carry,
    inStringMask_getLsbD (by decide : 31 < 32) (List.getElem?_eq_getElem h31),
    classCarryAt_succ bs st 31, List.getElem?_eq_getElem h31]
  rfl

/-- The lane step at the halfway point: lane 32's seed is lane 31's bit. -/
theorem specInString64_step_32 {lo hi : Block32} {st : ClassState} :
    (specInString64 lo hi st).getLsbD 32
      = ((specQuote64 lo hi st).getLsbD 32 ^^ (specInString64 lo hi st).getLsbD 31) := by
  rw [specInString64_bit_32, specQuote64_bit_32,
    specInString64_bit_lo (k := 31) (by decide : 31 < 32),
    inStringMask_zero (ofFn_getElem? (by decide : 0 < 32)),
    classWindow_carry_inside (List.ofFn lo) st (by simp)]

/-- The lane step inside the high half: `x_{k+1} = q_{k+1} ⊕ x_k`. -/
theorem specInString64_step_hi {lo hi : Block32} {st : ClassState} {k : Nat}
    (hk : 33 ≤ k + 1) (hk64 : k + 1 < 64) :
    (specInString64 lo hi st).getLsbD (k + 1)
      = ((specQuote64 lo hi st).getLsbD (k + 1) ^^ (specInString64 lo hi st).getLsbD k) := by
  have hk32 : 32 ≤ k := by omega
  rw [specInString64_bit_hi' (j := k + 1) (Nat.le_trans (by decide : 32 ≤ 33) hk) hk64,
    specQuote64_bit_hi' (j := k + 1) (Nat.le_trans (by decide : 32 ≤ 33) hk) hk64,
    specInString64_bit_hi' (j := k) hk32 (by omega)]
  rw [show k + 1 - 32 = ((k - 32) + 1) from by omega]
  exact inStringMask_recur (bs := List.ofFn hi)
    (st := (classWindow (List.ofFn lo) st).carry) (i := k - 32) (by omega)
    (ofFn_getElem? (by omega)) (ofFn_getElem? (by omega))

/-- **The sixty-four-lane identity.**  The kernel's in-string mask over one block
is the all-ones carry-less product of its unescaped-quote mask, XOR the carry
word: `m = pclmul(qm, all-ones) ⊕ carry`.  No hypothesis is needed here because
`Block32` is total: both halves are full windows, which is the case the identity
is stated for. -/
theorem specInString64_eq_clmul (lo hi : Block32) (st : ClassState) :
    specInString64 lo hi st =
      clmul (specQuote64 lo hi st) (BitVec.allOnes 64) ^^^ seedVec 64 st.inside := by
  refine eq_clmul_of_recur (a := specQuote64 lo hi st)
    (c := clmul (specQuote64 lo hi st) (BitVec.allOnes 64))
    (m := specInString64 lo hi st) (seed := st.inside) ?_ ?_ ?_ ?_
  · exact clmul_allOnes_getLsbD_zero _
  · intro k hk
    exact clmul_allOnes_getLsbD_succ hk
  · rw [specInString64_bit_lo (k := 0) (by decide : 0 < 32),
      specQuote64_bit_lo (k := 0) (by decide : 0 < 32)]
    exact inStringMask_zero (ofFn_getElem? (by decide : 0 < 32))
  · intro k hk
    by_cases hlt : k + 1 < 32
    · rw [specInString64_bit_lo (k := k + 1) hlt, specQuote64_bit_lo (k := k + 1) hlt,
        specInString64_bit_lo (k := k) (Nat.lt_of_succ_lt hlt)]
      exact inStringMask_recur hlt (ofFn_getElem? (Nat.lt_of_succ_lt hlt)) (ofFn_getElem? hlt)
    · by_cases hb : k + 1 = 32
      · have hk31 : k = 31 := by omega
        rw [hb, hk31]
        exact specInString64_step_32
      · exact specInString64_step_hi (by omega) hk

/-! ### The outgoing carry

The carry the next block is entered with is this block's top in-string bit, which
is the kernel's `%carryn = ashr %m, 63`. -/

/-- **The outgoing carry.**  The carry the next block inherits is bit 63 of the
joined in-string mask: the block boundary is not a second rule, it is the mask's
top lane. -/
theorem specInString64_outgoing_carry (lo hi : Block32) (st : ClassState) :
    (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry.inside
      = (specInString64 lo hi st).getLsbD 63 := by
  rw [classWindow_carry_inside (List.ofFn hi) _ (by simp)]
  rw [show (31 : Nat) = 63 - 32 from by decide]
  exact (specInString64_bit_hi' (j := 63) (by decide : 32 ≤ 63) (by decide : 63 < 64)).symm

/-- The same fact read through the identity: the carry the next block inherits is
bit 63 of `pclmul(qm, all-ones) ⊕ carry`. -/
theorem specInString64_outgoing_carry_pclmul (lo hi : Block32) (st : ClassState) :
    (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry.inside
      = ((clmul (specQuote64 lo hi st) (BitVec.allOnes 64)
          ^^^ seedVec 64 st.inside)).getLsbD 63 := by
  rw [specInString64_outgoing_carry, specInString64_eq_clmul]

end LeanLLVM.Refinement.Pclmul
