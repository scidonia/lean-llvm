/-
Kernel-checked comma-mask identities.

This file establishes that the packed SWAR formula and the byte loop both meet
the lane-wise specification, with no native axioms:

  `swar_eq_spec`, `byteLoop_eq_spec`, and
  `byteLoop_refines_swar : commaContract ⊢ byteLoop ⊑ swar`.

The proof is a byte-lane argument.  The packed addition in `swar` is shown to be
a concatenation of eight independent byte additions (no lane carries), each lane
is discharged by a 256-case kernel `decide` on eight bits, and the eight lanes
are glued back into the 64-bit word by a base-256 digit decomposition.  No
`bv_decide`, `native_decide`, `sorry` or `admit` is used.
-/
import LeanLLVM.Vellum.CommaMask

namespace LeanLLVM.Vellum

/-! ### Byte lanes -/

/-- The `i`-th byte lane of a 64-bit word. -/
def lane (x : BitVec 64) (i : Nat) : BitVec 8 := x.extractLsb' (8 * i) 8

/-- The `i`-th base-256 digit of a natural number. -/
def byte (n : Nat) (i : Nat) : Nat := n / 256 ^ i % 256

/-- The per-lane test of the loop formulation: byte `t` of the comma-XOR word
is zero. -/
abbrev isZeroByte (m : BitVec 64) (t : Nat) : Prop := ((m >>> (8 * t)) &&& 0xFF) = 0

theorem two_pow_eight : (2 : Nat) ^ 8 = 256 := by decide

theorem two_pow_sixtyfour : (2 : Nat) ^ 64 = 256 ^ 8 := by decide

theorem pow_256 (i : Nat) : (2 : Nat) ^ (8 * i) = 256 ^ i := by
  rw [Nat.pow_mul, two_pow_eight]

theorem lane_def (x : BitVec 64) (i : Nat) : lane x i = x.extractLsb' (8 * i) 8 := rfl

theorem byte_def (n i : Nat) : byte n i = n / 256 ^ i % 256 := rfl

theorem lane_toNat (x : BitVec 64) (i : Nat) : (lane x i).toNat = byte x.toNat i := by
  rw [lane_def, byte_def, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, pow_256,
    two_pow_eight]

/-- The `0` literal of a `BitVec` and `0#w` are definitionally but not
syntactically equal, so the rewrites below go through these forms. -/
theorem extractLsb'_zero' (start : Nat) :
    BitVec.extractLsb' start 8 (0 : BitVec 64) = (0 : BitVec 8) :=
  BitVec.extractLsb'_zero

theorem or_zero' {w : Nat} (x : BitVec w) : x ||| (0 : BitVec w) = x := BitVec.or_zero

theorem zero_or' {w : Nat} (x : BitVec w) : (0 : BitVec w) ||| x = x := BitVec.zero_or

theorem or_self' {w : Nat} (x : BitVec w) : x ||| x = x := BitVec.or_self

theorem or_assoc' {w : Nat} (x y z : BitVec w) : x ||| y ||| z = x ||| (y ||| z) :=
  BitVec.or_assoc x y z

theorem toNat_zero_eight : ((0 : BitVec 8)).toNat = 0 := by decide

theorem toNat_zero_sixtyfour : ((0 : BitVec 64)).toNat = 0 := by decide

theorem toNat_ite_zero (c : Prop) [Decidable c] (v : BitVec 8) :
    (if c then v else 0).toNat = if c then v.toNat else 0 := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    decide

theorem lane_zero (i : Nat) : lane (0 : BitVec 64) i = 0 := by
  rw [lane_def]
  exact extractLsb'_zero' (8 * i)

theorem lane_ite (c : Prop) [Decidable c] (u v : BitVec 64) (i : Nat) :
    lane (if c then u else v) i = if c then lane u i else lane v i := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

theorem lane_or (u v : BitVec 64) (i : Nat) : lane (u ||| v) i = lane u i ||| lane v i := by
  rw [lane_def, lane_def, lane_def, BitVec.extractLsb'_or]

theorem lane_and (u v : BitVec 64) (i : Nat) : lane (u &&& v) i = lane u i &&& lane v i := by
  rw [lane_def, lane_def, lane_def, BitVec.extractLsb'_and]

theorem lane_xor (u v : BitVec 64) (i : Nat) : lane (u ^^^ v) i = lane u i ^^^ lane v i := by
  rw [lane_def, lane_def, lane_def, BitVec.extractLsb'_xor]

/-! ### The repeated-byte constants

`repOnes k` is the packed byte pattern `01 01 .. 01`, so `c * repOnes 8` is the
constant with byte `c` in every lane.  Its base-256 digits are all `c`. -/

/-- `repOnes k = 1 + 256 + ... + 256 ^ (k-1)`. -/
def repOnes : Nat → Nat
  | 0 => 0
  | k + 1 => repOnes k + 256 ^ k

theorem repOnes_mul_255 (k : Nat) : 255 * repOnes k = 256 ^ k - 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [repOnes, Nat.mul_add, ih, Nat.pow_succ]
    have hsp : 256 ^ k * 256 = 255 * 256 ^ k + 256 ^ k := by
      rw [Nat.mul_comm]
      exact Nat.succ_mul 255 _
    have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
    omega

theorem repOnes_lt (k : Nat) : repOnes k < 256 ^ k := by
  have h1 : repOnes k ≤ 255 * repOnes k := Nat.le_mul_of_pos_left _ (by decide)
  have h2 : 255 * repOnes k = 256 ^ k - 1 := repOnes_mul_255 k
  have h3 : 0 < 256 ^ k := Nat.pow_pos (by decide)
  omega

theorem mul_repOnes_lt (c k : Nat) (hc : c < 256) : c * repOnes k < 256 ^ k := by
  have h1 : c * repOnes k ≤ 255 * repOnes k := Nat.mul_le_mul_right _ (by omega)
  have h2 : 255 * repOnes k = 256 ^ k - 1 := repOnes_mul_255 k
  have h3 : 0 < 256 ^ k := Nat.pow_pos (by decide)
  omega

theorem repOnes_add (m n : Nat) : repOnes (m + n) = repOnes m + 256 ^ m * repOnes n := by
  induction n with
  | zero => simp [repOnes]
  | succ n ih =>
    rw [Nat.add_succ]
    simp only [repOnes]
    rw [ih, Nat.pow_add, Nat.mul_add]
    ac_rfl

/-! ### Base-256 digits -/

theorem mod_pow_succ (n k : Nat) :
    n % 256 ^ (k + 1) = n % 256 ^ k + n / 256 ^ k % 256 * 256 ^ k := by
  rw [Nat.pow_succ]
  have h1 : n % (256 ^ k * 256) / 256 ^ k = n / 256 ^ k % 256 :=
    Nat.mod_mul_right_div_self n (256 ^ k) 256
  have h2 : n % (256 ^ k * 256) % 256 ^ k = n % 256 ^ k := by
    rw [Nat.mul_comm]
    exact Nat.mod_mul_left_mod n 256 (256 ^ k)
  have h3 := Nat.div_add_mod (n % (256 ^ k * 256)) (256 ^ k)
  rw [h1, h2] at h3
  rw [← h3]
  ac_rfl

/-- `digits n k` is the value of the `k` low base-256 digits of `n`. -/
def digits (n : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => digits n k + byte n k * 256 ^ k

theorem digits_eq_mod (n k : Nat) : digits n k = n % 256 ^ k := by
  induction k with
  | zero => rw [digits, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    rw [digits, ih, mod_pow_succ]
    rfl

theorem digits_congr {a b : Nat} (h : ∀ j, j < 8 → byte a j = byte b j) :
    ∀ k, k ≤ 8 → digits a k = digits b k := by
  intro k
  induction k with
  | zero => intro _; rw [digits, digits]
  | succ k ih =>
    intro hk
    rw [digits, digits, ih (by omega), h k (by omega)]

/-! ### Lane glue

Two 64-bit words with the same eight lanes are equal. -/

theorem toNat_eq_digits (x : BitVec 64) : x.toNat = digits x.toNat 8 := by
  rw [digits_eq_mod, ← two_pow_sixtyfour]
  exact (Nat.mod_eq_of_lt (BitVec.isLt x)).symm

theorem eq_of_lane_eq {a b : BitVec 64} (h : ∀ j, j < 8 → lane a j = lane b j) : a = b := by
  apply BitVec.toNat_inj.mp
  have hb : ∀ j, j < 8 → byte a.toNat j = byte b.toNat j := by
    intro j hj
    have h' := congrArg BitVec.toNat (h j hj)
    rwa [lane_toNat, lane_toNat] at h'
  rw [toNat_eq_digits a, toNat_eq_digits b]
  exact digits_congr hb 8 (by omega)

/-! ### No lane carries

Adding a packed byte pattern whose lanes sum to less than `256` never carries
out of a lane: the base-256 digits of the sum are the sums of the digits. -/

theorem noCarry (a b : Nat) :
    ∀ k, (∀ t, t < k → byte a t + byte b t < 256) →
      (a + b) % 256 ^ k = a % 256 ^ k + b % 256 ^ k ∧
        a % 256 ^ k + b % 256 ^ k < 256 ^ k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [Nat.mod_one, Nat.mod_one, Nat.mod_one]
    exact ⟨by omega, by omega⟩
  | succ k ih =>
    intro h
    have hprev := ih (fun t ht => h t (Nat.lt_succ_of_lt ht))
    have hk : byte a k + byte b k < 256 := h k (Nat.lt_succ_self k)
    have ha := mod_pow_succ a k
    have hb := mod_pow_succ b k
    have hsp : 256 ^ k * 256 = 255 * 256 ^ k + 256 ^ k := by
      rw [Nat.mul_comm]
      exact Nat.succ_mul 255 _
    have hsum : a % 256 ^ (k + 1) + b % 256 ^ (k + 1)
        = (a % 256 ^ k + b % 256 ^ k) + (byte a k + byte b k) * 256 ^ k := by
      rw [ha, hb, Nat.add_mul]
      ac_rfl
    have hlt : a % 256 ^ (k + 1) + b % 256 ^ (k + 1) < 256 ^ (k + 1) := by
      rw [hsum, Nat.pow_succ]
      have h1 : a % 256 ^ k + b % 256 ^ k ≤ 256 ^ k - 1 := by omega
      have h2 : (byte a k + byte b k) * 256 ^ k ≤ 255 * 256 ^ k :=
        Nat.mul_le_mul_right _ (by omega)
      have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
      have h3 : 256 ^ k - 1 + 255 * 256 ^ k = 256 ^ k * 256 - 1 := by omega
      omega
    refine ⟨?_, hlt⟩
    rw [Nat.add_mod, Nat.mod_eq_of_lt hlt]

theorem byte_add (a b : Nat) (h : ∀ t, t < 8 → byte a t + byte b t < 256)
    (j : Nat) (hj : j < 8) : byte (a + b) j = byte a j + byte b j := by
  have hM := noCarry a b (j + 1) (fun t ht => h t (by omega))
  have hP := noCarry a b j (fun t ht => h t (by omega))
  have hpos : 0 < 256 ^ j := Nat.pow_pos (by decide)
  have hdj : (a + b) % 256 ^ (j + 1) / 256 ^ j = byte (a + b) j := by
    rw [Nat.pow_succ]
    exact Nat.mod_mul_right_div_self (a + b) (256 ^ j) 256
  calc byte (a + b) j
      = (a + b) % 256 ^ (j + 1) / 256 ^ j := hdj.symm
    _ = (a % 256 ^ (j + 1) + b % 256 ^ (j + 1)) / 256 ^ j := by rw [hM.1]
    _ = byte a j + byte b j := by
        have e : a % 256 ^ (j + 1) + b % 256 ^ (j + 1)
            = (a % 256 ^ j + b % 256 ^ j) + (byte a j + byte b j) * 256 ^ j := by
          rw [mod_pow_succ a j, mod_pow_succ b j, Nat.add_mul]
          ac_rfl
        rw [e, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hP.2, Nat.zero_add]

theorem lane_add_of_byte (u v : BitVec 64) (j : Nat) (hj : j < 8)
    (hov : u.toNat + v.toNat < 2 ^ 64)
    (h : ∀ t, t < 8 → byte u.toNat t + byte v.toNat t < 256) :
    lane (u + v) j = lane u j + lane v j := by
  have hsum : (u + v).toNat = u.toNat + v.toNat := by
    rw [BitVec.toNat_add, ← two_pow_sixtyfour, Nat.mod_eq_of_lt hov]
  apply BitVec.toNat_inj.mp
  rw [lane_toNat, hsum, BitVec.toNat_add, lane_toNat, lane_toNat, two_pow_eight,
    Nat.mod_eq_of_lt (h j hj)]
  exact byte_add u.toNat v.toNat h j hj

/-! ### Constant lanes -/

theorem byte_mul_repOnes (c : Nat) (hc : c < 256) (j : Nat) (hj : j < 8) :
    byte (c * repOnes 8) j = c := by
  have hpos : 0 < 256 ^ j := Nat.pow_pos (by decide)
  have hjc : j + 1 + (8 - (j + 1)) = 8 := Nat.add_sub_of_le hj
  have hT8 : repOnes 8 = repOnes (j + 1) + 256 ^ (j + 1) * repOnes (8 - (j + 1)) := by
    have h := repOnes_add (j + 1) (8 - (j + 1))
    rwa [hjc] at h
  have e : c * repOnes 8 = c * repOnes j +
      (c + 256 * (c * repOnes (8 - (j + 1)))) * 256 ^ j := by
    rw [hT8]
    simp only [repOnes, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_mul]
    ac_rfl
  have hdiv : (c * repOnes j + (c + 256 * (c * repOnes (8 - (j + 1)))) * 256 ^ j)
      / 256 ^ j = c + 256 * (c * repOnes (8 - (j + 1))) := by
    rw [Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (mul_repOnes_lt c j hc),
      Nat.zero_add]
  rw [byte_def, e, hdiv, Nat.mul_comm 256 (c * repOnes (8 - (j + 1))),
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem lane_mul_repOnes (c : Nat) (hc : c < 256) (j : Nat) (hj : j < 8) :
    lane (BitVec.ofNat 64 (c * repOnes 8)) j = BitVec.ofNat 8 c := by
  apply BitVec.toNat_inj.mp
  rw [lane_toNat, BitVec.toNat_ofNat, two_pow_sixtyfour,
    Nat.mod_eq_of_lt (mul_repOnes_lt c 8 hc), byte_mul_repOnes c hc j hj,
    BitVec.toNat_ofNat, two_pow_eight, Nat.mod_eq_of_lt hc]

theorem lane_seven (j : Nat) (hj : j < 8) :
    lane (0x7F7F7F7F7F7F7F7F : BitVec 64) j = 0x7F := by
  have h : (0x7F7F7F7F7F7F7F7F : BitVec 64) = BitVec.ofNat 64 (127 * repOnes 8) := by
    decide
  rw [h, lane_mul_repOnes 127 (by decide) j hj]
  decide

theorem lane_eighty (j : Nat) (hj : j < 8) :
    lane (0x8080808080808080 : BitVec 64) j = 0x80 := by
  have h : (0x8080808080808080 : BitVec 64) = BitVec.ofNat 64 (128 * repOnes 8) := by
    decide
  rw [h, lane_mul_repOnes 128 (by decide) j hj]
  decide

theorem lane_allOnes (j : Nat) (hj : j < 8) :
    lane (BitVec.allOnes 64) j = BitVec.allOnes 8 := by
  have h : BitVec.allOnes 64 = BitVec.ofNat 64 (255 * repOnes 8) := by decide
  rw [h, lane_mul_repOnes 255 (by decide) j hj]
  decide

theorem lane_not (u : BitVec 64) (j : Nat) (hj : j < 8) : lane (~~~u) j = ~~~lane u j := by
  rw [BitVec.not_def, lane_xor, lane_allOnes j hj, BitVec.xor_comm]
  exact BitVec.xor_allOnes

/-! ### Shifted high bits -/

theorem byte_mul_pow (c a : Nat) (hc : c < 256) (j : Nat) :
    byte (c * 256 ^ a) j = if a = j then c else 0 := by
  rw [byte_def]
  rcases Nat.lt_trichotomy a j with hlt | heq | hgt
  · have h1 : c * 256 ^ a ≤ 255 * 256 ^ a := Nat.mul_le_mul_right _ (by omega)
    have h2 : 255 * 256 ^ a < 256 * 256 ^ a :=
      Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
    have h3 : 256 * 256 ^ a = 256 ^ (a + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have h4 : 256 ^ (a + 1) ≤ 256 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
    have h5 : c * 256 ^ a < 256 ^ j := by omega
    rw [Nat.div_eq_of_lt h5, ite_eq_right (by omega)]
  · rw [heq, ite_eq_left rfl, Nat.mul_comm,
      Nat.mul_div_right _ (Nat.pow_pos (by decide)), Nat.mod_eq_of_lt hc]
  · have hpow : 256 ^ a = 256 ^ j * 256 ^ (a - j) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hsplit : 256 ^ (a - j) = 256 * 256 ^ (a - j - 1) := by
      rw [Nat.mul_comm 256 (256 ^ (a - j - 1)), ← Nat.pow_succ]
      congr 1
      omega
    rw [hpow, Nat.mul_left_comm, Nat.mul_div_right _ (Nat.pow_pos (by decide)),
      ite_eq_right (by omega), hsplit, Nat.mul_left_comm c 256,
      Nat.mul_comm 256 (c * 256 ^ (a - j - 1)), Nat.mul_mod_left]

theorem natCast_eighty_shift (t : Nat) :
    ((128 <<< (8 * t) : Nat) : BitVec 64) = (0x80 : BitVec 64) <<< (8 * t) := by
  apply BitVec.toNat_inj.mp
  rw [show ((128 <<< (8 * t) : Nat) : BitVec 64) = BitVec.ofNat 64 (128 <<< (8 * t)) from rfl,
    BitVec.toNat_ofNat, BitVec.toNat_shiftLeft,
    show ((0x80 : BitVec 64)).toNat = 128 from by decide]

theorem lane_shift_eighty (a : Nat) (ha : a < 8) (j : Nat) :
    lane ((0x80 : BitVec 64) <<< (8 * a)) j = if a = j then 0x80 else 0 := by
  have hb : 128 * 256 ^ a < 256 ^ 8 := by
    have h1 : 128 * 256 ^ a ≤ 255 * 256 ^ a := Nat.mul_le_mul_right _ (by omega)
    have h2 : 255 * 256 ^ a < 256 * 256 ^ a :=
      Nat.mul_lt_mul_of_pos_right (by decide) (Nat.pow_pos (by decide))
    have h3 : 256 * 256 ^ a = 256 ^ (a + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have h4 : 256 ^ (a + 1) ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hshift : (0x80 : BitVec 64) <<< (8 * a) = BitVec.ofNat 64 (128 * 256 ^ a) := by
    apply BitVec.toNat_inj.mp
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, pow_256, BitVec.toNat_ofNat,
      show ((0x80 : BitVec 64)).toNat = 128 from by decide]
  apply BitVec.toNat_inj.mp
  rw [hshift, lane_toNat, BitVec.toNat_ofNat, two_pow_sixtyfour, Nat.mod_eq_of_lt hb,
    byte_mul_pow 128 a (by decide) j, toNat_ite_zero,
    show ((0x80 : BitVec 8)).toNat = 128 from by decide]

/-! ### The 8-bit field identity -/

/-- Per lane: the packed add sets the lane's high bit iff the byte was nonzero,
so the complemented, masked lane is the `0x80` marker iff the byte was zero. -/
theorem swar_byte_identity : ∀ c : BitVec 8,
    ~~~(((c &&& 0x7F) + 0x7F) ||| c) &&& 0x80 = if c = 0 then 0x80 else 0 := by
  decide

/-! ### Lane of the packed baseline -/

theorem lane_swar (x : BitVec 64) (j : Nat) (hj : j < 8) :
    lane (swar x) j = if lane (x ^^^ 0x2C2C2C2C2C2C2C2C) j = 0 then 0x80 else 0 := by
  have hov : (((x ^^^ 0x2C2C2C2C2C2C2C2C) &&& 0x7F7F7F7F7F7F7F7F)).toNat
      + (0x7F7F7F7F7F7F7F7F : BitVec 64).toNat < 2 ^ 64 := by
    have h1 : (((x ^^^ 0x2C2C2C2C2C2C2C2C) &&& 0x7F7F7F7F7F7F7F7F)).toNat
        ≤ 0x7F7F7F7F7F7F7F7F := by
      rw [BitVec.toNat_and]
      exact Nat.and_le_right
    have h2 : (0x7F7F7F7F7F7F7F7F : BitVec 64).toNat = 0x7F7F7F7F7F7F7F7F := by decide
    omega
  have hb : ∀ t, t < 8 →
      byte (((x ^^^ 0x2C2C2C2C2C2C2C2C) &&& 0x7F7F7F7F7F7F7F7F)).toNat t
        + byte (0x7F7F7F7F7F7F7F7F : BitVec 64).toNat t < 256 := by
    intro t ht
    have h1 : byte (((x ^^^ 0x2C2C2C2C2C2C2C2C) &&& 0x7F7F7F7F7F7F7F7F)).toNat t
        = ((lane (x ^^^ 0x2C2C2C2C2C2C2C2C) t &&& 0x7F) : BitVec 8).toNat := by
      rw [← lane_toNat, lane_and, lane_seven t ht]
    have h2 : byte (0x7F7F7F7F7F7F7F7F : BitVec 64).toNat t = 127 := by
      rw [← lane_toNat, lane_seven t ht]
      decide
    have h3 : ((lane (x ^^^ 0x2C2C2C2C2C2C2C2C) t &&& 0x7F) : BitVec 8).toNat ≤ 127 := by
      rw [BitVec.toNat_and, show ((0x7F : BitVec 8)).toNat = 127 from by decide]
      exact Nat.and_le_right
    rw [h1, h2]
    omega
  unfold swar
  dsimp only
  rw [lane_and, lane_not _ j hj, lane_eighty j hj, lane_or,
    lane_add_of_byte ((x ^^^ 0x2C2C2C2C2C2C2C2C) &&& 0x7F7F7F7F7F7F7F7F)
      (0x7F7F7F7F7F7F7F7F : BitVec 64) j hj hov hb,
    lane_and, lane_seven j hj]
  exact swar_byte_identity _

/-! ### The fold formulation

Both `spec` and `byteLoop` are the same fold over the eight lanes. -/

/-- The shared fold: OR in a lone high bit for every zero byte. -/
def maskFold (m : BitVec 64) : BitVec 64 :=
  ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat).foldl
    (fun acc t => acc ||| (if isZeroByte m t then (0x80 : BitVec 64) <<< (8 * t) else 0)) 0

theorem mem_eight (j : Nat) : j ∈ ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat) ↔ j < 8 := by
  rw [show ([0, 1, 2, 3, 4, 5, 6, 7] : List Nat) = List.range 8 from by decide,
    List.mem_range]

theorem ite_or_mem {w : Nat} (a j : Nat) (v : BitVec w) (l : List Nat) :
    (if a = j then v else 0) ||| (if j ∈ l then v else 0) = if j ∈ a :: l then v else 0 := by
  have hmem : (j ∈ a :: l) ↔ (a = j ∨ j ∈ l) := by
    rw [List.mem_cons]
    exact ⟨fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr,
      fun h => h.elim (fun h1 => Or.inl h1.symm) Or.inr⟩
  by_cases h1 : a = j
  · by_cases h2 : j ∈ l
    · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (hmem.mpr (Or.inl h1)), or_self']
    · rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (hmem.mpr (Or.inl h1)), or_zero']
  · by_cases h2 : j ∈ l
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (hmem.mpr (Or.inr h2)), zero_or']
    · rw [ite_eq_right h1, ite_eq_right h2,
        ite_eq_right (fun h => (hmem.mp h).elim h1 h2), zero_or']

theorem foldl_or_lane (m : BitVec 64) (l : List Nat) (acc : BitVec 64) (j : Nat)
    (hl : ∀ t ∈ l, t < 8) :
    lane (l.foldl (fun acc t =>
        acc ||| (if isZeroByte m t then (0x80 : BitVec 64) <<< (8 * t) else 0)) acc) j
      = lane acc j ||| (if j ∈ l then (if isZeroByte m j then 0x80 else 0) else 0) := by
  induction l generalizing acc with
  | nil =>
    rw [List.foldl_nil, ite_eq_right List.not_mem_nil, or_zero']
  | cons a as ih =>
    have ha : a < 8 := hl a List.mem_cons_self
    have hstep : lane (acc ||| (if isZeroByte m a then (0x80 : BitVec 64) <<< (8 * a) else 0)) j
        = lane acc j ||| (if a = j then (if isZeroByte m j then 0x80 else 0) else 0) := by
      rw [lane_or, lane_ite, lane_shift_eighty a ha j, lane_zero]
      congr 1
      by_cases haj : a = j
      · rw [haj, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right haj]
        split <;> rfl
    rw [List.foldl_cons,
      ih (acc ||| (if isZeroByte m a then (0x80 : BitVec 64) <<< (8 * a) else 0))
        (fun t ht => hl t (List.mem_cons_of_mem a ht)),
      hstep, or_assoc', ite_or_mem]

theorem lane_maskFold (m : BitVec 64) (j : Nat) (hj : j < 8) :
    lane (maskFold m) j = if isZeroByte m j then 0x80 else 0 := by
  unfold maskFold
  rw [foldl_or_lane m [0, 1, 2, 3, 4, 5, 6, 7] 0 j (fun t ht => (mem_eight t).mp ht),
    lane_zero, zero_or', ite_eq_left ((mem_eight j).mpr hj)]

theorem isZeroByte_iff (m : BitVec 64) (j : Nat) : isZeroByte m j ↔ lane m j = 0 := by
  have hext : ∀ x : BitVec 64, ((x >>> (8 * j)) &&& 0xFF).toNat = byte x.toNat j := by
    intro x
    rw [byte_def, BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      pow_256, show ((0xFF : BitVec 64)).toNat = 255 from by decide,
      show (255 : Nat) = 2 ^ 8 - 1 from by decide, Nat.and_two_pow_sub_one_eq_mod,
      two_pow_eight]
  constructor
  · intro h
    have h1 : ((m >>> (8 * j)) &&& 0xFF).toNat = 0 := by rw [h]; exact toNat_zero_sixtyfour
    rw [hext] at h1
    apply BitVec.eq_of_toNat_eq
    rw [lane_toNat, h1, toNat_zero_eight]
  · intro h
    have h1 : (lane m j).toNat = 0 := by rw [h]; exact toNat_zero_eight
    rw [lane_toNat] at h1
    apply BitVec.eq_of_toNat_eq
    rw [hext, h1, toNat_zero_sixtyfour]

theorem lane_maskFold' (m : BitVec 64) (j : Nat) (hj : j < 8) :
    lane (maskFold m) j = if lane m j = 0 then 0x80 else 0 := by
  rw [lane_maskFold m j hj]
  by_cases h : lane m j = 0
  · rw [ite_eq_left h, ite_eq_left ((isZeroByte_iff m j).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h ((isZeroByte_iff m j).mp hc))]

theorem foldl_congr' {f g : BitVec 64 → Nat → BitVec 64} (init : BitVec 64) (l : List Nat)
    (h : ∀ acc t, f acc t = g acc t) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, List.foldl_cons, h init a, ih (g init a)]

theorem byteLoop_eq_maskFold (x : BitVec 64) :
    byteLoop x = maskFold (x ^^^ 0x2C2C2C2C2C2C2C2C) := by
  unfold byteLoop maskFold
  apply foldl_congr'
  intro acc t
  dsimp only
  by_cases h : ((x ^^^ 0x2C2C2C2C2C2C2C2C) >>> (8 * t)) &&& 0xFF = 0
  · rw [ite_eq_left h, ite_eq_left h, natCast_eighty_shift t]
  · rw [ite_eq_right h, ite_eq_right h, or_zero']

theorem spec_eq_maskFold (x : BitVec 64) :
    spec x = maskFold (x ^^^ 0x2C2C2C2C2C2C2C2C) := by
  have e0 : ∀ m : BitVec 64,
      (if ((m >>> 0) &&& 0xFF) = 0 then (0x0000000000000080 : BitVec 64) else 0)
        = (if ((m >>> (8 * 0)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 0) else 0) := by
    intro m
    rw [show (8 * 0 : Nat) = 0 from by decide]
    by_cases h : ((m >>> 0) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e1 : ∀ m : BitVec 64,
      (if ((m >>> 8) &&& 0xFF) = 0 then (0x0000000000008000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 1)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 1) else 0) := by
    intro m
    rw [show (8 * 1 : Nat) = 8 from by decide]
    by_cases h : ((m >>> 8) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e2 : ∀ m : BitVec 64,
      (if ((m >>> 16) &&& 0xFF) = 0 then (0x0000000000800000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 2)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 2) else 0) := by
    intro m
    rw [show (8 * 2 : Nat) = 16 from by decide]
    by_cases h : ((m >>> 16) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e3 : ∀ m : BitVec 64,
      (if ((m >>> 24) &&& 0xFF) = 0 then (0x0000000080000000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 3)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 3) else 0) := by
    intro m
    rw [show (8 * 3 : Nat) = 24 from by decide]
    by_cases h : ((m >>> 24) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e4 : ∀ m : BitVec 64,
      (if ((m >>> 32) &&& 0xFF) = 0 then (0x0000008000000000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 4)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 4) else 0) := by
    intro m
    rw [show (8 * 4 : Nat) = 32 from by decide]
    by_cases h : ((m >>> 32) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e5 : ∀ m : BitVec 64,
      (if ((m >>> 40) &&& 0xFF) = 0 then (0x0000800000000000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 5)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 5) else 0) := by
    intro m
    rw [show (8 * 5 : Nat) = 40 from by decide]
    by_cases h : ((m >>> 40) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e6 : ∀ m : BitVec 64,
      (if ((m >>> 48) &&& 0xFF) = 0 then (0x0080000000000000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 6)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 6) else 0) := by
    intro m
    rw [show (8 * 6 : Nat) = 48 from by decide]
    by_cases h : ((m >>> 48) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  have e7 : ∀ m : BitVec 64,
      (if ((m >>> 56) &&& 0xFF) = 0 then (0x8000000000000000 : BitVec 64) else 0)
        = (if ((m >>> (8 * 7)) &&& 0xFF) = 0 then (0x80 : BitVec 64) <<< (8 * 7) else 0) := by
    intro m
    rw [show (8 * 7 : Nat) = 56 from by decide]
    by_cases h : ((m >>> 56) &&& 0xFF) = 0
    · rw [ite_eq_left h, ite_eq_left h]; decide
    · rw [ite_eq_right h, ite_eq_right h]
  unfold spec maskFold isZeroByte
  simp only [List.foldl_cons, List.foldl_nil, e0, e1, e2, e3, e4, e5, e6, e7]
  rw [zero_or']

/-! ### The two identities and the refinement -/

theorem swar_eq_spec (x : BitVec 64) : swar x = spec x := by
  apply eq_of_lane_eq
  intro j hj
  rw [lane_swar x j hj, spec_eq_maskFold x, lane_maskFold' _ j hj]

theorem byteLoop_eq_spec (x : BitVec 64) : byteLoop x = spec x := by
  rw [byteLoop_eq_maskFold x, ← spec_eq_maskFold x]

theorem byteLoop_refines_swar : commaContract ⊢ byteLoop ⊑ swar := by
  intro x _
  rw [byteLoop_eq_spec, swar_eq_spec]

theorem swar_correct : Correct commaContract swar := by
  intro x _
  exact swar_eq_spec x

theorem byteLoop_correct : Correct commaContract byteLoop :=
  Correct.of_refines byteLoop_refines_swar swar_correct

theorem twoCallContext_preserved (x : BitVec 64) :
    twoCallContext.run byteLoop x = twoCallContext.run swar x :=
  Context.refines byteLoop_refines_swar twoCallContext_admissible x trivial

/-! ### The `UInt64` seam

The probe's exported functions are `UInt64`; this is the same statement at the
type the C ABI uses.  The object-level connection is the IR bridge in
`CommaMaskIR.lean`, and `probes/install/` binds the installed objects to that
bridge with kernel-derived certificates: the producer re-elaborates the proof
module, checks this statement and its axiom footprint, and the selector
reproduces the certificate byte for byte before installing a unit.  The
differential transcript in the same directory is runtime evidence, not proof. -/

def seamBaseline (x : UInt64) : UInt64 :=
  UInt64.ofBitVec (swar x.toBitVec)

def seamCandidate (x : UInt64) : UInt64 :=
  UInt64.ofBitVec (byteLoop x.toBitVec)

theorem seam_refines (x : UInt64) : seamCandidate x = seamBaseline x := by
  unfold seamCandidate seamBaseline
  rw [byteLoop_eq_spec, swar_eq_spec]

end LeanLLVM.Vellum
