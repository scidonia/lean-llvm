/-
The emitter's arithmetic, read off the two unit forms.

`JsonEscapeDecodeTrace` models the unescaper's `\u` emitter as three blocks —
`if.end3.i` (the high-surrogate guard), `land.lhs.true22.i`/`if.then26.i` (the
pair's second unit and its value) and `if.end32.i` (the UTF-8 store) — but its
steps leave three equations as hypotheses rather than closing them:

* `hword`, the store's word against the specification's encoding,
  `(udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat)`;
* the high-surrogate range, `%21 = %vecext.i207 &&& 64512` tested against
  `55296`, as `surrogateTail`'s first guard clause;
* the pair's value, `%add30.i`, as `surrogateTail`'s pair code point.

Each is arithmetic over the block's own `BitVec` form and none mentions the
specification's rules, so they are stated and proved here rather than in the
trace, whose file owns the steps.  The proofs are bit-lane arithmetic: a
packed word is a sum of bytes at disjoint shifts, and the lemma that a
disjoint `|||` is a `+` is `Nat.lor_eq_add_of_and_eq_zero` from `BitLanes`.
Enumeration is not the route — the sixteen-bit range measured at 2m42s and
the four-byte range is over a million units — so the splits follow
`utf8Encode`'s own ranges and `udIfEnd32Word`'s own selects, and each closed
range is arithmetic on quarters, sixteenths and sixty-fourths.

The three theorems are the pins' subject: they carry `[propext, Quot.sound]`
and no carrier.
-/
import LeanLLVM.Vellum.BitLanes
import LeanLLVM.Vellum.JsonEscapeDecodeTrace

set_option autoImplicit false

namespace LeanLLVM.Vellum

open LeanLLVM

/-! ### Bit-lane arithmetic

A value below `2^k` shares no bit with a multiple of `2^k`, so their `&&&` is
zero; that is the hypothesis `Nat.lor_eq_add_of_and_eq_zero` asks for.  The
rest are the laws that let a packed word be read as its bytes. -/

/-- `2^(k+1) - 1 = 2 * (2^k - 1) + 1`. -/
theorem pow_succ_sub_one (k : Nat) : 2^(k+1) - 1 = 2*(2^k - 1) + 1 := by
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  rw [Nat.pow_succ]
  omega

/-- `(2^(k+1) - 1) / 2 = 2^k - 1`. -/
theorem div_two_pow_succ_sub_one (k : Nat) : (2^(k+1) - 1) / 2 = 2^k - 1 := by
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  rw [pow_succ_sub_one k,
    show (2*(2^k-1) + 1) = (2^k-1)*2 + 1 from by rw [Nat.mul_comm], Nat.add_comm,
    Nat.add_mul_div_right _ _ (by decide : 0 < 2),
    Nat.div_eq_of_lt (by decide : 1 < 2), Nat.zero_add]

/-- Every bit below `k` is set in `2^k - 1`; the rest are clear. -/
theorem testBit_two_pow_sub_one_clean (k i : Nat) :
    (2^k - 1).testBit i = decide (i < k) := by
  induction k generalizing i with
  | zero => cases i <;> simp
  | succ k ih =>
    cases i with
    | zero =>
      rw [Nat.testBit_zero, pow_succ_sub_one k,
        Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt (by decide : 1 < 2)]
      simp
    | succ j =>
      rw [Nat.testBit_succ, div_two_pow_succ_sub_one, ih j]
      simp [Nat.succ_lt_succ_iff]

/-- `&&&` with `2^k - 1` is the remainder modulo `2^k`.

This is `and_two_pow_sub_one_eq_mod_clean`'s statement with a smaller footprint:
the core lemma reaches `Classical.choice` through `Nat.testBit_two_pow_sub_one`,
and the induction below stays at `[propext, Quot.sound]`. -/
theorem and_two_pow_sub_one_eq_mod_clean (x k : Nat) : x &&& (2^k - 1) = x % 2^k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mod_two_pow, testBit_two_pow_sub_one_clean]
  cases x.testBit i <;> cases decide (i < k) <;> simp

/-- A value below `2^k` and a multiple of `2^k` are disjoint. -/
theorem and_eq_zero_of_lt_two_pow_of_mod {a m k : Nat} (ha : a < 2^k)
    (hm : m % 2^k = 0) : a &&& m = 0 := by
  have ha' : a &&& (2^k - 1) = a := by
    rw [and_two_pow_sub_one_eq_mod_clean, Nat.mod_eq_of_lt ha]
  calc a &&& m = (a &&& (2^k - 1)) &&& m := by rw [ha']
    _ = a &&& ((2^k - 1) &&& m) := Nat.and_assoc a (2^k - 1) m
    _ = a &&& (m &&& (2^k - 1)) := by rw [Nat.and_comm (2^k - 1) m]
    _ = a &&& (m % 2^k) := by rw [and_two_pow_sub_one_eq_mod_clean]
    _ = 0 := by rw [hm, Nat.and_zero]

/-- Disjointness survives `|||`: a disjunction of two lanes shares nothing with
a mask neither lane meets. -/
theorem and_or_zero {a b m : Nat} (ha : a &&& m = 0) (hb : b &&& m = 0) :
    (a ||| b) &&& m = 0 := by
  rw [Nat.and_or_distrib_right, ha, hb, Nat.zero_or]

/-- `&&&` of two values shifted by the same `k` is the `&&&` of the values,
shifted back. -/
theorem mul_two_pow_and (x k c : Nat) :
    (x * 2^k) &&& (c * 2^k) = (x &&& c) * 2^k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_and]
  by_cases h : k ≤ i <;> simp [h]

/-- `&&&` with a mask that is `c` shifted by `k` reads the operand's bits at
`k` and above, as `c`'s own mask does. -/
theorem and_mask_shift (n k c : Nat) :
    n &&& (c * 2^k) = ((n / 2^k) &&& c) * 2^k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_and]
  by_cases h : k ≤ i
  · have hik : i - k + k = i := Nat.sub_add_cancel h
    rw [Nat.testBit_div_two_pow, hik]
    simp [h]
  · simp [h]

/-! ### The four ranges of `udIfEnd32Word`

`udIfEnd32Word` selects its packed form with the same three thresholds
`utf8Encode` uses, so each range closes separately: below `0x80` the word is
the unit, below `0x800` it is two bytes, below `0x10000` three, and the
four-byte form covers the rest of the code-point range.  Each proof reads the
block's `|||` chain as a sum of bytes at disjoint shifts. -/

/-- Below `0x80`: the word is the unit itself. -/
theorem udIfEnd32Word_toNat_lt80 (cp : BitVec 32) (h : cp.toNat < 0x80) :
    (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat) := by
  have hc65535 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 65535) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 65535).toNat = 65535 := by decide
    omega
  have hc2047 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 2047) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 2047).toNat = 2047 := by decide
    omega
  have hc127 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 127).toNat = 127 := by decide
    omega
  unfold udIfEnd32Word udIfEnd32S2 udIfEnd32S1
  rw [if_neg hc65535, if_neg hc2047, if_neg hc127]
  rw [utf8Encode_eq_one h]
  have hb : (UInt8.ofNat cp.toNat).toNat = cp.toNat := toNat_ofNat_of_lt (by omega)
  simp [bytesToNat, hb]

/-- Below `0x800`: `udIfEnd32Or2`'s two bytes are `utf8Encode`'s. -/
theorem udIfEnd32Word_toNat_lt800 (cp : BitVec 32)
    (h0 : ¬ cp.toNat < 0x80) (h1 : cp.toNat < 0x800) :
    (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat) := by
  have hc65535 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 65535) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 65535).toNat = 65535 := by decide
    omega
  have hc2047 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 2047) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 2047).toNat = 2047 := by decide
    omega
  have hc127 : evalICmp .ugt cp (BitVec.ofInt 32 127) = (1 : BitVec 1) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 127).toNat = 127 := by decide
    omega
  unfold udIfEnd32Word udIfEnd32S2 udIfEnd32S1 udIfEnd32Or2
  rw [if_neg hc65535, if_neg hc2047, if_pos hc127]
  rw [BitVec.toNat_or, BitVec.toNat_or]
  have hs6 : (cp >>> (BitVec.ofInt 32 6)).toNat = cp.toNat / 64 := by
    show (cp >>> (6 : Nat)).toNat = cp.toNat / 64
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have ha63 : (cp &&& (BitVec.ofInt 32 63)).toNat = cp.toNat % 64 := by
    rw [BitVec.toNat_and]
    have h63 : (BitVec.ofInt 32 63).toNat = 63 := by decide
    rw [h63, show (63 : Nat) = 2^6 - 1 from by decide, and_two_pow_sub_one_eq_mod_clean]
  have ho128 : ((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)).toNat =
      cp.toNat % 64 + 128 := by
    rw [BitVec.toNat_or]
    have h128 : (BitVec.ofInt 32 128).toNat = 128 := by decide
    rw [h128, ha63, Nat.or_two_pow_eq_add_of_lt (n := 7) (by omega)]
  have hs8 : (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<<
      (BitVec.ofInt 32 8)).toNat = (cp.toNat % 64 + 128) * 256 := by
    show (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<< (8 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), ho128]
  have h192 : (BitVec.ofInt 32 192).toNat = 192 := by decide
  rw [hs6, hs8, h192]
  have hA8 : cp.toNat / 64 < 2^8 := by omega
  have hB8 : ((cp.toNat % 64 + 128) * 256) % 2^8 = 0 := by
    rw [show (256 : Nat) = 2^8 from by decide]
    exact Nat.mul_mod_left _ _
  have hAB : (cp.toNat / 64) ||| ((cp.toNat % 64 + 128) * 256) =
      cp.toNat / 64 + (cp.toNat % 64 + 128) * 256 :=
    Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hA8 hB8)
  have hAB192 : (cp.toNat / 64 + (cp.toNat % 64 + 128) * 256) ||| 192 =
      cp.toNat / 64 + (cp.toNat % 64 + 128) * 256 + 192 := by
    rw [← hAB]
    refine Nat.lor_eq_add_of_and_eq_zero _ _ (and_or_zero ?_ ?_)
    · exact and_eq_zero_of_lt_two_pow_of_mod (k := 6) (by omega) (by decide)
    · rw [Nat.and_comm]
      exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 192 < 2^8) hB8
  rw [hAB, hAB192]
  rw [utf8Encode_eq_two h0 h1]
  have hb0 : (UInt8.ofNat (0xC0 + cp.toNat / 0x40)).toNat = 0xC0 + cp.toNat / 0x40 :=
    toNat_ofNat_of_lt (by omega)
  have hb1 : (UInt8.ofNat (0x80 + cp.toNat % 0x40)).toNat = 0x80 + cp.toNat % 0x40 :=
    toNat_ofNat_of_lt (by omega)
  simp only [bytesToNat, hb0, hb1]
  omega
theorem udIfEnd32Word_toNat_lt10000 (cp : BitVec 32)
    (h0 : ¬ cp.toNat < 0x800) (h1 : cp.toNat < 0x10000) :
    (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat) := by
  have hc65535 : ¬ (evalICmp .ugt cp (BitVec.ofInt 32 65535) = (1 : BitVec 1)) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 65535).toNat = 65535 := by decide
    omega
  have hc2047 : evalICmp .ugt cp (BitVec.ofInt 32 2047) = (1 : BitVec 1) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 2047).toNat = 2047 := by decide
    omega
  unfold udIfEnd32Word udIfEnd32S2 udIfEnd32Or13
  rw [if_neg hc65535, if_pos hc2047]
  rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  have hA : (cp >>> (BitVec.ofInt 32 12)).toNat = cp.toNat / 4096 := by
    show (cp >>> (12 : Nat)).toNat = cp.toNat / 4096
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hb1 : (((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)).toNat = cp.toNat / 64 % 64 + 128 := by
    rw [BitVec.toNat_or]
    have h63 : (BitVec.ofInt 32 63).toNat = 63 := by decide
    have h128 : (BitVec.ofInt 32 128).toNat = 128 := by decide
    rw [BitVec.toNat_and]
    have hs6 : (cp >>> (BitVec.ofInt 32 6)).toNat = cp.toNat / 64 := by
      show (cp >>> (6 : Nat)).toNat = cp.toNat / 64
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hs6, h63, h128, show (63 : Nat) = 2^6 - 1 from by decide,
      and_two_pow_sub_one_eq_mod_clean, Nat.or_two_pow_eq_add_of_lt (n := 7) (by omega)]
  have hi1 : (((((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)) <<< (BitVec.ofInt 32 8))).toNat =
      (cp.toNat / 64 % 64 + 128) * 256 := by
    show ((((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)) <<< (8 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hb1]
  have hb2 : ((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)).toNat =
      cp.toNat % 64 + 128 := by
    rw [BitVec.toNat_or]
    have h63 : (BitVec.ofInt 32 63).toNat = 63 := by decide
    have h128 : (BitVec.ofInt 32 128).toNat = 128 := by decide
    rw [BitVec.toNat_and, h63, h128, show (63 : Nat) = 2^6 - 1 from by decide,
      and_two_pow_sub_one_eq_mod_clean, Nat.or_two_pow_eq_add_of_lt (n := 7) (by omega)]
  have hi2 : (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<<
      (BitVec.ofInt 32 16)).toNat = (cp.toNat % 64 + 128) * 65536 := by
    show (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<< (16 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hb2]
  have h224 : (BitVec.ofInt 32 224).toNat = 224 := by decide
  rw [hA, hi1, hi2, h224]
  have hA8 : cp.toNat / 4096 < 2^8 := by omega
  have hB8 : ((cp.toNat / 64 % 64 + 128) * 256) % 2^8 = 0 := by
    rw [show (256 : Nat) = 2^8 from by decide]
    exact Nat.mul_mod_left _ _
  have hC8 : ((cp.toNat % 64 + 128) * 65536) % 2^8 = 0 := by
    rw [show (65536 : Nat) = 2^8 * 2^8 from by decide, ← Nat.mul_assoc]
    exact Nat.mul_mod_left _ _
  have hB16 : ((cp.toNat / 64 % 64 + 128) * 256) < 2^16 := by omega
  have hC16 : ((cp.toNat % 64 + 128) * 65536) % 2^16 = 0 := by
    rw [show (65536 : Nat) = 2^16 from by decide]
    exact Nat.mul_mod_left _ _
  have hbc : ((cp.toNat / 64 % 64 + 128) * 256) ||| ((cp.toNat % 64 + 128) * 65536) =
      (cp.toNat / 64 % 64 + 128) * 256 + (cp.toNat % 64 + 128) * 65536 :=
    Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hB16 hC16)
  have hbc8 : (((cp.toNat / 64 % 64 + 128) * 256) ||| ((cp.toNat % 64 + 128) * 65536)) % 2^8 = 0 := by
    rw [Nat.or_mod_two_pow, hB8, hC8, Nat.zero_or]
  have habc : (cp.toNat / 4096) ||| (((cp.toNat / 64 % 64 + 128) * 256) +
      (cp.toNat % 64 + 128) * 65536) =
      cp.toNat / 4096 + (((cp.toNat / 64 % 64 + 128) * 256) + (cp.toNat % 64 + 128) * 65536) := by
    rw [← hbc]
    exact Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hA8 hbc8)
  have hfinal : (cp.toNat / 4096 + (((cp.toNat / 64 % 64 + 128) * 256) +
      (cp.toNat % 64 + 128) * 65536)) ||| 224 =
      cp.toNat / 4096 + (((cp.toNat / 64 % 64 + 128) * 256) +
        (cp.toNat % 64 + 128) * 65536) + 224 := by
    rw [← habc, ← hbc]
    refine Nat.lor_eq_add_of_and_eq_zero _ _ (and_or_zero ?_ (and_or_zero ?_ ?_))
    · exact and_eq_zero_of_lt_two_pow_of_mod (k := 5) (by omega) (by decide)
    · rw [Nat.and_comm]
      exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 224 < 2^8) hB8
    · rw [Nat.and_comm]
      exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 224 < 2^8) hC8
  rw [hbc, habc, hfinal]
  rw [utf8Encode_eq_three (by omega) (by omega) h1]
  have hb0 : (UInt8.ofNat (0xE0 + cp.toNat / 0x1000)).toNat = 0xE0 + cp.toNat / 0x1000 :=
    toNat_ofNat_of_lt (by omega)
  have hb1' : (UInt8.ofNat (0x80 + cp.toNat / 0x40 % 0x40)).toNat =
      0x80 + cp.toNat / 0x40 % 0x40 := toNat_ofNat_of_lt (by omega)
  have hb2' : (UInt8.ofNat (0x80 + cp.toNat % 0x40)).toNat = 0x80 + cp.toNat % 0x40 :=
    toNat_ofNat_of_lt (by omega)
  simp only [bytesToNat, hb0, hb1', hb2']
  omega


theorem udIfEnd32Word_toNat_of_lt110000 (cp : BitVec 32) (h2 : ¬ cp.toNat < 0x10000)
    (h3 : cp.toNat < 0x110000) :
    (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat) := by
  have hc65535 : evalICmp .ugt cp (BitVec.ofInt 32 65535) = (1 : BitVec 1) := by
    rw [evalICmp_ugt_one_iff_toNat]
    have hc : (BitVec.ofInt 32 65535).toNat = 65535 := by decide
    omega
  unfold udIfEnd32Word udIfEnd32Or29
  rw [if_pos hc65535]
  rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or]
  have hA : (cp >>> (BitVec.ofInt 32 18)).toNat = cp.toNat / 262144 := by
    show (cp >>> (18 : Nat)).toNat = cp.toNat / 262144
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hs12 : (cp >>> (BitVec.ofInt 32 12)).toNat = cp.toNat / 4096 := by
    show (cp >>> (12 : Nat)).toNat = cp.toNat / 4096
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hs8 : (((cp >>> (BitVec.ofInt 32 12)) <<< (BitVec.ofInt 32 8))).toNat =
      (cp.toNat / 4096) * 256 := by
    show ((cp >>> (BitVec.ofInt 32 12)) <<< (8 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hs12]
  have hB : (((cp >>> (BitVec.ofInt 32 12)) <<< (BitVec.ofInt 32 8)) &&&
      (BitVec.ofInt 32 16128)).toNat = (cp.toNat / 4096 % 64) * 256 := by
    rw [BitVec.toNat_and, hs8]
    have h16128 : (BitVec.ofInt 32 16128).toNat = 16128 := by decide
    rw [h16128, show (16128 : Nat) = 63 * 256 from by decide,
      show (256 : Nat) = 2^8 from by decide, mul_two_pow_and,
      show (63 : Nat) = 2^6 - 1 from by decide, and_two_pow_sub_one_eq_mod_clean]
  have hb1 : (((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)).toNat = cp.toNat / 64 % 64 + 128 := by
    rw [BitVec.toNat_or, BitVec.toNat_and]
    have h63 : (BitVec.ofInt 32 63).toNat = 63 := by decide
    have h128 : (BitVec.ofInt 32 128).toNat = 128 := by decide
    have hs6 : (cp >>> (BitVec.ofInt 32 6)).toNat = cp.toNat / 64 := by
      show (cp >>> (6 : Nat)).toNat = cp.toNat / 64
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [hs6, h63, h128, show (63 : Nat) = 2^6 - 1 from by decide,
      and_two_pow_sub_one_eq_mod_clean, Nat.or_two_pow_eq_add_of_lt (n := 7) (by omega)]
  have hC : ((((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)) <<< (BitVec.ofInt 32 16)).toNat =
      (cp.toNat / 64 % 64 + 128) * 65536 := by
    show ((((cp >>> (BitVec.ofInt 32 6)) &&& (BitVec.ofInt 32 63)) |||
      (BitVec.ofInt 32 128)) <<< (16 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hb1]
  have hb2 : ((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)).toNat =
      cp.toNat % 64 + 128 := by
    rw [BitVec.toNat_or, BitVec.toNat_and]
    have h63 : (BitVec.ofInt 32 63).toNat = 63 := by decide
    have h128 : (BitVec.ofInt 32 128).toNat = 128 := by decide
    rw [h63, h128, show (63 : Nat) = 2^6 - 1 from by decide,
      and_two_pow_sub_one_eq_mod_clean, Nat.or_two_pow_eq_add_of_lt (n := 7) (by omega)]
  have hD : (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<<
      (BitVec.ofInt 32 24)).toNat = (cp.toNat % 64 + 128) * 2^24 := by
    show (((cp &&& (BitVec.ofInt 32 63)) ||| (BitVec.ofInt 32 128)) <<< (24 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hb2]
  have hE : (BitVec.ofInt 32 33008).toNat = 33008 := by decide
  rw [hA, hB, hC, hD, hE]
  have hA8 : cp.toNat / 262144 < 2^8 := by omega
  have hP1 : ((cp.toNat / 4096 % 64) * 256) % 2^8 = 0 := by
    rw [show (256 : Nat) = 2^8 from by decide]
    exact Nat.mul_mod_left _ _
  have hB14 : ((cp.toNat / 4096 % 64) * 256) < 2^14 := by omega
  have hC16 : ((cp.toNat / 64 % 64 + 128) * 65536) % 2^16 = 0 := by
    rw [show (65536 : Nat) = 2^16 from by decide]
    exact Nat.mul_mod_left _ _
  have hD24 : ((cp.toNat % 64 + 128) * 2^24) % 2^24 = 0 :=
    Nat.mul_mod_left _ _
  have hAB : (cp.toNat / 262144) ||| ((cp.toNat / 4096 % 64) * 256) =
      cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 :=
    Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hA8 hP1)
  have hAB16 : cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 < 2^16 := by omega
  have hABC : (cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256) |||
      ((cp.toNat / 64 % 64 + 128) * 65536) =
      cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
        (cp.toNat / 64 % 64 + 128) * 65536 :=
    Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hAB16 hC16)
  have hABC24 : cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
      (cp.toNat / 64 % 64 + 128) * 65536 < 2^24 := by omega
  have hABCD : (cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
      (cp.toNat / 64 % 64 + 128) * 65536) ||| ((cp.toNat % 64 + 128) * 2^24) =
      cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
        (cp.toNat / 64 % 64 + 128) * 65536 + (cp.toNat % 64 + 128) * 2^24 :=
    Nat.lor_eq_add_of_and_eq_zero _ _
      (and_eq_zero_of_lt_two_pow_of_mod hABC24 hD24)
  have hE3 : 33008 % 2^3 = 0 := by decide
  have hA_E : (cp.toNat / 262144) &&& 33008 = 0 :=
    and_eq_zero_of_lt_two_pow_of_mod (k := 3) (by omega) hE3
  have hB_E : ((cp.toNat / 4096 % 64) * 256) &&& 33008 = 0 := by
    rw [show (33008 : Nat) = 240 ||| 32768 from by decide, Nat.and_or_distrib_left]
    have h1 : ((cp.toNat / 4096 % 64) * 256) &&& 240 = 0 := by
      rw [Nat.and_comm]
      exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 240 < 2^8) hP1
    have h2 : ((cp.toNat / 4096 % 64) * 256) &&& 32768 = 0 :=
      and_eq_zero_of_lt_two_pow_of_mod (k := 14) hB14 (by decide)
    rw [h1, h2, Nat.zero_or]
  have hC_E : ((cp.toNat / 64 % 64 + 128) * 65536) &&& 33008 = 0 := by
    rw [Nat.and_comm]
    exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 33008 < 2^16) hC16
  have hD_E : ((cp.toNat % 64 + 128) * 2^24) &&& 33008 = 0 := by
    rw [Nat.and_comm]
    exact and_eq_zero_of_lt_two_pow_of_mod (by decide : 33008 < 2^24) hD24
  have hABCDE : (cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
      (cp.toNat / 64 % 64 + 128) * 65536 + (cp.toNat % 64 + 128) * 2^24) ||| 33008 =
      cp.toNat / 262144 + (cp.toNat / 4096 % 64) * 256 +
        (cp.toNat / 64 % 64 + 128) * 65536 + (cp.toNat % 64 + 128) * 2^24 + 33008 := by
    rw [← hABCD, ← hABC, ← hAB]
    refine Nat.lor_eq_add_of_and_eq_zero _ _ ?_
    exact and_or_zero (and_or_zero (and_or_zero hA_E hB_E) hC_E) hD_E
  rw [hAB, hABC, hABCD, hABCDE]
  rw [utf8Encode_eq_four (by omega) (by omega) h2]
  have hb0 : (UInt8.ofNat (0xF0 + cp.toNat / 0x40000)).toNat = 0xF0 + cp.toNat / 0x40000 :=
    toNat_ofNat_of_lt (by omega)
  have hb1' : (UInt8.ofNat (0x80 + cp.toNat / 0x1000 % 0x40)).toNat =
      0x80 + cp.toNat / 0x1000 % 0x40 := toNat_ofNat_of_lt (by omega)
  have hb2' : (UInt8.ofNat (0x80 + cp.toNat / 0x40 % 0x40)).toNat =
      0x80 + cp.toNat / 0x40 % 0x40 := toNat_ofNat_of_lt (by omega)
  have hb3' : (UInt8.ofNat (0x80 + cp.toNat % 0x40)).toNat = 0x80 + cp.toNat % 0x40 :=
    toNat_ofNat_of_lt (by omega)
  simp only [bytesToNat, hb0, hb1', hb2', hb3']
  omega




/-- **`hword`**: the store's word is the specification's UTF-8 encoding. -/
theorem udIfEnd32Word_toNat (cp : BitVec 32) (hcp : cp.toNat < 0x110000) :
    (udIfEnd32Word cp).toNat = bytesToNat (utf8Encode cp.toNat) := by
  by_cases h1 : cp.toNat < 0x80
  · exact udIfEnd32Word_toNat_lt80 cp h1
  · by_cases h2 : cp.toNat < 0x800
    · exact udIfEnd32Word_toNat_lt800 cp h1 h2
    · by_cases h3 : cp.toNat < 0x10000
      · exact udIfEnd32Word_toNat_lt10000 cp h2 h3
      · exact udIfEnd32Word_toNat_of_lt110000 cp h3 hcp


/-- A sixteen-bit unit masked to sixteen bits is itself. -/
theorem toNat_and65535 (x : BitVec 32) (h : x.toNat < 0x10000) :
    (x &&& BitVec.ofInt 32 65535).toNat = x.toNat := by
  rw [BitVec.toNat_and]
  have hc : (BitVec.ofInt 32 65535).toNat = 65535 := by decide
  rw [hc, show (65535 : Nat) = 2^16 - 1 from by decide,
    and_two_pow_sub_one_eq_mod_clean, Nat.mod_eq_of_lt (by omega)]

/-- **The high-surrogate range.**  `if.end3.i` tests `%21 = %vecext.i207 &&& 64512`
against `55296`; with the unit read as sixteen bits, that test is the range
`D800`–`DBFF` `surrogateTail`'s first guard clause names.

The sixteen-bit hypothesis is not decoration: the mask clears bits sixteen and
above, so without it a value `0x1D800` would satisfy the same equality.  The block
reads a code unit, which is what supplies the bound. -/
theorem udIfEnd3I_highSurrogate_iff (cp : BitVec 32) (hcp : cp.toNat < 0x10000) :
    evalICmp .eq (cp &&& BitVec.ofInt 32 64512) (BitVec.ofInt 32 55296) = (1 : BitVec 1) ↔
      0xD800 ≤ cp.toNat ∧ cp.toNat ≤ 0xDBFF := by
  rw [evalICmp_eq_one_iff]
  have h64512 : BitVec.ofInt 32 64512 = BitVec.ofNat 32 64512 := by decide
  have h55296 : BitVec.ofInt 32 55296 = BitVec.ofNat 32 55296 := by decide
  rw [h64512, h55296, BitVec.toNat_eq]
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : 64512 < 2^32),
    Nat.mod_eq_of_lt (by decide : 55296 < 2^32)]
  have h64512n : (64512 : Nat) = 63 * 2^10 := by decide
  have h55296n : (55296 : Nat) = 54 * 2^10 := by decide
  rw [h64512n, h55296n, and_mask_shift]
  have hmul : (((cp.toNat / 1024) &&& 63) * 1024 = 54 * 1024) ↔
      (((cp.toNat / 1024) &&& 63) = 54) := by
    constructor
    · intro h; exact Nat.mul_right_cancel (by decide : 0 < 1024) h
    · intro h; rw [h]
  rw [hmul]
  have h63 : (63 : Nat) = 2^6 - 1 := by decide
  rw [h63, and_two_pow_sub_one_eq_mod_clean,
    Nat.mod_eq_of_lt (by omega)]
  constructor
  · intro h
    have hdm : 1024 * (cp.toNat / 1024) + cp.toNat % 1024 = cp.toNat :=
      Nat.div_add_mod cp.toNat 1024
    rw [h] at hdm
    have hlt : cp.toNat % 1024 < 1024 := Nat.mod_lt cp.toNat (by decide : 0 < 1024)
    constructor
    · omega
    · omega
  · intro h
    exact Nat.div_eq_of_lt_le (by omega) (by omega)


/-- **The pair's value.**  `%add30.i` is `%sub23.i ||| %add28.i`: the second
unit's low ten bits below `0x10000 + (hi - D800) << 10`.  The two operands are
bit-disjoint, so `|||` is `+` and the word is the pair code point
`surrogateTail` returns.  `hi` and `lo` are the two masked code units; the
hypotheses are the two surrogate ranges. -/
theorem udIfThen26I_pairValue (hi lo : BitVec 32)
    (hhi : 0xD800 ≤ hi.toNat ∧ hi.toNat ≤ 0xDBFF)
    (hlo : 0xDC00 ≤ lo.toNat ∧ lo.toNat ≤ 0xDFFF) :
    ((((lo &&& BitVec.ofInt 32 65535) + BitVec.ofInt 32 (-56320)) |||
      (((hi &&& BitVec.ofInt 32 65535) <<< (BitVec.ofInt 32 10)) +
        BitVec.ofInt 32 (-56557568)))).toNat
      = 0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00) := by
  have hhi16 : hi.toNat < 0x10000 := by omega
  have hlo16 : lo.toNat < 0x10000 := by omega
  have hhim : (hi &&& BitVec.ofInt 32 65535).toNat = hi.toNat := toNat_and65535 hi hhi16
  have hlom : (lo &&& BitVec.ofInt 32 65535).toNat = lo.toNat := toNat_and65535 lo hlo16
  have hs23 : ((lo &&& BitVec.ofInt 32 65535) + BitVec.ofInt 32 (-56320)).toNat =
      lo.toNat - 0xDC00 := by
    rw [BitVec.toNat_add, hlom]
    have hc : (BitVec.ofInt 32 (-56320)).toNat = 2^32 - 56320 := by decide
    rw [hc]
    have h : lo.toNat + (2^32 - 56320) = 2^32 + (lo.toNat - 0xDC00) := by omega
    rw [h, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hsh : (((hi &&& BitVec.ofInt 32 65535) <<< (BitVec.ofInt 32 10))).toNat =
      hi.toNat * 1024 := by
    show ((hi &&& BitVec.ofInt 32 65535) <<< (10 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), hhim]
  have hhigh : (((hi &&& BitVec.ofInt 32 65535) <<< (BitVec.ofInt 32 10)) +
      BitVec.ofInt 32 (-56557568)).toNat = 0x10000 + (hi.toNat - 0xD800) * 1024 := by
    rw [BitVec.toNat_add, hsh]
    have hc : (BitVec.ofInt 32 (-56557568)).toNat = 2^32 - 56557568 := by decide
    rw [hc]
    have h : hi.toNat * 1024 + (2^32 - 56557568) =
        2^32 + (0x10000 + (hi.toNat - 0xD800) * 1024) := by omega
    rw [h, Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_or, hs23, hhigh]
  have hlow : lo.toNat - 0xDC00 < 2^10 := by omega
  have hmod : (0x10000 + (hi.toNat - 0xD800) * 1024) % 2^10 = 0 := by
    rw [Nat.add_mod, show (0x10000 : Nat) % 2^10 = 0 from by decide,
      Nat.mul_mod_left, Nat.zero_add, Nat.zero_mod]
  rw [Nat.lor_eq_add_of_and_eq_zero _ _
    (and_eq_zero_of_lt_two_pow_of_mod hlow hmod)]
  show lo.toNat - 0xDC00 + (0x10000 + (hi.toNat - 0xD800) * 1024) =
    0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00)
  omega



/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Vellum.udIfEnd32Word_toNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd32Word_toNat

/-- info: 'LeanLLVM.Vellum.udIfEnd3I_highSurrogate_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfEnd3I_highSurrogate_iff

/-- info: 'LeanLLVM.Vellum.udIfThen26I_pairValue' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms udIfThen26I_pairValue

end LeanLLVM.Vellum
