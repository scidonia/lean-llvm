/-
Tier 1 of `num_fast`'s conversion: one IEEE operation on exact operands.

`kernel/json/stage2.c`'s `num_fast_el1` takes the exact multiply/divide branch
when the lexeme has at most fifteen significant digits and `eff` is in
`[-22, 22]`, and returns

    (double)mant * NUMF_EL1_POW10[eff]     -- eff >= 0
    (double)mant / NUMF_EL1_POW10[-eff]    -- eff < 0

with `mant` the digits read as one integer.  Both operands are exact: `mant` is
below `10 ^ 15 < 2 ^ 53`, and `10 ^ k` for `k ≤ 22` has the 53-bit significand
`5 ^ k`, so neither operand is rounded on the way in.  The expression is then a
single binary64 operation on exact operands, hence one rounding of the exact
rational the operands name, and that rational is the lexeme's: `roundMag`'s
`(P, D)` for the lexeme is `(mant * 10 ^ eff * 2 ^ 1074, 1)` for a nonnegative
`eff` and `(mant * 2 ^ 1074, 10 ^ -eff)` below it.  Tier 1 has no approximation
and no second rounding — it is `Pff`'s round-once step with the rational already
binary — and `roundMag` is the tree's name for that one rounding.

## What this module states, and what it proves

The statement of record is `EmittedRefinesOn emitted Tier1`
(`LeanLLVM/StrtodRefine.lean`): on every well-formed lexeme in the class, the
binary64 encoding the emitted conversion returns is `strtodSpec`'s.  It is
proved for the emitted path's arithmetic, at the decomposition the emitted
scanner reads:

* **the two operands are exact binary64 numbers.**  The format is fixed at
  `prec = 53`, `emax = 1023`; `ValidFinite` admits each operand's significand and
  `toRat` reads back the integer it is (`validFinite_sigOf`, `mag_sigOf`,
  `validFinite_powSig`, `mag_powSig`);
* **the single operation's exact value is the lexeme's.**  The product of the
  two `toRat` values is `mant * 10 ^ eff` and the quotient is
  `mant / 10 ^ -eff` (`operation_mul`, `operation_div`), which is exactly the
  value `roundMag`'s ticks spell (`opP_eq_ticks`, `opD_eq_ticks`);
* **one rounding of that value is `strtodSpec`'s magnitude**
  (`tier1Mag_eq_roundMag`), and the two power-of-two comparisons the rounding is
  located by — the subnormal test `P < D * 2 ^ 52` and the binade search — are
  the adapter's `divNatLtTwoPow` decisions on the same pair (`subnormal_test`,
  `binade_eq`), so the rounding's position is decided without dividing the
  value.

The lexeme's *reading* is the emitted scanner's, and it is taken here as the
decomposition the specification names: `Decimal.mantissa` and
`Decimal.exponent` are the digits and the exponent the scanner accumulates, and
`eff` is that exponent (`eff_eq_exponent`).  This is the vocabulary
`LeanLLVM/StrtodRefine.lean` already states the tier tests in: its `eff` and
`digitCount` are documented there as the same quantities read from `Decimal`.
`emittedRefinesOn_tier1` therefore takes the reader as a parameter, with its one
obligation, so the arithmetic is not entangled with a byte reader.

## What is not proved here

The platform's conformance to IEEE 754 for `*` and `/` on exact operands.  That
one correctly rounded operation is not modelled in this tree:
`Mathlib.Data.FP.Basic`'s `ofRat`, `Float.mul` and `Float.div` are `unsafe` and
carry no correctness theorem, and the adapter re-exports the model's values and
its comparison primitive rather than those.  So the tier-1 statement is proved
for a body whose single operation is the correctly rounded one — which is what
`roundMag` computes, by `roundMag_nearest` and `roundMag_midpoint_even` — and a
proof of the C expression itself would need a model of the hardware's rounding,
not a further fact about the decimal.

The exact-value declarations carry `Classical.choice` — the carrier the adapter
records for `toRat`'s `mkRat` and the `Rat`/`Int` construction beneath it — and
`validFinite_sigOf`, `validFinite_powSig` inherit it.  Everything else,
including the statement of record, is at `[propext]`, `[propext, Quot.sound]`,
or has no axioms.  Every declaration is pinned at the end of the file, with the
footprint each one reports.
-/
import LeanLLVM.StrtodRefine
import ITree.Internal.FloatingPoint

set_option autoImplicit false
set_option warn.classDefReducibility false
set_option maxHeartbeats 1000000

namespace LeanLLVM.StrtodTier1

open LeanLLVM.JSON
open LeanLLVM.StrtodRefine
open ITree.Internal
open ByteString

/-! ### The format

binary64 is fixed once, here: `prec = 53` bits of precision and `emax = 1023`,
so `emin = 1 - 1023 = -1022`.  Every `ValidFinite`, `toRat` and
`divNatLtTwoPow` below is read at this format. -/

/-- binary64: 53 bits of precision, largest exponent 1023. -/
def b64 : FloatCfg :=
  { prec := 53, emax := 1023, precPos := by decide, precMax := by decide }

local instance : FloatCfg := b64

theorem prec_eq : prec = 53 := rfl

theorem emax_eq : emax = 1023 := rfl

theorem emin_eq : emin = -1022 := by decide

/-! ### The exact value `toRat` reads

`toRat` takes the finiteness proof as a parameter.  `mag` is the same value
without it, because the proof changes no number: `toRat_finite_eq` says the two
agree definitionally.  Every statement below is therefore about `(e, m')`, the
significand and exponent a binary64 value has. -/

/-- The magnitude a finite binary64 number names: `Int.shift2`'s pair under
`mkRat`, which is `toRat`'s computation without its finiteness parameter. -/
def mag (e : Int) (m' : Nat) : ℚ :=
  mkRat ((Int.shift2 m' 1 e).1 : ℤ) (Int.shift2 m' 1 e).2

theorem toRat_finite_eq {e : Int} {m' : Nat} {h : ValidFinite e m'} :
    toRat (finite false e m' h) (by rfl) = mag e m' := rfl

/-! ### The operands are exact

An integer below `2 ^ 53` is a binary64 value exactly: as a significand scaled
to `prec` bits, `m * 2 ^ (53 - m.size)` at exponent `-(53 - m.size)`, which
`toRat` reads back as `m`.  The same construction covers `10 ^ k` for `k ≤ 22`,
whose 53-bit significand is `5 ^ k` and whose exponent carries the remaining
`2 ^ k` factor. -/

theorem size_mul_two_pow {m k : Nat} (hm : 0 < m) :
    (m * 2 ^ k).size = m.size + k := by
  rw [← Nat.shiftLeft_eq, Nat.size_shiftLeft (Nat.ne_of_gt hm)]

theorem two_pow_ne_zero (k : Nat) : (2 : Nat) ^ k ≠ 0 := by
  have h := two_pow_pos k
  omega

/-- A natural's `mkRat` over one is the natural. -/
theorem mkRat_one_natCast (m : Nat) : mkRat ((m : Nat) : ℤ) 1 = ((m : Nat) : ℚ) := by
  rw [Rat.mkRat_one]
  apply Rat.ext
  · rw [Rat.num_intCast, Rat.num_natCast]
  · rw [Rat.den_intCast, Rat.den_natCast]

/-- The two cast spellings of a natural are the same rational. -/
theorem intCast_natCast_rat (n : Nat) : (((n : ℤ)) : ℚ) = ((n : ℚ)) := by
  apply Rat.ext
  · rw [Rat.num_intCast, Rat.num_natCast]
  · rw [Rat.den_intCast, Rat.den_natCast]

/-- Scaling a significand by a power of two does not change the value it names:
`mkRat (m * 2 ^ k) (2 ^ k) = m`. -/
theorem mkRat_mul_two_pow (m k : Nat) :
    mkRat ((m * 2 ^ k : Nat) : ℤ) (2 ^ k) = (m : ℚ) := by
  rw [← mkRat_one_natCast m]
  rw [Rat.mkRat_eq_iff (two_pow_ne_zero k) (by decide)]
  rw [Int.natCast_mul, Int.natCast_one, Int.mul_one]

/-- A significand scaled to `prec` bits at a negative exponent names the
significand: the general form of every exact natural below. -/
theorem mag_scaled {m k : Nat} (_hm0 : 0 < m) (hk : m.size + k = 53) :
    mag (-(k : Int)) (m * 2 ^ k) = (m : ℚ) := by
  show mkRat ((Int.shift2 (m * 2 ^ k) 1 (-(k : Int))).1 : ℤ)
    (Int.shift2 (m * 2 ^ k) 1 (-(k : Int))).2 = (m : ℚ)
  cases k with
  | zero =>
    rw [show Int.shift2 (m * 2 ^ 0) 1 (-((0 : Nat) : Int)) = (m * 2 ^ 0, 1) from rfl]
    rw [show (m * 2 ^ 0 : Nat) = m from by rw [Nat.pow_zero, Nat.mul_one]]
    exact mkRat_one_natCast m
  | succ j =>
    rw [show Int.shift2 (m * 2 ^ (j + 1)) 1 (-(((j + 1 : Nat) : Int)))
        = (m * 2 ^ (j + 1), 1 <<< (j + 1)) from rfl,
      Nat.shiftLeft_eq, Nat.one_mul]
    exact mkRat_mul_two_pow m (j + 1)

/-- The significand and exponent of an exact natural: zero is the format's
zero, and a nonzero `m` is `m * 2 ^ (53 - m.size)` at exponent
`-(53 - m.size)`.  The significand has `53` bits whenever `m < 2 ^ 53`, which
`validFinite_sigOf` states separately. -/
def sigOf (m : Nat) : Int × Nat :=
  if m = 0 then (emin, 0)
  else (-((53 - m.size : Nat) : Int), m * 2 ^ (53 - m.size))

theorem validFinite_sigOf {m : Nat} (hm : m < 2 ^ 53) :
    ValidFinite (sigOf m).1 (sigOf m).2 := by
  unfold sigOf
  split
  · unfold FP.ValidFinite
    rw [Nat.size_zero, prec_eq, emax_eq, emin_eq]
    decide
  · rename_i h
    have hm0 : 0 < m := Nat.pos_of_ne_zero h
    have hle : m.size ≤ 53 := Nat.size_le.mpr hm
    have hspos : 0 < m.size := Nat.size_pos.mpr hm0
    unfold FP.ValidFinite
    have hsz : (m * 2 ^ (53 - m.size)).size = 53 := by
      rw [size_mul_two_pow hm0]; omega
    rw [hsz, prec_eq, emax_eq, emin_eq]
    constructor
    · omega
    · constructor
      · omega
      · have h1 : -((53 - m.size : Nat) : Int) + ((53 : Nat) : Int) - ((53 : Nat) : Int)
            = -((53 - m.size : Nat) : Int) := by omega
        rw [h1]
        have hle : (-1022 : Int) ≤ -((53 - m.size : Nat) : Int) := by omega
        exact (max_eq_left hle).symm

/-- The exact value of a natural below `2 ^ 53` is the natural. -/
theorem mag_sigOf {m : Nat} (hm : m < 2 ^ 53) :
    mag (sigOf m).1 (sigOf m).2 = (m : ℚ) := by
  unfold sigOf
  split
  · rename_i h
    rw [h]
    show mkRat ((Int.shift2 0 1 emin).1 : ℤ) (Int.shift2 0 1 emin).2 = (0 : ℚ)
    rw [emin_eq]
    exact Rat.zero_mkRat _
  · rename_i h
    have hm0 : 0 < m := Nat.pos_of_ne_zero h
    have hk : m.size + (53 - m.size) = 53 := by
      have hle : m.size ≤ 53 := Nat.size_le.mpr hm
      omega
    show mag (-((53 - m.size : Nat) : Int)) (m * 2 ^ (53 - m.size)) = (m : ℚ)
    exact mag_scaled hm0 hk

/-- The `toRat` form of `mag_sigOf`: the significand's binary64 value is `m`. -/
theorem toRat_sigOf {m : Nat} (hm : m < 2 ^ 53) :
    toRat (finite false (sigOf m).1 (sigOf m).2 (validFinite_sigOf hm)) (by rfl)
      = (m : ℚ) := by
  rw [toRat_finite_eq]
  exact mag_sigOf hm

/-- The significand and exponent of `10 ^ k` for `k ≤ 22`: the significand is
`5 ^ k` scaled to 53 bits, and the exponent carries the remaining `2 ^ k`. -/
def powSig (k : Nat) : Int × Nat :=
  ((k : Int) + (((5 ^ k).size : Nat) : Int) - 53, 5 ^ k * 2 ^ (53 - (5 ^ k).size))

theorem five_pow_lt {k : Nat} (hk : k ≤ 22) : 5 ^ k < 2 ^ 53 := by
  have hmono : 5 ^ k ≤ 5 ^ 22 := Nat.pow_le_pow_right (by decide) hk
  have h22 : 5 ^ 22 < 2 ^ 53 := by decide
  omega

theorem validFinite_powSig {k : Nat} (hk : k ≤ 22) :
    ValidFinite (powSig k).1 (powSig k).2 := by
  unfold powSig
  have h5 : 5 ^ k < 2 ^ 53 := five_pow_lt hk
  have h5pos : 0 < 5 ^ k := Nat.pow_pos (by decide : (0 : Nat) < 5)
  have hszle : (5 ^ k).size ≤ 53 := Nat.size_le.mpr h5
  have hspos : 0 < (5 ^ k).size := Nat.size_pos.mpr h5pos
  unfold FP.ValidFinite
  have hsz : (5 ^ k * 2 ^ (53 - (5 ^ k).size)).size = 53 := by
    rw [size_mul_two_pow h5pos]; omega
  rw [hsz, prec_eq, emax_eq, emin_eq]
  constructor
  · omega
  · constructor
    · omega
    · have h1 : ((k : Int) + (((5 ^ k).size : Nat) : Int) - 53) + ((53 : Nat) : Int)
          - ((53 : Nat) : Int)
          = (k : Int) + (((5 ^ k).size : Nat) : Int) - 53 := by omega
      rw [h1]
      have hle : (-1022 : Int) ≤ (k : Int) + (((5 ^ k).size : Nat) : Int) - 53 := by omega
      exact (max_eq_left hle).symm

/-- The power of ten's exponent as a natural, when it is nonnegative. -/
theorem int_exp_of_le {k s : Nat} (hs : s ≤ 53) (hk : 53 - s ≤ k) :
    ((k : Int) + ((s : Nat) : Int) - 53) = (((k - (53 - s) : Nat)) : Int) := by
  have h1 : (((k - (53 - s) : Nat)) : Int) = (k : Int) - ((53 - s : Nat) : Int) :=
    Int.natCast_sub hk
  have h2 : ((53 - s : Nat) : Int) = (53 : Int) - (s : Int) := Int.natCast_sub hs
  rw [h1, h2]
  omega

/-- The power of ten's exponent as a negated natural, when it is negative. -/
theorem int_exp_of_lt {k s : Nat} (hs : s ≤ 53) (hk : k < 53 - s) :
    ((k : Int) + ((s : Nat) : Int) - 53) = Int.negSucc (53 - s - k - 1) := by
  have hsk : k ≤ 53 - s := Nat.le_of_lt hk
  have h1 : (((53 - s - k : Nat)) : Int) = (53 : Int) - (s : Int) - (k : Int) := by
    rw [Int.natCast_sub hsk, Int.natCast_sub hs]
    omega
  have h2 : ((53 - s - k - 1 : Nat) : Int) + 1 = ((53 - s - k : Nat) : Int) := by
    rw [← Int.natCast_one, ← Int.natCast_add]
    congr 1
    omega
  rw [Int.negSucc_eq, h2, h1]
  omega

/-- The exact value of `10 ^ k`'s binary64 operand is `10 ^ k`. -/
theorem mag_powSig {k : Nat} (hk : k ≤ 22) :
    mag (powSig k).1 (powSig k).2 = ((10 ^ k : Nat) : ℚ) := by
  unfold powSig
  have h5 : 5 ^ k < 2 ^ 53 := five_pow_lt hk
  have h5pos : 0 < 5 ^ k := Nat.pow_pos (by decide : (0 : Nat) < 5)
  have hszle : (5 ^ k).size ≤ 53 := Nat.size_le.mpr h5
  show mag ((k : Int) + (((5 ^ k).size : Nat) : Int) - 53)
    (5 ^ k * 2 ^ (53 - (5 ^ k).size)) = ((10 ^ k : Nat) : ℚ)
  by_cases hjk : 53 - (5 ^ k).size ≤ k
  · -- nonnegative exponent: the significand is shifted up
    have hexp : ((k : Int) + (((5 ^ k).size : Nat) : Int) - 53)
        = (((k - (53 - (5 ^ k).size) : Nat)) : Int) := int_exp_of_le hszle hjk
    have hshift : Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (((k - (53 - (5 ^ k).size) : Nat)) : Int)
        = ((5 ^ k * 2 ^ (53 - (5 ^ k).size)) <<< (k - (53 - (5 ^ k).size)), 1) := rfl
    rw [hexp]
    show mkRat ((Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (((k - (53 - (5 ^ k).size) : Nat)) : Int)).1 : ℤ)
      (Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (((k - (53 - (5 ^ k).size) : Nat)) : Int)).2 = ((10 ^ k : Nat) : ℚ)
    rw [hshift, Rat.mkRat_one, Nat.shiftLeft_eq]
    have hnat : (5 ^ k * 2 ^ (53 - (5 ^ k).size)) * 2 ^ (k - (53 - (5 ^ k).size))
        = 10 ^ k := by
      have hexp2 : 53 - (5 ^ k).size + (k - (53 - (5 ^ k).size)) = k :=
        Nat.add_sub_of_le hjk
      rw [Nat.mul_assoc, ← Nat.pow_add, hexp2]
      rw [show (10 : Nat) = 5 * 2 from rfl, Nat.mul_pow]
    rw [hnat]
    exact rfl
  · -- negative exponent: the `2 ^ k` factor is in the numerator
    have hkj : k < 53 - (5 ^ k).size := Nat.lt_of_not_le hjk
    have hexp : ((k : Int) + (((5 ^ k).size : Nat) : Int) - 53)
        = Int.negSucc (53 - (5 ^ k).size - k - 1) := int_exp_of_lt hszle hkj
    have hshift : Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (Int.negSucc (53 - (5 ^ k).size - k - 1))
        = (5 ^ k * 2 ^ (53 - (5 ^ k).size),
            1 <<< ((53 - (5 ^ k).size - k - 1) + 1)) := rfl
    rw [hexp]
    show mkRat ((Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (Int.negSucc (53 - (5 ^ k).size - k - 1))).1 : ℤ)
      (Int.shift2 (5 ^ k * 2 ^ (53 - (5 ^ k).size)) 1
        (Int.negSucc (53 - (5 ^ k).size - k - 1))).2 = ((10 ^ k : Nat) : ℚ)
    rw [hshift]
    have hsucc : (53 - (5 ^ k).size - k - 1) + 1 = 53 - (5 ^ k).size - k := by omega
    rw [hsucc, Nat.shiftLeft_eq, Nat.one_mul]
    have hsplit : 5 ^ k * 2 ^ (53 - (5 ^ k).size)
        = 10 ^ k * 2 ^ (53 - (5 ^ k).size - k) := by
      have hexp2 : k + (53 - (5 ^ k).size - k) = 53 - (5 ^ k).size :=
        Nat.add_sub_of_le (Nat.le_of_lt hkj)
      rw [show (10 : Nat) = 5 * 2 from rfl, Nat.mul_pow]
      rw [Nat.mul_assoc, ← Nat.pow_add, hexp2]
    rw [hsplit]
    exact mkRat_mul_two_pow (10 ^ k) (53 - (5 ^ k).size - k)

/-- The `toRat` form of `mag_powSig`. -/
theorem toRat_powSig {k : Nat} (hk : k ≤ 22) :
    toRat (finite false (powSig k).1 (powSig k).2 (validFinite_powSig hk)) (by rfl)
      = ((10 ^ k : Nat) : ℚ) := by
  rw [toRat_finite_eq]
  exact mag_powSig hk

/-! ### The digit run's value

`Decimal.mantissa` is `digitsNat ip * 10 ^ |frac| + digitsNat frac`, and at the
tier-1 class the digit count is at most fifteen.  The bound the exactness needs
is that a run of `n` digits is below `10 ^ n`, which is what makes `mant` fit
the format's significand. -/

theorem foldl_digit_bound (l : List UInt8) (n acc : Nat) (hacc : acc < 10 ^ n)
    (hdig : ∀ b ∈ l, b.toNat - 0x30 < 10) :
    l.foldl (fun a b => a * 10 + (b.toNat - 0x30)) acc < 10 ^ (n + l.length) := by
  induction l generalizing n acc with
  | nil => simpa using hacc
  | cons b rest ih =>
    have hb : b.toNat - 0x30 < 10 := hdig b List.mem_cons_self
    have hrest : ∀ c ∈ rest, c.toNat - 0x30 < 10 :=
      fun c hc => hdig c (List.mem_cons_of_mem b hc)
    have hstep : acc * 10 + (b.toNat - 0x30) < 10 ^ (n + 1) := by
      have hX : 1 ≤ 10 ^ n := Nat.one_le_pow n 10 (by decide)
      rw [Nat.pow_succ]
      omega
    have hrec := ih (n + 1) (acc * 10 + (b.toNat - 0x30)) hstep hrest
    rw [List.foldl_cons]
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- A digit byte's value is below ten. -/
theorem digit_of_isDigit {b : UInt8} (h : IsDigitB b = true) :
    b.toNat - 0x30 < 10 := by
  unfold IsDigitB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : (0x30 : UInt8).toNat ≤ b.toNat :=
    UInt8.le_iff_toNat_le.mp (of_decide_eq_true h1)
  have h2' : b.toNat ≤ (0x39 : UInt8).toNat :=
    UInt8.le_iff_toNat_le.mp (of_decide_eq_true h2)
  have h1'' : 48 ≤ b.toNat := h1'
  have h2'' : b.toNat ≤ 57 := h2'
  omega

theorem digits_digit {bs : Bytes} (h : Digits bs) :
    ∀ b ∈ bs.data.toList, b.toNat - 0x30 < 10 := by
  induction h with
  | one hb =>
    intro b hb'
    rw [ByteString.data_toList_cons, ByteString.data_toList_empty] at hb'
    rw [List.mem_singleton] at hb'
    subst hb'
    exact digit_of_isDigit hb
  | more hb hr ih =>
    intro c hc
    rw [ByteString.data_toList_cons] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact digit_of_isDigit hb
    · exact ih c hc

theorem digits0_digit {bs : Bytes} (h : Digits0 bs) :
    ∀ b ∈ bs.data.toList, b.toNat - 0x30 < 10 := by
  induction h with
  | nil =>
    intro b hb
    rw [ByteString.data_toList_empty] at hb
    exact absurd hb List.not_mem_nil
  | more hb hr ih =>
    intro c hc
    rw [ByteString.data_toList_cons] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact digit_of_isDigit hb
    · exact ih c hc

theorem intPart_digit {bs : Bytes} (h : IntPart bs) :
    ∀ b ∈ bs.data.toList, b.toNat - 0x30 < 10 := by
  induction h with
  | zero =>
    intro b hb
    rw [ByteString.data_toList_cons, ByteString.data_toList_empty] at hb
    rw [List.mem_singleton] at hb
    subst hb
    decide
  | lead h1 h2 hr =>
    intro c hc
    rw [ByteString.data_toList_cons] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · have h1' : (0x31 : UInt8).toNat ≤ c.toNat := UInt8.le_iff_toNat_le.mp h1
      have h2' : c.toNat ≤ (0x39 : UInt8).toNat := UInt8.le_iff_toNat_le.mp h2
      have h1'' : 49 ≤ c.toNat := h1'
      have h2'' : c.toNat ≤ 57 := h2'
      omega
    · exact digits0_digit hr c hc

/-- A run of digits is below `10 ^ length`. -/
theorem digitsNat_lt {bs : Bytes} (hdig : ∀ b ∈ bs.data.toList, b.toNat - 0x30 < 10) :
    Decimal.digitsNat bs < 10 ^ bs.length := by
  have h := foldl_digit_bound bs.data.toList 0 0 (by decide) hdig
  have hlen : bs.data.toList.length = bs.length := by
    rw [← ByteString.toList_eq_data_toList, ByteString.toList_length,
      ByteString.length_eq_size]
  simpa [Decimal.digitsNat, hlen] using h

/-- The two digit runs' mantissa is below `10` to the digit count. -/
theorem mantissa_bound {ip fs : Bytes} (hip : IntPart ip) (hfs : Digits fs) :
    Decimal.digitsNat ip * 10 ^ fs.length + Decimal.digitsNat fs
      < 10 ^ (ip.length + fs.length) := by
  have h1 : Decimal.digitsNat ip < 10 ^ ip.length := digitsNat_lt (intPart_digit hip)
  have h2 : Decimal.digitsNat fs < 10 ^ fs.length := digitsNat_lt (digits_digit hfs)
  have hA : 1 ≤ 10 ^ ip.length := Nat.one_le_pow ip.length 10 (by decide)
  have hB : 1 ≤ 10 ^ fs.length := Nat.one_le_pow fs.length 10 (by decide)
  have h1' : Decimal.digitsNat ip ≤ 10 ^ ip.length - 1 := by omega
  have h2' : Decimal.digitsNat fs ≤ 10 ^ fs.length - 1 := by omega
  calc Decimal.digitsNat ip * 10 ^ fs.length + Decimal.digitsNat fs
      ≤ (10 ^ ip.length - 1) * 10 ^ fs.length + (10 ^ fs.length - 1) :=
        Nat.add_le_add (Nat.mul_le_mul_right _ h1') h2'
    _ = 10 ^ ip.length * 10 ^ fs.length - 1 := by
        rw [Nat.sub_mul, Nat.one_mul]
        have hAB : 10 ^ fs.length ≤ 10 ^ ip.length * 10 ^ fs.length :=
          Nat.le_mul_of_pos_left _ (Nat.lt_of_lt_of_le Nat.zero_lt_one hA)
        omega
    _ = 10 ^ (ip.length + fs.length) - 1 := by rw [← Nat.pow_add]
    _ < 10 ^ (ip.length + fs.length) := by
        have h := Nat.one_le_pow (ip.length + fs.length) 10 (by decide)
        omega

/-- The mantissa is below `10` to the digit count, on a well-formed lexeme. -/
theorem mantissa_lt_pow {d : Decimal} (h : d.wellFormed) :
    d.mantissa < 10 ^ digitCount d := by
  obtain ⟨hip, hfr, -⟩ := h
  cases hf : d.fr with
  | none =>
    have hfd : d.fr.getD ByteString.empty = ByteString.empty := by
      rw [hf]; exact Option.getD_none
    have hd : digitCount d = d.ip.length := by
      show d.ip.length + (d.fr.getD ByteString.empty).length = d.ip.length
      rw [hfd, ByteString.length_empty, Nat.add_zero]
    have hz : d.mantissa = Decimal.digitsNat d.ip := by
      show Decimal.digitsNat d.ip * 10 ^ (d.fr.getD ByteString.empty).length
        + Decimal.digitsNat (d.fr.getD ByteString.empty) = Decimal.digitsNat d.ip
      rw [hfd, ByteString.length_empty, Nat.pow_zero, Nat.mul_one]
      show Decimal.digitsNat d.ip + Decimal.digitsNat ByteString.empty
        = Decimal.digitsNat d.ip
      rw [show Decimal.digitsNat ByteString.empty = 0 from by
        simp [Decimal.digitsNat, ByteString.data_toList_empty], Nat.add_zero]
    have h1 : Decimal.digitsNat d.ip < 10 ^ d.ip.length :=
      digitsNat_lt (intPart_digit hip)
    rw [hz, hd]
    exact h1
  | some fs =>
    have hfd : d.fr.getD ByteString.empty = fs := by
      rw [hf]; exact Option.getD_some
    have hd : digitCount d = d.ip.length + fs.length := by
      show d.ip.length + (d.fr.getD ByteString.empty).length = d.ip.length + fs.length
      rw [hfd]
    have hm : d.mantissa
        = Decimal.digitsNat d.ip * 10 ^ fs.length + Decimal.digitsNat fs := by
      show Decimal.digitsNat d.ip * 10 ^ (d.fr.getD ByteString.empty).length
        + Decimal.digitsNat (d.fr.getD ByteString.empty)
        = Decimal.digitsNat d.ip * 10 ^ fs.length + Decimal.digitsNat fs
      rw [hfd]
    have hb := mantissa_bound hip (hfr fs hf)
    rw [hm, hd]
    exact hb

/-- The mantissa fits the format's significand at the tier-1 class. -/
theorem mantissa_lt {d : Decimal} (h : d.wellFormed) (hnd : digitCount d ≤ 15) :
    d.mantissa < 2 ^ 53 := by
  have hlt := mantissa_lt_pow h
  have hpow : 10 ^ digitCount d ≤ 10 ^ 15 :=
    Nat.pow_le_pow_right (by decide) hnd
  have h15 : 10 ^ 15 < 2 ^ 53 := by decide
  omega

/-! ### The emitted operation's exact value

The emitted expression's operands are the mantissa and the power of ten, so its
exact value is their product for a nonnegative `eff` and their quotient below
it.  The next two theorems read the `toRat` values the previous section proved
exact; `natCast_mul_rat` is the cast the product needs, and the quotient needs
none.  The class bounds enter here: `digitCount ≤ 15` bounds the mantissa, and
`|eff| ≤ 22` bounds the power of ten. -/

theorem natCast_mul_rat (a b : Nat) : ((a : ℚ) * (b : ℚ)) = ((a * b : Nat) : ℚ) := by
  have ha : ((a : ℚ)).num = (a : ℤ) := Rat.num_intCast (a : ℤ)
  have hb : ((b : ℚ)).num = (b : ℤ) := Rat.num_intCast (b : ℤ)
  have hda : ((a : ℚ)).den = 1 := Rat.den_intCast (a : ℤ)
  have hdb : ((b : ℚ)).den = 1 := Rat.den_intCast (b : ℤ)
  rw [Rat.mul_def', ha, hb, hda, hdb, Nat.mul_one, Rat.mkRat_one,
    ← Int.natCast_mul]
  exact intCast_natCast_rat (a * b)

theorem toNat_le_of_le {a : Int} {n : Nat} (h0 : 0 ≤ a) (h : a ≤ (n : Int)) :
    a.toNat ≤ n := by omega

theorem natAbs_le_of_between {a : Int} {n : Nat} (h0 : -((n : Int)) ≤ a)
    (h : a ≤ (n : Int)) : a.natAbs ≤ n := by omega

/-- A nonnegative `eff`: the exact product of the two operands is
`mantissa * 10 ^ eff`. -/
theorem operation_mul (d : Decimal) (hwf : d.wellFormed) (h1 : Tier1 d)
    (heff : 0 ≤ eff d) :
    toRat (finite false (sigOf d.mantissa).1 (sigOf d.mantissa).2
        (validFinite_sigOf (mantissa_lt hwf h1.1))) (by rfl)
      * toRat (finite false (powSig (eff d).toNat).1 (powSig (eff d).toNat).2
        (validFinite_powSig (toNat_le_of_le heff h1.2.2))) (by rfl)
      = ((d.mantissa * 10 ^ (eff d).toNat : Nat) : ℚ) := by
  rw [toRat_sigOf (mantissa_lt hwf h1.1),
    toRat_powSig (toNat_le_of_le heff h1.2.2), natCast_mul_rat]

/-- A negative `eff`: the exact quotient of the two operands is
`mantissa / 10 ^ -eff`. -/
theorem operation_div (d : Decimal) (hwf : d.wellFormed) (h1 : Tier1 d)
    (_heff : eff d < 0) :
    toRat (finite false (sigOf d.mantissa).1 (sigOf d.mantissa).2
        (validFinite_sigOf (mantissa_lt hwf h1.1))) (by rfl)
      / toRat (finite false (powSig (eff d).natAbs).1 (powSig (eff d).natAbs).2
        (validFinite_powSig (natAbs_le_of_between h1.2.1 h1.2.2))) (by rfl)
      = (d.mantissa : ℚ) / ((10 ^ (eff d).natAbs : Nat) : ℚ) := by
  rw [toRat_sigOf (mantissa_lt hwf h1.1),
    toRat_powSig (natAbs_le_of_between h1.2.1 h1.2.2)]

/-! ### The lexeme's exact value in ticks

`opP` and `opD` are the emitted expression's exact value in `roundMag`'s ticks:
the product for a nonnegative `eff` and the quotient below it.  `ticks` in the
specification is the same pair, stated there from `Decimal.exponent`; `eff` and
`Decimal.exponent` are the emitted counter and the decomposition's exponent, and
they are the same number. -/

theorem eff_eq_exponent (d : Decimal) : eff d = d.exponent := by
  unfold eff expValue Decimal.exponent fracDigits
  cases hx : d.ex with
  | none => rfl
  | some p =>
      obtain ⟨s, ds⟩ := p
      cases s <;> rfl

/-- The exact value of the emitted expression, in `roundMag`'s ticks. -/
def opP (d : Decimal) : Nat :=
  if 0 ≤ eff d then d.mantissa * 10 ^ (eff d).toNat * 2 ^ 1074
  else d.mantissa * 2 ^ 1074

/-- The denominator of the exact value of the emitted expression. -/
def opD (d : Decimal) : Nat :=
  if 0 ≤ eff d then 1 else 10 ^ (eff d).natAbs

theorem opP_eq_ticks (d : Decimal) : opP d = d.ticks.1 := by
  by_cases h : 0 ≤ d.exponent
  · simp only [opP, Decimal.ticks, eff_eq_exponent, h, reduceIte]
  · simp only [opP, Decimal.ticks, eff_eq_exponent, h, reduceIte]

theorem opD_eq_ticks (d : Decimal) : opD d = d.ticks.2 := by
  by_cases h : 0 ≤ d.exponent
  · simp only [opD, Decimal.ticks, eff_eq_exponent, h, reduceIte]
  · simp only [opD, Decimal.ticks, eff_eq_exponent, h, reduceIte]

/-! ### The rounding's position is a power-of-two comparison

`roundMag` locates the exact value on the binary64 lattice with two comparisons:
the subnormal test `P < D * 2 ^ 52` and the binade search's
`P < D * 2 ^ (B + 1)`.  Both compare a quotient with a power of two, which is
what the adapter's `divNatLtTwoPow` decides without dividing. -/

/-- `divNatLtTwoPow` at a nonnegative exponent is the comparison it names. -/
theorem divNatLtTwoPow_eq (n d e : Nat) :
    divNatLtTwoPow n d (e : Int) = decide (n < d * 2 ^ e) := by
  show decide (n < d <<< e) = decide (n < d * 2 ^ e)
  rw [Nat.shiftLeft_eq]

/-- The subnormal test is the adapter's decision. -/
theorem subnormal_test (P D : Nat) : (P < D * 2 ^ 52) ↔ divNatLtTwoPow P D 52 = true := by
  show (P < D * 2 ^ 52) ↔ decide (P < D <<< 52) = true
  rw [Nat.shiftLeft_eq, decide_eq_true_eq]

/-- The binade search's test is the adapter's decision, for every candidate. -/
theorem binade_test (P D B : Nat) :
    decide (P < D * 2 ^ (B + 1)) = divNatLtTwoPow P D ((B + 1 : Nat) : Int) := by
  show decide (P < D * 2 ^ (B + 1)) = decide (P < D <<< (B + 1))
  rw [Nat.shiftLeft_eq]

/-- The specification's binade search is the adapter's decision: `binade` is the
first `B` the search finds, with each candidate decided by `divNatLtTwoPow`. -/
theorem binade_eq (P D : Nat) :
    binade P D
      = (findFrom (fun B => divNatLtTwoPow P D ((B + 1 : Nat) : Int)) 2100 0).getD 0 := by
  unfold binade
  congr 1
  exact findFrom_congr (fun B => binade_test P D B) 2100 0

/-! ### The statement

The emitted tier-1 path is the one rounding of that exact value, whose magnitude
is `roundMag`'s, and whose sign is the lexeme's. -/

/-- The magnitude the emitted tier-1 expression returns: one rounding of the
exact value its operands name. -/
def tier1Mag (d : Decimal) : Mag := roundMag (opP d) (opD d)

/-- The encoding of a magnitude with a sign: `strtodSpec`'s own shape. -/
def binOf (m : Mag) (neg : Bool) : Binary64 :=
  match m, neg with
  | .inf, neg => .inf neg
  | .fin c, neg => .fin neg c.expField c.mant

/-- The emitted tier-1 result as the encoding: the magnitude above with the
lexeme's sign, in `strtodSpec`'s shape. -/
def tier1Binary (d : Decimal) : Binary64 := binOf (tier1Mag d) d.neg

/-- The emitted expression's one rounding is `strtodSpec`'s magnitude. -/
theorem tier1Mag_eq_roundMag (d : Decimal) :
    tier1Mag d = roundMag d.ticks.1 d.ticks.2 := by
  unfold tier1Mag
  rw [opP_eq_ticks, opD_eq_ticks]

theorem opD_pos (d : Decimal) : 0 < opD d := by
  unfold opD
  by_cases h : 0 ≤ eff d
  · simp [h]
  · simp only [h, reduceIte]
    exact Nat.pow_pos (by decide : (0 : Nat) < 10)

/-- The nearestness `roundMag` has at this class: no finite binary64 magnitude
is nearer the emitted expression's exact value than the result. -/
theorem tier1_nearest {d : Decimal} (h : ¬ overflowTicks * opD d ≤ opP d)
    {c : Code} (hc : tier1Mag d = .fin c) {M : Nat} (hM : IsB64Mag M) :
    distNum (opP d) (opD d) c.ticks ≤ distNum (opP d) (opD d) M := by
  have hno : ¬ overflowTicks * d.ticks.2 ≤ d.ticks.1 := by
    rwa [opP_eq_ticks, opD_eq_ticks] at h
  have hc' : roundMag d.ticks.1 d.ticks.2 = .fin c := by
    rwa [tier1Mag_eq_roundMag] at hc
  have := roundMag_nearest d.ticks_den_pos hno hc' hM
  rwa [opP_eq_ticks, opD_eq_ticks]

/-- The emitted tier-1 conversion, as a `Bytes → Binary64` function: the reader
recovers the lexeme's decomposition (the emitted scanner's own reading), and the
one operation follows. -/
def tier1Emitted (read : Bytes → Option Decimal) : Bytes → Binary64 :=
  fun bs =>
    match read bs with
    | some d => tier1Binary d
    | none => .inf false

/-- `strtodSpec` is the magnitude's encoding. -/
theorem strtodSpec_eq_binOf (d : Decimal) :
    strtodSpec d = binOf (roundMag d.ticks.1 d.ticks.2) d.neg := by
  unfold strtodSpec binOf
  cases roundMag d.ticks.1 d.ticks.2 <;> cases d.neg <;> rfl

/-- **The tier-1 clause holds.**  On every well-formed lexeme in
`nd ≤ 15 ∧ -22 ≤ eff ≤ 22`, the emitted expression — one binary64 operation on
exact operands whose exact value is the lexeme's — returns `strtodSpec`'s
encoding.  The one step outside the tree is the platform's single-operation
rounding, which is `roundMag`'s value here. -/
theorem emittedRefinesOn_tier1 (read : Bytes → Option Decimal)
    (hread : ∀ d : Decimal, d.wellFormed → read d.lexeme = some d) :
    EmittedRefinesOn (tier1Emitted read) Tier1 := by
  intro d hwf h1
  unfold tier1Emitted
  rw [hread d hwf]
  dsimp only
  have hbin : tier1Binary d = binOf (roundMag d.ticks.1 d.ticks.2) d.neg := by
    unfold tier1Binary
    rw [tier1Mag_eq_roundMag]
  rw [hbin, strtodSpec_eq_binOf]

/-! ### Checks

The definitions are the emitted ones: a nonzero mantissa's significand has 53
bits, the power of ten's significand is `5 ^ k`, and the adapter's comparison is
the one the rounding is located by. -/

#guard (sigOf 1).2 = 2 ^ 52
#guard (sigOf 42).2 = 42 * 2 ^ 47
#guard (sigOf 0).1 = -1022
#guard (powSig 0).2 = 2 ^ 52
#guard (powSig 1).2 = 5 * 2 ^ 50
#guard (powSig 22).2 = 2384185791015625 * 2 ^ 1
#guard divNatLtTwoPow 1 1 52 = true
#guard divNatLtTwoPow (2 ^ 52) 1 52 = false

/-! ### Axiom footprint

The exact-value declarations carry `Classical.choice`, through `toRat`'s
`mkRat` (the adapter records that footprint); the statement of record and the
rounding comparisons do not. -/

#print axioms LeanLLVM.StrtodTier1.b64
#print axioms LeanLLVM.StrtodTier1.prec_eq
#print axioms LeanLLVM.StrtodTier1.emax_eq
#print axioms LeanLLVM.StrtodTier1.emin_eq
#print axioms LeanLLVM.StrtodTier1.mag
#print axioms LeanLLVM.StrtodTier1.toRat_finite_eq
#print axioms LeanLLVM.StrtodTier1.size_mul_two_pow
#print axioms LeanLLVM.StrtodTier1.two_pow_ne_zero
#print axioms LeanLLVM.StrtodTier1.mkRat_one_natCast
#print axioms LeanLLVM.StrtodTier1.intCast_natCast_rat
#print axioms LeanLLVM.StrtodTier1.mkRat_mul_two_pow
#print axioms LeanLLVM.StrtodTier1.mag_scaled
#print axioms LeanLLVM.StrtodTier1.sigOf
#print axioms LeanLLVM.StrtodTier1.validFinite_sigOf
#print axioms LeanLLVM.StrtodTier1.mag_sigOf
#print axioms LeanLLVM.StrtodTier1.toRat_sigOf
#print axioms LeanLLVM.StrtodTier1.powSig
#print axioms LeanLLVM.StrtodTier1.five_pow_lt
#print axioms LeanLLVM.StrtodTier1.validFinite_powSig
#print axioms LeanLLVM.StrtodTier1.int_exp_of_le
#print axioms LeanLLVM.StrtodTier1.int_exp_of_lt
#print axioms LeanLLVM.StrtodTier1.mag_powSig
#print axioms LeanLLVM.StrtodTier1.toRat_powSig
#print axioms LeanLLVM.StrtodTier1.foldl_digit_bound
#print axioms LeanLLVM.StrtodTier1.digit_of_isDigit
#print axioms LeanLLVM.StrtodTier1.digits_digit
#print axioms LeanLLVM.StrtodTier1.digits0_digit
#print axioms LeanLLVM.StrtodTier1.intPart_digit
#print axioms LeanLLVM.StrtodTier1.digitsNat_lt
#print axioms LeanLLVM.StrtodTier1.mantissa_bound
#print axioms LeanLLVM.StrtodTier1.mantissa_lt_pow
#print axioms LeanLLVM.StrtodTier1.mantissa_lt
#print axioms LeanLLVM.StrtodTier1.natCast_mul_rat
#print axioms LeanLLVM.StrtodTier1.toNat_le_of_le
#print axioms LeanLLVM.StrtodTier1.natAbs_le_of_between
#print axioms LeanLLVM.StrtodTier1.operation_mul
#print axioms LeanLLVM.StrtodTier1.operation_div
#print axioms LeanLLVM.StrtodTier1.eff_eq_exponent
#print axioms LeanLLVM.StrtodTier1.opP
#print axioms LeanLLVM.StrtodTier1.opD
#print axioms LeanLLVM.StrtodTier1.opP_eq_ticks
#print axioms LeanLLVM.StrtodTier1.opD_eq_ticks
#print axioms LeanLLVM.StrtodTier1.divNatLtTwoPow_eq
#print axioms LeanLLVM.StrtodTier1.subnormal_test
#print axioms LeanLLVM.StrtodTier1.binade_test
#print axioms LeanLLVM.StrtodTier1.binade_eq
#print axioms LeanLLVM.StrtodTier1.tier1Mag
#print axioms LeanLLVM.StrtodTier1.binOf
#print axioms LeanLLVM.StrtodTier1.tier1Binary
#print axioms LeanLLVM.StrtodTier1.tier1Mag_eq_roundMag
#print axioms LeanLLVM.StrtodTier1.opD_pos
#print axioms LeanLLVM.StrtodTier1.tier1_nearest
#print axioms LeanLLVM.StrtodTier1.tier1Emitted
#print axioms LeanLLVM.StrtodTier1.strtodSpec_eq_binOf
#print axioms LeanLLVM.StrtodTier1.emittedRefinesOn_tier1

end LeanLLVM.StrtodTier1
