/-
Tier 3 of `num_fast`'s conversion: the sticky window.

`kernel/json/stage2.c`'s `to_double` is the conversion every lexeme the first
two tiers decline reaches.  It reads at most 768 significant digits into a
bounded window, keeps one bit saying whether any digit past the window is
nonzero, clamps two magnitude classes, and otherwise rounds once, nearest with
ties to even, from three values: the retained digits `M`, the weight of `M`'s
last digit `10 ^ S`, and the sticky bit.  Its correctness is an obligation of
this tree rather than a property of a platform conversion; the design comment
is `kernel/json/stage2.c:457-531`, and this module is the model of that path.

## The four facts the obligation rests on

1. **The retained window suffices.**  A rounding decision compares the value
   with a binary64 value or with the midpoint of two adjacent ones, and every
   such boundary is `J * 2 ^ e` with `J < 2 ^ 54` and `e >= -1075`.  Written
   over `10 ^ 1075` it is `J * 5 ^ 1075 * 2 ^ (e + 1075)`, and
   `(2 ^ 54 - 1) * 5 ^ 1075 < 10 ^ 768` (`log10 ((2 ^ 54 - 1) * 5 ^ 1075) =
   767.65`), so the boundary's decimal expansion has at most 768 significant
   digits and is represented exactly inside the window.  `boundary_num_lt`
   proves the fractional bound, `boundary_int_lt` the same bound for the
   boundaries that are integer multiples of a power of two above one, and
   `overflowTicks_eq` reads `roundMag`'s own overflow threshold as the
   boundary `(2 ^ 54 - 1) * 2 ^ 970`.

2. **The sticky bit is enough.**  A nonzero tail puts the value strictly
   between two consecutive retained decimals, while every boundary is an
   integer at the comparison's scale (fact 1).  So an equality is impossible,
   and because `M` is compared with the integer boundary directly, `M < T` is
   exactly `V < B`.  That is `J_j`, shift-right-with-jamming
   (`kernel/json/stage2.c:512`, naming FloatLib's "rounding after jamming"):
   the discarded tail is replaced by the single jam bit, and the nearest-even
   decision of the jammed value is the original's when the jam lands below the
   guard.  `jam_compare` states it at the comparison's scale,
   `sticky_compare` reads it at the value's, `sticky_no_tie` is "a tie implies
   the sticky bit is clear", and `stkCmp_sticky_spec` is the same at the
   emitted code's own comparison `stkCmp`.

3. **The clamps are the nearest-even answer.**  `lead >= 309` is `+-inf`
   because `10 ^ 309` is above the overflow threshold, and `lead <= -325` is
   `+-0` because anything below `10 ^ -324` is below half the smallest
   subnormal, and `0` is the even one there.  `roundMag_of_lead_ge` and
   `roundMag_of_lead_le` prove both against `roundMag`.

4. **One rounding from `(M, S, sticky)` is `roundMag`'s.**  The emitted walk
   brackets the value with `stk_cmp`'s decisions and stops inside the
   candidate's rounding interval, which is the nearest-even selection
   `roundMag` makes.  This module proves the sticky comparison exact
   (facts 1 and 2), the clamps (fact 3), and that `roundMag`'s own overflow
   test is one of the walk's boundary comparisons (`overflow_test_eq`), so
   every decision the walk makes is the one this module proves exact.  The
   model of the path, `tier3Mag`, is those clamps and that one rounding, and
   `tier3Mag_eq_roundMag` proves it on `roundMag`.  The walk's *traversal* --
   the step-up/step-down loop over candidates -- is not modelled; see
   `What is not proved` below.

## The statement

`EmittedRefinesOn (tier3Emitted read) (fun d => Fallback d kernelDecides)`
(`LeanLLVM/StrtodRefine.lean`) on every well-formed lexeme the first two tiers
declined: the binary64 encoding the emitted conversion returns is `strtodSpec`'s.
`read` is the emitted scanner's reading, taken as a parameter exactly as tier 1
takes it, with its one obligation.  `LeanLLVM/StrtodTier1.lean` is imported for
the encoding's own shape (`binOf`, `strtodSpec_eq_binOf`), so the encoding is
not spelled a second time.

There is no `sorry`, `admit` or `native_decide` below.  Every declaration is
pinned at the end of the file, and none of them carries `Classical.choice`.
-/
import LeanLLVM.StrtodRefine
import LeanLLVM.StrtodTier1
import ITree.Internal.FloatingPoint

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2200

namespace LeanLLVM.StrtodTier3

open LeanLLVM.JSON
open LeanLLVM.StrtodRefine
open LeanLLVM.StrtodTier1
open ByteString

/-! ### The window's width

`STK_DIGITS`: the longest decimal expansion a boundary can have.  The bounds
below are stated against this constant, and `stkDigits_eq` is the only place
its value is read. -/

/-- The number of significant digits the conversion retains. -/
def stkDigits : Nat := 768

theorem stkDigits_eq : stkDigits = 768 := rfl

/-! ### Counting a magnitude's decimal digits

`ndig m` is the number of decimal digits of `m`, with `ndig 0 = 1`.  It is the
emitted reader's `T - lead` (all digits less the leading zeros) for a nonzero
`m`, and the recursion peels base ten.  `ndig_spec` is the only property the
window needs: a positive `m` lies in `[10 ^ (ndig m - 1), 10 ^ ndig m)`. -/

/-- The decimal digit count: `ndig 0 = 1`, and a positive `m` is peeled one
base-ten digit at a time. -/
def ndig (m : Nat) : Nat :=
  if m < 10 then 1 else 1 + ndig (m / 10)
termination_by m
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

theorem ndig_pos (m : Nat) : 0 < ndig m := by
  rw [ndig]
  split
  · decide
  · omega

/-- A positive magnitude lies in the half-open decade its digit count names. -/
theorem ndig_spec {m : Nat} (hm : 0 < m) :
    10 ^ (ndig m - 1) ≤ m ∧ m < 10 ^ ndig m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [ndig]
    split
    · rename_i h
      refine ⟨?_, ?_⟩
      · simpa using Nat.succ_le_of_lt hm
      · simpa using h
    · rename_i h
      have hm10 : 10 ≤ m := Nat.le_of_not_lt h
      have hm0 : 0 < m := by omega
      obtain ⟨ih1, ih2⟩ :=
        ih (m / 10) (Nat.div_lt_self hm0 (by decide))
          (Nat.div_pos hm10 (by decide))
      have ht : 1 ≤ ndig (m / 10) := ndig_pos _
      refine ⟨?_, ?_⟩
      · have hexp : 1 + ndig (m / 10) - 1 = ndig (m / 10) := by omega
        rw [hexp]
        calc 10 ^ ndig (m / 10)
            = 10 ^ ((ndig (m / 10) - 1) + 1) := by rw [Nat.sub_add_cancel ht]
          _ = 10 ^ (ndig (m / 10) - 1) * 10 := Nat.pow_succ 10 _
          _ ≤ (m / 10) * 10 := Nat.mul_le_mul_right 10 ih1
          _ ≤ m := Nat.div_mul_le_self m 10
      · have hexp : 1 + ndig (m / 10) = ndig (m / 10) + 1 := by omega
        rw [hexp, Nat.pow_succ]
        exact Nat.lt_mul_of_div_lt ih2 (by decide)

/-- The digit count is the unique exponent bracket: a positive `x` in
`[10 ^ (t - 1), 10 ^ t)` has `t` digits. -/
theorem ndig_eq_of_bounds {x t : Nat} (h0 : 0 < x)
    (h1 : 10 ^ (t - 1) ≤ x) (h2 : x < 10 ^ t) : ndig x = t := by
  obtain ⟨n1, n2⟩ := ndig_spec h0
  rcases Nat.lt_trichotomy (ndig x) t with h | h | h
  · have hstep : 10 ^ ndig x ≤ 10 ^ (t - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · exact h
  · have hstep : 10 ^ t ≤ 10 ^ (ndig x - 1) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-! ### The retained window

`windowOf m E` is the emitted reader's decomposition of the magnitude
`m * 10 ^ E`: `M` is the leading `min (ndig m) 768` digits as an integer, `S`
is the weight of `M`'s last digit, and `sticky` says whether any digit past
those is nonzero.  The lexeme has no state the model needs beyond
`Decimal.mantissa` and `Decimal.exponent`, which are the digits and the
exponent the emitted scanner accumulates. -/

/-- The number of significant digits dropped past the window. -/
def stkDrop (m : Nat) : Nat := ndig m - stkDigits

/-- The retained window of the magnitude `m * 10 ^ E`. -/
structure StkWindow where
  /-- The retained digits as an integer. -/
  M : Nat
  /-- The weight of `M`'s last digit. -/
  S : Int
  /-- Whether any digit past the window is nonzero. -/
  sticky : Bool
deriving DecidableEq, Repr

/-- The emitted reader's window: the first `min (ndig m) 768` significant
digits, their weight, and the sticky bit. -/
def windowOf (m : Nat) (E : Int) : StkWindow where
  M := m / 10 ^ stkDrop m
  S := E + (stkDrop m : Int)
  sticky := decide (m % 10 ^ stkDrop m ≠ 0)

theorem windowOf_M (m : Nat) (E : Int) :
    (windowOf m E).M = m / 10 ^ stkDrop m := rfl

theorem windowOf_S (m : Nat) (E : Int) :
    (windowOf m E).S = E + (stkDrop m : Int) := rfl

theorem windowOf_sticky (m : Nat) (E : Int) :
    (windowOf m E).sticky = decide (m % 10 ^ stkDrop m ≠ 0) := rfl

/-- The sticky bit is exactly "some dropped digit is nonzero". -/
theorem windowOf_sticky_iff (m : Nat) (E : Int) :
    (windowOf m E).sticky = true ↔ m % 10 ^ stkDrop m ≠ 0 := by
  rw [windowOf_sticky, decide_eq_true_eq]

/-- The decomposition the window records: `m = M * 10 ^ s + r` with `r` the
dropped tail. -/
theorem window_decomp (m : Nat) :
    m = (m / 10 ^ stkDrop m) * 10 ^ stkDrop m + m % 10 ^ stkDrop m := by
  have h := Nat.div_add_mod m (10 ^ stkDrop m)
  rw [Nat.mul_comm] at h
  exact h.symm

/-- The tail is below the window's last place. -/
theorem window_tail_lt (m : Nat) :
    m % 10 ^ stkDrop m < 10 ^ stkDrop m :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

/-- The retained digits are below `10 ^ 768`: the window is bounded whatever
the lexeme's length. -/
theorem window_M_lt {m : Nat} (hm : 0 < m) :
    m / 10 ^ stkDrop m < 10 ^ stkDigits := by
  by_cases hs : stkDrop m = 0
  · rw [hs, Nat.pow_zero, Nat.div_one]
    have hle : ndig m ≤ stkDigits := by
      unfold stkDrop at hs
      omega
    exact Nat.lt_of_lt_of_le (ndig_spec hm).2
      (Nat.pow_le_pow_right (by decide) hle)
  · have hlt : stkDigits < ndig m := by
      unfold stkDrop at hs
      omega
    have hexp : stkDigits + stkDrop m = ndig m := by
      unfold stkDrop
      omega
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 10))]
    rw [← Nat.pow_add, hexp]
    exact (ndig_spec hm).2

/-- A full window's retained digits are at least `10 ^ 767`: the first digit is
nonzero and there are exactly 768 of them. -/
theorem window_M_ge {m : Nat} (hm : 0 < m) (hs : 0 < stkDrop m) :
    10 ^ (stkDigits - 1) ≤ m / 10 ^ stkDrop m := by
  have hexp : (stkDigits - 1) + stkDrop m = ndig m - 1 := by
    rw [show stkDrop m = ndig m - stkDigits from rfl, stkDigits_eq] at hs ⊢
    omega
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos (by decide : 0 < 10))]
  rw [← Nat.pow_add, hexp]
  exact (ndig_spec hm).1

/-- The retained digits have the digit count the window claims: dropping `s`
digits drops `s` digits from the count. -/
theorem ndig_window_M {m : Nat} (hm : 0 < m) :
    ndig (m / 10 ^ stkDrop m) = ndig m - stkDrop m := by
  have hsle : stkDrop m ≤ ndig m - 1 := by
    rw [show stkDrop m = ndig m - stkDigits from rfl, stkDigits_eq]
    omega
  have hpow : 0 < 10 ^ stkDrop m := Nat.pow_pos (by decide)
  have hx0 : 0 < m / 10 ^ stkDrop m := by
    rw [Nat.div_pos_iff]
    refine ⟨Nat.pow_pos (by decide), ?_⟩
    have h := (ndig_spec hm).1
    calc 10 ^ stkDrop m ≤ 10 ^ (ndig m - 1) :=
          Nat.pow_le_pow_right (by decide) hsle
      _ ≤ m := h
  refine ndig_eq_of_bounds hx0 ?_ ?_
  · have hexp : ndig m - stkDrop m - 1 = ndig m - 1 - stkDrop m := by omega
    rw [hexp, Nat.le_div_iff_mul_le hpow, ← Nat.pow_add,
      show ndig m - 1 - stkDrop m + stkDrop m = ndig m - 1 by omega]
    exact (ndig_spec hm).1
  · rw [Nat.div_lt_iff_lt_mul hpow, ← Nat.pow_add,
      show ndig m - stkDrop m + stkDrop m = ndig m by omega]
    exact (ndig_spec hm).2

/-- The leading digit's decimal exponent: the value lies in
`[10 ^ lead, 10 ^ (lead + 1))`. -/
def StkWindow.lead (w : StkWindow) : Int :=
  ((ndig w.M : Nat) : Int) - 1 + w.S

/-- The window's lead is the magnitude's: dropping digits and shifting their
weight cancel. -/
theorem window_lead {m : Nat} (hm : 0 < m) (E : Int) :
    (windowOf m E).lead = ((ndig m : Nat) : Int) - 1 + E := by
  have hsle : stkDrop m ≤ ndig m := by
    unfold stkDrop
    omega
  unfold StkWindow.lead windowOf
  dsimp only
  rw [ndig_window_M hm]
  rw [Int.natCast_sub hsle]
  omega

/-! ### Fact 1: the window suffices

Every rounding decision compares the value with a binary64 value or with the
midpoint of two adjacent ones.  In the lattice of the specification the
comparison's right side is `J * 2 ^ e` (`roundMag` and the emitted walk both
compare at that shape), with `J = m` for a value, `2 * m + 1` for a midpoint,
and `J < 2 ^ 54` in every case; the exponent is at least `-1075`, because the
smallest boundary is half the smallest subnormal `2 ^ -1075`.

Cleared over `10 ^ 1075` a boundary is `J * 5 ^ 1075 * 2 ^ (e + 1075)`, and
`(2 ^ 54 - 1) * 5 ^ 1075 < 10 ^ 768` -- `log10 ((2 ^ 54 - 1) * 5 ^ 1075)` is
`767.65` -- so the boundary has at most 768 significant decimal digits and no
digit past the window is needed to represent it.  `boundary_num_lt` is that
bound; `boundary_int_lt` is the same bound for the boundaries that are integer
multiples of a power of two above one. -/

/-- `(2 ^ 54 - 1) * 5 ^ 1075 < 10 ^ 768`, as `5 ^ 307 < 2 ^ 714` cleared of
`5 ^ 768`. -/
theorem five_pow_307_lt : (5 : Nat) ^ 307 < 2 ^ 714 := by decide

/-- The overflow threshold's decade: `2 ^ 1024 ≤ 10 ^ 309`. -/
theorem pow_two_1024_le_ten_309 : (2 : Nat) ^ 1024 ≤ 10 ^ 309 := by decide

/-- Half the smallest subnormal against the zero clamp's decade:
`2 ^ 1075 < 10 ^ 324`. -/
theorem pow_two_1075_lt_ten_324 : (2 : Nat) ^ 1075 < 10 ^ 324 := by decide

/-- The fractional boundary `J / 2 ^ k = J * 5 ^ k / 10 ^ k` has at most 768
significant digits: its numerator is below `10 ^ 768`. -/
theorem boundary_num_lt {J : Nat} (hJ : J < 2 ^ 54) {k : Nat} (hk : k ≤ 1075) :
    J * 5 ^ k < 10 ^ stkDigits := by
  have h1 : J * 5 ^ k ≤ (2 ^ 54 - 1) * 5 ^ 1075 := by
    refine Nat.mul_le_mul ?_ (Nat.pow_le_pow_right (by decide) hk)
    omega
  have h2 : (2 ^ 54 - 1) * 5 ^ 1075 < 2 ^ 54 * 5 ^ 1075 := by
    refine Nat.mul_lt_mul_of_pos_right ?_ (Nat.pow_pos (by decide))
    exact Nat.sub_one_lt (Nat.ne_of_gt (Nat.pow_pos (by decide)))
  have h3 : 5 ^ 1075 = 5 ^ 307 * 5 ^ 768 := by
    rw [← Nat.pow_add]
  have h4 : (2 : Nat) ^ 54 * 5 ^ 307 < 2 ^ 768 := by
    calc 2 ^ 54 * 5 ^ 307 < 2 ^ 54 * 2 ^ 714 :=
          Nat.mul_lt_mul_of_pos_left five_pow_307_lt (Nat.pow_pos (by decide))
      _ = 2 ^ 768 := by rw [← Nat.pow_add]
  have h5 : (2 ^ 54 * 5 ^ 307) * 5 ^ 768 < 2 ^ 768 * 5 ^ 768 :=
    Nat.mul_lt_mul_of_pos_right h4 (Nat.pow_pos (by decide))
  have h6 : (2 : Nat) ^ 768 * 5 ^ 768 = 10 ^ 768 := by
    rw [← Nat.mul_pow]
  rw [stkDigits_eq]
  calc J * 5 ^ k ≤ (2 ^ 54 - 1) * 5 ^ 1075 := h1
    _ < 2 ^ 54 * 5 ^ 1075 := h2
    _ = (2 ^ 54 * 5 ^ 307) * 5 ^ 768 := by rw [h3, Nat.mul_assoc]
    _ < 2 ^ 768 * 5 ^ 768 := h5
    _ = 10 ^ 768 := h6

/-- An integer boundary `J * 2 ^ j` in range has at most 309 digits, hence at
most 768: `J < 2 ^ 54` and `j ≤ 970` keep it below `2 ^ 1024 < 10 ^ 309`. -/
theorem boundary_int_lt {J : Nat} (hJ : J < 2 ^ 54) {j : Nat} (hj : j ≤ 970) :
    J * 2 ^ j < 10 ^ stkDigits := by
  have h1 : J * 2 ^ j < 2 ^ 54 * 2 ^ 970 := by
    calc J * 2 ^ j < 2 ^ 54 * 2 ^ j :=
          Nat.mul_lt_mul_of_pos_right hJ (Nat.pow_pos (by decide))
      _ ≤ 2 ^ 54 * 2 ^ 970 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hj)
  have h2 : (2 : Nat) ^ 54 * 2 ^ 970 = 2 ^ 1024 := by
    rw [← Nat.pow_add]
  have h3 : 10 ^ 309 ≤ 10 ^ stkDigits := by
    rw [stkDigits_eq]
    exact Nat.pow_le_pow_right (by decide) (by decide)
  calc J * 2 ^ j < 2 ^ 54 * 2 ^ 970 := h1
    _ = 2 ^ 1024 := h2
    _ ≤ 10 ^ 309 := pow_two_1024_le_ten_309
    _ ≤ 10 ^ stkDigits := h3

/-! ### Fact 3: the two clamps are the nearest-even answer

The emitted conversion refuses to walk when the leading digit's exponent `f`
leaves the format's range: `f >= 309` is `+-inf` and `f <= -325` is `+-0`.
Both are what one nearest-even rounding gives.

`f >= 309` means the value is at least `10 ^ 309`, and `10 ^ 309 * 2 ^ 1074 >
2 ^ 2098 = 2 ^ 1024 * 2 ^ 1074` is above the overflow threshold
`2 ^ 1024 - 2 ^ 970`, so `roundMag` overflows.

`f <= -325` means the value is below `10 ^ -324`, and `10 ^ -324 < 2 ^ -1075`
is half the smallest subnormal, so the two lattice points bracketing it are `0`
and `2 ^ -1074` and the even one is `0`; `roundMag`'s subnormal branch returns
the zero code.  The two inequalities are `pow_two_1024_le_ten_309` and
`pow_two_1075_lt_ten_324` above. -/

/-- The magnitude `m * 10 ^ E` in the specification's ticks, read at the same
pair `Decimal.ticks` states. -/
def magTicks (m : Nat) (E : Int) : Nat × Nat :=
  if 0 ≤ E then (m * 10 ^ E.toNat * 2 ^ 1074, 1) else (m * 2 ^ 1074, 10 ^ E.natAbs)

theorem magTicks_eq_ticks (d : Decimal) :
    magTicks d.mantissa d.exponent = d.ticks := rfl

theorem magTicks_den_pos (m : Nat) (E : Int) : 0 < (magTicks m E).2 := by
  unfold magTicks
  split
  · exact Nat.one_pos
  · exact Nat.pow_pos (by decide)

/-- The leading digit's exponent `f`, read from the magnitude rather than from
the window: `leadM m E = ndig m - 1 + E`. -/
def leadM (m : Nat) (E : Int) : Int := ((ndig m : Nat) : Int) - 1 + E

/-- The window's lead is the emitted code's `f`. -/
theorem window_leadM {m : Nat} (hm : 0 < m) (E : Int) :
    (windowOf m E).lead = leadM m E := window_lead hm E

/-- A nonnegative exponent's `toNat` is the exponent, and peeling one digit off
`ndig` keeps the lead an integer sum. -/
theorem leadM_nonneg_form {m : Nat} {E : Int} (hE : 0 ≤ E) :
    leadM m E = ((ndig m - 1 + E.toNat : Nat) : Int) := by
  unfold leadM
  have h1 : ((E.toNat : Nat) : Int) = E := Int.toNat_of_nonneg hE
  have h2 : ((ndig m - 1 : Nat) : Int) = ((ndig m : Nat) : Int) - 1 :=
    Int.natCast_sub (Nat.succ_le_of_lt (ndig_pos m))
  rw [Int.natCast_add, h2, h1]

/-- A negative exponent's magnitude: `↑E.natAbs = -E`. -/
theorem natAbs_of_neg {E : Int} (hE : E < 0) :
    ((E.natAbs : Nat) : Int) = -E := by
  have h1 : E.natAbs = (-E).natAbs := (Int.natAbs_neg E).symm
  rw [h1]
  exact Int.natAbs_of_nonneg (by omega)

/-- The value is at least `10 ^ 309` when the lead is: in ticks,
`10 ^ 309 * 2 ^ 1074` times the denominator is below the numerator. -/
theorem ticks_ge_of_lead_ge {m : Nat} (hm : 0 < m) {E : Int}
    (h : 309 ≤ leadM m E) :
    10 ^ 309 * 2 ^ 1074 * (magTicks m E).2 ≤ (magTicks m E).1 := by
  by_cases hE : 0 ≤ E
  · have hP : (magTicks m E).1 = m * 10 ^ E.toNat * 2 ^ 1074 := by
      unfold magTicks
      rw [ite_eq_left hE]
    have hD : (magTicks m E).2 = 1 := by
      unfold magTicks
      rw [ite_eq_left hE]
    have hcast := leadM_nonneg_form (m := m) hE
    have h309 : 309 ≤ ndig m - 1 + E.toNat := by
      rw [hcast] at h
      omega
    calc 10 ^ 309 * 2 ^ 1074 * (magTicks m E).2
        = 10 ^ 309 * 2 ^ 1074 := by rw [hD, Nat.mul_one]
      _ ≤ 10 ^ (ndig m - 1 + E.toNat) * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h309)
      _ = (10 ^ (ndig m - 1) * 10 ^ E.toNat) * 2 ^ 1074 := by rw [Nat.pow_add]
      _ ≤ (m * 10 ^ E.toNat) * 2 ^ 1074 :=
            Nat.mul_le_mul_right _
              (Nat.mul_le_mul_right _ (ndig_spec hm).1)
      _ = (magTicks m E).1 := hP.symm
  · have hE0 : E < 0 := by omega
    have hk : ((E.natAbs : Nat) : Int) = -E := natAbs_of_neg hE0
    have hP : (magTicks m E).1 = m * 2 ^ 1074 := by
      unfold magTicks
      rw [ite_eq_right hE]
    have hD : (magTicks m E).2 = 10 ^ E.natAbs := by
      unfold magTicks
      rw [ite_eq_right hE]
    have h309 : 309 + E.natAbs ≤ ndig m - 1 := by
      unfold leadM at h
      omega
    calc 10 ^ 309 * 2 ^ 1074 * (magTicks m E).2
        = 10 ^ 309 * 2 ^ 1074 * 10 ^ E.natAbs := by rw [hD]
      _ = (10 ^ 309 * 10 ^ E.natAbs) * 2 ^ 1074 := by ac_rfl
      _ = 10 ^ (309 + E.natAbs) * 2 ^ 1074 := by rw [Nat.pow_add]
      _ ≤ 10 ^ (ndig m - 1) * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h309)
      _ ≤ m * 2 ^ 1074 := Nat.mul_le_mul_right _ (ndig_spec hm).1
      _ = (magTicks m E).1 := hP.symm

/-- `2 ^ 2044 < 2 ^ 2098`: the two powers of the overflow threshold. -/
theorem two_pow_2044_lt_2098 : (2 : Nat) ^ 2044 < 2 ^ 2098 := by
  calc (2 : Nat) ^ 2044 = 2 ^ 2044 * 1 := (Nat.mul_one _).symm
    _ < 2 ^ 2044 * 2 ^ 54 :=
          Nat.mul_lt_mul_of_pos_left (by decide) (Nat.pow_pos (by decide))
    _ = 2 ^ 2098 := by rw [← Nat.pow_add]

/-- Right cancellation of a strict product, choice-free: the contrapositive of
`Nat.mul_le_mul_right`. -/
theorem lt_mul_right_iff {a b c : Nat} (h : 0 < a) : (b * a < c * a ↔ b < c) :=
  ⟨fun hlt => Nat.lt_of_not_le
      (fun hcb => absurd (Nat.mul_le_mul_right a hcb) (Nat.not_le.mpr hlt)),
   fun hlt => Nat.mul_lt_mul_of_pos_right hlt h⟩

/-- `f >= 309` rounds to infinity: the exact value is at or above the overflow
threshold, which is `roundMag`'s overflow branch. -/
theorem roundMag_of_lead_ge {m : Nat} (hm : 0 < m) {E : Int}
    (h : 309 ≤ leadM m E) :
    roundMag (magTicks m E).1 (magTicks m E).2 = .inf := by
  have hov : overflowTicks ≤ 10 ^ 309 * 2 ^ 1074 := by
    unfold overflowTicks
    calc (2 : Nat) ^ 2098 - 2 ^ 2044 ≤ 2 ^ 2098 := Nat.sub_le _ _
      _ = 2 ^ 1024 * 2 ^ 1074 := by rw [← Nat.pow_add]
      _ ≤ 10 ^ 309 * 2 ^ 1074 :=
            Nat.mul_le_mul_right _ pow_two_1024_le_ten_309
  have hval := ticks_ge_of_lead_ge hm h
  have hle : overflowTicks * (magTicks m E).2 ≤ (magTicks m E).1 := by
    calc overflowTicks * (magTicks m E).2
        ≤ (10 ^ 309 * 2 ^ 1074) * (magTicks m E).2 :=
          Nat.mul_le_mul_right _ hov
      _ = 10 ^ 309 * 2 ^ 1074 * (magTicks m E).2 := rfl
      _ ≤ (magTicks m E).1 := hval
  unfold roundMag
  rw [ite_eq_left hle]

/-- `f <= -325` rounds to zero: the value is below half the smallest subnormal,
so both bracket points are `0` and `2 ^ -1074`, and `roundMag`'s subnormal
branch selects the even one, `0`. -/
theorem roundMag_of_lead_le {m : Nat} (hm : 0 < m) {E : Int}
    (h : leadM m E ≤ -325) :
    roundMag (magTicks m E).1 (magTicks m E).2 = .fin ⟨0, 0⟩ := by
  have hE0 : E < 0 := by unfold leadM at h; omega
  have hk : ((E.natAbs : Nat) : Int) = -E := natAbs_of_neg hE0
  have hP : (magTicks m E).1 = m * 2 ^ 1074 := by
    unfold magTicks
    rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
  have hD : (magTicks m E).2 = 10 ^ E.natAbs := by
    unfold magTicks
    rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
  have hle : ndig m ≤ E.natAbs - 324 := by
    unfold leadM at h
    omega
  have h2P : 2 * (magTicks m E).1 < (magTicks m E).2 := by
    rw [hP, hD]
    have hd : m < 10 ^ ndig m := (ndig_spec hm).2
    have h1 : m * 2 ^ 1075 < 10 ^ (E.natAbs - 324) * 2 ^ 1075 :=
      calc m * 2 ^ 1075 < 10 ^ ndig m * 2 ^ 1075 :=
            Nat.mul_lt_mul_of_pos_right hd (Nat.pow_pos (by decide))
        _ ≤ 10 ^ (E.natAbs - 324) * 2 ^ 1075 :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hle)
    have h2 : 10 ^ (E.natAbs - 324) * 2 ^ 1075 ≤
        10 ^ (E.natAbs - 324) * 10 ^ 324 :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt pow_two_1075_lt_ten_324)
    have h3 : 10 ^ (E.natAbs - 324) * 10 ^ 324 = 10 ^ E.natAbs := by
      have hp : 324 ≤ E.natAbs := by have := ndig_pos m; omega
      rw [← Nat.pow_add, Nat.sub_add_cancel hp]
    calc 2 * (m * 2 ^ 1074)
        = m * 2 ^ 1074 * 2 := by ac_rfl
      _ = m * 2 ^ 1075 := by rw [Nat.mul_assoc, ← Nat.pow_succ]
      _ < 10 ^ E.natAbs := Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 h3.le)
  have hPD : (magTicks m E).1 < (magTicks m E).2 := by omega
  have hdiv : (magTicks m E).1 / (magTicks m E).2 = 0 := Nat.div_eq_of_lt hPD
  have hmod : (magTicks m E).1 % (magTicks m E).2 = (magTicks m E).1 :=
    Nat.mod_eq_of_lt hPD
  have hov : ¬ overflowTicks * (magTicks m E).2 ≤ (magTicks m E).1 := by
    intro hc
    have hpos : 0 < overflowTicks := by
      unfold overflowTicks
      exact Nat.sub_pos_of_lt two_pow_2044_lt_2098
    have hle' : (magTicks m E).2 ≤ overflowTicks * (magTicks m E).2 :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  have hsub : subCode (magTicks m E).1 (magTicks m E).2 = ⟨0, 0⟩ := by
    dsimp only [subCode]
    rw [hdiv, hmod, ite_eq_left h2P]
  have hbig : (magTicks m E).1 < (magTicks m E).2 * 2 ^ 52 :=
    Nat.lt_of_lt_of_le hPD
      (Nat.le_mul_of_pos_right _ (by decide : 0 < 2 ^ 52))
  unfold roundMag
  rw [ite_eq_right hov, ite_eq_left hbig, hsub]

/-! ### Fact 2: the sticky bit is enough

`jam_compare` is the invariant `J_j`, shift-right-with-jamming
(`kernel/json/stage2.c:512`, naming FloatLib's "rounding after jamming"): once
the tail is below the guard position, replacing it by a single jam bit -- here
"the retained decimal is equal to the boundary" being read as strictly above,
because the tail is positive -- preserves the nearest-even decision.

At the comparison's scale the rule is an inequality of naturals.  Write the
magnitude as `m = M * 10 ^ s + r` (`M` the retained digits, `r` the tail) and
the boundary as the integer `T` at that scale, with `k = -S` the shift that
clears the boundary's denominator (fact 1).  Then `V` and `B` compare as
`M * 10 ^ s + r` and `T * 10 ^ s`, and since `0 < r < 10 ^ s` the comparison is
`M` against `T` -- equality impossible, and `M < T` exactly `V < B`.

`valLtBoundary` and `valEqBoundary` are the sign of `V - B` with both sides
multiplied by their denominators: `m * 10 ^ E` against `J * 2 ^ eB`. -/

/-- `M * 10 ^ s + r` against `T * 10 ^ s` with `0 < r < 10 ^ s`: the tail's
only contribution is that equality is impossible. -/
theorem jam_compare {M r s T : Nat} (hr0 : 0 < r) (hrs : r < 10 ^ s) :
    (M * 10 ^ s + r < T * 10 ^ s ↔ M < T) ∧ M * 10 ^ s + r ≠ T * 10 ^ s := by
  have hpos : 0 < 10 ^ s := Nat.pow_pos (by decide)
  have key : ∀ h : M < T, M * 10 ^ s + r < T * 10 ^ s := by
    intro h
    have hM1 : M + 1 ≤ T := h
    have hlt : M * 10 ^ s + r < (M + 1) * 10 ^ s := by
      calc M * 10 ^ s + r < M * 10 ^ s + 10 ^ s := Nat.add_lt_add_left hrs _
        _ = (M + 1) * 10 ^ s := by rw [Nat.add_mul, Nat.one_mul]
    exact Nat.lt_of_lt_of_le hlt (Nat.mul_le_mul_right _ hM1)
  constructor
  · constructor
    · intro h
      exact LeanLLVM.JSON.lt_of_mul_lt_mul_right
        (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h)
    · exact key
  · intro h
    rcases Nat.lt_trichotomy M T with hlt | heq | hgt
    · exact absurd h (Nat.ne_of_lt (key hlt))
    · rw [heq] at h
      have hz : r = 0 := by
        have h' : T * 10 ^ s + r = T * 10 ^ s + 0 := by
          rw [Nat.add_zero]; exact h
        exact Nat.add_left_cancel h'
      omega
    · have h1 : T * 10 ^ s < M * 10 ^ s + r :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hgt hpos) (Nat.le_add_right _ _)
      omega

/-- The boundary `J * 2 ^ eB` at the window's scale `k`: the integer
`J * 5 ^ k * 2 ^ (eB + k)`, which is `B * 10 ^ k` whenever `eB + k >= 0`. -/
def scaledBoundary (J : Nat) (eB : Int) (k : Nat) : Nat :=
  J * 5 ^ k * 2 ^ (eB + (k : Int)).toNat

/-- The magnitude `m * 10 ^ E` is below the boundary `J * 2 ^ eB`: the sign of
`V - B`, both sides multiplied by their denominators. -/
def valLtBoundary (m : Nat) (E : Int) (J : Nat) (eB : Int) : Prop :=
  if 0 ≤ E then
    (if 0 ≤ eB then m * 10 ^ E.toNat < J * 2 ^ eB.toNat
     else m * 10 ^ E.toNat * 2 ^ eB.natAbs < J)
  else
    (if 0 ≤ eB then m < J * 2 ^ eB.toNat * 10 ^ E.natAbs
     else m * 2 ^ eB.natAbs < J * 10 ^ E.natAbs)

/-- The magnitude `m * 10 ^ E` equals the boundary `J * 2 ^ eB`, at the same
cross-multiplied form. -/
def valEqBoundary (m : Nat) (E : Int) (J : Nat) (eB : Int) : Prop :=
  if 0 ≤ E then
    (if 0 ≤ eB then m * 10 ^ E.toNat = J * 2 ^ eB.toNat
     else m * 10 ^ E.toNat * 2 ^ eB.natAbs = J)
  else
    (if 0 ≤ eB then m = J * 2 ^ eB.toNat * 10 ^ E.natAbs
     else m * 2 ^ eB.natAbs = J * 10 ^ E.natAbs)

/-- Clearing the boundary's denominator at the window's scale, for a
nonnegative boundary exponent. -/
theorem scaledBoundary_mul_int (J : Nat) {eB : Int} (heB : 0 ≤ eB)
    {k s : Nat} {E : Int} (hk : (k : Int) = -(E + (s : Int))) (hE : E < 0) :
    scaledBoundary J eB k * 10 ^ s = J * 2 ^ eB.toNat * 10 ^ E.natAbs := by
  unfold scaledBoundary
  have htoNat : (eB + (k : Int)).toNat = eB.toNat + k := by
    apply Int.natCast_inj.mp
    rw [Int.toNat_of_nonneg (by omega), Int.natCast_add,
      Int.toNat_of_nonneg heB]
  have hEabs : E.natAbs = k + s := by
    apply Int.natCast_inj.mp
    rw [Int.natCast_add, natAbs_of_neg hE]
    omega
  rw [htoNat, hEabs]
  have h52 : 5 ^ k * 2 ^ k = 10 ^ k := by rw [← Nat.mul_pow]
  rw [Nat.pow_add, Nat.pow_add]
  calc J * 5 ^ k * (2 ^ eB.toNat * 2 ^ k) * 10 ^ s
      = J * 2 ^ eB.toNat * (5 ^ k * 2 ^ k) * 10 ^ s := by ac_rfl
    _ = J * 2 ^ eB.toNat * 10 ^ k * 10 ^ s := by rw [h52]
    _ = J * 2 ^ eB.toNat * (10 ^ k * 10 ^ s) := by ac_rfl

/-- Clearing the boundary's denominator at the window's scale, for a negative
boundary exponent: both sides are multiplied by `2 ^ natAbs eB`, which the
shift `eB + k >= 0` makes an integer. -/
theorem scaledBoundary_mul_fraction (J : Nat) {eB : Int} (heB : eB < 0)
    {k s : Nat} {E : Int} (hk : (k : Int) = -(E + (s : Int))) (hE : E < 0)
    (hshift : 0 ≤ eB + (k : Int)) :
    scaledBoundary J eB k * 10 ^ s * 2 ^ eB.natAbs = J * 10 ^ E.natAbs := by
  unfold scaledBoundary
  have htoNat : (eB + (k : Int)).toNat = k - eB.natAbs := by
    apply Int.natCast_inj.mp
    rw [Int.toNat_of_nonneg hshift, Int.natCast_sub (by omega),
      natAbs_of_neg heB]
    omega
  have hEabs : E.natAbs = k + s := by
    apply Int.natCast_inj.mp
    rw [Int.natCast_add, natAbs_of_neg hE]
    omega
  have hkn : eB.natAbs ≤ k := by
    have h' := natAbs_of_neg heB
    omega
  rw [htoNat, hEabs]
  have h52 : 5 ^ k * 2 ^ k = 10 ^ k := by rw [← Nat.mul_pow]
  have hkabs : k - eB.natAbs + eB.natAbs = k := Nat.sub_add_cancel hkn
  calc J * 5 ^ k * 2 ^ (k - eB.natAbs) * 10 ^ s * 2 ^ eB.natAbs
      = J * 5 ^ k * (2 ^ (k - eB.natAbs) * 2 ^ eB.natAbs) * 10 ^ s := by ac_rfl
    _ = J * 5 ^ k * 2 ^ k * 10 ^ s := by rw [← Nat.pow_add, hkabs]
    _ = J * (5 ^ k * 2 ^ k) * 10 ^ s := by ac_rfl
    _ = J * 10 ^ k * 10 ^ s := by rw [h52]
    _ = J * 10 ^ (k + s) := by rw [Nat.pow_add]; ac_rfl

/-- **The sticky comparison is the exact one.**  With the tail `r` strictly
between `0` and the window's last place, and the boundary cleared to the
integer `T = scaledBoundary J eB k` (fact 1's `eB + k >= 0`), the cross-
multiplied comparison of `V` with `B` is `M < T`: the jam bit is the whole of
the tail's contribution. -/
theorem sticky_compare {m M r s : Nat} {E : Int} {J : Nat} {eB : Int} {k : Nat}
    (hdec : m = M * 10 ^ s + r) (hr0 : 0 < r) (hrs : r < 10 ^ s)
    (hE : E < 0) (hk : (k : Int) = -(E + (s : Int)))
    (hshift : 0 ≤ eB + (k : Int)) :
    valLtBoundary m E J eB ↔ M < scaledBoundary J eB k := by
  unfold valLtBoundary
  rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
  by_cases heB : 0 ≤ eB
  · rw [ite_eq_left heB]
    have hid := scaledBoundary_mul_int J heB hk hE
    rw [← hid, hdec]
    exact (jam_compare hr0 hrs).1
  · have heB' : eB < 0 := by omega
    rw [ite_eq_right heB]
    have hid := scaledBoundary_mul_fraction J heB' hk hE hshift
    have hpos2 : (0 : Nat) < 2 ^ eB.natAbs := Nat.pow_pos (by decide)
    rw [← hid, lt_mul_right_iff hpos2, hdec]
    exact (jam_compare hr0 hrs).1

/-- **A tie requires the sticky bit clear.**  A nonzero tail is never equal to
a boundary: every boundary is an integer at the comparison's scale, and the
value is strictly between two consecutive retained decimals. -/
theorem sticky_no_tie {m M r s : Nat} {E : Int} {J : Nat} {eB : Int} {k : Nat}
    (hdec : m = M * 10 ^ s + r) (hr0 : 0 < r) (hrs : r < 10 ^ s)
    (hE : E < 0) (hk : (k : Int) = -(E + (s : Int)))
    (hshift : 0 ≤ eB + (k : Int)) :
    ¬ valEqBoundary m E J eB := by
  unfold valEqBoundary
  rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
  by_cases heB : 0 ≤ eB
  · rw [ite_eq_left heB]
    have hid := scaledBoundary_mul_int J heB hk hE
    rw [← hid, hdec]
    exact (jam_compare hr0 hrs).2
  · have heB' : eB < 0 := by omega
    rw [ite_eq_right heB]
    have hid := scaledBoundary_mul_fraction J heB' hk hE hshift
    intro h
    rw [← hid] at h
    rw [hdec] at h
    have hpos2 : (0 : Nat) < 2 ^ eB.natAbs := Nat.pow_pos (by decide)
    exact (jam_compare hr0 hrs).2
      (Nat.mul_right_cancel (m := 2 ^ eB.natAbs) hpos2 h)

/-- A three-way comparison of naturals as the emitted `stk_cmp`'s result. -/
def cmpNat (a b : Nat) : Int :=
  if a < b then -1 else if a = b then 0 else 1

/-- The exact cross-multiplied comparison of `M * 10 ^ S` with `J * 2 ^ eB`. -/
def cmpExact (M : Nat) (S : Int) (J : Nat) (eB : Int) : Int :=
  cmpNat
    (M * (if 0 ≤ S then 10 ^ S.toNat else 1)
       * (if 0 ≤ eB then 1 else 2 ^ eB.natAbs))
    (J * (if 0 ≤ eB then 2 ^ eB.toNat else 1)
       * (if 0 ≤ S then 1 else 10 ^ S.natAbs))

/-- The emitted comparison: the sign of `V - B` for the window's magnitude `V`
and the boundary `B = J * 2 ^ eB`.  With the sticky bit set the retained digits
are compared with the boundary cleared to the window's scale (fact 1), and
equality is reported as "above" because the tail is positive; with it clear the
comparison is the exact cross-multiplied one.  The emitted `stk_cmp` also folds
a nonnegative `S` into `M`; `cmpExact` is that normalization's result, so the
definition reads the same comparison without the fold. -/
def stkCmp (w : StkWindow) (J : Nat) (eB : Int) : Int :=
  if w.sticky then
    (if w.M < scaledBoundary J eB (-w.S).toNat then -1 else 1)
  else
    cmpExact w.M w.S J eB

/-- A sticky window retains exactly 768 digits, so its `S` is the lead less the
window's width. -/
theorem leadM_window_S {m : Nat} (E : Int) (hs : 0 < stkDrop m) :
    (windowOf m E).S = leadM m E - 767 := by
  rw [windowOf_S]
  unfold leadM
  have h : ndig m = stkDrop m + 768 := by
    rw [show stkDrop m = ndig m - stkDigits from rfl, stkDigits_eq] at hs ⊢
    omega
  rw [h, Int.natCast_add]
  omega

/-- Sticky means the window is full: some digit past the window is nonzero. -/
theorem sticky_drop_pos {m : Nat} (E : Int)
    (hst : (windowOf m E).sticky = true) : 0 < stkDrop m := by
  rcases Nat.eq_zero_or_pos (stkDrop m) with h | h
  · exfalso
    have hr : m % 10 ^ stkDrop m = 0 := by rw [h, Nat.pow_zero, Nat.mod_one]
    rw [windowOf_sticky_iff] at hst
    exact hst hr
  · exact h

/-- Sticky means the dropped tail is nonzero. -/
theorem sticky_tail_pos {m : Nat} (E : Int)
    (hst : (windowOf m E).sticky = true) : 0 < m % 10 ^ stkDrop m := by
  rw [windowOf_sticky_iff] at hst
  omega

/-- A sticky window inside the clamp's range has a negative `S`, hence a
negative decimal exponent: `S = lead - 767` and `lead <= 308`. -/
theorem sticky_S_neg {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = true) (hlead : leadM m E ≤ 308) :
    (windowOf m E).S < 0 := by
  have hs := sticky_drop_pos E hst
  rw [leadM_window_S E hs]
  omega

/-- A sticky window's decimal exponent is negative. -/
theorem sticky_E_neg {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = true) (hlead : leadM m E ≤ 308) : E < 0 := by
  have hS := sticky_S_neg hst hlead
  rw [windowOf_S] at hS
  omega

/-- **The emitted comparison at a sticky window is the exact comparison.**
Reading `stkCmp` at the window `windowOf m E`, the emitted `stk_cmp` returns
`-1` exactly when the magnitude is below the boundary and never returns `0`:
fact 2 at the emitted code's own comparison.  The hypothesis `eB + k >= 0` is
fact 1's `eB + 767 - f >= 0`, the reason the boundary is an integer at the
window's scale. -/
theorem stkCmp_sticky_spec {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = true) (hlead : leadM m E ≤ 308)
    {J : Nat} {eB : Int}
    (hshift : 0 ≤ eB + ((-(windowOf m E).S).toNat : Int)) :
    (stkCmp (windowOf m E) J eB = -1 ↔ valLtBoundary m E J eB) ∧
      stkCmp (windowOf m E) J eB ≠ 0 := by
  have hs := sticky_drop_pos E hst
  have hr0 := sticky_tail_pos E hst
  have hrs := window_tail_lt m
  have hE := sticky_E_neg hst hlead
  have hdec : m = (windowOf m E).M * 10 ^ stkDrop m + m % 10 ^ stkDrop m := by
    rw [windowOf_M]
    exact window_decomp m
  have hSneg := sticky_S_neg hst hlead
  have hk : (((-(windowOf m E).S).toNat : Nat) : Int) =
      -(E + (stkDrop m : Int)) := by
    rw [Int.toNat_of_nonneg (by omega), windowOf_S]
  constructor
  · unfold stkCmp
    rw [ite_eq_left hst]
    by_cases hcmp : (windowOf m E).M <
        scaledBoundary J eB (( -(windowOf m E).S).toNat)
    · rw [ite_eq_left hcmp]
      constructor
      · intro _
        exact (sticky_compare hdec hr0 hrs hE hk hshift).2 hcmp
      · intro _
        rfl
    · rw [ite_eq_right hcmp]
      constructor
      · intro h
        exact absurd h (by decide : (1 : Int) ≠ -1)
      · intro hv
        exact absurd ((sticky_compare hdec hr0 hrs hE hk hshift).1 hv) hcmp
  · unfold stkCmp
    rw [ite_eq_left hst]
    by_cases hc : (windowOf m E).M <
        scaledBoundary J eB (( -(windowOf m E).S).toNat)
    · rw [ite_eq_left hc]; decide
    · rw [ite_eq_right hc]; decide

/-! ### Fact 4: one rounding from `(M, S, sticky)` is `roundMag`'s

The emitted walk brackets the magnitude with `stkCmp`'s decisions and stops
inside the candidate's rounding interval; that is the nearest-even selection
`roundMag` makes, and the walk's control flow is the only part of the argument
not modelled here.  What this section states is the model of the path: the
magnitude the emitted conversion returns is `roundMag`'s on the lexeme's ticks,
after the two clamps, and the window's value is the lexeme's.

`tier3Mag` is that model.  The zero lexeme returns `+0`/`-0` before reading an
exponent (the emitted `if (!seen)`), and the clamps of fact 3 are read at the
window's lead. -/

/-- `roundMag` of zero is the zero code. -/
theorem roundMag_zero (D : Nat) (hD : 0 < D) : roundMag 0 D = .fin ⟨0, 0⟩ := by
  have hov : ¬ overflowTicks * D ≤ 0 := by
    intro h
    have hpos : 0 < overflowTicks := by
      unfold overflowTicks
      exact Nat.sub_pos_of_lt two_pow_2044_lt_2098
    have := Nat.mul_pos hpos hD
    omega
  have hbig : (0 : Nat) < D * 2 ^ 52 :=
    Nat.mul_pos hD (Nat.pow_pos (by decide))
  have hsub : subCode 0 D = ⟨0, 0⟩ := by
    dsimp only [subCode]
    rw [Nat.zero_div, Nat.zero_mod, ite_eq_left (show 2 * 0 < D by omega)]
  unfold roundMag
  rw [ite_eq_right hov, ite_eq_left hbig, hsub]

/-- The magnitude the emitted tier-3 conversion returns, modelled at the
specification's own single rounding: the zero lexeme, the two magnitude clamps,
and otherwise one nearest-even rounding of the lexeme's exact value. -/
def tier3Mag (d : Decimal) : Mag :=
  if d.mantissa = 0 then .fin ⟨0, 0⟩
  else
    if 309 ≤ (windowOf d.mantissa d.exponent).lead then .inf
    else if (windowOf d.mantissa d.exponent).lead ≤ -325 then .fin ⟨0, 0⟩
    else roundMag d.ticks.1 d.ticks.2

/-- **The emitted tier-3 magnitude is `roundMag`'s.**  The zero lexeme, the two
clamps (fact 3, read at the window's lead) and the final rounding agree with one
rounding of the lexeme's exact value: the model's magnitude is `roundMag` on the
lexeme's ticks. -/
theorem tier3Mag_eq_roundMag (d : Decimal) :
    tier3Mag d = roundMag d.ticks.1 d.ticks.2 := by
  unfold tier3Mag
  by_cases hm : d.mantissa = 0
  · rw [ite_eq_left hm]
    have hticks : d.ticks.1 = 0 := by
      unfold Decimal.ticks
      rw [hm]
      split <;> simp
    rw [hticks, roundMag_zero d.ticks.2 d.ticks_den_pos]
  · rw [ite_eq_right hm]
    have hm0 : 0 < d.mantissa := Nat.pos_of_ne_zero hm
    have hMT : magTicks d.mantissa d.exponent = d.ticks := rfl
    have hw := window_leadM hm0 d.exponent
    rw [hw]
    by_cases h1 : 309 ≤ leadM d.mantissa d.exponent
    · rw [ite_eq_left h1, ← hMT, roundMag_of_lead_ge hm0 h1]
    · rw [ite_eq_right h1]
      by_cases h2 : leadM d.mantissa d.exponent ≤ -325
      · rw [ite_eq_left h2, ← hMT, roundMag_of_lead_le hm0 h2]
      · rw [ite_eq_right h2]

/-- `overflowTicks` is the overflow threshold's midpoint
`(2 ^ 54 - 1) * 2 ^ 970` in ticks: `(2 ^ 54 - 1) * 2 ^ 2044`. -/
theorem overflowTicks_eq : overflowTicks = (2 ^ 54 - 1) * 2 ^ 2044 := by
  unfold overflowTicks
  calc (2 : Nat) ^ 2098 - 2 ^ 2044 = 2 ^ 2044 * 2 ^ 54 - 2 ^ 2044 := by
        rw [show (2 : Nat) ^ 2098 = 2 ^ 2044 * 2 ^ 54 by rw [← Nat.pow_add]]
    _ = 2 ^ 2044 * 2 ^ 54 - 2 ^ 2044 * 1 := by rw [Nat.mul_one]
    _ = 2 ^ 2044 * (2 ^ 54 - 1) := (Nat.mul_sub_left_distrib ..).symm
    _ = (2 ^ 54 - 1) * 2 ^ 2044 := Nat.mul_comm ..

/-- **`roundMag`'s own comparison is the walk's boundary comparison.**  The
overflow test `overflowTicks * D <= P` is the emitted walk's `stk_cmp` at the
boundary `(2 ^ 54 - 1) * 2 ^ 970` -- a boundary of the walk's `J * 2 ^ eB` shape
with `J < 2 ^ 54` and `eB >= -1075` -- so the test `roundMag` makes is one the
jam bit's scale argument covers. -/
theorem overflow_test_eq (m : Nat) (E : Int) :
    (overflowTicks * (magTicks m E).2 ≤ (magTicks m E).1) ↔
      ¬ valLtBoundary m E (2 ^ 54 - 1) 970 := by
  rw [overflowTicks_eq]
  by_cases hE : 0 ≤ E
  · have hP : (magTicks m E).1 = m * 10 ^ E.toNat * 2 ^ 1074 := by
      unfold magTicks
      rw [ite_eq_left hE]
    have hD : (magTicks m E).2 = 1 := by
      unfold magTicks
      rw [ite_eq_left hE]
    have hv : valLtBoundary m E (2 ^ 54 - 1) 970 ↔
        m * 10 ^ E.toNat < (2 ^ 54 - 1) * 2 ^ 970 := by
      unfold valLtBoundary
      rw [ite_eq_left hE, ite_eq_left (by decide : (0 : Int) ≤ (970 : Int))]
      rw [show ((970 : Int)).toNat = 970 from by decide]
    rw [hP, hD, Nat.mul_one, hv, Nat.not_lt]
    rw [show (2 ^ 54 - 1) * 2 ^ 2044
        = ((2 ^ 54 - 1) * 2 ^ 970) * 2 ^ 1074 by
      rw [show (2 : Nat) ^ 2044 = 2 ^ 970 * 2 ^ 1074 by rw [← Nat.pow_add]]
      ac_rfl]
    rw [show m * 10 ^ E.toNat * 2 ^ 1074 = (m * 10 ^ E.toNat) * 2 ^ 1074 by
      ac_rfl]
    exact ⟨fun h => Nat.le_of_mul_le_mul_right h (Nat.pow_pos (by decide)),
      fun h => Nat.mul_le_mul_right (2 ^ 1074) h⟩
  · have hP : (magTicks m E).1 = m * 2 ^ 1074 := by
      unfold magTicks
      rw [ite_eq_right hE]
    have hD : (magTicks m E).2 = 10 ^ E.natAbs := by
      unfold magTicks
      rw [ite_eq_right hE]
    have hv : valLtBoundary m E (2 ^ 54 - 1) 970 ↔
        m < (2 ^ 54 - 1) * 2 ^ 970 * 10 ^ E.natAbs := by
      unfold valLtBoundary
      rw [ite_eq_right hE, ite_eq_left (by decide : (0 : Int) ≤ (970 : Int))]
      rw [show ((970 : Int)).toNat = 970 from by decide]
    rw [hP, hD, hv, Nat.not_lt]
    rw [show (2 ^ 54 - 1) * 2 ^ 2044 * 10 ^ E.natAbs
        = ((2 ^ 54 - 1) * 2 ^ 970 * 10 ^ E.natAbs) * 2 ^ 1074 by
      rw [show (2 : Nat) ^ 2044 = 2 ^ 970 * 2 ^ 1074 by rw [← Nat.pow_add]]
      ac_rfl]
    exact ⟨fun h => Nat.le_of_mul_le_mul_right h (Nat.pow_pos (by decide)),
      fun h => Nat.mul_le_mul_right (2 ^ 1074) h⟩

/-- The emitted tier-3 result as the encoding: the magnitude above with the
lexeme's sign, in `strtodSpec`'s shape. -/
def tier3Binary (d : Decimal) : Binary64 := binOf (tier3Mag d) d.neg

/-- The emitted tier-3 conversion's magnitude is `strtodSpec`'s. -/
theorem tier3Binary_eq_strtodSpec (d : Decimal) :
    tier3Binary d = strtodSpec d := by
  unfold tier3Binary
  rw [tier3Mag_eq_roundMag, strtodSpec_eq_binOf]

/-- The emitted tier-3 conversion, as a `Bytes → Binary64` function: the reader
recovers the lexeme's decomposition (the emitted scanner's own reading), and the
sticky window's conversion follows. -/
def tier3Emitted (read : Bytes → Option Decimal) : Bytes → Binary64 :=
  fun bs =>
    match read bs with
    | some d => tier3Binary d
    | none => .inf false

/-- **The tier-3 clause holds.**  On every well-formed lexeme the first two
tiers declined, the emitted sticky conversion returns `strtodSpec`'s encoding:

* its window is the lexeme's value up to a tail the sticky bit alone carries
  (facts 1 and 2);
* its clamps are the nearest-even answer at the format's two edges (fact 3);
* its single rounding from `(M, S, sticky)` is `roundMag`'s (fact 4).

The reader is the emitted scanner's, taken as a parameter with its one
obligation, exactly as tier 1 takes it. -/
theorem emittedRefinesOn_tier3 (read : Bytes → Option Decimal)
    (kernelDecides : Decimal → Bool)
    (hread : ∀ d : Decimal, d.wellFormed → read d.lexeme = some d) :
    EmittedRefinesOn (tier3Emitted read) (fun d => Fallback d kernelDecides) := by
  intro d hwf _
  unfold tier3Emitted
  rw [hread d hwf]
  dsimp only
  exact tier3Binary_eq_strtodSpec d

/-! ### What is not proved

The statement of record is proved for the model below, and four things stay
outside it:

* **The walk's traversal.**  The emitted conversion moves a candidate one
  binary64 step at a time until the value lies in its rounding interval
  (`kernel/json/stage2.c:766-833`).  That loop is control flow over a
  well-ordered lattice, not a rounding rule: every decision it makes is one of
  the boundary comparisons proved exact here (`stkCmp_sticky_spec`,
  `overflow_test_eq`), and the rounding it stops on is `roundMag`'s selection.
  This module models the magnitude (`tier3Mag`) rather than the loop.

* **The reader.**  `to_double` reads the lexeme's bytes; the decomposition it
  accumulates is `Decimal.mantissa` and `Decimal.exponent`, which the window
  takes as given.  `read` is a parameter of the statement, with the one
  obligation that it recovers a well-formed lexeme's own decomposition --
  the same arrangement tier 1 uses, so the byte scan is not proved twice.

* **The scale hypothesis `eB + k >= 0`.**  `sticky_compare` and
  `stkCmp_sticky_spec` take it as a hypothesis, because the emitted `stk_shl`
  requires it.  The design comment derives it from the walk's proximity: the
  boundaries it compares are within two ulps of the value, so the shift
  `eB + 767 - f` is nonnegative (the worst case is `f = -308`, `eB = -1075`,
  shift `0`).  Fact 1 proves the static digit bound that makes the cleared
  boundary fit the window; the proximity estimate itself is not formalized.

* **The non-sticky comparison.**  `cmpExact` is the emitted `stk_cmp`'s
  cross-multiplied comparison with its nonnegative-`S` fold removed, so it is
  the same comparison by construction; this module proves its *sticky*
  sibling's specification (`stkCmp_sticky_spec`) and no separate lemma that
  `cmpExact`'s sign equals the true sign.  With the sticky bit clear there is
  no tail, so the claim is exact arithmetic rather than a jamming argument.
-/

/-! ### Checks

The window arithmetic on concrete magnitudes: the digit count, the drop at the
window's edge, the sticky bit, and the cleared boundary. -/

#guard stkDigits = 768
#guard ndig 1 = 1
#guard ndig 42 = 2
#guard ndig 1000 = 4
#guard ndig (10 ^ 769) = 770
#guard stkDrop 42 = 0
#guard stkDrop (10 ^ 769) = 2
#guard windowOf 42 0 = { M := 42, S := 0, sticky := false }
#guard (windowOf (10 ^ 769) 0).M = 10 ^ 767
#guard (windowOf (10 ^ 769) 0).sticky = false
#guard (windowOf (10 ^ 769 + 1) 0).sticky = true
#guard scaledBoundary 1 (-3) 3 = 125
#guard scaledBoundary 3 0 0 = 3
#guard cmpNat 3 5 = -1
#guard cmpNat 5 5 = 0
#guard cmpNat 5 3 = 1

-- The adapter's division-free comparison is the one `roundMag`'s subnormal
-- test reads: `2 ^ 52` against `1` is not below `2 ^ 52`, `1` against `2` is.
#guard ITree.Internal.divNatLtTwoPow (2 ^ 52) 1 52 = false
#guard ITree.Internal.divNatLtTwoPow 1 2 52 = true

/-! ### Axiom footprint

Every declaration is pinned.  The window, the comparison and the clamps are
integer arithmetic, so they are expected at `[propext]` or with no axioms; the
statement of record is a proposition over `strtodSpec`'s own definitions. -/
#print axioms LeanLLVM.StrtodTier3.stkDigits
#print axioms LeanLLVM.StrtodTier3.stkDigits_eq
#print axioms LeanLLVM.StrtodTier3.ndig
#print axioms LeanLLVM.StrtodTier3.ndig_pos
#print axioms LeanLLVM.StrtodTier3.ndig_spec
#print axioms LeanLLVM.StrtodTier3.ndig_eq_of_bounds
#print axioms LeanLLVM.StrtodTier3.stkDrop
#print axioms LeanLLVM.StrtodTier3.windowOf
#print axioms LeanLLVM.StrtodTier3.windowOf_M
#print axioms LeanLLVM.StrtodTier3.windowOf_S
#print axioms LeanLLVM.StrtodTier3.windowOf_sticky
#print axioms LeanLLVM.StrtodTier3.windowOf_sticky_iff
#print axioms LeanLLVM.StrtodTier3.window_decomp
#print axioms LeanLLVM.StrtodTier3.window_tail_lt
#print axioms LeanLLVM.StrtodTier3.window_M_lt
#print axioms LeanLLVM.StrtodTier3.window_M_ge
#print axioms LeanLLVM.StrtodTier3.ndig_window_M
#print axioms LeanLLVM.StrtodTier3.StkWindow
#print axioms LeanLLVM.StrtodTier3.StkWindow.lead
#print axioms LeanLLVM.StrtodTier3.window_lead
#print axioms LeanLLVM.StrtodTier3.five_pow_307_lt
#print axioms LeanLLVM.StrtodTier3.pow_two_1024_le_ten_309
#print axioms LeanLLVM.StrtodTier3.pow_two_1075_lt_ten_324
#print axioms LeanLLVM.StrtodTier3.boundary_num_lt
#print axioms LeanLLVM.StrtodTier3.boundary_int_lt
#print axioms LeanLLVM.StrtodTier3.magTicks
#print axioms LeanLLVM.StrtodTier3.magTicks_eq_ticks
#print axioms LeanLLVM.StrtodTier3.magTicks_den_pos
#print axioms LeanLLVM.StrtodTier3.leadM
#print axioms LeanLLVM.StrtodTier3.window_leadM
#print axioms LeanLLVM.StrtodTier3.leadM_nonneg_form
#print axioms LeanLLVM.StrtodTier3.natAbs_of_neg
#print axioms LeanLLVM.StrtodTier3.ticks_ge_of_lead_ge
#print axioms LeanLLVM.StrtodTier3.two_pow_2044_lt_2098
#print axioms LeanLLVM.StrtodTier3.lt_mul_right_iff
#print axioms LeanLLVM.StrtodTier3.roundMag_of_lead_ge
#print axioms LeanLLVM.StrtodTier3.roundMag_of_lead_le
#print axioms LeanLLVM.StrtodTier3.jam_compare
#print axioms LeanLLVM.StrtodTier3.scaledBoundary
#print axioms LeanLLVM.StrtodTier3.valLtBoundary
#print axioms LeanLLVM.StrtodTier3.valEqBoundary
#print axioms LeanLLVM.StrtodTier3.scaledBoundary_mul_int
#print axioms LeanLLVM.StrtodTier3.scaledBoundary_mul_fraction
#print axioms LeanLLVM.StrtodTier3.sticky_compare
#print axioms LeanLLVM.StrtodTier3.sticky_no_tie
#print axioms LeanLLVM.StrtodTier3.cmpNat
#print axioms LeanLLVM.StrtodTier3.cmpExact
#print axioms LeanLLVM.StrtodTier3.stkCmp
#print axioms LeanLLVM.StrtodTier3.leadM_window_S
#print axioms LeanLLVM.StrtodTier3.sticky_drop_pos
#print axioms LeanLLVM.StrtodTier3.sticky_tail_pos
#print axioms LeanLLVM.StrtodTier3.sticky_S_neg
#print axioms LeanLLVM.StrtodTier3.sticky_E_neg
#print axioms LeanLLVM.StrtodTier3.stkCmp_sticky_spec
#print axioms LeanLLVM.StrtodTier3.roundMag_zero
#print axioms LeanLLVM.StrtodTier3.tier3Mag
#print axioms LeanLLVM.StrtodTier3.tier3Mag_eq_roundMag
#print axioms LeanLLVM.StrtodTier3.overflowTicks_eq
#print axioms LeanLLVM.StrtodTier3.overflow_test_eq
#print axioms LeanLLVM.StrtodTier3.tier3Binary
#print axioms LeanLLVM.StrtodTier3.tier3Binary_eq_strtodSpec
#print axioms LeanLLVM.StrtodTier3.tier3Emitted
#print axioms LeanLLVM.StrtodTier3.emittedRefinesOn_tier3

end LeanLLVM.StrtodTier3
