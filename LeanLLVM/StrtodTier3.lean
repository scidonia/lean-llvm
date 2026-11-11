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
   emitted code's own comparison `stkCmp`.  The other branch is exact rather
   than jammed: with the sticky bit clear nothing was dropped, the lexeme is
   the decimal `M * 10 ^ S`, and `cmpExact_spec` proves `cmpExact` is the sign
   of `M * 10 ^ S - J * 2 ^ eB` with both denominators cleared;
   `stkCmp_nosticky_spec` reads that at the lexeme's own coordinates, so both
   branches of the emitted `stk_cmp` are specified.

   The shift the sticky branch performs, `eB + 767 - f`, is `shift_of_near`:
   given the two facts the walk supplies about a boundary it compares -- the
   exponent is at least `-1075`, and the boundary is at least half the value --
   the boundary is an integer at the window's scale, and the constant is sharp
   at `f = -307`.  `sticky_shift` reads it at the window and
   `stkCmp_sticky_spec'` composes it with `stkCmp_sticky_spec`; what the
   proximity estimate itself rests on is in `What is not proved` below.

3. **The clamps are the nearest-even answer.**  `lead >= 309` is `+-inf`
   because `10 ^ 309` is above the overflow threshold, and `lead <= -325` is
   `+-0` because anything below `10 ^ -324` is below half the smallest
   subnormal, and `0` is the even one there.  `roundMag_of_lead_ge` and
   `roundMag_of_lead_le` prove both against `roundMag`.

4. **One rounding from `(M, S, sticky)` is `roundMag`'s.**  The emitted walk
   brackets the value with `stk_cmp`'s decisions and stops inside the
   candidate's rounding interval, which is the nearest-even selection
   `roundMag` makes.  This module proves the comparisons exact on both branches
   (facts 1 and 2), the clamps (fact 3), the shift the sticky branch performs
   (`shift_of_near`), and that `roundMag`'s own overflow test is one of the
   walk's boundary comparisons (`overflow_test_eq`), so every decision the walk
   makes is the one this module proves exact.  The model of the path,
   `tier3Mag`, is those clamps and that one rounding, and
   `tier3Mag_eq_roundMag` proves it on `roundMag`.

5. **The walk's traversal.**  The loop itself is modelled over bit patterns
   (`walkStep`, from `stage2.c:769-813`): the decode, the boundary selection,
   the step of one pattern, and the two escapes.  `bound2_up`, `bound2_down`
   and `bound2_overflow` prove its boundaries are the `stk_cmp` boundaries the
   code forms, and `valLtBoundary_iff_cmpWalk` reads each of them as a sign.
   The stopping criterion is the rounding interval (`inInterval`), and it
   selects one candidate: `inInterval_uniq`.  `step_fin_stop_self` and
   `step_fin_stop_of_mem` make the body stop exactly at that candidate,
   `step_fin_stop_next` and `step_fin_stop_pred` make the two tie branches hand
   a midpoint to the even significand, `step_fin_move_next` and
   `step_fin_move_pred` make each step move toward the interval, and
   `stop_fin_interval`, `stop_zero_only` and `step_top_stop` read a stop back
   as membership.  What still separates the loop from `tier3Mag` is the
   identification of this lattice with `roundMag`'s, and the recursion down the
   distance to the answer; see `What is not proved` below.

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
window's scale; `sticky_shift` derives it from the two facts the walk supplies
about a boundary, and `stkCmp_sticky_spec'` composes the two. -/
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

/-! ### Fact 1's other half: the scale hypothesis `eB + k >= 0`

`stkCmp`'s sticky branch compares `M` with the boundary cleared to the window's
scale, `scaledBoundary J eB k = J * 5 ^ k * 2 ^ (eB + k)`, which is an integer
only when `eB + k` is nonnegative.  That is the design comment's proximity
estimate (`kernel/json/stage2.c:512`): the boundaries the walk compares against
are within two ulps of the value, so `f - eB <= 767`, and the worst case -- a
value in the low binades near `2 ^ -1021`, whose down-midpoint is
`(2 ^ 54 - 1) * 2 ^ -1075` -- has `f = -308`, `eB = -1075`, and shift `0`.

What is proved here is the arithmetic: `shift_of_near` derives `eB >= f - 767`
from exactly the two facts the walk supplies about a boundary it compares --
`eB >= -1075`, which every `stk_cmp` boundary of the emitted loop has, and
`B >= V / 2`, which is what "within two ulps of the value" gives.  `sticky_shift`
reads that at the window (`S = f - 767`), and `stkCmp_sticky_spec'` composes it
with `stkCmp_sticky_spec`.  The proximity estimate itself is a property of the
emitted starting approximation `top * 10 ^ e10`, whose error is a bound on
rounded binary64 multiplication and division -- the platform's arithmetic, which
this tree does not model.  See `What is not proved` below. -/

/-- The value is at most the boundary: the two strict comparisons of
`valLtBoundary` and `valEqBoundary`, together. -/
def valLeqBoundary (m : Nat) (E : Int) (J : Nat) (eB : Int) : Prop :=
  valLtBoundary m E J eB ∨ valEqBoundary m E J eB

/-- The sharp numeric constant of the scale estimate: `5 ^ 307 < 2 ^ 713`.  A
boundary within the window's scale has its power of two above the value's lead,
and this is the inequality that forces it. -/
theorem five_pow_307_lt_713 : (5 : Nat) ^ 307 < 2 ^ 713 := by decide

/-- The nearness premise at a negative boundary exponent, for a nonnegative
decimal exponent: `V <= 2 * J * 2 ^ eB` as an integer inequality. -/
theorem near_ticks_nonneg {m : Nat} {E : Int} {J : Nat} {eB : Int}
    (hE : 0 ≤ E) (heB : eB < 0) (h : valLeqBoundary m E (2 * J) eB) :
    m * 10 ^ E.toNat * 2 ^ eB.natAbs ≤ 2 * J := by
  rcases h with h | h
  · unfold valLtBoundary at h
    rw [ite_eq_left hE, ite_eq_right (by omega : ¬ 0 ≤ eB)] at h
    exact Nat.le_of_lt h
  · unfold valEqBoundary at h
    rw [ite_eq_left hE, ite_eq_right (by omega : ¬ 0 ≤ eB)] at h
    exact Nat.le_of_eq h

/-- The nearness premise at a negative boundary exponent, for a negative decimal
exponent. -/
theorem near_ticks_neg {m : Nat} {E : Int} {J : Nat} {eB : Int}
    (hE : E < 0) (heB : eB < 0) (h : valLeqBoundary m E (2 * J) eB) :
    m * 2 ^ eB.natAbs ≤ 2 * J * 10 ^ E.natAbs := by
  rcases h with h | h
  · unfold valLtBoundary at h
    rw [ite_eq_right (by omega : ¬ 0 ≤ E), ite_eq_right (by omega : ¬ 0 ≤ eB)] at h
    exact Nat.le_of_lt h
  · unfold valEqBoundary at h
    rw [ite_eq_right (by omega : ¬ 0 ≤ E), ite_eq_right (by omega : ¬ 0 ≤ eB)] at h
    exact Nat.le_of_eq h

/-- A nonnegative lead's `toNat` is the value's digit count less one plus the
exponent. -/
theorem lead_toNat_nonneg {m : Nat} {E : Int} (hE : 0 ≤ E) :
    (leadM m E).toNat = ndig m - 1 + E.toNat := by
  rw [leadM_nonneg_form hE, Int.toNat_natCast]

/-- A nonnegative lead clears to a difference of naturals. -/
theorem nat_sub_lead {f : Int} (hf : 0 ≤ f) (hle : f.toNat ≤ 768) :
    ((768 : Int) - f).toNat = 768 - f.toNat := by
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ 768 - f), Int.natCast_sub hle,
    Int.toNat_of_nonneg hf]
  rfl

/-- The two-pow bound `2 ^ 460 ≤ 2 ^ (768 - f)` for a lead at most 308. -/
theorem two_pow_le_pow_lead {f : Nat} (hf : f ≤ 308) : 2 ^ 460 ≤ 2 ^ (768 - f) :=
  Nat.pow_le_pow_right (by decide) (by omega)

/-- **The scale hypothesis from a boundary at the window's scale.**  Writing
`f` for the magnitude's decimal lead, a boundary `J * 2 ^ eB` with `J < 2 ^ 54`,
`eB >= -1075`, and at least half the value (`valLeqBoundary` at `2 * J`) has
`eB >= f - 767`: the shift `eB + 767 - f` the emitted comparison performs is a
right shift.

The case split is the format's own.  At or below `f = -308` the exponent floor
alone decides it: `f - 767 <= -1075 <= eB`.  Above it the value's decade and the
boundary's size force the inequality, and the constant is sharp: at `f = -307`
the contradiction needs `5 ^ 307 < 2 ^ 713`, which is what `five_pow_307_lt_713`
supplies, and at `f = -308` the worst case the design comment names
(`f = -308`, `eB = -1075`) has the shift exactly `0`. -/
theorem shift_of_near {m : Nat} {E : Int} {J : Nat} {eB : Int}
    (hm : 0 < m) (hJ : J < 2 ^ 54) (heB : -1075 ≤ eB)
    (hlead : leadM m E ≤ 308) (hnear : valLeqBoundary m E (2 * J) eB) :
    leadM m E - 767 ≤ eB := by
  by_cases hlow : leadM m E ≤ -308
  · omega
  · have hf : -307 ≤ leadM m E := by omega
    by_cases hfin : leadM m E - 767 ≤ eB
    · exact hfin
    · exfalso
      have hlt : eB < leadM m E - 767 := by omega
      have heBneg : eB < 0 := by omega
      have hshift : ((768 : Int) - leadM m E) ≤ (eB.natAbs : Int) := by
        have h := natAbs_of_neg heBneg
        omega
      have hJ2 : 2 * J < 2 ^ 55 := by
        calc 2 * J < 2 * 2 ^ 54 := Nat.mul_lt_mul_of_pos_left hJ (by decide)
          _ = 2 ^ 55 := by decide
      -- the leading bound `2 ^ 460 <= 10 ^ f * 2 ^ (768 - f)` for a lead at most 308
      have hsmall_pow : ∀ (t : Nat), t ≤ 308 →
          2 ^ 460 ≤ 10 ^ t * 2 ^ (768 - t) := by
        intro t ht
        calc 2 ^ 460 = 1 * 2 ^ 460 := (Nat.one_mul _).symm
          _ ≤ 10 ^ t * 2 ^ 460 :=
              Nat.mul_le_mul (Nat.succ_le_of_lt (Nat.pow_pos (by decide))) (Nat.le_refl _)
          _ ≤ 10 ^ t * 2 ^ (768 - t) := Nat.mul_le_mul_left _ (two_pow_le_pow_lead ht)
      by_cases hE : 0 ≤ E
      · -- a nonnegative decimal exponent: the leading bound is exact
        have hf0 : (0 : Int) ≤ leadM m E := by
          rw [leadM_nonneg_form hE]; omega
        have hfn := lead_toNat_nonneg (m := m) hE
        have hexp : 768 - (leadM m E).toNat ≤ eB.natAbs := by
          have h1 : ((768 : Int) - leadM m E).toNat = 768 - (leadM m E).toNat :=
            nat_sub_lead hf0 (by omega)
          rw [← h1]
          exact Int.toNat_le_toNat hshift
        have hlo : 10 ^ (leadM m E).toNat ≤ m * 10 ^ E.toNat := by
          rw [hfn, Nat.pow_add]
          exact Nat.mul_le_mul_right _ (ndig_spec hm).1
        have hn := near_ticks_nonneg hE heBneg hnear
        have hsmall : 10 ^ (leadM m E).toNat * 2 ^ (768 - (leadM m E).toNat) < 2 ^ 55 :=
          lt_of_le_of_lt
            (Nat.mul_le_mul hlo (Nat.pow_le_pow_right (by decide) hexp))
            (lt_of_le_of_lt hn hJ2)
        exact absurd (le_trans (hsmall_pow _ (by omega)) hsmall.le)
          (Nat.not_le.mpr (two_pow_lt_of_lt (by decide)))
      · have hEneg : E < 0 := by omega
        by_cases hf0 : 0 ≤ leadM m E
        · -- a nonnegative lead with a negative exponent
          have hfsum : (leadM m E).toNat + E.natAbs = ndig m - 1 := by
            apply Int.natCast_inj.mp
            rw [Int.natCast_add, Int.toNat_of_nonneg hf0, natAbs_of_neg hEneg,
              Int.natCast_sub (ndig_pos m)]
            unfold leadM
            omega
          have hexp : 768 - (leadM m E).toNat ≤ eB.natAbs := by
            have h1 : ((768 : Int) - leadM m E).toNat = 768 - (leadM m E).toNat :=
              nat_sub_lead hf0 (by omega)
            rw [← h1]
            exact Int.toNat_le_toNat hshift
          have hlo : 10 ^ (leadM m E).toNat * 10 ^ E.natAbs ≤ m := by
            rw [← Nat.pow_add, hfsum]
            exact (ndig_spec hm).1
          have hn := near_ticks_neg hEneg heBneg hnear
          have hsmall : 10 ^ (leadM m E).toNat * 2 ^ (768 - (leadM m E).toNat) < 2 ^ 55 := by
            have h5 : 10 ^ (leadM m E).toNat * 10 ^ E.natAbs * 2 ^ (768 - (leadM m E).toNat)
                < 2 ^ 55 * 10 ^ E.natAbs := by
              calc 10 ^ (leadM m E).toNat * 10 ^ E.natAbs * 2 ^ (768 - (leadM m E).toNat)
                  ≤ m * 2 ^ (768 - (leadM m E).toNat) := Nat.mul_le_mul_right _ hlo
                _ ≤ m * 2 ^ eB.natAbs :=
                    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
                _ ≤ 2 * J * 10 ^ E.natAbs := hn
                _ < 2 ^ 55 * 10 ^ E.natAbs :=
                    Nat.mul_lt_mul_of_pos_right hJ2 (Nat.pow_pos (by decide))
            rw [show 10 ^ (leadM m E).toNat * 10 ^ E.natAbs * 2 ^ (768 - (leadM m E).toNat)
                = 10 ^ (leadM m E).toNat * 2 ^ (768 - (leadM m E).toNat) * 10 ^ E.natAbs
                from by ac_rfl] at h5
            exact LeanLLVM.JSON.lt_of_mul_lt_mul_right h5
          exact absurd (le_trans (hsmall_pow _ (by omega)) hsmall.le)
            (Nat.not_le.mpr (two_pow_lt_of_lt (by decide)))
        · -- both exponents negative: the subnormal-scale case
          have hfneg : leadM m E < 0 := by omega
          have hgnn : (0 : Int) ≤ -leadM m E := by omega
          let g : Nat := (-leadM m E).toNat
          have hg : (g : Int) = -leadM m E := Int.toNat_of_nonneg hgnn
          have hg307 : g ≤ 307 := by
            have h : (g : Int) ≤ ((307 : Nat) : Int) := by omega
            exact Int.toNat_le_toNat h
          have hexp : 768 + g ≤ eB.natAbs := by
            have h1 : ((768 : Int) - leadM m E).toNat = 768 + g := by
              rw [show ((768 : Int) - leadM m E) = ((768 + g : Nat) : Int) from by
                push_cast; omega, Int.toNat_natCast]
            rw [← h1]
            exact Int.toNat_le_toNat hshift
          have hEabs : E.natAbs = g + (ndig m - 1) := by
            apply Int.natCast_inj.mp
            rw [Int.natCast_add, natAbs_of_neg hEneg, hg, Int.natCast_sub (ndig_pos m)]
            unfold leadM
            omega
          have hlo : 10 ^ E.natAbs ≤ m * 10 ^ g := by
            rw [hEabs, Nat.pow_add, Nat.mul_comm]
            exact Nat.mul_le_mul_right _ (ndig_spec hm).1
          have hn := near_ticks_neg hEneg heBneg hnear
          have hcut : 2 ^ (768 + g) ≤ 2 * J * 10 ^ g := by
            have hchain : 10 ^ E.natAbs * 2 ^ (768 + g)
                ≤ (2 * J * 10 ^ E.natAbs) * 10 ^ g := by
              calc 10 ^ E.natAbs * 2 ^ (768 + g)
                  ≤ m * 10 ^ g * 2 ^ (768 + g) := Nat.mul_le_mul_right _ hlo
                _ ≤ m * 10 ^ g * 2 ^ eB.natAbs :=
                    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
                _ = m * 2 ^ eB.natAbs * 10 ^ g := by ac_rfl
                _ ≤ (2 * J * 10 ^ E.natAbs) * 10 ^ g := Nat.mul_le_mul_right _ hn
            have h' : 2 ^ (768 + g) * 10 ^ E.natAbs ≤ (2 * J * 10 ^ g) * 10 ^ E.natAbs := by
              rw [Nat.mul_comm (2 ^ (768 + g)) (10 ^ E.natAbs)]
              calc 10 ^ E.natAbs * 2 ^ (768 + g)
                  ≤ (2 * J * 10 ^ E.natAbs) * 10 ^ g := hchain
                _ = (2 * J * 10 ^ g) * 10 ^ E.natAbs := by ac_rfl
            exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))
          have hstep2 : 2 ^ (713 + g) ≤ 10 ^ g := by
            have hpow : (2:Nat) ^ (768 + g) = 2 ^ (713 + g) * 2 ^ 55 := by
              rw [← Nat.pow_add]; congr 1; omega
            have h : 2 ^ (713 + g) * 2 ^ 55 ≤ 2 ^ 55 * 10 ^ g := by
              rw [← hpow]
              calc 2 ^ (768 + g) ≤ 2 * J * 10 ^ g := hcut
                _ ≤ 2 ^ 55 * 10 ^ g := Nat.mul_le_mul_right _ (Nat.le_of_lt hJ2)
            have h' : 2 ^ (713 + g) * 2 ^ 55 ≤ 10 ^ g * 2 ^ 55 := by
              rw [Nat.mul_comm (2 ^ 55) (10 ^ g)] at h
              exact h
            exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))
          have h710 : 2 ^ 713 ≤ 5 ^ g := by
            have h := hstep2
            rw [show (2:Nat) ^ (713 + g) = 2 ^ 713 * 2 ^ g from Nat.pow_add ..] at h
            have h10 : (10:Nat) ^ g = 5 ^ g * 2 ^ g := by
              rw [show (10:Nat) = 2 * 5 from rfl, Nat.mul_pow, Nat.mul_comm]
            have h' : 2 ^ 713 * 2 ^ g ≤ 5 ^ g * 2 ^ g := by
              rwa [h10] at h
            exact Nat.le_of_mul_le_mul_right h' (Nat.pow_pos (by decide))
          have hg5 : 5 ^ g ≤ 5 ^ 307 := Nat.pow_le_pow_right (by decide) hg307
          exact absurd h710 (Nat.not_le.mpr (lt_of_le_of_lt hg5 five_pow_307_lt_713))


/-- **The scale hypothesis, at the window.**  For a sticky window the retained
decimal's exponent is the lead less 767 (`leadM_window_S`), so
`shift_of_near`'s `eB >= f - 767` is exactly the nonnegativity of
`eB + (-S)`: the emitted `stk_shl` shifts right. -/
theorem sticky_shift {m : Nat} {E : Int} (hst : (windowOf m E).sticky = true)
    (hlead : leadM m E ≤ 308) {J : Nat} {eB : Int} (hJ : J < 2 ^ 54)
    (heB : -1075 ≤ eB) (hnear : valLeqBoundary m E (2 * J) eB) :
    0 ≤ eB + ((-(windowOf m E).S).toNat : Int) := by
  have htail : m % 10 ^ stkDrop m ≠ 0 := (windowOf_sticky_iff m E).1 hst
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h, Nat.zero_mod] at htail
      exact htail rfl
    · exact h
  have hs := sticky_drop_pos E hst
  have hSneg := sticky_S_neg hst hlead
  have hf := shift_of_near hm hJ heB hlead hnear
  have hSe : -(windowOf m E).S = 767 - leadM m E := by
    rw [leadM_window_S E hs]
    omega
  rw [Int.toNat_of_nonneg (by omega : (0 : Int) ≤ -(windowOf m E).S), hSe]
  omega

/-- **The sticky comparison, with the shift derived rather than assumed.**  The
emitted comparison at a sticky window is the exact one, given the two facts the
walk supplies about the boundary it compares: its exponent is at least `-1075`,
and it is no smaller than half the value. -/
theorem stkCmp_sticky_spec' {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = true) (hlead : leadM m E ≤ 308)
    {J : Nat} {eB : Int} (hJ : J < 2 ^ 54) (heB : -1075 ≤ eB)
    (hnear : valLeqBoundary m E (2 * J) eB) :
    (stkCmp (windowOf m E) J eB = -1 ↔ valLtBoundary m E J eB) ∧
      stkCmp (windowOf m E) J eB ≠ 0 :=
  stkCmp_sticky_spec hst hlead (sticky_shift hst hlead hJ heB hnear)

/-! ### Fact 2, the other branch: a clear sticky bit is the exact comparison

With the sticky bit clear no digit was dropped, so the lexeme is the decimal
`M * 10 ^ S` exactly and there is no tail to jam.  `cmpExact` is the emitted
`stk_cmp`'s cross-multiplied comparison with the nonnegative-`S` fold removed --
one integer comparison of `M * 10 ^ S` against `J * 2 ^ eB`, both denominators
cleared -- and `cmpExact_spec` is its meaning: `-1` is below, `0` is equal, `1`
is above.  `cmpCross` is that same comparison at an arbitrary relation, so the
transfer lemma below serves both `valLtBoundary` and `valEqBoundary`;
`valLtBoundary_mul_ten` and `valEqBoundary_mul_ten` read a value in the lexeme's
own coordinates (`m = M * 10 ^ s`, `S = E + s`) as the same value, and
`stkCmp_nosticky_spec` composes the two into the emitted comparison's second
branch. -/

/-- The comparison of `M * 10 ^ S` with `J * 2 ^ eB`, cross-multiplied so that
both sides are integers: each side carries the other's denominator.  `cmpExact`
is this comparison at the order, and `valLtBoundary` and `valEqBoundary` are its
two relations. -/
def cmpCross (rel : Nat → Nat → Prop) (M : Nat) (S : Int) (J : Nat) (eB : Int) : Prop :=
  rel (M * (if 0 ≤ S then 10 ^ S.toNat else 1)
       * (if 0 ≤ eB then 1 else 2 ^ eB.natAbs))
    (J * (if 0 ≤ eB then 2 ^ eB.toNat else 1)
       * (if 0 ≤ S then 1 else 10 ^ S.natAbs))

/-- `cmpCross` at the strict order is the boundary comparison. -/
theorem cmpCross_lt (M : Nat) (S : Int) (J : Nat) (eB : Int) :
    valLtBoundary M S J eB ↔ cmpCross (· < ·) M S J eB := by
  simp only [cmpCross, valLtBoundary]
  by_cases hS : 0 ≤ S
  · by_cases he : 0 ≤ eB
    · simp only [ite_eq_left hS, ite_eq_left he, Nat.mul_one]
    · simp only [ite_eq_left hS, ite_eq_right he, Nat.mul_one]
  · by_cases he : 0 ≤ eB
    · simp only [ite_eq_right hS, ite_eq_left he, Nat.mul_one]
    · simp only [ite_eq_right hS, ite_eq_right he, Nat.mul_one]

/-- `cmpCross` at equality is the boundary equality. -/
theorem cmpCross_eq (M : Nat) (S : Int) (J : Nat) (eB : Int) :
    valEqBoundary M S J eB ↔ cmpCross (· = ·) M S J eB := by
  simp only [cmpCross, valEqBoundary]
  by_cases hS : 0 ≤ S
  · by_cases he : 0 ≤ eB
    · simp only [ite_eq_left hS, ite_eq_left he, Nat.mul_one]
    · simp only [ite_eq_left hS, ite_eq_right he, Nat.mul_one]
  · by_cases he : 0 ≤ eB
    · simp only [ite_eq_right hS, ite_eq_left he, Nat.mul_one]
    · simp only [ite_eq_right hS, ite_eq_right he, Nat.mul_one]

/-- The three-way comparison of naturals is the order it reads: below is `-1`,
equal is `0`, and `1` is neither below nor equal. -/
theorem cmpNat_spec (a b : Nat) :
    (cmpNat a b = -1 ↔ a < b) ∧ (cmpNat a b = 0 ↔ a = b) ∧
      (cmpNat a b = 1 ↔ ¬ a < b ∧ a ≠ b) := by
  unfold cmpNat
  by_cases h : a < b
  · rw [ite_eq_left h]
    exact ⟨⟨fun _ => h, fun _ => rfl⟩,
      ⟨fun hc => absurd hc (by decide : (-1 : Int) ≠ 0), fun hc => by omega⟩,
      ⟨fun hc => absurd hc (by decide : (-1 : Int) ≠ 1), fun hc => absurd h hc.1⟩⟩
  · rw [ite_eq_right h]
    by_cases h2 : a = b
    · subst h2
      rw [ite_eq_left rfl]
      exact ⟨⟨fun hc => absurd hc (by decide : (0 : Int) ≠ -1), fun hc => by omega⟩,
        ⟨fun _ => rfl, fun _ => rfl⟩,
        ⟨fun hc => absurd hc (by decide : (0 : Int) ≠ 1), fun hc => (hc.2 rfl).elim⟩⟩
    · rw [ite_eq_right h2]
      have hba : b < a := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h) (fun hba => h2 hba.symm)
      exact ⟨⟨fun hc => absurd hc (by decide : (1 : Int) ≠ -1), fun hlt => absurd hlt h⟩,
        ⟨fun hc => absurd hc (by decide : (1 : Int) ≠ 0), fun he => absurd he h2⟩,
        ⟨fun _ => ⟨h, h2⟩, fun _ => rfl⟩⟩

/-- **`cmpExact` computes exactly what it is a comparison of.**  Its result is
the sign of `V - B` for `V = M * 10 ^ S` and `B = J * 2 ^ eB`, in the
cross-multiplied integer form: `-1` is below, `0` is equal, `1` is above.  Both
denominators are cleared exactly, so with the sticky bit clear the emitted
`stk_cmp` carries no approximation. -/
theorem cmpExact_spec (M : Nat) (S : Int) (J : Nat) (eB : Int) :
    (cmpExact M S J eB = -1 ↔ valLtBoundary M S J eB) ∧
      (cmpExact M S J eB = 0 ↔ valEqBoundary M S J eB) ∧
      (cmpExact M S J eB = 1 ↔ ¬ valLtBoundary M S J eB ∧
        ¬ valEqBoundary M S J eB) := by
  obtain ⟨h1, h2, h3⟩ := cmpNat_spec
    (M * (if 0 ≤ S then 10 ^ S.toNat else 1)
       * (if 0 ≤ eB then 1 else 2 ^ eB.natAbs))
    (J * (if 0 ≤ eB then 2 ^ eB.toNat else 1)
       * (if 0 ≤ S then 1 else 10 ^ S.natAbs))
  exact ⟨h1.trans (cmpCross_lt M S J eB).symm,
    h2.trans (cmpCross_eq M S J eB).symm,
    h3.trans (by rw [cmpCross_lt, cmpCross_eq]; exact Iff.rfl)⟩


/-- A nonnegative exponent clears: `S.toNat` is the two terms' sum. -/
theorem toNat_of_nonneg_add {S E : Int} {s : Nat} (hS : S = E + (s : Int))
    (hE : 0 ≤ E) : S.toNat = E.toNat + s := by
  apply Int.natCast_inj.mp
  rw [Int.natCast_add, Int.toNat_of_nonneg hE, Int.toNat_of_nonneg (by omega : (0 : Int) ≤ S)]
  exact hS

/-- Digits dropped out of a magnitude rejoin its exponent: a negative exponent
below a nonnegative one. -/
theorem nat_add_natAbs_of_mixed {S E : Int} {s : Nat} (hS : S = E + (s : Int))
    (hE : E < 0) (hS0 : 0 ≤ S) : s = S.toNat + E.natAbs := by
  apply Int.natCast_inj.mp
  rw [Int.natCast_add, Int.toNat_of_nonneg hS0, natAbs_of_neg hE]
  omega

/-- Digits dropped out of a magnitude rejoin its exponent: both exponents
negative. -/
theorem nat_natAbs_add_of_neg {S E : Int} {s : Nat} (hS : S = E + (s : Int))
    (hE : E < 0) (hS0 : S < 0) : s + S.natAbs = E.natAbs := by
  apply Int.natCast_inj.mp
  rw [Int.natCast_add, natAbs_of_neg hE, natAbs_of_neg hS0]
  omega

/-- **The cross-multiplied comparison only reads the value.**  Writing `s`
digits of the significand out and adding them to the exponent multiplies both
sides by the same positive power of ten, and each of the six sign
combinations of `(E, S)` and `eB` is that cancellation. -/
theorem cmpCross_mul_ten {rel : Nat → Nat → Prop}
    (hrel : ∀ a b c : Nat, 0 < c → (rel (a * c) (b * c) ↔ rel a b))
    {M s : Nat} {S E : Int} {J : Nat} {eB : Int} (hS : S = E + (s : Int)) :
    cmpCross rel (M * 10 ^ s) E J eB ↔ cmpCross rel M S J eB := by
  have hpow : ∀ n : Nat, 0 < 10 ^ n := fun n => Nat.pow_pos (by decide)
  by_cases hE : 0 ≤ E
  · have hSn : S.toNat = E.toNat + s := toNat_of_nonneg_add hS hE
    have hS0 : 0 ≤ S := by omega
    by_cases he : 0 ≤ eB
    · simp only [cmpCross, ite_eq_left hE, ite_eq_left hS0, ite_eq_left he, Nat.mul_one]
      rw [hSn, Nat.pow_add]
      rw [show M * 10 ^ s * 10 ^ E.toNat = M * (10 ^ E.toNat * 10 ^ s) from by ac_rfl]
    · simp only [cmpCross, ite_eq_left hE, ite_eq_left hS0, ite_eq_right he, Nat.mul_one]
      rw [hSn, Nat.pow_add]
      rw [show M * 10 ^ s * 10 ^ E.toNat * 2 ^ eB.natAbs
        = M * (10 ^ E.toNat * 10 ^ s) * 2 ^ eB.natAbs from by ac_rfl]
  · have hE' : E < 0 := by omega
    by_cases hS0 : 0 ≤ S
    · have hs : s = S.toNat + E.natAbs := nat_add_natAbs_of_mixed hS hE' hS0
      by_cases he : 0 ≤ eB
      · simp only [cmpCross, ite_eq_right hE, ite_eq_left hS0, ite_eq_left he, Nat.mul_one]
        rw [← hrel (M * 10 ^ S.toNat) (J * 2 ^ eB.toNat) (10 ^ E.natAbs) (hpow _)]
        rw [show M * 10 ^ s = M * 10 ^ S.toNat * 10 ^ E.natAbs from by
          rw [hs, Nat.pow_add]; ac_rfl]
      · simp only [cmpCross, ite_eq_right hE, ite_eq_left hS0, ite_eq_right he, Nat.mul_one]
        rw [← hrel (M * 10 ^ S.toNat * 2 ^ eB.natAbs) J (10 ^ E.natAbs) (hpow _)]
        rw [show M * 10 ^ s * 2 ^ eB.natAbs
          = M * 10 ^ S.toNat * 2 ^ eB.natAbs * 10 ^ E.natAbs from by
          rw [hs, Nat.pow_add]; ac_rfl]
    · have hS0' : S < 0 := by omega
      have hs : s + S.natAbs = E.natAbs := nat_natAbs_add_of_neg hS hE' hS0'
      by_cases he : 0 ≤ eB
      · simp only [cmpCross, ite_eq_right hE, ite_eq_right hS0, ite_eq_left he, Nat.mul_one]
        rw [← hrel M (J * 2 ^ eB.toNat * 10 ^ S.natAbs) (10 ^ s) (hpow _)]
        rw [show J * 2 ^ eB.toNat * 10 ^ E.natAbs
          = J * 2 ^ eB.toNat * 10 ^ S.natAbs * 10 ^ s from by
          rw [← hs, Nat.pow_add]; ac_rfl]
      · simp only [cmpCross, ite_eq_right hE, ite_eq_right hS0, ite_eq_right he, Nat.mul_one]
        rw [← hrel (M * 2 ^ eB.natAbs) (J * 10 ^ S.natAbs) (10 ^ s) (hpow _)]
        rw [show M * 10 ^ s * 2 ^ eB.natAbs = M * 2 ^ eB.natAbs * 10 ^ s from by ac_rfl]
        rw [show J * 10 ^ E.natAbs = J * 10 ^ S.natAbs * 10 ^ s from by
          rw [← hs, Nat.pow_add]; ac_rfl]

/-- The boundary comparison is a function of the value alone: dropping `s`
digits of a magnitude into its exponent leaves it unchanged. -/
theorem valLtBoundary_mul_ten {M s : Nat} {S E : Int} {J : Nat} {eB : Int}
    (hS : S = E + (s : Int)) :
    valLtBoundary (M * 10 ^ s) E J eB ↔ valLtBoundary M S J eB := by
  simp only [cmpCross_lt]
  exact cmpCross_mul_ten (rel := (· < ·))
    (fun a b c hc => ⟨fun h => lt_of_mul_lt_mul_right h, fun h => Nat.mul_lt_mul_of_pos_right h hc⟩) hS

/-- The boundary equality is a function of the value alone. -/
theorem valEqBoundary_mul_ten {M s : Nat} {S E : Int} {J : Nat} {eB : Int}
    (hS : S = E + (s : Int)) :
    valEqBoundary (M * 10 ^ s) E J eB ↔ valEqBoundary M S J eB := by
  simp only [cmpCross_eq]
  exact cmpCross_mul_ten (rel := (· = ·))
    (fun a b c hc => ⟨fun h => Nat.mul_right_cancel (hc) h,
      fun h => by rw [h]⟩) hS

/-- A clear sticky bit means nothing was dropped. -/
theorem nosticky_no_tail {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = false) : m % 10 ^ stkDrop m = 0 := by
  rcases Nat.eq_zero_or_pos (m % 10 ^ stkDrop m) with h | h
  · exact h
  · exfalso
    have h1 := (windowOf_sticky_iff m E).2 (Nat.pos_iff_ne_zero.mp h)
    rw [hst] at h1
    exact absurd h1 (by decide : ¬ ((false : Bool) = true))

/-- **The emitted comparison with the sticky bit clear is the exact
comparison.**  With no digit past the window the lexeme is the decimal
`M * 10 ^ S` exactly, so the emitted `stk_cmp` -- which clears both
denominators (`cmpExact_spec`) -- returns `-1` exactly when the value is below
the boundary and `0` exactly when it is equal, never a guess. -/
theorem stkCmp_nosticky_spec {m : Nat} {E : Int}
    (hst : (windowOf m E).sticky = false) {J : Nat} {eB : Int} :
    (stkCmp (windowOf m E) J eB = -1 ↔ valLtBoundary m E J eB) ∧
      (stkCmp (windowOf m E) J eB = 0 ↔ valEqBoundary m E J eB) := by
  have hzero := nosticky_no_tail hst
  have hdec : (windowOf m E).M * 10 ^ stkDrop m = m := by
    rw [windowOf_M]
    have h := window_decomp m
    rw [hzero, Nat.add_zero] at h
    exact h.symm
  have hS : (windowOf m E).S = E + (stkDrop m : Int) := windowOf_S m E
  have hcc := cmpExact_spec (windowOf m E).M (windowOf m E).S J eB
  have hno : ¬ ((windowOf m E).sticky = true) := by rw [hst]; decide
  rw [stkCmp, ite_eq_right hno]
  exact ⟨hcc.1.trans ((valLtBoundary_mul_ten hS).symm.trans (by rw [hdec])),
    hcc.2.1.trans ((valEqBoundary_mul_ten hS).symm.trans (by rw [hdec]))⟩

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

The statement of record is proved for the model below, and three things stay
outside it:

* **The walk's traversal.**  The loop is modelled (`walkStep`, `walkTicks`,
  `bound2`, `inInterval`, from `kernel/json/stage2.c:766-833`), and the model's
  decision half is proved: the boundaries it compares against are the `stk_cmp`
  boundaries this module specifies (`bound2_up`, `bound2_down`,
  `bound2_overflow`, `valLtBoundary_iff_cmpWalk`), the interval it stops in is a
  single candidate's (`inInterval_uniq`, `inInterval_not_top`), the body stops
  exactly there (`step_fin_stop_self`, `step_fin_stop_of_mem`), a midpoint tie
  is handed to the even significand (`step_fin_stop_next`,
  `step_fin_stop_pred`), and every step moves toward the interval
  (`step_fin_move_next`, `step_fin_move_pred`).

  Two steps join that model to the specification's answer, and both are proved
  below.  **The identification**: `binade_eq_of_tick_bounds` reads the binade
  search at a pattern whose tick value is at or below the value and whose
  successor's is above it, and `walk_lattice_eq` adds `ulp`, `lo` and `hi`, so
  the specification's lattice and the ladder are one lattice.  **The target and
  the descent**: `inInterval_roundMag` proves `inInterval P d (bitsOf c)` for
  `roundMag P d = .fin c`, `walkLoop_stops_of_interval` runs the body to that
  candidate on the measure `(tgt - b) + (b - tgt)`, `walkLoop_top` climbs to the
  infinity pattern over the threshold, and `walkLoop_computes` states both as
  one -- the loop halts at the pattern `roundMag`'s answer is encoded at, which
  is `tier3Mag`'s on the lexeme's ticks (`walkLoop_computes_tier3Mag`).

* **The reader.**  `to_double` reads the lexeme's bytes; the decomposition it
  accumulates is `Decimal.mantissa` and `Decimal.exponent`, which the window
  takes as given.  `read` is a parameter of the statement, with the one
  obligation that it recovers a well-formed lexeme's own decomposition --
  the same arrangement tier 1 uses, so the byte scan is not proved twice.

* **The proximity estimate behind the scale hypothesis.**  The hypothesis
  `eB + ((-S).toNat) >= 0` that `stkCmp_sticky_spec` takes is now derived, by
  `stkCmp_sticky_spec'`, from two facts about the boundary being compared:
  `eB >= -1075` and `B >= V / 2`.  `shift_of_near` is the arithmetic, and it is
  sharp: at `f = -307` it needs exactly `5 ^ 307 < 2 ^ 713`, and the design
  comment's worst case `f = -308`, `eB = -1075` has shift `0`.  What is not
  formalized is that the emitted walk's boundaries have those two properties.
  The first is a reading of the loop's own shapes: the boundaries it forms are
  `(2 * m +- 1, e - 1)`, the constant `(2 ^ 53 - 1, -1075)`, the half-ulp
  `(1, -1075)` and the overflow threshold `(2 ^ 54 - 1, 970)`, and the only
  `e - 2` case is a binade bottom above the subnormal range, so every one is at
  least `-1075`.  The second follows from the starting approximation: it is
  `top * 10 ^ e10`, whose error after rounding each multiplication and division
  by a power of ten is a few ulps, so each comparison the loop makes is at a
  boundary within a few ulps of the value.  Two ulps are far below the `V / 2`
  the premise asks for, which allows `2 ^ 51` ulps of slack at the tightest
  point.  An ulp bound on that starting point is a bound on rounded binary64
  multiplication and division (`kernel/json/stage2.c:748-766`): the platform's
  arithmetic, which this tree does not model -- the same class of
  outside-the-tree step tier 1 names for its single operation.
-/

/-! ### The ladder of bit patterns

`kernel/json/stage2.c:768` starts the walk at the pattern of the double
`dbits(d)` and steps it one pattern at a time (`b++` at lines 794 and 797,
`b--` at lines 809 and 812) until a boundary test stops it (lines 770-782 for
the two ends of the format, and 788, 792, 795, 807, 810 in the body).  The
pattern's fields are the format's own: `(b >> 52) & 0x7ff` is the biased
exponent, `b & ((1 << 52) - 1)` the trailing significand, and a zero exponent
field means the leading bit is implicit. -/

/-- The significand field's width, `1 << 52`. -/
def sigBits : Nat := 2 ^ 52

/-- `0x7ff0000000000000`, the pattern of an infinity: the largest exponent
field with a zero significand. -/
def infBits : Nat := 2047 * 2 ^ 52

/-- `0x7fefffffffffffff`, the largest finite magnitude's pattern. -/
def maxBits : Nat := infBits - 1

theorem sigBits_eq : sigBits = 2 ^ 52 := rfl

theorem infBits_eq : infBits = 2047 * 2 ^ 52 := rfl

theorem maxBits_eq : maxBits = 2046 * 2 ^ 52 + (2 ^ 52 - 1) := by
  have hsplit : (2047 : Nat) * 2 ^ 52 = 2046 * 2 ^ 52 + 2 ^ 52 := by
    rw [show (2047 : Nat) = 2046 + 1 from by decide, Nat.add_mul, Nat.one_mul]
  simp only [maxBits, infBits]
  omega

theorem infBits_pos : 0 < infBits := by
  simp only [infBits]
  exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))

theorem maxBits_lt_infBits : maxBits < infBits := by
  have hpos : 0 < infBits := by
    simp only [infBits]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  simp only [maxBits]
  omega

theorem maxBits_succ : maxBits + 1 = infBits := by
  have hpos : 0 < infBits := by
    simp only [infBits]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  simp only [maxBits]
  omega

/-- The biased exponent field: the pattern's bits 52 to 62. -/
def walkExp (b : Nat) : Nat := (b / 2 ^ 52) % 2048

/-- The trailing significand field: the pattern's low 52 bits. -/
def walkFrac (b : Nat) : Nat := b % 2 ^ 52

/-- The significand the pattern denotes: the fraction field for a subnormal,
with the implicit leading bit for a normal. -/
def walkMant (b : Nat) : Nat :=
  if walkExp b = 0 then walkFrac b else 2 ^ 52 + walkFrac b

/-- The encoding the pattern denotes, in the specification's own fields. -/
def walkCode (b : Nat) : Code := ⟨walkExp b, walkMant b⟩

/-- The pattern's magnitude in ticks.  A pattern past the finite range reads
through the same formula, so a pattern of the infinity field is `2 ^ 2098` in
ticks -- the tick value of `2 ^ 1024`, which is what makes the ladder
continuous across the top of the finite range. -/
def walkTicks (b : Nat) : Nat := (walkCode b).ticks

/-- The ladder's step at `b`: `t (b + 1) - t b`, one ulp of the binade the
pattern sits in. -/
def walkGap (b : Nat) : Nat := if walkExp b = 0 then 1 else 2 ^ (walkExp b - 1)

/-! #### Quotient and remainder at a step

The pattern's exponent and fraction fields are `b`'s quotient and remainder at
`2 ^ 52`, so a step of the pattern moves the fraction by one and carries into
the exponent at the field's edge. -/

theorem div_add_one_of_mod_lt {a n : Nat} (hn : 0 < n) (h : a % n + 1 < n) :
    (a + 1) / n = a / n := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hdec : (a % n + 1) + n * (a / n) = a + 1 := by
    rw [show (a % n + 1) + n * (a / n) = (n * (a / n) + a % n) + 1 from by ac_rfl, h1]
  rw [← hdec, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt h, Nat.zero_add]

theorem mod_add_one_of_mod_lt {a n : Nat} (h : a % n + 1 < n) :
    (a + 1) % n = a % n + 1 := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hdec : (a % n + 1) + n * (a / n) = a + 1 := by
    rw [show (a % n + 1) + n * (a / n) = (n * (a / n) + a % n) + 1 from by ac_rfl, h1]
  rw [← hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

theorem div_add_one_of_mod_top {a n : Nat} (hn : 1 < n) (h : a % n = n - 1) :
    (a + 1) / n = a / n + 1 := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hmul : n * (a / n + 1) = a + 1 := by
    rw [Nat.mul_add, Nat.mul_one]
    have h2 : n * (a / n) + n = n * (a / n) + a % n + 1 := by omega
    rw [h2, h1]
  rw [← hmul, Nat.mul_div_right (a / n + 1) (by omega : 0 < n)]

theorem mod_add_one_of_mod_top {a n : Nat} (hn : 0 < n) (h : a % n = n - 1) :
    (a + 1) % n = 0 := by
  have hmod : (a + 1) % n = (a % n + 1) % n := by
    rw [Nat.add_mod]
    rcases Nat.lt_or_ge 1 n with h2 | h2
    · rw [Nat.mod_eq_of_lt h2]
    · have h1 : n = 1 := by omega
      subst h1
      simp only [Nat.mod_one, Nat.add_zero]
  rw [hmod, h, Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]

theorem mod_sub_one_of_mod_pos {a n : Nat} (hn : 0 < n) (h : 0 < a % n) :
    (a - 1) % n = a % n - 1 := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have key : (a % n - 1) + n * (a / n) + 1 = a := by
    rw [show (a % n - 1) + n * (a / n) + 1 = (a % n - 1 + 1) + n * (a / n) from by
        ac_rfl,
      Nat.sub_add_cancel (by omega : 1 ≤ a % n), Nat.add_comm, h1]
  have hdec : (a % n - 1) + n * (a / n) = a - 1 := Nat.eq_sub_of_add_eq key
  rw [← hdec, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (by have := Nat.mod_lt a hn; omega)]

theorem div_sub_one_of_mod_pos {a n : Nat} (hn : 0 < n) (ha : 0 < a) (h : 0 < a % n) :
    (a - 1) / n = a / n := by
  have hm := mod_sub_one_of_mod_pos hn h
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have h2 : n * ((a - 1) / n) + (a - 1) % n = a - 1 := Nat.div_add_mod (a - 1) n
  rw [hm] at h2
  have h2' : n * ((a - 1) / n) + a % n = a := by omega
  have hq : n * ((a - 1) / n) = n * (a / n) := by omega
  exact Nat.eq_of_mul_eq_mul_left hn hq

theorem mul_div_exact {a n : Nat} (h1 : n * (a / n) + a % n = a) (h : a % n = 0) :
    n * (a / n) = a := by omega

theorem div_sub_one_of_mod_zero {a n : Nat} (hn : 1 < n) (ha : 0 < a) (h : a % n = 0) :
    (a - 1) / n = a / n - 1 := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hmul : n * (a / n) = a := mul_div_exact h1 h
  have hq : 0 < a / n := by
    rcases Nat.eq_zero_or_pos (a / n) with hz | hp
    · rw [hz, Nat.mul_zero] at hmul
      omega
    · exact hp
  have hnmul : n * (a / n - 1) = a - n := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, hmul]
  have hle : n ≤ a := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (a / n) := Nat.mul_le_mul_left n hq
      _ = a := hmul
  have hdec : n - 1 + n * (a / n - 1) = a - 1 := by
    rw [hnmul]
    omega
  rw [← hdec, Nat.add_mul_div_left _ _ (by omega : 0 < n),
    Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem mod_sub_one_of_mod_zero {a n : Nat} (hn : 1 < n) (ha : 0 < a) (h : a % n = 0) :
    (a - 1) % n = n - 1 := by
  have h1 : n * (a / n) + a % n = a := Nat.div_add_mod a n
  have hmul : n * (a / n) = a := mul_div_exact h1 h
  have hq : 0 < a / n := by
    rcases Nat.eq_zero_or_pos (a / n) with hz | hp
    · rw [hz, Nat.mul_zero] at hmul
      omega
    · exact hp
  have hnmul : n * (a / n - 1) = a - n := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, hmul]
  have hle : n ≤ a := by
    calc n = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (a / n) := Nat.mul_le_mul_left n hq
      _ = a := hmul
  have hdec : n - 1 + n * (a / n - 1) = a - 1 := by
    rw [hnmul]
    omega
  rw [← hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem walkExp_lt (b : Nat) : walkExp b < 2048 :=
  Nat.mod_lt _ (by decide)

theorem walkFrac_lt (b : Nat) : walkFrac b < 2 ^ 52 :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem walkGap_pos (b : Nat) : 0 < walkGap b := by
  unfold walkGap
  split
  · decide
  · exact Nat.pow_pos (by decide)

theorem walkMant_eq_zero {b : Nat} (h : walkExp b = 0) : walkMant b = walkFrac b := by
  simp only [walkMant, h, reduceIte]

theorem walkMant_eq_normal {b : Nat} (h : walkExp b ≠ 0) :
    walkMant b = 2 ^ 52 + walkFrac b := by
  simp only [walkMant, h, reduceIte]

theorem walkTicks_eq_zero {b : Nat} (h : walkExp b = 0) : walkTicks b = walkFrac b := by
  simp only [walkTicks, walkCode, Code.ticks, h, reduceIte, walkMant]

theorem walkTicks_eq_normal {b : Nat} (h : walkExp b ≠ 0) :
    walkTicks b = (2 ^ 52 + walkFrac b) * 2 ^ (walkExp b - 1) := by
  simp only [walkTicks, walkCode, Code.ticks, h, reduceIte, walkMant]

theorem walkGap_eq_zero {b : Nat} (h : walkExp b = 0) : walkGap b = 1 := by
  simp only [walkGap, h, reduceIte]

theorem walkGap_eq_normal {b : Nat} (h : walkExp b ≠ 0) :
    walkGap b = 2 ^ (walkExp b - 1) := by
  simp only [walkGap, h, reduceIte]

theorem walkExp_def_of_lt {b : Nat} (hb : b < infBits) : walkExp b = b / 2 ^ 52 := by
  unfold walkExp
  rw [Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
  calc b < 2047 * 2 ^ 52 := hb
    _ ≤ 2048 * 2 ^ 52 := Nat.mul_le_mul_right _ (by decide)

theorem walkExp_lt_2047 {b : Nat} (hb : b < infBits) : walkExp b < 2047 := by
  rw [walkExp_def_of_lt hb, Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))]
  simpa only [infBits] using hb

theorem walk_bits_decomp {b : Nat} (hb : b < infBits) :
    walkExp b * 2 ^ 52 + walkFrac b = b := by
  have h := Nat.div_add_mod b (2 ^ 52)
  rw [Nat.mul_comm] at h
  rw [walkExp_def_of_lt hb]
  simpa only [walkFrac] using h

theorem walkFrac_succ_of_frac_lt {b : Nat} (h : walkFrac b < 2 ^ 52 - 1) :
    walkFrac (b + 1) = walkFrac b + 1 := by
  have hlt : walkFrac b + 1 < 2 ^ 52 := by
    have := walkFrac_lt b
    omega
  exact mod_add_one_of_mod_lt hlt

theorem walkExp_succ_of_frac_lt {b : Nat} (h : walkFrac b < 2 ^ 52 - 1) :
    walkExp (b + 1) = walkExp b := by
  have hlt : walkFrac b + 1 < 2 ^ 52 := by
    have := walkFrac_lt b
    omega
  unfold walkExp
  rw [div_add_one_of_mod_lt (by decide : 0 < 2 ^ 52) hlt]

theorem walkFrac_succ_of_frac_top {b : Nat} (h : walkFrac b = 2 ^ 52 - 1) :
    walkFrac (b + 1) = 0 := by
  simpa only [walkFrac] using mod_add_one_of_mod_top (by decide : 0 < 2 ^ 52) h

theorem walkExp_succ_of_frac_top {b : Nat} (h : walkFrac b = 2 ^ 52 - 1)
    (hb : b < infBits) : walkExp (b + 1) = walkExp b + 1 := by
  have hlt : b / 2 ^ 52 + 1 < 2048 := by
    have hle := walkExp_lt_2047 hb
    rw [walkExp_def_of_lt hb] at hle
    omega
  unfold walkExp
  rw [div_add_one_of_mod_top (by decide : 1 < 2 ^ 52) h,
    mod_add_one_of_mod_lt (by omega : b / 2 ^ 52 % 2048 + 1 < 2048)]

theorem walkFrac_pred_of_frac_pos {b : Nat} (h : 0 < walkFrac b) :
    walkFrac (b - 1) = walkFrac b - 1 := by
  simpa only [walkFrac] using mod_sub_one_of_mod_pos (by decide : 0 < 2 ^ 52) h

theorem walkExp_pred_of_frac_pos {b : Nat} (h : 0 < walkFrac b) (hb : b < infBits) :
    walkExp (b - 1) = walkExp b := by
  have hpos : walkFrac b ≤ b := by
    have := walk_bits_decomp hb
    have hz : 0 ≤ walkExp b * 2 ^ 52 := Nat.zero_le _
    omega
  unfold walkExp
  rw [div_sub_one_of_mod_pos (by decide : 0 < 2 ^ 52) (by omega) h]

theorem walkFrac_pred_of_frac_zero {b : Nat} (h0 : 0 < b) (h : walkFrac b = 0) :
    walkFrac (b - 1) = 2 ^ 52 - 1 := by
  simpa only [walkFrac] using mod_sub_one_of_mod_zero (by decide : 1 < 2 ^ 52) h0 h

theorem walkExp_pred_of_frac_zero {b : Nat} (h0 : 0 < b) (h : walkFrac b = 0)
    (hb : b < infBits) : walkExp (b - 1) = walkExp b - 1 := by
  have hpos : 0 < walkExp b := by
    rcases Nat.eq_zero_or_pos (walkExp b) with hz | hp
    · exfalso
      have := walk_bits_decomp hb
      rw [h, hz, Nat.zero_mul, Nat.zero_add] at this
      omega
    · exact hp
  have hb2048 : b / 2 ^ 52 < 2048 := by
    rw [← walkExp_def_of_lt hb]
    exact walkExp_lt b
  unfold walkExp
  rw [div_sub_one_of_mod_zero (by decide : 1 < 2 ^ 52) (by omega) h,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem walkExp_pred_le_2047 {b : Nat} (hb : b < infBits) (h0 : 0 < b) :
    walkExp (b - 1) < 2047 := by
  by_cases hz : walkFrac b = 0
  · rw [walkExp_pred_of_frac_zero h0 hz hb]
    have := walkExp_lt_2047 hb
    omega
  · have hp : 0 < walkFrac b := Nat.pos_of_ne_zero hz
    rw [walkExp_pred_of_frac_pos hp hb]
    exact walkExp_lt_2047 hb

theorem two_pow_53_eq : (2 : Nat) ^ 53 = 2 ^ 52 + 2 ^ 52 := by
  rw [show 53 = 52 + 1 from by decide, Nat.pow_succ, Nat.mul_two]

theorem two_pow_52_add_pred : 2 ^ 52 + (2 ^ 52 - 1) = 2 ^ 53 - 1 := by
  rw [← Nat.add_sub_assoc (by decide : 1 ≤ 2 ^ 52), two_pow_53_eq]

theorem walkFrac_lt_pred {b : Nat} (h : walkFrac b ≠ 2 ^ 52 - 1) :
    walkFrac b < 2 ^ 52 - 1 := by
  have h1 : 2 ^ 52 - 1 + 1 = 2 ^ 52 := Nat.sub_one_add_one (by decide)
  have h2 : walkFrac b < 2 ^ 52 := walkFrac_lt b
  rw [← h1] at h2
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h2) h

theorem two_pow_mul_shift {be : Nat} (h : 0 < be) :
    2 ^ 52 * 2 ^ be = 2 ^ 53 * 2 ^ (be - 1) := by
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

theorem walkTicks_succ {b : Nat} (hb : b < infBits) :
    walkTicks (b + 1) = walkTicks b + walkGap b := by
  by_cases htop : walkFrac b = 2 ^ 52 - 1
  · have hexp : walkExp (b + 1) = walkExp b + 1 := walkExp_succ_of_frac_top htop hb
    have hfr : walkFrac (b + 1) = 0 := walkFrac_succ_of_frac_top htop
    have hne : walkExp (b + 1) ≠ 0 := by rw [hexp]; exact Nat.succ_ne_zero _
    rw [walkTicks_eq_normal hne, hfr, Nat.add_zero, hexp,
      show walkExp b + 1 - 1 = walkExp b from by omega]
    by_cases h0 : walkExp b = 0
    · rw [walkGap_eq_zero h0, walkTicks_eq_zero h0, h0, Nat.pow_zero, Nat.mul_one,
        htop]
      exact (Nat.sub_one_add_one (by decide : (2 : Nat) ^ 52 ≠ 0)).symm
    · rw [walkGap_eq_normal h0, walkTicks_eq_normal h0, htop, two_pow_52_add_pred,
        two_pow_mul_shift (Nat.pos_of_ne_zero h0)]
      rw [← Nat.succ_mul]
      exact congrArg (· * 2 ^ (walkExp b - 1)) (Nat.succ_eq_add_one (2 ^ 53 - 1) ▸ by rfl)
  · have hlt : walkFrac b < 2 ^ 52 - 1 := walkFrac_lt_pred htop
    have hexp : walkExp (b + 1) = walkExp b := walkExp_succ_of_frac_lt hlt
    have hfr : walkFrac (b + 1) = walkFrac b + 1 := walkFrac_succ_of_frac_lt hlt
    by_cases h0 : walkExp b = 0
    · rw [walkTicks_eq_zero (by rw [hexp]; exact h0), hfr, walkTicks_eq_zero h0,
        walkGap_eq_zero h0]
    · rw [walkTicks_eq_normal (by rw [hexp]; exact h0), hfr, hexp,
        walkTicks_eq_normal h0, walkGap_eq_normal h0,
        show 2 ^ 52 + (walkFrac b + 1) = (2 ^ 52 + walkFrac b) + 1 from by ac_rfl,
        Nat.add_mul, Nat.one_mul]

theorem walkTicks_pred {b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkTicks b = walkTicks (b - 1) + walkGap (b - 1) := by
  have hstep := walkTicks_succ (b := b - 1) (by omega : b - 1 < infBits)
  rwa [Nat.sub_add_cancel h0] at hstep


/-! #### The significand's parity across a step -/

theorem add_sub_one_of_lt {c r : Nat} (h : 0 < r) : c + (r - 1) = c + r - 1 := by omega

theorem two_pow_52_mod_two : 2 ^ 52 % 2 = 0 := by decide

theorem two_pow_52_add_mod_two (x : Nat) : (2 ^ 52 + x) % 2 = x % 2 := by
  rw [Nat.add_mod, two_pow_52_mod_two, Nat.zero_add,
    Nat.mod_eq_of_lt (Nat.mod_lt x (by decide))]

theorem two_pow_52_pred_mod_two : (2 ^ 52 - 1) % 2 = 1 := by decide

theorem two_pow_53_pred_mod_two : (2 ^ 53 - 1) % 2 = 1 := by decide

theorem two_pow_54_eq : (2 : Nat) ^ 54 = 2 ^ 53 + 2 ^ 53 := by
  rw [show 54 = 53 + 1 from by decide, Nat.pow_succ, Nat.mul_two]

theorem two_pow_2098_eq : (2 : Nat) ^ 2098 = 2 ^ 53 * 2 ^ 2045 := by
  rw [← Nat.pow_add]

theorem walkMant_succ {b : Nat} (hb : b < infBits) :
    walkMant (b + 1) = walkMant b + 1 ∨ walkMant (b + 1) = 2 ^ 52 := by
  by_cases htop : walkFrac b = 2 ^ 52 - 1
  · right
    have hexp : walkExp (b + 1) = walkExp b + 1 := walkExp_succ_of_frac_top htop hb
    have hfr : walkFrac (b + 1) = 0 := walkFrac_succ_of_frac_top htop
    have hne : walkExp (b + 1) ≠ 0 := by rw [hexp]; exact Nat.succ_ne_zero _
    rw [walkMant_eq_normal hne, hfr, Nat.add_zero]
  · left
    have hlt : walkFrac b < 2 ^ 52 - 1 := walkFrac_lt_pred htop
    have hexp : walkExp (b + 1) = walkExp b := walkExp_succ_of_frac_lt hlt
    have hfr : walkFrac (b + 1) = walkFrac b + 1 := walkFrac_succ_of_frac_lt hlt
    by_cases h0 : walkExp b = 0
    · rw [walkMant_eq_zero (by rw [hexp]; exact h0), walkMant_eq_zero h0, hfr]
    · rw [walkMant_eq_normal (by rw [hexp]; exact h0), walkMant_eq_normal h0, hfr]
      ac_rfl

theorem walkMant_pred {b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkMant (b - 1) = walkMant b - 1 ∨ walkMant (b - 1) = 2 ^ 53 - 1 := by
  by_cases hz : walkFrac b = 0
  · have hexp : walkExp (b - 1) = walkExp b - 1 := walkExp_pred_of_frac_zero h0 hz hb
    have hfr : walkFrac (b - 1) = 2 ^ 52 - 1 := walkFrac_pred_of_frac_zero h0 hz
    by_cases hb1 : walkExp b = 1
    · left
      have hne : walkExp (b - 1) = 0 := by rw [hexp, hb1]
      have hbne : walkExp b ≠ 0 := by omega
      rw [walkMant_eq_zero hne, hfr, walkMant_eq_normal hbne, hz, Nat.add_zero]
    · right
      have hbne : walkExp b ≠ 0 := by
        intro hz0
        exfalso
        have hdec := walk_bits_decomp hb
        rw [hz0, hz, Nat.zero_mul, Nat.zero_add] at hdec
        omega
      have hne : walkExp (b - 1) ≠ 0 := by rw [hexp]; omega
      rw [walkMant_eq_normal hne, hfr]
      exact two_pow_52_add_pred
  · have hp : 0 < walkFrac b := Nat.pos_of_ne_zero hz
    left
    have hexp : walkExp (b - 1) = walkExp b := walkExp_pred_of_frac_pos hp hb
    have hfr : walkFrac (b - 1) = walkFrac b - 1 := walkFrac_pred_of_frac_pos hp
    by_cases h0' : walkExp b = 0
    · rw [walkMant_eq_zero (by rw [hexp]; exact h0'), walkMant_eq_zero h0', hfr]
    · rw [walkMant_eq_normal (by rw [hexp]; exact h0'), walkMant_eq_normal h0', hfr,
        add_sub_one_of_lt hp]

theorem walkMant_succ_even {b : Nat} (hb : b < infBits) (h : walkMant b % 2 ≠ 0) :
    walkMant (b + 1) % 2 = 0 := by
  rcases walkMant_succ hb with h1 | h1
  · rw [h1]; omega
  · rw [h1, two_pow_52_mod_two]

theorem walkMant_succ_not_both_even {b : Nat} (hb : b < infBits) :
    ¬ (walkMant b % 2 = 0 ∧ walkMant (b + 1) % 2 = 0) := by
  rintro ⟨h1, h2⟩
  by_cases htop : walkFrac b = 2 ^ 52 - 1
  · have hexp : walkExp (b + 1) = walkExp b + 1 := walkExp_succ_of_frac_top htop hb
    have hfr : walkFrac (b + 1) = 0 := walkFrac_succ_of_frac_top htop
    have hne : walkExp (b + 1) ≠ 0 := by rw [hexp]; exact Nat.succ_ne_zero _
    rw [walkMant_eq_normal hne, hfr, Nat.add_zero] at h2
    by_cases h0 : walkExp b = 0
    · rw [walkMant_eq_zero h0, htop] at h1
      rw [two_pow_52_pred_mod_two] at h1
      exact absurd h1 (by decide)
    · rw [walkMant_eq_normal h0, htop, two_pow_52_add_pred] at h1
      rw [two_pow_53_pred_mod_two] at h1
      exact absurd h1 (by decide)
  · have hlt : walkFrac b < 2 ^ 52 - 1 := walkFrac_lt_pred htop
    have hexp : walkExp (b + 1) = walkExp b := walkExp_succ_of_frac_lt hlt
    have hfr : walkFrac (b + 1) = walkFrac b + 1 := walkFrac_succ_of_frac_lt hlt
    by_cases h0 : walkExp b = 0
    · rw [walkMant_eq_zero h0] at h1
      rw [walkMant_eq_zero (by rw [hexp]; exact h0), hfr] at h2
      omega
    · rw [walkMant_eq_normal h0, two_pow_52_add_mod_two] at h1
      rw [walkMant_eq_normal (by rw [hexp]; exact h0), hfr,
        two_pow_52_add_mod_two] at h2
      omega

theorem walkMant_pred_even {b : Nat} (hb : b < infBits)
    (h : walkMant b % 2 ≠ 0) : walkMant (b - 1) % 2 = 0 := by
  by_cases hz : walkFrac b = 0
  · exfalso
    by_cases hb1 : walkExp b = 0
    · rw [walkMant_eq_zero hb1, hz] at h
      exact h (by decide)
    · rw [walkMant_eq_normal hb1, hz, Nat.add_zero, two_pow_52_mod_two] at h
      exact h rfl
  · have hp : 0 < walkFrac b := Nat.pos_of_ne_zero hz
    have hexp : walkExp (b - 1) = walkExp b := walkExp_pred_of_frac_pos hp hb
    have hfr : walkFrac (b - 1) = walkFrac b - 1 := walkFrac_pred_of_frac_pos hp
    by_cases h0' : walkExp b = 0
    · have hne' : walkExp (b - 1) = 0 := by rw [hexp, h0']
      rw [walkMant_eq_zero hne', hfr]
      rw [walkMant_eq_zero h0'] at h
      omega
    · have hne' : walkExp (b - 1) ≠ 0 := by rw [hexp]; omega
      rw [walkMant_eq_normal hne', hfr, two_pow_52_add_mod_two]
      rw [walkMant_eq_normal h0'] at h
      rw [two_pow_52_add_mod_two] at h
      omega

/-! #### The ladder is strictly increasing -/

theorem walkTicks_lt_succ {b : Nat} (hb : b < infBits) :
    walkTicks b < walkTicks (b + 1) := by
  rw [walkTicks_succ hb]
  have := walkGap_pos b
  omega

theorem walkTicks_le_of_le {b b' : Nat} (h : b ≤ b') (hb' : b' ≤ infBits) :
    walkTicks b ≤ walkTicks b' := by
  induction b' using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.lt_or_ge b n with hlt | hge
    · have hstep : walkTicks (n - 1) < walkTicks n := by
        have hs := walkTicks_lt_succ (b := n - 1) (by omega : n - 1 < infBits)
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
      have hrec := ih (n - 1) (by omega) (by omega) (by omega)
      omega
    · have hbn : n = b := by omega
      subst hbn
      exact Nat.le_refl _

theorem walkTicks_lt_of_lt {b b' : Nat} (h : b < b') (hb' : b' ≤ infBits) :
    walkTicks b < walkTicks b' := by
  have h1 : walkTicks b < walkTicks (b + 1) := walkTicks_lt_succ (by omega)
  have h2 : walkTicks (b + 1) ≤ walkTicks b' := walkTicks_le_of_le (by omega) hb'
  omega

/-- Twice the midpoint above `b`: `t b + t (b + 1)`. -/
def upTwice (b : Nat) : Nat := walkTicks b + walkTicks (b + 1)

/-- Twice the midpoint below `b`: `t (b - 1) + t b`. -/
def downTwice (b : Nat) : Nat := walkTicks (b - 1) + walkTicks b

theorem downTwice_succ (b : Nat) : downTwice (b + 1) = upTwice b := by
  simp only [downTwice, upTwice, Nat.succ_sub_one]

theorem upTwice_lt_of_lt {b b' : Nat} (h : b < b') (hb' : b' < infBits) :
    upTwice b < upTwice b' := by
  unfold upTwice
  exact Nat.add_lt_add (walkTicks_lt_of_lt h (by omega))
    (walkTicks_lt_of_lt (by omega) (by omega))

theorem upTwice_le_of_le {b b' : Nat} (h : b ≤ b') (hb' : b' < infBits) :
    upTwice b ≤ upTwice b' := by
  rcases Nat.eq_or_lt_of_le h with rfl | hlt
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (upTwice_lt_of_lt hlt hb')

theorem walkExp_infBits : walkExp infBits = 2047 := by
  unfold walkExp infBits
  rw [Nat.mul_comm, Nat.mul_div_right _ (Nat.pow_pos (by decide)),
    Nat.mod_eq_of_lt (by decide)]

theorem walkFrac_infBits : walkFrac infBits = 0 := by
  unfold walkFrac infBits
  rw [Nat.mul_comm, Nat.mul_mod_right]

theorem walkTicks_infBits : walkTicks infBits = 2 ^ 2098 := by
  rw [walkTicks_eq_normal (by rw [walkExp_infBits]; decide), walkFrac_infBits,
    Nat.add_zero, walkExp_infBits, show 2047 - 1 = 2046 from rfl, ← Nat.pow_add]

theorem walkExp_maxBits : walkExp maxBits = 2046 := by
  have hdec : maxBits = 2 ^ 52 * 2046 + (2 ^ 52 - 1) := by
    rw [maxBits_eq, Nat.mul_comm 2046 (2 ^ 52)]
  unfold walkExp
  rw [hdec, Nat.mul_add_div (by decide : 0 < 2 ^ 52), Nat.div_eq_of_lt (by omega),
    Nat.add_zero, Nat.mod_eq_of_lt (by decide)]

theorem walkFrac_maxBits : walkFrac maxBits = 2 ^ 52 - 1 := by
  have hdec : maxBits = (2 ^ 52 - 1) + 2 ^ 52 * 2046 := by
    rw [maxBits_eq, Nat.mul_comm 2046 (2 ^ 52), Nat.add_comm]
  unfold walkFrac
  rw [hdec, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide)]

theorem walkMant_maxBits : walkMant maxBits = 2 ^ 53 - 1 := by
  rw [walkMant_eq_normal (by rw [walkExp_maxBits]; decide), walkFrac_maxBits,
    two_pow_52_add_pred]

theorem walkTicks_maxBits : walkTicks maxBits = maxMagTicks := by
  rw [walkTicks_eq_normal (by rw [walkExp_maxBits]; decide), walkFrac_maxBits,
    walkExp_maxBits, two_pow_52_add_pred, show 2046 - 1 = 2045 from rfl, maxMagTicks]

theorem upTwice_maxBits : upTwice maxBits = 2 * overflowTicks := by
  unfold upTwice
  rw [walkTicks_maxBits, maxBits_succ, walkTicks_infBits, maxMagTicks,
    two_pow_2098_eq, two_overflowTicks, ← Nat.add_mul, two_pow_54_eq]
  congr 1

theorem upTwice_le_top {b : Nat} (hb : b ≤ maxBits) : upTwice b ≤ 2 * overflowTicks := by
  rw [← upTwice_maxBits]
  exact upTwice_le_of_le hb maxBits_lt_infBits

/-! ### The boundaries the emitted code compares against

The body's three comparisons (`stage2.c:787`, `:791`, `:806`) are against the
candidate's own tick value and its two midpoints.  The midpoint above is
`(2m + 1) * 2^(e - 1)` in every binade (`:791`); the midpoint below is the same
shape except at the bottom of a normal binade, where the previous binade's ulp
is the one to halve, so the code selects the shape by the binade
(`:803-805`).  `bound2` reads a boundary `J * 2^eB` at twice the tick scale,
which is the scale at which the boundary is the midpoint of two candidate
ticks. -/

/-- The comparison's exponent `e` (`stage2.c:786`): `be - 1075` for a normal,
`-1074` for a subnormal. -/
def walkE (b : Nat) : Int := if walkExp b = 0 then -1074 else (walkExp b : Int) - 1075

theorem walkE_eq_zero {b : Nat} (h : walkExp b = 0) : walkE b = -1074 := by
  simp only [walkE, h, reduceIte]

theorem walkE_eq_normal {b : Nat} (h : walkExp b ≠ 0) :
    walkE b = (walkExp b : Int) - 1075 := by
  simp only [walkE, h, reduceIte]

/-- `stage2.c:791`: the boundary above's significand, `2 * m + 1`. -/
def upJ (b : Nat) : Nat := 2 * walkMant b + 1

/-- `stage2.c:791`: the boundary above's exponent, `e - 1`. -/
def upE (b : Nat) : Int := walkE b - 1

/-- `stage2.c:803`: whether the boundary below is half an ulp of the
candidate's own binade. -/
def downSub (b : Nat) : Prop := walkExp b = 0 ∨ 0 < walkFrac b

instance downSub_decidable (b : Nat) : Decidable (downSub b) :=
  inferInstanceAs (Decidable (walkExp b = 0 ∨ 0 < walkFrac b))

/-- `stage2.c:803-805`: the boundary below's significand. -/
def downJ (b : Nat) : Nat :=
  if downSub b then 2 * walkMant b - 1
  else if walkExp b = 1 then 2 ^ 53 - 1
  else 2 ^ 54 - 1

/-- `stage2.c:803-805`: the boundary below's exponent. -/
def downE (b : Nat) : Int :=
  if downSub b then walkE b - 1
  else if walkExp b = 1 then -1075
  else walkE b - 2

/-- A boundary `J * 2^eB` at twice the tick scale.  Every boundary the walk
forms has `eB >= -1075`, so this is an integer. -/
def bound2 (J : Nat) (eB : Int) : Nat := J * 2 ^ (eB + 1075).toNat

theorem upE_toNat_zero {b : Nat} (h : walkExp b = 0) : (upE b + 1075).toNat = 0 := by
  rw [upE, walkE_eq_zero h]
  decide

theorem upE_toNat_normal {b : Nat} (h : walkExp b ≠ 0) :
    (upE b + 1075).toNat = walkExp b - 1 := by
  have hb1 : 1 ≤ walkExp b := Nat.one_le_iff_ne_zero.mpr h
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (by rw [upE, walkE_eq_normal h]; omega),
    Int.natCast_sub hb1, upE, walkE_eq_normal h]
  omega

theorem downE_toNat_sub {b : Nat} (h : walkExp b = 0) : (downE b + 1075).toNat = 0 := by
  have hsub : downSub b := Or.inl h
  rw [downE, ite_eq_left hsub, walkE_eq_zero h]
  decide

theorem downE_toNat_frac {b : Nat} (h0 : walkExp b ≠ 0) (hf : 0 < walkFrac b) :
    (downE b + 1075).toNat = walkExp b - 1 := by
  have hsub : downSub b := Or.inr hf
  have hb1 : 1 ≤ walkExp b := Nat.one_le_iff_ne_zero.mpr h0
  rw [downE, ite_eq_left hsub]
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (by rw [walkE_eq_normal h0]; omega), Int.natCast_sub hb1]
  rw [walkE_eq_normal h0]
  omega

theorem downE_toNat_one {b : Nat} (h1 : walkExp b = 1) (hf : ¬ 0 < walkFrac b) :
    (downE b + 1075).toNat = 0 := by
  have hsub : ¬ downSub b := by
    intro h
    rcases h with h | h
    · omega
    · exact hf h
  rw [downE, ite_eq_right hsub, ite_eq_left h1]
  decide

theorem downE_toNat_two {b : Nat} (h2 : 2 ≤ walkExp b) (hf : ¬ 0 < walkFrac b) :
    (downE b + 1075).toNat = walkExp b - 2 := by
  have hsub : ¬ downSub b := by
    intro h
    rcases h with h | h
    · omega
    · exact hf h
  have h1 : ¬ walkExp b = 1 := by omega
  rw [downE, ite_eq_right hsub, ite_eq_right h1]
  apply Int.natCast_inj.mp
  rw [Int.toNat_of_nonneg (by rw [walkE_eq_normal (by omega)]; omega),
    Int.natCast_sub (by omega)]
  rw [walkE_eq_normal (by omega)]
  omega

theorem bound2_up {b : Nat} (hb : b < infBits) : bound2 (upJ b) (upE b) = upTwice b := by
  have hsucc := walkTicks_succ hb
  by_cases h0 : walkExp b = 0
  · rw [bound2, upJ, walkMant_eq_zero h0, upE_toNat_zero h0, Nat.pow_zero, Nat.mul_one,
      upTwice, hsucc, walkTicks_eq_zero h0, walkGap_eq_zero h0]
    omega
  · rw [bound2, upJ, walkMant_eq_normal h0, upE_toNat_normal h0, upTwice, hsucc,
      walkTicks_eq_normal h0, walkGap_eq_normal h0]
    rw [show 2 * (2 ^ 52 + walkFrac b) + 1 = (2 ^ 52 + walkFrac b) + 1 + (2 ^ 52 + walkFrac b)
        from by omega, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    ac_rfl

theorem pred_double_mul {A k : Nat} (h : 0 < A) :
    (2 * A - 1) * k = (A - 1) * k + A * k := by
  rw [← Nat.add_mul]
  congr 1
  omega

theorem top_double_mul (k : Nat) :
    (2 ^ 54 - 1) * k = (2 ^ 53 - 1) * k + 2 ^ 53 * k := by
  rw [← Nat.add_mul, two_pow_54_eq]
  congr 1

theorem two_pow_shift_down {be : Nat} (h : 2 ≤ be) :
    2 ^ 52 * 2 ^ (be - 1) = 2 ^ 53 * 2 ^ (be - 2) := by
  rw [← Nat.pow_add, ← Nat.pow_add]
  congr 1
  omega

theorem walkTicks_two_pow_52 : walkTicks (2 ^ 52) = 2 ^ 52 := by
  have hexp : walkExp (2 ^ 52) = 1 := by
    unfold walkExp
    rw [Nat.div_self (by decide : 0 < 2 ^ 52), Nat.mod_eq_of_lt (by decide)]
  have hfr : walkFrac (2 ^ 52) = 0 := by
    unfold walkFrac
    exact Nat.mod_self _
  rw [walkTicks_eq_normal (by rw [hexp]; decide), hfr, Nat.add_zero, hexp,
    show 1 - 1 = 0 from rfl, Nat.pow_zero, Nat.mul_one]

theorem bound2_down {b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    bound2 (downJ b) (downE b) = downTwice b := by
  by_cases hz : walkFrac b = 0
  · have hpos : 0 < walkExp b := by
      rcases Nat.eq_zero_or_pos (walkExp b) with h | h
      · exfalso
        have hdec := walk_bits_decomp hb
        rw [h, hz, Nat.zero_mul, Nat.zero_add] at hdec
        omega
      · exact h
    have hsub : ¬ downSub b := by
      intro hs
      rcases hs with hs | hs
      · omega
      · omega
    have hfr : walkFrac (b - 1) = 2 ^ 52 - 1 := walkFrac_pred_of_frac_zero h0 hz
    have hexp' : walkExp (b - 1) = walkExp b - 1 := walkExp_pred_of_frac_zero h0 hz hb
    by_cases hb1 : walkExp b = 1
    · have hnat : (downE b + 1075).toNat = 0 := downE_toNat_one hb1 (by omega)
      have hJ : downJ b = 2 ^ 53 - 1 := by
        simp only [downJ, ite_eq_right hsub, ite_eq_left hb1]
      have hb_eq : b = 2 ^ 52 := by
        have hdec := walk_bits_decomp hb
        rw [hb1, hz, Nat.one_mul, Nat.add_zero] at hdec
        omega
      have hz0 : walkExp (b - 1) = 0 := by rw [hexp', hb1, show 1 - 1 = 0 from rfl]
      rw [bound2, hnat, Nat.pow_zero, Nat.mul_one, hJ, downTwice,
        walkTicks_eq_zero hz0, hfr, hb_eq, walkTicks_two_pow_52]
      exact two_pow_52_add_pred
    · have hb2 : 2 ≤ walkExp b := by omega
      have hnat : (downE b + 1075).toNat = walkExp b - 2 := downE_toNat_two hb2 (by omega)
      have hJ : downJ b = 2 ^ 54 - 1 := by
        simp only [downJ, ite_eq_right hsub, ite_eq_right hb1]
      have hne' : walkExp (b - 1) ≠ 0 := by rw [hexp']; omega
      rw [bound2, hnat, hJ, downTwice, walkTicks_eq_normal hne', hfr, hexp',
        walkTicks_eq_normal (by omega),
        show walkExp b - 1 - 1 = walkExp b - 2 from by omega, two_pow_52_add_pred, hz,
        Nat.add_zero]
      rw [top_double_mul, two_pow_shift_down hb2]
  · have hf : 0 < walkFrac b := Nat.pos_of_ne_zero hz
    have hfr : walkFrac (b - 1) = walkFrac b - 1 := walkFrac_pred_of_frac_pos hf
    have hexp' : walkExp (b - 1) = walkExp b := walkExp_pred_of_frac_pos hf hb
    by_cases hb0 : walkExp b = 0
    · have hsub : downSub b := Or.inl hb0
      have hnat : (downE b + 1075).toNat = 0 := downE_toNat_sub hb0
      have hJ : downJ b = 2 * walkFrac b - 1 := by
        simp only [downJ, ite_eq_left hsub, walkMant_eq_zero hb0]
      have hz0 : walkExp (b - 1) = 0 := by rw [hexp', hb0]
      rw [bound2, hnat, Nat.pow_zero, Nat.mul_one, hJ, downTwice,
        walkTicks_eq_zero hz0, hfr, walkTicks_eq_zero hb0]
      omega
    · have hsub : downSub b := Or.inr hf
      have hnat : (downE b + 1075).toNat = walkExp b - 1 := downE_toNat_frac hb0 hf
      have hJ : downJ b = 2 * (2 ^ 52 + walkFrac b) - 1 := by
        simp only [downJ, ite_eq_left hsub, walkMant_eq_normal hb0]
      have hne' : walkExp (b - 1) ≠ 0 := by rw [hexp']; exact hb0
      rw [bound2, hnat, hJ, downTwice, walkTicks_eq_normal hne', hfr, hexp',
        walkTicks_eq_normal hb0]
      rw [pred_double_mul (by omega : 0 < 2 ^ 52 + walkFrac b), add_sub_one_of_lt hf]

theorem bound2_overflow : bound2 (2 ^ 54 - 1) 970 = 2 * overflowTicks := by
  rw [bound2, show ((970 : Int) + 1075).toNat = 2045 from by decide, two_overflowTicks]



/-! ### The comparison the walk makes

`stk_cmp` returns the sign of the value against its boundary
(`stkCmp_sticky_spec'`, `stkCmp_nosticky_spec`), so the walk's decisions are
those of a three-way comparison at the boundary's tick value.  `cmpWalk` states
that comparison at twice the tick scale, which is where `bound2` reads every
boundary of the loop: `valLtBoundary_iff_cmpWalk` and
`valEqBoundary_iff_cmpWalk` identify the two. -/

/-- The sign of the value `P / d` against the boundary whose doubled tick value
is `B2`. -/
def cmpWalk (P d : Nat) (B2 : Nat) : Int := cmpNat (2 * P) (B2 * d)

theorem cmpWalk_lt {P d B2 : Nat} : cmpWalk P d B2 = -1 ↔ 2 * P < B2 * d :=
  (cmpNat_spec _ _).1

theorem cmpWalk_eq {P d B2 : Nat} : cmpWalk P d B2 = 0 ↔ 2 * P = B2 * d :=
  (cmpNat_spec _ _).2.1

theorem cmpWalk_gt {P d B2 : Nat} : cmpWalk P d B2 = 1 ↔ B2 * d < 2 * P := by
  have h := (cmpNat_spec (2 * P) (B2 * d)).2.2
  rw [cmpWalk]
  constructor
  · intro h1
    rcases h.mp h1 with ⟨h2, h3⟩
    omega
  · intro h1
    exact h.mpr ⟨by omega, by omega⟩

theorem mul_two_pow_1075 (x : Nat) : 2 * (x * 2 ^ 1074) = x * 2 ^ 1075 := by
  rw [show (2 : Nat) ^ 1075 = 2 ^ 1074 * 2 from by
    rw [show 1075 = 1074 + 1 from by decide, Nat.pow_succ]]
  ac_rfl

theorem two_pow_1075_eq_mul {eB : Nat} : 2 ^ (eB + 1075) = 2 ^ eB * 2 ^ 1075 :=
  Nat.pow_add ..

theorem two_pow_1075_split {k : Nat} (hk : k ≤ 1075) :
    2 ^ (1075 - k) * 2 ^ k = 2 ^ 1075 := by
  rw [← Nat.pow_add, Nat.sub_add_cancel hk]

/-- The boundary's doubled tick value, as a comparison: `valLtBoundary` is the
same comparison cleared at the value's own scale. -/
theorem valLtBoundary_iff_cmpWalk {m : Nat} {E : Int} {J : Nat} {eB : Int}
    (hle : -1075 ≤ eB) :
    valLtBoundary m E J eB ↔
      2 * (magTicks m E).1 < bound2 J eB * (magTicks m E).2 := by
  by_cases hE : 0 ≤ E <;> by_cases heB : 0 ≤ eB
  · -- a nonnegative decimal exponent, a nonnegative boundary exponent
    have hP : (magTicks m E).1 = m * 10 ^ E.toNat * 2 ^ 1074 := by
      unfold magTicks; rw [ite_eq_left hE]
    have hD : (magTicks m E).2 = 1 := by unfold magTicks; rw [ite_eq_left hE]
    have hn : (eB + 1075).toNat = eB.toNat + 1075 := by
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (by omega), Int.natCast_add, Int.toNat_of_nonneg heB]
      omega
    have hEb : ((eB.toNat : Nat) : Int) = eB := Int.toNat_of_nonneg heB
    unfold valLtBoundary
    rw [ite_eq_left hE, ite_eq_left heB, hP, hD, Nat.mul_one, bound2, hn]
    rw [two_pow_1075_eq_mul, mul_two_pow_1075,
      show J * (2 ^ eB.toNat * 2 ^ 1075) = (J * 2 ^ eB.toNat) * 2 ^ 1075 from by ac_rfl]
    exact lt_iff_mul_lt_mul_right (two_pow_pos 1075)
  · -- a nonnegative decimal exponent, a negative boundary exponent
    have hP : (magTicks m E).1 = m * 10 ^ E.toNat * 2 ^ 1074 := by
      unfold magTicks; rw [ite_eq_left hE]
    have hD : (magTicks m E).2 = 1 := by unfold magTicks; rw [ite_eq_left hE]
    have hne : eB < 0 := by omega
    have hk : eB.natAbs ≤ 1075 := by
      have := natAbs_of_neg hne
      omega
    have hn : (eB + 1075).toNat = 1075 - eB.natAbs := by
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (by omega), Int.natCast_sub hk, natAbs_of_neg hne]
      omega
    unfold valLtBoundary
    rw [ite_eq_left hE, ite_eq_right (by omega : ¬ 0 ≤ eB), hP, hD, Nat.mul_one,
      bound2, hn, mul_two_pow_1075]
    rw [show J * 2 ^ (1075 - eB.natAbs) = J * 2 ^ (1075 - eB.natAbs) from rfl]
    rw [show m * 10 ^ E.toNat * 2 ^ 1075
        = (m * 10 ^ E.toNat * 2 ^ eB.natAbs) * 2 ^ (1075 - eB.natAbs) from by
      rw [show (2 : Nat) ^ 1075 = 2 ^ (1075 - eB.natAbs) * 2 ^ eB.natAbs from
        (two_pow_1075_split hk).symm]
      ac_rfl]
    exact lt_iff_mul_lt_mul_right (two_pow_pos (1075 - eB.natAbs))
  · -- a negative decimal exponent, a nonnegative boundary exponent
    have hP : (magTicks m E).1 = m * 2 ^ 1074 := by
      unfold magTicks; rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
    have hD : (magTicks m E).2 = 10 ^ E.natAbs := by
      unfold magTicks; rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
    have hn : (eB + 1075).toNat = eB.toNat + 1075 := by
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (by omega), Int.natCast_add, Int.toNat_of_nonneg heB]
      omega
    unfold valLtBoundary
    rw [ite_eq_right (by omega : ¬ 0 ≤ E), ite_eq_left heB, hP, hD, bound2, hn,
      two_pow_1075_eq_mul, mul_two_pow_1075]
    rw [show J * (2 ^ eB.toNat * 2 ^ 1075) * 10 ^ E.natAbs
        = (J * 2 ^ eB.toNat * 10 ^ E.natAbs) * 2 ^ 1075 from by ac_rfl]
    exact lt_iff_mul_lt_mul_right (two_pow_pos 1075)
  · -- a negative decimal exponent, a negative boundary exponent
    have hP : (magTicks m E).1 = m * 2 ^ 1074 := by
      unfold magTicks; rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
    have hD : (magTicks m E).2 = 10 ^ E.natAbs := by
      unfold magTicks; rw [ite_eq_right (by omega : ¬ 0 ≤ E)]
    have hne : eB < 0 := by omega
    have hk : eB.natAbs ≤ 1075 := by
      have := natAbs_of_neg hne
      omega
    have hn : (eB + 1075).toNat = 1075 - eB.natAbs := by
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (by omega), Int.natCast_sub hk, natAbs_of_neg hne]
      omega
    unfold valLtBoundary
    rw [ite_eq_right (by omega : ¬ 0 ≤ E), ite_eq_right (by omega : ¬ 0 ≤ eB), hP, hD,
      bound2, hn, mul_two_pow_1075]
    rw [show m * 2 ^ 1075 = (m * 2 ^ eB.natAbs) * 2 ^ (1075 - eB.natAbs) from by
        rw [show (2 : Nat) ^ 1075 = 2 ^ (1075 - eB.natAbs) * 2 ^ eB.natAbs from
          (two_pow_1075_split hk).symm]
        ac_rfl,
      show J * 2 ^ (1075 - eB.natAbs) * 10 ^ E.natAbs
        = (J * 10 ^ E.natAbs) * 2 ^ (1075 - eB.natAbs) from by ac_rfl]
    exact lt_iff_mul_lt_mul_right (two_pow_pos (1075 - eB.natAbs))



/-! ### The walk's step

`walkStep` is the loop body of `stage2.c:769-813`, over the pattern `b`: the two
escapes at the ends of the format (`:770-782`), the exact test (`:787`), and the
two half-ulp tests with their tie branches (`:789-812`).  A step's result is
either the candidate it stops at or the candidate it moves to.

`inInterval` is the rounding interval: the value at or above the candidate's
lower midpoint and at or below its upper one, with a tie at either going to the
even significand.  `inTop` is the interval of infinity. -/

/-- What the body at `b` does. -/
inductive WalkResult where
  | stop (b : Nat)
  | move (b : Nat)
deriving DecidableEq, Repr

/-- The candidate's rounding interval contains the value. -/
def inInterval (P d b : Nat) : Prop :=
  downTwice b * d ≤ 2 * P ∧ 2 * P ≤ upTwice b * d ∧
    (downTwice b * d = 2 * P → walkMant b % 2 = 0) ∧
    (upTwice b * d = 2 * P → walkMant b % 2 = 0)

/-- The value is at or above the overflow threshold: infinity's interval. -/
def inTop (P d : Nat) : Prop := overflowTicks * d ≤ P

/-- The loop body at `b`, as `stage2.c:769-813` writes it. -/
def walkStep (P d : Nat) (b : Nat) : WalkResult :=
  if b = 0 then
    (if 0 < cmpWalk P d (upTwice 0) then .move 1 else .stop 0)
  else if infBits ≤ b then
    (if cmpWalk P d (2 * overflowTicks) < 0 then .move maxBits else .stop infBits)
  else
    if cmpWalk P d (2 * walkTicks b) = 0 then .stop b
    else if 0 < cmpWalk P d (2 * walkTicks b) then
      (if cmpWalk P d (upTwice b) < 0 then .stop b
       else if cmpWalk P d (upTwice b) = 0 then
         (if walkMant b % 2 = 0 then .stop b else .stop (b + 1))
       else .move (b + 1))
    else
      (if 0 < cmpWalk P d (downTwice b) then .stop b
       else if cmpWalk P d (downTwice b) = 0 then
         (if walkMant b % 2 = 0 then .stop b else .stop (b - 1))
       else .move (b - 1))

theorem cmpWalk_mem (P d B2 : Nat) :
    cmpWalk P d B2 = -1 ∨ cmpWalk P d B2 = 0 ∨ cmpWalk P d B2 = 1 := by
  unfold cmpWalk cmpNat
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem cmpWalk_lt' {P d B2 : Nat} (h : cmpWalk P d B2 < 0) : 2 * P < B2 * d := by
  rcases cmpWalk_mem P d B2 with h' | h' | h'
  · exact cmpWalk_lt.mp h'
  · rw [h'] at h
    exact absurd h (by decide)
  · rw [h'] at h
    exact absurd h (by decide)

theorem cmpWalk_gt' {P d B2 : Nat} (h : 0 < cmpWalk P d B2) : B2 * d < 2 * P := by
  rcases cmpWalk_mem P d B2 with h' | h' | h'
  · rw [h'] at h
    exact absurd h (by decide)
  · rw [h'] at h
    exact absurd h (by decide)
  · exact cmpWalk_gt.mp h'

theorem cmpWalk_nonpos {P d B2 : Nat} (h : ¬ 0 < cmpWalk P d B2) : 2 * P ≤ B2 * d := by
  rcases cmpWalk_mem P d B2 with h' | h' | h'
  · exact Nat.le_of_lt (cmpWalk_lt.mp h')
  · exact Nat.le_of_eq (cmpWalk_eq.mp h')
  · rw [h'] at h
    exact absurd h (by decide)

theorem cmpWalk_nonneg {P d B2 : Nat} (h : ¬ cmpWalk P d B2 < 0) : B2 * d ≤ 2 * P := by
  rcases cmpWalk_mem P d B2 with h' | h' | h'
  · rw [h'] at h
    exact absurd h (by decide)
  · exact Nat.le_of_eq (cmpWalk_eq.mp h').symm
  · exact Nat.le_of_lt (cmpWalk_gt.mp h')

theorem walkTicks_zero : walkTicks 0 = 0 := by
  have h : walkExp 0 = 0 := by unfold walkExp; decide
  rw [walkTicks_eq_zero h]
  unfold walkFrac
  exact Nat.zero_mod _

theorem downTwice_zero : downTwice 0 = 0 := by
  unfold downTwice
  rw [walkTicks_zero]

theorem walkMant_zero : walkMant 0 = 0 := by
  have h : walkExp 0 = 0 := by unfold walkExp; decide
  rw [walkMant_eq_zero h]
  unfold walkFrac
  exact Nat.zero_mod _

/-- A candidate's own tick value is strictly inside its interval. -/
theorem walkTicks_lt_upTwice {b : Nat} (hb : b < infBits) :
    2 * walkTicks b < upTwice b := by
  unfold upTwice
  have := walkTicks_lt_succ hb
  omega

theorem walkTicks_pred_lt {b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkTicks (b - 1) < walkTicks b := by
  have h := walkTicks_pred h0 hb
  have := walkGap_pos (b - 1)
  omega

theorem downTwice_lt_ticks {b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    downTwice b < 2 * walkTicks b := by
  unfold downTwice
  have := walkTicks_pred_lt h0 hb
  omega

theorem walkStep_fin {P d b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b =
      (if cmpWalk P d (2 * walkTicks b) = 0 then .stop b
       else if 0 < cmpWalk P d (2 * walkTicks b) then
         (if cmpWalk P d (upTwice b) < 0 then .stop b
          else if cmpWalk P d (upTwice b) = 0 then
            (if walkMant b % 2 = 0 then .stop b else .stop (b + 1))
          else .move (b + 1))
       else
         (if 0 < cmpWalk P d (downTwice b) then .stop b
          else if cmpWalk P d (downTwice b) = 0 then
            (if walkMant b % 2 = 0 then .stop b else .stop (b - 1))
          else .move (b - 1))) := by
  unfold walkStep
  rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_right (by omega : ¬ infBits ≤ b)]

theorem step_zero_stop {P d : Nat} (h : walkStep P d 0 = .stop 0) : inInterval P d 0 := by
  have hle : 2 * P ≤ upTwice 0 * d := by
    unfold walkStep at h
    rw [ite_eq_left rfl] at h
    by_cases hc : 0 < cmpWalk P d (upTwice 0)
    · rw [ite_eq_left hc] at h
      exact absurd h (by intro hh; cases hh)
    · rw [ite_eq_right hc] at h
      exact cmpWalk_nonpos hc
  unfold inInterval
  refine ⟨by rw [downTwice_zero, Nat.zero_mul]; exact Nat.zero_le _, hle, ?_, ?_⟩
  · intro hh
    show walkMant 0 % 2 = 0
    rw [walkMant_zero]
  · intro hh
    show walkMant 0 % 2 = 0
    rw [walkMant_zero]

theorem step_zero_move {P d : Nat} (h : walkStep P d 0 = .move 1) :
    upTwice 0 * d < 2 * P := by
  unfold walkStep at h
  rw [ite_eq_left rfl] at h
  by_cases hc : 0 < cmpWalk P d (upTwice 0)
  · rw [ite_eq_left hc] at h
    exact cmpWalk_gt' hc
  · rw [ite_eq_right hc] at h
    exact absurd h (by intro hh; cases hh)

theorem step_top_stop {P d b : Nat} (hb : infBits ≤ b) (h : walkStep P d b = .stop infBits) :
    inTop P d := by
  have hpos := infBits_pos
  unfold walkStep at h
  rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_left hb] at h
  by_cases hc : cmpWalk P d (2 * overflowTicks) < 0
  · rw [ite_eq_left hc] at h
    exact absurd h (by intro hh; cases hh)
  · rw [ite_eq_right hc] at h
    have h2 : 2 * (overflowTicks * d) ≤ 2 * P := by
      have h3 := cmpWalk_nonneg hc
      rwa [Nat.mul_assoc] at h3
    unfold inTop
    exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)

theorem step_top_move {P d b : Nat} (hb : infBits ≤ b) (h : walkStep P d b = .move maxBits) :
    2 * P < 2 * overflowTicks * d := by
  have hpos := infBits_pos
  unfold walkStep at h
  rw [ite_eq_right (by omega : ¬ b = 0), ite_eq_left hb] at h
  by_cases hc : cmpWalk P d (2 * overflowTicks) < 0
  · rw [ite_eq_left hc] at h
    exact cmpWalk_lt' hc
  · rw [ite_eq_right hc] at h
    exact absurd h (by intro hh; cases hh)



/-! #### The body's five verdicts -/

theorem downTwice_mul_le {P d b : Nat} (h0 : 0 < b) (hb : b < infBits)
    (h : 2 * walkTicks b * d ≤ 2 * P) : downTwice b * d ≤ 2 * P :=
  Nat.le_trans (Nat.mul_le_mul_right d (Nat.le_of_lt (downTwice_lt_ticks h0 hb))) h

theorem ticks_mul_le_up {P d b : Nat} (hb : b < infBits)
    (h : 2 * P ≤ 2 * walkTicks b * d) : 2 * P ≤ upTwice b * d :=
  Nat.le_trans h (Nat.mul_le_mul_right d (Nat.le_of_lt (walkTicks_lt_upTwice hb)))

theorem downTwice_mul_lt {d b : Nat} (hd : 0 < d) (h0 : 0 < b) (hb : b < infBits) :
    downTwice b * d < 2 * walkTicks b * d :=
  Nat.mul_lt_mul_of_pos_right (downTwice_lt_ticks h0 hb) hd

theorem ticks_mul_lt_up {d b : Nat} (hd : 0 < d) (hb : b < infBits) :
    2 * walkTicks b * d < upTwice b * d :=
  Nat.mul_lt_mul_of_pos_right (walkTicks_lt_upTwice hb) hd

theorem WalkResult.stop_ne_stop_of_ne {a b : Nat} (h : a ≠ b) :
    (WalkResult.stop a : WalkResult) ≠ .stop b :=
  fun hh => h (WalkResult.stop.inj hh)

theorem WalkResult.stop_ne_move (a b : Nat) : (WalkResult.stop a : WalkResult) ≠ .move b := by
  intro h
  cases h

theorem WalkResult.move_ne_stop (a b : Nat) : (WalkResult.move a : WalkResult) ≠ .stop b := by
  intro h
  cases h

theorem WalkResult.move_ne_move_of_ne {a b : Nat} (h : a ≠ b) :
    (WalkResult.move a : WalkResult) ≠ .move b :=
  fun hh => h (WalkResult.move.inj hh)

/-- A stop at the candidate itself puts the value in the candidate's interval. -/
theorem step_fin_stop_self {P d b : Nat} (hd : 0 < d) (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b = .stop b → inInterval P d b := by
  intro h
  rw [walkStep_fin h0 hb] at h
  have hdn0 : downTwice b * d < 2 * walkTicks b * d := downTwice_mul_lt hd h0 hb
  have hup0 : 2 * walkTicks b * d < upTwice b * d := ticks_mul_lt_up hd hb
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    have heq : 2 * P = 2 * walkTicks b * d := cmpWalk_eq.mp hs
    have hdn : downTwice b * d < 2 * P := by rw [heq]; exact hdn0
    have hup : 2 * P < upTwice b * d := by rw [heq]; exact hup0
    exact ⟨Nat.le_of_lt hdn, Nat.le_of_lt hup, fun hh => absurd hh (ne_of_lt hdn),
      fun hh => absurd hh (ne_of_gt hup)⟩
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    have hgt : 2 * walkTicks b * d < 2 * P := cmpWalk_gt' hs2
    have hdn : downTwice b * d < 2 * P := Nat.lt_of_lt_of_le hdn0 (Nat.le_of_lt hgt)
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      have hup : 2 * P < upTwice b * d := cmpWalk_lt' hu
      exact ⟨Nat.le_of_lt hdn, Nat.le_of_lt hup, fun hh => absurd hh (ne_of_lt hdn),
        fun hh => absurd hh (ne_of_gt hup)⟩
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      have heq : 2 * P = upTwice b * d := cmpWalk_eq.mp hu2
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact ⟨Nat.le_of_lt hdn, Nat.le_of_eq heq, fun hh => absurd hh (ne_of_lt hdn),
          fun hh => he⟩
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hu2] at h
    exact absurd h (WalkResult.move_ne_stop (b + 1) b)
  · rw [ite_eq_right hs2] at h
    have hlt : 2 * P < 2 * walkTicks b * d := by
      have hpos : cmpWalk P d (2 * walkTicks b) < 0 := by omega
      exact cmpWalk_lt' hpos
    have hup : 2 * P < upTwice b * d := Nat.lt_of_lt_of_le hlt (Nat.le_of_lt hup0)
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      have hdn : downTwice b * d < 2 * P := cmpWalk_gt' hd1
      exact ⟨Nat.le_of_lt hdn, Nat.le_of_lt hup, fun hh => absurd hh (ne_of_lt hdn),
        fun hh => absurd hh (ne_of_gt hup)⟩
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      have heq : 2 * P = downTwice b * d := cmpWalk_eq.mp hd2
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact ⟨Nat.le_of_eq heq.symm, Nat.le_of_lt hup, fun hh => he,
          fun hh => absurd hh (ne_of_gt hup)⟩
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hd2] at h
    exact absurd h (WalkResult.move_ne_stop (b - 1) b)

/-- A stop at the candidate above happens only at the upper midpoint, and only
when the candidate's significand is odd. -/
theorem step_fin_stop_next {P d b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b = .stop (b + 1) →
      upTwice b * d = 2 * P ∧ walkMant b % 2 ≠ 0 := by
  intro h
  rw [walkStep_fin h0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      refine ⟨(cmpWalk_eq.mp hu2).symm, ?_⟩
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
      · exact he
    rw [ite_eq_right hu2] at h
    exact absurd h (WalkResult.move_ne_stop (b + 1) (b + 1))
  · rw [ite_eq_right hs2] at h
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hd2] at h
    exact absurd h (WalkResult.move_ne_stop (b - 1) (b + 1))

/-- A stop at the candidate below happens only at the lower midpoint, and only
when the candidate's significand is odd. -/
theorem step_fin_stop_pred {P d b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b = .stop (b - 1) →
      downTwice b * d = 2 * P ∧ walkMant b % 2 ≠ 0 := by
  intro h
  rw [walkStep_fin h0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hu2] at h
    exact absurd h (WalkResult.move_ne_stop (b + 1) (b - 1))
  · rw [ite_eq_right hs2] at h
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      refine ⟨(cmpWalk_eq.mp hd2).symm, ?_⟩
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_stop_of_ne (by omega))
      · exact he
    rw [ite_eq_right hd2] at h
    exact absurd h (WalkResult.move_ne_stop (b - 1) (b - 1))

/-- A step up is the value strictly above the upper midpoint. -/
theorem step_fin_move_next {P d b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b = .move (b + 1) → upTwice b * d < 2 * P := by
  intro h
  rw [walkStep_fin h0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact absurd h (WalkResult.stop_ne_move b (b + 1))
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact absurd h (WalkResult.stop_ne_move b (b + 1))
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_move b (b + 1))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_move (b + 1) (b + 1))
    rw [ite_eq_right hu2] at h
    have hpos : 0 < cmpWalk P d (upTwice b) := by omega
    exact cmpWalk_gt' hpos
  · rw [ite_eq_right hs2] at h
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      exact absurd h (WalkResult.stop_ne_move b (b + 1))
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_move b (b + 1))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_move (b - 1) (b + 1))
    rw [ite_eq_right hd2] at h
    exact absurd h (WalkResult.move_ne_move_of_ne (by omega))

/-- A step down is the value strictly below the lower midpoint. -/
theorem step_fin_move_pred {P d b : Nat} (h0 : 0 < b) (hb : b < infBits) :
    walkStep P d b = .move (b - 1) → 2 * P < downTwice b * d := by
  intro h
  rw [walkStep_fin h0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact absurd h (WalkResult.stop_ne_move b (b - 1))
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact absurd h (WalkResult.stop_ne_move b (b - 1))
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_move b (b - 1))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_move (b + 1) (b - 1))
    rw [ite_eq_right hu2] at h
    exact absurd h (WalkResult.move_ne_move_of_ne (by omega))
  · rw [ite_eq_right hs2] at h
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      exact absurd h (WalkResult.stop_ne_move b (b - 1))
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_move b (b - 1))
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_move (b - 1) (b - 1))
    rw [ite_eq_right hd2] at h
    have hneg : cmpWalk P d (downTwice b) < 0 := by omega
    exact cmpWalk_lt' hneg

/-- A candidate whose interval contains the value is where the body stops. -/
theorem step_fin_stop_of_mem {P d b : Nat} (h0 : 0 < b) (hb : b < infBits)
    (hi : inInterval P d b) : walkStep P d b = .stop b := by
  obtain ⟨h1, h2, h3, h4⟩ := hi
  rw [walkStep_fin h0 hb]
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs]
  rw [ite_eq_right hs]
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2]
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu]
    rw [ite_eq_right hu]
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2]
      have heq : 2 * P = upTwice b * d := cmpWalk_eq.mp hu2
      rw [ite_eq_left (h4 heq.symm)]
    rw [ite_eq_right hu2]
    have hpos : 0 < cmpWalk P d (upTwice b) := by omega
    have := cmpWalk_gt' hpos
    omega
  · rw [ite_eq_right hs2]
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1]
    rw [ite_eq_right hd1]
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2]
      have heq : 2 * P = downTwice b * d := cmpWalk_eq.mp hd2
      rw [ite_eq_left (h3 heq.symm)]
    rw [ite_eq_right hd2]
    have hneg : cmpWalk P d (downTwice b) < 0 := by omega
    have := cmpWalk_lt' hneg
    omega



/-! #### The interval is one candidate's -/

theorem upTwice_lt_downTwice {b b' : Nat} (h : b + 1 < b') (hb' : b' < infBits) :
    upTwice b < downTwice b' := by
  unfold upTwice downTwice
  have h1 : walkTicks b < walkTicks b' := walkTicks_lt_of_lt (by omega) (by omega)
  have h2 : walkTicks (b + 1) ≤ walkTicks (b' - 1) :=
    walkTicks_le_of_le (by omega) (by omega)
  omega

theorem downTwice_le_upTwice {b : Nat} (hb : b < infBits) : downTwice b ≤ upTwice b := by
  unfold downTwice upTwice
  have h1 : walkTicks (b - 1) ≤ walkTicks (b + 1) := walkTicks_le_of_le (by omega) (by omega)
  omega

theorem downTwice_lt_upTwice {b : Nat} (hb0 : 0 < b) (hb : b < infBits) :
    downTwice b < upTwice b := by
  unfold downTwice upTwice
  have h1 : walkTicks (b - 1) < walkTicks (b + 1) :=
    walkTicks_lt_of_lt (by omega) (by omega)
  omega

/-- The candidate whose interval contains the value is unique. -/
theorem inInterval_uniq {P d b b' : Nat} (hd : 0 < d) (hb : b < infBits)
    (hb' : b' < infBits) (h : inInterval P d b) (h' : inInterval P d b') : b = b' := by
  rcases Nat.lt_trichotomy b b' with hlt | heq | hgt
  · obtain ⟨-, h2, -, h4⟩ := h
    obtain ⟨h1', -, h3', -⟩ := h'
    rcases Nat.lt_or_ge (b + 1) b' with hgap | hadj
    · have hlt : upTwice b * d < downTwice b' * d :=
        Nat.mul_lt_mul_of_pos_right (upTwice_lt_downTwice hgap hb') hd
      have hle : downTwice b' * d ≤ upTwice b * d := le_trans h1' h2
      exact absurd hle (Nat.not_le.mpr hlt)
    · have hb1 : b + 1 = b' := by omega
      have hle : downTwice b' * d = upTwice b * d := by rw [← hb1, downTwice_succ]
      have heq2 : upTwice b * d = 2 * P := by
        rw [hle] at h1'
        exact le_antisymm h1' h2
      have hmant : walkMant (b + 1) % 2 = 0 := by
        have h'1 : walkMant b' % 2 = 0 := h3' (by rw [hle]; exact heq2)
        rwa [← hb1] at h'1
      exact absurd ⟨h4 heq2, hmant⟩ (walkMant_succ_not_both_even hb)
  · exact heq
  · obtain ⟨h1, -, h3, -⟩ := h
    obtain ⟨-, h2', -, h4'⟩ := h'
    rcases Nat.lt_or_ge (b' + 1) b with hgap | hadj
    · have hlt : upTwice b' * d < downTwice b * d :=
        Nat.mul_lt_mul_of_pos_right (upTwice_lt_downTwice hgap hb) hd
      have hle : downTwice b * d ≤ upTwice b' * d := le_trans h1 h2'
      exact absurd hle (Nat.not_le.mpr hlt)
    · have hb1 : b' + 1 = b := by omega
      have hle : downTwice b * d = upTwice b' * d := by rw [← hb1, downTwice_succ]
      have heq2 : upTwice b' * d = 2 * P := by
        rw [hle] at h1
        exact le_antisymm h1 h2'
      have hmant : walkMant (b' + 1) % 2 = 0 := by
        have h1' : walkMant b % 2 = 0 := h3 (by rw [hle]; exact heq2)
        rwa [← hb1] at h1'
      have hmant' : walkMant b' % 2 = 0 := h4' heq2
      exact absurd ⟨hmant', hmant⟩ (walkMant_succ_not_both_even hb')

theorem upTwice_eq_top {b : Nat} (hb : b ≤ maxBits) (h : upTwice b = 2 * overflowTicks) :
    b = maxBits := by
  by_cases hlt : b = maxBits
  · exact hlt
  · exfalso
    have hlt' : b < maxBits := by omega
    have hge := upTwice_lt_of_lt hlt' maxBits_lt_infBits
    rw [upTwice_maxBits] at hge
    exact absurd hge (by rw [h]; exact Nat.lt_irrefl _)

/-- Infinity's interval is disjoint from every finite candidate's. -/
theorem inInterval_not_top {P d b : Nat} (hd : 0 < d) (hb : b < infBits)
    (h : inInterval P d b) : ¬ inTop P d := by
  intro ht
  obtain ⟨-, h2, -, h4⟩ := h
  have hble : b ≤ maxBits := by
    have hmax : maxBits = infBits - 1 := rfl
    omega
  have htop : 2 * (overflowTicks * d) ≤ 2 * P := Nat.mul_le_mul_left 2 ht
  have hle : upTwice b * d ≤ 2 * (overflowTicks * d) := by
    have h1 := upTwice_le_top hble
    have h2' := Nat.mul_le_mul_right d h1
    rwa [Nat.mul_assoc] at h2'
  have heq2 : upTwice b * d = 2 * P := le_antisymm (le_trans hle htop) h2
  have hP : 2 * P = 2 * (overflowTicks * d) :=
    le_antisymm (by rw [← heq2]; exact hle) htop
  have hb_eq : b = maxBits := by
    apply upTwice_eq_top hble
    exact Nat.mul_right_cancel hd (by rw [heq2, hP, Nat.mul_assoc])
  subst hb_eq
  have hm := h4 heq2
  rw [walkMant_maxBits, two_pow_53_pred_mod_two] at hm
  exact absurd hm (by decide)

/-- The zero escape stops only at zero. -/
theorem stop_zero_only {P d b' : Nat} (h : walkStep P d 0 = .stop b') : b' = 0 := by
  unfold walkStep at h
  rw [ite_eq_left rfl] at h
  by_cases hc : 0 < cmpWalk P d (upTwice 0)
  · rw [ite_eq_left hc] at h
    exact absurd h (WalkResult.move_ne_stop 1 b')
  · rw [ite_eq_right hc] at h
    exact (WalkResult.stop.inj h).symm

/-- The finite body's stop is its own candidate, the one above, or the one
below. -/
theorem stop_fin_mem {P d b : Nat} (hb0 : 0 < b) (hb : b < infBits)
    {b' : Nat} (h : walkStep P d b = .stop b') :
    b' = b - 1 ∨ b' = b ∨ b' = b + 1 := by
  by_cases h1 : b' = b
  · exact Or.inr (Or.inl h1)
  by_cases h2 : b' = b + 1
  · exact Or.inr (Or.inr h2)
  by_cases h3 : b' = b - 1
  · exact Or.inl h3
  exfalso
  rw [walkStep_fin hb0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact h1 (WalkResult.stop.inj h).symm
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact h1 (WalkResult.stop.inj h).symm
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact h1 (WalkResult.stop.inj h).symm
      · rw [ite_eq_right he] at h
        exact h2 (WalkResult.stop.inj h).symm
    rw [ite_eq_right hu2] at h
    exact absurd h (WalkResult.move_ne_stop (b + 1) b')
  · rw [ite_eq_right hs2] at h
    by_cases hd1 : 0 < cmpWalk P d (downTwice b)
    · rw [ite_eq_left hd1] at h
      exact h1 (WalkResult.stop.inj h).symm
    rw [ite_eq_right hd1] at h
    by_cases hd2 : cmpWalk P d (downTwice b) = 0
    · rw [ite_eq_left hd2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact h1 (WalkResult.stop.inj h).symm
      · rw [ite_eq_right he] at h
        exact h3 (WalkResult.stop.inj h).symm
    rw [ite_eq_right hd2] at h
    exact absurd h (WalkResult.move_ne_stop (b - 1) b')

/-- The interval at the candidate the body stops at: the step tests supply its
two ends, and a tie supplies the even significand. -/
theorem stop_fin_interval {P d b : Nat} (hd : 0 < d) (hb0 : 0 < b) (hb : b < infBits)
    {b' : Nat} (h : walkStep P d b = .stop b') (hb' : b' < infBits) :
    inInterval P d b' := by
  rcases stop_fin_mem hb0 hb h with h1 | h2 | h3
  · -- the candidate below
    rw [h1]
    rcases step_fin_stop_pred hb0 hb (h1 ▸ h) with ⟨htie, hodd⟩
    have hb1 : b - 1 + 1 = b := Nat.sub_add_cancel (by omega)
    have hsucc : downTwice b = upTwice (b - 1) := by
      rw [← hb1]; exact downTwice_succ (b - 1)
    rw [hsucc] at htie
    by_cases hb_eq : b = 1
    · subst hb_eq
      have hz : upTwice 0 * d = 2 * P := htie
      refine ⟨by rw [downTwice_zero, Nat.zero_mul]; exact Nat.zero_le _,
        le_of_eq hz.symm, ?_, ?_⟩
      · intro hh
        show walkMant 0 % 2 = 0
        rw [walkMant_zero]
      · intro hh
        show walkMant 0 % 2 = 0
        rw [walkMant_zero]
    · have hpos : 0 < b - 1 := by omega
      have hb'fin : b - 1 < infBits := by omega
      have hlt : downTwice (b - 1) < upTwice (b - 1) := downTwice_lt_upTwice hpos hb'fin
      have hlt' := Nat.mul_lt_mul_of_pos_right hlt hd
      refine ⟨le_of_lt (lt_of_lt_of_le hlt' (le_of_eq htie)), le_of_eq htie.symm, ?_, ?_⟩
      · intro hh
        have h2' : upTwice (b - 1) * d = 2 * P := htie
        rw [h2'] at hlt'
        exact absurd hh (ne_of_lt hlt')
      · intro hh
        exact walkMant_pred_even hb hodd
  · -- the candidate itself
    rw [h2]
    exact step_fin_stop_self hd hb0 hb (h2 ▸ h)
  · -- the candidate above
    rw [h3]
    rcases step_fin_stop_next hb0 hb (h3 ▸ h) with ⟨htie, hodd⟩
    have hsucc : downTwice (b + 1) = upTwice b := downTwice_succ b
    have hb'fin : b + 1 < infBits := by omega
    have hlt : upTwice b < upTwice (b + 1) := upTwice_lt_of_lt (by omega) hb'fin
    have hlt' := Nat.mul_lt_mul_of_pos_right hlt hd
    refine ⟨by rw [hsucc]; exact le_of_eq htie, ?_, ?_, ?_⟩
    · exact le_of_lt (by rw [← htie]; exact hlt')
    · intro hh
      rw [hsucc] at hh
      exact walkMant_succ_even hb hodd
    · intro hh
      rw [htie] at hlt'
      exact absurd hh (ne_of_gt hlt')





/-! ### The ladder, the specification's lattice, and the loop

`binade`, `ulp`, `sig`, `lo` and `hi` state the specification's lattice at the
exact value `P / d`; `walkExp`, `walkFrac`, `walkTicks` and `walkGap` state the
emitted ladder over the pattern.  The two are one lattice at the value: the
sections below identify them, name the candidate the loop's interval criterion
picks, and run the loop to it. -/

/-! #### The pattern a code names -/

/-- The bit pattern whose fields are the code's: the significand itself in the
subnormal binade, and the fraction field plus the implicit leading bit above
it.  `walkCode (bitsOf c) = c` for every magnitude `c` of the format. -/
def bitsOf (c : Code) : Nat :=
  if c.expField = 0 then c.mant else c.expField * 2 ^ 52 + (c.mant - 2 ^ 52)

theorem code_ext {a b : Code} (h1 : a.expField = b.expField) (h2 : a.mant = b.mant) :
    a = b := by
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  simp only at h1 h2
  rw [h1, h2]

theorem bitsOf_sub {c : Code} (h : c.expField = 0) : bitsOf c = c.mant := by
  simp only [bitsOf, h, reduceIte]

theorem bitsOf_normal {c : Code} (h : c.expField ≠ 0) :
    bitsOf c = c.expField * 2 ^ 52 + (c.mant - 2 ^ 52) := by
  simp only [bitsOf, h, reduceIte]

theorem walkExp_bitsOf {c : Code} (h : c.IsMag) : walkExp (bitsOf c) = c.expField := by
  obtain ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩ := h
  · rw [bitsOf_sub hE]
    have hdiv : c.mant / 2 ^ 52 = 0 := Nat.div_eq_of_lt hm
    simp only [walkExp, hdiv, Nat.zero_mod]
    exact hE.symm
  · have hE0 : c.expField ≠ 0 := by omega
    rw [bitsOf_normal hE0]
    have hk : c.mant - 2 ^ 52 < 2 ^ 52 := by omega
    have hdiv : (c.expField * 2 ^ 52 + (c.mant - 2 ^ 52)) / 2 ^ 52 = c.expField := by
      rw [Nat.mul_comm c.expField (2 ^ 52)]
      rw [Nat.mul_add_div (by decide : 0 < 2 ^ 52) c.expField (c.mant - 2 ^ 52)]
      rw [Nat.div_eq_of_lt hk, Nat.add_zero]
    simp only [walkExp, hdiv]
    exact Nat.mod_eq_of_lt (by omega)

theorem walkFrac_bitsOf_normal {c : Code} (hE : c.expField ≠ 0) (hm : 2 ^ 52 ≤ c.mant)
    (hm2 : c.mant < 2 ^ 53) :
    walkFrac (bitsOf c) = c.mant - 2 ^ 52 := by
  rw [bitsOf_normal hE]
  show (c.expField * 2 ^ 52 + (c.mant - 2 ^ 52)) % 2 ^ 52 = c.mant - 2 ^ 52
  rw [Nat.add_comm (c.expField * 2 ^ 52) (c.mant - 2 ^ 52)]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (by omega)

theorem walkMant_bitsOf {c : Code} (h : c.IsMag) : walkMant (bitsOf c) = c.mant := by
  obtain ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩ := h
  · rw [walkMant_eq_zero (by rw [walkExp_bitsOf (Or.inl ⟨hE, hm⟩)]; exact hE),
      bitsOf_sub hE]
    show c.mant % 2 ^ 52 = c.mant
    exact Nat.mod_eq_of_lt hm
  · have hE0 : c.expField ≠ 0 := by omega
    have hexp : walkExp (bitsOf c) ≠ 0 := by
      rw [walkExp_bitsOf (Or.inr ⟨hE1, hE2, hm1, hm2⟩)]
      exact hE0
    rw [walkMant_eq_normal hexp, walkFrac_bitsOf_normal hE0 hm1 hm2]
    omega

theorem walkCode_bitsOf {c : Code} (h : c.IsMag) : walkCode (bitsOf c) = c := by
  apply code_ext
  · simp only [walkCode]
    exact walkExp_bitsOf h
  · simp only [walkCode]
    exact walkMant_bitsOf h

theorem walkTicks_bitsOf {c : Code} (h : c.IsMag) : walkTicks (bitsOf c) = c.ticks := by
  unfold walkTicks
  rw [walkCode_bitsOf h]

theorem bitsOf_lt_infBits {c : Code} (h : c.IsMag) : bitsOf c < infBits := by
  obtain ⟨hE, hm⟩ | ⟨hE1, hE2, hm1, hm2⟩ := h
  · rw [bitsOf_sub hE]
    have h2 : 2 ^ 52 ≤ infBits := by
      simp only [infBits]
      calc 2 ^ 52 = 1 * 2 ^ 52 := (Nat.one_mul _).symm
        _ ≤ 2047 * 2 ^ 52 := Nat.mul_le_mul_right _ (by decide)
    omega
  · have hE0 : c.expField ≠ 0 := by omega
    rw [bitsOf_normal hE0]
    have hk : c.mant - 2 ^ 52 < 2 ^ 52 := by omega
    have hmono : c.expField * 2 ^ 52 ≤ 2046 * 2 ^ 52 := Nat.mul_le_mul_right _ hE2
    have hexpand : (2046 : Nat) * 2 ^ 52 + 2 ^ 52 = 2047 * 2 ^ 52 := by omega
    simp only [infBits]
    omega

/-- Every finite pattern's code is a magnitude of the format. -/
theorem walkCode_isMag {b : Nat} (hb : b < infBits) : (walkCode b).IsMag := by
  have hexp := walkExp_lt_2047 hb
  have hfrac := walkFrac_lt b
  by_cases h0 : walkExp b = 0
  · left
    simp only [walkCode]
    exact ⟨h0, by rw [walkMant_eq_zero h0]; exact hfrac⟩
  · right
    simp only [walkCode]
    exact ⟨Nat.pos_of_ne_zero h0, by omega, by rw [walkMant_eq_normal h0]; omega,
      by rw [walkMant_eq_normal h0]; omega⟩

/-! ### The specification's lattice at a pattern -/

/-- The pattern of the binade's floor lattice point: the code
`(binade - 51, sig)` read as a pattern. -/
def loBits (P d : Nat) : Nat := bitsOf ⟨binade P d - 51, sig P d⟩

theorem lo_code_isMag {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    (⟨binade P d - 51, sig P d⟩ : Code).IsMag := by
  obtain ⟨hB, hB', hlo, hup⟩ := binade_facts hd hno hsub
  obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hlo hup
  refine Or.inr ⟨?_, ?_, hq1, hq2⟩
  · show 1 ≤ binade P d - 51
    omega
  · show binade P d - 51 ≤ 2046
    omega

theorem walkExp_loBits {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkExp (loBits P d) = binade P d - 51 :=
  walkExp_bitsOf (lo_code_isMag hd hno hsub)

theorem walkMant_loBits {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkMant (loBits P d) = sig P d :=
  walkMant_bitsOf (lo_code_isMag hd hno hsub)

theorem loBits_lt {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    loBits P d < infBits :=
  bitsOf_lt_infBits (lo_code_isMag hd hno hsub)

theorem walkTicks_loBits {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkTicks (loBits P d) = lo P d := by
  obtain ⟨hB, -⟩ := binade_facts hd hno hsub
  show walkTicks (bitsOf ⟨binade P d - 51, sig P d⟩) = lo P d
  rw [walkTicks_bitsOf (lo_code_isMag hd hno hsub)]
  rw [ticks_normal (show binade P d - 51 ≠ 0 by omega)]
  rw [show binade P d - 51 - 1 = binade P d - 52 by omega]
  rfl

theorem walkGap_loBits {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkGap (loBits P d) = ulp P d := by
  obtain ⟨hB, -⟩ := binade_facts hd hno hsub
  have hexp := walkExp_loBits hd hno hsub
  have hne : walkExp (loBits P d) ≠ 0 := by rw [hexp]; omega
  rw [walkGap_eq_normal hne, hexp]
  rw [show binade P d - 51 - 1 = binade P d - 52 by omega]
  rfl

theorem walkTicks_loBits_succ {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkTicks (loBits P d + 1) = hi P d := by
  rw [walkTicks_succ (loBits_lt hd hno hsub), walkTicks_loBits hd hno hsub,
    walkGap_loBits hd hno hsub]
  show sig P d * ulp P d + ulp P d = (sig P d + 1) * ulp P d
  rw [Nat.add_mul, Nat.one_mul]

/-! ### The ladder below the smallest normal -/

theorem walkTicks_small {n : Nat} (hn : n ≤ 2 ^ 52) : walkTicks n = n := by
  by_cases h : n < 2 ^ 52
  · have hexp : walkExp n = 0 := by
      simp only [walkExp, Nat.div_eq_of_lt h, Nat.zero_mod]
    rw [walkTicks_eq_zero hexp]
    show n % 2 ^ 52 = n
    exact Nat.mod_eq_of_lt h
  · have heq : n = 2 ^ 52 := by omega
    subst heq
    have hexp : walkExp (2 ^ 52) = 1 := by decide
    have hfrac : walkFrac (2 ^ 52) = 0 := by decide
    have hne : walkExp (2 ^ 52) ≠ 0 := by rw [hexp]; decide
    simp only [walkTicks_eq_normal hne, hfrac, hexp, Nat.add_zero, Nat.sub_self,
      Nat.pow_zero, Nat.mul_one]

theorem walkMant_small {n : Nat} (hn : n ≤ 2 ^ 52) : walkMant n = n := by
  by_cases h : n < 2 ^ 52
  · have hexp : walkExp n = 0 := by
      simp only [walkExp, Nat.div_eq_of_lt h, Nat.zero_mod]
    rw [walkMant_eq_zero hexp]
    show n % 2 ^ 52 = n
    exact Nat.mod_eq_of_lt h
  · have heq : n = 2 ^ 52 := by omega
    subst heq
    have hexp : walkExp (2 ^ 52) = 1 := by decide
    have hfrac : walkFrac (2 ^ 52) = 0 := by decide
    have hne : walkExp (2 ^ 52) ≠ 0 := by rw [hexp]; decide
    simp only [walkMant_eq_normal hne, hfrac, Nat.add_zero]

theorem downTwice_of_le {b : Nat} (hb : b ≤ 2 ^ 52) : downTwice b = 2 * b - 1 := by
  unfold downTwice
  rcases Nat.eq_zero_or_pos b with h0 | h0
  · subst h0
    rw [walkTicks_zero, Nat.zero_add]
  · rw [walkTicks_small (by omega), walkTicks_small hb]
    omega

theorem upTwice_of_le {b : Nat} (hb : b + 1 ≤ 2 ^ 52) : upTwice b = 2 * b + 1 := by
  unfold upTwice
  rw [walkTicks_small (by omega), walkTicks_small hb]
  omega

theorem downTwice_le_ticks2 {b : Nat} (hb : b < infBits) :
    downTwice b ≤ 2 * walkTicks b := by
  unfold downTwice
  have h := walkTicks_le_of_le (b := b - 1) (b' := b) (by omega) (by omega)
  omega

theorem ticks2_le_upTwice {b : Nat} (hb : b < infBits) :
    2 * walkTicks b ≤ upTwice b := by
  unfold upTwice
  have h := walkTicks_le_of_le (b := b) (b' := b + 1) (by omega) (by omega)
  omega

/-- `hi` is `lo` plus the binade's ulp. -/
theorem hi_eq_lo_add (P d : Nat) : hi P d = lo P d + ulp P d := by
  unfold hi lo
  rw [Nat.add_mul, Nat.one_mul]

theorem add_51_sub_52 (n : Nat) : n + 51 - 52 = n - 1 := by
  rw [show (52 : Nat) = 1 + 51 from rfl, Nat.add_sub_add_right]

/-- **The binade search returns the pattern's exponent field plus fifty-one.**
This is the identification between the ladder and the specification's lattice:
the search looks for the least `B` with `P < d * 2 ^ (B + 1)`, and a pattern
whose tick value is at or below the value, whose successor's is above it, and
whose tick value and successor fit the binade's two powers of two, has exponent
field `B - 51`. -/
theorem binade_eq_of_tick_bounds {P d b : Nat}
    (hle : walkTicks b * d ≤ P) (hlt : P < walkTicks (b + 1) * d)
    (hpow : 2 ^ (walkExp b + 51) ≤ walkTicks b)
    (hpow' : walkTicks (b + 1) ≤ 2 ^ (walkExp b + 52))
    (hbe : walkExp b + 51 < 2100) :
    binade P d = walkExp b + 51 := by
  have hPup : P < d * 2 ^ (walkExp b + 52) := by
    calc P < walkTicks (b + 1) * d := hlt
      _ ≤ 2 ^ (walkExp b + 52) * d := Nat.mul_le_mul_right d hpow'
      _ = d * 2 ^ (walkExp b + 52) := Nat.mul_comm _ _
  have hex : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1) := ⟨walkExp b + 51, hbe, hPup⟩
  obtain ⟨hup, hmin⟩ := binade_spec hex
  refine le_antisymm ?_ ?_
  · apply Nat.le_of_not_lt
    intro hlt'
    have h := hmin (walkExp b + 51) hlt'
    rw [show walkExp b + 51 + 1 = walkExp b + 52 from by rw [Nat.add_assoc]] at h
    exact absurd hPup (Nat.not_lt.mpr h)
  · apply Nat.le_of_not_lt
    intro hlt'
    have hle' : binade P d + 1 ≤ walkExp b + 51 := Nat.succ_le_of_lt hlt'
    have hble : d * 2 ^ (binade P d + 1) ≤ d * 2 ^ (walkExp b + 51) :=
      Nat.mul_le_mul_left d (two_pow_le_iff.mpr hle')
    have hdle : d * 2 ^ (walkExp b + 51) ≤ d * walkTicks b :=
      Nat.mul_le_mul_left d hpow
    have hdle' : d * walkTicks b ≤ walkTicks b * d := le_of_eq (Nat.mul_comm d _)
    exact absurd hup
      (Nat.not_lt.mpr (le_trans hble (le_trans hdle (le_trans hdle' hle))))

/-- **The lattice is the ladder's.**  A pattern whose tick value is at or below
the exact value and whose successor's is above it, and whose tick value and
successor fit the binade's two powers of two, sits where the specification
rounds: `ulp` is the pattern's gap, and `lo`/`hi` are its tick value and its
successor's. -/
theorem walk_lattice_eq {P d b : Nat} (hd : 0 < d)
    (hle : walkTicks b * d ≤ P) (hlt : P < walkTicks (b + 1) * d)
    (hpow : 2 ^ (walkExp b + 51) ≤ walkTicks b)
    (hpow' : walkTicks (b + 1) ≤ 2 ^ (walkExp b + 52))
    (hbe1 : 1 ≤ walkExp b) (hbe : walkExp b + 51 < 2100) (hb : b < infBits) :
    binade P d = walkExp b + 51 ∧ ulp P d = walkGap b ∧
      lo P d = walkTicks b ∧ hi P d = walkTicks (b + 1) := by
  have hB : binade P d = walkExp b + 51 :=
    binade_eq_of_tick_bounds hle hlt hpow hpow' hbe
  have hne0 : 0 < walkExp b := Nat.succ_le_iff.mp hbe1
  have hulp : ulp P d = walkGap b := by
    have hne : walkExp b ≠ 0 := Nat.ne_of_gt hne0
    rw [walkGap_eq_normal hne]
    show 2 ^ (binade P d - 52) = 2 ^ (walkExp b - 1)
    rw [hB, add_51_sub_52]
  -- the pattern's tick value is a multiple of the binade's ulp
  have hne : walkExp b ≠ 0 := Nat.ne_of_gt hne0
  have hmul : walkTicks b = walkMant b * ulp P d := by
    rw [walkTicks_eq_normal hne, walkMant_eq_normal hne, hulp, walkGap_eq_normal hne]
  -- and its quotient is at most the significand
  have hmle : walkMant b ≤ sig P d := by
    have h1 : walkMant b * (ulp P d * d) ≤ P := by
      rw [← Nat.mul_assoc, ← hmul]
      exact hle
    have h2 : walkMant b * (d * ulp P d) ≤ P := by
      rwa [Nat.mul_comm (ulp P d) d] at h1
    rw [show sig P d = P / (d * ulp P d) from rfl]
    exact (Nat.le_div_iff_mul_le (mul_ulp_pos hd P)).mpr h2
  have hle_lo : walkTicks b ≤ lo P d := by
    have h2 : walkMant b * ulp P d ≤ sig P d * ulp P d :=
      Nat.mul_le_mul_right (ulp P d) hmle
    rwa [← hmul] at h2
  -- a smaller lattice point would put the successor's tick value at or below
  -- the value, which the sandwich forbids
  have hnlt : ¬ walkTicks b < lo P d := by
    intro hh
    have hltm : walkMant b < sig P d := by
      refine lt_of_mul_lt_mul_right (c := ulp P d) ?_
      rw [← hmul]
      exact hh
    have hs : (walkMant b + 1) * ulp P d ≤ sig P d * ulp P d :=
      Nat.mul_le_mul_right (ulp P d) (Nat.succ_le_of_lt hltm)
    have hstep : walkTicks (b + 1) = walkTicks b + walkGap b := walkTicks_succ hb
    rw [← hulp] at hstep
    have h1 : walkTicks (b + 1) ≤ lo P d := by
      rw [hstep, hmul]
      rw [Nat.add_mul, Nat.one_mul] at hs
      exact hs
    have h3 : walkTicks (b + 1) * d ≤ lo P d * d := Nat.mul_le_mul_right d h1
    have h4 : lo P d * d ≤ P := lo_d_le (P := P) (d := d)
    exact absurd hlt (Nat.not_lt.mpr (le_trans h3 h4))
  have hlo : lo P d = walkTicks b := le_antisymm (Nat.le_of_not_lt hnlt) hle_lo
  refine ⟨hB, hulp, hlo, ?_⟩
  have hstep : walkTicks (b + 1) = walkTicks b + walkGap b := walkTicks_succ hb
  have hhi := hi_eq_lo_add P d
  rw [hulp] at hhi
  rw [hhi, hstep, hlo]

/-! ### The target: the interval at the specification's answer

`inInterval P d b` says the value lies in `b`'s rounding interval, with a
midpoint tie going to the even significand.  The specification's answer has
exactly that: below the subnormal edge the ladder is the tick lattice itself,
and above it the bridge above makes `lo` and `hi` the ladder's two points. -/

theorem bitsOf_sub_code (q : Nat) : bitsOf (⟨0, q⟩ : Code) = q :=
  bitsOf_sub rfl

theorem bitsOf_carry_code : bitsOf (⟨1, 2 ^ 52⟩ : Code) = 2 ^ 52 := by
  rw [bitsOf_normal (by decide : (1 : Nat) ≠ 0), Nat.sub_self, Nat.add_zero, Nat.one_mul]

theorem bitsOf_sub_succ {q : Nat} :
    bitsOf (if q + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else ⟨0, q + 1⟩) = q + 1 := by
  by_cases h : q + 1 = 2 ^ 52
  · rw [ite_eq_left h, bitsOf_carry_code, h]
  · rw [ite_eq_right h, bitsOf_sub_code]

theorem bitsOf_normal_succ {B q : Nat} (hB : 52 ≤ B) (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53) :
    bitsOf (if q + 1 = 2 ^ 53 then (⟨B - 50, 2 ^ 52⟩ : Code) else ⟨B - 51, q + 1⟩)
      = bitsOf (⟨B - 51, q⟩ : Code) + 1 := by
  have h1 : bitsOf (⟨B - 51, q⟩ : Code) = (B - 51) * 2 ^ 52 + (q - 2 ^ 52) := by
    refine bitsOf_normal ?_
    show B - 51 ≠ 0
    omega
  by_cases h : q + 1 = 2 ^ 53
  · have hcarry : bitsOf (⟨B - 50, 2 ^ 52⟩ : Code) = (B - 50) * 2 ^ 52 := by
      rw [bitsOf_normal (show B - 50 ≠ 0 by omega), Nat.sub_self, Nat.add_zero]
    rw [ite_eq_left h, hcarry, h1]
    have hBs : B - 50 = (B - 51) + 1 := by omega
    have hq : q - 2 ^ 52 = 2 ^ 52 - 1 := by omega
    have hy : 2 ^ 52 - 1 + 1 = 2 ^ 52 := Nat.sub_add_cancel (by decide : 1 ≤ 2 ^ 52)
    rw [hBs, Nat.add_mul, Nat.one_mul, hq]
    omega
  · have hn : bitsOf (⟨B - 51, q + 1⟩ : Code) = (B - 51) * 2 ^ 52 + (q + 1 - 2 ^ 52) := by
      refine bitsOf_normal ?_
      show B - 51 ≠ 0
      omega
    rw [ite_eq_right h, hn, h1]
    have hq : q + 1 - 2 ^ 52 = q - 2 ^ 52 + 1 := by omega
    rw [hq]
    omega

/-! #### Below the subnormal edge -/

theorem div_mod_eq {P d : Nat} : P / d * d + P % d = P := by
  have := Nat.div_add_mod P d
  rwa [Nat.mul_comm d (P / d)] at this

/-- The floor significand's interval in the subnormal region: the value is at or
below the upper midpoint, and a tie there is the even significand's. -/
theorem inInterval_sub_lo {P d q r : Nat} (hd : 0 < d) (hq : q = P / d)
    (hr : r = P % d) (hq2 : q < 2 ^ 52) (hle2 : 2 * r ≤ d)
    (heven : 2 * r = d → q % 2 = 0) :
    inInterval P d q := by
  have hqle : q ≤ 2 ^ 52 := le_of_lt hq2
  have hq1le : q + 1 ≤ 2 ^ 52 := Nat.succ_le_of_lt hq2
  have hdec : q * d + r = P := by
    rw [hq, hr]
    exact div_mod_eq
  have hrem : r < d := by
    rw [hr]
    exact Nat.mod_lt _ hd
  have h2P : 2 * P = 2 * (q * d) + 2 * r := by rw [← hdec, Nat.mul_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [downTwice_of_le hqle, Nat.sub_mul, Nat.one_mul, Nat.mul_assoc]
    exact le_trans (Nat.sub_le _ _)
      (le_trans (Nat.le_add_right _ _) (le_of_eq h2P.symm))
  · rw [upTwice_of_le hq1le, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, h2P]
    exact Nat.add_le_add_left hle2 _
  · intro htie
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · rw [h0, walkMant_zero]
    · exfalso
      have hXpos : 0 < 2 * (q * d) :=
        Nat.mul_pos (by decide) (Nat.mul_pos h0 hd)
      rw [downTwice_of_le hqle, Nat.sub_mul, Nat.one_mul, Nat.mul_assoc, h2P] at htie
      have hlt : 2 * (q * d) - d < 2 * (q * d) := Nat.sub_lt hXpos hd
      have hge : 2 * (q * d) ≤ 2 * (q * d) - d := by
        rw [htie]
        exact Nat.le_add_right _ _
      exact absurd hge (Nat.not_le.mpr hlt)
  · intro htie
    have h2r : 2 * r = d := by
      rw [upTwice_of_le hq1le, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, h2P] at htie
      exact Nat.add_left_cancel htie.symm
    rw [walkMant_small hqle]
    exact heven h2r

/-- The ceiling significand's interval in the subnormal region: the value is at
or above the lower midpoint, and a tie there is the even significand's. -/
theorem inInterval_sub_hi {P d q r : Nat} (hd : 0 < d) (hq : q = P / d)
    (hr : r = P % d) (hq2 : q < 2 ^ 52) (hge2 : d ≤ 2 * r)
    (heven : d = 2 * r → (q + 1) % 2 = 0) :
    inInterval P d (q + 1) := by
  have hqle : q ≤ 2 ^ 52 := le_of_lt hq2
  have hq1le : q + 1 ≤ 2 ^ 52 := Nat.succ_le_of_lt hq2
  have hdec : q * d + r = P := by
    rw [hq, hr]
    exact div_mod_eq
  have hrem : r < d := by
    rw [hr]
    exact Nat.mod_lt _ hd
  have h2P : 2 * P = 2 * (q * d) + 2 * r := by rw [← hdec, Nat.mul_add]
  have hqd1 : (q + 1) * d = q * d + d := by rw [Nat.add_mul, Nat.one_mul]
  have hkey : 2 * (q + 1) - 1 = 2 * q + 1 := by omega
  have htin : q + 1 < infBits := by
    have h4 : 2 ^ 52 < infBits := by
      simp only [infBits]
      have h52 : 0 < 2 ^ 52 := by decide
      calc 2 ^ 52 = 1 * 2 ^ 52 := (Nat.one_mul _).symm
        _ < 2047 * 2 ^ 52 := Nat.mul_lt_mul_of_pos_right (by decide) h52
    have h5 : q + 1 ≤ 2 ^ 52 := hq1le
    omega
  have ht1 : walkTicks (q + 1) = q + 1 := walkTicks_small hq1le
  have htw : 2 * walkTicks (q + 1) ≤ upTwice (q + 1) := ticks2_le_upTwice htin
  rw [ht1] at htw
  have h2d : 2 * (q + 1) * d = 2 * (q * d) + 2 * d := by
    rw [Nat.mul_assoc, hqd1, Nat.mul_add]
  have hsmall : 2 * (q * d) + 2 * r < 2 * (q + 1) * d := by
    rw [h2d]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hrem (by decide)) _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [downTwice_of_le hq1le, hkey, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, h2P]
    exact Nat.add_le_add_left hge2 _
  · rw [h2P]
    exact le_trans (le_of_lt hsmall) (Nat.mul_le_mul_right d htw)
  · intro htie
    have h2r : d = 2 * r := by
      rw [downTwice_of_le hq1le, hkey, Nat.add_mul, Nat.one_mul, Nat.mul_assoc, h2P] at htie
      exact Nat.add_left_cancel htie
    rw [walkMant_small hq1le]
    exact heven h2r
  · intro htie
    exfalso
    have hlt : 2 * P < upTwice (q + 1) * d := by
      rw [h2P]
      exact lt_of_lt_of_le hsmall (Nat.mul_le_mul_right d htw)
    rw [htie] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- **The specification's answer has the interval `inInterval` names**, in the
subnormal region: the answer is the quotient or its successor, and the branch
that chose it is the interval's two ends and its tie clause. -/
theorem inInterval_subCode {P d : Nat} (hd : 0 < d) (hsub : P < d * 2 ^ 52) :
    inInterval P d (bitsOf (subCode P d)) := by
  have hq2 : P / d < 2 ^ 52 := sub_sig_lt hd hsub
  by_cases h1 : 2 * (P % d) < d
  · have hcode : subCode P d = ⟨0, P / d⟩ := by simp only [subCode, h1, reduceIte]
    rw [hcode, bitsOf_sub_code]
    exact inInterval_sub_lo hd rfl rfl hq2 (le_of_lt h1)
      (fun he => absurd he (Nat.ne_of_lt h1))
  · by_cases h2 : d < 2 * (P % d)
    · have hcode : subCode P d =
          (if P / d + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else ⟨0, P / d + 1⟩) := by
        simp only [subCode, h1, h2, reduceIte]
      rw [hcode, bitsOf_sub_succ]
      exact inInterval_sub_hi hd rfl rfl hq2 (le_of_lt h2)
        (fun he => absurd he (Nat.ne_of_lt h2))
    · have h3 : 2 * (P % d) = d :=
        le_antisymm (Nat.le_of_not_lt h2) (Nat.le_of_not_lt h1)
      by_cases h4 : P / d % 2 = 0
      · have hcode : subCode P d = ⟨0, P / d⟩ := by
          simp only [subCode, h1, h2, h4, reduceIte]
        rw [hcode, bitsOf_sub_code]
        exact inInterval_sub_lo hd rfl rfl hq2 (le_of_eq h3) (fun _ => h4)
      · have hcode : subCode P d =
            (if P / d + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else ⟨0, P / d + 1⟩) := by
          simp only [subCode, h1, h2, h4, reduceIte]
        rw [hcode, bitsOf_sub_succ]
        refine inInterval_sub_hi hd rfl rfl hq2 (le_of_eq h3.symm) (fun _ => ?_)
        have hone : P / d % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one (P / d) with h | h
          · exact absurd h h4
          · exact h
        show (P / d + 1) % 2 = 0
        omega

/-! #### Above the subnormal edge -/

theorem normal_ticks_lo {P d : Nat} (hB : 52 ≤ binade P d) :
    (⟨binade P d - 51, sig P d⟩ : Code).ticks = lo P d := by
  rw [ticks_normal (show binade P d - 51 ≠ 0 by omega)]
  rw [show binade P d - 51 - 1 = binade P d - 52 by omega]
  rfl

theorem walkTicks_loBits_sub {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    walkTicks (loBits P d + 1 - 1) = lo P d := by
  rw [show loBits P d + 1 - 1 = loBits P d from by omega]
  exact walkTicks_loBits hd hno hsub

theorem upTwice_loBits {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    upTwice (loBits P d) = lo P d + hi P d := by
  unfold upTwice
  rw [walkTicks_loBits hd hno hsub, walkTicks_loBits_succ hd hno hsub]

theorem downTwice_loBits_succ {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    downTwice (loBits P d + 1) = lo P d + hi P d := by
  unfold downTwice
  rw [walkTicks_loBits_sub hd hno hsub, walkTicks_loBits_succ hd hno hsub]

theorem loBits_ge {P d : Nat} (hd : 0 < d) (hno : ¬ overflowTicks * d ≤ P)
    (hsub : ¬ P < d * 2 ^ 52) : 2 ^ 52 ≤ loBits P d := by
  obtain ⟨hB, hB', hblo, hbup⟩ := binade_facts hd hno hsub
  obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hblo hbup
  have hdecomp : loBits P d = (binade P d - 51) * 2 ^ 52 + (sig P d - 2 ^ 52) :=
    bitsOf_normal (show binade P d - 51 ≠ 0 by omega)
  have h1 : (1 : Nat) * 2 ^ 52 ≤ (binade P d - 51) * 2 ^ 52 :=
    Nat.mul_le_mul_right _ (by omega)
  rw [Nat.one_mul] at h1
  omega

theorem loBits_pos {P d : Nat} (hd : 0 < d) (hno : ¬ overflowTicks * d ≤ P)
    (hsub : ¬ P < d * 2 ^ 52) : 0 < loBits P d := by
  have h := loBits_ge hd hno hsub
  omega

/-- The ceiling code of the normal region, as `normalCode` writes it. -/
def ceilCode (P d : Nat) : Code :=
  if sig P d + 1 = 2 ^ 53 then (⟨binade P d - 50, 2 ^ 52⟩ : Code)
    else ⟨binade P d - 51, sig P d + 1⟩

/-- The answer at the lattice's ceiling point: the value is above the lower
midpoint (`normal_choice_le`) and below the upper one, and a midpoint tie is the
even significand's (`roundMag_midpoint_even`). -/
theorem inInterval_ceiling {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52)
    (hc : roundMag P d = .fin (ceilCode P d)) (hcode : normalCode P d = ceilCode P d) :
    inInterval P d (loBits P d + 1) := by
  obtain ⟨hB, hB', hblo, hbup⟩ := binade_facts hd hno hsub
  obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hblo hbup
  have hthi : walkTicks (loBits P d + 1) = hi P d := walkTicks_loBits_succ hd hno hsub
  have hlole : lo P d * d ≤ P := lo_d_le P d
  have hhigt : P < hi P d * d := lt_hi_d (mul_ulp_pos hd P)
  have hnot : ¬ hi P d * d ≤ P := Nat.not_le.mpr hhigt
  have hmag : (ceilCode P d).IsMag := by
    obtain ⟨c', hc', hmag'⟩ := roundMag_isCode (P := P) (d := d) hd hno
    rw [hc] at hc'
    rw [Mag.fin.injEq] at hc'
    rw [hc']
    exact hmag'
  have hcb : bitsOf (ceilCode P d) = loBits P d + 1 := bitsOf_normal_succ hB hq1 hq2
  have hlt : loBits P d + 1 < infBits := by
    rw [← hcb]
    exact bitsOf_lt_infBits hmag
  have hchoice := (normal_choice_le (P := P) (d := d) hd hB).1
  have hticks : (ceilCode P d).ticks = hi P d := by
    rw [← walkTicks_bitsOf hmag, hcb, hthi]
  rw [hcode, hticks] at hchoice
  simp only [distNum, hlole, hnot, reduceIte] at hchoice
  have hdown2 : downTwice (loBits P d + 1) = lo P d + hi P d :=
    downTwice_loBits_succ hd hno hsub
  have hupge : 2 * walkTicks (loBits P d + 1) ≤ upTwice (loBits P d + 1) :=
    ticks2_le_upTwice hlt
  rw [hthi] at hupge
  have h2P : 2 * P < 2 * (hi P d * d) :=
    Nat.mul_lt_mul_of_pos_left hhigt (by decide : 0 < 2)
  have hmid2 : 2 * (hi P d * d) ≤ upTwice (loBits P d + 1) * d := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right d hupge
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdown2, Nat.add_mul]
    omega
  · omega
  · intro htie
    have hmid : P - lo P d * d = hi P d * d - P := by
      rw [hdown2, Nat.add_mul] at htie
      omega
    rw [← hcb, walkMant_bitsOf hmag]
    exact roundMag_midpoint_even hd hno hmid hc
  · intro htie
    exfalso
    omega

/-- **The specification's answer has the interval `inInterval` names**, in the
normal region. -/
theorem inInterval_normalCode {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) {c : Code}
    (hc : roundMag P d = .fin c) (hcn : c = normalCode P d) :
    inInterval P d (bitsOf c) := by
  obtain ⟨hB, hB', hblo, hbup⟩ := binade_facts hd hno hsub
  obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hblo hbup
  have hbits : loBits P d < infBits := loBits_lt hd hno hsub
  have htlo : walkTicks (loBits P d) = lo P d := walkTicks_loBits hd hno hsub
  have hlole : lo P d * d ≤ P := lo_d_le P d
  have hhigt : P < hi P d * d := lt_hi_d (mul_ulp_pos hd P)
  have hnot : ¬ hi P d * d ≤ P := Nat.not_le.mpr hhigt
  have hchoice := (normal_choice_le (P := P) (d := d) hd hB).2
  have hup2 : upTwice (loBits P d) = lo P d + hi P d := upTwice_loBits hd hno hsub
  have floor_case : ∀ (hcode : normalCode P d = ⟨binade P d - 51, sig P d⟩)
      (hcc : c = ⟨binade P d - 51, sig P d⟩), inInterval P d (loBits P d) := by
    intro hcode hcc
    have hcce : roundMag P d = .fin (⟨binade P d - 51, sig P d⟩ : Code) := by rw [hc, hcc]
    have hd2 := hchoice
    rw [hcode, normal_ticks_lo hB] at hd2
    simp only [distNum, hlole, hnot, reduceIte] at hd2
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hle := downTwice_le_ticks2 hbits
      rw [htlo] at hle
      have h2 : (2 * lo P d) * d ≤ 2 * P := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 2 hlole
      exact le_trans (Nat.mul_le_mul_right d hle) h2
    · rw [hup2, Nat.add_mul]
      omega
    · intro htie
      exfalso
      have hb0 : 0 < loBits P d := loBits_pos hd hno hsub
      have hlt := downTwice_lt_ticks hb0 hbits
      rw [htlo] at hlt
      have h2 : downTwice (loBits P d) * d < (2 * lo P d) * d :=
        Nat.mul_lt_mul_of_pos_right hlt hd
      rw [Nat.mul_assoc] at h2
      have h4 : 2 * (lo P d * d) ≤ 2 * P := Nat.mul_le_mul_left 2 hlole
      omega
    · intro htie
      have hmid : P - lo P d * d = hi P d * d - P := by
        rw [hup2, Nat.add_mul] at htie
        omega
      have heven := roundMag_midpoint_even hd hno hmid hcce
      rw [walkMant_loBits hd hno hsub]
      exact heven
  by_cases h1 : 2 * (P % (d * ulp P d)) < d * ulp P d
  · have hcode : normalCode P d = ⟨binade P d - 51, sig P d⟩ := by
      simp only [normalCode, sig, h1, reduceIte]
    have hcc : c = ⟨binade P d - 51, sig P d⟩ := by rw [hcn, hcode]
    have hcb : bitsOf c = loBits P d := by rw [hcc]; rfl
    rw [hcb]
    exact floor_case hcode hcc
  · by_cases h2 : d * ulp P d < 2 * (P % (d * ulp P d))
    · have hcode : normalCode P d = ceilCode P d := by
        simp only [ceilCode, sig, normalCode, h1, h2, reduceIte]
        rfl
      have hcc : c = ceilCode P d := by rw [hcn, hcode]
      have hcb : bitsOf c = loBits P d + 1 := by rw [hcc]; exact bitsOf_normal_succ hB hq1 hq2
      rw [hcb]
      have hcE : roundMag P d = .fin (ceilCode P d) := by rw [hc, hcc]
      exact inInterval_ceiling hd hno hsub hcE hcode
    · by_cases h4 : P / (d * ulp P d) % 2 = 0
      · have hcode : normalCode P d = ⟨binade P d - 51, sig P d⟩ := by
          simp only [normalCode, sig, h1, h2, h4, reduceIte]
        have hcc : c = ⟨binade P d - 51, sig P d⟩ := by rw [hcn, hcode]
        have hcb : bitsOf c = loBits P d := by rw [hcc]; rfl
        rw [hcb]
        exact floor_case hcode hcc
      · have hcode : normalCode P d = ceilCode P d := by
          simp only [ceilCode, sig, normalCode, h1, h2, h4, reduceIte]
          rfl
        have hcc : c = ceilCode P d := by rw [hcn, hcode]
        have hcb : bitsOf c = loBits P d + 1 := by rw [hcc]; exact bitsOf_normal_succ hB hq1 hq2
        rw [hcb]
        have hcE : roundMag P d = .fin (ceilCode P d) := by rw [hc, hcc]
        exact inInterval_ceiling hd hno hsub hcE hcode

/-- **The target.**  Under the overflow threshold, the specification's answer's
own pattern is the candidate whose interval contains the value. -/
theorem inInterval_roundMag {P d : Nat} (hd : 0 < d) (hno : ¬ inTop P d) {c : Code}
    (hc : roundMag P d = .fin c) : inInterval P d (bitsOf c) := by
  have hno' : ¬ (overflowTicks * d ≤ P) := hno
  have hc0 : roundMag P d = .fin c := hc
  unfold roundMag at hc
  rw [ite_eq_right hno'] at hc
  by_cases hsub : P < d * 2 ^ 52
  · rw [ite_eq_left hsub] at hc
    have hc' : c = subCode P d := (Mag.fin.inj hc).symm
    rw [hc']
    exact inInterval_subCode hd hsub
  · rw [ite_eq_right hsub] at hc
    have hcn : c = normalCode P d := (Mag.fin.inj hc).symm
    have hmag : c.IsMag := by
      obtain ⟨c', hc', hmag'⟩ := roundMag_isCode (P := P) (d := d) hd hno'
      rw [hc0] at hc'
      rw [Mag.fin.injEq] at hc'
      rw [hc']
      exact hmag'
    exact inInterval_normalCode hd hno' hsub hc0 hcn

/-! ### The descent

The five finite verdicts are the step's; what they are consumed by is the
recursion that runs them.  The measure is `(tgt - b) + (b - tgt)`: a stop is at
the target (`stop_fin_interval` and `inInterval_uniq`), a step up happens only
when the value is above the upper midpoint (`step_fin_move_next`), so the answer
is above `b`, and a step down only when it is below the lower one
(`step_fin_move_pred`).  Each is a strict decrease of that measure, so the run
halts at the target from any finite pattern. -/

/-- One run of the loop: `n` steps from `b`, read as the pattern it halts at;
`none` when the steps run out before a stop. -/
def walkLoop (P d : Nat) : Nat → Nat → Option Nat
  | 0, b =>
    match walkStep P d b with
    | .stop b' => some b'
    | .move _ => none
  | n + 1, b =>
    match walkStep P d b with
    | .stop b' => some b'
    | .move b' => walkLoop P d n b'

theorem walkLoop_stop {P d n b e : Nat} (h : walkStep P d b = .stop e) :
    walkLoop P d (n + 1) b = some e := by
  simp only [walkLoop, h]

theorem walkLoop_move {P d n b e : Nat} (h : walkStep P d b = .move e) :
    walkLoop P d (n + 1) b = walkLoop P d n e := by
  simp only [walkLoop, h]

theorem walkStep_zero_cases (P d : Nat) :
    walkStep P d 0 = .move 1 ∨ walkStep P d 0 = .stop 0 := by
  unfold walkStep
  rw [ite_eq_left rfl]
  by_cases h : 0 < cmpWalk P d (upTwice 0)
  · exact Or.inl (ite_eq_left h)
  · exact Or.inr (ite_eq_right h)

/-- A finite step's move goes to one of the two neighbours. -/
theorem move_fin_mem {P d b e : Nat} (hb0 : 0 < b) (hb : b < infBits)
    (h : walkStep P d b = .move e) : e = b - 1 ∨ e = b + 1 := by
  rw [walkStep_fin hb0 hb] at h
  by_cases hs : cmpWalk P d (2 * walkTicks b) = 0
  · rw [ite_eq_left hs] at h
    exact absurd h (WalkResult.stop_ne_move b e)
  rw [ite_eq_right hs] at h
  by_cases hs2 : 0 < cmpWalk P d (2 * walkTicks b)
  · rw [ite_eq_left hs2] at h
    by_cases hu : cmpWalk P d (upTwice b) < 0
    · rw [ite_eq_left hu] at h
      exact absurd h (WalkResult.stop_ne_move b e)
    rw [ite_eq_right hu] at h
    by_cases hu2 : cmpWalk P d (upTwice b) = 0
    · rw [ite_eq_left hu2] at h
      by_cases he : walkMant b % 2 = 0
      · rw [ite_eq_left he] at h
        exact absurd h (WalkResult.stop_ne_move b e)
      · rw [ite_eq_right he] at h
        exact absurd h (WalkResult.stop_ne_move (b + 1) e)
    rw [ite_eq_right hu2] at h
    exact Or.inr (WalkResult.move.inj h).symm
  rw [ite_eq_right hs2] at h
  by_cases hd1 : 0 < cmpWalk P d (downTwice b)
  · rw [ite_eq_left hd1] at h
    exact absurd h (WalkResult.stop_ne_move b e)
  rw [ite_eq_right hd1] at h
  by_cases hd2 : cmpWalk P d (downTwice b) = 0
  · rw [ite_eq_left hd2] at h
    by_cases he : walkMant b % 2 = 0
    · rw [ite_eq_left he] at h
      exact absurd h (WalkResult.stop_ne_move b e)
    · rw [ite_eq_right he] at h
      exact absurd h (WalkResult.stop_ne_move (b - 1) e)
  rw [ite_eq_right hd2] at h
  exact Or.inl (WalkResult.move.inj h).symm

theorem downTwice_le_of_le {b b' : Nat} (h : b ≤ b') (hb' : b' < infBits) :
    downTwice b ≤ downTwice b' := by
  unfold downTwice
  have h1 : walkTicks (b - 1) ≤ walkTicks (b' - 1) :=
    walkTicks_le_of_le (by omega) (by omega)
  have h2 : walkTicks b ≤ walkTicks b' := walkTicks_le_of_le h (by omega)
  omega

/-- **The descent reaches the interval's candidate.**  From any finite pattern,
the loop stops at the candidate whose interval contains the value. -/
theorem walkLoop_stops_of_interval {P d tgt : Nat} (hd : 0 < d)
    (htgt : tgt < infBits) (hint : inInterval P d tgt) :
    ∀ b, b < infBits → ∃ n, walkLoop P d n b = some tgt := by
  suffices h : ∀ k, ∀ b, b < infBits → (tgt - b) + (b - tgt) = k →
      ∃ n, walkLoop P d n b = some tgt from fun b hb => h _ b hb rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b hb hdist
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · -- the zero escape
      subst hb0
      rcases walkStep_zero_cases P d with hstep | hstep
      · have hne : tgt ≠ 0 := by
          intro h0
          subst h0
          have hcmp : 0 < cmpWalk P d (upTwice 0) := by
            unfold walkStep at hstep
            rw [ite_eq_left rfl] at hstep
            by_contra hcon
            rw [ite_eq_right hcon] at hstep
            exact absurd hstep (WalkResult.stop_ne_move 0 1)
          have hup : upTwice 0 * d < 2 * P := by
            rcases cmpWalk_mem P d (upTwice 0) with h' | h' | h'
            · rw [h'] at hcmp
              exact absurd hcmp (by decide)
            · rw [h'] at hcmp
              exact absurd hcmp (by decide)
            · exact cmpWalk_gt.mp h'
          have hle : 2 * P ≤ upTwice 0 * d := hint.2.1
          omega
        obtain ⟨n, hn⟩ := ih (tgt - 1) (by omega) 1 (by omega) (by omega)
        exact ⟨n + 1, by rw [walkLoop_move hstep]; exact hn⟩
      · have hi0 := step_zero_stop hstep
        have heq : tgt = 0 := inInterval_uniq hd htgt (by omega : 0 < infBits) hint hi0
        refine ⟨1, ?_⟩
        rw [heq]
        exact walkLoop_stop hstep
    · -- the finite body
      have hbpos : 0 < b := hb0
      cases hstep : walkStep P d b with
      | stop e =>
        rcases stop_fin_mem hbpos hb hstep with h1 | h2 | h3
        · rw [h1] at hstep
          have hlt : b - 1 < infBits := by omega
          have hmem := stop_fin_interval hd hbpos hb hstep hlt
          have heq : tgt = b - 1 := inInterval_uniq hd htgt hlt hint hmem
          refine ⟨1, ?_⟩
          rw [heq]
          exact walkLoop_stop hstep
        · rw [h2] at hstep
          have hmem := step_fin_stop_self hd hbpos hb hstep
          have heq : tgt = b := inInterval_uniq hd htgt hb hint hmem
          refine ⟨1, ?_⟩
          rw [heq]
          exact walkLoop_stop hstep
        · rw [h3] at hstep
          by_cases hlt : b + 1 < infBits
          · have hmem := stop_fin_interval hd hbpos hb hstep hlt
            have heq : tgt = b + 1 := inInterval_uniq hd htgt hlt hint hmem
            refine ⟨1, ?_⟩
            rw [heq]
            exact walkLoop_stop hstep
          · exfalso
            have hbeq : b = maxBits := by
              have := maxBits_succ
              omega
            obtain ⟨htie, -⟩ := step_fin_stop_next hbpos hb hstep
            have htop : inTop P d := by
              unfold inTop
              rw [hbeq, upTwice_maxBits, Nat.mul_assoc] at htie
              exact Nat.le_of_mul_le_mul_left (le_of_eq htie) (by decide : 0 < 2)
            exact inInterval_not_top hd htgt hint htop
      | move e =>
        rcases move_fin_mem hbpos hb hstep with h1 | h2
        · rw [h1] at hstep
          have hdown : 2 * P < downTwice b * d := step_fin_move_pred hbpos hb hstep
          have hlt : tgt < b := by
            by_contra hcon
            have hge : b ≤ tgt := Nat.le_of_not_lt hcon
            have hmono : downTwice b ≤ downTwice tgt := downTwice_le_of_le hge htgt
            have h2' : downTwice b * d ≤ downTwice tgt * d := Nat.mul_le_mul_right d hmono
            have h3 : downTwice tgt * d ≤ 2 * P := hint.1
            omega
          obtain ⟨n, hn⟩ := ih ((tgt - (b - 1)) + ((b - 1) - tgt)) (by omega) (b - 1)
            (by omega) rfl
          exact ⟨n + 1, by rw [walkLoop_move hstep]; exact hn⟩
        · rw [h2] at hstep
          have hup : upTwice b * d < 2 * P := step_fin_move_next hbpos hb hstep
          have hgt : b < tgt := by
            by_contra hcon
            have hle : tgt ≤ b := Nat.le_of_not_lt hcon
            have hmono : upTwice tgt ≤ upTwice b := upTwice_le_of_le hle hb
            have h2' : upTwice tgt * d ≤ upTwice b * d := Nat.mul_le_mul_right d hmono
            have h3 : 2 * P ≤ upTwice tgt * d := hint.2.1
            omega
          obtain ⟨n, hn⟩ := ih ((tgt - (b + 1)) + ((b + 1) - tgt)) (by omega) (b + 1)
            (by omega) rfl
          exact ⟨n + 1, by rw [walkLoop_move hstep]; exact hn⟩

/-! ### Under the overflow threshold the loop climbs

When the value is at or above the overflow threshold, every test the body makes
compares against a boundary at or below twice the threshold, so the value is
above every upper midpoint and the pattern rises one step at a time to the
infinity pattern. -/

theorem step_fin_top {P d b : Nat} (hd : 0 < d) (htop : inTop P d) (hb0 : 0 < b)
    (hb : b < infBits) :
    walkStep P d b = .move (b + 1) ∨ walkStep P d b = .stop infBits := by
  have hble : b ≤ maxBits := by
    have hmax : maxBits = infBits - 1 := rfl
    omega
  have hup_le : upTwice b ≤ 2 * overflowTicks := upTwice_le_top hble
  have htop2 : 2 * overflowTicks * d ≤ 2 * P := by
    have h := Nat.mul_le_mul_left 2 htop
    rw [Nat.mul_assoc]
    exact h
  have hcmp1 : 0 < cmpWalk P d (2 * walkTicks b) := by
    have h1 := walkTicks_lt_upTwice hb
    have h2 : 2 * walkTicks b * d < upTwice b * d := Nat.mul_lt_mul_of_pos_right h1 hd
    have h3 : upTwice b * d ≤ 2 * overflowTicks * d := Nat.mul_le_mul_right d hup_le
    have h4 : cmpWalk P d (2 * walkTicks b) = 1 := cmpWalk_gt.mpr (by omega)
    omega
  have hne0 : ¬ cmpWalk P d (2 * walkTicks b) = 0 := by omega
  rw [walkStep_fin hb0 hb, ite_eq_right hne0, ite_eq_left hcmp1]
  by_cases hu : cmpWalk P d (upTwice b) < 0
  · exfalso
    have hneg : cmpWalk P d (upTwice b) = -1 := by
      rcases cmpWalk_mem P d (upTwice b) with h | h | h
      · exact h
      · rw [h] at hu
        exact absurd hu (by decide)
      · rw [h] at hu
        exact absurd hu (by decide)
    have h1 : 2 * P < upTwice b * d := cmpWalk_lt.mp hneg
    have h3 : upTwice b * d ≤ 2 * overflowTicks * d := Nat.mul_le_mul_right d hup_le
    omega
  by_cases hu2 : cmpWalk P d (upTwice b) = 0
  · right
    have htie : upTwice b * d = 2 * P := (cmpWalk_eq.mp hu2).symm
    have hge : 2 * overflowTicks ≤ upTwice b := by
      have h : 2 * overflowTicks * d ≤ upTwice b * d := by rw [htie]; exact htop2
      exact Nat.le_of_mul_le_mul_right h hd
    have hbmax : b = maxBits := upTwice_eq_top hble (le_antisymm hup_le hge)
    have hodd : walkMant b % 2 ≠ 0 := by
      rw [hbmax, walkMant_maxBits, two_pow_53_pred_mod_two]
      decide
    rw [ite_eq_right hu, ite_eq_left hu2, ite_eq_right hodd, hbmax, maxBits_succ]
  · left
    rw [ite_eq_right hu, ite_eq_right hu2]

/-- The infinity pattern stops under the overflow threshold: the only test left
is the overflow boundary, which the value is at or above. -/
theorem step_top_stop_of_top {P d : Nat} (htop : inTop P d) :
    walkStep P d infBits = .stop infBits := by
  have hcmp : ¬ (cmpWalk P d (2 * overflowTicks) < 0) := by
    intro h
    have h1 : 2 * P < 2 * overflowTicks * d := cmpWalk_lt' h
    have h2 : 2 * overflowTicks * d ≤ 2 * P := by
      have h3 : 2 * overflowTicks * d ≤ 2 * overflowTicks * d := le_refl _
      unfold inTop at htop
      have h4 := Nat.mul_le_mul_left 2 htop
      rw [Nat.mul_assoc]
      exact h4
    omega
  unfold walkStep
  rw [ite_eq_right (by decide : ¬ (infBits = 0))]
  rw [ite_eq_left (by decide : infBits ≤ infBits)]
  rw [ite_eq_right hcmp]

/-- **Under the overflow threshold the loop halts at infinity.** -/
theorem walkLoop_top {P d : Nat} (hd : 0 < d) (htop : inTop P d) :
    ∀ b, b < infBits → ∃ n, walkLoop P d n b = some infBits := by
  have hip : 1 < infBits := by simp only [infBits]; decide
  suffices h : ∀ k, ∀ b, b < infBits → infBits - b = k →
      ∃ n, walkLoop P d n b = some infBits from fun b hb => h _ b hb rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro b hb hk
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · subst hb0
      rcases walkStep_zero_cases P d with hstep | hstep
      · obtain ⟨n, hn⟩ := ih (infBits - 1) (by omega) 1 (by omega) (by omega)
        exact ⟨n + 1, by rw [walkLoop_move hstep]; exact hn⟩
      · exfalso
        have hi0 := step_zero_stop hstep
        exact inInterval_not_top hd (by omega : 0 < infBits) hi0 htop
    · rcases step_fin_top hd htop hb0 hb with hstep | hstep
      · by_cases hlt : b + 1 < infBits
        · obtain ⟨n, hn⟩ := ih (infBits - (b + 1)) (by omega) (b + 1) hlt (by omega)
          exact ⟨n + 1, by rw [walkLoop_move hstep]; exact hn⟩
        · have hbeq : b + 1 = infBits := by omega
          refine ⟨2, ?_⟩
          rw [walkLoop_move hstep, hbeq]
          exact walkLoop_stop (step_top_stop_of_top htop)
      · exact ⟨1, walkLoop_stop hstep⟩

/-! ### What the loop computes -/

/-- The pattern the specification's magnitude is emitted at. -/
def bitsOfMag (m : Mag) : Nat :=
  match m with
  | .inf => infBits
  | .fin c => bitsOf c

/-- **The loop computes the specification's magnitude.**  From any finite
pattern, some run of the loop halts at the pattern `roundMag`'s answer is
encoded at: the infinity pattern over the threshold, and the answer's own code
below it. -/
theorem walkLoop_computes (P d : Nat) (hd : 0 < d) (b : Nat) (hb : b < infBits) :
    ∃ n, walkLoop P d n b = some (bitsOfMag (roundMag P d)) := by
  cases hrm : roundMag P d with
  | inf =>
    have htop : inTop P d := (roundMag_overflow_iff (P := P) (d := d) hd).mp hrm
    obtain ⟨n, hn⟩ := walkLoop_top hd htop b hb
    exact ⟨n, by rw [hn]; rfl⟩
  | fin c =>
    have hno : ¬ inTop P d := by
      intro ht
      have hinf := (roundMag_overflow_iff (P := P) (d := d) hd).mpr ht
      rw [hinf] at hrm
      exact Mag.noConfusion hrm
    have hmag : c.IsMag := by
      obtain ⟨c', hc', hmag'⟩ := roundMag_isCode (P := P) (d := d) hd hno
      rw [hrm] at hc'
      rw [Mag.fin.injEq] at hc'
      rw [hc']
      exact hmag'
    have hint := inInterval_roundMag hd hno hrm
    obtain ⟨n, hn⟩ := walkLoop_stops_of_interval hd (bitsOf_lt_infBits hmag) hint b hb
    exact ⟨n, by rw [hn]; rfl⟩

/-- The magnitude a halting pattern denotes: the infinity pattern is `inf`, and
any finite pattern is its code. -/
def magOfPattern (b : Nat) : Mag := if b = infBits then .inf else .fin (walkCode b)

theorem magOfPattern_bitsOfMag (P d : Nat) (hd : 0 < d) :
    magOfPattern (bitsOfMag (roundMag P d)) = roundMag P d := by
  cases hrm : roundMag P d with
  | inf =>
    show magOfPattern infBits = .inf
    unfold magOfPattern
    rw [ite_eq_left rfl]
  | fin c =>
    have hno : ¬ inTop P d := by
      intro ht
      have hinf := (roundMag_overflow_iff (P := P) (d := d) hd).mpr ht
      rw [hinf] at hrm
      exact Mag.noConfusion hrm
    have hmag : c.IsMag := by
      obtain ⟨c', hc', hmag'⟩ := roundMag_isCode (P := P) (d := d) hd hno
      rw [hrm] at hc'
      rw [Mag.fin.injEq] at hc'
      rw [hc']
      exact hmag'
    have hlt : bitsOf c < infBits := bitsOf_lt_infBits hmag
    have hne : ¬ (bitsOf c = infBits) := Nat.ne_of_lt hlt
    show magOfPattern (bitsOf c) = .fin c
    unfold magOfPattern
    rw [ite_eq_right hne, walkCode_bitsOf hmag]

/-- **The loop computes `roundMag`, read back as a magnitude.** -/
theorem walkLoop_mag (P d : Nat) (hd : 0 < d) (b : Nat) (hb : b < infBits) :
    ∃ n, walkLoop P d n b = some (bitsOfMag (roundMag P d)) ∧
      magOfPattern (bitsOfMag (roundMag P d)) = roundMag P d := by
  obtain ⟨n, hn⟩ := walkLoop_computes P d hd b hb
  exact ⟨n, hn, magOfPattern_bitsOfMag P d hd⟩

/-- **The loop computes `tier3Mag`.**  On the lexeme's ticks, the emitted walk
halts at the pattern `tier3Mag` encodes, from any finite start. -/
theorem walkLoop_computes_tier3Mag (d : Decimal) (b : Nat) (hb : b < infBits) :
    ∃ n, walkLoop d.ticks.1 d.ticks.2 n b = some (bitsOfMag (tier3Mag d)) := by
  rw [tier3Mag_eq_roundMag]
  exact walkLoop_computes d.ticks.1 d.ticks.2 d.ticks_den_pos b hb

/-! ### What this section settles, and what it does not

Settled:

* **The ladder.**  `walkTicks` is the emitted decode `(be, frac) -> Code` read
  in ticks, and `walkTicks_succ` is the step: the pattern's tick value rises by
  one ulp of its binade, `walkGap`, including the carry at the top of a binade.
  `walkTicks_lt_of_lt` makes the ladder strictly increasing, which is how the
  walk's order over patterns is the order over values.

* **The boundaries are the emitted ones.**  `bound2_up`, `bound2_down` and
  `bound2_overflow` prove that `upTwice`, `downTwice` and `2 * overflowTicks`
  are exactly the `stk_cmp` boundaries `stage2.c:773`, `:780`, `:791` and
  `:803-805` form, read at twice the tick scale.  The code's own
  `(2 * m +- 1, e - 1)`, the constant `((1 << 53) - 1, -1075)` and
  `((1 << 54) - 1, e - 2)` selections all land on the midpoint of the two
  candidate ticks they sit between.

* **The comparison.**  `valLtBoundary_iff_cmpWalk` reads the specification's
  cleared comparison at the same boundary, so `cmpWalk` is the sign of
  `V - B`, and the `stkCmp` specifications proved above say the emitted
  `stk_cmp` returns that sign.

* **The body's five verdicts.**  `step_fin_stop_self` (a stop at the candidate
  means the value is in its interval), `step_fin_stop_next` and
  `step_fin_stop_pred` (a stop at a neighbour means the value is at that
  midpoint and the candidate's significand is odd, which is where the tie is
  handed to the even significand), `step_fin_move_next` and
  `step_fin_move_pred` (a move means the value is strictly past the midpoint in
  that direction), and `step_fin_stop_of_mem` (the converse: the interval's
  candidate is where the body stops).  The two escapes are `step_zero_stop`,
  `step_zero_move`, `step_top_stop` and `step_top_move`.

* **The stopping criterion is the interval, and it selects one candidate.**
  `inInterval_uniq` proves that at most one candidate's interval contains the
  value: two intervals are either separated by a whole interval, or adjacent and
  sharing a midpoint, and then the parity of the two significands forbids both
  being even.  `inInterval_not_top` proves infinity's interval is disjoint from
  every finite one.  `stop_fin_interval`, `stop_zero_only` and `step_top_stop`
  read the stops back: every candidate the body stops at has the value in its
  interval, or the value is at or above the overflow threshold.

* **The specification's lattice is the ladder's.**  `binade_eq_of_tick_bounds`
  identifies the two: a pattern whose tick value is at or below the value, whose
  successor's is above it, and whose tick value and successor fit the binade's
  two powers of two `2 ^ (walkExp b + 51)` and `2 ^ (walkExp b + 52)` has
  exponent field `binade P d - 51`.  `walk_lattice_eq` reads the rest of the
  lattice there: `ulp P d` is the pattern's gap, and `lo` and `hi` are its tick
  value and its successor's.

* **The interval at the specification's answer.**  `inInterval_roundMag` names
  the target: `inInterval P d (bitsOf c)` for `roundMag P d = .fin c`, where
  `bitsOf` reads a code back as the pattern whose fields it is.  Below the
  subnormal edge the ladder is the tick lattice itself (`inInterval_subCode`,
  `inInterval_sub_lo`, `inInterval_sub_hi`); above it the answer is the
  lattice's floor or ceiling point, and `normal_choice_le`'s comparison of the
  answer with the two is the interval's two ends
  (`inInterval_normalCode`, `inInterval_ceiling`).  The tie clause is
  `roundMag_midpoint_even`'s even significand.

* **The descent, and what it computes.**  `walkLoop` runs the body, and the
  measure `(tgt - b) + (b - tgt)` decreases at every move: a stop is the
  interval's candidate (`stop_fin_interval` and `inInterval_uniq`), a step up
  happens only when the value is above the upper midpoint
  (`step_fin_move_next`), so the answer is above `b`, and a step down only when
  it is below the lower one (`step_fin_move_pred`).
  `walkLoop_stops_of_interval` runs the body to the candidate from any finite
  pattern, `walkLoop_top` climbs to the infinity pattern when the value is at or
  above the overflow threshold, and `walkLoop_computes` reads both as one
  statement: `roundMag`'s answer is the pattern the loop halts at.
  `walkLoop_computes_tier3Mag` reads it on the lexeme's ticks, so the magnitude
  the emitted walk returns is `tier3Mag`'s.


-/

/-! ### Axiom footprint of the walk

Every declaration here is pinned: the ladder, the boundaries and the five
verdicts are integer arithmetic, so they are expected at `[propext]` or with no
axioms. -/

#print axioms LeanLLVM.StrtodTier3.sigBits
#print axioms LeanLLVM.StrtodTier3.infBits
#print axioms LeanLLVM.StrtodTier3.maxBits
#print axioms LeanLLVM.StrtodTier3.sigBits_eq
#print axioms LeanLLVM.StrtodTier3.infBits_eq
#print axioms LeanLLVM.StrtodTier3.maxBits_eq
#print axioms LeanLLVM.StrtodTier3.infBits_pos
#print axioms LeanLLVM.StrtodTier3.maxBits_lt_infBits
#print axioms LeanLLVM.StrtodTier3.maxBits_succ
#print axioms LeanLLVM.StrtodTier3.walkExp
#print axioms LeanLLVM.StrtodTier3.walkFrac
#print axioms LeanLLVM.StrtodTier3.walkMant
#print axioms LeanLLVM.StrtodTier3.walkCode
#print axioms LeanLLVM.StrtodTier3.walkTicks
#print axioms LeanLLVM.StrtodTier3.walkGap
#print axioms LeanLLVM.StrtodTier3.div_add_one_of_mod_lt
#print axioms LeanLLVM.StrtodTier3.mod_add_one_of_mod_lt
#print axioms LeanLLVM.StrtodTier3.div_add_one_of_mod_top
#print axioms LeanLLVM.StrtodTier3.mod_add_one_of_mod_top
#print axioms LeanLLVM.StrtodTier3.mod_sub_one_of_mod_pos
#print axioms LeanLLVM.StrtodTier3.div_sub_one_of_mod_pos
#print axioms LeanLLVM.StrtodTier3.mul_div_exact
#print axioms LeanLLVM.StrtodTier3.div_sub_one_of_mod_zero
#print axioms LeanLLVM.StrtodTier3.mod_sub_one_of_mod_zero
#print axioms LeanLLVM.StrtodTier3.walkExp_lt
#print axioms LeanLLVM.StrtodTier3.walkFrac_lt
#print axioms LeanLLVM.StrtodTier3.walkGap_pos
#print axioms LeanLLVM.StrtodTier3.walkMant_eq_zero
#print axioms LeanLLVM.StrtodTier3.walkMant_eq_normal
#print axioms LeanLLVM.StrtodTier3.walkTicks_eq_zero
#print axioms LeanLLVM.StrtodTier3.walkTicks_eq_normal
#print axioms LeanLLVM.StrtodTier3.walkGap_eq_zero
#print axioms LeanLLVM.StrtodTier3.walkGap_eq_normal
#print axioms LeanLLVM.StrtodTier3.walkExp_def_of_lt
#print axioms LeanLLVM.StrtodTier3.walkExp_lt_2047
#print axioms LeanLLVM.StrtodTier3.walk_bits_decomp
#print axioms LeanLLVM.StrtodTier3.walkFrac_succ_of_frac_lt
#print axioms LeanLLVM.StrtodTier3.walkExp_succ_of_frac_lt
#print axioms LeanLLVM.StrtodTier3.walkFrac_succ_of_frac_top
#print axioms LeanLLVM.StrtodTier3.walkExp_succ_of_frac_top
#print axioms LeanLLVM.StrtodTier3.walkFrac_pred_of_frac_pos
#print axioms LeanLLVM.StrtodTier3.walkExp_pred_of_frac_pos
#print axioms LeanLLVM.StrtodTier3.walkFrac_pred_of_frac_zero
#print axioms LeanLLVM.StrtodTier3.walkExp_pred_of_frac_zero
#print axioms LeanLLVM.StrtodTier3.walkExp_pred_le_2047
#print axioms LeanLLVM.StrtodTier3.two_pow_53_eq
#print axioms LeanLLVM.StrtodTier3.two_pow_52_add_pred
#print axioms LeanLLVM.StrtodTier3.walkFrac_lt_pred
#print axioms LeanLLVM.StrtodTier3.two_pow_mul_shift
#print axioms LeanLLVM.StrtodTier3.walkTicks_succ
#print axioms LeanLLVM.StrtodTier3.walkTicks_pred
#print axioms LeanLLVM.StrtodTier3.add_sub_one_of_lt
#print axioms LeanLLVM.StrtodTier3.two_pow_52_mod_two
#print axioms LeanLLVM.StrtodTier3.two_pow_52_add_mod_two
#print axioms LeanLLVM.StrtodTier3.two_pow_52_pred_mod_two
#print axioms LeanLLVM.StrtodTier3.two_pow_53_pred_mod_two
#print axioms LeanLLVM.StrtodTier3.two_pow_54_eq
#print axioms LeanLLVM.StrtodTier3.two_pow_2098_eq
#print axioms LeanLLVM.StrtodTier3.walkMant_succ
#print axioms LeanLLVM.StrtodTier3.walkMant_pred
#print axioms LeanLLVM.StrtodTier3.walkMant_succ_even
#print axioms LeanLLVM.StrtodTier3.walkMant_succ_not_both_even
#print axioms LeanLLVM.StrtodTier3.walkMant_pred_even
#print axioms LeanLLVM.StrtodTier3.walkTicks_lt_succ
#print axioms LeanLLVM.StrtodTier3.walkTicks_le_of_le
#print axioms LeanLLVM.StrtodTier3.walkTicks_lt_of_lt
#print axioms LeanLLVM.StrtodTier3.upTwice
#print axioms LeanLLVM.StrtodTier3.downTwice
#print axioms LeanLLVM.StrtodTier3.downTwice_succ
#print axioms LeanLLVM.StrtodTier3.upTwice_lt_of_lt
#print axioms LeanLLVM.StrtodTier3.upTwice_le_of_le
#print axioms LeanLLVM.StrtodTier3.walkExp_infBits
#print axioms LeanLLVM.StrtodTier3.walkFrac_infBits
#print axioms LeanLLVM.StrtodTier3.walkTicks_infBits
#print axioms LeanLLVM.StrtodTier3.walkExp_maxBits
#print axioms LeanLLVM.StrtodTier3.walkFrac_maxBits
#print axioms LeanLLVM.StrtodTier3.walkMant_maxBits
#print axioms LeanLLVM.StrtodTier3.walkTicks_maxBits
#print axioms LeanLLVM.StrtodTier3.upTwice_maxBits
#print axioms LeanLLVM.StrtodTier3.upTwice_le_top
#print axioms LeanLLVM.StrtodTier3.walkE
#print axioms LeanLLVM.StrtodTier3.walkE_eq_zero
#print axioms LeanLLVM.StrtodTier3.walkE_eq_normal
#print axioms LeanLLVM.StrtodTier3.upJ
#print axioms LeanLLVM.StrtodTier3.upE
#print axioms LeanLLVM.StrtodTier3.downSub
#print axioms LeanLLVM.StrtodTier3.downJ
#print axioms LeanLLVM.StrtodTier3.downE
#print axioms LeanLLVM.StrtodTier3.bound2
#print axioms LeanLLVM.StrtodTier3.upE_toNat_zero
#print axioms LeanLLVM.StrtodTier3.upE_toNat_normal
#print axioms LeanLLVM.StrtodTier3.downE_toNat_sub
#print axioms LeanLLVM.StrtodTier3.downE_toNat_frac
#print axioms LeanLLVM.StrtodTier3.downE_toNat_one
#print axioms LeanLLVM.StrtodTier3.downE_toNat_two
#print axioms LeanLLVM.StrtodTier3.bound2_up
#print axioms LeanLLVM.StrtodTier3.pred_double_mul
#print axioms LeanLLVM.StrtodTier3.top_double_mul
#print axioms LeanLLVM.StrtodTier3.two_pow_shift_down
#print axioms LeanLLVM.StrtodTier3.walkTicks_two_pow_52
#print axioms LeanLLVM.StrtodTier3.bound2_down
#print axioms LeanLLVM.StrtodTier3.bound2_overflow
#print axioms LeanLLVM.StrtodTier3.cmpWalk
#print axioms LeanLLVM.StrtodTier3.cmpWalk_lt
#print axioms LeanLLVM.StrtodTier3.cmpWalk_eq
#print axioms LeanLLVM.StrtodTier3.cmpWalk_gt
#print axioms LeanLLVM.StrtodTier3.mul_two_pow_1075
#print axioms LeanLLVM.StrtodTier3.two_pow_1075_eq_mul
#print axioms LeanLLVM.StrtodTier3.two_pow_1075_split
#print axioms LeanLLVM.StrtodTier3.valLtBoundary_iff_cmpWalk
#print axioms LeanLLVM.StrtodTier3.WalkResult
#print axioms LeanLLVM.StrtodTier3.inInterval
#print axioms LeanLLVM.StrtodTier3.inTop
#print axioms LeanLLVM.StrtodTier3.walkStep
#print axioms LeanLLVM.StrtodTier3.cmpWalk_mem
#print axioms LeanLLVM.StrtodTier3.cmpWalk_lt
#print axioms LeanLLVM.StrtodTier3.cmpWalk_gt
#print axioms LeanLLVM.StrtodTier3.cmpWalk_nonpos
#print axioms LeanLLVM.StrtodTier3.cmpWalk_nonneg
#print axioms LeanLLVM.StrtodTier3.walkTicks_zero
#print axioms LeanLLVM.StrtodTier3.downTwice_zero
#print axioms LeanLLVM.StrtodTier3.walkMant_zero
#print axioms LeanLLVM.StrtodTier3.walkTicks_lt_upTwice
#print axioms LeanLLVM.StrtodTier3.walkTicks_pred_lt
#print axioms LeanLLVM.StrtodTier3.downTwice_lt_ticks
#print axioms LeanLLVM.StrtodTier3.walkStep_fin
#print axioms LeanLLVM.StrtodTier3.step_zero_stop
#print axioms LeanLLVM.StrtodTier3.step_zero_move
#print axioms LeanLLVM.StrtodTier3.step_top_stop
#print axioms LeanLLVM.StrtodTier3.step_top_move
#print axioms LeanLLVM.StrtodTier3.downTwice_mul_le
#print axioms LeanLLVM.StrtodTier3.ticks_mul_le_up
#print axioms LeanLLVM.StrtodTier3.downTwice_mul_lt
#print axioms LeanLLVM.StrtodTier3.ticks_mul_lt_up
#print axioms LeanLLVM.StrtodTier3.WalkResult.stop_ne_stop_of_ne
#print axioms LeanLLVM.StrtodTier3.WalkResult.stop_ne_move
#print axioms LeanLLVM.StrtodTier3.WalkResult.move_ne_stop
#print axioms LeanLLVM.StrtodTier3.WalkResult.move_ne_move_of_ne
#print axioms LeanLLVM.StrtodTier3.step_fin_stop_self
#print axioms LeanLLVM.StrtodTier3.step_fin_stop_next
#print axioms LeanLLVM.StrtodTier3.step_fin_stop_pred
#print axioms LeanLLVM.StrtodTier3.step_fin_move_next
#print axioms LeanLLVM.StrtodTier3.step_fin_move_pred
#print axioms LeanLLVM.StrtodTier3.step_fin_stop_of_mem
#print axioms LeanLLVM.StrtodTier3.upTwice_lt_downTwice
#print axioms LeanLLVM.StrtodTier3.downTwice_le_upTwice
#print axioms LeanLLVM.StrtodTier3.downTwice_lt_upTwice
#print axioms LeanLLVM.StrtodTier3.inInterval_uniq
#print axioms LeanLLVM.StrtodTier3.upTwice_eq_top
#print axioms LeanLLVM.StrtodTier3.inInterval_not_top
#print axioms LeanLLVM.StrtodTier3.stop_zero_only
#print axioms LeanLLVM.StrtodTier3.stop_fin_mem
#print axioms LeanLLVM.StrtodTier3.stop_fin_interval
#print axioms LeanLLVM.StrtodTier3.bitsOf
#print axioms LeanLLVM.StrtodTier3.code_ext
#print axioms LeanLLVM.StrtodTier3.bitsOf_sub
#print axioms LeanLLVM.StrtodTier3.bitsOf_normal
#print axioms LeanLLVM.StrtodTier3.walkExp_bitsOf
#print axioms LeanLLVM.StrtodTier3.walkFrac_bitsOf_normal
#print axioms LeanLLVM.StrtodTier3.walkMant_bitsOf
#print axioms LeanLLVM.StrtodTier3.walkCode_bitsOf
#print axioms LeanLLVM.StrtodTier3.walkTicks_bitsOf
#print axioms LeanLLVM.StrtodTier3.bitsOf_lt_infBits
#print axioms LeanLLVM.StrtodTier3.walkCode_isMag
#print axioms LeanLLVM.StrtodTier3.loBits
#print axioms LeanLLVM.StrtodTier3.lo_code_isMag
#print axioms LeanLLVM.StrtodTier3.walkExp_loBits
#print axioms LeanLLVM.StrtodTier3.walkMant_loBits
#print axioms LeanLLVM.StrtodTier3.loBits_lt
#print axioms LeanLLVM.StrtodTier3.walkTicks_loBits
#print axioms LeanLLVM.StrtodTier3.walkGap_loBits
#print axioms LeanLLVM.StrtodTier3.walkTicks_loBits_succ
#print axioms LeanLLVM.StrtodTier3.walkTicks_small
#print axioms LeanLLVM.StrtodTier3.walkMant_small
#print axioms LeanLLVM.StrtodTier3.downTwice_of_le
#print axioms LeanLLVM.StrtodTier3.upTwice_of_le
#print axioms LeanLLVM.StrtodTier3.downTwice_le_ticks2
#print axioms LeanLLVM.StrtodTier3.ticks2_le_upTwice
#print axioms LeanLLVM.StrtodTier3.hi_eq_lo_add
#print axioms LeanLLVM.StrtodTier3.add_51_sub_52
#print axioms LeanLLVM.StrtodTier3.binade_eq_of_tick_bounds
#print axioms LeanLLVM.StrtodTier3.walk_lattice_eq
#print axioms LeanLLVM.StrtodTier3.bitsOf_sub_code
#print axioms LeanLLVM.StrtodTier3.bitsOf_carry_code
#print axioms LeanLLVM.StrtodTier3.bitsOf_sub_succ
#print axioms LeanLLVM.StrtodTier3.bitsOf_normal_succ
#print axioms LeanLLVM.StrtodTier3.div_mod_eq
#print axioms LeanLLVM.StrtodTier3.inInterval_sub_lo
#print axioms LeanLLVM.StrtodTier3.inInterval_sub_hi
#print axioms LeanLLVM.StrtodTier3.inInterval_subCode
#print axioms LeanLLVM.StrtodTier3.normal_ticks_lo
#print axioms LeanLLVM.StrtodTier3.walkTicks_loBits_sub
#print axioms LeanLLVM.StrtodTier3.upTwice_loBits
#print axioms LeanLLVM.StrtodTier3.downTwice_loBits_succ
#print axioms LeanLLVM.StrtodTier3.loBits_ge
#print axioms LeanLLVM.StrtodTier3.loBits_pos
#print axioms LeanLLVM.StrtodTier3.ceilCode
#print axioms LeanLLVM.StrtodTier3.inInterval_ceiling
#print axioms LeanLLVM.StrtodTier3.inInterval_normalCode
#print axioms LeanLLVM.StrtodTier3.inInterval_roundMag
#print axioms LeanLLVM.StrtodTier3.walkLoop
#print axioms LeanLLVM.StrtodTier3.walkLoop_stop
#print axioms LeanLLVM.StrtodTier3.walkLoop_move
#print axioms LeanLLVM.StrtodTier3.walkStep_zero_cases
#print axioms LeanLLVM.StrtodTier3.move_fin_mem
#print axioms LeanLLVM.StrtodTier3.downTwice_le_of_le
#print axioms LeanLLVM.StrtodTier3.walkLoop_stops_of_interval
#print axioms LeanLLVM.StrtodTier3.step_fin_top
#print axioms LeanLLVM.StrtodTier3.step_top_stop_of_top
#print axioms LeanLLVM.StrtodTier3.walkLoop_top
#print axioms LeanLLVM.StrtodTier3.bitsOfMag
#print axioms LeanLLVM.StrtodTier3.walkLoop_computes
#print axioms LeanLLVM.StrtodTier3.magOfPattern
#print axioms LeanLLVM.StrtodTier3.magOfPattern_bitsOfMag
#print axioms LeanLLVM.StrtodTier3.walkLoop_mag
#print axioms LeanLLVM.StrtodTier3.walkLoop_computes_tier3Mag

/-! ### Checks

The window arithmetic on concrete magnitudes: the digit count, the drop at the
window's edge, the sticky bit, and the cleared boundary.  Below them, the
boundary comparisons on a few concrete pairs, and the scale estimate's constant,
which is sharp: `5 ^ 307` is below `2 ^ 713` and not below `2 ^ 712`. -/

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
example : valLtBoundary 3 0 5 0 := by unfold valLtBoundary; decide
example : valEqBoundary 5 0 5 0 := by unfold valEqBoundary; decide
example : valLeqBoundary 3 0 5 0 := by
  unfold valLeqBoundary; exact Or.inl (by unfold valLtBoundary; decide)

-- The scale estimate's constant is sharp: `5 ^ 307` is below `2 ^ 713` and not
-- below `2 ^ 712`, which is why `f = -307` is the last lead the arithmetic
-- settles.
#guard decide ((5 : Nat) ^ 307 < 2 ^ 713)
#guard decide (¬ ((5 : Nat) ^ 307 < 2 ^ 712))

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
#print axioms LeanLLVM.StrtodTier3.cmpCross
#print axioms LeanLLVM.StrtodTier3.cmpCross_lt
#print axioms LeanLLVM.StrtodTier3.cmpCross_eq
#print axioms LeanLLVM.StrtodTier3.cmpNat_spec
#print axioms LeanLLVM.StrtodTier3.cmpExact_spec
#print axioms LeanLLVM.StrtodTier3.toNat_of_nonneg_add
#print axioms LeanLLVM.StrtodTier3.nat_add_natAbs_of_mixed
#print axioms LeanLLVM.StrtodTier3.nat_natAbs_add_of_neg
#print axioms LeanLLVM.StrtodTier3.cmpCross_mul_ten
#print axioms LeanLLVM.StrtodTier3.valLtBoundary_mul_ten
#print axioms LeanLLVM.StrtodTier3.valEqBoundary_mul_ten
#print axioms LeanLLVM.StrtodTier3.nosticky_no_tail
#print axioms LeanLLVM.StrtodTier3.stkCmp_nosticky_spec
#print axioms LeanLLVM.StrtodTier3.stkCmp
#print axioms LeanLLVM.StrtodTier3.leadM_window_S
#print axioms LeanLLVM.StrtodTier3.sticky_drop_pos
#print axioms LeanLLVM.StrtodTier3.sticky_tail_pos
#print axioms LeanLLVM.StrtodTier3.sticky_S_neg
#print axioms LeanLLVM.StrtodTier3.sticky_E_neg
#print axioms LeanLLVM.StrtodTier3.stkCmp_sticky_spec
#print axioms LeanLLVM.StrtodTier3.valLeqBoundary
#print axioms LeanLLVM.StrtodTier3.five_pow_307_lt_713
#print axioms LeanLLVM.StrtodTier3.near_ticks_nonneg
#print axioms LeanLLVM.StrtodTier3.near_ticks_neg
#print axioms LeanLLVM.StrtodTier3.lead_toNat_nonneg
#print axioms LeanLLVM.StrtodTier3.nat_sub_lead
#print axioms LeanLLVM.StrtodTier3.two_pow_le_pow_lead
#print axioms LeanLLVM.StrtodTier3.shift_of_near
#print axioms LeanLLVM.StrtodTier3.sticky_shift
#print axioms LeanLLVM.StrtodTier3.stkCmp_sticky_spec'
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
