/-
The copy's count, by arithmetic.

`stk_copy` hands `(size_t)s->n * sizeof s->w[0]` to `__memcpy_chk`, whose fourth
argument is the destination's own extent — `776` for the comparator's local
`StkBn`.  The check passes at a count of at most `97`; the constant-size half of
that is `NumFastCalleeCmp.numCmpCopyLen_le`, which needs the count at most `96`
(the source object's own `uint64_t w[96]`).  That theorem takes the count's bound
as a hypothesis: the tree has no invariant on the count cell.

This module supplies the bound from arithmetic.  The two `StkBn`s `stk_cmp`
copies hold numbers that the ingest's own clamps bound, whatever the input's
length:

* `v->m` is the retained window's `M`, below `10 ^ 768`
  (`StrtodTier3.window_M_lt`); on the branch that folds a nonnegative `S` into
  the significand it is instead the whole magnitude, below `10 ^ 309`
  (`window_fold_lt`).
* `v->pow` is `5 ^ k` on the sticky branch and `10 ^ k` on the exact branch with
  `S < 0`.  There `k = -S ≤ 1091`: the clamps admit `-324 ≤ f ≤ 308`, the window
  retains at most `768` digits, and `-S = (ndig M - 1) - f` (`window_pow_k_le`).
* The multiply's own step keeps its carry below `2 ^ 64`
  (`stkMulFold_carry_lt`), so a limb step adds at most one limb and the value
  bound survives (`stkMulWords_value`, `stkMulWords_length_le`,
  `stkMulWords_canon`).

All four numbers are far below `2 ^ (64 * 96)`: `10 ^ 768 < 2 ^ 2560`,
`10 ^ 309 < 2 ^ 1030`, `5 ^ 1091 < 2 ^ 2546`, `10 ^ 1091 < 2 ^ 3637`.  A
canonical little-endian limb list whose value is below `2 ^ (64 * N)` has at
most `N` limbs (`length_le_of_limbVal_lt`), so a count that is such a list's
length is at most `96`, and the copy's byte count is at most `776`
(`numCmpCopyLen_le_of_value`).  `window_M_size_le`, `pow_five_size_le` and
`pow_ten_size_le` read the same bounds as `Nat.size`.

**The pins, and what each bound depends on.**

| bound | theorem | hypotheses it needs |
|---|---|---|
| `v->m` (window) | `window_M_lt_two_pow` | `0 < m`; `R ≤ stkDigits = 768`, built into `windowOf`'s `stkDrop` |
| `v->m` (folded) | `window_fold_lt` | `0 < M`, `0 ≤ S`, `lead ≤ 308` (the `f >= 309` clamp did not fire) |
| `pow = 5 ^ k` | `pow_five_lt` | `k ≤ 1091`, from `R ≤ 768` and `lead ≥ -324` (`window_pow_k_le`) |
| `pow = 10 ^ k` | `pow_ten_lt` | the same `k ≤ 1091` |
| the step's carry | `stkMulFold_carry_lt` | limbs, multiplier and incoming carry below `2 ^ 64` |
| the count | `length_le_of_limbVal_lt` | canonical limb list, value below `2 ^ (64 * N)` |
| the nest's step | `stkMulWords_count_le` | canonical input, `0 < m < 2 ^ 64`, product below `2 ^ (64 * N)` |
| the check | `numCmpCopyLen_le_of_value` | the above, and `count = ws.length` |

**What stays open.**  The ingest's digit and power loops
(`for.body132.i.i` … `if.end151.i.i.sink.split`; `JsonStage2NumFastToDouble`
records that their bodies are not stated) have no `Nat`-level model, so
`value(limbs of v->m) = M` and `value(limbs of v->pow) = 5 ^ k` are not
derivable here: they are the memory tie's, not this module's.  Likewise the
count cell is an unconstrained four-byte read in `NumFastCalls.stkCount`, and its
equality with the limb list's length is the tie's.  What this module fixes is
the arithmetic those ties consume.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalleeCmp

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.StrtodTier3
open LeanLLVM.Refinement.NumFastCalleeCmp

namespace NumFastStkArith

/-! ### The number a limb list holds

Little-endian, `64`-bit limbs, as `StkBn`'s `uint64_t w[96]` and the reader's
`stkLimbs` lay them out: `w[0]` is the least significant.  `limbVal` is the
number they denote, and the two facts a count needs are that a `k`-limb list is
below `2 ^ (64 * k)` and that a canonical one reaches `2 ^ (64 * (k - 1))`. -/

/-- The number a little-endian limb list holds. -/
def limbVal : List Nat → Nat
  | [] => 0
  | w :: ws => w + 2 ^ 64 * limbVal ws

/-- A limb list is canonical when it is empty or its value reaches the top
limb's place.  With limbs below `2 ^ 64` this is exactly its last limb being
nonzero — the representation `stk_mul_add` maintains by extending while a carry
remains. -/
def LimbCanon (ws : List Nat) : Prop :=
  ws = [] ∨ 2 ^ (64 * (ws.length - 1)) ≤ limbVal ws

theorem limbVal_cons (w : Nat) (ws : List Nat) :
    limbVal (w :: ws) = w + 2 ^ 64 * limbVal ws := rfl

/-- Concatenating limb lists shifts the second by the first's width. -/
theorem limbVal_append (as bs : List Nat) :
    limbVal (as ++ bs) = limbVal as + 2 ^ (64 * as.length) * limbVal bs := by
  induction as with
  | nil => simp [limbVal]
  | cons a as ih =>
      rw [List.cons_append, limbVal_cons, ih, limbVal_cons, List.length_cons]
      have hexp : 64 * (as.length + 1) = 64 * as.length + 64 := by omega
      rw [hexp, Nat.pow_add, Nat.mul_add]
      ac_rfl

/-- **A `k`-limb list is below `2 ^ (64 * k)`.** -/
theorem limbVal_succ_le (ws : List Nat) (hw : ∀ w ∈ ws, w < 2 ^ 64) :
    limbVal ws + 1 ≤ 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => simp [limbVal]
  | cons a as ih =>
      have ha : a < 2 ^ 64 := hw a (by simp)
      have has : ∀ w ∈ as, w < 2 ^ 64 := fun w hw' => hw w (by simp [hw'])
      have hih : limbVal as + 1 ≤ 2 ^ (64 * as.length) := ih has
      rw [limbVal_cons, List.length_cons]
      have hstep : a + 2 ^ 64 * limbVal as + 1 ≤ 2 ^ 64 * (limbVal as + 1) := by
        have h1 : a + 1 ≤ 2 ^ 64 := Nat.succ_le_of_lt ha
        calc a + 2 ^ 64 * limbVal as + 1 ≤ 2 ^ 64 + 2 ^ 64 * limbVal as := by omega
          _ = 2 ^ 64 * (limbVal as + 1) := by
              rw [Nat.mul_add, Nat.mul_one]
              omega
      calc a + 2 ^ 64 * limbVal as + 1 ≤ 2 ^ 64 * (limbVal as + 1) := hstep
        _ ≤ 2 ^ 64 * 2 ^ (64 * as.length) := Nat.mul_le_mul_left _ hih
        _ = 2 ^ (64 * (as.length + 1)) := by
            rw [← Nat.pow_add,
              show 64 + 64 * as.length = 64 * (as.length + 1) from by omega]

theorem limbVal_lt (ws : List Nat) (hw : ∀ w ∈ ws, w < 2 ^ 64) :
    limbVal ws < 2 ^ (64 * ws.length) := by
  have := limbVal_succ_le ws hw
  omega

/-- **A canonical list reaches the top limb's place.**  This is the direction a
count needs: without it the value's upper bound says nothing about the list's
length, since padding with zero limbs leaves the value alone. -/
theorem LimbCanon.limbVal_ge {ws : List Nat} (h : LimbCanon ws) (hne : ws ≠ []) :
    2 ^ (64 * (ws.length - 1)) ≤ limbVal ws := by
  rcases h with hnil | h
  · exact absurd hnil hne
  · exact h

/-- **The count from the value.**  A canonical list of `64`-bit limbs whose value
is below `2 ^ (64 * N)` has at most `N` limbs.  This is the step that turns the
arithmetic bounds below into the count the copy's check reads. -/
theorem length_le_of_limbVal_lt {ws : List Nat} {N : Nat}
    (hcanon : LimbCanon ws) (hne : ws ≠ []) (hval : limbVal ws < 2 ^ (64 * N)) :
    ws.length ≤ N := by
  have hlow := LimbCanon.limbVal_ge hcanon hne
  have hlt : 2 ^ (64 * (ws.length - 1)) < 2 ^ (64 * N) := lt_of_le_of_lt hlow hval
  have hexp : 64 * (ws.length - 1) < 64 * N :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt
  omega

/-! ### The decimal bounds

The four magnitudes the ingest's clamps bound.  Each is a closed comparison of
numerals, so `decide` settles it, as the tree already does for
`StrtodTier3.five_pow_307_lt` and `pow_two_1024_le_ten_309`. -/

theorem ten_pow_768_lt : (10 : Nat) ^ 768 < 2 ^ 2560 := by decide

theorem ten_pow_309_lt : (10 : Nat) ^ 309 < 2 ^ 1030 := by decide

theorem five_pow_1091_lt : (5 : Nat) ^ 1091 < 2 ^ 2546 := by decide

theorem ten_pow_1091_lt : (10 : Nat) ^ 1091 < 2 ^ 3637 := by decide

/-! ### The window's retained digits

`(windowOf m E).M` is the retained leading digits, below `10 ^ 768` by
`window_M_lt`.  On the branch where the ingest folds a nonnegative `S` into the
significand the stored number is `M * 10 ^ S` instead, and that is the magnitude
itself: with the sticky bit clear the dropped tail is zero, so `M * 10 ^ S` has
leading digit `lead ≤ 308` and is below `10 ^ 309`. -/

/-- The window's retained digits are positive at a positive magnitude. -/
theorem windowOf_M_pos {m : Nat} (hm : 0 < m) (E : Int) : 0 < (windowOf m E).M := by
  rw [windowOf_M, Nat.div_pos_iff]
  refine ⟨Nat.pow_pos (by decide), ?_⟩
  have hsle : stkDrop m ≤ ndig m - 1 := by
    rw [show stkDrop m = ndig m - stkDigits from rfl, stkDigits_eq]
    omega
  calc 10 ^ stkDrop m ≤ 10 ^ (ndig m - 1) := Nat.pow_le_pow_right (by decide) hsle
    _ ≤ m := (ndig_spec hm).1

/-- **The window's retained digits are below `2 ^ (64 * 96)`.** -/
theorem window_M_lt_two_pow {m : Nat} (hm : 0 < m) (E : Int) :
    (windowOf m E).M < 2 ^ (64 * 96) := by
  have h := window_M_lt (m := m) hm
  rw [stkDigits_eq] at h
  rw [windowOf_M]
  calc m / 10 ^ stkDrop m < 10 ^ 768 := h
    _ < 2 ^ 2560 := ten_pow_768_lt
    _ ≤ 2 ^ (64 * 96) := Nat.pow_le_pow_right (by decide) (by omega)

/-- **The same in bit length.**  `Nat.size` of the retained digits is at most
`6144`. -/
theorem window_M_size_le {m : Nat} (hm : 0 < m) (E : Int) :
    (windowOf m E).M.size ≤ 64 * 96 :=
  Nat.size_le.mpr (window_M_lt_two_pow hm E)

/-- **The fold's significand is below `2 ^ (64 * 96)`.**  With `S ≥ 0` the ingest
multiplies the retained digits by `10 ^ S`; the result's leading decimal
exponent is `(ndig M - 1) + S = lead`, and `lead ≤ 308` (the `f >= 309` branch
returns infinity) puts it below `10 ^ 309`. -/
theorem window_fold_lt {M : Nat} {S : Int} (hM : 0 < M) (hS : 0 ≤ S)
    (hlead : ((ndig M : Nat) : Int) - 1 + S ≤ 308) :
    M * 10 ^ S.toNat < 2 ^ (64 * 96) := by
  have hSnat : (S.toNat : Int) = S := Int.toNat_of_nonneg hS
  have hexp : ndig M + S.toNat ≤ 309 := by
    have hcast : ((ndig M + S.toNat : Nat) : Int) ≤ 309 := by
      rw [Nat.cast_add, hSnat]
      omega
    omega
  have hlt : M < 10 ^ ndig M := (ndig_spec hM).2
  calc M * 10 ^ S.toNat < 10 ^ ndig M * 10 ^ S.toNat :=
        Nat.mul_lt_mul_of_pos_right hlt (Nat.pow_pos (by decide))
    _ = 10 ^ (ndig M + S.toNat) := (Nat.pow_add 10 _ _).symm
    _ ≤ 10 ^ 309 := Nat.pow_le_pow_right (by decide) hexp
    _ < 2 ^ 1030 := ten_pow_309_lt
    _ ≤ 2 ^ (64 * 96) := Nat.pow_le_pow_right (by decide) (by omega)

/-! ### The power's exponent

`v->pow` holds `5 ^ k` on the sticky branch and `10 ^ k` on the exact branch with
`S < 0`, where `k = -S`.  The window's own fields bound it. -/

/-- The retained digits have at most `768` decimal digits. -/
theorem ndig_le_of_lt_ten_pow {M : Nat} (hM : 0 < M) (hlt : M < 10 ^ 768) :
    ndig M ≤ 768 := by
  have h1 : 10 ^ (ndig M - 1) ≤ M := (ndig_spec hM).1
  have h2 : 10 ^ (ndig M - 1) < 10 ^ 768 := lt_of_le_of_lt h1 hlt
  have h3 : ndig M - 1 < 768 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 10)).mp h2
  omega

/-- **The power's exponent is at most `1091`.**  On the branch that builds a
power, `S < 0` and `-S = (ndig M - 1) - lead`; the lower clamp `lead ≥ -324`
(the `f <= -325` branch returns zero) and `ndig M ≤ 768` give
`-S ≤ 767 + 324`. -/
theorem window_pow_k_le {m : Nat} (hm : 0 < m) (E : Int)
    (hS : (windowOf m E).S < 0) (hlead : -324 ≤ (windowOf m E).lead) :
    (-(windowOf m E).S).toNat ≤ 1091 := by
  have hMpos : 0 < (windowOf m E).M := windowOf_M_pos hm E
  have hMlt : (windowOf m E).M < 10 ^ 768 := by
    have h := window_M_lt (m := m) hm
    rw [stkDigits_eq] at h
    rwa [windowOf_M]
  have hndig : ((ndig (windowOf m E).M : Nat) : Int) ≤ 768 := by
    have h := ndig_le_of_lt_ten_pow hMpos hMlt
    omega
  have hleadEq : (windowOf m E).lead
      = ((ndig (windowOf m E).M : Nat) : Int) - 1 + (windowOf m E).S := rfl
  have hSexpr : -((windowOf m E).S)
      = (((ndig (windowOf m E).M : Nat) : Int) - 1) - (windowOf m E).lead := by
    rw [hleadEq]
    omega
  have hbound : -((windowOf m E).S) ≤ 1091 := by
    rw [hSexpr]
    omega
  have hnonneg : (0 : Int) ≤ -((windowOf m E).S) := by omega
  have hcast : (((-((windowOf m E).S)).toNat : Nat) : Int) ≤ 1091 := by
    rw [Int.toNat_of_nonneg hnonneg]
    exact hbound
  omega

/-- **`5 ^ k` is below `2 ^ (64 * 96)` at the power's exponent.** -/
theorem pow_five_lt {k : Nat} (hk : k ≤ 1091) : (5 : Nat) ^ k < 2 ^ (64 * 96) := by
  calc (5 : Nat) ^ k ≤ 5 ^ 1091 := Nat.pow_le_pow_right (by decide) hk
    _ < 2 ^ 2546 := five_pow_1091_lt
    _ ≤ 2 ^ (64 * 96) := Nat.pow_le_pow_right (by decide) (by omega)

/-- **`10 ^ k` is below `2 ^ (64 * 96)` at the power's exponent.** -/
theorem pow_ten_lt {k : Nat} (hk : k ≤ 1091) : (10 : Nat) ^ k < 2 ^ (64 * 96) := by
  calc (10 : Nat) ^ k ≤ 10 ^ 1091 := Nat.pow_le_pow_right (by decide) hk
    _ < 2 ^ 3637 := ten_pow_1091_lt
    _ ≤ 2 ^ (64 * 96) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The same in bit length. -/
theorem pow_five_size_le {k : Nat} (hk : k ≤ 1091) : ((5 : Nat) ^ k).size ≤ 64 * 96 :=
  Nat.size_le.mpr (pow_five_lt hk)

/-- The same in bit length. -/
theorem pow_ten_size_le {k : Nat} (hk : k ≤ 1091) : ((10 : Nat) ^ k).size ≤ 64 * 96 :=
  Nat.size_le.mpr (pow_ten_lt hk)

/-! ### The pins at the emitted counters

`JsonStage2NumFastTier3.copy_S_window` and `copy_lead_window` identify the
emitted scale `exp10 - F + (T - lead - R)` and leading exponent
`(R - 1) + S` with `(windowOf m (exp10 - F)).S` and `.lead`, at the tree's own
`R = min nsig stkDigits`.  The two bounds above therefore apply to the numbers
the ingest stores, with the clamps as the only hypotheses beyond the counters'
own equations. -/

/-- **The power's exponent at the emitted counters.**  `k <= 1091` from the
tree's `hR`, the `f <= -325` clamp (did not fire) and `S < 0`. -/
theorem copy_pow_k_le {m nsig R T lead F : Nat} {exp10 : Int}
    (hm : 0 < m) (hnd : ndig m = nsig) (hnsig : nsig = T - lead)
    (hR : R = min nsig stkDigits)
    (hS : (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int)) < 0)
    (hlead : -324 ≤ ((R : Int) - 1
      + (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int)))) :
    (-(exp10 - (F : Int) + (((T - lead) - R : Nat) : Int))).toNat ≤ 1091 := by
  have hS' : (windowOf m (exp10 - (F : Int))).S < 0 := by
    rwa [← NumFastTier3.copy_S_window hnd hnsig hR]
  have hlead' : -324 ≤ (windowOf m (exp10 - (F : Int))).lead := by
    rwa [← NumFastTier3.copy_lead_window hm hnd hnsig hR]
  rw [NumFastTier3.copy_S_window hnd hnsig hR]
  exact window_pow_k_le hm (exp10 - (F : Int)) hS' hlead'

/-- **The fold's significand at the emitted counters.**  With the `f >= 309`
clamp not fired and `S >= 0`, the folded significand is below `2 ^ (64 * 96)`. -/
theorem copy_fold_lt {m nsig R T lead F : Nat} {exp10 : Int}
    (hm : 0 < m) (hnd : ndig m = nsig) (hnsig : nsig = T - lead)
    (hR : R = min nsig stkDigits)
    (hS : 0 ≤ (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int)))
    (hlead : ((R : Int) - 1
      + (exp10 - (F : Int) + (((T - lead) - R : Nat) : Int))) ≤ 308) :
    (windowOf m (exp10 - (F : Int))).M
        * 10 ^ ((windowOf m (exp10 - (F : Int))).S).toNat < 2 ^ (64 * 96) := by
  have hS' : 0 ≤ (windowOf m (exp10 - (F : Int))).S := by
    rwa [← NumFastTier3.copy_S_window hnd hnsig hR]
  have hlead' : ((ndig (windowOf m (exp10 - (F : Int))).M : Nat) : Int) - 1
      + (windowOf m (exp10 - (F : Int))).S ≤ 308 := by
    rw [NumFastTier3.copy_lead_window hm hnd hnsig hR] at hlead
    exact hlead
  exact window_fold_lt (windowOf_M_pos hm (exp10 - (F : Int))) hS' hlead'

/-! ### The multiply's limb step

`stk_mul_add(a, m, 0)` is `stkMulWords`, and each limb step is `t = w * m + c`,
the low `64` bits kept and `t / 2 ^ 64` carried.  The carry's bound is what makes
the step arithmetic rather than a growth: with 64-bit limbs the carry out is
again a 64-bit word, so the final carry is one limb at most. -/

/-- A 64-bit limb times a 64-bit multiplier plus a 64-bit carry is below
`2 ^ 128`, so the carry out is a 64-bit word. -/
theorem stkMulStep_lt {w m c : Nat} (hw : w < 2 ^ 64) (hm : m < 2 ^ 64)
    (hc : c < 2 ^ 64) : w * m + c < 2 ^ 128 := by
  have hw' : w ≤ 2 ^ 64 - 1 := by omega
  have hm' : m ≤ 2 ^ 64 - 1 := by omega
  have hc' : c ≤ 2 ^ 64 - 1 := by omega
  have hnum : ((2 : Nat) ^ 64 - 1) * ((2 : Nat) ^ 64 - 1) + ((2 : Nat) ^ 64 - 1) < 2 ^ 128 := by
    decide
  calc w * m + c ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) + (2 ^ 64 - 1) :=
        Nat.add_le_add (Nat.mul_le_mul hw' hm') hc'
    _ < 2 ^ 128 := hnum

theorem two_pow_64_sq : (2 : Nat) ^ 64 * 2 ^ 64 = 2 ^ 128 := by decide

/-- The fold's kept limbs, unfolded one limb.  Definitional. -/
theorem stkMulFold_succ_fst (w : Nat) (ws : List Nat) (m c : Nat) :
    (stkMulFold (w :: ws) m c).1
      = ((w * m + c) % 2 ^ 64) :: (stkMulFold ws m ((w * m + c) / 2 ^ 64)).1 := rfl

/-- The fold's carry, unfolded one limb.  Definitional. -/
theorem stkMulFold_succ_snd (w : Nat) (ws : List Nat) (m c : Nat) :
    (stkMulFold (w :: ws) m c).2
      = (stkMulFold ws m ((w * m + c) / 2 ^ 64)).2 := rfl

/-- **The fold's carry is below `2 ^ 64`** — hence below `2 ^ (64 * 96)`, the
bound the count needs.  Induction over the limbs: each step's carry feeds the
next as a 64-bit word by `stkMulStep_lt`. -/
theorem stkMulFold_carry_lt {ws : List Nat} {m c : Nat}
    (hws : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64) :
    (stkMulFold ws m c).2 < 2 ^ 64 := by
  induction ws generalizing c with
  | nil => simpa [stkMulFold] using hc
  | cons w ws ih =>
      rw [stkMulFold_succ_snd]
      have hw : w < 2 ^ 64 := hws w (by simp)
      have hws' : ∀ u ∈ ws, u < 2 ^ 64 := fun u hu => hws u (by simp [hu])
      have hstep : w * m + c < 2 ^ 128 := stkMulStep_lt hw hm hc
      have hcarry : (w * m + c) / 2 ^ 64 < 2 ^ 64 := by
        rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 2 ^ 64), two_pow_64_sq]
        exact hstep
      exact ih hws' hcarry

/-- The carry's own bound against the limb count's width. -/
theorem stkMulFold_carry_lt_96 {ws : List Nat} {m c : Nat}
    (hws : ∀ w ∈ ws, w < 2 ^ 64) (hm : m < 2 ^ 64) (hc : c < 2 ^ 64) :
    (stkMulFold ws m c).2 < 2 ^ (64 * 96) :=
  lt_of_lt_of_le (stkMulFold_carry_lt hws hm hc)
    (Nat.pow_le_pow_right (by decide) (by omega))

/-- The fold's kept limbs are as many as its input's. -/
theorem stkMulFold_fst_length (ws : List Nat) (m c : Nat) :
    (stkMulFold ws m c).1.length = ws.length := by
  induction ws generalizing c with
  | nil => rfl
  | cons w ws ih =>
      rw [stkMulFold_succ_fst, List.length_cons]
      have := ih ((w * m + c) / 2 ^ 64)
      simp only [List.length_cons, this]

/-- The fold's kept limbs are 64-bit words. -/
theorem stkMulFold_fst_lt (ws : List Nat) (m c : Nat) :
    ∀ u ∈ (stkMulFold ws m c).1, u < 2 ^ 64 := by
  induction ws generalizing c with
  | nil => simp [stkMulFold]
  | cons w ws ih =>
      intro u hu
      rw [stkMulFold_succ_fst] at hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · exact Nat.mod_lt _ (Nat.pow_pos (by decide))
      · exact ih ((w * m + c) / 2 ^ 64) u hu'

/-- **The fold's value.**  The kept limbs plus the final carry at the input's
width are exactly the input's value times the multiplier plus the incoming
carry. -/
theorem stkMulFold_value (ws : List Nat) (m c : Nat) :
    limbVal (stkMulFold ws m c).1 + 2 ^ (64 * ws.length) * (stkMulFold ws m c).2
      = limbVal ws * m + c := by
  induction ws generalizing c with
  | nil => simp [stkMulFold, limbVal]
  | cons w ws ih =>
      rw [stkMulFold_succ_fst, stkMulFold_succ_snd, limbVal_cons, List.length_cons]
      have hexp : 2 ^ (64 * (ws.length + 1)) = 2 ^ 64 * 2 ^ (64 * ws.length) := by
        rw [show 64 * (ws.length + 1) = 64 + 64 * ws.length from by omega, Nat.pow_add]
      rw [hexp]
      calc (w * m + c) % 2 ^ 64
            + 2 ^ 64 * limbVal (stkMulFold ws m ((w * m + c) / 2 ^ 64)).1
            + (2 ^ 64 * 2 ^ (64 * ws.length))
              * (stkMulFold ws m ((w * m + c) / 2 ^ 64)).2
          = ((w * m + c) % 2 ^ 64)
              + 2 ^ 64 * (limbVal (stkMulFold ws m ((w * m + c) / 2 ^ 64)).1
                + 2 ^ (64 * ws.length)
                  * (stkMulFold ws m ((w * m + c) / 2 ^ 64)).2) := by
              rw [Nat.mul_add]
              ac_rfl
        _ = ((w * m + c) % 2 ^ 64)
              + 2 ^ 64 * (limbVal ws * m + (w * m + c) / 2 ^ 64) := by
              rw [ih ((w * m + c) / 2 ^ 64)]
        _ = ((w * m + c) % 2 ^ 64 + 2 ^ 64 * ((w * m + c) / 2 ^ 64))
              + 2 ^ 64 * (limbVal ws * m) := by
              rw [Nat.mul_add]
              ac_rfl
        _ = (w * m + c) + 2 ^ 64 * (limbVal ws * m) := by rw [Nat.mod_add_div]
        _ = (w + 2 ^ 64 * limbVal ws) * m + c := by
              rw [Nat.add_mul]
              ac_rfl

/-! ### The multiply's answer

`stkMulWords ws m` appends the final carry's limbs above the kept ones.  With the
carry below `2 ^ 64` that is at most one limb, the value is exactly `limbVal ws *
m`, and a canonical input gives a canonical output. -/

theorem stkCarryLimbs_zero : stkCarryLimbs 0 = [] := stkCarryLimbs.eq_1

theorem stkCarryLimbs_succ (c : Nat) :
    stkCarryLimbs (c + 1)
      = (c + 1) % 2 ^ 64 :: stkCarryLimbs ((c + 1) / 2 ^ 64) := by
  simpa using stkCarryLimbs.eq_2 c

/-- The carry's limbs are 64-bit words. -/
theorem stkCarryLimbs_lt {c : Nat} (hc : c < 2 ^ 64) :
    ∀ w ∈ stkCarryLimbs c, w < 2 ^ 64 := by
  rcases Nat.eq_zero_or_pos c with hzero | hpos
  · rw [hzero, stkCarryLimbs_zero]
    simp
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    intro w hw
    rw [stkCarryLimbs_succ] at hw
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact Nat.mod_lt _ (Nat.pow_pos (by decide))
    · have hdiv : (c' + 1) / 2 ^ 64 = 0 := Nat.div_eq_of_lt hc
      rw [hdiv, stkCarryLimbs_zero] at hw'
      simp at hw'

/-- The carry's limbs denote the carry. -/
theorem stkCarryLimbs_value {c : Nat} (hc : c < 2 ^ 64) :
    limbVal (stkCarryLimbs c) = c := by
  rcases Nat.eq_zero_or_pos c with hzero | hpos
  · rw [hzero, stkCarryLimbs_zero]
    rfl
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hdiv : (c' + 1) / 2 ^ 64 = 0 := Nat.div_eq_of_lt hc
    have hmod : (c' + 1) % 2 ^ 64 = c' + 1 := Nat.mod_eq_of_lt hc
    rw [stkCarryLimbs_succ, hmod, hdiv, stkCarryLimbs_zero]
    simp [limbVal]

/-- A 64-bit carry is one limb. -/
theorem stkCarryLimbs_length_le {c : Nat} (hc : c < 2 ^ 64) :
    (stkCarryLimbs c).length ≤ 1 := by
  rcases Nat.eq_zero_or_pos c with hzero | hpos
  · rw [hzero, stkCarryLimbs_zero]
    simp
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hdiv : (c' + 1) / 2 ^ 64 = 0 := Nat.div_eq_of_lt hc
    rw [stkCarryLimbs_succ, hdiv, stkCarryLimbs_zero]
    simp

/-- The multiply's limbs, as the fold and the carry. -/
theorem stkMulWords_eq (ws : List Nat) (m : Nat) :
    stkMulWords ws m
      = (stkMulFold ws m 0).1 ++ stkCarryLimbs (stkMulFold ws m 0).2 := rfl

/-- **The multiply's value.**  A 64-bit carry makes the answer's limbs denote
exactly `limbVal ws * m`. -/
theorem stkMulWords_value {ws : List Nat} {m : Nat}
    (hc : (stkMulFold ws m 0).2 < 2 ^ 64) :
    limbVal (stkMulWords ws m) = limbVal ws * m := by
  rw [stkMulWords_eq, limbVal_append, stkCarryLimbs_value hc,
    stkMulFold_fst_length, stkMulFold_value]
  omega

/-- **The multiply adds at most one limb.** -/
theorem stkMulWords_length_le {ws : List Nat} {m : Nat}
    (hc : (stkMulFold ws m 0).2 < 2 ^ 64) :
    (stkMulWords ws m).length ≤ ws.length + 1 := by
  rw [stkMulWords_eq, List.length_append, stkMulFold_fst_length]
  have := stkCarryLimbs_length_le hc
  omega

/-- The multiply's limbs are 64-bit words. -/
theorem stkMulWords_lt {ws : List Nat} {m : Nat}
    (hc : (stkMulFold ws m 0).2 < 2 ^ 64) :
    ∀ w ∈ stkMulWords ws m, w < 2 ^ 64 := by
  intro w hw
  rw [stkMulWords_eq] at hw
  rcases List.mem_append.mp hw with h | h
  · exact stkMulFold_fst_lt ws m 0 w h
  · exact stkCarryLimbs_lt hc w h

/-- **The multiply keeps a canonical list canonical.**  The step's arithmetic is
what makes the ingest's repeated `stk_mul_u64` keep the copy's count bounded: a
canonical list times a nonzero 64-bit word is canonical again, whether the final
carry is zero (the length is kept and the value is at least the input's) or not
(the carry is a new top limb). -/
theorem stkMulWords_canon {ws : List Nat} {m : Nat}
    (hcanon : LimbCanon ws) (hm : 0 < m) (hc : (stkMulFold ws m 0).2 < 2 ^ 64) :
    LimbCanon (stkMulWords ws m) := by
  rcases hcanon with hnil | hlow
  · refine Or.inl ?_
    rw [hnil, stkMulWords_eq]
    simp [stkMulFold, stkCarryLimbs]
  · have hlen : (stkMulFold ws m 0).1.length = ws.length :=
      stkMulFold_fst_length ws m 0
    have hval : limbVal (stkMulFold ws m 0).1
        + 2 ^ (64 * ws.length) * (stkMulFold ws m 0).2 = limbVal ws * m := by
      have h := stkMulFold_value ws m 0
      simpa only [Nat.add_zero] using h
    have happend : limbVal (stkMulWords ws m)
        = limbVal (stkMulFold ws m 0).1
          + 2 ^ (64 * ws.length) * (stkMulFold ws m 0).2 := by
      rw [stkMulWords_eq, limbVal_append, stkCarryLimbs_value hc, hlen]
    rcases Nat.eq_zero_or_pos ((stkMulFold ws m 0).2) with hzero | hpos
    · have hres : stkMulWords ws m = (stkMulFold ws m 0).1 := by
        rw [stkMulWords_eq, hzero, stkCarryLimbs_zero, List.append_nil]
      have hv : limbVal (stkMulFold ws m 0).1 = limbVal ws * m := by
        have h := hval
        rw [hzero, Nat.mul_zero, Nat.add_zero] at h
        exact h
      refine Or.inr ?_
      rw [hres, hlen, hv]
      exact le_trans hlow (Nat.le_mul_of_pos_right _ hm)
    · have hone : (stkCarryLimbs ((stkMulFold ws m 0).2)).length = 1 := by
        obtain ⟨c', hc'⟩ : ∃ c', (stkMulFold ws m 0).2 = c' + 1 :=
          ⟨(stkMulFold ws m 0).2 - 1, by omega⟩
        rw [hc', stkCarryLimbs_succ,
          Nat.div_eq_of_lt (by rw [← hc']; exact hc), stkCarryLimbs_zero]
        simp
      have hreslen : (stkMulWords ws m).length = ws.length + 1 := by
        rw [stkMulWords_eq, List.length_append, hlen, hone]
      refine Or.inr ?_
      rw [hreslen, show ws.length + 1 - 1 = ws.length from by omega, happend]
      have hmul : 2 ^ (64 * ws.length)
          ≤ 2 ^ (64 * ws.length) * (stkMulFold ws m 0).2 :=
        Nat.le_mul_of_pos_right _ hpos
      exact le_trans hmul (Nat.le_add_left _ _)

/-- **The power nest's count.**  One `stk_mul_u64` step from a canonical list by
a 64-bit row keeps the count at most `N` whenever the *product's* value is below
`2 ^ (64 * N)`.  That is the step the `v->pow` loops apply — `5 ^ k` by `5 ^ 27`
and `5 ^ k` remainders, `10 ^ k` by `10 ^ 19` — so at `k ≤ 1091`
(`pow_five_lt`/`pow_ten_lt`) every intermediate count stays at most `96`. -/
theorem stkMulWords_count_le {ws : List Nat} {m N : Nat}
    (hcanon : LimbCanon ws) (hne : ws ≠ []) (hm : 0 < m) (hmw : m < 2 ^ 64)
    (hws : ∀ w ∈ ws, w < 2 ^ 64)
    (hval : limbVal ws * m < 2 ^ (64 * N)) :
    (stkMulWords ws m).length ≤ N := by
  have hc : (stkMulFold ws m 0).2 < 2 ^ 64 :=
    stkMulFold_carry_lt hws hmw (by decide : 0 < 2 ^ 64)
  have hcanon' : LimbCanon (stkMulWords ws m) := stkMulWords_canon hcanon hm hc
  have hlen : (stkMulWords ws m).length
      = ws.length + (stkCarryLimbs (stkMulFold ws m 0).2).length := by
    rw [stkMulWords_eq, List.length_append, stkMulFold_fst_length]
  have hne' : stkMulWords ws m ≠ [] := by
    intro h
    have h0 : (stkMulWords ws m).length = 0 := by rw [h]; rfl
    rw [hlen] at h0
    exact hne (List.eq_nil_of_length_eq_zero (by omega))
  have hv : limbVal (stkMulWords ws m) = limbVal ws * m := stkMulWords_value hc
  exact length_le_of_limbVal_lt hcanon' hne' (by rwa [hv])

/-! ### The copy's count, and the check

`numCmpCopyLen` is the byte count the comparator's copy takes at the count cell's
word.  Its constant-size bound needs the count at most `96`; the value bound
gives it, and the count cell's equality with the limb list's length is the one
tie left. -/

/-- **The copy's byte count, from the source's limb list.**  A canonical list
holding a number below `2 ^ (64 * N)` gives a count of at most `N`, so the
fortified copy's length is at most `776`. -/
theorem numCmpCopyLen_le_of_limbs {ws : List Nat} {nw : BitVec 32} {N : Nat}
    (hcanon : LimbCanon ws) (hne : ws ≠ []) (hval : limbVal ws < 2 ^ (64 * N))
    (hN : N ≤ 96) (hcount : nw.toNat = ws.length) :
    numCmpCopyLen nw ≤ 776 := by
  have hlen : ws.length ≤ N := length_le_of_limbVal_lt hcanon hne hval
  exact numCmpCopyLen_le (by omega)

/-- **The copy's byte count at the limb count's own width.**  The value bound is
the one this module's windows and powers supply (`window_M_lt_two_pow`,
`window_fold_lt`, `pow_five_lt`, `pow_ten_lt`); `count = ws.length` is the tie. -/
theorem numCmpCopyLen_le_of_value {ws : List Nat} {nw : BitVec 32} {v : Nat}
    (hcanon : LimbCanon ws) (hne : ws ≠ []) (hvalue : limbVal ws = v)
    (hval : v < 2 ^ (64 * 96)) (hcount : nw.toNat = ws.length) :
    numCmpCopyLen nw ≤ 776 := by
  refine numCmpCopyLen_le_of_limbs hcanon hne ?_ le_rfl hcount
  rwa [hvalue]

/-- **The bytes the copy moves are at most `776`.**  The same count, at its own
byte width: `8 * n ≤ 776`. -/
theorem copy_bytes_le {ws : List Nat} {N : Nat}
    (hcanon : LimbCanon ws) (hne : ws ≠ []) (hval : limbVal ws < 2 ^ (64 * N))
    (hN : N ≤ 96) :
    8 * ws.length ≤ 776 := by
  have hlen : ws.length ≤ N := length_le_of_limbVal_lt hcanon hne hval
  omega

end NumFastStkArith

end LeanLLVM.Refinement
