/-
binary64 on bit patterns: the exact IEEE 754 value model the floating-point
instruction forms read, and the round-to-nearest-even lattice hoisted out of
`LeanLLVM.JSON.Strtod` so the model layer can read its rounding without
importing the JSON reference parser.

The carrier is `BitVec 64` — LLVM's `double` — so `bitcast` is the identity,
signed zeros are distinct, and a NaN keeps its payload.  The arithmetic is
defined on the encoding's fields; every operation computes its exact value as
a pair `(P, d)` in ticks (units of `2 ^ -1074`) and rounds it once with
`roundMag`, so there is no intermediate rounding and no dependence on Lean's
native `Float`.

`IsB64Mag` … `roundMag` and their theorems are the definitions and proofs of
`LeanLLVM/JSON/Strtod.lean`, which imports this module: the lattice is stated
once, here, and the decimal specification reads it from this side.
-/
import LeanLLVM.Basic

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanLLVM

/-! ### The lattice, hoisted from `LeanLLVM.JSON.Strtod`

`IsB64Mag` is the set of tick counts a binary64 value can have, `Code` is an
encoding's exponent field and significand, and `findFrom`/`binade` locate the
binade.  `subCode`/`normalCode` choose the nearest code with the even significand
on a tie, and `roundMag` rounds an exact `P / d` in ticks to the nearest
magnitude.  The decimal specification of `LeanLLVM.JSON.Strtod` imports this
module and reads `roundMag` from here. -/

/-- A finite binary64 magnitude's tick value. -/
def IsB64Mag (M : Nat) : Prop :=
  M = 0 ∨ M < 2 ^ 52 ∨
    ∃ j m : Nat, j ≤ 2045 ∧ 2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ M = m * 2 ^ j

/-- The larger the tick value, the larger the represented value, and the
negative sign is the only thing `IsB64Mag` does not see. -/
def maxMagTicks : Nat := (2 ^ 53 - 1) * 2 ^ 2045

/-- `2 ^ 1024 - 2 ^ 970` in ticks: the overflow threshold. -/
def overflowTicks : Nat := 2 ^ 2098 - 2 ^ 2044

/-- The magnitude as the encoding's own two fields. -/
structure Code where
  /-- The biased exponent field. -/
  expField : Nat
  /-- The trailing significand field. -/
  mant : Nat
deriving DecidableEq, Repr

namespace Code

/-- The tick value of the encoding `expField`, `mant`. -/
def ticks (c : Code) : Nat :=
  if c.expField = 0 then c.mant else c.mant * 2 ^ (c.expField - 1)

/-- The two fields are a code: a subnormal `(0, m < 2 ^ 52)`, or a normal
`(1 ≤ E ≤ 2046, 2 ^ 52 ≤ m < 2 ^ 53)`.  The infinity encoding `E = 2047` is not
a magnitude and `NaN` is not a result of a decimal conversion. -/
def IsMag (c : Code) : Prop :=
  (c.expField = 0 ∧ c.mant < 2 ^ 52) ∨
    (1 ≤ c.expField ∧ c.expField ≤ 2046 ∧ 2 ^ 52 ≤ c.mant ∧ c.mant < 2 ^ 53)

theorem isB64Mag_ticks {c : Code} (h : c.IsMag) : IsB64Mag c.ticks := by
  obtain h | ⟨h1, h2, h3, h4⟩ := h
  · obtain ⟨hE, hm⟩ := h
    simp only [ticks, hE, reduceIte]
    exact Or.inr (Or.inl hm)
  · refine Or.inr (Or.inr ⟨c.expField - 1, c.mant, by omega, h3, h4, ?_⟩)
    simp only [ticks, show c.expField ≠ 0 by omega, reduceIte]

end Code

/-- A magnitude: `inf` for the overflow result, or a finite encoding. -/
inductive Mag where
  | inf
  | fin (code : Code)
deriving DecidableEq, Repr

/-- The magnitude order: an infinity is above every finite code, and finite
codes are ordered by their tick value. -/
def Mag.le : Mag → Mag → Prop
  | .inf, .inf => True
  | .inf, .fin _ => False
  | .fin _, .inf => True
  | .fin c₁, .fin c₂ => c₁.ticks ≤ c₂.ticks

/-! ### A bounded search for the first exponent

`binade` needs the least `B` with `P < d * 2 ^ (B + 1)`.  The search is
`findFrom`, with the two properties an unbounded `Nat.find` would give: the
result satisfies the predicate and no smaller index does.  It is a `Bool`
predicate on `Nat`, so both facts are inductions on the fuel. -/

/-- The first `k` at or after `start` (searching `fuel` indices) whose predicate
holds. -/
def findFrom (p : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k => if p k then some k else findFrom p fuel (k + 1)

theorem findFrom_spec (p : Nat → Bool) :
    ∀ (fuel k : Nat) {B : Nat}, findFrom p fuel k = some B →
      k ≤ B ∧ p B = true ∧ ∀ j, k ≤ j → j < B → p j = false := by
  intro fuel
  induction fuel with
  | zero =>
    intro k B h
    simp only [findFrom] at h
    exact absurd h (by simp)
  | succ fuel ih =>
    intro k B h
    simp only [findFrom] at h
    split at h
    · rename_i hp
      cases h
      exact ⟨Nat.le_refl k, hp, fun j _ hjk => absurd hjk (by omega)⟩
    · rename_i hp
      obtain ⟨h1, h2, h3⟩ := ih (k + 1) h
      exact ⟨by omega, h2, fun j hj hjb => by
        rcases Nat.eq_or_lt_of_le hj with rfl | hlt
        · simpa using hp
        · exact h3 j (by omega) hjb⟩

theorem findFrom_exists (p : Nat → Bool) :
    ∀ (fuel k j : Nat), k ≤ j → j < k + fuel → p j = true →
      ∃ B, findFrom p fuel k = some B := by
  intro fuel
  induction fuel with
  | zero =>
    intro k j hkj hlt hp
    exact absurd hlt (by omega)
  | succ fuel ih =>
    intro k j hkj hlt hp
    simp only [findFrom]
    split
    · exact ⟨k, rfl⟩
    · rename_i hk
      have hkj' : k + 1 ≤ j := by
        rcases Nat.eq_or_lt_of_le hkj with hEq | hlt'
        · subst hEq; exact absurd hp hk
        · omega
      obtain ⟨B, hB⟩ := ih (k + 1) j hkj' (by omega) hp
      exact ⟨B, hB⟩

/-- The least `B < 2100` with `P < d * 2 ^ (B + 1)`; `0` when there is none,
which the callers rule out before reading it. -/
def binade (P d : Nat) : Nat :=
  (findFrom (fun B => decide (P < d * 2 ^ (B + 1))) 2100 0).getD 0

theorem binade_spec {P d : Nat} (h : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1)) :
    P < d * 2 ^ (binade P d + 1) ∧
      ∀ j, j < binade P d → d * 2 ^ (j + 1) ≤ P := by
  obtain ⟨B, hB, hp⟩ := h
  have hp' : (fun B => decide (P < d * 2 ^ (B + 1))) B = true := by
    simpa using hp
  obtain ⟨B', hB'⟩ :=
    findFrom_exists (fun B => decide (P < d * 2 ^ (B + 1))) 2100 0 B (Nat.zero_le _)
      (by omega) hp'
  obtain ⟨-, hpred, hmin⟩ := findFrom_spec (fun B => decide (P < d * 2 ^ (B + 1))) 2100 0 hB'
  refine ⟨?_, ?_⟩
  · simpa [binade, hB'] using of_decide_eq_true hpred
  · intro j hj
    have hfalse := hmin j (Nat.zero_le _) (by simpa [binade, hB'] using hj)
    exact Nat.le_of_not_lt (by simpa using hfalse)

/-! ### The correctly rounded magnitude

`roundMag` reads the exact value `P / d` (in ticks) onto the binary64 lattice. -/

/-- The ulp of the lattice the exact value falls in: `2 ^ (binade - 52)`. -/
def ulp (P d : Nat) : Nat := 2 ^ (binade P d - 52)

/-- The first significand the binade's lattice has: the quotient's floor. -/
def sig (P d : Nat) : Nat := P / (d * ulp P d)

/-- The lattice point at or below the exact value. -/
def lo (P d : Nat) : Nat := sig P d * ulp P d

/-- The lattice point at or above the exact value. -/
def hi (P d : Nat) : Nat := (sig P d + 1) * ulp P d

/-- The subnormal region's lattice point at or below the exact value.  The ulp
there is one tick, so the pair is the quotient and its successor; the successor
of the largest subnormal significand is the smallest normal, which is the carry
`(1, 2 ^ 52)`. -/
def subCode (P d : Nat) : Code :=
  let q := P / d
  let r := P % d
  if 2 * r < d then ⟨0, q⟩
  else if d < 2 * r then (if q + 1 = 2 ^ 52 then ⟨1, 2 ^ 52⟩ else ⟨0, q + 1⟩)
  else if q % 2 = 0 then ⟨0, q⟩
  else if q + 1 = 2 ^ 52 then ⟨1, 2 ^ 52⟩ else ⟨0, q + 1⟩

/-- The normal region: the lattice is the binade's, and the significand's
successor can carry into the next exponent field. -/
def normalCode (P d : Nat) : Code :=
  let B := binade P d
  let u := ulp P d
  let q := P / (d * u)
  let r := P % (d * u)
  if 2 * r < d * u then ⟨B - 51, q⟩
  else if d * u < 2 * r then
    (if q + 1 = 2 ^ 53 then ⟨B - 50, 2 ^ 52⟩ else ⟨B - 51, q + 1⟩)
  else if q % 2 = 0 then ⟨B - 51, q⟩
  else if q + 1 = 2 ^ 53 then ⟨B - 50, 2 ^ 52⟩ else ⟨B - 51, q + 1⟩

/-- The magnitude nearest `P / d`, in ticks, as a finite encoding; or `inf` when
`P / d` is at or beyond `2 ^ 1024 - 2 ^ 970`.

The lattice points bracketing `P / d` are the ones used, so the "nearest" is
decided by two comparisons, and the subnormal region (`P < d * 2 ^ 52`) is the
`ulp = 1` branch rather than a special case at the edges.  A tie is
`2 * rem = ulp`, and then the significand is chosen even
(`deterministic` and `midpoint_even` below).  `Code.IsMag` holds of every
`fin` this returns (`roundMag_isMag`). -/
def roundMag (P d : Nat) : Mag :=
  if overflowTicks * d ≤ P then .inf
  else if P < d * 2 ^ 52 then .fin (subCode P d)
  else .fin (normalCode P d)

theorem two_pow_pos (n : Nat) : 0 < 2 ^ n := Nat.pow_pos (by decide)

/-- `2` grows strictly with its exponent, from the exponent's monotonicity
alone: the library's strict form selects a witness and so carries choice, which
this module's pins rule out. -/
theorem two_pow_lt_of_lt {a b : Nat} (h : a < b) : 2 ^ a < 2 ^ b := by
  have hle : 2 ^ 1 ≤ 2 ^ (b - a) := Nat.pow_le_pow_right (by decide) (by omega)
  have h2 : 1 < 2 ^ (b - a) := by
    have h2' := hle
    simp only [Nat.pow_one] at h2'
    exact Nat.lt_of_lt_of_le (by decide) h2'
  calc 2 ^ a = 2 ^ a * 1 := (Nat.mul_one _).symm
    _ < 2 ^ a * 2 ^ (b - a) := Nat.mul_lt_mul_of_pos_left h2 (two_pow_pos a)
    _ = 2 ^ (a + (b - a)) := (Nat.pow_add 2 a (b - a)).symm
    _ = 2 ^ b := by rw [Nat.add_sub_cancel' (Nat.le_of_lt h)]

theorem two_pow_lt_iff {a b : Nat} : 2 ^ a < 2 ^ b ↔ a < b := by
  constructor
  · intro h
    apply Nat.lt_of_not_le
    intro hba
    exact absurd (Nat.pow_le_pow_right (by decide) hba) (Nat.not_le.mpr h)
  · exact two_pow_lt_of_lt

theorem two_pow_le_iff {a b : Nat} : 2 ^ a ≤ 2 ^ b ↔ a ≤ b := by
  constructor
  · intro h
    apply Nat.le_of_not_lt
    intro hba
    exact absurd (two_pow_lt_of_lt hba) (Nat.not_lt.mpr h)
  · intro h
    exact Nat.pow_le_pow_right (by decide) h

/-- Right cancellation of a strict product, without the choice the library form
carries: it is the contrapositive of `Nat.mul_le_mul_right`. -/
theorem lt_of_mul_lt_mul_right {a b c : Nat} (h : a * c < b * c) : a < b := by
  apply Nat.lt_of_not_le
  intro hba
  exact absurd (Nat.mul_le_mul_right c hba) (Nat.not_le.mpr h)

/-- `d` times the distance between the exact value `P / d` and the lattice point
`M`: `|P - M d|`.  `d` is positive, so this orders distances as the values do. -/
def distNum (P d M : Nat) : Nat :=
  if M * d ≤ P then P - M * d else M * d - P

theorem ticks_zero (m : Nat) : (⟨0, m⟩ : Code).ticks = m := by
  simp only [Code.ticks, reduceIte]

theorem ticks_normal {E m : Nat} (hE : E ≠ 0) :
    (⟨E, m⟩ : Code).ticks = m * 2 ^ (E - 1) := by
  simp only [Code.ticks, hE, reduceIte]

/-- The successor of a subnormal significand, carrying into the smallest normal
when it reaches `2 ^ 52`, has that successor's tick value. -/
theorem sub_succ_ticks (q : Nat) :
    (if q + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else ⟨0, q + 1⟩).ticks = q + 1 := by
  split
  · rename_i h
    rw [ticks_normal (by decide : (1 : Nat) ≠ 0), h, Nat.sub_self, Nat.pow_zero,
      Nat.mul_one]
  · rw [ticks_zero]

/-- The successor of a normal significand, carrying into the next exponent field
when it reaches `2 ^ 53`, has `(q + 1) * 2 ^ (E - 1)` as its tick value. -/
theorem normal_succ_ticks {E q : Nat} (hE : E ≠ 0) (hE1 : E + 1 ≠ 0) :
    (if q + 1 = 2 ^ 53 then (⟨E + 1, 2 ^ 52⟩ : Code) else ⟨E, q + 1⟩).ticks
      = (q + 1) * 2 ^ (E - 1) := by
  split
  · rename_i h
    rw [ticks_normal hE1, h, show E + 1 - 1 = E by omega, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  · rw [ticks_normal hE]

/-- The successor of a subnormal significand is a code. -/
theorem sub_succ_isMag {q : Nat} (hq : q < 2 ^ 52) :
    (if q + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else ⟨0, q + 1⟩).IsMag := by
  split
  · exact Or.inr ⟨by decide, by decide, by decide, by decide⟩
  · exact Or.inl ⟨rfl, show q + 1 < 2 ^ 52 from by omega⟩

theorem ulp_mul_52 {P d : Nat} (hB : 52 ≤ binade P d) :
    ulp P d * 2 ^ 52 = 2 ^ binade P d := by
  simp only [ulp]
  rw [← Nat.pow_add]
  congr 1
  omega

theorem ulp_mul_53 {P d : Nat} (hB : 52 ≤ binade P d) :
    ulp P d * 2 ^ 53 = 2 ^ (binade P d + 1) := by
  simp only [ulp]
  rw [← Nat.pow_add]
  congr 1
  omega

theorem ulp_pos (P d : Nat) : 0 < ulp P d := two_pow_pos _

theorem mul_ulp_pos {d : Nat} (hd : 0 < d) (P : Nat) : 0 < d * ulp P d :=
  Nat.mul_pos hd (ulp_pos P d)

/-- The binade the exact value falls in: the exponent field is in range, the
exact value is inside that binade, and the binade is the first one above it. -/
theorem binade_facts {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    52 ≤ binade P d ∧ binade P d ≤ 2097 ∧
      d * 2 ^ binade P d ≤ P ∧ P < d * 2 ^ (binade P d + 1) := by
  have hex : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1) := by
    refine ⟨2097, by decide, ?_⟩
    have h1 : P < overflowTicks * d := Nat.lt_of_not_le hno
    have h2 : overflowTicks ≤ 2 ^ 2098 := by
      simp only [overflowTicks]; exact Nat.sub_le _ _
    have h3 : overflowTicks * d ≤ 2 ^ 2098 * d := Nat.mul_le_mul_right d h2
    have h4 : d * 2 ^ (2097 + 1) = 2 ^ 2098 * d := by
      rw [show 2097 + 1 = 2098 from by decide, Nat.mul_comm]
    rw [h4]
    exact Nat.lt_of_lt_of_le h1 h3
  obtain ⟨hup, hmin⟩ := binade_spec hex
  have hsub' : d * 2 ^ 52 ≤ P := Nat.le_of_not_lt hsub
  have h52 : 52 ≤ binade P d := by
    apply Nat.le_of_not_lt
    intro hlt
    have hlt' : binade P d + 1 ≤ 52 := Nat.succ_le_of_lt hlt
    have hle : 2 ^ (binade P d + 1) ≤ 2 ^ 52 := two_pow_le_iff.mpr hlt'
    have hle' : d * 2 ^ (binade P d + 1) ≤ d * 2 ^ 52 := Nat.mul_le_mul_left d hle
    exact absurd hup (Nat.not_lt.mpr (Nat.le_trans hle' hsub'))
  have h2097 : binade P d ≤ 2097 := by
    apply Nat.le_of_not_lt
    intro hlt
    have hlt' : 2097 < binade P d := hlt
    have hle := hmin 2097 hlt'
    have hle' : d * 2 ^ 2098 ≤ P := by
      have he : 2097 + 1 = 2098 := by decide
      rwa [he] at hle
    have h2 : overflowTicks ≤ 2 ^ 2098 := by
      simp only [overflowTicks]; exact Nat.sub_le _ _
    have h3 : overflowTicks * d ≤ 2 ^ 2098 * d := Nat.mul_le_mul_right d h2
    have h1 : P < overflowTicks * d := Nat.lt_of_not_le hno
    have h3' : 2 ^ 2098 * d ≤ P := by rw [Nat.mul_comm]; exact hle'
    exact absurd (Nat.lt_of_lt_of_le h1 h3) (Nat.not_lt.mpr h3')
  have hlo : d * 2 ^ binade P d ≤ P := by
    have hb0 : binade P d ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide : 0 < 52) h52)
    have h := hmin (binade P d - 1) (Nat.sub_one_lt hb0)
    have he : binade P d - 1 + 1 = binade P d :=
      Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 52) h52)
    rwa [he] at h
  exact ⟨h52, h2097, hlo, hup⟩

/-- The significand of the bracket is a fifty-three bit one. -/
theorem sig_bounds {P d : Nat} (hd : 0 < d) (hB : 52 ≤ binade P d)
    (hlo : d * 2 ^ binade P d ≤ P) (hup : P < d * 2 ^ (binade P d + 1)) :
    2 ^ 52 ≤ sig P d ∧ sig P d < 2 ^ 53 := by
  have hu := ulp_mul_52 (P := P) (d := d) hB
  have hu53 := ulp_mul_53 (P := P) (d := d) hB
  have hpos := mul_ulp_pos hd P
  constructor
  · simp only [sig]
    rw [Nat.le_div_iff_mul_le hpos]
    calc 2 ^ 52 * (d * ulp P d) = d * (ulp P d * 2 ^ 52) := by ac_rfl
      _ = d * 2 ^ binade P d := by rw [hu]
      _ ≤ P := hlo
  · simp only [sig]
    rw [Nat.div_lt_iff_lt_mul hpos]
    calc P < d * 2 ^ (binade P d + 1) := hup
      _ = d * (ulp P d * 2 ^ 53) := by rw [hu53]
      _ = 2 ^ 53 * (d * ulp P d) := by ac_rfl

theorem div_mul_add_mod (P k : Nat) : P / k * k + P % k = P := by
  have := Nat.div_add_mod P k
  rwa [Nat.mul_comm k (P / k)] at this

theorem lo_d_le (P d : Nat) : lo P d * d ≤ P := by
  have hP : P / (d * ulp P d) * (d * ulp P d) ≤ P := Nat.div_mul_le_self P _
  calc lo P d * d = (P / (d * ulp P d)) * (d * ulp P d) := by
        simp only [lo, sig]; ac_rfl
    _ ≤ P := hP

theorem lt_hi_d {P d : Nat} (hpos : 0 < d * ulp P d) : P < hi P d * d := by
  have h1 := div_mul_add_mod P (d * ulp P d)
  have h2 : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt _ hpos
  have h3 : hi P d * d = (P / (d * ulp P d) + 1) * (d * ulp P d) := by
    simp only [hi, sig]; ac_rfl
  rw [h3, Nat.add_mul, Nat.one_mul]
  omega

theorem lo_rem (P d : Nat) : P - lo P d * d = P % (d * ulp P d) := by
  have h1 := div_mul_add_mod P (d * ulp P d)
  have h2 : lo P d * d = (P / (d * ulp P d)) * (d * ulp P d) := by
    simp only [lo, sig]; ac_rfl
  rw [h2]
  omega

theorem hi_rem {P d : Nat} (hpos : 0 < d * ulp P d) :
    hi P d * d - P = d * ulp P d - P % (d * ulp P d) := by
  have h1 := div_mul_add_mod P (d * ulp P d)
  have h2 : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt _ hpos
  have h3 : hi P d * d = (P / (d * ulp P d) + 1) * (d * ulp P d) := by
    simp only [hi, sig]; ac_rfl
  rw [h3, Nat.add_mul, Nat.one_mul]
  omega

/-- Among the lattice points at or below the exact value, the largest is the
nearest. -/
theorem dist_min_le {P d X M : Nat} (hX : X * d ≤ P) (hM : M ≤ X) :
    distNum P d X ≤ distNum P d M := by
  have hMd : M * d ≤ P := Nat.le_trans (Nat.mul_le_mul_right d hM) hX
  have hmono : M * d ≤ X * d := Nat.mul_le_mul_right d hM
  simp only [distNum, hX, hMd, reduceIte]
  omega

/-- Among the lattice points at or above the exact value, the smallest is the
nearest. -/
theorem dist_min_ge {P d X M : Nat} (hX : P < X * d) (hM : X ≤ M) :
    distNum P d X ≤ distNum P d M := by
  have hmono : X * d ≤ M * d := Nat.mul_le_mul_right (n := X) (m := M) d hM
  have h1 : ¬ X * d ≤ P := by omega
  have h2 : ¬ M * d ≤ P := by omega
  simp only [distNum, h1, h2, reduceIte]
  omega

theorem dvd_ulp_of_mem {M t : Nat} (hM : IsB64Mag M) (hlo : 2 ^ (t + 52) ≤ M) :
    2 ^ t ∣ M := by
  obtain rfl | hsub | ⟨j, m, hj, hm1, hm2, rfl⟩ := hM
  · have hpos : 0 < 2 ^ (t + 52) := two_pow_pos _
    omega
  · have hle : 2 ^ 52 ≤ 2 ^ (t + 52) := two_pow_le_iff.mpr (by omega)
    omega
  · have hlt : 2 ^ (t + 52) < 2 ^ (j + 53) := by
      calc 2 ^ (t + 52) ≤ m * 2 ^ j := hlo
        _ < 2 ^ 53 * 2 ^ j := Nat.mul_lt_mul_of_pos_right hm2 (two_pow_pos j)
        _ = 2 ^ (j + 53) := by rw [← Nat.pow_add]; congr 1; omega
    have htj : t ≤ j := by
      have := two_pow_lt_iff.mp hlt
      omega
    refine ⟨m * 2 ^ (j - t), ?_⟩
    calc m * 2 ^ j = m * (2 ^ t * 2 ^ (j - t)) := by
          rw [← Nat.pow_add, Nat.add_comm, Nat.sub_add_cancel htj]
      _ = 2 ^ t * (m * 2 ^ (j - t)) := by ac_rfl

/-- Every finite magnitude is at or below the floor or at or above the ceiling:
the two are adjacent on the binade's lattice, and a magnitude inside them would
have to be a multiple of the ulp strictly between two consecutive multiples. -/
theorem no_gap {P d : Nat} (hd : 0 < d) (hB : 52 ≤ binade P d)
    (hlo : d * 2 ^ binade P d ≤ P) (hup : P < d * 2 ^ (binade P d + 1))
    {M : Nat} (hM : IsB64Mag M) : M ≤ lo P d ∨ hi P d ≤ M := by
  by_cases h : M ≤ lo P d
  · exact Or.inl h
  · right
    have hu := ulp_mul_52 (P := P) (d := d) hB
    have hu53 := ulp_mul_53 (P := P) (d := d) hB
    obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hlo hup
    have hMlo : lo P d < M := Nat.lt_of_not_le h
    have hle_lo : 2 ^ binade P d ≤ lo P d := by
      calc 2 ^ binade P d = 2 ^ 52 * ulp P d := by rw [← hu]; ac_rfl
        _ ≤ sig P d * ulp P d := Nat.mul_le_mul_right (ulp P d) hq1
        _ = lo P d := rfl
    have hBlt : 2 ^ binade P d < M := Nat.lt_of_le_of_lt hle_lo hMlo
    by_cases hhi : hi P d ≤ M
    · exact hhi
    · exfalso
      have hMhi : M < hi P d := Nat.lt_of_not_le hhi
      have hMlt : M < 2 ^ (binade P d + 1) := by
        refine Nat.lt_of_lt_of_le hMhi ?_
        calc hi P d = (sig P d + 1) * ulp P d := rfl
          _ ≤ 2 ^ 53 * ulp P d :=
              Nat.mul_le_mul_right (n := sig P d + 1) (m := 2 ^ 53) (ulp P d) (by omega)
          _ = 2 ^ (binade P d + 1) := by rw [← hu53]; ac_rfl
      have heq : binade P d - 52 + 52 = binade P d := by omega
      have hdvd : 2 ^ (binade P d - 52) ∣ M := by
        apply dvd_ulp_of_mem hM
        rw [heq]
        exact Nat.le_of_lt hBlt
      obtain ⟨c, hc⟩ := hdvd
      have hc1 : sig P d < c := by
        have h1 : sig P d * ulp P d < c * ulp P d := by
          calc sig P d * ulp P d = lo P d := rfl
            _ < M := hMlo
            _ = 2 ^ (binade P d - 52) * c := hc
            _ = c * ulp P d := by rw [Nat.mul_comm]; rfl
        exact lt_of_mul_lt_mul_right h1
      have hc2 : c < sig P d + 1 := by
        have h1 : ulp P d * c < (sig P d + 1) * ulp P d := by
          calc ulp P d * c = M := by rw [hc, ulp]
            _ < hi P d := hMhi
            _ = (sig P d + 1) * ulp P d := rfl
        have h1' : c * ulp P d < (sig P d + 1) * ulp P d := by
          rw [Nat.mul_comm]; exact h1
        exact lt_of_mul_lt_mul_right h1'
      omega

/-! ### The overflow threshold's arithmetic

`overflowTicks` is `2 ^ 2098 - 2 ^ 2044`, the tick value of `2 ^ 1024 - 2 ^ 970`.
The factored form `(2 ^ 54 - 1) * 2 ^ 2044` is what the carry case needs. -/

theorem overflowTicks_factor : overflowTicks = (2 ^ 54 - 1) * 2 ^ 2044 := by
  simp only [overflowTicks]
  rw [show 2 ^ 2098 = 2 ^ 54 * 2 ^ 2044 from by
    rw [← Nat.pow_add, show 54 + 2044 = 2098 from by decide]]
  rw [Nat.sub_one_mul]

theorem two_pow_2045 : 2 * 2 ^ 2044 = 2 ^ 2045 := by
  rw [show 2045 = 2044 + 1 from by decide, Nat.pow_add, Nat.pow_one, Nat.mul_comm]

theorem overflowTicks_le : overflowTicks ≤ 2 ^ 2098 := by
  rw [overflowTicks_factor,
    show (2 : Nat) ^ 2098 = 2 ^ 54 * 2 ^ 2044 from by
      rw [← Nat.pow_add, show 54 + 2044 = 2098 from by decide]]
  exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)

/-- Two ticks-pairs of the threshold equal the factored form at the next power of
two, which is the form the carry case's bound produces. -/
theorem two_overflowTicks :
    2 * overflowTicks = (2 ^ 54 - 1) * 2 ^ 2045 := by
  rw [overflowTicks_factor,
    show 2 ^ 2045 = 2 * 2 ^ 2044 from two_pow_2045.symm]
  rw [Nat.mul_left_comm]

/-- A carried normal significand is only ever the ceil of a value at or above the
overflow threshold: the carry needs `2 ^ 53` significands' worth of the binade,
and at or above the top binade that is already past the midpoint between the
largest finite value and `2 ^ 1024`. -/
theorem normal_carry_overflow {P d : Nat} (hd : 0 < d) (hB : 2097 ≤ binade P d)
    (hcons : sig P d + 1 = 2 ^ 53)
    (hge : d * ulp P d ≤ 2 * (P % (d * ulp P d))) :
    overflowTicks * d ≤ P := by
  have hB52 : 52 ≤ binade P d := by omega
  have hpos := mul_ulp_pos hd P
  have hmod : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt _ hpos
  have hdec : sig P d * (d * ulp P d) + P % (d * ulp P d) = P := by
    simpa only [sig] using div_mul_add_mod P (d * ulp P d)
  have hsig : sig P d = 2 ^ 53 - 1 := by omega
  have htwo : 2 * sig P d + 1 = 2 ^ 54 - 1 := by
    rw [hsig, Nat.mul_sub_left_distrib, Nat.mul_one]
  have h2P : (2 ^ 54 - 1) * (d * ulp P d) ≤ 2 * P := by
    have h1 : 2 * (sig P d * (d * ulp P d)) + (d * ulp P d) ≤
        2 * (sig P d * (d * ulp P d) + P % (d * ulp P d)) := by
      have h2 := Nat.mul_le_mul_left 2 hge
      omega
    calc (2 ^ 54 - 1) * (d * ulp P d)
        = (2 * sig P d + 1) * (d * ulp P d) := by rw [htwo]
      _ = 2 * (sig P d * (d * ulp P d)) + (d * ulp P d) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      _ ≤ 2 * (sig P d * (d * ulp P d) + P % (d * ulp P d)) := h1
      _ = 2 * P := by rw [hdec]
  have hu2045 : 2 ^ 2045 ≤ ulp P d := by
    show 2 ^ 2045 ≤ 2 ^ (binade P d - 52)
    exact two_pow_le_iff.mpr (by omega)
  have hstep : (2 ^ 54 - 1) * (d * 2 ^ 2045) ≤ (2 ^ 54 - 1) * (d * ulp P d) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left d hu2045)
  have hkey : 2 * overflowTicks * d = (2 ^ 54 - 1) * (d * 2 ^ 2045) := by
    rw [two_overflowTicks, Nat.mul_assoc, Nat.mul_comm (2 ^ 2045) d, ← Nat.mul_assoc]
  rw [← hkey] at hstep
  have hfin : 2 * (overflowTicks * d) ≤ 2 * P := by
    calc 2 * (overflowTicks * d) = 2 * overflowTicks * d := by rw [Nat.mul_assoc]
      _ ≤ 2 * P := Nat.le_trans hstep h2P
  exact Nat.le_of_mul_le_mul_left hfin (by decide)

/-! ### The two branches' codes -/

theorem normal_succ_ticks' {B q : Nat} (hB : 52 ≤ B) :
    (if q + 1 = 2 ^ 53 then (⟨B - 50, 2 ^ 52⟩ : Code) else ⟨B - 51, q + 1⟩).ticks
      = (q + 1) * 2 ^ (B - 52) := by
  split
  · rename_i h
    rw [ticks_normal (show B - 50 ≠ 0 by omega), h,
      show B - 50 - 1 = B - 51 by omega, ← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  · rw [ticks_normal (show B - 51 ≠ 0 by omega),
      show B - 51 - 1 = B - 52 by omega]

theorem normal_ticks {P d : Nat} (hB : 52 ≤ binade P d) :
    (normalCode P d).ticks = lo P d ∨ (normalCode P d).ticks = hi P d := by
  have hE : binade P d - 51 ≠ 0 := by omega
  have he : binade P d - 51 - 1 = binade P d - 52 := by omega
  have hs : (if P / (d * ulp P d) + 1 = 2 ^ 53 then
      (⟨binade P d - 50, 2 ^ 52⟩ : Code)
      else ⟨binade P d - 51, P / (d * ulp P d) + 1⟩).ticks
      = (P / (d * ulp P d) + 1) * 2 ^ (binade P d - 52) := by
    rw [show binade P d - 52 = binade P d - 51 - 1 by omega]
    exact normal_succ_ticks' hB
  have hlo : lo P d = P / (d * ulp P d) * 2 ^ (binade P d - 52) := rfl
  have hhi : hi P d = (P / (d * ulp P d) + 1) * 2 ^ (binade P d - 52) := rfl
  by_cases h1 : 2 * (P % (d * ulp P d)) < d * ulp P d
  · left
    simp only [normalCode, h1, reduceIte, hlo, ticks_normal hE, he]
  · by_cases h2 : d * ulp P d < 2 * (P % (d * ulp P d))
    · right
      simp only [normalCode, h1, h2, reduceIte, hhi, hs]
    · by_cases h3 : P / (d * ulp P d) % 2 = 0
      · left
        simp only [normalCode, h1, h2, h3, reduceIte, hlo, ticks_normal hE, he]
      · right
        simp only [normalCode, h1, h2, h3, reduceIte, hhi, hs]

theorem sub_ticks {P d : Nat} :
    (subCode P d).ticks = P / d ∨ (subCode P d).ticks = P / d + 1 := by
  have hs : (if P / d + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else
      ⟨0, P / d + 1⟩).ticks = P / d + 1 := sub_succ_ticks _
  by_cases h1 : 2 * (P % d) < d
  · left; simp only [subCode, h1, reduceIte, ticks_zero]
  · by_cases h2 : d < 2 * (P % d)
    · right; simp only [subCode, h1, h2, reduceIte, hs]
    · by_cases h3 : P / d % 2 = 0
      · left; simp only [subCode, h1, h2, h3, reduceIte, ticks_zero]
      · right; simp only [subCode, h1, h2, h3, reduceIte, hs]

theorem normalCode_isMag {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    (normalCode P d).IsMag := by
  obtain ⟨hB, hB', hlo, hup⟩ := binade_facts hd hno hsub
  obtain ⟨hq1, hq2⟩ := sig_bounds hd hB hlo hup
  simp only [sig] at hq1 hq2
  have hE1 : 1 ≤ binade P d - 51 := by omega
  have hE2 : binade P d - 51 ≤ 2046 := by omega
  have hcarry : ∀ (_ : d * ulp P d ≤ 2 * (P % (d * ulp P d))),
      (if P / (d * ulp P d) + 1 = 2 ^ 53 then
        (⟨binade P d - 50, 2 ^ 52⟩ : Code)
        else ⟨binade P d - 51, P / (d * ulp P d) + 1⟩).IsMag := by
    intro hge
    by_cases hq : P / (d * ulp P d) + 1 = 2 ^ 53
    · simp only [hq, reduceIte]
      by_cases hb : 2097 ≤ binade P d
      · exfalso
        exact absurd (normal_carry_overflow hd hb hq hge) hno
      · exact Or.inr ⟨show 1 ≤ binade P d - 50 from by omega,
          show binade P d - 50 ≤ 2046 from by omega, Nat.le_refl _,
          two_pow_lt_iff.mpr (by omega)⟩
    · simp only [hq, reduceIte]
      exact Or.inr ⟨hE1, hE2,
        show 2 ^ 52 ≤ P / (d * ulp P d) + 1 from by omega,
        show P / (d * ulp P d) + 1 < 2 ^ 53 from by omega⟩
  by_cases h1 : 2 * (P % (d * ulp P d)) < d * ulp P d
  · simp only [normalCode, h1, reduceIte]
    exact Or.inr ⟨hE1, hE2, hq1, hq2⟩
  · by_cases h2 : d * ulp P d < 2 * (P % (d * ulp P d))
    · simp only [normalCode, h1, h2, reduceIte]
      exact hcarry (by omega)
    · by_cases h3 : P / (d * ulp P d) % 2 = 0
      · simp only [normalCode, h1, h2, h3, reduceIte]
        exact Or.inr ⟨hE1, hE2, hq1, hq2⟩
      · simp only [normalCode, h1, h2, h3, reduceIte]
        exact hcarry (by omega)

theorem sub_sig_lt {P d : Nat} (hd : 0 < d) (hsub : P < d * 2 ^ 52) :
    P / d < 2 ^ 52 := by
  rw [Nat.div_lt_iff_lt_mul hd]
  calc P < d * 2 ^ 52 := hsub
    _ = 2 ^ 52 * d := Nat.mul_comm _ _

theorem subCode_isMag {P d : Nat} (hd : 0 < d) (hsub : P < d * 2 ^ 52) :
    (subCode P d).IsMag := by
  have hq := sub_sig_lt hd hsub
  have hcarry : (if P / d + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else
      ⟨0, P / d + 1⟩).IsMag := by
    by_cases h : P / d + 1 = 2 ^ 52
    · simp only [h, reduceIte]
      exact Or.inr ⟨show 1 ≤ 1 from by omega, show 1 ≤ 2046 from by omega,
        Nat.le_refl _, two_pow_lt_iff.mpr (by omega)⟩
    · simp only [h, reduceIte]
      exact Or.inl ⟨rfl, show P / d + 1 < 2 ^ 52 from by omega⟩
  by_cases h1 : 2 * (P % d) < d
  · simp only [subCode, h1, reduceIte]
    exact Or.inl ⟨rfl, by omega⟩
  · by_cases h2 : d < 2 * (P % d)
    · simp only [subCode, h1, h2, reduceIte]
      exact hcarry
    · by_cases h3 : P / d % 2 = 0
      · simp only [subCode, h1, h2, h3, reduceIte]
        exact Or.inl ⟨rfl, by omega⟩
      · simp only [subCode, h1, h2, h3, reduceIte]
        exact hcarry

/-! #### The chosen point is the nearer of the two -/

theorem ulp_eq (P d : Nat) : ulp P d = 2 ^ (binade P d - 52) := rfl

theorem normal_choice_le {P d : Nat} (hd : 0 < d) (hB : 52 ≤ binade P d) :
    distNum P d (normalCode P d).ticks ≤ distNum P d (lo P d) ∧
      distNum P d (normalCode P d).ticks ≤ distNum P d (hi P d) := by
  have hpos := mul_ulp_pos hd P
  have hlo := lo_d_le (P := P) (d := d)
  have hhi := lt_hi_d (P := P) (d := d) hpos
  have hlr := lo_rem (P := P) (d := d)
  have hhr := hi_rem (P := P) (d := d) hpos
  have hres : distNum P d (P / (d * ulp P d) * ulp P d) = P % (d * ulp P d) := by
    show distNum P d (lo P d) = P % (d * ulp P d)
    simp only [distNum, hlo, reduceIte]; exact hlr
  have hres' : distNum P d ((P / (d * ulp P d) + 1) * ulp P d)
      = d * ulp P d - P % (d * ulp P d) := by
    show distNum P d (hi P d) = d * ulp P d - P % (d * ulp P d)
    have h : ¬ hi P d * d ≤ P := Nat.not_le.mpr hhi
    simp only [distNum, h, reduceIte]; exact hhr
  have hlt : P % (d * ulp P d) < d * ulp P d := Nat.mod_lt _ hpos
  have h1 : binade P d - 51 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.lt_of_lt_of_le (by decide : 51 < 52) hB)
  have hsucc : (if P / (d * ulp P d) + 1 = 2 ^ 53 then
      (⟨binade P d - 50, 2 ^ 52⟩ : Code)
      else ⟨binade P d - 51, P / (d * ulp P d) + 1⟩).ticks
      = (P / (d * ulp P d) + 1) * ulp P d := by
    rw [normal_succ_ticks' hB, ← ulp_eq]
  have hlo' : (⟨binade P d - 51, P / (d * ulp P d)⟩ : Code).ticks
      = P / (d * ulp P d) * ulp P d := by
    rw [ticks_normal h1, show binade P d - 51 - 1 = binade P d - 52 from by rw [Nat.sub_sub], ← ulp_eq]
  have hhi'' : hi P d = (P / (d * ulp P d) + 1) * ulp P d := rfl
  have hlo'' : lo P d = P / (d * ulp P d) * ulp P d := rfl
  by_cases hc1 : 2 * (P % (d * ulp P d)) < d * ulp P d
  · rw [show (normalCode P d).ticks = P / (d * ulp P d) * ulp P d from by
      simp only [normalCode, hc1, reduceIte]; exact hlo']
    rw [hlo'', hhi'', hres, hres']
    constructor <;> omega
  · by_cases hc2 : d * ulp P d < 2 * (P % (d * ulp P d))
    · rw [show (normalCode P d).ticks = (P / (d * ulp P d) + 1) * ulp P d from by
        simp only [normalCode, hc1, hc2, reduceIte]; exact hsucc]
      rw [hlo'', hhi'', hres, hres']
      constructor <;> omega
    · by_cases hc3 : P / (d * ulp P d) % 2 = 0
      · rw [show (normalCode P d).ticks = P / (d * ulp P d) * ulp P d from by
          simp only [normalCode, hc1, hc2, hc3, reduceIte]; exact hlo']
        rw [hlo'', hhi'', hres, hres']
        constructor <;> omega
      · rw [show (normalCode P d).ticks = (P / (d * ulp P d) + 1) * ulp P d from by
          simp only [normalCode, hc1, hc2, hc3, reduceIte]; exact hsucc]
        rw [hlo'', hhi'', hres, hres']
        constructor <;> omega

theorem sub_choice_le {P d : Nat} (hd : 0 < d) :
    distNum P d (subCode P d).ticks ≤ distNum P d (P / d) ∧
      distNum P d (subCode P d).ticks ≤ distNum P d (P / d + 1) := by
  have hlo : P / d * d ≤ P := Nat.div_mul_le_self P d
  have hdv := div_mul_add_mod P d
  have hlt : P % d < d := Nat.mod_lt _ hd
  have hmul : (P / d + 1) * d = P / d * d + d := by rw [Nat.add_mul, Nat.one_mul]
  have hres : distNum P d (P / d) = P % d := by
    simp only [distNum, hlo, reduceIte]
    omega
  have hres' : distNum P d (P / d + 1) = d - P % d := by
    have h : ¬ (P / d + 1) * d ≤ P := by omega
    simp only [distNum, h, reduceIte]
    rw [hmul]
    omega
  have htick : (if P / d + 1 = 2 ^ 52 then (⟨1, 2 ^ 52⟩ : Code) else
      ⟨0, P / d + 1⟩).ticks = P / d + 1 := sub_succ_ticks _
  have hz : (⟨0, P / d⟩ : Code).ticks = P / d := ticks_zero _
  by_cases hc1 : 2 * (P % d) < d
  · rw [show (subCode P d).ticks = P / d from by
      simp only [subCode, hc1, reduceIte]; exact hz]
    simp only [hres, hres']
    constructor <;> omega
  · by_cases hc2 : d < 2 * (P % d)
    · rw [show (subCode P d).ticks = P / d + 1 from by
        simp only [subCode, hc1, hc2, reduceIte]; exact htick]
      simp only [hres, hres']
      constructor <;> omega
    · by_cases hc3 : P / d % 2 = 0
      · rw [show (subCode P d).ticks = P / d from by
          simp only [subCode, hc1, hc2, hc3, reduceIte]; exact hz]
        simp only [hres, hres']
        constructor <;> omega
      · rw [show (subCode P d).ticks = P / d + 1 from by
          simp only [subCode, hc1, hc2, hc3, reduceIte]; exact htick]
        simp only [hres, hres']
        constructor <;> omega

/-! #### Nearestness -/

theorem normal_nearest {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) (hsub : ¬ P < d * 2 ^ 52) :
    ∀ M, IsB64Mag M → distNum P d (normalCode P d).ticks ≤ distNum P d M := by
  intro M hM
  obtain ⟨hB, hB', hlo, hup⟩ := binade_facts hd hno hsub
  have hpos := mul_ulp_pos hd P
  obtain ⟨h1, h2⟩ := normal_choice_le hd hB
  rcases no_gap hd hB hlo hup hM with h | h
  · exact Nat.le_trans h1 (dist_min_le (lo_d_le P d) h)
  · exact Nat.le_trans h2 (dist_min_ge (lt_hi_d hpos) h)

theorem sub_no_gap {P d : Nat} {M : Nat} (hM : IsB64Mag M) :
    M ≤ P / d ∨ P / d + 1 ≤ M := by
  by_cases h : M ≤ P / d
  · exact Or.inl h
  · exact Or.inr (by omega)

theorem sub_nearest {P d : Nat} (hd : 0 < d) (hsub : P < d * 2 ^ 52) :
    ∀ M, IsB64Mag M → distNum P d (subCode P d).ticks ≤ distNum P d M := by
  intro M hM
  have hlo : P / d * d ≤ P := Nat.div_mul_le_self P d
  have hhi : P < (P / d + 1) * d := by
    have hdv := div_mul_add_mod P d
    have hlt := Nat.mod_lt P hd
    have : (P / d + 1) * d = P / d * d + d := by rw [Nat.add_mul, Nat.one_mul]
    omega
  obtain ⟨h1, h2⟩ := sub_choice_le hd
  rcases sub_no_gap (P := P) (d := d) hM with h | h
  · exact Nat.le_trans h1 (dist_min_le hlo h)
  · exact Nat.le_trans h2 (dist_min_ge hhi h)

/-! ### Nearestness for the definition's result -/

/-- **The rounding property.**  Under the overflow threshold, the code
`roundMag` returns is a code of the format and no finite binary64 magnitude is
nearer the exact value `P / d` (in ticks). -/
theorem roundMag_nearest {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) {c : Code} (hc : roundMag P d = .fin c)
    {M : Nat} (hM : IsB64Mag M) : distNum P d c.ticks ≤ distNum P d M := by
  unfold roundMag at hc
  simp only [hno, reduceIte] at hc
  split at hc
  · rename_i hsub
    simp only [Mag.fin.injEq] at hc
    subst hc
    exact sub_nearest hd hsub M hM
  · rename_i hsub
    simp only [Mag.fin.injEq] at hc
    subst hc
    exact normal_nearest hd hno hsub M hM

/-- No finite magnitude lies strictly between the exact value and the result:
the result is one of the two lattice points bracketing the exact value, and no
magnitude lies between them.  This is the direct reading of
`roundMag_nearest`: a magnitude strictly inside the bracket would be nearer than
the result. -/
theorem roundMag_no_strict_between {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) {c : Code} (hc : roundMag P d = .fin c)
    {M : Nat} (hM : IsB64Mag M) :
    ¬ (c.ticks * d < M * d ∧ M * d < P) ∧
      ¬ (P < M * d ∧ M * d < c.ticks * d) := by
  have hn := roundMag_nearest hd hno hc hM
  constructor
  · intro ⟨h1, h2⟩
    have hd1 : c.ticks * d ≤ P := by omega
    have hd2 : M * d ≤ P := by omega
    simp only [distNum, hd1, hd2, reduceIte] at hn
    omega
  · intro ⟨h1, h2⟩
    have hd1 : ¬ c.ticks * d ≤ P := by omega
    have hd2 : ¬ M * d ≤ P := by omega
    simp only [distNum, hd1, hd2, reduceIte] at hn
    omega

/-- The result is a value of the format: an infinity, or a finite encoding whose
exponent field and significand are inside the format's fields. -/
theorem roundMag_isCode {P d : Nat} (hd : 0 < d) (hno : ¬ overflowTicks * d ≤ P) :
    ∃ c : Code, roundMag P d = .fin c ∧ c.IsMag := by
  unfold roundMag
  simp only [hno, reduceIte]
  split
  · rename_i hsub
    exact ⟨subCode P d, rfl, subCode_isMag hd hsub⟩
  · rename_i hsub
    exact ⟨normalCode P d, rfl, normalCode_isMag hd hno hsub⟩

/-- Overflow, stated rather than excluded: the result is an infinity exactly at
and above `2 ^ 1024 - 2 ^ 970` in the exact value, and that is `roundTiesToEven`'s
overflow: the threshold is the midpoint between the largest finite value and
`2 ^ 1024`, and the tie goes to the even significand, which is `2 ^ 1024`'s. -/
theorem roundMag_overflow_iff {P d : Nat} (hd : 0 < d) :
    roundMag P d = .inf ↔ overflowTicks * d ≤ P := by
  by_cases h : overflowTicks * d ≤ P
  · have hin : roundMag P d = .inf := by
      unfold roundMag; rw [if_pos h]
    rw [hin]
    exact Iff.intro (fun _ => h) (fun _ => rfl)
  · have hfin : ∃ c : Code, roundMag P d = .fin c := by
      unfold roundMag
      rw [if_neg h]
      split
      · exact ⟨subCode P d, rfl⟩
      · exact ⟨normalCode P d, rfl⟩
    refine Iff.intro ?_ (fun hc => absurd hc h)
    intro hin
    obtain ⟨c, hc⟩ := hfin
    rw [hc] at hin
    exact absurd hin (by intro he; cases he)

/-- Below the threshold the finite result is at least as near the exact value as
`2 ^ 1024`: the threshold is the midpoint between the largest finite value and
`2 ^ 1024`, so below it the largest finite value is the nearer of the two, and
the result is at least as near as that. -/
theorem roundMag_overflow_nearest {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P) {c : Code} (hc : roundMag P d = .fin c) :
    distNum P d c.ticks ≤ distNum P d (2 ^ 2098) := by
  have hlt : P < overflowTicks * d := Nat.lt_of_not_le hno
  have hpow : (2 : Nat) ^ 2098 = 2 ^ 53 * 2 ^ 2045 := by
    rw [show 2098 = 53 + 2045 from by omega, Nat.pow_add]
  have hmid : maxMagTicks + 2 ^ 2098 = (2 ^ 54 - 1) * 2 ^ 2045 := by
    simp only [maxMagTicks]
    rw [hpow, ← Nat.add_mul]
  have h2P : 2 * P < maxMagTicks * d + 2 ^ 2098 * d := by
    have hm : 2 * P < 2 * (overflowTicks * d) := by omega
    calc 2 * P < 2 * (overflowTicks * d) := hm
      _ = 2 * overflowTicks * d := by rw [Nat.mul_assoc]
      _ = (2 ^ 54 - 1) * 2 ^ 2045 * d := by rw [two_overflowTicks]
      _ = (maxMagTicks + 2 ^ 2098) * d := by rw [← hmid]
      _ = maxMagTicks * d + 2 ^ 2098 * d := by rw [Nat.add_mul]
  have hM : IsB64Mag maxMagTicks := by
    refine Or.inr (Or.inr ⟨2045, 2 ^ 53 - 1, by omega, ?_, ?_,
      by simp only [maxMagTicks]⟩)
    · have h := two_pow_lt_iff (a := 52) (b := 53) |>.mpr (by omega)
      omega
    · have hp := two_pow_pos 53
      omega
  have hnearest := roundMag_nearest hd hno hc hM
  have hle_max : maxMagTicks ≤ 2 ^ 2098 := by
    simp only [maxMagTicks]
    calc (2 ^ 53 - 1) * 2 ^ 2045 ≤ 2 ^ 53 * 2 ^ 2045 :=
          Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ = 2 ^ 2098 := by rw [← Nat.pow_add]
  have hlt2 : P < 2 ^ 2098 * d := by
    have h2 : overflowTicks * d ≤ 2 ^ 2098 * d :=
      Nat.mul_le_mul_right d overflowTicks_le
    omega
  have hle : distNum P d maxMagTicks ≤ distNum P d (2 ^ 2098) := by
    have hneg : ¬ 2 ^ 2098 * d ≤ P := Nat.not_le.mpr hlt2
    have hmul : maxMagTicks * d ≤ 2 ^ 2098 * d := Nat.mul_le_mul_right d hle_max
    by_cases hP : maxMagTicks * d ≤ P
    · simp only [distNum, hP, hneg, reduceIte]
      omega
    · simp only [distNum, hP, hneg, reduceIte]
      omega
  exact Nat.le_trans hnearest hle

/-! ### The exact value's sign, and the signed zero -/

theorem roundMag_zero {d : Nat} (hd : 0 < d) : roundMag 0 d = .fin ⟨0, 0⟩ := by
  unfold roundMag
  have hpos : 0 < overflowTicks := by
    rw [overflowTicks_factor]
    refine Nat.mul_pos ?_ (two_pow_pos 2044)
    have h2 : 1 < 2 ^ 54 := by
      rw [show (1 : Nat) = 2 ^ 0 from rfl]
      exact two_pow_lt_iff.mpr (by omega)
    omega
  have h1 : ¬ overflowTicks * d ≤ 0 := by
    have := Nat.mul_pos hpos hd
    rw [Nat.mul_comm] at this ⊢
    omega
  have h2 : 0 < d * 2 ^ 52 := Nat.mul_pos hd (two_pow_pos 52)
  simp only [h1, h2, reduceIte, subCode, Nat.zero_div, Nat.zero_mod]
  simp

/-- A tie in the normal region: the result's trailing significand is even. -/
theorem normalCode_tie_even {P d : Nat}
    (hmid : 2 * (P % (d * ulp P d)) = d * ulp P d) :
    (normalCode P d).mant % 2 = 0 := by
  have h1 : ¬ (2 * (P % (d * ulp P d)) < d * ulp P d) := by omega
  have h2 : ¬ (d * ulp P d < 2 * (P % (d * ulp P d))) := by omega
  by_cases h3 : P / (d * ulp P d) % 2 = 0
  · simp only [normalCode, h1, h2, h3, reduceIte] <;> first | decide | omega | assumption
  · by_cases h4 : P / (d * ulp P d) + 1 = 2 ^ 53
    · simp only [normalCode, h1, h2, h3, h4, reduceIte] <;>
        first | decide | omega | assumption
    · simp only [normalCode, h1, h2, h3, h4, reduceIte] <;>
        first | decide | omega | assumption

/-- A tie in the subnormal region: the result's trailing significand is even. -/
theorem subCode_tie_even {P d : Nat} (hmid : 2 * (P % d) = d) :
    (subCode P d).mant % 2 = 0 := by
  have h1 : ¬ (2 * (P % d) < d) := by omega
  have h2 : ¬ (d < 2 * (P % d)) := by omega
  by_cases h3 : P / d % 2 = 0
  · simp only [subCode, h1, h2, h3, reduceIte] <;> first | decide | omega | assumption
  · by_cases h4 : P / d + 1 = 2 ^ 52
    · simp only [subCode, h1, h2, h3, h4, reduceIte] <;>
        first | decide | omega | assumption
    · simp only [subCode, h1, h2, h3, h4, reduceIte] <;>
        first | decide | omega | assumption

/-- The tie clause for the definition's result: when the exact value is the
midpoint between the two adjacent lattice points, the result's trailing
significand is even.  A midpoint is equidistant from both points, so nearestness
alone leaves the choice open; `roundTiesToEven` decides it by parity, and this is
where that clause enters. -/
theorem roundMag_midpoint_even {P d : Nat} (hd : 0 < d)
    (hno : ¬ overflowTicks * d ≤ P)
    (hmid : P - lo P d * d = hi P d * d - P)
    {c : Code} (hc : roundMag P d = .fin c) : c.mant % 2 = 0 := by
  have hLo : lo P d * d ≤ P := lo_d_le (P := P) (d := d)
  have hHi : P < hi P d * d := lt_hi_d (mul_ulp_pos hd P)
  have hhi : hi P d * d = lo P d * d + d * ulp P d := by
    simp only [hi, lo]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.mul_comm (ulp P d) d]
  have hsum : 2 * (P - lo P d * d) = d * ulp P d := by
    omega
  have hrem : P - lo P d * d = P % (d * ulp P d) := lo_rem (P := P) (d := d)
  have hmod : 2 * (P % (d * ulp P d)) = d * ulp P d := by
    rw [← hrem]
    exact hsum
  by_cases hsub : P < d * 2 ^ 52
  · have hB : binade P d ≤ 51 := by
      have hex : ∃ B, B < 2100 ∧ P < d * 2 ^ (B + 1) :=
        ⟨51, by decide, by simpa using hsub⟩
      obtain ⟨-, hmin⟩ := binade_spec hex
      have hnot : ¬ 52 ≤ binade P d := by
        intro h52
        have h51 : d * 2 ^ 52 ≤ P := by
          have h := hmin 51 (Nat.lt_of_lt_of_le (by decide : 51 < 52) h52)
          rwa [show 51 + 1 = 52 from by decide] at h
        exact absurd h51 (Nat.not_le.mpr hsub)
      clear hex hmin
      omega
    have hulp1 : ulp P d = 1 := by
      simp only [ulp]
      have : binade P d - 52 = 0 := by omega
      rw [this, Nat.pow_zero]
    have hmidsub : 2 * (P % d) = d := by
      rw [show d * ulp P d = d from by rw [hulp1, Nat.mul_one]] at hmod
      exact hmod
    unfold roundMag at hc
    simp only [hno, hsub, reduceIte] at hc
    simp only [Mag.fin.injEq] at hc
    rw [← hc]
    exact subCode_tie_even hmidsub
  · unfold roundMag at hc
    simp only [hno, hsub, reduceIte] at hc
    simp only [Mag.fin.injEq] at hc
    rw [← hc]
    exact normalCode_tie_even hmod

/-! ### The event stream's number clause

The record encoding (`stage2.h:68-75`) is a tag byte then, for `T_NUM`, the
value's eight IEEE bytes.  `strtodSpec`'s `toBits` is that value, so the number
clause of `EventStreamRel` is the statement that the record's payload is
`toBits (strtodSpec ·)` — the parameter `ParserHalf` leaves open stops being a
parameter once the emitted conversion is proved to compute this function, which
is the separate refinement slice. -/

theorem lt_iff_mul_lt_mul_right {x y k : Nat} (hk : 0 < k) : x < y ↔ x * k < y * k :=
  ⟨fun h => Nat.mul_lt_mul_of_pos_right h hk, fun h => lt_of_mul_lt_mul_right h⟩

theorem le_iff_mul_le_mul_right {x y k : Nat} (hk : 0 < k) : x ≤ y ↔ x * k ≤ y * k :=
  ⟨fun h => Nat.mul_le_mul_right k h, fun h => Nat.le_of_mul_le_mul_right h hk⟩

theorem findFrom_congr {p q : Nat → Bool} (h : ∀ k, p k = q k) :
    ∀ (n k : Nat), findFrom p n k = findFrom q n k := by
  intro n
  induction n with
  | zero => intro k; rfl
  | succ n ih =>
    intro k
    simp only [findFrom, h]
    rw [ih]

/-- `a / b = c / e` when `a * e = c * b`: both are the floor of one rational. -/
theorem div_eq_of_ratio {a b c e : Nat} (hb : 0 < b) (he : 0 < e)
    (h : a * e = c * b) : a / b = c / e := by
  have hle : a / b * b ≤ a := Nat.div_mul_le_self a b
  have hlt : a < (a / b + 1) * b := by
    have h1 := div_mul_add_mod a b
    have h2 := Nat.mod_lt a hb
    calc a = a / b * b + a % b := h1.symm
      _ < a / b * b + b := by omega
      _ = (a / b + 1) * b := by rw [Nat.add_mul, Nat.one_mul]
  have hle' : a / b * e ≤ c := by
    have hm : a / b * b * e ≤ a * e := Nat.mul_le_mul_right e hle
    rw [h] at hm
    rw [Nat.mul_assoc, Nat.mul_comm b e, ← Nat.mul_assoc] at hm
    exact Nat.le_of_mul_le_mul_right hm hb
  have hlt' : c < (a / b + 1) * e := by
    have hm : a * e < (a / b + 1) * b * e := Nat.mul_lt_mul_of_pos_right hlt he
    rw [h] at hm
    rw [Nat.mul_assoc, Nat.mul_comm b e, ← Nat.mul_assoc] at hm
    exact lt_of_mul_lt_mul_right hm
  exact (Nat.div_eq_of_lt_le hle' hlt').symm

/-- The remainders of a ratio's two scales cross-multiply: the quotient is the
same, so what is left over is too, in the two scales' own terms. -/
theorem rem_cross {a b c e q : Nat} (hr : a = q * b + a % b) (hr' : c = q * e + c % e)
    (h : a * e = c * b) : a % b * e = c % e * b := by
  have e1 : (q * b + a % b) * e = (q * e + c % e) * b := by rw [← hr, ← hr']; exact h
  rw [Nat.add_mul, Nat.add_mul] at e1
  have h1 : q * b * e = q * (b * e) := Nat.mul_assoc q b e
  have h2 : q * e * b = q * (b * e) := by rw [Nat.mul_assoc, Nat.mul_comm e b]
  rw [h1, h2] at e1
  omega

/-- The remainder comparison `2 * r < ulp` is carried across a ratio. -/
theorem rem_lt_iff_of_ratio {a b c e q : Nat} (hb : 0 < b) (he : 0 < e)
    (hr : a = q * b + a % b) (hr' : c = q * e + c % e) (h : a * e = c * b) :
    (2 * (a % b) < b) ↔ (2 * (c % e) < e) := by
  have hA : 2 * (a % b) * e = 2 * (c % e) * b := by
    rw [Nat.mul_assoc, rem_cross hr hr' h, Nat.mul_assoc]
  have step1 : (2 * (a % b) < b) ↔ (2 * (a % b) * e < b * e) :=
    lt_iff_mul_lt_mul_right he
  have step2 : (2 * (a % b) * e < b * e) ↔ (2 * (c % e) * b < e * b) := by
    rw [hA, Nat.mul_comm b e]
  have step3 : (2 * (c % e) * b < e * b) ↔ (2 * (c % e) < e) :=
    (lt_iff_mul_lt_mul_right hb).symm
  exact step1.trans (step2.trans step3)

/-- The other side of the tie comparison, carried across a ratio. -/
theorem rem_gt_iff_of_ratio {a b c e q : Nat} (hb : 0 < b) (he : 0 < e)
    (hr : a = q * b + a % b) (hr' : c = q * e + c % e) (h : a * e = c * b) :
    (b < 2 * (a % b)) ↔ (e < 2 * (c % e)) := by
  have hA : 2 * (a % b) * e = 2 * (c % e) * b := by
    rw [Nat.mul_assoc, rem_cross hr hr' h, Nat.mul_assoc]
  have step1 : (b < 2 * (a % b)) ↔ (b * e < 2 * (a % b) * e) :=
    lt_iff_mul_lt_mul_right he
  have step2 : (b * e < 2 * (a % b) * e) ↔ (e * b < 2 * (c % e) * b) := by
    rw [hA, Nat.mul_comm b e]
  have step3 : (e * b < 2 * (c % e) * b) ↔ (e < 2 * (c % e)) :=
    (lt_iff_mul_lt_mul_right hb).symm
  exact step1.trans (step2.trans step3)

/-- The subnormal branch's code depends only on the value. -/
theorem subCode_eq_of_ratio {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr : P₁ * d₂ = P₂ * d₁) : subCode P₁ d₁ = subCode P₂ d₂ := by
  have hq : P₁ / d₁ = P₂ / d₂ := div_eq_of_ratio h₁ h₂ hr
  have hd1 : P₁ = P₁ / d₁ * d₁ + P₁ % d₁ := (div_mul_add_mod P₁ d₁).symm
  have hd2 : P₂ = P₂ / d₂ * d₂ + P₂ % d₂ := (div_mul_add_mod P₂ d₂).symm
  have hd2' : P₂ = P₁ / d₁ * d₂ + P₂ % d₂ := by
    rw [← hq] at hd2
    exact hd2
  have cmp1 : (2 * (P₁ % d₁) < d₁) ↔ (2 * (P₂ % d₂) < d₂) :=
    rem_lt_iff_of_ratio h₁ h₂ hd1 hd2' hr
  have cmp2 : (d₁ < 2 * (P₁ % d₁)) ↔ (d₂ < 2 * (P₂ % d₂)) :=
    rem_gt_iff_of_ratio h₁ h₂ hd1 hd2' hr
  have par : (P₁ / d₁ % 2 = 0) ↔ (P₂ / d₂ % 2 = 0) := by rw [hq]
  unfold subCode
  by_cases c1 : 2 * (P₁ % d₁) < d₁
  · rw [if_pos c1, if_pos (cmp1.mp c1)] <;> simp only [hq]
  · rw [if_neg c1, if_neg (fun h => c1 (cmp1.mpr h))]
    by_cases c2 : d₁ < 2 * (P₁ % d₁)
    · rw [if_pos c2, if_pos (cmp2.mp c2)] <;> simp only [hq]
    · rw [if_neg c2, if_neg (fun h => c2 (cmp2.mpr h))] <;> simp only [hq]

/-- The normal branch's code depends only on the value. -/
theorem normalCode_eq_of_ratio {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr : P₁ * d₂ = P₂ * d₁) (hb : binade P₁ d₁ = binade P₂ d₂) :
    normalCode P₁ d₁ = normalCode P₂ d₂ := by
  have hbm : 0 < d₁ * ulp P₁ d₁ := mul_ulp_pos h₁ P₁
  have hbn : 0 < d₂ * ulp P₁ d₁ := by
    have h := mul_ulp_pos h₂ P₂
    rwa [show ulp P₂ d₂ = ulp P₁ d₁ from by simp only [ulp, hb]] at h
  have hq : P₁ / (d₁ * ulp P₁ d₁) = P₂ / (d₂ * ulp P₁ d₁) := by
    apply div_eq_of_ratio hbm hbn
    calc P₁ * (d₂ * ulp P₁ d₁) = P₁ * d₂ * ulp P₁ d₁ := by rw [Nat.mul_assoc]
      _ = P₂ * d₁ * ulp P₁ d₁ := by rw [hr]
      _ = P₂ * (d₁ * ulp P₁ d₁) := by rw [Nat.mul_assoc]
  have hd1 : P₁ = P₁ / (d₁ * ulp P₁ d₁) * (d₁ * ulp P₁ d₁) + P₁ % (d₁ * ulp P₁ d₁) :=
    (div_mul_add_mod P₁ _).symm
  have hd2 : P₂ = P₁ / (d₁ * ulp P₁ d₁) * (d₂ * ulp P₁ d₁) + P₂ % (d₂ * ulp P₁ d₁) := by
    have h := (div_mul_add_mod P₂ (d₂ * ulp P₂ d₂)).symm
    rw [show ulp P₂ d₂ = ulp P₁ d₁ from by simp only [ulp, hb]] at h
    rw [← hq] at h
    exact h
  have hr' : P₁ * (d₂ * ulp P₁ d₁) = P₂ * (d₁ * ulp P₁ d₁) := by
    calc P₁ * (d₂ * ulp P₁ d₁) = P₁ * d₂ * ulp P₁ d₁ := by rw [Nat.mul_assoc]
      _ = P₂ * d₁ * ulp P₁ d₁ := by rw [hr]
      _ = P₂ * (d₁ * ulp P₁ d₁) := by rw [Nat.mul_assoc]
  have cmp1 := rem_lt_iff_of_ratio hbm hbn hd1 hd2 hr'
  have cmp2 := rem_gt_iff_of_ratio hbm hbn hd1 hd2 hr'
  have hq' : P₁ / (d₁ * ulp P₁ d₁) = P₂ / (d₂ * ulp P₁ d₁) := hq
  simp only [normalCode]
  rw [show ulp P₂ d₂ = ulp P₁ d₁ from by simp only [ulp, hb], hb]
  by_cases c1 : 2 * (P₁ % (d₁ * ulp P₁ d₁)) < d₁ * ulp P₁ d₁
  · rw [if_pos c1, if_pos (cmp1.mp c1)] <;> simp only [hq']
  · rw [if_neg c1, if_neg (fun h => c1 (cmp1.mpr h))]
    by_cases c2 : d₁ * ulp P₁ d₁ < 2 * (P₁ % (d₁ * ulp P₁ d₁))
    · rw [if_pos c2, if_pos (cmp2.mp c2)] <;> simp only [hq]
    · rw [if_neg c2, if_neg (fun h => c2 (cmp2.mpr h))] <;> simp only [hq]

/-- The rounding depends only on the exact value: two tick pairs with the same
ratio round to the same code. -/
theorem roundMag_eq_of_ratio {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr : P₁ * d₂ = P₂ * d₁) : roundMag P₁ d₁ = roundMag P₂ d₂ := by
  have hpred : ∀ B, (P₁ < d₁ * 2 ^ (B + 1)) ↔ (P₂ < d₂ * 2 ^ (B + 1)) := by
    intro B
    have s1 : (P₁ < d₁ * 2 ^ (B + 1)) ↔
        (P₁ * d₂ < (d₁ * 2 ^ (B + 1)) * d₂) := lt_iff_mul_lt_mul_right h₂
    have s2 : (P₁ * d₂ < (d₁ * 2 ^ (B + 1)) * d₂) ↔
        (P₂ < d₂ * 2 ^ (B + 1)) := by
      rw [hr]
      rw [show (d₁ * 2 ^ (B + 1)) * d₂ = (d₂ * 2 ^ (B + 1)) * d₁ by ac_rfl]
      exact (lt_iff_mul_lt_mul_right h₁).symm
    exact s1.trans s2
  have hbin : binade P₁ d₁ = binade P₂ d₂ := by
    have hfc : findFrom (fun B => decide (P₁ < d₁ * 2 ^ (B + 1))) 2100 0
        = findFrom (fun B => decide (P₂ < d₂ * 2 ^ (B + 1))) 2100 0 :=
      findFrom_congr (fun k => by simp only [hpred k]) 2100 0
    simp only [binade, hfc]
  have hov : (overflowTicks * d₁ ≤ P₁) ↔ (overflowTicks * d₂ ≤ P₂) := by
    have s1 : (overflowTicks * d₁ ≤ P₁) ↔
        (overflowTicks * d₁ * d₂ ≤ P₁ * d₂) := le_iff_mul_le_mul_right h₂
    have s2 : (overflowTicks * d₁ * d₂ ≤ P₁ * d₂) ↔
        (overflowTicks * d₂ ≤ P₂) := by
      rw [hr]
      rw [show overflowTicks * d₁ * d₂ = (overflowTicks * d₂) * d₁ by ac_rfl]
      exact (le_iff_mul_le_mul_right h₁).symm
    exact s1.trans s2
  have hsub : (P₁ < d₁ * 2 ^ 52) ↔ (P₂ < d₂ * 2 ^ 52) := by
    have := hpred 51
    simpa using this
  unfold roundMag
  by_cases c0 : overflowTicks * d₁ ≤ P₁
  · rw [if_pos c0, if_pos (hov.mp c0)]
  · rw [if_neg c0, if_neg (fun h => c0 (hov.mpr h))]
    by_cases c1 : P₁ < d₁ * 2 ^ 52
    · rw [if_pos c1, if_pos (hsub.mp c1), subCode_eq_of_ratio h₁ h₂ hr]
    · rw [if_neg c1, if_neg (fun h => c1 (hsub.mpr h)),
        normalCode_eq_of_ratio h₁ h₂ hr hbin]

/-! ### Monotonicity in the exact value

The conversion is monotone: a larger exact value does not round to a smaller
magnitude.  The proof does not repeat the case analysis the definition performs.
It reads the two results against `roundMag_nearest` instead: if the smaller
value's result were the larger of the two, it would be no farther from the larger
value than that value's own result, and vice versa, which puts both values at or
past the midpoint between the two codes; the midpoint is then both values, and
`roundMag_eq_of_ratio` says one value cannot have two results. -/

/-- Overflow is monotone in the exact value: a pair that overflows at one tick
ratio overflows at every pair naming a value at least as large. -/
theorem overflow_mono {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁)
    (hr : P₁ * d₂ ≤ P₂ * d₁) (h : overflowTicks * d₁ ≤ P₁) :
    overflowTicks * d₂ ≤ P₂ := by
  have hm : overflowTicks * d₁ * d₂ ≤ P₁ * d₂ := Nat.mul_le_mul_right d₂ h
  have hm2 : overflowTicks * d₁ * d₂ ≤ P₂ * d₁ := Nat.le_trans hm hr
  have hcomm : overflowTicks * d₁ * d₂ = overflowTicks * d₂ * d₁ := by ac_rfl
  rw [hcomm] at hm2
  exact Nat.le_of_mul_le_mul_right hm2 h₁

/-- Two finite results are ordered by their magnitudes. -/
theorem roundMag_fin_le {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr : P₁ * d₂ ≤ P₂ * d₁) {c₁ c₂ : Code}
    (hc₁ : roundMag P₁ d₁ = .fin c₁) (hc₂ : roundMag P₂ d₂ = .fin c₂) :
    c₁.ticks ≤ c₂.ticks := by
  have hno₁ : ¬ overflowTicks * d₁ ≤ P₁ := by
    intro hov
    rw [(roundMag_overflow_iff h₁).mpr hov] at hc₁
    cases hc₁
  have hno₂ : ¬ overflowTicks * d₂ ≤ P₂ := by
    intro hov
    rw [(roundMag_overflow_iff h₂).mpr hov] at hc₂
    cases hc₂
  have hm₁ : IsB64Mag c₁.ticks := by
    obtain ⟨c, hc, hmag⟩ := roundMag_isCode h₁ hno₁
    rw [hc] at hc₁
    have he : c = c₁ := by simpa using hc₁
    rw [he] at hmag
    exact Code.isB64Mag_ticks hmag
  have hm₂ : IsB64Mag c₂.ticks := by
    obtain ⟨c, hc, hmag⟩ := roundMag_isCode h₂ hno₂
    rw [hc] at hc₂
    have he : c = c₂ := by simpa using hc₂
    rw [he] at hmag
    exact Code.isB64Mag_ticks hmag
  have hn₁ : distNum P₁ d₁ c₁.ticks ≤ distNum P₁ d₁ c₂.ticks :=
    roundMag_nearest h₁ hno₁ hc₁ hm₂
  have hn₂ : distNum P₂ d₂ c₂.ticks ≤ distNum P₂ d₂ c₁.ticks :=
    roundMag_nearest h₂ hno₂ hc₂ hm₁
  apply Nat.le_of_not_lt
  intro hrs
  have hlt1 : c₂.ticks * d₁ < c₁.ticks * d₁ := Nat.mul_lt_mul_of_pos_right hrs h₁
  have hlt2 : c₂.ticks * d₂ < c₁.ticks * d₂ := Nat.mul_lt_mul_of_pos_right hrs h₂
  have hleR : c₂.ticks * d₁ ≤ P₁ := by
    apply Nat.le_of_not_lt
    intro hPlt
    have hSgt : ¬ c₁.ticks * d₁ ≤ P₁ := by omega
    have hRlt : ¬ c₂.ticks * d₁ ≤ P₁ := Nat.not_le.mpr hPlt
    have h := hn₁
    simp only [distNum, hSgt, hRlt, reduceIte] at h
    omega
  have hgeR : c₂.ticks * d₂ ≤ P₂ := by
    have hm : c₂.ticks * d₁ * d₂ ≤ P₁ * d₂ := Nat.mul_le_mul_right d₂ hleR
    have hm2 : c₂.ticks * d₁ * d₂ ≤ P₂ * d₁ := Nat.le_trans hm hr
    have hcomm : c₂.ticks * d₁ * d₂ = c₂.ticks * d₂ * d₁ := by ac_rfl
    rw [hcomm] at hm2
    exact Nat.le_of_mul_le_mul_right hm2 h₁
  have hgtS₂ : ¬ c₁.ticks * d₂ ≤ P₂ := by
    intro hSle
    have hR : c₂.ticks * d₂ ≤ P₂ := by omega
    have h := hn₂
    simp only [distNum, hR, hSle, reduceIte] at h
    omega
  have hgtS : ¬ c₁.ticks * d₁ ≤ P₁ := by
    intro hSle
    have hSd₂ : c₁.ticks * d₂ ≤ P₂ := by
      have hm : c₁.ticks * d₁ * d₂ ≤ P₁ * d₂ := Nat.mul_le_mul_right d₂ hSle
      have hm2 : c₁.ticks * d₁ * d₂ ≤ P₂ * d₁ := Nat.le_trans hm hr
      have hcomm : c₁.ticks * d₁ * d₂ = c₁.ticks * d₂ * d₁ := by ac_rfl
      rw [hcomm] at hm2
      exact Nat.le_of_mul_le_mul_right hm2 h₁
    have hR : c₂.ticks * d₂ ≤ P₂ := by omega
    have h := hn₂
    simp only [distNum, hR, hSd₂, reduceIte] at h
    omega
  have h1a : c₁.ticks * d₁ + c₂.ticks * d₁ ≤ 2 * P₁ := by
    have h := hn₁
    simp only [distNum, hgtS, hleR, reduceIte] at h
    omega
  have h2a : 2 * P₂ ≤ c₁.ticks * d₂ + c₂.ticks * d₂ := by
    have h := hn₂
    simp only [distNum, hgeR, hgtS₂, reduceIte] at h
    omega
  have e1 : (c₁.ticks * d₁ + c₂.ticks * d₁) * d₂ ≤ 2 * P₁ * d₂ :=
    Nat.mul_le_mul_right d₂ h1a
  have e2 : 2 * P₁ * d₂ ≤ 2 * P₂ * d₁ := by
    have h2' := Nat.mul_le_mul_left 2 hr
    calc 2 * P₁ * d₂ = 2 * (P₁ * d₂) := by ac_rfl
      _ ≤ 2 * (P₂ * d₁) := h2'
      _ = 2 * P₂ * d₁ := by ac_rfl
  have e3 : 2 * P₂ * d₁ ≤ (c₁.ticks * d₂ + c₂.ticks * d₂) * d₁ :=
    Nat.mul_le_mul_right d₁ h2a
  have e4 : (c₁.ticks * d₁ + c₂.ticks * d₁) * d₂
      = (c₁.ticks * d₂ + c₂.ticks * d₂) * d₁ := by
    rw [Nat.add_mul, Nat.add_mul]
    ac_rfl
  have hA : (c₁.ticks * d₁ + c₂.ticks * d₁) * d₂ = 2 * P₁ * d₂ :=
    Nat.le_antisymm e1 (by rw [e4]; exact Nat.le_trans e2 e3)
  have hB : 2 * P₁ * d₂ = 2 * P₂ * d₁ := by
    refine Nat.le_antisymm e2 ?_
    rw [← e4] at e3
    rw [hA] at e3
    exact e3
  have hratio : P₁ * d₂ = P₂ * d₁ := by
    have h2' : 2 * (P₁ * d₂) = 2 * (P₂ * d₁) := by
      calc 2 * (P₁ * d₂) = 2 * P₁ * d₂ := by ac_rfl
        _ = 2 * P₂ * d₁ := hB
        _ = 2 * (P₂ * d₁) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2'
  have heq : roundMag P₁ d₁ = roundMag P₂ d₂ := roundMag_eq_of_ratio h₁ h₂ hratio
  rw [hc₁, hc₂] at heq
  have hcc : c₁ = c₂ := by simpa using heq
  have hticks : c₁.ticks = c₂.ticks := by rw [hcc]
  omega

/-- The rounding is monotone in the exact value. -/
theorem roundMag_mono {P₁ d₁ P₂ d₂ : Nat} (h₁ : 0 < d₁) (h₂ : 0 < d₂)
    (hr : P₁ * d₂ ≤ P₂ * d₁) : Mag.le (roundMag P₁ d₁) (roundMag P₂ d₂) := by
  cases hc₁ : roundMag P₁ d₁ with
  | inf =>
    cases hc₂ : roundMag P₂ d₂ with
    | inf => exact trivial
    | fin c₂ =>
      have ho₁ : overflowTicks * d₁ ≤ P₁ := (roundMag_overflow_iff h₁).mp hc₁
      have ho₂ : overflowTicks * d₂ ≤ P₂ := overflow_mono h₁ hr ho₁
      rw [(roundMag_overflow_iff h₂).mpr ho₂] at hc₂
      cases hc₂
  | fin c₁ =>
    cases hc₂ : roundMag P₂ d₂ with
    | inf => exact trivial
    | fin c₂ => exact roundMag_fin_le h₁ h₂ hr hc₁ hc₂

/-! ### The encoding

`F64` is the three fields of the pattern.  `mant` is the 52-bit trailing
significand field, so a normal's leading bit is implicit and a subnormal's is
absent — the same split `Code` uses. -/

structure F64 where
  neg : Bool
  expField : Nat
  mant : Nat
deriving DecidableEq, Repr

namespace F64

def ofBits (b : BitVec 64) : F64 :=
  let n := b.toNat
  { neg := n / 2 ^ 63 = 1, expField := (n / 2 ^ 52) % 2048, mant := n % 2 ^ 52 }

def toNat (f : F64) : Nat :=
  (if f.neg then 2 ^ 63 else 0) + f.expField * 2 ^ 52 + f.mant

def toBits (f : F64) : BitVec 64 := BitVec.ofNat 64 f.toNat

def isNaN (f : F64) : Bool := f.expField == 2047 && f.mant != 0

def isInf (f : F64) : Bool := f.expField == 2047 && f.mant == 0

def isZero (f : F64) : Bool := f.expField == 0 && f.mant == 0

/-- The magnitude in ticks: `m * 2 ^ -1074`, the smallest positive binary64. -/
def magTicks (f : F64) : Nat :=
  if f.expField = 0 then f.mant else (f.mant + 2 ^ 52) * 2 ^ (f.expField - 1)

end F64

/-- The canonical quiet NaN this model answers with, assigned to LLVM's
"unspecified" NaN result. -/
def nanBits : BitVec 64 := BitVec.ofNat 64 0x7FF8000000000000

def Mag.toNat : Mag → Nat
  | .inf => 0x7FF0000000000000
  | .fin c => c.expField * 2 ^ 52 + (if c.expField = 0 then c.mant else c.mant - 2 ^ 52)

def packMag (m : Mag) (neg : Bool) : BitVec 64 :=
  BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + m.toNat)

/-! ### The operations

Each finite case forms the exact value as `P / d` in ticks and rounds once.
The tick unit cancels: a product of magnitudes `Ma * 2 ^ -1074` and
`Mb * 2 ^ -1074` is `(Ma * Mb / 2 ^ 1074) * 2 ^ -1074`, and a quotient
`(Ma * 2 ^ 1074 / Mb) * 2 ^ -1074`; an integer `x` is `(x * 2 ^ 1074)` ticks.
-/

def fmulBits (a b : BitVec 64) : BitVec 64 :=
  let fa := F64.ofBits a
  let fb := F64.ofBits b
  let s := fa.neg != fb.neg
  if fa.isNaN || fb.isNaN then nanBits
  else if (fa.isInf && fb.isZero) || (fa.isZero && fb.isInf) then nanBits
  else if fa.isInf || fb.isInf then packMag .inf s
  else packMag (roundMag (fa.magTicks * fb.magTicks) (2 ^ 1074)) s

def fdivBits (a b : BitVec 64) : BitVec 64 :=
  let fa := F64.ofBits a
  let fb := F64.ofBits b
  let s := fa.neg != fb.neg
  if fa.isNaN || fb.isNaN then nanBits
  else if fa.isInf && fb.isInf then nanBits
  else if fa.isInf then packMag .inf s
  else if fb.isInf then packMag (.fin ⟨0, 0⟩) s
  else if fb.isZero then (if fa.isZero then nanBits else packMag .inf s)
  else packMag (roundMag (fa.magTicks * 2 ^ 1074) fb.magTicks) s

def uitofpBits (x : Nat) : BitVec 64 :=
  packMag (roundMag (x * 2 ^ 1074) 1) false

/-- Sign flip, payload and all: LLVM's `fneg` is the sign bit's inversion. -/
def fnegBits (a : BitVec 64) : BitVec 64 :=
  let f := F64.ofBits a
  (F64.mk (!f.neg) f.expField f.mant).toBits

/-- `fcmp oeq`: ordered and equal, so a NaN operand makes it false and the two
zeros are equal. -/
def fcmpOeqBits (a b : BitVec 64) : Bool :=
  let fa := F64.ofBits a
  let fb := F64.ofBits b
  !fa.isNaN && !fb.isNaN && (a == b || (fa.isZero && fb.isZero))

end LeanLLVM
