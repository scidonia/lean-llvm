/-
`strtodSpec`: what a JSON number lexeme denotes as an IEEE 754 binary64 value.

The emitted stage-2 event records a number as eight bytes of a double
(`stage2.h:68-75`, `stage2.c:598`), while the model keeps the source lexeme in
`Value.number` (`Tape.lean:130-133`).  Nothing in this tree relates the two, so
`EventStreamRel` (`JsonPipelineSpec.lean:209`) takes the record stream's meaning
as a parameter and the number arm of that relation is the one clause no record
in the tree states.  This module states it: the double a number record carries
is `strtodSpec` of the lexeme.

**A specification, not an implementation.**  `strtodSpec` names the value RFC
8259 §6's number denotes under IEEE 754's `roundTiesToEven`; it says nothing
about C, `strtod`, `num_fast`, `p6.c` or any emitted instruction.  Its input is
the lexeme's own decomposition — the sign, `IntPart`, the optional `frac`'s
digits and the optional `exp` (`NumBody`'s four shapes, `Spec.lean:285-292`) —
so a caller supplies the parts the grammar already produced rather than parsing
the bytes a second time.  Its output is the binary64 encoding: the sign, the
biased exponent field and the trailing significand field, i.e. the eight bytes
the record writes.

**What is stated and proved here.**

1. `Decimal.lexeme` and `Decimal.rfcNumber`: the decomposition denotes an
   `RfcNumber` lexeme, so the input is the grammar's own decomposition of the
   token's span and not a second reading of it.
2. `Decimal.ticks`: the lexeme's exact value as a rational `P / d`, measured in
   units of `2 ^ -1074` — the smallest positive binary64.  Every finite
   binary64 value is an integer number of those units, so one integer lattice
   holds the subnormals, the normals, and the largest finite value at once, and
   every comparison below is integer arithmetic (`IsB64Mag`).
3. `roundMag`: the correctly rounded magnitude.  It is stated as the value at
   the exact value's own position on that lattice — the two lattice points
   bracketing `P / d`, with the closer one chosen and the even significand
   chosen on a tie — with the subnormal region and the overflow threshold
   `2 ^ 1024 - 2 ^ 970` each a branch rather than an excluded case, and the
   largest finite value the top of the normal range rather than a special case.
4. `roundMag_nearest`: no binary64 value is nearer the exact value than the
   result, with `roundMag_no_strict_between` the corollary that no binary64
   value lies strictly between the exact value and the result, and
   `roundMag_midpoint_even` the tie clause: at the exact midpoint of the two
   adjacent values the result's trailing significand is even.
5. `roundMag_overflow_iff` and `roundMag_overflow_nearest`: overflow is
   `overflowTicks * d ≤ P` and the result is then `(±)infinity`; below the
   threshold the finite result is at least as near as `2 ^ 1024`.
6. `roundMag_eq_of_ratio`: the result depends only on the exact value and not on
   the `(P, d)` pair a lexeme happens to spell it with, and
   `strtodSpec_mono`: the result's magnitude is monotone in the lexeme's exact
   value.
7. `strtodSpec`, `strtodSpec_isCode`, `strtodSpec_zero` (a zero lexeme's result
   keeps the lexeme's sign, so `-0` is `-0.0`), and the bridge
   `EventStreamNumberArm` / `strtodSpec_isNumberArm`: the number record's eight
   payload bytes are `strtodSpec`'s encoding.

**What is not here.**  The refinement — that `num_fast`'s tier 1 (a `double`
multiply or divide by an exact `10 ^ eff`), its tier 2 (`num_el`'s 128-bit
multiply against `epow_table.h`'s normalised `10 ^ eff` with its
"undecidable → `strtod`" fallback) and its tier 3 (`num_scan` copying into a
64-byte buffer and calling `strtod`) computes this function — is a separate
slice, and the last paragraph of this file names what it needs.  This module
proves no run of any emitted code computes anything.  The corpus check
(`tests/json-strtod/`) is evidence about the specification's agreement with
glibc's `strtod`, not a proof about the emitted body.

There is no `sorry`, `admit` or `native_decide` below, and the declarations'
axioms are pinned at the end of the file.
-/
import LeanLLVM.JSON.Spec

set_option autoImplicit false
set_option maxRecDepth 10000

namespace LeanLLVM.JSON

open ByteString

/-! ### The lexeme's decomposition

`Decimal` is `NumBody`'s decomposition as data: `Spec.lean:285-292` gives the
four shapes `int`, `int "." frac`, `int exp` and `int "." frac exp` under an
optional `minus`.  The parts are the ones the grammar's productions name
(`IntPart`, `Digits`, `ExpPart`), and `wellFormed` is the condition that makes
`lexeme` a number. -/

/-- RFC 8259 §6's `number` without the bytes: the optional `minus`, the `int`
part, the optional `frac`'s digits, and the optional `exp`'s sign and digits. -/
structure Decimal where
  /-- `true` for a leading `minus`. -/
  neg : Bool
  /-- `int`'s bytes, an `IntPart`. -/
  ip : Bytes
  /-- `frac`'s digits, or `none` when the lexeme has no `.`. -/
  fr : Option Bytes
  /-- `exp`'s sign (`true` for `-`) and digits, or `none` when absent. -/
  ex : Option (Bool × Bytes)
deriving DecidableEq, Repr

namespace Decimal

/-- The sign's bytes: `-` or nothing. -/
def signBytes (s : Bool) : Bytes := if s then 0x2D +: empty else empty

/-- The lexeme without its sign, in `NumBody`'s four shapes. -/
def body (d : Decimal) : Bytes :=
  match d.fr, d.ex with
  | none, none => d.ip
  | some fs, none => d.ip ++ (0x2E +: fs)
  | none, some (s, ds) => d.ip ++ (0x65 +: (signBytes s ++ ds))
  | some fs, some (s, ds) => (d.ip ++ (0x2E +: fs)) ++ (0x65 +: (signBytes s ++ ds))

/-- The lexeme the decomposition denotes. -/
def lexeme (d : Decimal) : Bytes := signBytes d.neg ++ d.body

/-- The decomposition is the grammar's: an `IntPart`, `Digits` after the `.` if
there is one, and `Digits` after the `e` if there is one. -/
def wellFormed (d : Decimal) : Prop :=
  IntPart d.ip ∧
    (∀ fs, d.fr = some fs → Digits fs) ∧
    (∀ s ds, d.ex = some (s, ds) → Digits ds)

theorem signBytes_false : signBytes false = empty := rfl

theorem signBytes_true : signBytes true = 0x2D +: empty := rfl

theorem signBytes_cases (s : Bool) : signBytes s = empty ∨
    signBytes s = 0x2B +: empty ∨ signBytes s = 0x2D +: empty := by
  cases s
  · exact Or.inl rfl
  · exact Or.inr (Or.inr rfl)

/-- A well-formed decomposition denotes an `RfcNumber` lexeme: the parts are
`NumBody`'s, so the derivation is the constructor of the shape the parts name. -/
theorem rfcNumber {d : Decimal} (h : d.wellFormed) : RfcNumber d.lexeme := by
  obtain ⟨hip, hfr, hex⟩ := h
  have hsign : ∀ s, signBytes s = empty ∨ signBytes s = 0x2B +: empty ∨
      signBytes s = 0x2D +: empty := signBytes_cases
  have hbody : NumBody d.body := by
    cases hf : d.fr with
    | none =>
      cases he : d.ex with
      | none =>
        have hb : d.body = d.ip := by simp only [body, hf, he]
        rw [hb]; exact NumBody.plain hip
      | some p =>
        obtain ⟨s, ds⟩ := p
        have hb : d.body = d.ip ++ (0x65 +: (signBytes s ++ ds)) := by
          simp only [body, hf, he]
        rw [hb]; exact NumBody.exp hip (ExpPart.mk (Or.inl rfl) (hsign s) (hex s ds he))
    | some fs =>
      cases he : d.ex with
      | none =>
        have hb : d.body = d.ip ++ (0x2E +: fs) := by simp only [body, hf, he]
        rw [hb]; exact NumBody.frac hip (hfr fs hf)
      | some p =>
        obtain ⟨s, ds⟩ := p
        have hb : d.body = (d.ip ++ (0x2E +: fs)) ++ (0x65 +: (signBytes s ++ ds)) := by
          simp only [body, hf, he]
        rw [hb]
        exact NumBody.fracExp hip (hfr fs hf) (ExpPart.mk (Or.inl rfl) (hsign s) (hex s ds he))
  cases hn : d.neg with
  | false =>
    have hlex : d.lexeme = d.body := by
      simp only [lexeme, hn, signBytes_false, empty_append]
    rw [hlex]
    exact RfcNumber.pos hbody
  | true =>
    have hlex : d.lexeme = 0x2D +: d.body := by
      simp only [lexeme, hn, signBytes_true, cons_append, empty_append]
    rw [hlex]
    exact RfcNumber.neg hbody

/-! ### The exact value

The exact value is a decimal: `(intDigits . fracDigits) * 10 ^ (exp - |frac|)`.
`ticks` puts it over the lattice of `2 ^ -1074`, so `P / d` is the value in units
of the smallest subnormal and every rounding comparison below is on `Nat`. -/

/-- The natural number a run of decimal digits denotes.  Bytes outside `0`–`9`
saturate at zero through the truncated subtraction; `wellFormed` is what makes
this the digits' value. -/
def digitsNat (bs : Bytes) : Nat :=
  bs.data.toList.foldl (fun acc b => acc * 10 + (b.toNat - 0x30)) 0

/-- The integer and fraction digits as one integer: `12.34 ↦ 1234`. -/
def mantissa (d : Decimal) : Nat :=
  let fs := d.fr.getD empty
  digitsNat d.ip * 10 ^ fs.length + digitsNat fs

/-- The power of ten the mantissa is scaled by: `12.34e5 ↦ 3`, `12.34e-5 ↦ -7`,
and `12 ↦ 0`. -/
def exponent (d : Decimal) : Int :=
  let e : Int :=
    match d.ex with
    | none => 0
    | some (s, ds) => if s then -(digitsNat ds : Int) else (digitsNat ds : Int)
  e - ((d.fr.getD empty).length : Int)

/-- The exact value in units of `2 ^ -1074`, as `(P, d)` with value `P / d`. -/
def ticks (d : Decimal) : Nat × Nat :=
  if 0 ≤ d.exponent then
    (d.mantissa * 10 ^ d.exponent.toNat * 2 ^ 1074, 1)
  else
    (d.mantissa * 2 ^ 1074, 10 ^ d.exponent.natAbs)

theorem ticks_den_pos (d : Decimal) : 0 < d.ticks.2 := by
  simp only [ticks]
  split
  · exact Nat.one_pos
  · exact Nat.pow_pos (by decide : 0 < 10)

end Decimal

/-! ### The binary64 encoding

The result is the encoding's own three pieces — the sign bit, the eleven-bit
exponent field and the fifty-two-bit trailing significand field — or an
infinity.  `NaN` is not a constructor because a decimal lexeme never denotes
one.  `toBits` is the eight bytes the event record carries, as a `Nat` in the
emitted little-endian byte order. -/

/-- A binary64 value: an infinity, or the encoding's sign bit, exponent field
and trailing significand field. -/
inductive Binary64 where
  | inf (neg : Bool)
  | fin (neg : Bool) (expField : Nat) (mant : Nat)
deriving DecidableEq, Repr

namespace Binary64

/-- The pattern's sign bit. -/
def sign : Binary64 → Bool
  | .inf neg => neg
  | .fin neg _ _ => neg

/-- The eight bytes as a little-endian `Nat`. -/
def toBits : Binary64 → Nat
  | .inf neg => (if neg then 2 ^ 63 else 0) + 0x7FF0000000000000
  | .fin neg E m =>
      (if neg then 2 ^ 63 else 0) + E * 2 ^ 52 + (if E = 0 then m else m - 2 ^ 52)

/-- The magnitude in ticks, or `none` for an infinity. -/
def magTicks : Binary64 → Option Nat
  | .inf _ => none
  | .fin _ E m => some (if E = 0 then m else m * 2 ^ (E - 1))

/-- Same-sign magnitude order: an infinity is above every finite value, and
finite values are ordered by their tick value.  At one sign this is the order on
the values the encodings name; across signs it is not, because the sign bit
inverts the order of the pattern. -/
def magLe : Binary64 → Binary64 → Prop
  | .inf _, .inf _ => True
  | .inf _, .fin _ _ _ => False
  | .fin _ _ _, .inf _ => True
  | .fin _ E₁ m₁, .fin _ E₂ m₂ =>
      (if E₁ = 0 then m₁ else m₁ * 2 ^ (E₁ - 1)) ≤
        (if E₂ = 0 then m₂ else m₂ * 2 ^ (E₂ - 1))

/-- The result is a value of the format: an infinity, or a well-formed finite
encoding.  This is the "the value is a binary64" property: the exponent field is
inside the eleven bits the encoding has, and the significand inside the
fifty-two. -/
def IsCode : Binary64 → Prop
  | .inf _ => True
  | .fin _ E m => (E = 0 ∧ m < 2 ^ 52) ∨
      (1 ≤ E ∧ E ≤ 2046 ∧ 2 ^ 52 ≤ m ∧ m < 2 ^ 53)

end Binary64

/-! ### The binary64 lattice

Every finite binary64 value is `m * 2 ^ -1074` for an integer `m` — the
subnormals are `0 ≤ m < 2 ^ 52`, the normals are `m = significand * 2 ^ j` with
`2 ^ 52 ≤ significand < 2 ^ 53` and `j ≤ 2045` — so `IsB64Mag` is the whole
finite value set in the tick lattice.  `2 ^ 2098 - 2 ^ 2044` is the tick value of
`2 ^ 1024 - 2 ^ 970`, the midpoint between the largest finite value and
`2 ^ 1024`: the threshold at and above which `roundTiesToEven` overflows. -/

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

/-- The signed result of a decimal conversion. -/
def strtodSpec (d : Decimal) : Binary64 :=
  match roundMag d.ticks.1 d.ticks.2, d.neg with
  | .inf, neg => .inf neg
  | .fin c, neg => .fin neg c.expField c.mant

/-! ### The rounding property

The exact value is `P / d` in ticks and a result is a lattice point.  Every
statement below is integer arithmetic on the two tick coordinates: the distance
from `P / d` to the lattice point `M` is `|P - M d| / d`, and the common
positive factor `d` is dropped, so ordering `|P - M d|` orders the distances.
The three things a correctly rounded conversion owes are then: the result is a
code of the format, no finite magnitude is nearer, and a tie is decided by the
significand's parity. -/

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

/-- The signed result of a decimal: the sign comes from the lexeme and the
magnitude from the rounding.  A zero lexeme keeps its sign, so `-0` and `-0.0`
convert to `-0.0`, and `0` to `+0.0`; `strtodSpec_zero` states it. -/
theorem strtodSpec_isCode (d : Decimal) : (strtodSpec d).IsCode := by
  have hd := d.ticks_den_pos
  cases h : roundMag d.ticks.1 d.ticks.2 with
  | inf => simp only [strtodSpec, h]; exact trivial
  | fin c =>
    have hno : ¬ overflowTicks * d.ticks.2 ≤ d.ticks.1 := by
      intro hov
      rw [(roundMag_overflow_iff hd).mpr hov] at h
      exact absurd h (by simp)
    obtain ⟨c', hc', hm⟩ := roundMag_isCode hd hno
    rw [hc'] at h
    simp only [Mag.fin.injEq] at h
    subst h
    simp only [strtodSpec, hc']
    exact hm

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

/-- A zero lexeme's result keeps the lexeme's sign: `-0` is `-0.0`. -/
theorem strtodSpec_zero {d : Decimal} (h : d.mantissa = 0) :
    strtodSpec d = .fin d.neg 0 0 := by
  have helim : d.ticks.1 = 0 := by
    unfold Decimal.ticks
    split <;> simp [h]
  unfold strtodSpec
  rw [helim, roundMag_zero d.ticks_den_pos]

/-! ### The tie clause

`roundTiesToEven` decides a tie by the significand's parity, and that is the one
thing nearestness alone leaves open: the exact midpoint of two adjacent lattice
points is equidistant from both.  The midpoint is `2 * rem = ulp` in the
definition's own terms, and the result's trailing significand is then even. -/

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

/-- The eight bytes of a 64-bit pattern, little-endian, as `out_u64` writes them
(`stage2.c`'s `out_u64`). -/
def bitsBytes (n : Nat) : List UInt8 :=
  (List.range 8).map (fun i => UInt8.ofNat ((n >>> (8 * i)) &&& 0xFF))

/-- A number's event record at `at`: the `T_NUM` tag (`7`) and the eight payload
bytes of `bits`. -/
def NumberRecordAt (evs : List UInt8) (off : Nat) (bits : Nat) : Prop :=
  evs[off]? = some 7 ∧ (evs.drop (off + 1)).take 8 = bitsBytes bits

/-- **The number arm.**  A `T_NUM` record whose payload is `strtodSpec`'s
encoding of the lexeme the token's span holds: the clause `EventStreamRel`
(`JsonPipelineSpec.lean:209`) takes as a parameter and `ParserHalf`
(`JsonPipelineRefine.lean:941`) names as owed. -/
def EventStreamNumberArm (evs : List UInt8) (off : Nat) (d : Decimal) : Prop :=
  NumberRecordAt evs off (strtodSpec d).toBits

/-- The arm's content: the record's payload is `strtodSpec`'s bits, which is the
`double` the record carries.  Reading the payload back gives the encoding, so a
relation that names this arm binds the record to the lexeme's value. -/
theorem numberArm_payload {evs : List UInt8} {off : Nat} {d : Decimal}
    (h : EventStreamNumberArm evs off d) :
    evs[off]? = some 7 ∧
      (evs.drop (off + 1)).take 8 = bitsBytes (strtodSpec d).toBits := h

/-- The conversion's own record is the arm at offset zero: the `T_NUM` tag and
the eight bytes `strtodSpec` encodes.  The arm is inhabited by the specification
itself, so a relation that names it is not vacuous. -/
theorem strtodSpec_isNumberArm (d : Decimal) :
    EventStreamNumberArm (7 :: bitsBytes (strtodSpec d).toBits) 0 d := by
  have hlen : (bitsBytes (strtodSpec d).toBits).length = 8 := by
    simp [bitsBytes]
  refine ⟨rfl, ?_⟩
  have hdrop : (7 :: bitsBytes (strtodSpec d).toBits).drop (0 + 1)
      = bitsBytes (strtodSpec d).toBits := rfl
  rw [hdrop]
  exact List.take_of_length_le (by simp [hlen])

/-- The payload's bits are the result's encoding, and the result is a binary64
with the number's sign: the record and `Value.number`'s lexeme agree on the
value's encoding, which is what the relation needs. -/
theorem numberArm_isCode {evs : List UInt8} {off : Nat} {d : Decimal}
    (_h : EventStreamNumberArm evs off d) : (strtodSpec d).IsCode :=
  strtodSpec_isCode d

/-- What the refinement slice owes, stated at this module's vocabulary: the
emitted conversion's bits equal `strtodSpec`'s on every lexeme the parser
accepts.  It is not proved here and no emitted run is modelled: `num_fast`'s
tier 1 is a `double` multiply or divide by an exact power of ten, its tier 2 a
128-bit multiply against `epow_table.h`'s normalised significands with the
`strtod` fallback, and its tier 3 `num_scan`'s `strtod` call.  Proving these
compute `strtodSpec` needs, in this module's terms: (a) the tier-1 identity —
`(mant : double) * 10 ^ k` with both operands exact below `2 ^ 53` is one IEEE
operation, so it is the correctly rounded value of the exact product, which is
`roundMag`'s bracket for those `(P, d)`; (b) the tier-2 bound — the 128-bit
product's error is below a half-ulp except in the reported-ambiguous cases, so
`roundMag`'s two candidate distances are decided by its comparison and the
ambiguous cases are exactly the ones that fall back; (c) the tier-3 identity —
`strtod` rounds correctly, which is a property of the C library and not of this
tree, so that tier is an assumption about the platform or is dropped from the
domain. -/
def NumberArmOwed (numFastBits : Bytes → Nat) : Prop :=
  ∀ (d : Decimal), RfcNumber d.lexeme → numFastBits d.lexeme = (strtodSpec d).toBits

/-! ### The result depends on the exact value, not on the pair

Two tick pairs with the same ratio round to the same code: every branch's test is
a comparison of two products with this pair's positive factors, and the
comparison and the quotient are carried across the ratio.  This is what makes
`strtodSpec` a function of the value; `strtodSpec_mono` needs it only at the
exact midpoint, where two representations of one value must agree. -/

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

/-- At a fixed sign the conversion is monotone in the lexeme's exact value: a
larger value does not convert to a smaller magnitude. -/
theorem strtodSpec_mono {d₁ d₂ : Decimal}
    (hval : d₁.ticks.1 * d₂.ticks.2 ≤ d₂.ticks.1 * d₁.ticks.2) :
    (strtodSpec d₁).magLe (strtodSpec d₂) := by
  have hd₁ := d₁.ticks_den_pos
  have hd₂ := d₂.ticks_den_pos
  have hm := roundMag_mono hd₁ hd₂ hval
  cases h₁ : roundMag d₁.ticks.1 d₁.ticks.2 with
  | inf =>
    cases h₂ : roundMag d₂.ticks.1 d₂.ticks.2 with
    | inf => simp only [strtodSpec, h₁, h₂, Binary64.magLe]
    | fin c₂ =>
      rw [h₁, h₂] at hm
      have hfalse : Mag.le Mag.inf (Mag.fin c₂) := hm
      simp only [Mag.le] at hfalse
  | fin c₁ =>
    cases h₂ : roundMag d₂.ticks.1 d₂.ticks.2 with
    | inf => simp only [strtodSpec, h₁, h₂, Binary64.magLe]
    | fin c₂ =>
      rw [h₁, h₂] at hm
      simp only [strtodSpec, h₁, h₂, Binary64.magLe]
      exact hm

/-! ### Axiom pins

Every declaration above is pinned: `#print axioms` names what it depends on, so a
change that introduces an axiom is visible in the build log.  The theorems depend
on `propext` and `Quot.sound` at most; the arithmetic ones on nothing. -/

#print axioms LeanLLVM.JSON.Decimal
#print axioms LeanLLVM.JSON.Decimal.signBytes
#print axioms LeanLLVM.JSON.Decimal.body
#print axioms LeanLLVM.JSON.Decimal.lexeme
#print axioms LeanLLVM.JSON.Decimal.wellFormed
#print axioms LeanLLVM.JSON.Decimal.signBytes_false
#print axioms LeanLLVM.JSON.Decimal.signBytes_true
#print axioms LeanLLVM.JSON.Decimal.signBytes_cases
#print axioms LeanLLVM.JSON.Decimal.rfcNumber
#print axioms LeanLLVM.JSON.Decimal.digitsNat
#print axioms LeanLLVM.JSON.Decimal.mantissa
#print axioms LeanLLVM.JSON.Decimal.exponent
#print axioms LeanLLVM.JSON.Decimal.ticks
#print axioms LeanLLVM.JSON.Decimal.ticks_den_pos
#print axioms LeanLLVM.JSON.Binary64
#print axioms LeanLLVM.JSON.Binary64.sign
#print axioms LeanLLVM.JSON.Binary64.toBits
#print axioms LeanLLVM.JSON.Binary64.magTicks
#print axioms LeanLLVM.JSON.Binary64.magLe
#print axioms LeanLLVM.JSON.Binary64.IsCode
#print axioms LeanLLVM.JSON.IsB64Mag
#print axioms LeanLLVM.JSON.maxMagTicks
#print axioms LeanLLVM.JSON.overflowTicks
#print axioms LeanLLVM.JSON.Code
#print axioms LeanLLVM.JSON.Code.ticks
#print axioms LeanLLVM.JSON.Code.IsMag
#print axioms LeanLLVM.JSON.Code.isB64Mag_ticks
#print axioms LeanLLVM.JSON.Mag
#print axioms LeanLLVM.JSON.Mag.le
#print axioms LeanLLVM.JSON.findFrom
#print axioms LeanLLVM.JSON.findFrom_spec
#print axioms LeanLLVM.JSON.findFrom_exists
#print axioms LeanLLVM.JSON.binade
#print axioms LeanLLVM.JSON.binade_spec
#print axioms LeanLLVM.JSON.ulp
#print axioms LeanLLVM.JSON.sig
#print axioms LeanLLVM.JSON.lo
#print axioms LeanLLVM.JSON.hi
#print axioms LeanLLVM.JSON.subCode
#print axioms LeanLLVM.JSON.normalCode
#print axioms LeanLLVM.JSON.roundMag
#print axioms LeanLLVM.JSON.strtodSpec
#print axioms LeanLLVM.JSON.two_pow_pos
#print axioms LeanLLVM.JSON.two_pow_lt_of_lt
#print axioms LeanLLVM.JSON.two_pow_lt_iff
#print axioms LeanLLVM.JSON.two_pow_le_iff
#print axioms LeanLLVM.JSON.distNum
#print axioms LeanLLVM.JSON.ticks_zero
#print axioms LeanLLVM.JSON.ticks_normal
#print axioms LeanLLVM.JSON.sub_succ_ticks
#print axioms LeanLLVM.JSON.normal_succ_ticks
#print axioms LeanLLVM.JSON.sub_succ_isMag
#print axioms LeanLLVM.JSON.ulp_mul_52
#print axioms LeanLLVM.JSON.ulp_mul_53
#print axioms LeanLLVM.JSON.ulp_pos
#print axioms LeanLLVM.JSON.mul_ulp_pos
#print axioms LeanLLVM.JSON.binade_facts
#print axioms LeanLLVM.JSON.sig_bounds
#print axioms LeanLLVM.JSON.div_mul_add_mod
#print axioms LeanLLVM.JSON.lo_d_le
#print axioms LeanLLVM.JSON.lt_hi_d
#print axioms LeanLLVM.JSON.lo_rem
#print axioms LeanLLVM.JSON.hi_rem
#print axioms LeanLLVM.JSON.dist_min_le
#print axioms LeanLLVM.JSON.dist_min_ge
#print axioms LeanLLVM.JSON.dvd_ulp_of_mem
#print axioms LeanLLVM.JSON.no_gap
#print axioms LeanLLVM.JSON.overflowTicks_factor
#print axioms LeanLLVM.JSON.two_pow_2045
#print axioms LeanLLVM.JSON.overflowTicks_le
#print axioms LeanLLVM.JSON.two_overflowTicks
#print axioms LeanLLVM.JSON.normal_carry_overflow
#print axioms LeanLLVM.JSON.normal_succ_ticks'
#print axioms LeanLLVM.JSON.normal_ticks
#print axioms LeanLLVM.JSON.sub_ticks
#print axioms LeanLLVM.JSON.normalCode_isMag
#print axioms LeanLLVM.JSON.sub_sig_lt
#print axioms LeanLLVM.JSON.subCode_isMag
#print axioms LeanLLVM.JSON.ulp_eq
#print axioms LeanLLVM.JSON.normal_choice_le
#print axioms LeanLLVM.JSON.sub_choice_le
#print axioms LeanLLVM.JSON.normal_nearest
#print axioms LeanLLVM.JSON.sub_no_gap
#print axioms LeanLLVM.JSON.sub_nearest
#print axioms LeanLLVM.JSON.roundMag_nearest
#print axioms LeanLLVM.JSON.roundMag_no_strict_between
#print axioms LeanLLVM.JSON.roundMag_isCode
#print axioms LeanLLVM.JSON.roundMag_overflow_iff
#print axioms LeanLLVM.JSON.roundMag_overflow_nearest
#print axioms LeanLLVM.JSON.strtodSpec_isCode
#print axioms LeanLLVM.JSON.roundMag_zero
#print axioms LeanLLVM.JSON.strtodSpec_zero
#print axioms LeanLLVM.JSON.normalCode_tie_even
#print axioms LeanLLVM.JSON.subCode_tie_even
#print axioms LeanLLVM.JSON.roundMag_midpoint_even
#print axioms LeanLLVM.JSON.bitsBytes
#print axioms LeanLLVM.JSON.NumberRecordAt
#print axioms LeanLLVM.JSON.EventStreamNumberArm
#print axioms LeanLLVM.JSON.numberArm_payload
#print axioms LeanLLVM.JSON.strtodSpec_isNumberArm
#print axioms LeanLLVM.JSON.numberArm_isCode
#print axioms LeanLLVM.JSON.NumberArmOwed
#print axioms LeanLLVM.JSON.lt_iff_mul_lt_mul_right
#print axioms LeanLLVM.JSON.lt_of_mul_lt_mul_right
#print axioms LeanLLVM.JSON.le_iff_mul_le_mul_right
#print axioms LeanLLVM.JSON.findFrom_congr
#print axioms LeanLLVM.JSON.div_eq_of_ratio
#print axioms LeanLLVM.JSON.rem_cross
#print axioms LeanLLVM.JSON.rem_lt_iff_of_ratio
#print axioms LeanLLVM.JSON.rem_gt_iff_of_ratio
#print axioms LeanLLVM.JSON.subCode_eq_of_ratio
#print axioms LeanLLVM.JSON.normalCode_eq_of_ratio
#print axioms LeanLLVM.JSON.roundMag_eq_of_ratio
#print axioms LeanLLVM.JSON.overflow_mono
#print axioms LeanLLVM.JSON.roundMag_fin_le
#print axioms LeanLLVM.JSON.roundMag_mono
#print axioms LeanLLVM.JSON.strtodSpec_mono
