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
multiply against `epow_table.h`'s normalised `10 ^ eff`, with its undecidable
cases handed to the next tier) and its tier 3 (the unit's own conversion: a
768-digit window of significant digits, one sticky bit for the digits past it,
and one nearest-even rounding from the three) computes this function — is a
separate slice, and `NumberArmOwed`'s docstring names what it needs.  This
module proves no run of any emitted code computes anything.  The corpus checks
(`tests/json-strtod/`) use glibc's `strtod` as an oracle, not as an assumption
about how a tier is implemented: `check.sh` is evidence about the
specification's agreement with it, and `long.sh` is evidence about the emitted
conversion's agreement with it on the lexemes whose length or whose tail
decides the rounding.  Neither is a proof about either side.

There is no `sorry`, `admit` or `native_decide` below, and the declarations'
axioms are pinned at the end of the file.
-/
import LeanLLVM.Binary64
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
128-bit multiply against `epow_table.h`'s normalised significands with its
undecidable cases handed on, and its tier 3 the unit's own conversion — a
bounded window of significant digits, one sticky bit for the digits past it, and
one nearest-even rounding from the three.  Proving these compute `strtodSpec`
needs, in this module's terms: (a) the tier-1 identity — `(mant : double) *
10 ^ k` with both operands exact below `2 ^ 53` is one IEEE operation, so it is
the correctly rounded value of the exact product, which is `roundMag`'s bracket
for those `(P, d)`; (b) the tier-2 bound — the 128-bit product's error is below
a half-ulp except in the reported-ambiguous cases, so `roundMag`'s two candidate
distances are decided by its comparison and the ambiguous cases are exactly the
ones that fall through; (c) the tier-3 identity — the fallback's one nearest-even
rounding from its retained window and its sticky bit is `roundMag`'s, which is a
proof about this tree's own code and needs no platform axiom.  All three are
obligations here, not results. -/
def NumberArmOwed (numFastBits : Bytes → Nat) : Prop :=
  ∀ (d : Decimal), RfcNumber d.lexeme → numFastBits d.lexeme = (strtodSpec d).toBits

/-! ### The result depends on the exact value, not on the pair

Two tick pairs with the same ratio round to the same code: every branch's test is
a comparison of two products with this pair's positive factors, and the
comparison and the quotient are carried across the ratio.  This is what makes
`strtodSpec` a function of the value; `strtodSpec_mono` needs it only at the
exact midpoint, where two representations of one value must agree. -/

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
#print axioms LeanLLVM.IsB64Mag
#print axioms LeanLLVM.maxMagTicks
#print axioms LeanLLVM.overflowTicks
#print axioms LeanLLVM.Code
#print axioms LeanLLVM.Code.ticks
#print axioms LeanLLVM.Code.IsMag
#print axioms LeanLLVM.Code.isB64Mag_ticks
#print axioms LeanLLVM.Mag
#print axioms LeanLLVM.Mag.le
#print axioms LeanLLVM.findFrom
#print axioms LeanLLVM.findFrom_spec
#print axioms LeanLLVM.findFrom_exists
#print axioms LeanLLVM.binade
#print axioms LeanLLVM.binade_spec
#print axioms LeanLLVM.ulp
#print axioms LeanLLVM.sig
#print axioms LeanLLVM.lo
#print axioms LeanLLVM.hi
#print axioms LeanLLVM.subCode
#print axioms LeanLLVM.normalCode
#print axioms LeanLLVM.roundMag
#print axioms LeanLLVM.JSON.strtodSpec
#print axioms LeanLLVM.two_pow_pos
#print axioms LeanLLVM.two_pow_lt_of_lt
#print axioms LeanLLVM.two_pow_lt_iff
#print axioms LeanLLVM.two_pow_le_iff
#print axioms LeanLLVM.distNum
#print axioms LeanLLVM.ticks_zero
#print axioms LeanLLVM.ticks_normal
#print axioms LeanLLVM.sub_succ_ticks
#print axioms LeanLLVM.normal_succ_ticks
#print axioms LeanLLVM.sub_succ_isMag
#print axioms LeanLLVM.ulp_mul_52
#print axioms LeanLLVM.ulp_mul_53
#print axioms LeanLLVM.ulp_pos
#print axioms LeanLLVM.mul_ulp_pos
#print axioms LeanLLVM.binade_facts
#print axioms LeanLLVM.sig_bounds
#print axioms LeanLLVM.div_mul_add_mod
#print axioms LeanLLVM.lo_d_le
#print axioms LeanLLVM.lt_hi_d
#print axioms LeanLLVM.lo_rem
#print axioms LeanLLVM.hi_rem
#print axioms LeanLLVM.dist_min_le
#print axioms LeanLLVM.dist_min_ge
#print axioms LeanLLVM.dvd_ulp_of_mem
#print axioms LeanLLVM.no_gap
#print axioms LeanLLVM.overflowTicks_factor
#print axioms LeanLLVM.two_pow_2045
#print axioms LeanLLVM.overflowTicks_le
#print axioms LeanLLVM.two_overflowTicks
#print axioms LeanLLVM.normal_carry_overflow
#print axioms LeanLLVM.normal_succ_ticks'
#print axioms LeanLLVM.normal_ticks
#print axioms LeanLLVM.sub_ticks
#print axioms LeanLLVM.normalCode_isMag
#print axioms LeanLLVM.sub_sig_lt
#print axioms LeanLLVM.subCode_isMag
#print axioms LeanLLVM.ulp_eq
#print axioms LeanLLVM.normal_choice_le
#print axioms LeanLLVM.sub_choice_le
#print axioms LeanLLVM.normal_nearest
#print axioms LeanLLVM.sub_no_gap
#print axioms LeanLLVM.sub_nearest
#print axioms LeanLLVM.roundMag_nearest
#print axioms LeanLLVM.roundMag_no_strict_between
#print axioms LeanLLVM.roundMag_isCode
#print axioms LeanLLVM.roundMag_overflow_iff
#print axioms LeanLLVM.roundMag_overflow_nearest
#print axioms LeanLLVM.JSON.strtodSpec_isCode
#print axioms LeanLLVM.roundMag_zero
#print axioms LeanLLVM.JSON.strtodSpec_zero
#print axioms LeanLLVM.normalCode_tie_even
#print axioms LeanLLVM.subCode_tie_even
#print axioms LeanLLVM.roundMag_midpoint_even
#print axioms LeanLLVM.JSON.bitsBytes
#print axioms LeanLLVM.JSON.NumberRecordAt
#print axioms LeanLLVM.JSON.EventStreamNumberArm
#print axioms LeanLLVM.JSON.numberArm_payload
#print axioms LeanLLVM.JSON.strtodSpec_isNumberArm
#print axioms LeanLLVM.JSON.numberArm_isCode
#print axioms LeanLLVM.JSON.NumberArmOwed
#print axioms LeanLLVM.lt_iff_mul_lt_mul_right
#print axioms LeanLLVM.lt_of_mul_lt_mul_right
#print axioms LeanLLVM.le_iff_mul_le_mul_right
#print axioms LeanLLVM.findFrom_congr
#print axioms LeanLLVM.div_eq_of_ratio
#print axioms LeanLLVM.rem_cross
#print axioms LeanLLVM.rem_lt_iff_of_ratio
#print axioms LeanLLVM.rem_gt_iff_of_ratio
#print axioms LeanLLVM.subCode_eq_of_ratio
#print axioms LeanLLVM.normalCode_eq_of_ratio
#print axioms LeanLLVM.roundMag_eq_of_ratio
#print axioms LeanLLVM.overflow_mono
#print axioms LeanLLVM.roundMag_fin_le
#print axioms LeanLLVM.roundMag_mono
#print axioms LeanLLVM.JSON.strtodSpec_mono
