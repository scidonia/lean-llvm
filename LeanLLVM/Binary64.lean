/-
binary64 on bit patterns: the exact IEEE 754 value model the floating-point
instruction forms read, and the round-to-nearest-even lattice
`LeanLLVM.JSON.Strtod` states, restated here so the model layer can read its
rounding without importing the JSON reference parser.

The carrier is `BitVec 64` — LLVM's `double` — so `bitcast` is the identity,
signed zeros are distinct, and a NaN keeps its payload.  The arithmetic is
defined on the encoding's fields; every operation computes its exact value as
a pair `(P, d)` in ticks (units of `2 ^ -1074`) and rounds it once with
`roundMag`, so there is no intermediate rounding and no dependence on Lean's
native `Float`.

`IsB64Mag` … `roundMag` are the definitions and proofs
`LeanLLVM/JSON/Strtod.lean` also states; the model layer restates them here
because it cannot import the JSON reference parser, and the decimal
specification keeps its own copies until the lattice moves to this module.
-/
import LeanLLVM.Basic

namespace LeanLLVM

/-! ### The lattice

A magnitude is a natural number of ticks, `2 ^ -1074` units.  `IsB64Mag` is the
set of ticks a binary64 value can have; `Code` is an encoding's exponent field
and significand, `findFrom`/`binade` locate the binade, and `subCode`/
`normalCode` choose the nearest code with the even significand on a tie. -/

def IsB64Mag (M : Nat) : Prop :=
  M = 0 ∨ M < 2 ^ 52 ∨
    ∃ j m : Nat, j ≤ 2045 ∧ 2 ^ 52 ≤ m ∧ m < 2 ^ 53 ∧ M = m * 2 ^ j

def maxMagTicks : Nat := (2 ^ 53 - 1) * 2 ^ 2045

def overflowTicks : Nat := 2 ^ 2098 - 2 ^ 2044

structure Code where
  expField : Nat
  mant : Nat
deriving DecidableEq, Repr

namespace Code

def ticks (c : Code) : Nat :=
  if c.expField = 0 then c.mant else c.mant * 2 ^ (c.expField - 1)

/-- The codes a binary64 value has: zero, a subnormal, or a normalised
significand with the implicit bit. -/
def IsMag (c : Code) : Prop :=
  c.ticks = 0 ∨
    (c.expField = 0 ∧ c.mant < 2 ^ 52) ∨
    (c.expField ≠ 0 ∧ 2 ^ 52 ≤ c.mant ∧ c.mant < 2 ^ 53)

end Code

inductive Mag where
  | inf
  | fin (code : Code)
deriving DecidableEq, Repr

/-- Order on magnitudes, comparing the value a code denotes. -/
def Mag.le : Mag → Mag → Prop
  | .inf, .inf => True
  | .inf, .fin _ => False
  | .fin _, .inf => True
  | .fin a, .fin b => a.ticks ≤ b.ticks

def findFrom (p : Nat → Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, k => if p k then some k else findFrom p fuel (k + 1)

def binade (P d : Nat) : Nat :=
  (findFrom (fun B => decide (P < d * 2 ^ (B + 1))) 2100 0).getD 0

def ulp (P d : Nat) : Nat := 2 ^ (binade P d - 52)

def sig (P d : Nat) : Nat := P / (d * ulp P d)

def lo (P d : Nat) : Nat := sig P d * ulp P d

def hi (P d : Nat) : Nat := (sig P d + 1) * ulp P d

def subCode (P d : Nat) : Code :=
  let q := P / d
  let r := P % d
  if 2 * r < d then ⟨0, q⟩
  else if d < 2 * r then (if q + 1 = 2 ^ 52 then ⟨1, 2 ^ 52⟩ else ⟨0, q + 1⟩)
  else if q % 2 = 0 then ⟨0, q⟩
  else if q + 1 = 2 ^ 52 then ⟨1, 2 ^ 52⟩ else ⟨0, q + 1⟩

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

/-- Round the exact value `P / d` ticks to the nearest binary64 magnitude, ties
to even, and overflow to infinity. -/
def roundMag (P d : Nat) : Mag :=
  if overflowTicks * d ≤ P then .inf
  else if P < d * 2 ^ 52 then .fin (subCode P d)
  else .fin (normalCode P d)

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
