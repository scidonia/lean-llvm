/-
Floating-point numbers: the adapter for `Mathlib.Data.FP.Basic`.

`Mathlib.Data.FP.Basic` is Mario Carneiro's port of Flocq's approach.  A format
is fixed by an instance of `FP.FloatCfg` — a precision and a maximum exponent,
with the minimum exponent derived.  A number is a sign together with an
exponent and a significand, and the pair `(e, m)` is a well-formed finite number
exactly when `FP.ValidFinite e m` holds; the number it denotes has an exact
rational value, `FP.toRat`.  A rounding decision compares a quotient with a
power of two, and `FP.divNatLtTwoPow` takes it without dividing.

`Mathlib.*` is confined to the adapters under `ITree/Internal/` (`AGENTS.md`),
so this file re-exports what a floating-point model needs and adds nothing: no
new structure, no notation, and no renamed spelling of an existing name.  Each
name below is the mathlib constant itself, so a client imports this file and
writes the statement it would have written against mathlib.  The one exception
is the carrier, whose mathlib name `Float` collides with Lean's own `Float`; it
is re-exported as `FloatingPoint`.  Its constructors are re-exported too: a
client that cannot build a number cannot apply `toRat`, so leaving them out
would send it back to `FP.Float.finite` at its first value, and the boundary
would move rather than hold.

| here | `Mathlib.Data.FP.Basic` | meaning |
| --- | --- | --- |
| `FloatCfg` | `FP.FloatCfg` | the format: `prec`, `emax`, `precPos`, `precMax` |
| `prec` | `FP.prec` | the precision, in bits |
| `emax` | `FP.emax` | the largest exponent the leading bit may reach |
| `emin` | `FP.emin` | the derived minimum exponent, `1 - emax` |
| `ValidFinite` | `FP.ValidFinite` | an `(exponent, significand)` pair is a finite number |
| `FloatingPoint` | `FP.Float` | the numbers of a format: sign, exponent, significand, infinities, NaN |
| `inf`, `nan`, `finite` | `FP.Float.inf`, `FP.Float.nan`, `FP.Float.finite` | the constructors: an infinity from its sign, a NaN, and a finite number from a sign, an exponent and a significand with the `ValidFinite` proof that admits them |
| `isFinite` | `FP.Float.isFinite` | the `Bool` discriminator a finite value's proof is drawn from |
| `toRat` | `FP.toRat` | the exact rational value of a finite number |
| `divNatLtTwoPow` | `FP.divNatLtTwoPow` | whether `n / d < 2 ^ e`, decided without dividing |

Adapted from no upstream file: this is a local adapter, and the names it
re-exports belong to the pinned mathlib revision in `lakefile.toml`.  See
`ITree/README.md` for the import boundary.
-/
import Mathlib.Data.FP.Basic

namespace ITree.Internal

export FP (FloatCfg prec emax emin ValidFinite divNatLtTwoPow toRat)

export FP.Float (isFinite inf nan finite)

/-- The numbers of a format (`Mathlib.Data.FP.Basic`'s `FP.Float`): `inf`, `nan`,
or a finite sign, exponent and significand carrying the proof that the pair is
in range.

The name is the one deviation this adapter makes: `FP.Float`'s bare name here
would hide Lean's own `Float`.  The format is the `FloatCfg` instance in scope,
so `FloatingPoint` is a type only where a format is fixed. -/
abbrev FloatingPoint [C : FloatCfg] : Type := FP.Float

/-! ### The format parameters

`prec`, `emax` and `emin` are `FP.prec`, `FP.emax` and `FP.emin`.  They are
projections of the format's `FloatCfg` instance, so they are read at the
instance in scope rather than passed: `emin = 1 - emax`, and the leading bit of
a finite number occupies an exponent between `emin` and `emax`. -/

/-! ### The exactness predicate

`ValidFinite e m` is `FP.ValidFinite e m`: for a significand `m : ℕ` and an
exponent `e : ℤ`, the scaled leading exponent `e + prec - 1` lies in
`emin`'s range up to `emax`, and `e` is the exponent that normalises `m` to
`prec` bits, floored at `emin` for the subnormal step.  The number it admits is
exact — `toRat` rounds nothing — and the predicate is decidable, so a concrete
pair's membership is a computation. -/

/-! ### The exact value

`toRat f h` is `FP.toRat`: the value of the finite number `f`, whose finiteness
is the proof `h`, as a rational.  The proof is the parameter, not a bundled
subtype: a caller that already has `h : isFinite f = true` passes it. -/

/-! ### The comparison primitive

`divNatLtTwoPow n d e` is `FP.divNatLtTwoPow`: it decides `n / d < 2 ^ e` for
`n d : ℕ` and `e : ℤ`.  For `e ≥ 0` it compares `n` with `d * 2 ^ e`, for
`e < 0` it clears the denominator's power on the other side and compares
`n * 2 ^ (-e)` with `d`, so no division and no rounding happens on the way. -/

/-! ### Checks

Each re-export is exercised below.  The format is a local binary64 instance
(`prec = 53`, `emax = 1023`, hence `emin = -1022`): it exists only for these
checks, and this adapter fixes no format. -/

section Checks

local instance checkFormat : FloatCfg :=
  { prec := 53, emax := 1023, precPos := by decide, precMax := by decide }

/-- The precision projects from the instance in scope. -/
example : prec = 53 := rfl
#guard emax = 1023
#guard emin = -1022

/-- Zero is a finite number at `emin`, the format's own witness. -/
example : ValidFinite emin 0 := FP.Float.Zero.valid
/-- The predicate is decidable and is not vacuous: `0` at exponent `0` would
denote a number whose leading bit sits below the significand's own precision
and the normalising equation fails. -/
example : ¬ ValidFinite 0 0 := by decide

/-- One, as a binary64 value: exponent `0`, significand `2 ^ 52`, so
`toRat` shifts the significand by the exponent and divides by `1`. -/
private def one : FloatingPoint :=
  finite false 0 (2 ^ 52) (by decide)

example : isFinite one = true := rfl
#guard toRat one rfl == (2 ^ 52 : ℚ)

/-- The sign branch of `toRat`: the same magnitudes, negated. -/
private def negOne : FloatingPoint :=
  finite true 0 (2 ^ 52) (by decide)

#guard toRat negOne rfl == (-(2 ^ 52) : ℚ)

/-- A non-finite value reports `false`, so a finite value's proof cannot be had
for it.  Both infinities and NaN are built through the exported constructors. -/
example : isFinite (inf true) = false := rfl
example : isFinite (inf false) = false := rfl
example : isFinite nan = false := rfl

-- `divNatLtTwoPow` at nonnegative exponents: `1 / 2 < 1` holds and
-- `1 / 1 < 1` does not.
#guard divNatLtTwoPow 1 2 0 = true
#guard divNatLtTwoPow 1 1 0 = false
-- At negative exponents the comparison moves the power of two across:
-- `1 / 3 < 1 / 2` holds, `1 / 2 < 1 / 2` and `1 / 2 < 1 / 4` do not.
#guard divNatLtTwoPow 1 3 (-1) = true
#guard divNatLtTwoPow 1 2 (-1) = false
#guard divNatLtTwoPow 1 2 (-2) = false

-- The re-exports add no proof of their own — each is the mathlib constant — so
-- the footprint printed here is the one that constant already has, not a new
-- one.  `FP.Float` and `FP.ValidFinite` are `[propext, Quot.sound]` (from the
-- derived `Decidable` instance); `FP.toRat` reaches `Classical.choice` through
-- `mkRat`.
#print axioms FloatingPoint
#print axioms ValidFinite
#print axioms toRat
#print axioms divNatLtTwoPow
#print axioms one
#print axioms negOne

end Checks

end ITree.Internal
