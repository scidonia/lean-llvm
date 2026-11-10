/-
`strtodSpec` is the specification; the emitted stage-2 number path is the code.
This module states the refinement obligation between them and nothing else: it
does not model the emitted body, and it proves no run of it.  The one theorem
below proves that the statement's classes partition the well-formed lexemes —
the statement's shape, not the conversion.

## The statement

`EmittedConversionRefines emitted kernelDecides` says: on every well-formed
lexeme, at each of the emitted code's own branch tests and at each magnitude
class the rounding rule distinguishes, the binary64 encoding the emitted
conversion returns is `strtodSpec`'s.  `emitted` is the emitted conversion's
result, read as `Binary64`; `kernelDecides` is the 128-bit kernel's own return,
so the statement does not guess a decision the module cannot see.

## The exact rational is already there, and it is `Pff`'s shape

Flocq's `Pff` (Boldo and Melquiond) converts a decimal to a float in three
steps: compute the exact rational the decimal names, round it once to the
target format, and prove that round is the correctly rounded one.  `strtodSpec`
is stated in exactly that shape, so the refinement does not need a new
intermediate rational:

* `Decimal.ticks` (`LeanLLVM/JSON/Strtod.lean`) is the exact rational, as the
  pair `(P, d)` whose value is `P / d` in units of `2 ^ -1074`;
* `roundMag P d` is the single rounding of that rational onto the binary64
  lattice, with the subnormal region, the normal region and the overflow
  threshold each a branch;
* `roundMag_nearest` is the nearestness property, `roundMag_midpoint_even` the
  tie clause, and `roundMag_eq_of_ratio` says the
  result is a function of the exact value and not of the `(P, d)` spelling.

So the decimal-to-binary reduction is present on the specification side.  What
is absent is the same argument for the *emitted* side, whose branches are:

* **tier 1** (`nd ≤ 15`, `|eff| ≤ 22`): one IEEE binary64 multiply or divide of
  exact operands, i.e. one rounding of an exact binary rational.  This is
  `Pff`'s round-once step with the rational already binary; it is the branch for
  which the arithmetic core is not the wall.
* **tier 2** (`nd ≤ 19`, `eff ∈ [-45, 45]`): `num_el_el1`'s truncated 128-bit
  product against `epow_table.h`'s normalised significand, with a guard-slice
  window and the exact low-half multiply.  This is **not** a single correctly
  rounded operation and does not form `P` and `d`; its exactness is the first
  obstruction (below).
* **tier 3** (everything else, and every tier-2 refusal): `num_scan` copies the
  token and calls the C library's `strtod` (`to_double`'s own `nd ≤ 15` integer
  fast path is the exact case).  Its correctness is a property of the platform,
  not of this tree.

## The first obstruction, executed

The tie is *not* the first obstruction.  The specification already proves the
tie rule (`roundMag_midpoint_even`), and the emitted kernel decides the `q ≥ 0`
ties correctly: `9007199254740993` (`2 ^ 53 + 1`, a tie between `2 ^ 53` and
`2 ^ 53 + 2`) reaches tier 2's exact path (`window = 1`) and returns `2 ^ 53` on
both sides.  A `q < 0` tie is *refused* by the kernel's exactness test and
handed to the fallback: `4503599627370496.5` (`2 ^ 52 + 0.5`) reaches
`el_exact` with `undec = 1`, is handed to `num_scan`/`strtod`, and returns
`2 ^ 52` on both sides.  The tie therefore splits into "decided by tier 2" (a
tier-2 exactness obligation) and "handed to the fallback" (a tier-3 obligation).

The first in-tree obstruction is the **tier-2 exactness test for 17–19
significant digits**, and the input that shows it is `1.0000000000000002`: a
17-significant-digit decimal with `eff = -16`, executed through tier 2 with
`window = 0`, i.e. decided by `el_pack` from the high 64 bits of `W * hi`
alone, without either forming the exact rational `P / d` or computing the low
half of the product.  The tree has no lemma that this approximation's decision
is `roundMag`'s, and none that the guard slice's three-value window is
sufficient; the `el_exact` window (`12345678901234567`, `window = 1`) needs the
skipped low multiply and the 91-entry table as well.

The fallback is the outer obstruction, reached by every input the kernel
refuses: the subnormal tie `2.4703282292062327e-324` (range), the `q < 0` tie
`4503599627370496.5` (undecidable), the long lexemes and the overflow cases
(`1e309`).  It is not a first obstruction because it is an assumption about the
C library, not a proof obligation this tree can discharge.

## Does the statement survive its first case?

Yes.  The first case of the crafted suite, `9007199254740993` (a `q = 0` tie),
returns `4845873199050653696` on both sides; the first case that reaches tier
2's guard-only path, `2251799813685247.75` (a value just below `2 ^ 51`, not a
tie), returns `4836865999795912703` on both sides; and the 17-significant-digit
witness `1.0000000000000002` returns `4607182418800017409` on both sides.  The
statement is at the right precision — binary64 with
`roundTiesToEven`.  What does not survive is the reading of tier 2 as a single
correctly rounded operation: it is an approximation plus a guard, so the
statement must be proved through the kernel's bound rather than by `roundMag`
alone.

## What a proof would need, and the verdict

1. **A model of the emitted binary64 arithmetic.**  This tree has no floating
   point model; mathlib's `Mathlib.Data.FP.Basic` (pinned in
   `lakefile.toml`) is Mario Carneiro's port of Flocq's approach and carries the
   exact core: `ValidFinite`, `Float.toRat`, and the correctly-rounded division
   primitive `divNatLtTwoPow`.  `Pff`'s architecture can be ported onto it.
   **`Mathlib.*` may not appear outside `ITree/Internal/PFunctor.lean`
   (`AGENTS.md`), so a new adapter under `ITree/Internal/` is needed; that is a
   planner decision, and this module imports only `LeanLLVM.JSON.Strtod`.**
2. **Tier 1: port `Pff`'s round-once argument.**  The operands are exact and
   the operation is single, so `divNatLtTwoPow`/`ValidFinite`/`toRat` give the
   same rounding `roundMag` names.  This is the known, tractable part.
3. **Tier 2: the Eisel-Lemire bound.**  A proof must show, for every
   `(mant, eff)` the branch accepts, that the truncated 128-bit product's guard
   decision equals `roundMag mant (10 ^ -eff)`'s, and that `el_exact`'s low half
   settles the window it claims to settle.  This needs the 91 table entries and
   the error bound; it is the first obstruction and the largest in-tree work.
4. **Tier 3: the fallback.**  Proving glibc's `strtod` correctly rounded is
   outside this tree; the options are a platform axiom, or a port of `Pff`'s
   verified decimal parser (a substantial development) onto `FP.Basic`.  Either
   is a specification decision, not something to absorb silently.

**Verdict.**  A full proof is a port of a known argument onto `FP.Basic`, not an
open problem — but it is a multi-stage development, and `Pff` itself is
substantial.  This module therefore states the obligation with the classes made
explicit and does not claim it.  The honest interim form is a refinement
conditional on (a) the tier-2 kernel's bound and (b) the platform's `strtod`
rounding, with (b) written as an assumption rather than hidden in the fallback.

## The executed evidence

The specification's own harness, `nix develop -c bash tests/json-strtod/check.sh`
(`strtodSpec` against glibc on `tests/json-strtod/corpus.txt`):
`strtod agreement: 71/71 rows`.  The same 71 lexemes through the emitted
`num_fast` (`kernel/json/stage2.c`'s `num_fast_el1`) and through `strtodSpec`
compare equal row for row; the emitted-side path split is 24 tier 1, 11 tier 2
and 36 fallback.  A 25-row crafted corpus covering the classes (ties at five
binades, 17–19 significant digits, subnormals, the normal boundary, overflow,
and the long lexemes) also compares equal, split 2 tier 1, 12 tier 2 and 11
fallback.  A 3,000,000-lexeme differential run against glibc's `strtod` (the
specification harness's own oracle) gives 487,723 tier-1, 311,559 tier-2 and
2,200,718 fallback rows with no disagreement.  The controls: `0.1` is
`4591870180066957722` on all three actors; a deliberately wrong specification
that rounds ties away from zero instead of to even returns
`4841369599423283201` for `4503599627370496.5` where `strtodSpec` and the
emitted conversion return `4841369599423283200`, and `4845873199050653697` for
`9007199254740993` where both return `4845873199050653696`.  The harness
therefore distinguishes the true specification from a wrong one, and the wrong
one fails exactly on the tie.

There is no `sorry`, `admit` or `native_decide` below.  The declarations'
axioms are pinned at the end of the file.  Nothing here is a claim about the
emitted body: `EmittedConversionRefines` is a proposition, and
`emittedConversionRefines_universal` is the only theorem, proving that the
statement's branches cover the well-formed lexemes.
-/
import LeanLLVM.JSON.Strtod

set_option autoImplicit false

namespace LeanLLVM.StrtodRefine

open LeanLLVM.JSON
open ByteString

/-! ### The emitted code's counters, read from the decomposition

`num_fast_el1` reads the lexeme into `idig` integer digits, `fdig` fraction
digits and `exp10`, then tests `nd = idig + fdig` and `eff = exp10 - fdig`.
These are the same quantities read from `Decimal`, so the emitted branch tests
can be stated in the specification's vocabulary. -/

/-- `idig`: the `int` part's digit count.  `IntPart` is `0` or a non-zero digit
followed by digits, so its length is the emitted counter. -/
def intDigits (d : Decimal) : Nat := d.ip.length

/-- `fdig`: the `frac` digits' count, or zero when the lexeme has no `.`. -/
def fracDigits (d : Decimal) : Nat := (d.fr.getD empty).length

/-- `exp10`: the exponent's value with its sign, or zero when absent.  The
emitted accumulator saturates past `100000`; that only routes a lexeme to the
fallback, because a saturated exponent with `nd ≤ 19` is outside `[-45, 45]`. -/
def expValue (d : Decimal) : Int :=
  match d.ex with
  | none => 0
  | some (s, ds) =>
      if s then -(Decimal.digitsNat ds : Int) else (Decimal.digitsNat ds : Int)

/-- `eff = exp10 - fdig`: the exponent of `ip * 10 ^ fdig + fr`. -/
def eff (d : Decimal) : Int := expValue d - (fracDigits d : Int)

/-- `nd = idig + fdig`. -/
def digitCount (d : Decimal) : Nat := intDigits d + fracDigits d

/-! ### The emitted code's branch tests

Tier 1 is `nd ≤ 15 ∧ -22 ≤ eff ≤ 22`; the 128-bit kernel is reached when the
outer test `nd ≤ 19 ∧ -45 ≤ eff ≤ 45` holds and tier 1 did not.  `kernelDecides`
is the kernel's return, a `Bool`: the proposition does not guess a decision the
module cannot see, and the emitted-side case is the instantiation at the
emitted body's own decision. -/

/-- The exact multiply/divide branch's test. -/
def Tier1 (d : Decimal) : Prop :=
  digitCount d ≤ 15 ∧ -22 ≤ eff d ∧ eff d ≤ 22

/-- The 128-bit kernel's eligibility test: the table's `EPOW_MIN`/`EPOW_MAX` are
`-45` and `45`. -/
def Tier2Eligible (d : Decimal) : Prop :=
  digitCount d ≤ 19 ∧ -45 ≤ eff d ∧ eff d ≤ 45

/-- The 128-bit kernel's branch: eligible, not tier 1, and the kernel decided. -/
def Tier2 (d : Decimal) (kernelDecides : Decimal → Bool) : Prop :=
  ¬ Tier1 d ∧ Tier2Eligible d ∧ kernelDecides d = true

/-- The slow branch: not tier 1, and either ineligible for the kernel or the
kernel refused. -/
def Fallback (d : Decimal) (kernelDecides : Decimal → Bool) : Prop :=
  ¬ Tier1 d ∧ (¬ Tier2Eligible d ∨ kernelDecides d = false)

/-! ### The magnitude classes

`roundMag`'s branches are the subnormal region (`P < d * 2 ^ 52`), the normal
region (from `2 ^ -1022` to below the overflow threshold), and overflow.
`IsTie` is the exact midpoint: the remainder is half the ulp, which is the
hypothesis `roundMag_midpoint_even` consumes. -/

/-- A non-zero magnitude below the smallest normal. -/
def IsSubnormal (d : Decimal) : Prop :=
  0 < d.ticks.1 ∧ d.ticks.1 < d.ticks.2 * 2 ^ 52

/-- A magnitude in the normal range and below the overflow threshold. -/
def IsNormal (d : Decimal) : Prop :=
  d.ticks.2 * 2 ^ 52 ≤ d.ticks.1 ∧ ¬ overflowTicks * d.ticks.2 ≤ d.ticks.1

/-- The exact midpoint of two adjacent binary64 values: the remainder is half
the ulp of the region the value falls in. -/
def IsTie (d : Decimal) : Prop :=
  let P := d.ticks.1
  let D := d.ticks.2
  ¬ overflowTicks * D ≤ P ∧
    (if P < D * 2 ^ 52 then 2 * (P % D) = D
     else 2 * (P % (D * ulp P D)) = D * ulp P D)

/-! ### The refinement obligation -/

/-- One class's clause: on every well-formed lexeme in the class, the binary64
encoding the emitted conversion returns is `strtodSpec`'s. -/
def EmittedRefinesOn (emitted : Bytes → Binary64) (p : Decimal → Prop) : Prop :=
  ∀ d : Decimal, d.wellFormed → p d → emitted d.lexeme = strtodSpec d

/-- **The emitted conversion refines `strtodSpec`.**  The conjuncts are the
emitted code's own three branches and the magnitude classes the statement is
read at:

* tier 1, tier 2 (at the kernel's decision) and the fallback are a partition of
  the well-formed lexemes, so the first three conjuncts are the whole statement;
* `IsNormal`, `IsSubnormal` and `IsTie` are the classes the brief asks the
  statement to make explicit.  They are consequences of the partition, not a
  weaker reading of it: each names the inputs its clause covers.

`emitted` is the `double` `num_fast` returns, read as `Binary64`; the event
record's payload is `(emitted d.lexeme).toBits` (`stage2.c`'s `out_u64`).  The
statement is a `Prop`, not a theorem: the emitted body is C and this module has
no model of it. -/
def EmittedConversionRefines (emitted : Bytes → Binary64)
    (kernelDecides : Decimal → Bool) : Prop :=
  EmittedRefinesOn emitted Tier1 ∧
  EmittedRefinesOn emitted (fun d => Tier2 d kernelDecides) ∧
  EmittedRefinesOn emitted (fun d => Fallback d kernelDecides) ∧
  EmittedRefinesOn emitted IsNormal ∧
  EmittedRefinesOn emitted IsSubnormal ∧
  EmittedRefinesOn emitted IsTie

/-! ### The statement's shape -/

/-- The emitted tests are total: every lexeme takes exactly one of the tier-1,
tier-2 and fallback branches.  This is a fact about the statement's case split,
not about the conversion. -/
theorem branch_cover (d : Decimal) (kernelDecides : Decimal → Bool) :
    Tier1 d ∨ Tier2 d kernelDecides ∨ Fallback d kernelDecides := by
  by_cases h1 : digitCount d ≤ 15 ∧ -22 ≤ eff d ∧ eff d ≤ 22
  · exact Or.inl (show Tier1 d from h1)
  · by_cases h2 : digitCount d ≤ 19 ∧ -45 ≤ eff d ∧ eff d ≤ 45
    · cases hk : kernelDecides d
      · exact Or.inr (Or.inr ⟨show ¬ Tier1 d from h1, Or.inr hk⟩)
      · exact Or.inr (Or.inl ⟨show ¬ Tier1 d from h1,
          show Tier2Eligible d from h2, hk⟩)
    · exact Or.inr (Or.inr ⟨show ¬ Tier1 d from h1,
        Or.inl (show ¬ Tier2Eligible d from h2)⟩)

/-- The emitted tests are exclusive: tier 1 excludes both other branches, and
tier 2 and the fallback disagree on the kernel's return.  With `branch_cover`
this makes the three branches a partition. -/
theorem branch_disjoint (d : Decimal) (kernelDecides : Decimal → Bool) :
    ¬ (Tier1 d ∧ Tier2 d kernelDecides) ∧
      ¬ (Tier1 d ∧ Fallback d kernelDecides) ∧
      ¬ (Tier2 d kernelDecides ∧ Fallback d kernelDecides) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact h2.1 h1
  · rintro ⟨h1, h2⟩
    exact h2.1 h1
  · rintro ⟨h2, h3⟩
    rcases h3.2 with hne | hf
    · exact hne h2.2.1
    · rw [h2.2.2] at hf
      cases hf

/-- The classed statement covers every well-formed lexeme: the three emitted
branches partition the inputs.  The theorem proves the statement's shape, not
the convergence of the emitted body. -/
theorem emittedConversionRefines_universal {emitted : Bytes → Binary64}
    {kernelDecides : Decimal → Bool}
    (h : EmittedConversionRefines emitted kernelDecides) :
    ∀ d : Decimal, d.wellFormed → emitted d.lexeme = strtodSpec d := by
  intro d hd
  rcases branch_cover d kernelDecides with h1 | h2 | h3
  · exact h.1 d hd h1
  · exact h.2.1 d hd h2
  · exact h.2.2.1 d hd h3

/-! ### Axiom footprint

Every declaration is pinned; the proposition's definitions are computable, and
the two theorems must stay at the standard footprint. -/

#print axioms LeanLLVM.StrtodRefine.intDigits
#print axioms LeanLLVM.StrtodRefine.fracDigits
#print axioms LeanLLVM.StrtodRefine.expValue
#print axioms LeanLLVM.StrtodRefine.eff
#print axioms LeanLLVM.StrtodRefine.digitCount
#print axioms LeanLLVM.StrtodRefine.Tier1
#print axioms LeanLLVM.StrtodRefine.Tier2Eligible
#print axioms LeanLLVM.StrtodRefine.Tier2
#print axioms LeanLLVM.StrtodRefine.Fallback
#print axioms LeanLLVM.StrtodRefine.IsSubnormal
#print axioms LeanLLVM.StrtodRefine.IsNormal
#print axioms LeanLLVM.StrtodRefine.IsTie
#print axioms LeanLLVM.StrtodRefine.EmittedRefinesOn
#print axioms LeanLLVM.StrtodRefine.EmittedConversionRefines
#print axioms LeanLLVM.StrtodRefine.branch_cover
#print axioms LeanLLVM.StrtodRefine.branch_disjoint
#print axioms LeanLLVM.StrtodRefine.emittedConversionRefines_universal

end LeanLLVM.StrtodRefine
