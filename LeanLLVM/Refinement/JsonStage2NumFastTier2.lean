/-
The tier-2 bridge: the body's `num_el_el1` model and the guard's decision.

`JsonStage2NumFastCalls` supplies `numElEl1` — the callee's model, with the
`EPOW` table as a parameter — while `LeanLLVM.ElGuardRefine.elTier2Code` is the
guard's own decision over the emitted table, and `elGuardRefinesOn` proves that
decision is `roundMag`'s on sixty-four-bit mantissas.  What was owed is the
correspondence between the two *models*: the same C text, written twice in two
namespaces (`LeanLLVM.Refinement.EPow` here, `LeanLLVM.ElGuardRefine.EPow`
there), and no lemma relating their `el_pack`/`el_exact` forms.

**The model's low-word wrap.**  Reading the correspondence first found a defect
in the model, not only a missing lemma.  `el_exact`'s two additions are
`uint64_t` in the emitted code: `Rlo = Alo + c` wraps and the carry is
`Rlo < Alo` on the wrapped word, and `Rhi` carries it into another sixty-four-bit
word.  The model's `Rlo`/`Rhi` were *unreduced* naturals.  At
`(w, q) = (34, -36)` — one of `ElGuardRefine.witnesses`, the very inputs the
guard's check prints — the unwrapped sum is `18870555535664931523 ≥ 2 ^ 64`, the
unwrapped reading sees `hp = 511 = hh - 1` and rounds down, and the emitted
kernel (and `elTier2Code`) sees `hp = 512 = hh` and rounds up: `…961` against
`…962`.  `JsonStage2NumFastCalls.elExact` now reduces both words modulo
`2 ^ 64`, which is what the C does and what `elTier2Code` computes.

**What this module states.**  `guardTable` is the body's table taken from the
guard's rows, and `NumFastElAgrees` is the bridge: on every `(w, q)`,
`numElEl1 guardTable w q` is `elTier2Code w q`'s encoding bits.  The general
proof is not in this tree — it is the remaining obligation — but the statement
is fixed here, the written words now agree, and the check below discharges it at
the guard's own witness set.

**Axiom footprints** are at the end.
-/
import LeanLLVM.Refinement.JsonStage2NumFastCalls
import LeanLLVM.ElGuardRefine

set_option autoImplicit false
set_option maxRecDepth 20000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement

/-! ### The two tables

The body's `EPow` and the guard's are the same three fields under different
namespaces; `ofGuard` carries a guard row to the model's type, and `guardTable`
is the model's table read from the guard's own rows. -/

/-- A guard row as the model's row. -/
def EPow.ofGuard (t : LeanLLVM.ElGuardRefine.EPow) : EPow :=
  ⟨t.hi, t.lo, t.e⟩

/-- The body's table, taken from the guard's rows. -/
def guardTable : Int → Option EPow :=
  fun q => (LeanLLVM.ElGuardRefine.epowAt q).map EPow.ofGuard

/-- The encoding's bits, as the emitted kernel's `out_u64` carries them. -/
abbrev tier2Bits (c : LeanLLVM.Code) : Nat :=
  LeanLLVM.ElGuardRefine.codeBits c

/-! ### The bridge

The obligation: everywhere the model decides, its word is the guard's encoding.
The model's range gate (`none` outside `-45 … 45`), its zero mantissa
(`some 0`), its window and its `el_pack` all have a counterpart in
`elTier2Code`; the statement below is what a proof must close. -/

/-- **The tier-2 bridge.**  On every mantissa `w` and exponent `q`, the model's
decision is the guard's encoding bits.  Stated, not proved: the arithmetic
correspondence (the window's `Bool` form, `el_exact`'s two-word carries and
`el_pack`'s bit pattern) is the open obligation this module records. -/
def NumFastElAgrees : Prop :=
  ∀ (w : Nat) (q : Int),
    numElEl1 guardTable w q = (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits

/-! ### The check at the guard's witnesses

The guard's own test set is `ElGuardRefine.witnesses`; the model and the guard
decide the same bits at every one of them.  This is a `decide`-checked theorem,
not an evaluation, so a regression in either model fails the build. -/

set_option exponentiation.threshold 2200 in
set_option maxRecDepth 20000 in
/-- **The bridge at the guard's witnesses.**  `numElEl1 guardTable` and
`elTier2Code`'s bits are equal at each of `ElGuardRefine.witnesses`, including
the two 15- and 16-digit rows the guard's window alone would decide the other
way. -/
theorem numElEl1_witnesses :
    (LeanLLVM.ElGuardRefine.witnesses.all (fun (w, q) =>
      decide (numElEl1 guardTable w q
        = (LeanLLVM.ElGuardRefine.elTier2Code w q).map tier2Bits))) = true := by
  decide

/-! ### Why the wrap is load-bearing

The pre-fix model is not in the tree, so the record of the defect is a theorem
about its arithmetic: at `(34, -36)` the low sum is at least `2 ^ 64`, so an
unreduced low word is not the emitted word, and the wrapped model is the one
that decides with the guard. -/

/-- The exponent `-45 … 45` table's row for `q`, as the model's row. -/
def rowAt (q : Int) : Option EPow := guardTable q

/-- The emitted row at `-36`, whose low sum overflows at `w = 34`. -/
theorem rowAt_neg36 :
    (rowAt (-36)).map (fun t => (t.hi, t.lo, t.e))
      = some (12259964326927110866, 15989199047912110569, -247) := by
  decide

/-- The low-word sum at `(34, -36)`, before the emitted wrap, is at least
`2 ^ 64`; that is the input where the unwrapped reading rounds down and the
wrapped one rounds up. -/
theorem low_sum_overflows_at_34_neg36 :
    2 ^ 64 ≤
      (34 * 2 ^ (64 - (34 : Nat).size) * 12259964326927110866) % 2 ^ 64 +
        (34 * 2 ^ (64 - (34 : Nat).size) * 15989199047912110569) / 2 ^ 64 := by
  decide

/-- **The wrapped model is the guard's at that input.**  The model and the guard
return the same bits at `(34, -36)`, which the unwrapped reading does not
(the reading is recorded in `JsonStage2NumFastCalls.elExact`'s docstring). -/
theorem numElEl1_34_neg36 :
    numElEl1 guardTable 34 (-36)
      = (LeanLLVM.ElGuardRefine.elTier2Code 34 (-36)).map tier2Bits := by
  decide

/-! ### Axiom footprints -/



#print axioms numElEl1_witnesses



#print axioms low_sum_overflows_at_34_neg36



#print axioms numElEl1_34_neg36

end LeanLLVM.Refinement
