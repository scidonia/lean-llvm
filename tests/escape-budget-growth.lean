/-
The expander's budget growth, measured.

`escapeExpandBudget` gained one summand when the entry stage became two-armed: the
walk's latch is reached only through a position, so the entry performs one
iteration **before** the loop's counter admits it, and a four-stage value was not a
stronger claim but an unattainable one.  The check this file runs is that the growth
is *exactly* that named stage: the new value minus the value it replaced is
`decodeIterCost n` at every argument list, with nothing left over.

That subtraction is the whole content of the decision.  A growth that carried any
margin would be the budget grown by convenience rather than by a stage the body
performs, and the difference is what tells the two apart — so it is measured here
rather than argued in a docstring.

The four-stage value is restated in this file because the change under test is what
replaced it; the library carries only the current definition.

Run: `nix develop -c lake env lean tests/escape-budget-growth.lean`.
-/
import LeanLLVM.Refinement.JsonEscapeDecodeRun

set_option maxRecDepth 8000

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonEscapeIR

namespace EscapeBudgetGrowth

/-- The four-stage value this change replaced: the same summands with the entry's
iteration left out. -/
def fourStage (n nps : Nat) : Nat :=
  (nps + 1) * 3 + decodeWalkFuel nps n + (n / 64 + 3) + 4

/-- The record's argument list at a body length and a position count. -/
def args (n nps : Nat) : List Value :=
  [.ptr 0, .int 64 (BitVec.ofNat 64 n), .ptr 0, .ptr 0, .ptr 0, .ptr 0,
   .int 64 (BitVec.ofNat 64 nps), .int 64 0, .ptr 0]

/-- The rows: the empty body, the smallest non-empty ones, the copy's block
boundary, and two lengths past it, at several position counts. -/
def rows : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 9), (1, 0), (1, 1), (63, 0), (64, 0), (65, 0),
   (127, 1), (128, 2), (129, 5), (1048576, 3)]

/-- The growth is one named stage at every row. -/
def growthOk (p : Nat × Nat) : Bool :=
  escapeExpandBudget (args p.1 p.2) [] == fourStage p.1 p.2 + decodeIterCost p.1

/-- The difference, spelled out: new minus old, beside `decodeIterCost n`. -/
def differences : List (Nat × Nat × Nat × Nat × Nat) :=
  rows.map fun p =>
    (p.1, p.2, escapeExpandBudget (args p.1 p.2) [], fourStage p.1 p.2, decodeIterCost p.1)

-- No row grows by anything other than the entry's iteration.
#guard rows.all growthOk

-- The same difference at every position count, so the growth is not per position.
#guard (rows.filter fun p => p.1 == 65).map (fun p =>
  escapeExpandBudget (args p.1 p.2) [] - fourStage p.1 p.2) ==
  (rows.filter fun p => p.1 == 65).map (fun p => decodeIterCost p.1)

-- The rows, as (n, nps, new, old, difference).
#eval differences

end EscapeBudgetGrowth
