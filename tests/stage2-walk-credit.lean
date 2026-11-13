/-
The revolution's credit, measured — and the dispatch's pivots, executed.

`walkPotential` charges one entry allowance per entry not yet dispatched and one
byte allowance per document byte not yet reached, so it *falls* as the walk
consumes them; a revolution's price is bounded by the credit it consumes
(`walkPotential_spend`), never by the credit that remains.  This file holds the
counted rows the change is stated at, the negative control that shows the form it
replaced fails at every one of them, and a step of the pinned body's dispatch: the
binary search's first two pivots are stepped on `stage2Body` itself, at bytes that
select each edge — so the check runs the dispatch's own control flow, not only the
arithmetic.

What it does not do is run a whole revolution: that is `WalkDispatch`, and its
counted run is the price premise this change states in the credit's form.

Run: `nix develop -c lake env lean tests/stage2-walk-credit.lean`.
-/
import LeanLLVM.Refinement.JsonStage2WalkAssembly

set_option maxRecDepth 8000

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.WalkScope

namespace Stage2WalkCredit

/-- The dispatch's counted price fits the credit it consumes at every entry width:
twenty-two blocks and six per byte against thirty-two and eight. -/
example (b : Nat) : 22 + 6 * b + 2 ≤ 32 + 8 * b := by omega

/-- The rows this change is stated at: `(scenario, blocks the dispatch traverses,
bytes the entry spans)`.  A hundred-byte string body, one whose bytes are all
escape positions (the escape scan visits each), a whitespace-heavy entry, a
refusal reached late (four blocks more, the store's chain), and the last entry's
exit (its dispatch plus the finalisation's five). -/
def rows : List (String × Nat × Nat) :=
  [("long string", 22 + 6 * 100, 100),
   ("escaped string", 22 + 6 * 96, 96),
   ("whitespace-heavy", 22 + 6 * 80, 80),
   ("malformed late", 22 + 6 * 64 + 4, 64),
   ("the last entry's exit", 22 + 6 * 100 + 5, 100)]

/-- The credit form's row test: `p ≤ 32·Δk + 8·ΔA` at `Δk = 1`. -/
def creditOk (r : String × Nat × Nat) : Bool := r.2.1 + 2 ≤ 32 + 8 * r.2.2

#guard rows.all creditOk

/-- The form the credit replaced: the price had to fit inside `32` *after* the
newly decoded bytes were charged. -/
def oldOk (r : String × Nat × Nat) : Bool := r.2.1 + 2 + 8 * r.2.2 ≤ 32

-- No row fits it — the premise had no producer, which is the defect.
#guard !rows.any oldOk

/-- A `Calls` that answers nothing: the pivot blocks call no helper, so a run
through them never asks. -/
def noCalls : Calls := fun _ _ _ _ => none

/-- The block a step enters, if it jumps. -/
def pcOf : Ctrl → Option String
  | .jump s => some s.pc
  | _ => none

/-- `NodeBlock21` at `{` (`91`): `%8 < 91` is false, so the dispatch leaves for
`NodeBlock19`. -/
def pivot22 : State :=
  { env := [("%8", .int 8 (91 : BitVec 8))], mem := [], next := 0,
    pc := "NodeBlock21", pre := none }

/-- `NodeBlock19` at the same byte: `%8 < 123` is true, so `NodeBlock11`. -/
def pivot20 : State :=
  { pivot22 with
    env := [("%Pivot22", .int 1 (0 : BitVec 1)), ("%8", .int 8 (91 : BitVec 8))],
    pc := "NodeBlock19", pre := some "NodeBlock21" }

-- The dispatch's first pivot, executed on the pinned body.
#guard pcOf (step noCalls stage2Body pivot22) == some "NodeBlock19"

-- And the second, at the bit the first selected.
#guard pcOf (step noCalls stage2Body pivot20) == some "NodeBlock11"

/-- The byte `123`, the middle of the switch's `{`/`}` interval. -/
def brace123 : State :=
  { env := [("%8", .int 8 (123 : BitVec 8))], mem := [], next := 0,
    pc := "NodeBlock17", pre := some "NodeBlock19" }

-- `123 < 125` is true, so the third pivot leaves for the leaf that compares it.
#guard pcOf (step noCalls stage2Body brace123) == some "LeafBlock13"

end Stage2WalkCredit
