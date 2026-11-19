/-
# The traversal's row: a document fact, and the field it produces

`HcontPayload.trav` (`JsonStage2WalkDispatchSupply`) is the last unproduced group of the
continuing payload:

```
  visits : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
    C.k + 1 < G.nep → ScanVisits G (entryPos G (C.k + 1)) (entryPos G C.k)
```

`ScanVisits G c i` (`JsonStage2WalkDispatchRunOfStaging`) is a `∀` over the extra-token
scan's states, and its `∃` carries the visited byte's *class*: the byte the latch reads at
`%47` is `< 13` and `(%47 + 247) ≤ 1` — a `9` or `10`.  So the field reduces
(`hcontTrav_visits_of_class`, `JsonStage2WalkDispatchAbiOfInv`) to one row about the
document: **every index the scan visits — every `j` with
`entryPos G C.k < j < entryPos G (C.k + 1)` — reads a `9` or `10` byte**.

## It is the document's content, not a consequence of the geometry

`WalkGeom` fixes no interior byte: `doc` is a read (`readBytes m0 G.b n = some bs`), and
`entries`/`order`/`inside` name *positions*, not values.  A document whose continuing
token has a non-whitespace interior — a multi-byte number, a string with a space in it —
satisfies every clause and fails the row.  So there is **no `∀ G` theorem** producing it,
and it cannot be assumed: it is the document-content supply that sits beside the payload.

## What this module states, and what carries it

* `ScanVisitsDoc` — the row, at the document (`G.bs.getD`), and only over the interior
  indices.  This is the supply's statement.
* `scanVisitsDoc_bits` / `hcontTravVisits_of_doc` — the row implies the byte-class bits
  every visit needs, and hence the field (`ScanVisits`), through
  `hcontTrav_visits_of_class`.  These are the producer target: the tree supports the
  *reduction* to this row, not a producer of the row.
* **The consumer.**  In the tree, `HcontTrav.visits` is held only as `HcontPayload.trav`,
  and no theorem reads it yet.  The run class's traversal is stated inside its bundle, as
  `HcontFacts`' two premises `hround`/`hbyte` that `hcontFacts_of_staging` produces — a
  different `∀`, not this field.  So the payload's supplier is what must
  carry `ScanVisitsDoc`; a future consumer of `HcontPayload.trav` takes it from there, not
  from `WalkInv`.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchAbiOfInv
import LeanLLVM.Refinement.JsonStage2WalkDispatchRunOfStaging

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-- **The traversal's document row.**  Every byte strictly between this entry's position
and the next entry's is a space (`9`) or a newline (`10`): those are exactly the indices
the extra-token scan visits, and the class the scan's latch needs at each visit.  Nothing
in `WalkGeom` implies it (it fixes positions, not values), so this is the payload's
document-content supply. -/
def ScanVisitsDoc {m0 : Mem} (G : WalkGeom m0) (c i : Nat) : Prop :=
  ∀ j, i < j → j < c → G.bs.getD j 0 = 9 ∨ G.bs.getD j 0 = 10

/-- **The row, as the scan's byte-class bits.**  A visited byte that is `9` or `10` gives
the latch's two comparisons their value: `< 13` and `(+ 247) ≤ 1`. -/
theorem scanVisitsDoc_bits {m0 : Mem} {G : WalkGeom m0} {c i : Nat}
    (h : ScanVisitsDoc G c i) :
    ∀ p, i < p + 1 → p + 1 < c →
      evalICmp .slt (wsX G (p + 1)) (BitVec.ofNat 8 13) = 1 ∧
        evalICmp .ule (wsX G (p + 1) + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 := by
  intro p h1 h2
  rcases h (p + 1) h1 h2 with hb | hb
  · rw [wsX, wsByte, hb]
    decide
  · rw [wsX, wsByte, hb]
    decide

/-- **The field, from its document row.**  This is the producer target the tree supports:
`HcontTrav.visits` follows from `ScanVisitsDoc` at the entry's own span, by
`hcontTrav_visits_of_class` (`JsonStage2WalkDispatchAbiOfInv`).  The row itself is the
supply; a `∀ G` theorem cannot produce it. -/
theorem hcontTravVisits_of_doc {m0 : Mem} (G : WalkGeom m0)
    (h : ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep →
      ScanVisitsDoc G (entryPos G (C.k + 1)) (entryPos G C.k)) :
    ∀ (C : WalkCarry G) (s : State), WalkInv G C s → C.block = walkLoopHead →
      C.k + 1 < G.nep → ScanVisits G (entryPos G (C.k + 1)) (entryPos G C.k) :=
  hcontTrav_visits_of_class G (fun C s hInv hblock hk p h1 h2 =>
    scanVisitsDoc_bits (h C s hInv hblock hk) p h1 h2)

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.scanVisitsDoc_bits
#print axioms LeanLLVM.Refinement.WalkScope.hcontTravVisits_of_doc

end WalkScope
end LeanLLVM.Refinement
