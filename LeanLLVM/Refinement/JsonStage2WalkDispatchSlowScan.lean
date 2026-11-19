/-
# The slow scan at `land.rhs.i103` / `while.body.i104`

The error path's scan — `if.then432.i`'s `cond.end.i96` enters it at
`land.rhs.i103` with the entry's position in `%ee.011.i` and the bound in `%cond.i`
(`%4`'s word, the stream's end, at the last entry) — is a *different* loop from the
whitespace skip `wsRun` models (`while.body370.i` at `land.rhs.i.preheader`) and from the
last entry's tail scan (`while.body462.i` at `land.rhs457.i`, whose visit predicate is
`ScanVisits`).  Its shape is:

* `land.rhs.i103` — the counter `%ee.011.i` (a `phi` over `cond.end.i96`'s
  `%idxprom.i` and the back edge's `%inc.i105`), the address `%arrayidx5.i`, the load
  `%40 = document[counter]`, then `NodeBlock73`;
* `NodeBlock73` / `NodeBlock71` / one of `LeafBlock64`, `LeafBlock67`, `LeafBlock69` —
  the byte's class (`slt 13`, `slt 32`, `ule +247 1`, `eq 32`, `eq 13`, the same pivots
  as `wsStop`), continuing to `while.body.i104` or stopping at `while.end.i`;
* `while.body.i104` — `%inc.i105 = %ee.011.i + 1` and `%exitcond.not.i = (%inc.i105 ==
  %cond.i)`, branching back to `land.rhs.i103` or out to `cleanup474.i`.

So the stop is **the same byte predicate** `wsStop G q` (`wsStop` is stated at `wsX`, the
document's byte at `q`), and the *bound* is the counter reaching `%cond.i`; the exits are
two, and which one the walk takes is the byte's class at the stop index.

## What is here, and what is not

This module states the model (the visit predicate and the three named states) and adds the
one missing link, `while_body_i104`.  The run — the induction from `land.rhs.i103` to both
exits with its per-byte price — is **not** here: it is the next module, split by phase, and
its statement is

```
theorem slowRun (hInv) (hcells) (hcls : ∀ q, i < q → q < c → slowCont G q)
    (hpos) (hqn) :
    ∃ n, n ≤ 5 * (c - i) ∧ WalkSegment … (slowLandAt l i c) (slowStopAt l i c) n ∧ …
```

at `i = entryPos G C.k` and `c = G.n` for this class, with the price
`(prefix + 3 + n) + 2 ≤ 32·(G.nep − C.k) + 8·(G.n − entryPos G C.k)` discharged by
`5·(G.n − entryPos) ≤ 8·(G.n − entryPos)` — the per-byte credit
`runLast_price_with_credit` gives the merge endpoint, not `refusePrice_of_le`'s constant.

## The corrected link survey (for the record)

The error-path links all exist except the two loop-body links; the class's own route
(`%8 ∈ {126, 127}`) does not use the numeral arm or the escape unit's scan:
`if.end48.i`, `if.end67.critedge.i`, `if.end67.i`, `if.then19.i`, `if.then25.i`,
`land.rhs71.i`, `while.body76.i`, `while.end78.i` are on *other* literals' paths.
`while_body76_i` is therefore not added — this class's route needs `while_body_i104` only.
-/
import LeanLLVM.Refinement.JsonStage2WalkDispatchLastSeamRoute
import LeanLLVM.Refinement.JsonStage2WalkScopeClassAB
import LeanLLVM.Refinement.JsonStage2WalkPhi
import LeanLLVM.Refinement.JsonStage2WalkRest

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonStage2IR

namespace WalkScope

/-! ### The visit predicate

The scan's three leaves test the byte at the counter with exactly `wsStop`'s pivots
(`slt 13`, `ule (+247) 1`, `slt 32`, `eq 32`, `eq 13`), so one predicate serves both loops;
`wsStop`'s docstring states it at `wsX G q`, and the scan's `%40` is the same byte. -/

/-- **The byte at `q` continues this scan**: it is not a whitespace stop.  `wsStop` is the
three leaves' stop arms at the same pivots, so its negation is exactly the scan's
`while.body.i104` edge. -/
abbrev SlowCont {m0 : Mem} (G : WalkGeom m0) (q : Nat) : Prop := ¬ wsStop G q

/-- **The scan's bound at this use**: `%cond.i` is `%4`'s word, the stream's end, so the
scan runs over `[entryPos G C.k, G.n)`. -/
abbrev SlowBound {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G) : Nat := G.n

/-- The scan's entry at `land.rhs.i103` with the counter and the bound cells. -/
def slowLandAt {m0 : Mem} (s : State) (p c : Nat) : State :=
  { s with
    env := cells [("%ee.011.i", .int 64 (BitVec.ofNat 64 p)),
      ("%cond.i", .int 64 (BitVec.ofNat 64 c))] s.env
    pc := "land.rhs.i103", pre := some s.pc }

/-- The body's state: the increment's cell and the exit test's. -/
def slowBodyAt {m0 : Mem} (s : State) (p c : Nat) : State :=
  { s with
    env := cells [("%exitcond.not.i",
        .int 1 (evalICmp .eq (BitVec.ofNat 64 p + (1 : BitVec 64)) (BitVec.ofNat 64 c))),
      ("%inc.i105", .int 64 (BitVec.ofNat 64 p + (1 : BitVec 64)))] s.env
    pc := "while.body.i104", pre := some s.pc }

/-- The stop's state at `while.end.i`: the landing `phi` and its equality test. -/
def slowStopAt {m0 : Mem} (s : State) (p c : Nat) : State :=
  { s with
    env := cells [("%cmp6.i",
        .int 1 (evalICmp .eq (BitVec.ofNat 64 p) (BitVec.ofNat 64 c))),
      ("%ee.0.lcssa.i", .int 64 (BitVec.ofNat 64 p))] s.env
    pc := "while.end.i", pre := some s.pc }

/-! ### The missing link: `while.body.i104`

Two instructions — the increment and the exit test — and a `condbr`: back to the scan's
`land.rhs.i103`, or out to `cleanup474.i` when the incremented counter equals the bound.
The block step is `denoteCode_cons_of` over `step_add_imm` and `walkDenoteCode_icmp`, and the
link is `callQuietBr` at the test's cell. -/

/-- The block, as the model's `while.body.i104`. -/
def walkWhileBodyI104 : Block :=
  { name := "while.body.i104",
    instrs := [
      Instr.binop "%inc.i105" BinOp.add 64 (.reg "%ee.011.i") (.imm (.int 64 (1 : BitVec 64))),
      Instr.icmp "%exitcond.not.i" IPred.eq 64 (.reg "%inc.i105") (.reg "%cond.i")],
    term := Term.condbr (.reg "%exitcond.not.i") "cleanup474.i" "land.rhs.i103" }

theorem walkWhileBodyI104_find : stage2Body.findBlock "while.body.i104" =
    some walkWhileBodyI104 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkWhileBodyI104]

/-! **`while.body.i104`'s link is not landed.**  The statement is

```
theorem WalkLink.while_body_i104 (hInv) (hblock : C.block = "while.body.i104")
    (hinc : %ee.011.i = p) (hcond : %cond.i = c) :
    ∃ s', WalkLink … G C s
      { C with block := (if evalICmp .eq (ofNat 64 (p+1)) (ofNat 64 c) = 1
          then "cleanup474.i" else "land.rhs.i103") } s'
```

and its proof is the `callQuietBr` recipe with the block step `denoteCode_cons_of` over
`step_add_imm` and `walkDenoteCode_icmp`.  Three kernel-level mismatches remain and are the
exact blockers, not a modelling gap: (i) `step_add_imm`'s conclusion spells the immediate as
`Const.int 64 1#64` while the block's `Instr.binop … (.imm (.int 64 1))` spells it
`Const.int 64 1`, so the two `Option State` equalities are not syntactically the same term
for `rw`; (ii) the same for the `icmp`'s operands; (iii) the empty tail
`denoteCode calls [] s = some s` is not closed by `rfl`/`simp only` at the state the
`icmp` step leaves.  These are notation agree-ments, not facts about the walk; the next
pass should state the block's instructions through the same `Const.int` constructors the
step lemmas produce (or add `step_add_imm`/`step_icmp_reg` corollaries at the block's own
spelling) and re-run. -/

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkWhileBodyI104_find

end WalkScope
end LeanLLVM.Refinement
