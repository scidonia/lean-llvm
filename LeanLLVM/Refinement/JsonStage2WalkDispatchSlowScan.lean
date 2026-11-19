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
one missing link, `while_body_i104`.  The link needed a vocabulary addition first:
`land.rhs.i103`'s `WalkLocal` now carries `ScanEmpty`, because the latch's bound exit
branches out of the loop and a condbr link must supply the untaken arm's `WalkLocal`
(`WalkLocal`, `JsonStage2WalkScopeGeom`, and `WalkLocal.stringScanLanded`,
`JsonStage2WalkScopeArms`, say why).  The run — the induction from `land.rhs.i103` to
both exits with its per-byte price — is **not** here: it is the next module, split by
phase, and its statement is

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
      Instr.binop "%inc.i105" BinOp.add 64 (.reg "%ee.011.i") (.imm (.int 64 (BitVec.ofNat 64 1))),
      Instr.icmp "%exitcond.not.i" IPred.eq 64 (.reg "%inc.i105") (.reg "%cond.i")],
    term := Term.condbr (.reg "%exitcond.not.i") "cleanup474.i" "land.rhs.i103" }

theorem walkWhileBodyI104_find : stage2Body.findBlock "while.body.i104" =
    some walkWhileBodyI104 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkWhileBodyI104]

/-- **`while.body.i104`'s link**: the scan's back edge and its bound exit.  The block's
two instructions are stated at the `Const.int` spelling the step lemmas produce, so the
block step is one `rw` chain, and the link is `callQuietBr` at `%exitcond.not.i`.  The two
arm facts are the caller's: on the continuing visit the landing's clause is `ScanLanded`
with the budget `c - (p + 1) ≤ C.inner`; on the bound visit it is `ScanEmpty`
(`%inc.i105 = %cond.i`), which is why the landing's clause carries that third disjunct. -/
theorem WalkLink.while_body_i104 {m0 : Mem} (G : WalkGeom m0) (C : WalkCarry G)
    (s : State) (hInv : WalkInv G C s) (hblock : C.block = "while.body.i104") {p c : Nat}
    (hinc : lookupName s.env "%ee.011.i" = some (.int 64 (BitVec.ofNat 64 p)))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hl : WalkLocal { C with block := "cleanup474.i" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s with
        pc := "cleanup474.i", pre := some s.pc })
    (hf : WalkLocal { C with block := "land.rhs.i103" }
      { stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s with
        pc := "land.rhs.i103", pre := some s.pc }) :
    ∃ s', WalkLink (stage2Calls stage2SubCalls) G C s
      { C with block := (if evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
          (BitVec.ofNat 64 c) = 1 then "cleanup474.i" else "land.rhs.i103") } s' := by
  have hinc' : lookupName (("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))
      :: s.env) "%inc.i105" =
      some (.int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :=
    lookupName_cons_self _ _ _
  have hcond' : lookupName (("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))
      :: s.env) "%cond.i" = some (.int 64 (BitVec.ofNat 64 c)) :=
    (lookupName_cons_ne _ _ (by decide)).trans hcond
  have hstep : denoteCode (stage2Calls stage2SubCalls) walkWhileBodyI104.instrs
      (stateAt s.env s) =
      some (stateAt (("%exitcond.not.i",
          .int 1 (evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1)
            (BitVec.ofNat 64 c))) ::
        ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env) s) := by
    simp only [walkWhileBodyI104]
    rw [denoteCode_cons_of (calls := stage2Calls stage2SubCalls)
      (i := Instr.binop "%inc.i105" BinOp.add 64 (.reg "%ee.011.i")
        (.imm (.int 64 (BitVec.ofNat 64 1))))
      (is := [Instr.icmp "%exitcond.not.i" IPred.eq 64 (.reg "%inc.i105") (.reg "%cond.i")])
      (s := stateAt s.env s)
      (s' := stateAt (("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1))
        :: s.env) s)
      (step_add_imm (calls := stage2Calls stage2SubCalls) s.env s "%inc.i105" "%ee.011.i"
        (x := BitVec.ofNat 64 p) (c := BitVec.ofNat 64 1) hinc)]
    rw [walkDenoteCode_icmp (calls := stage2Calls stage2SubCalls)
      (env := ("%inc.i105", .int 64 (BitVec.ofNat 64 p + BitVec.ofNat 64 1)) :: s.env)
      (s := s) (d := "%exitcond.not.i") (w := 64) (p := IPred.eq)
      (oa := .reg "%inc.i105") (ob := .reg "%cond.i")
      (x := BitVec.ofNat 64 p + BitVec.ofNat 64 1) (y := BitVec.ofNat 64 c)
      (ha := evalOperand_reg_of _ _ _ _ hinc')
      (hb := evalOperand_reg_of _ _ _ _ hcond') (is := [])]
    rfl
  exact WalkLink.callQuietBr (G := G) (C := C) (s := s) hInv
    (B := walkWhileBodyI104) (by rw [hblock]; exact walkWhileBodyI104_find)
    hstep (by unfold walkCarried; decide) rfl hInv.next_ge hInv.frame hInv.owned
    hInv.root_slot (fun _ _ _ => rfl) rfl
    (TM := C.tyMap) (SM := C.stMap)
    (by simpa only [stateAt] using hInv.tyBytes)
    (by simpa only [stateAt] using hInv.stBytes)
    (d := "%exitcond.not.i") (tl := "cleanup474.i") (fl := "land.rhs.i103")
    (by simp only [walkWhileBodyI104])
    (bit := evalICmp .eq (BitVec.ofNat 64 p + BitVec.ofNat 64 1) (BitVec.ofNat 64 c))
    (by simp only [stateAt]; exact lookupName_cons_self _ _ _) hl hf

/-! ### The instrument -/

#print axioms LeanLLVM.Refinement.WalkScope.walkWhileBodyI104_find
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.while_body_i104

end WalkScope
end LeanLLVM.Refinement
