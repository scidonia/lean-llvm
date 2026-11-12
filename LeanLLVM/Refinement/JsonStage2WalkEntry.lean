/-
The stage-2 walk's entry edges, and the outer loop's preheader.

`JsonStage2WalkScope` states the measure as the remaining entries radix the inner
component, and the inner component is a **shared per-iteration budget**:
`walkInnerCap G = 4 * G.n + 5`, refilled at the loop head (`walkSeed`,
`walkBack_step`) and drawn on by every scan the iteration runs.  That reading is
what makes a scan's entry edge a link.  A scan's local facts are `c - i ≤ C.inner`
— the budget covers the work still to do — and an entry edge leaves `inner` alone
and shows only that coverage; with `inner` read as one scan's remaining work the
measure would rise at every entry (a finished scan leaves it at zero, the next one
can need `n`), which is why the component is the budget and not the scan.

Two facts an entry link takes from its caller, neither of which `WalkInv` states:

* `G.n + 5 ≤ C.inner` is the budget's **floor at an entry**: at most three scans
  have run since the refill, each at most the document, so at least one scan's
  worth plus slack remains of `4 * n + 5`.  The floor is the composition's
  arithmetic, not a single link's; the link consumes it the way class C consumes
  the refusal offset's bound.
* `c ≤ G.n` is the scan's bound being an entry position — `WalkGeom.inside`'s
  fact, read at the register the block selected.  With it and the floor,
  `walkEntryBudget` gives `c - i ≤ C.inner`.

## What is here

* `while.body.i.lr.ph`, the outer loop's preheader: five literal-offset
  `getelementptr`s, the first of which is `%k11.i` at the staging's `%c.i + 32`
  (`WalkLink.pureJumpK11`'s instance).  It reads `%c.i`, `%z` and `%t352.i`, which
  `WalkPtrs` does not carry — it binds the six registers the dispatch *reads*, and
  these three are the preheader's own inputs — so the link takes their bindings as
  hypotheses, as the entry links take their floor.
* `land.rhs.i.preheader`'s edge into `land.rhs.i`, and `if.end67.i`'s into
  `land.rhs71.i`: the two landed links whose landing fact was an argument.
* `cond.end.i96` (the string scan's bound `phi` and its entry test) and
  `if.end48.i` (the literal comparison's two `phi`s, its `min`, and its entry
  test).

The escapes' scan entry — `if.then447.i`'s edge into `land.rhs457.i` — is a block
that calls, so its link is class F's and is not claimed here.
-/
import LeanLLVM.Refinement.JsonStage2WalkRest

set_option autoImplicit false

namespace LeanLLVM.Refinement
open LeanLLVM
open LeanLLVM.Refinement.JsonStage2IR
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonEntrySteps (denoteCode_lookupName)
open LeanLLVM.Refinement.JsonScanLane

namespace WalkScope

/-! ### A `sub` of two registers, the comparison's boolean, and the entry budget -/

theorem walkStep_sub_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y)) :
    evalInstr calls (stateAt env s) (.binop d .sub w (.reg a) (.reg b)) =
      some (stateAt ((d, .int w (x - y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using LeanLLVM.Refinement.JsonS1MasksIR.evalInstr_binop (r := (x - y).toNat)
      (ha := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := LeanLLVM.Refinement.BlockEval.evalOperand_reg_of env s b (.int w y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

theorem walkDenoteCode_sub_reg_w (calls : Calls) (env : Env) (s : State) (d a b : String)
    (w : Nat) {x y : BitVec w}
    (ha : lookupName env a = some (.int w x)) (hb : lookupName env b = some (.int w y))
    (is : List Instr) :
    denoteCode calls (.binop d .sub w (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x - y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (walkStep_sub_reg_w calls env s d a b w ha hb)]

/-- A one-bit `ult` comparison that is one is a strict order on the operands. -/
theorem walkLt_of_icmp_ult {w : Nat} {a b : BitVec w} (h : evalICmp .ult a b = 1) :
    a.toNat < b.toNat := by
  have hb : BitVec.ult a b = true := by
    cases h' : BitVec.ult a b with
    | false =>
        rw [show evalICmp .ult a b = 0 from by simp [evalICmp, h']] at h
        exact absurd h (by decide)
    | true => rfl
  exact (BitVec.ult_iff_toNat_lt).1 hb

/-- The same for `ugt`, whose value compares its operands the other way round. -/
theorem walkLt_of_icmp_ugt {w : Nat} {a b : BitVec w} (h : evalICmp .ugt b a = 1) :
    a.toNat < b.toNat :=
  walkLt_of_icmp_ult (w := w) (a := a) (b := b) h

/-- **An entry edge's budget arithmetic**: a scan whose bound is an entry position
(`c ≤ n`) and whose budget floor is one whole scan (`n + 5`) is covered. -/
theorem walkEntryBudget {m0 : Mem} (G : WalkGeom m0) {C : WalkCarry G} {i c : Nat}
    (hfloor : G.n + 5 ≤ C.inner) (hc : c ≤ G.n) :
    c - i ≤ C.inner := by omega

/-! ### The outer loop's preheader: `while.body.i.lr.ph` -/

/-- **`while.body.i.lr.ph` as a link**: its five literal-offset `getelementptr`s, the
first of which is `%k11.i` at the staging's own `%c.i + 32`. -/
theorem WalkLink.while_body_i_lr_ph {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "while.body.i.lr.ph")
    (hc : lookupName s.env "%c.i" = some (.ptr C.stage.c))
    (hz : lookupName s.env "%z" = some (.ptr C.stage.z))
    (ht : lookupName s.env "%t352.i" = some (.ptr C.stage.tok)) :
    ∃ s', WalkLink calls G C s { C with block := "while.body.i" } s' := by
  have hden : denoteCode calls walkWhileBodyLrPh.instrs s =
      some (s.bind "%k11.i" (.ptr (C.stage.c + 32)) |>.bind "%h1.i.i.i51" (.ptr (C.stage.z + 24))
        |>.bind "%gap.i" (.ptr (C.stage.tok + 20)) |>.bind "%end.i" (.ptr (C.stage.tok + 8))
        |>.bind "%kind404.i" (.ptr (C.stage.tok + 16))) := by
    simp only [walkWhileBodyLrPh]
    rw [walkDenoteCode_gep8_imm (calls := calls) (s := s) (d := "%k11.i") (base := "%c.i")
      (a := C.stage.c) (c := 32) hc (by decide)]
    rw [walkDenoteCode_gep8_imm (calls := calls)
      (s := s.bind "%k11.i" (.ptr (C.stage.c + 32))) (d := "%h1.i.i.i51") (base := "%z")
      (a := C.stage.z) (c := 24)
      (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact hz)
      (by decide)]
    rw [walkDenoteCode_gep8_imm (calls := calls)
      (s := s.bind "%k11.i" (.ptr (C.stage.c + 32)) |>.bind "%h1.i.i.i51" (.ptr (C.stage.z + 24)))
      (d := "%gap.i") (base := "%t352.i") (a := C.stage.tok) (c := 20)
      (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
      (by decide)]
    rw [walkDenoteCode_gep8_imm (calls := calls)
      (s := s.bind "%k11.i" (.ptr (C.stage.c + 32)) |>.bind "%h1.i.i.i51" (.ptr (C.stage.z + 24))
        |>.bind "%gap.i" (.ptr (C.stage.tok + 20)))
      (d := "%end.i") (base := "%t352.i") (a := C.stage.tok) (c := 8)
      (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
      (by decide)]
    rw [walkDenoteCode_gep8_imm (calls := calls)
      (s := s.bind "%k11.i" (.ptr (C.stage.c + 32)) |>.bind "%h1.i.i.i51" (.ptr (C.stage.z + 24))
        |>.bind "%gap.i" (.ptr (C.stage.tok + 20)) |>.bind "%end.i" (.ptr (C.stage.tok + 8)))
      (d := "%kind404.i") (base := "%t352.i") (a := C.stage.tok) (c := 16)
      (by simp only [State.bind]; repeat rw [lookupName_cons_ne _ _ (by decide)]; exact ht)
      (by decide)]
    rfl
  refine WalkLink.pureJumpK11 (G := G) (C := C) (s := s) hInv
    (B := walkWhileBodyLrPh) (by rw [hblock]; exact walkWhileBodyLrPh_find) hden
    (by unfold walkCarriedNoK11; decide) rfl rfl ?_ rfl (by simp [WalkLocal])
  simp only [State.bind]
  repeat rw [lookupName_cons_ne _ _ (by decide)]
  rfl

/-! ### The scan entries' landing facts -/

/-- **The whitespace skip's entry edge**: `land.rhs.i.preheader` hands `land.rhs.i`
the scan's counter, and the budget covers the scan.  `inner` does not move: the
entry is where a scan *starts*, so the shared budget is checked, not reset. -/
theorem WalkLink.land_rhs_i_preheader_entry {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "land.rhs.i.preheader")
    {i c : Nat}
    (hi : lookupName s.env "%idxprom.i" = some (.int 64 (BitVec.ofNat 64 i)))
    (hcd : lookupName s.env "%cond350.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hlt : i < c) (hcw : c < 2 ^ 64) (hbudget : c - i ≤ C.inner) :
    ∃ s', WalkLink calls G C s { C with block := "land.rhs.i" } s' := by
  refine WalkLink.land_rhs_i_preheader (G := G) (C := C) (s := s) hInv hblock ?_
  rw [WalkLocal.whitespaceLanded rfl]
  refine Or.inr ⟨i, c, hbudget, hlt, hcw, ?_, hi, hcd⟩
  rw [hInv.pc_eq, hblock]

/-- **The escape scan's entry edge**: `if.end67.i`'s comparison selects
`land.rhs71.i`, whose counter is the document position the test compared. -/
theorem WalkLink.if_end67_i_entry {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end67.i")
    {x1 x2 : BitVec 64}
    (h1 : evalOperand s (.reg "%ee.0.lcssa.i") = some (.int 64 x1))
    (h2 : evalOperand s (.reg "%cond.i") = some (.int 64 x2))
    (hult : evalICmp .ult x1 x2 = 1)
    (hbudget : x2.toNat - x1.toNat ≤ C.inner) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ult x1 x2 = 1 then "land.rhs71.i" else "while.end78.i") } s' := by
  refine WalkLink.if_end67_i (G := G) (C := C) (s := s) hInv hblock h1 h2 ?_
  rw [WalkLocal.escapeLanded rfl]
  have hlt : x1.toNat < x2.toNat := walkLt_of_icmp_ult hult
  refine Or.inr ⟨x1.toNat, x2.toNat, hbudget, hlt, x2.isLt, ?_, ?_, ?_⟩
  · rw [hInv.pc_eq, hblock]
  · simp only [stateAt, evalOperand]
    rw [lookupName_cons_ne _ _ (by decide)]
    simpa [evalOperand] using h1
  · simp only [stateAt, evalOperand]
    rw [lookupName_cons_ne _ _ (by decide)]
    simpa [evalOperand] using h2

/-- `cond.end.i96`: the string scan's bound `phi` and the test that enters the scan. -/
def walkCond_end_i96 : Block :=
  { name := "cond.end.i96",
    instrs := [
      Instr.phi "%cond.i" (Ty.int 64) [("cond.true.i106", (Operand.reg "%conv.i")),
        ("if.then432.i", (Operand.reg "%4"))],
      Instr.icmp "%cmp310.i" IPred.ugt 64 (Operand.reg "%cond.i") (Operand.reg "%idxprom.i")],
    term := Term.condbr (Operand.reg "%cmp310.i") "land.rhs.i103" "while.end.i" }

theorem walkCond_end_i96_find : stage2Body.findBlock "cond.end.i96" = some walkCond_end_i96 := by
  simp [stage2Body, Function.findBlock, findBlockList, walkCond_end_i96]

/-- **`cond.end.i96` as a link**: the bound `phi`, the unsigned test, and the entry
edge into the string scan. -/
theorem WalkLink.cond_end_i96 {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "cond.end.i96")
    {p : String} {cvv ivv : BitVec 64} {op : Operand}
    (hpre : s.pre = some p)
    (hin : phiIncoming p [("cond.true.i106", (Operand.reg "%conv.i")),
      ("if.then432.i", (Operand.reg "%4"))] = some op)
    (hv : evalOperand s op = some (.int 64 cvv))
    (hi : lookupName s.env "%idxprom.i" = some (.int 64 ivv))
    (hult : evalICmp .ugt cvv ivv = 1)
    (hbudget : cvv.toNat - ivv.toNat ≤ C.inner) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .ugt cvv ivv = 1
          then "land.rhs.i103" else "while.end.i") } s' := by
  have hlt : ivv.toNat < cvv.toNat := walkLt_of_icmp_ugt hult
  have hden : denoteCode calls walkCond_end_i96.instrs s =
      some (stateAt (("%cmp310.i", .int 1 (evalICmp .ugt cvv ivv)) ::
        ("%cond.i", .int 64 cvv) :: s.env) s) := by
    have hspecs : walkCond_end_i96.instrs =
        ([{ dst := "%cond.i", ty := Ty.int 64,
            incoming := [("cond.true.i106", (Operand.reg "%conv.i")),
              ("if.then432.i", (Operand.reg "%4"))] }].map PhiSpec.instr) ++
          [Instr.icmp "%cmp310.i" IPred.ugt 64 (Operand.reg "%cond.i") (Operand.reg "%idxprom.i")] := by
      simp [walkCond_end_i96, PhiSpec.instr]
    rw [hspecs, denoteCode_phiRun (specs :=
      [{ dst := "%cond.i", ty := Ty.int 64,
         incoming := [("cond.true.i106", (Operand.reg "%conv.i")),
           ("if.then432.i", (Operand.reg "%4"))] }])
      (vs := [("%cond.i", .int 64 cvv)])
      (rest := [Instr.icmp "%cmp310.i" IPred.ugt 64 (Operand.reg "%cond.i") (Operand.reg "%idxprom.i")])
      hpre (PhiSelects.cons hin hv PhiSelects.nil) (by rfl)]
    rw [show s.bindAll [("%cond.i", .int 64 cvv)] =
      stateAt (("%cond.i", .int 64 cvv) :: s.env) s from rfl]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%cond.i", .int 64 cvv) :: s.env) (s := s)
      (d := "%cmp310.i") (a := "%cond.i") (b := "%idxprom.i") IPred.ugt 64
      (x := cvv) (y := ivv)
      (by simp [lookupName]) (by
        rw [lookupName_cons_ne _ _ (by decide)]
        exact hi)]
    rfl
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkCond_end_i96) (by rw [hblock]; exact walkCond_end_i96_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .ugt cvv ivv)
    (by simp [stateAt, lookupName]) ?_ (by simp [WalkLocal])
  rw [WalkLocal.stringScanLanded rfl]
  refine Or.inr ⟨ivv.toNat, cvv.toNat, hbudget, hlt, cvv.isLt, ?_, ?_, ?_⟩
  · rw [hInv.pc_eq, hblock]
  · simp only [stateAt, evalOperand]
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    simpa using hi
  · simp [stateAt, lookupName]

/-- A nonzero bit-vector's value is positive. -/
theorem walkToNat_pos {w : Nat} {x : BitVec w} (h : x ≠ 0) : 0 < x.toNat := by
  rcases Nat.eq_zero_or_pos x.toNat with h0 | hp
  · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h0) : x = 0) h
  · exact hp

/-- `if.end48.i`: the literal comparison's two `phi`s, the remaining length, its
`min` with the literal's own length, and the entry test. -/
def walkIf_end48_i : Block :=
  { name := "if.end48.i",
    instrs := [
      Instr.phi "%lit.0.i" Ty.ptr [("if.then37.i", (Operand.imm .null)),
        ("if.then42.i", (Operand.imm .null)), ("LeafBlock79", (Operand.imm .null))],
      Instr.phi "%ln.0.i" (Ty.int 64) [("if.then37.i", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))),
        ("if.then42.i", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
        ("LeafBlock79", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))],
      Instr.binop "%sub54.i" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i"),
      Instr.icmp "%cond.i.i.min" IPred.ult 64 (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
      Instr.select "%cond.i.i" (Ty.int 64) (Operand.reg "%cond.i.i.min")
        (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
      Instr.icmp "%cmp3.not28.not.i.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i")
        (Operand.reg "%idxprom.i")],
    term := Term.condbr (Operand.reg "%cmp3.not28.not.i.i") "for.end.i.i" "for.body.i.i" }

theorem walkIf_end48_i_find : stage2Body.findBlock "if.end48.i" = some walkIf_end48_i := by
  simp [stage2Body, Function.findBlock, findBlockList, walkIf_end48_i]

/-- **`if.end48.i` as a link**: the literal comparison's entry edge.  The landing
fact is `for.body.i.i`'s second disjunct — the zero counter the block hands it — and
the budget covers the at-most-five-byte comparison. -/
theorem WalkLink.if_end48_i {calls : Calls} {m0 : Mem}
    (G : WalkGeom m0) (C : WalkCarry G) (s : State) (hInv : WalkInv G C s)
    (hblock : C.block = "if.end48.i")
    {p : String} {ee idx lv : BitVec 64} {op₁ op₂ : Operand}
    (hpre : s.pre = some p)
    (hin₁ : phiIncoming p [("if.then37.i", (Operand.imm .null)),
      ("if.then42.i", (Operand.imm .null)), ("LeafBlock79", (Operand.imm .null))] = some op₁)
    (hv₁ : evalOperand s op₁ = some (.ptr 0))
    (hin₂ : phiIncoming p [("if.then37.i", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))),
      ("if.then42.i", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
      ("LeafBlock79", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] = some op₂)
    (hv₂ : evalOperand s op₂ = some (.int 64 lv))
    (hee : lookupName s.env "%ee.0.lcssa.i" = some (.int 64 ee))
    (hidx : lookupName s.env "%idxprom.i" = some (.int 64 idx))
    (hlv4 : 4 ≤ lv.toNat) (hlv5 : lv.toNat ≤ 5)
    (hpos : ¬ ee - idx = 0)
    (hbudget : 5 ≤ C.inner) :
    ∃ s', WalkLink calls G C s
      { C with block := (if evalICmp .eq ee idx = 1 then "for.end.i.i" else "for.body.i.i") } s' := by
  have hden : denoteCode calls walkIf_end48_i.instrs s =
      some (stateAt (("%cmp3.not28.not.i.i", .int 1 (evalICmp .eq ee idx)) ::
        ("%cond.i.i", .int 64 (if evalICmp .ult (ee - idx) lv = 1 then ee - idx else lv)) ::
        ("%cond.i.i.min", .int 1 (evalICmp .ult (ee - idx) lv)) ::
        ("%sub54.i", .int 64 (ee - idx)) ::
        ("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) s) := by
    have hspecs : walkIf_end48_i.instrs =
        ([{ dst := "%lit.0.i", ty := Ty.ptr,
            incoming := [("if.then37.i", (Operand.imm .null)),
              ("if.then42.i", (Operand.imm .null)), ("LeafBlock79", (Operand.imm .null))] },
          { dst := "%ln.0.i", ty := Ty.int 64,
            incoming := [("if.then37.i", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))),
              ("if.then42.i", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
              ("LeafBlock79", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] }].map PhiSpec.instr) ++
          [Instr.binop "%sub54.i" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i"),
           Instr.icmp "%cond.i.i.min" IPred.ult 64 (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
           Instr.select "%cond.i.i" (Ty.int 64) (Operand.reg "%cond.i.i.min")
             (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
           Instr.icmp "%cmp3.not28.not.i.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i")
             (Operand.reg "%idxprom.i")] := by
      simp [walkIf_end48_i, PhiSpec.instr]
    rw [hspecs, denoteCode_phiRun (specs :=
      [{ dst := "%lit.0.i", ty := Ty.ptr,
         incoming := [("if.then37.i", (Operand.imm .null)),
           ("if.then42.i", (Operand.imm .null)), ("LeafBlock79", (Operand.imm .null))] },
       { dst := "%ln.0.i", ty := Ty.int 64,
         incoming := [("if.then37.i", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))),
           ("if.then42.i", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
           ("LeafBlock79", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))] }])
      (vs := [("%lit.0.i", .ptr 0), ("%ln.0.i", .int 64 lv)])
      (rest := [Instr.binop "%sub54.i" BinOp.sub 64 (Operand.reg "%ee.0.lcssa.i") (Operand.reg "%idxprom.i"),
        Instr.icmp "%cond.i.i.min" IPred.ult 64 (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
        Instr.select "%cond.i.i" (Ty.int 64) (Operand.reg "%cond.i.i.min")
          (Operand.reg "%sub54.i") (Operand.reg "%ln.0.i"),
        Instr.icmp "%cmp3.not28.not.i.i" IPred.eq 64 (Operand.reg "%ee.0.lcssa.i")
          (Operand.reg "%idxprom.i")])
      hpre (PhiSelects.cons hin₁ hv₁ (PhiSelects.cons hin₂ hv₂ PhiSelects.nil)) (by rfl)]
    rw [show s.bindAll [("%lit.0.i", .ptr 0), ("%ln.0.i", .int 64 lv)] =
      stateAt (("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) s from rfl]
    rw [walkDenoteCode_sub_reg_w (calls := calls)
      (env := ("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) (s := s)
      (d := "%sub54.i") (a := "%ee.0.lcssa.i") (b := "%idxprom.i") 64
      (x := ee) (y := idx)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hee)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hidx)]
    rw [denoteCode_icmp_reg_w (calls := calls)
      (env := ("%sub54.i", .int 64 (ee - idx)) ::
        ("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) (s := s)
      (d := "%cond.i.i.min") (a := "%sub54.i") (b := "%ln.0.i") IPred.ult 64
      (x := ee - idx) (y := lv)
      (by simp [lookupName]) (by simp [lookupName])]
    rw [denoteCode_select_bit_reg_w (calls := calls)
      (env := ("%cond.i.i.min", .int 1 (evalICmp .ult (ee - idx) lv)) ::
        ("%sub54.i", .int 64 (ee - idx)) ::
        ("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) (s := s)
      (d := "%cond.i.i") (c := "%cond.i.i.min") (a := "%sub54.i") (b := "%ln.0.i") 64
      (bb := evalICmp .ult (ee - idx) lv) (x := ee - idx) (y := lv)
      (by simp [lookupName]) (by simp [lookupName]) (by simp [lookupName])]
    rw [denoteCode_icmp_eq_reg (calls := calls)
      (env := ("%cond.i.i", .int 64 (if evalICmp .ult (ee - idx) lv = 1 then ee - idx else lv)) ::
        ("%cond.i.i.min", .int 1 (evalICmp .ult (ee - idx) lv)) ::
        ("%sub54.i", .int 64 (ee - idx)) ::
        ("%ln.0.i", .int 64 lv) :: ("%lit.0.i", .ptr 0) :: s.env) (s := s)
      (d := "%cmp3.not28.not.i.i") (a := "%ee.0.lcssa.i") (b := "%idxprom.i")
      (x := ee) (y := idx)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hee)
      (by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact hidx)]
    rfl
  refine WalkLink.pureCore (G := G) (C := C) (s := s) hInv
    (B := walkIf_end48_i) (by rw [hblock]; exact walkIf_end48_i_find) hden
    (by unfold walkCarried; decide) rfl rfl rfl
    (bit := evalICmp .eq ee idx)
    (by simp [stateAt, lookupName]) (by simp [WalkLocal]) ?_
  simp only [WalkLocal]
  refine Or.inr ⟨(if evalICmp .ult (ee - idx) lv = 1 then ee - idx else lv).toNat,
    ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : evalICmp .ult (ee - idx) lv = 1
    · have := walkLt_of_icmp_ult h
      simp only [h, ite_true]
      omega
    · simp only [h, ite_false]
      omega
  · by_cases h : evalICmp .ult (ee - idx) lv = 1
    · simp only [h, ite_true]
      exact walkToNat_pos hpos
    · simp only [h, ite_false]
      omega
  · by_cases h : evalICmp .ult (ee - idx) lv = 1
    · simp only [h, ite_true]; exact (ee - idx).isLt
    · simp only [h, ite_false]; exact lv.isLt
  · rw [hInv.pc_eq, hblock]
  · simp [stateAt, lookupName, BitVec.ofNat_toNat]

/-! ### The instrument -/

/-- info: 'LeanLLVM.Refinement.WalkScope.walkStep_sub_reg_w' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkStep_sub_reg_w

/-- info: 'LeanLLVM.Refinement.WalkScope.walkEntryBudget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.walkEntryBudget

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.while_body_i_lr_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.while_body_i_lr_ph

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.cond_end_i96' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.cond_end_i96

/-- info: 'LeanLLVM.Refinement.WalkScope.WalkLink.if_end48_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Refinement.WalkScope.WalkLink.if_end48_i

end WalkScope
end LeanLLVM.Refinement
