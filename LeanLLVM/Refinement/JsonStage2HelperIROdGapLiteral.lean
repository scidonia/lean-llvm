/-
`od_gap_recover`'s literal compare unit, as a run of the pinned body.

`JsonStage2HelperIROdGapSteps` pins the body's blocks and proves the instruction
and terminator steps at its widths, and `JsonStage2HelperIROdGapRun` proves the
entry chain and the first scan.  This module proves the unit those leave: from
`if.else` — the number test's false arm at the scan's merge — the byte dispatch
to `if.then37`/`if.then42`/`LeafBlock11` and, past them, `if.end48`'s literal
selection and compare loop, or the non-scalar refusal at `if.else43`.

The unit's exits are the body's own: `if.end67` when the loop matched, and the
record the mismatch site writes (`if.then57`, tag 2 at `%msg2.i132`, offset
`%ei49.0.ph + %t.0.val`) or the scalar site writes (`if.else43`, tag 3 at
`%msg2.i130`, offset `%t.0.val`).  The statement is a `runFuel` prefix at the
exit states, with the record's memory effect and the compare loop's own
memory-unchanged fact.  The loop is a `BoundLoop` over the counter `%i.029.i`,
whose bound is the compare length `min (%ee.0.lcssa - %t.0.val) %ln.0`.

The dispatch is composed in both directions.  The three accepted bytes reach
`if.end48` in four or five control steps, and every other byte reaches
`cleanup82` through `if.else43` in at most five; the split is the switch's own
signed byte comparisons, so a byte at or above `0x80` takes the left edge.  On
the exit side, the word the loop leaves carries the record word
`readBytes mem (cur + 1112) 8` the refusal sites load, and the two exits are
continued: `if.then57` writes the tag-2 record in one step, and `for.end.i` takes
`if.end67` when the token's length equals the literal's and otherwise reaches the
same record at `%cond.i + %t.0.val` in two.  The empty range — a token of length
zero — takes `if.end48`'s `for.end.i` edge directly, so the compare loop is
skipped and only that test runs.

The blocks and instruction steps are the pinned ones: every step below is
`step` at a `findBlock` pin and a `denoteCode` chain built from the `gap_*`
steps of the Steps module, and the byte reads are the Run module's
`gap_readOne`/`gap_natToBytes_gapByte` at the body's own addressing.
-/
import LeanLLVM.Refinement.JsonStage2HelperIROdGapRun

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval

/-! ### One control step, from a block's run and terminator -/

/-- One control step from a block's run: `step` at a state whose program counter
finds the block, whose instructions denote to `s'`, and whose terminator is `c`.
The block is named by its three fields so that the terminator's shape reaches
the last hypothesis as a term rather than as a projection. -/
theorem gapLit_step_at_block {calls : Calls} {f : Function}
    {s s' : State} {name : String} {is : List Instr} {term : Term} {c : Ctrl}
    (hfind : f.findBlock s.pc = some ⟨name, is, term⟩)
    (hcode : denoteCode calls is s = some s')
    (hterm : execTerm s' term = c) : step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- A `condbr` on a one-bit value the block computed: the branch target, in one
form for both bits. -/
theorem gapLit_execTerm_condbr (s : State) (c t f pcName : String) {b : BitVec 1}
    (hpc : s.pc = pcName)
    (hop : evalOperand s (.reg c) = some (.int 1 b)) :
    execTerm s (.condbr (.reg c) t f) =
      .jump { s with pc := if b = 1 then t else f, pre := some pcName } := by
  rcases bitVec1_eq_zero_or_one b with hb | hb
  · subst hb
    simp [execTerm, hop, hpc]
  · subst hb
    simp [execTerm, hop, hpc]

/-- A state's three written fields, named so a statement can spell the exit
state without a structure literal in argument position. -/
def gapLitSet (s : State) (pc lpc : String) (mem : Mem) : State :=
  { s with pc := pc, pre := some lpc, mem := mem }

@[simp] theorem gapLitSet_pc (s : State) (pc lpc : String) (mem : Mem) :
    (gapLitSet s pc lpc mem).pc = pc := rfl

@[simp] theorem gapLitSet_mem (s : State) (pc lpc : String) (mem : Mem) :
    (gapLitSet s pc lpc mem).mem = mem := rfl

/-! ### The blocks' environments, as named builders -/

/-- `if.end48`'s cells: the literal, its width, the token's length and the
compare bound. -/
def gapLitEnd48Env (env : Env) (litBase : Nat) (lnw ee t : BitVec 64) : Env :=
  ("%cmp3.not28.not.i", .int 1 (evalICmp .eq ee t)) ::
  ("%cond.i", .int 64 (if evalICmp .ult (ee - t) lnw = 1 then ee - t else lnw)) ::
  ("%cond.i.min", .int 1 (evalICmp .ult (ee - t) lnw)) ::
  ("%sub54", .int 64 (ee - t)) ::
  ("%ln.0", .int 64 lnw) ::
  ("%lit.0", .ptr litBase) :: env

/-- `for.body.i`'s cells: the index, the two bytes and their test. -/
def gapLitBodyEnv (env : Env) (base litBase : Nat) (iw : BitVec 64) (se : Nat)
    (x y : BitVec 8) : Env :=
  ("%cmp8.not.i", .int 1 (evalICmp .eq x y)) ::
  ("%13", .int 8 y) ::
  ("%arrayidx6.i", .ptr (litBase + se)) ::
  ("%12", .int 8 x) ::
  ("%arrayidx.i", .ptr (base + se)) ::
  ("%i.029.i", .int 64 iw) :: env

/-- `for.inc.i`'s cells: the successor and its test against the bound. -/
def gapLitIncEnv (env : Env) (iw mw : BitVec 64) : Env :=
  ("%exitcond.not.i", .int 1 (evalICmp .eq (iw + 1) mw)) ::
  ("%inc.i", .int 64 (iw + 1)) :: env

/-- `for.end.i`'s cell: the token length's equality with the literal width. -/
def gapLitEndEnv (env : Env) (nw lnw : BitVec 64) : Env :=
  ("%cmp11.not.i", .int 1 (evalICmp .eq nw lnw)) :: env

/-- `if.else43`'s cells: the record pointer word and its three stores. -/
def gapLitElse43Env (env : Env) (cur r : Nat) : Env :=
  ("%msg2.i130", .ptr (r + 16)) :: ("%off1.i129", .ptr (r + 8)) ::
  ("%11", .ptr r) :: ("%e44", .ptr (cur + 1112)) :: env

/-- `if.then57`'s record writes: the tag-2 record at the selected offset. -/
def gapLitThen57Mem (s : State) (r : Nat) (ew tw : BitVec 64) : Mem :=
  writeBytes
    (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8)
      (natToBytes (ew + tw).toNat 8))
    (r + 16) (natToBytes 2 8)

/-- `if.then57`'s cells: the selected refusal index, the record pointer word and
its three stores. -/
def gapLitThen57Env (env : Env) (cur r : Nat) (ew tw : BitVec 64) : Env :=
  ("%msg2.i132", .ptr (r + 16)) :: ("%off1.i131", .ptr (r + 8)) ::
  ("%add60", .int 64 (ew + tw)) :: ("%14", .ptr r) ::
  ("%e58", .ptr (cur + 1112)) :: ("%ei49.0.ph", .int 64 ew) :: env

/-! ### The byte dispatch -/

/-- `if.else`: no instructions, and the edge to `NodeBlock15`. -/
theorem gapLit_step_ifElse {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.else") :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) := by
  let mid : State := { s with pc := "NodeBlock15", pre := some "if.else" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env s) (name := "if.else") (is := odGapRecoverIfElseInstrs)
    (term := Term.br "NodeBlock15") (c := .jump (stateAt env mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_else
  · simp only [odGapRecoverIfElseInstrs, denoteCode_nil]
  · rw [gap_execTerm_br]; simp only [stateAt, hpc]
    rfl

/-- `NodeBlock15`: `%7 < 110` selects `LeafBlock7`. -/
theorem gapLit_step_NodeBlock15 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 8}
    (hpc : s.pc = "NodeBlock15")
    (h7 : lookupName env "%7" = some (.int 8 x)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot16", .int 1 (evalICmp .slt x (BitVec.ofNat 8 110))) :: env)
        { s with pc := if evalICmp .slt x (BitVec.ofNat 8 110) = 1
                        then "LeafBlock7" else "NodeBlock13",
                 pre := some "NodeBlock15" }) := by
  let env' : Env := ("%Pivot16", .int 1 (evalICmp .slt x (BitVec.ofNat 8 110))) :: env
  let mid : State :=
    { s with pc := if evalICmp .slt x (BitVec.ofNat 8 110) = 1
                    then "LeafBlock7" else "NodeBlock13",
             pre := some "NodeBlock15" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "NodeBlock15")
    (is := odGapRecoverNodeBlock15Instrs)
    (term := Term.condbr (Operand.reg "%Pivot16") "LeafBlock7" "NodeBlock13")
    (c := .jump (stateAt env' mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_NodeBlock15
  · unfold odGapRecoverNodeBlock15Instrs
    gap_eval
  · rw [gapLit_execTerm_condbr (s := stateAt env' s) (c := "%Pivot16")
      (t := "LeafBlock7") (f := "NodeBlock13") (pcName := "NodeBlock15")
      (by simp only [stateAt, hpc])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-- `NodeBlock13`: `%7 < 116` selects `LeafBlock9`. -/
theorem gapLit_step_NodeBlock13 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 8}
    (hpc : s.pc = "NodeBlock13")
    (h7 : lookupName env "%7" = some (.int 8 x)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot14", .int 1 (evalICmp .slt x (BitVec.ofNat 8 116))) :: env)
        { s with pc := if evalICmp .slt x (BitVec.ofNat 8 116) = 1
                        then "LeafBlock9" else "LeafBlock11",
                 pre := some "NodeBlock13" }) := by
  let env' : Env := ("%Pivot14", .int 1 (evalICmp .slt x (BitVec.ofNat 8 116))) :: env
  let mid : State :=
    { s with pc := if evalICmp .slt x (BitVec.ofNat 8 116) = 1
                    then "LeafBlock9" else "LeafBlock11",
             pre := some "NodeBlock13" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "NodeBlock13")
    (is := odGapRecoverNodeBlock13Instrs)
    (term := Term.condbr (Operand.reg "%Pivot14") "LeafBlock9" "LeafBlock11")
    (c := .jump (stateAt env' mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_NodeBlock13
  · unfold odGapRecoverNodeBlock13Instrs
    gap_eval
  · rw [gapLit_execTerm_condbr (s := stateAt env' s) (c := "%Pivot14")
      (t := "LeafBlock9") (f := "LeafBlock11") (pcName := "NodeBlock13")
      (by simp only [stateAt, hpc])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-- `LeafBlock11`: `%7 == 116` selects `if.end48`. -/
theorem gapLit_step_LeafBlock11 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 8}
    (hpc : s.pc = "LeafBlock11")
    (h7 : lookupName env "%7" = some (.int 8 x)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf12", .int 1 (evalICmp .eq x (BitVec.ofNat 8 116))) :: env)
        { s with pc := if evalICmp .eq x (BitVec.ofNat 8 116) = 1
                        then "if.end48" else "if.else43",
                 pre := some "LeafBlock11" }) := by
  let env' : Env := ("%SwitchLeaf12", .int 1 (evalICmp .eq x (BitVec.ofNat 8 116))) :: env
  let mid : State :=
    { s with pc := if evalICmp .eq x (BitVec.ofNat 8 116) = 1
                    then "if.end48" else "if.else43",
             pre := some "LeafBlock11" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "LeafBlock11")
    (is := odGapRecoverLeafBlock11Instrs)
    (term := Term.condbr (Operand.reg "%SwitchLeaf12") "if.end48" "if.else43")
    (c := .jump (stateAt env' mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_LeafBlock11
  · unfold odGapRecoverLeafBlock11Instrs
    gap_eval
  · rw [gapLit_execTerm_condbr (s := stateAt env' s) (c := "%SwitchLeaf12")
      (t := "if.end48") (f := "if.else43") (pcName := "LeafBlock11")
      (by simp only [stateAt, hpc])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-- `LeafBlock9`: `%7 == 110` selects `if.then42`. -/
theorem gapLit_step_LeafBlock9 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 8}
    (hpc : s.pc = "LeafBlock9")
    (h7 : lookupName env "%7" = some (.int 8 x)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf10", .int 1 (evalICmp .eq x (BitVec.ofNat 8 110))) :: env)
        { s with pc := if evalICmp .eq x (BitVec.ofNat 8 110) = 1
                        then "if.then42" else "if.else43",
                 pre := some "LeafBlock9" }) := by
  let env' : Env := ("%SwitchLeaf10", .int 1 (evalICmp .eq x (BitVec.ofNat 8 110))) :: env
  let mid : State :=
    { s with pc := if evalICmp .eq x (BitVec.ofNat 8 110) = 1
                    then "if.then42" else "if.else43",
             pre := some "LeafBlock9" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "LeafBlock9")
    (is := odGapRecoverLeafBlock9Instrs)
    (term := Term.condbr (Operand.reg "%SwitchLeaf10") "if.then42" "if.else43")
    (c := .jump (stateAt env' mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_LeafBlock9
  · unfold odGapRecoverLeafBlock9Instrs
    gap_eval
  · rw [gapLit_execTerm_condbr (s := stateAt env' s) (c := "%SwitchLeaf10")
      (t := "if.then42") (f := "if.else43") (pcName := "LeafBlock9")
      (by simp only [stateAt, hpc])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-- `LeafBlock7`: `%7 == 102` selects `if.then37`. -/
theorem gapLit_step_LeafBlock7 {calls : Calls} {env : Env} {s : State}
    {x : BitVec 8}
    (hpc : s.pc = "LeafBlock7")
    (h7 : lookupName env "%7" = some (.int 8 x)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf8", .int 1 (evalICmp .eq x (BitVec.ofNat 8 102))) :: env)
        { s with pc := if evalICmp .eq x (BitVec.ofNat 8 102) = 1
                        then "if.then37" else "if.else43",
                 pre := some "LeafBlock7" }) := by
  let env' : Env := ("%SwitchLeaf8", .int 1 (evalICmp .eq x (BitVec.ofNat 8 102))) :: env
  let mid : State :=
    { s with pc := if evalICmp .eq x (BitVec.ofNat 8 102) = 1
                    then "if.then37" else "if.else43",
             pre := some "LeafBlock7" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env' s) (name := "LeafBlock7")
    (is := odGapRecoverLeafBlock7Instrs)
    (term := Term.condbr (Operand.reg "%SwitchLeaf8") "if.then37" "if.else43")
    (c := .jump (stateAt env' mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_LeafBlock7
  · unfold odGapRecoverLeafBlock7Instrs
    gap_eval
  · rw [gapLit_execTerm_condbr (s := stateAt env' s) (c := "%SwitchLeaf8")
      (t := "if.then37") (f := "if.else43") (pcName := "LeafBlock7")
      (by simp only [stateAt, hpc])
      (by simp only [stateAt, evalOperand]; rw [lookupName_cons_self])]
    rfl

/-- `if.then37`: the `false` literal's edge to `if.end48`. -/
theorem gapLit_step_ifThen37 {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.then37") :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "if.end48", pre := some "if.then37" }) := by
  let mid : State := { s with pc := "if.end48", pre := some "if.then37" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env s) (name := "if.then37") (is := odGapRecoverIfThen37Instrs)
    (term := Term.br "if.end48") (c := .jump (stateAt env mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then37
  · simp only [odGapRecoverIfThen37Instrs, denoteCode_nil]
  · rw [gap_execTerm_br]; simp only [stateAt, hpc]
    rfl

/-- `if.then42`: the `null` literal's edge to `if.end48`. -/
theorem gapLit_step_ifThen42 {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.then42") :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "if.end48", pre := some "if.then42" }) := by
  let mid : State := { s with pc := "if.end48", pre := some "if.then42" }
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt env s) (name := "if.then42") (is := odGapRecoverIfThen42Instrs)
    (term := Term.br "if.end48") (c := .jump (stateAt env mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then42
  · simp only [odGapRecoverIfThen42Instrs, denoteCode_nil]
  · rw [gap_execTerm_br]; simp only [stateAt, hpc]
    rfl

/-! ### The non-scalar refusal -/

/-- `if.else43`: the record's tag store for the non-scalar byte, and the return
path's edge to `cleanup82`. -/
theorem gapLit_step_ifElse43 {calls : Calls} {env : Env} {s : State}
    {cur r : Nat} {t : BitVec 64}
    (hpc : s.pc = "if.else43")
    (hc : lookupName env "%c" = some (.ptr cur))
    (hrec : readBytes s.mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (ht : lookupName env "%t.0.val" = some (.int 64 t)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitElse43Env env cur r)
        (gapLitSet s "cleanup82" "if.else43"
          (writeBytes
            (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8) (natToBytes t.toNat 8))
            (r + 16) (natToBytes 3 8)))) := by
  let mem' : Mem :=
    writeBytes
      (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8) (natToBytes t.toNat 8))
      (r + 16) (natToBytes 3 8)
  have hcode : denoteCode calls odGapRecoverIfElse43Instrs (stateAt env s) =
      some (stateAt (gapLitElse43Env env cur r) { s with mem := mem' }) := by
    unfold odGapRecoverIfElse43Instrs
    gap_eval
    all_goals decide
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitElse43Env env cur r) { s with mem := mem' })
    (name := "if.else43") (is := odGapRecoverIfElse43Instrs) (term := Term.br "cleanup82")
    (c := .jump (stateAt (gapLitElse43Env env cur r)
      (gapLitSet s "cleanup82" "if.else43" mem'))) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_else43
  · exact hcode
  · rw [gap_execTerm_br]; simp only [stateAt, hpc, gapLitSet]

/-! ### `if.end48`: the literal selection and the compare bound -/

/-- `if.end48`: the two `phi`s select the literal pointer and its length, the
token's length is `%ee.0.lcssa - %t.0.val`, the compare bound is the unsigned
minimum, and the empty-range test is the token's own length test. -/
theorem gapLit_step_ifEnd48 {calls : Calls} {env : Env} {s : State}
    {p : String} {litBase : Nat} {lnw ee t : BitVec 64}
    {opL opN : Operand}
    (hpc : s.pc = "if.end48") (hpre : s.pre = some p)
    (hincL : phiIncoming p
      [("if.then37", Operand.reg "%litfalse"), ("if.then42", Operand.reg "%litnull"),
       ("LeafBlock11", Operand.reg "%littrue")] = some opL)
    (hopL : evalOperand (stateAt env s) opL = some (.ptr litBase))
    (hincN : phiIncoming p
      [("if.then37", Operand.imm (Const.int 64 0x0000000000000005#64)),
       ("if.then42", Operand.imm (Const.int 64 0x0000000000000004#64)),
       ("LeafBlock11", Operand.imm (Const.int 64 0x0000000000000004#64))] = some opN)
    (hopN : evalOperand (stateAt env s) opN = some (.int 64 lnw))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (htt : lookupName env "%t.0.val" = some (.int 64 t)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitEnd48Env env litBase lnw ee t)
        { s with pc := if evalICmp .eq ee t = 1 then "for.end.i" else "for.body.i",
                 pre := some "if.end48" }) := by
  let mid : State :=
    { s with pc := if evalICmp .eq ee t = 1 then "for.end.i" else "for.body.i",
             pre := some "if.end48" }
  have hcode : denoteCode calls odGapRecoverIfEnd48Instrs (stateAt env s) =
      some (stateAt (gapLitEnd48Env env litBase lnw ee t) s) := by
    unfold odGapRecoverIfEnd48Instrs
    block_phi_run
    gap_eval
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitEnd48Env env litBase lnw ee t) s) (name := "if.end48")
    (is := odGapRecoverIfEnd48Instrs)
    (term := Term.condbr (Operand.reg "%cmp3.not28.not.i") "for.end.i" "for.body.i")
    (c := .jump (stateAt (gapLitEnd48Env env litBase lnw ee t) mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_end48
  · exact hcode
  · rw [gapLit_execTerm_condbr (s := stateAt (gapLitEnd48Env env litBase lnw ee t) s)
      (c := "%cmp3.not28.not.i") (t := "for.end.i") (f := "for.body.i")
      (pcName := "if.end48")
      (by simp only [stateAt, hpc])
      (by simp only [gapLitEnd48Env, stateAt, evalOperand]
          rw [lookupName_cons_self])]
    rfl

/-! ### The compare loop's three blocks -/

/-- `for.body.i`: the carried index, the token byte at `%arrayidx9 + i`, the
literal byte at `%lit.0 + i`, and their equality. -/
theorem gapLit_step_forBody {calls : Calls} {env : Env} {s : State}
    {p : String} {base litBase : Nat} {iw : BitVec 64} {se : Nat}
    {x y : BitVec 8} {op : Operand}
    (hpc : s.pc = "for.body.i") (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("for.inc.i", Operand.reg "%inc.i"),
       ("if.end48", Operand.imm (Const.int 64 0x0000000000000000#64))] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 iw))
    (hbase : lookupName env "%arrayidx9" = some (.ptr base))
    (hlit : lookupName env "%lit.0" = some (.ptr litBase))
    (hse : (iw.signExtend 64).toNat = se) (hse63 : se < 2 ^ 63)
    (hx : readBytes s.mem (base + se) 1 = some (natToBytes x.toNat 1))
    (hy : readBytes s.mem (litBase + se) 1 = some (natToBytes y.toNat 1)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitBodyEnv env base litBase iw se x y)
        { s with pc := if evalICmp .eq x y = 1 then "for.inc.i" else "if.then57",
                 pre := some "for.body.i" }) := by
  let mid : State :=
    { s with pc := if evalICmp .eq x y = 1 then "for.inc.i" else "if.then57",
             pre := some "for.body.i" }
  have hcode : denoteCode calls odGapRecoverForBodyIInstrs (stateAt env s) =
      some (stateAt (gapLitBodyEnv env base litBase iw se x y) s) := by
    unfold odGapRecoverForBodyIInstrs
    rw [denoteCode_phi calls env s "%i.029.i" (Ty.int 64)
      [("for.inc.i", Operand.reg "%inc.i"),
       ("if.end48", Operand.imm (Const.int 64 0x0000000000000000#64))]
      (p := p) (op := op) (v := .int 64 iw) hpre hinc hop
      [Instr.gep "%arrayidx.i" (Ty.int 8) (Operand.reg "%arrayidx9") (Operand.reg "%i.029.i"),
       Instr.load "%12" (Ty.int 8) (Operand.reg "%arrayidx.i"),
       Instr.gep "%arrayidx6.i" (Ty.int 8) (Operand.reg "%lit.0") (Operand.reg "%i.029.i"),
       Instr.load "%13" (Ty.int 8) (Operand.reg "%arrayidx6.i"),
       Instr.icmp "%cmp8.not.i" (IPred.eq) 8 (Operand.reg "%12") (Operand.reg "%13")]
      (by decide)]
    rw [denoteCode_gep8_reg calls (("%i.029.i", .int 64 iw) :: env) s
      "%arrayidx.i" "%arrayidx9" "%i.029.i" (by block_lk) (by block_lk) (by rw [hse]; exact hse63) _]
    rw [gap_denote_load8 calls (("%arrayidx.i", .ptr (base + (iw.signExtend 64).toNat)) ::
        ("%i.029.i", .int 64 iw) :: env) s "%12" "%arrayidx.i"
      (by block_lk) (by rw [hse]; exact hx) _]
    rw [denoteCode_gep8_reg calls
      (("%12", .int 8 x) :: ("%arrayidx.i", .ptr (base + (iw.signExtend 64).toNat)) ::
        ("%i.029.i", .int 64 iw) :: env) s
      "%arrayidx6.i" "%lit.0" "%i.029.i" (by block_lk) (by block_lk) (by rw [hse]; exact hse63) _]
    rw [gap_denote_load8 calls (("%arrayidx6.i", .ptr (litBase + (iw.signExtend 64).toNat)) ::
        ("%12", .int 8 x) ::
        ("%arrayidx.i", .ptr (base + (iw.signExtend 64).toNat)) ::
        ("%i.029.i", .int 64 iw) :: env) s "%13" "%arrayidx6.i"
      (by block_lk) (by rw [hse]; exact hy) _]
    rw [gap_denote_icmp_eq_reg calls
      (("%13", .int 8 y) ::
        ("%arrayidx6.i", .ptr (litBase + (iw.signExtend 64).toNat)) ::
        ("%12", .int 8 x) ::
        ("%arrayidx.i", .ptr (base + (iw.signExtend 64).toNat)) ::
        ("%i.029.i", .int 64 iw) :: env) s "%cmp8.not.i" "%12" "%13"
      (by block_lk) (by block_lk) []]
    rw [hse]
    rfl
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitBodyEnv env base litBase iw se x y) s) (name := "for.body.i")
    (is := odGapRecoverForBodyIInstrs)
    (term := Term.condbr (Operand.reg "%cmp8.not.i") "for.inc.i" "if.then57")
    (c := .jump (stateAt (gapLitBodyEnv env base litBase iw se x y) mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_for_body_i
  · exact hcode
  · rw [gapLit_execTerm_condbr (s := stateAt (gapLitBodyEnv env base litBase iw se x y) s)
      (c := "%cmp8.not.i") (t := "for.inc.i") (f := "if.then57")
      (pcName := "for.body.i")
      (by simp only [stateAt, hpc])
      (by simp only [gapLitBodyEnv, stateAt, evalOperand]
          rw [lookupName_cons_self])]
    rfl

/-- `for.inc.i`: the incremented index and its test against the compare bound. -/
theorem gapLit_step_forInc {calls : Calls} {env : Env} {s : State}
    {iw mw : BitVec 64}
    (hpc : s.pc = "for.inc.i")
    (hi : lookupName env "%i.029.i" = some (.int 64 iw))
    (hm : lookupName env "%cond.i" = some (.int 64 mw)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitIncEnv env iw mw)
        { s with pc := if evalICmp .eq (iw + 1) mw = 1 then "for.end.i" else "for.body.i",
                 pre := some "for.inc.i" }) := by
  let mid : State :=
    { s with pc := if evalICmp .eq (iw + 1) mw = 1 then "for.end.i" else "for.body.i",
             pre := some "for.inc.i" }
  have hcode : denoteCode calls odGapRecoverForIncIInstrs (stateAt env s) =
      some (stateAt (gapLitIncEnv env iw mw) s) := by
    unfold odGapRecoverForIncIInstrs
    gap_eval
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitIncEnv env iw mw) s) (name := "for.inc.i")
    (is := odGapRecoverForIncIInstrs)
    (term := Term.condbr (Operand.reg "%exitcond.not.i") "for.end.i" "for.body.i")
    (c := .jump (stateAt (gapLitIncEnv env iw mw) mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_for_inc_i
  · exact hcode
  · rw [gapLit_execTerm_condbr (s := stateAt (gapLitIncEnv env iw mw) s)
      (c := "%exitcond.not.i") (t := "for.end.i") (f := "for.body.i")
      (pcName := "for.inc.i")
      (by simp only [stateAt, hpc])
      (by simp only [gapLitIncEnv, stateAt, evalOperand]
          rw [lookupName_cons_self])]
    rfl

/-- `for.end.i`: the token length equals the literal's width. -/
theorem gapLit_step_forEnd {calls : Calls} {env : Env} {s : State}
    {nw lnw : BitVec 64}
    (hpc : s.pc = "for.end.i")
    (hn : lookupName env "%sub54" = some (.int 64 nw))
    (hl : lookupName env "%ln.0" = some (.int 64 lnw)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitEndEnv env nw lnw)
        { s with pc := if evalICmp .eq nw lnw = 1 then "if.end67" else "if.then57",
                 pre := some "for.end.i" }) := by
  let mid : State :=
    { s with pc := if evalICmp .eq nw lnw = 1 then "if.end67" else "if.then57",
             pre := some "for.end.i" }
  have hcode : denoteCode calls odGapRecoverForEndIInstrs (stateAt env s) =
      some (stateAt (gapLitEndEnv env nw lnw) s) := by
    unfold odGapRecoverForEndIInstrs
    gap_eval
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitEndEnv env nw lnw) s) (name := "for.end.i")
    (is := odGapRecoverForEndIInstrs)
    (term := Term.condbr (Operand.reg "%cmp11.not.i") "if.end67" "if.then57")
    (c := .jump (stateAt (gapLitEndEnv env nw lnw) mid)) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_for_end_i
  · exact hcode
  · rw [gapLit_execTerm_condbr (s := stateAt (gapLitEndEnv env nw lnw) s)
      (c := "%cmp11.not.i") (t := "if.end67") (f := "if.then57")
      (pcName := "for.end.i")
      (by simp only [stateAt, hpc])
      (by simp only [gapLitEndEnv, stateAt, evalOperand]
          rw [lookupName_cons_self])]
    rfl

/-! ### The literal refusal site -/

/-- `if.then57`: the refusal record's tag 2 and the offset `%ei49.0.ph +
%t.0.val`, then the return path's edge to `cleanup82`. -/
theorem gapLit_step_ifThen57 {calls : Calls} {env : Env} {s : State}
    {p : String} {cur r : Nat} {ew tw : BitVec 64} {op : Operand}
    (hpc : s.pc = "if.then57") (hpre : s.pre = some p)
    (hinc : phiIncoming p
      [("for.end.i", Operand.reg "%cond.i"),
       ("for.body.i", Operand.reg "%i.029.i")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 ew))
    (hc : lookupName env "%c" = some (.ptr cur))
    (hrec : readBytes s.mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (ht : lookupName env "%t.0.val" = some (.int 64 tw)) :
    step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitThen57Env env cur r ew tw)
        (gapLitSet s "cleanup82" "if.then57"
          (gapLitThen57Mem s r ew tw))) := by
  have hcode : denoteCode calls odGapRecoverIfThen57Instrs (stateAt env s) =
      some (stateAt (gapLitThen57Env env cur r ew tw) { s with mem := gapLitThen57Mem s r ew tw }) := by
    unfold odGapRecoverIfThen57Instrs
    block_phi_run
    gap_eval
    all_goals decide
  refine gapLit_step_at_block (f := odGapRecoverBody) (s := stateAt env s)
    (s' := stateAt (gapLitThen57Env env cur r ew tw) { s with mem := gapLitThen57Mem s r ew tw })
    (name := "if.then57") (is := odGapRecoverIfThen57Instrs) (term := Term.br "cleanup82")
    (c := .jump (stateAt (gapLitThen57Env env cur r ew tw)
      (gapLitSet s "cleanup82" "if.then57" (gapLitThen57Mem s r ew tw)))) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using odGapRecover_findBlock_if_then57
  · exact hcode
  · rw [gap_execTerm_br]; simp only [stateAt, hpc, gapLitSet]

/-! ### The compare loop -/

/-- A byte's encoding is injective: the loop's `icmp eq` is the model's byte
equality. -/
theorem gapLit_gapByte_eq {a b : UInt8} : gapByte a = gapByte b ↔ a = b := by
  constructor
  · intro h
    have h2 : a.toNat = b.toNat := by
      have := congrArg BitVec.toNat h
      simpa only [gapByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.toNat_lt,
        Nat.mod_eq_of_lt b.toNat_lt] using this
    exact UInt8.toNat_inj.mp h2
  · intro h; rw [h]

/-- `icmp eq` at equal eight-bit words is one. -/
theorem gapLit_icmp_eq_one {w : Nat} {x y : BitVec w} (h : x = y) :
    evalICmp .eq x y = 1#1 := by
  simp only [evalICmp, h]
  rfl

/-- The carried index at `for.body.i`, by predecessor: the first visit carries
zero, and every later one the `for.inc.i` binding. -/
def gapLitCarried (s : State) (c : Nat) : Prop :=
  (s.pre = some "if.end48" ∧ c = 0) ∨
  (s.pre = some "for.inc.i" ∧
    lookupName s.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 c)))

/-- The loop's invariant at `for.body.i`: the head's cells, the carried counter,
the compare length and the compared prefix. -/
def gapLitInv (bytes litBytes : List UInt8) (cur base litBase t n ln m : Nat)
    (mem : Mem) (r : Nat) (s : State) (c : Nat) : Prop :=
  s.pc = "for.body.i" ∧ s.mem = mem ∧
  lookupName s.env "%arrayidx9" = some (.ptr base) ∧
  lookupName s.env "%lit.0" = some (.ptr litBase) ∧
  lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)) ∧
  lookupName s.env "%sub54" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName s.env "%ln.0" = some (.int 64 (BitVec.ofNat 64 ln)) ∧
  lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) ∧
  lookupName s.env "%c" = some (.ptr cur) ∧
  gapLitCarried s c ∧
  m ≤ n ∧ m ≤ ln ∧ c < m ∧ m ≤ 2 ^ 63 ∧
  (∀ j, j < c → bytes.getD (t + j) 0 = litBytes.getD j 0) ∧
  m - 1 ≤ c + r

/-- The head's exit test: a differing byte, or the last compared index. -/
def gapLitAtBound (bytes litBytes : List UInt8) (t m : Nat) (_s : State) (c : Nat) : Bool :=
  decide (bytes.getD (t + c) 0 ≠ litBytes.getD c 0) || decide (c + 1 = m)

/-- The two blocks the loop leaves for. -/
def gapLitExitBlock (e : State) : Prop := e.pc = "if.then57" ∨ e.pc = "for.end.i"

/-- The exit word: the caller's memory, the record word the refusal sites read
and its address bound, the cells the refusal sites read, and the exit's own index
— a differing position on the mismatch, the compare length on the bound exit. -/
def gapLitExitWord (bytes litBytes : List UInt8) (cur t n ln m : Nat) (mem : Mem)
    (e : State) : Prop :=
  e.mem = mem ∧
  lookupName e.env "%c" = some (.ptr cur) ∧
  lookupName e.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) ∧
  lookupName e.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)) ∧
  lookupName e.env "%sub54" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName e.env "%ln.0" = some (.int 64 (BitVec.ofNat 64 ln)) ∧
  ((∃ c, e.pc = "if.then57" ∧ e.pre = some "for.body.i" ∧
      lookupName e.env "%i.029.i" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      c < m ∧
      (∀ j, j < c → bytes.getD (t + j) 0 = litBytes.getD j 0) ∧
      bytes.getD (t + c) 0 ≠ litBytes.getD c 0)
   ∨ (e.pc = "for.end.i" ∧ e.pre = some "for.inc.i" ∧
      lookupName e.env "%inc.i" = some (.int 64 (BitVec.ofNat 64 m)) ∧
      (∀ j, j < m → bytes.getD (t + j) 0 = litBytes.getD j 0))) ∧
  (∃ r, readBytes mem (cur + 1112) 8 = some (natToBytes r 8) ∧ r < 2 ^ 64)

/-- The head's own step, at the body bytes the invariant's prefix reaches. -/
theorem gapLit_head_step {calls : Calls} {s : State}
    {bytes litBytes : List UInt8} {cur base litBase b t n ln m r c ip : Nat} {mem : Mem}
    (hinv : gapLitInv bytes litBytes cur base litBase t n ln m mem r s c)
    (hbase : base = b + t)
    (hbytes : gapBytesAt mem bytes b ip) (hlt : t + n ≤ ip)
    (hlit : gapBytesAt mem litBytes litBase ln) :
    step calls odGapRecoverBody s =
      .jump (stateAt (gapLitBodyEnv s.env base litBase (BitVec.ofNat 64 c) c
          (gapByte (bytes.getD (t + c) 0)) (gapByte (litBytes.getD c 0)))
        { s with pc := if evalICmp .eq (gapByte (bytes.getD (t + c) 0))
                            (gapByte (litBytes.getD c 0)) = 1
                         then "for.inc.i" else "if.then57",
                 pre := some "for.body.i" }) := by
  obtain ⟨hpc, hmem, harr, hlit0, hcond, hsub, hln0, ht0, hcur, hcar,
    hmn, hml, hcm, hm63, hpfx, _⟩ := hinv
  have hse : ((BitVec.ofNat 64 c).signExtend 64).toNat = c :=
    gap_signExtend_ofNat c (by omega)
  have hx0 : readBytes mem (b + (t + c)) 1 =
      some (natToBytes (gapByte (bytes.getD (t + c) 0)).toNat 1) :=
    gap_readOne hbytes (c := t + c) (by omega) rfl
  have haddr : base + c = b + (t + c) := by omega
  have hx : readBytes s.mem (base + c) 1 =
      some (natToBytes (gapByte (bytes.getD (t + c) 0)).toNat 1) := by
    rw [hmem, haddr]; exact hx0
  have hy0 : readBytes mem (litBase + c) 1 =
      some (natToBytes (gapByte (litBytes.getD c 0)).toNat 1) :=
    gap_readOne hlit (c := c) (by omega) rfl
  have hy : readBytes s.mem (litBase + c) 1 =
      some (natToBytes (gapByte (litBytes.getD c 0)).toNat 1) := by
    rw [hmem]; exact hy0
  rcases hcar with ⟨hpre, hc0⟩ | ⟨hpre, hinc⟩
  · subst hc0
    have hincL : phiIncoming "if.end48"
        [("for.inc.i", Operand.reg "%inc.i"),
         ("if.end48", Operand.imm (Const.int 64 0x0000000000000000#64))] =
        some (Operand.imm (Const.int 64 0x0000000000000000#64)) := by decide
    have hopL : evalOperand (stateAt s.env s)
        (Operand.imm (Const.int 64 0x0000000000000000#64)) =
        some (.int 64 (BitVec.ofNat 64 0)) := by
      simp only [evalOperand, stateAt, Const.toValue]
    simpa only [stateAt] using
      gapLit_step_forBody (calls := calls) (env := s.env) (s := s) (p := "if.end48")
        (base := base) (litBase := litBase) (iw := BitVec.ofNat 64 0) (se := 0)
        (x := gapByte (bytes.getD (t + 0) 0)) (y := gapByte (litBytes.getD 0 0))
        (op := Operand.imm (Const.int 64 0x0000000000000000#64))
        hpc hpre hincL hopL harr hlit0 (gap_signExtend_ofNat 0 (by decide))
        (by decide) hx hy
  · have hincL : phiIncoming "for.inc.i"
        [("for.inc.i", Operand.reg "%inc.i"),
         ("if.end48", Operand.imm (Const.int 64 0x0000000000000000#64))] =
        some (Operand.reg "%inc.i") := by decide
    have hopL : evalOperand (stateAt s.env s) (Operand.reg "%inc.i") =
        some (.int 64 (BitVec.ofNat 64 c)) := by
      simp only [evalOperand, stateAt]
      rw [hinc]
    simpa only [stateAt] using
      gapLit_step_forBody (calls := calls) (env := s.env) (s := s) (p := "for.inc.i")
        (base := base) (litBase := litBase) (iw := BitVec.ofNat 64 c) (se := c)
        (x := gapByte (bytes.getD (t + c) 0)) (y := gapByte (litBytes.getD c 0))
        (op := Operand.reg "%inc.i")
        hpc hpre hincL hopL harr hlit0 hse (by omega) hx hy

/-- **The compare loop as a `BoundLoop`.**  The bound is `m - 1`, the last
compared index; the exit is the differing byte or the bound's last index, and
the loop's two blocks write nothing. -/
def gapLitLoop (calls : Calls) (bytes litBytes : List UInt8)
    (cur base litBase b t n ln m ip : Nat) (mem : Mem)
    (r : Nat) (hrec : readBytes mem (cur + 1112) 8 = some (natToBytes r 8))
    (hr64 : r < 2 ^ 64)
    (hbase : base = b + t)
    (hbytes : gapBytesAt mem bytes b ip) (hlt : t + n ≤ ip)
    (hlit : gapBytesAt mem litBytes litBase ln) : BoundLoop calls odGapRecoverBody where
  head := "for.body.i"
  exitBlock := "for.end.i"
  N := m - 1
  cost := 2
  Inv := gapLitInv bytes litBytes cur base litBase t n ln m mem
  atBound := gapLitAtBound bytes litBytes t m
  Exit := gapLitExitBlock
  ExitWord := gapLitExitWord bytes litBytes cur t n ln m mem
  step_exit := by
    intro r s c hinv hat
    have hs := gapLit_head_step (calls := calls) (mem := mem) (b := b) (ip := ip)
      hinv hbase hbytes hlt hlit
    obtain ⟨hpc, hmem, harr, hlit0, hcond, hsub, hln0, ht0, hcur, hcar,
      hmn, hml, hcm, hm63, hpfx, _⟩ := hinv
    by_cases hbe : (gapByte (bytes.getD (t + c) 0)) = (gapByte (litBytes.getD c 0))
    · -- equal bytes: the head advances, and the test at `for.inc.i` exits at the bound
      have hbit : evalICmp .eq (gapByte (bytes.getD (t + c) 0))
          (gapByte (litBytes.getD c 0)) = 1#1 := gapLit_icmp_eq_one hbe
      have hc1 : c + 1 = m := by
        unfold gapLitAtBound at hat
        rcases Bool.or_eq_true_iff.mp hat with hdiff | hbound
        · exact absurd (gapLit_gapByte_eq.mp hbe) (of_decide_eq_true hdiff)
        · exact of_decide_eq_true hbound
      have hc64 : c + 1 < 2 ^ 64 := by omega
      let s1 : State := stateAt (gapLitBodyEnv s.env base litBase (BitVec.ofNat 64 c) c
          (gapByte (bytes.getD (t + c) 0)) (gapByte (litBytes.getD c 0)))
        { s with pc := "for.inc.i", pre := some "for.body.i" }
      have hs1 : step calls odGapRecoverBody s = .jump s1 := by
        rw [hs, hbit]; simp [s1]
      have hi1 : lookupName s1.env "%i.029.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
        simp only [s1, stateAt, gapLitBodyEnv]; block_lk
      have hm1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)) := by
        simp only [s1, stateAt, gapLitBodyEnv]; block_lk
      have hs2 := gapLit_step_forInc (calls := calls) (env := s1.env) (s := s1)
        (iw := BitVec.ofNat 64 c) (mw := BitVec.ofNat 64 m) rfl hi1 hm1
      have hbit2 : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 m) = 1#1 := by
        rw [gap_ofNat64_add_one hc64, hc1]; exact gapLit_icmp_eq_one rfl
      let e : State := stateAt (gapLitIncEnv s1.env (BitVec.ofNat 64 c) (BitVec.ofNat 64 m))
        { s1 with pc := "for.end.i", pre := some "for.inc.i" }
      have hs2' : step calls odGapRecoverBody s1 = .jump e := by
        have h := hs2
        rw [hbit2] at h
        exact h
      refine ⟨e, 2, by decide, Or.inr rfl, ?_, ?_⟩
      · unfold gapLitExitWord
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, rfl, ?_, ?_⟩, ?_⟩
        · simp [e, s1, stateAt, hmem]
        · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
        · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
        · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
        · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
        · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
        · -- `%inc.i` carries the bound
          simp only [e, stateAt, gapLitIncEnv]
          rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self,
            gap_ofNat64_add_one hc64, hc1]
        · -- the prefix through the matched byte
          intro j hj
          have hjle : j ≤ c := by omega
          rcases Nat.lt_or_eq_of_le hjle with hjc | hjc
          · exact hpfx j hjc
          · subst hjc
            exact gapLit_gapByte_eq.1 hbe
        · -- the record word the refusal sites read
          exact ⟨_, hrec, hr64⟩
      · intro k
        rw [show 2 + k = 1 + (1 + k) from by omega,
          runFuel_jump_prefix hs1 (1 + k), runFuel_jump_prefix hs2' k]
    · -- differing bytes: the head refuses at this index
      have hne : bytes.getD (t + c) 0 ≠ litBytes.getD c 0 :=
        fun hh => hbe (by rw [hh])
      have hbit : evalICmp .eq (gapByte (bytes.getD (t + c) 0))
          (gapByte (litBytes.getD c 0)) = 0#1 :=
        gap_eq_zero (fun hh => hbe hh)
      let e : State := stateAt (gapLitBodyEnv s.env base litBase (BitVec.ofNat 64 c) c
          (gapByte (bytes.getD (t + c) 0)) (gapByte (litBytes.getD c 0)))
        { s with pc := "if.then57", pre := some "for.body.i" }
      have hs' : step calls odGapRecoverBody s = .jump e := by
        rw [hs, hbit]; simp [e]
      refine ⟨e, 1, by decide, Or.inl rfl, ?_, ?_⟩
      · unfold gapLitExitWord
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inl ⟨c, rfl, rfl, ?_, hcm, hpfx, hne⟩, ?_⟩
        · simp [e, stateAt, hmem]
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · simp only [e, stateAt, gapLitBodyEnv]; block_lk
        · exact ⟨_, hrec, hr64⟩
      · intro k
        rw [show 1 + k = 1 + k from rfl, runFuel_jump_prefix hs' k]
  step_loop := by
    intro r s c hinv hat
    have hs := gapLit_head_step (calls := calls) (mem := mem) (b := b) (ip := ip)
      hinv hbase hbytes hlt hlit
    obtain ⟨hpc, hmem, harr, hlit0, hcond, hsub, hln0, ht0, hcur, hcar,
      hmn, hml, hcm, hm63, hpfx, hbud⟩ := hinv
    unfold gapLitAtBound at hat
    rcases Bool.or_eq_false_iff.mp hat with ⟨hdiff, hbound⟩
    have hbe : gapByte (bytes.getD (t + c) 0) = gapByte (litBytes.getD c 0) := by
      by_contra hne
      exact of_decide_eq_false hdiff (fun hh => hne (by rw [hh]))
    have hne_m : c + 1 ≠ m := of_decide_eq_false hbound
    have hbit : evalICmp .eq (gapByte (bytes.getD (t + c) 0))
        (gapByte (litBytes.getD c 0)) = 1#1 := gapLit_icmp_eq_one hbe
    have hc64 : c + 1 < 2 ^ 64 := by omega
    let s1 : State := stateAt (gapLitBodyEnv s.env base litBase (BitVec.ofNat 64 c) c
        (gapByte (bytes.getD (t + c) 0)) (gapByte (litBytes.getD c 0)))
      { s with pc := "for.inc.i", pre := some "for.body.i" }
    have hs1 : step calls odGapRecoverBody s = .jump s1 := by
      rw [hs, hbit]; simp [s1]
    have hi1 : lookupName s1.env "%i.029.i" = some (.int 64 (BitVec.ofNat 64 c)) := by
      simp only [s1, stateAt, gapLitBodyEnv]; block_lk
    have hm1 : lookupName s1.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)) := by
      simp only [s1, stateAt, gapLitBodyEnv]; block_lk
    have hs2 := gapLit_step_forInc (calls := calls) (env := s1.env) (s := s1)
      (iw := BitVec.ofNat 64 c) (mw := BitVec.ofNat 64 m) rfl hi1 hm1
    have hbit2 : evalICmp .eq (BitVec.ofNat 64 c + 1) (BitVec.ofNat 64 m) = 0#1 := by
      rw [gap_ofNat64_add_one hc64]
      exact gap_eq_zero (fun hh => hne_m (by
        have h2 := congrArg BitVec.toNat hh
        rw [gap_word64 hc64, gap_word64 (show m < 2 ^ 64 by omega)] at h2
        exact h2))
    let e : State := stateAt (gapLitIncEnv s1.env (BitVec.ofNat 64 c) (BitVec.ofNat 64 m))
      { s1 with pc := "for.body.i", pre := some "for.inc.i" }
    have hs2' : step calls odGapRecoverBody s1 = .jump e := by
      have h := hs2
      rw [hbit2] at h
      exact h
    refine ⟨e, c + 1, 2, by decide, rfl, by omega, ?_, ?_⟩
    · -- the invariant one counter further
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Or.inr ⟨rfl, ?_⟩, hmn, hml,
        by omega, hm63, ?_, ?_⟩
      · simp [e, s1, stateAt, hmem]
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · simp only [e, s1, stateAt, gapLitIncEnv, gapLitBodyEnv]; block_lk
      · -- `%inc.i` is the successor word
        simp only [e, stateAt, gapLitIncEnv]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self,
          gap_ofNat64_add_one hc64]
      · intro j hj
        by_cases hjc : j < c
        · exact hpfx j hjc
        · have hje : j = c := by omega
          subst hje
          exact gapLit_gapByte_eq.1 hbe
      · omega
    · intro k
      rw [show 2 + k = 1 + (1 + k) from by omega,
        runFuel_jump_prefix hs1 (1 + k), runFuel_jump_prefix hs2' k]
  exit_at_zero := by
    intro s c hinv
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcm, _, _, hbud⟩ := hinv
    have hc1 : c + 1 = m := by
      have : m - 1 ≤ c := by omega
      omega
    unfold gapLitAtBound
    rw [Bool.or_eq_true_iff]
    right
    simpa only [decide_eq_true_iff] using hc1
  budget := by
    intro r s c hinv
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hcm, _, _, hbud⟩ := hinv
    exact ⟨by omega, hbud⟩

/-- The loop's first visit: the carried counter is zero and the budget is the
whole bound. -/
theorem gapLitInv_seed {bytes litBytes : List UInt8} {cur base litBase t n ln m : Nat}
    {mem : Mem} {s : State}
    (hm : 0 < m) (hpc : s.pc = "for.body.i") (hpre : s.pre = some "if.end48")
    (hmem : s.mem = mem)
    (harr : lookupName s.env "%arrayidx9" = some (.ptr base))
    (hlit0 : lookupName s.env "%lit.0" = some (.ptr litBase))
    (hcond : lookupName s.env "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)))
    (hsub : lookupName s.env "%sub54" = some (.int 64 (BitVec.ofNat 64 n)))
    (hln0 : lookupName s.env "%ln.0" = some (.int 64 (BitVec.ofNat 64 ln)))
    (ht0 : lookupName s.env "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)))
    (hcur : lookupName s.env "%c" = some (.ptr cur))
    (hmn : m ≤ n) (hml : m ≤ ln) (hm63 : m ≤ 2 ^ 63) :
    gapLitInv bytes litBytes cur base litBase t n ln m mem (m - 1) s 0 :=
  ⟨hpc, hmem, harr, hlit0, hcond, hsub, hln0, ht0, hcur, Or.inl ⟨hpre, rfl⟩,
    hmn, hml, hm, hm63, by intro j hj; omega, by omega⟩

/-- **The compare loop's run.**  From its head with the whole bound as budget,
the run reaches one of the two exit blocks within `((m - 1) + 1) * 2` steps,
writes nothing, and satisfies the exit word. -/
theorem gapLitLoop_run {calls : Calls} {bytes litBytes : List UInt8}
    {cur base litBase b t n ln m ip : Nat} {mem : Mem}
    {r : Nat} (hrec : readBytes mem (cur + 1112) 8 = some (natToBytes r 8))
    (hr64 : r < 2 ^ 64)
    (hbase : base = b + t)
    (hbytes : gapBytesAt mem bytes b ip) (hlt : t + n ≤ ip)
    (hlit : gapBytesAt mem litBytes litBase ln)
    (s : State) (hinv : gapLitInv bytes litBytes cur base litBase t n ln m mem (m - 1) s 0)
    (k : Nat) :
    ∃ (e : State) (j : Nat), j ≤ ((m - 1) + 1) * 2 ∧ gapLitExitBlock e ∧
      gapLitExitWord bytes litBytes cur t n ln m mem e ∧
      runFuel calls (j + k) odGapRecoverBody s = runFuel calls k odGapRecoverBody e :=
  (gapLitLoop calls bytes litBytes cur base litBase b t n ln m ip mem
    r hrec hr64 hbase hbytes hlt hlit).run s 0 hinv k

/-! ### The byte dispatch, from `if.else`

`if.else` is the number test's false arm: it branches to `NodeBlock15`, whose two
signed byte comparisons select a leaf block, and each leaf compares the byte with
its literal's first character.  `icmp slt i8` is signed, so a byte at or above
`0x80` is negative and takes the left edge; the three accepted bytes are `0x74`
(`"true"`), `0x66` (`"false"`) and `0x6e` (`"null"`), and every other byte falls
to `if.else43`.

The three accepted bytes reach `if.end48` — `0x74` and `0x66` in four control
steps, `0x6e` in five — and any other byte reaches `cleanup82` through
`if.else43` in at most five, writing the tag-3 record at `%t.0.val`. -/

/-- A one-bit comparison whose value is one takes the `then` branch. -/
@[simp] theorem gapLit_ite_one {a b : String} :
    (if (1#1 : BitVec 1) = 1 then a else b) = a := by
  simp only [show ((1#1 : BitVec 1) = 1) = True from by decide, ite_true]

/-- A one-bit comparison whose value is zero takes the `else` branch. -/
@[simp] theorem gapLit_ite_zero {a b : String} :
    (if (0#1 : BitVec 1) = 1 then a else b) = b := by
  simp only [show ((0#1 : BitVec 1) = 1) = False from by decide, ite_false]

/-- `if.else43`'s record cells, at the block's own environment. -/
theorem gapLit_else43_cells (env : Env) (cur r : Nat) :
    lookupName (gapLitElse43Env env cur r) "%msg2.i130" = some (.ptr (r + 16)) ∧
    lookupName (gapLitElse43Env env cur r) "%off1.i129" = some (.ptr (r + 8)) ∧
    lookupName (gapLitElse43Env env cur r) "%11" = some (.ptr r) := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp only [gapLitElse43Env]; block_lk)

/-- **`"true"`'s dispatch.**  `0x74` is not below `110`, not below `116`, and
equal to `116`: `NodeBlock15`, `NodeBlock13` and `LeafBlock11` reach `if.end48`
in four control steps. -/
theorem gapLit_dispatch_true {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.else")
    (h7 : lookupName env "%7" = some (.int 8 (BitVec.ofNat 8 116))) :
    ∀ k, runFuel calls (4 + k) odGapRecoverBody (stateAt env s) =
      runFuel calls k odGapRecoverBody
        (stateAt (("%SwitchLeaf12", .int 1 1#1) :: ("%Pivot14", .int 1 0#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
          { s with pc := "if.end48", pre := some "LeafBlock11" }) := by
  intro k
  have hb110 : evalICmp .slt (BitVec.ofNat 8 116) (BitVec.ofNat 8 110) = 0#1 := by decide
  have hb116 : evalICmp .slt (BitVec.ofNat 8 116) (BitVec.ofNat 8 116) = 0#1 := by decide
  have heq : evalICmp .eq (BitVec.ofNat 8 116) (BitVec.ofNat 8 116) = 1#1 := by decide
  have h7₂ : lookupName (("%Pivot16", .int 1 0#1) :: env) "%7" =
      some (.int 8 (BitVec.ofNat 8 116)) := by
    rw [lookupName_cons_ne _ _ (by decide)]; exact h7
  have h7₃ : lookupName (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
      "%7" = some (.int 8 (BitVec.ofNat 8 116)) := by
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h7
  have h1 : step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) :=
    gapLit_step_ifElse (calls := calls) hpc
  have h2 : step calls odGapRecoverBody
      (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
      .jump (stateAt (("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) := by
    have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
      (s := { s with pc := "NodeBlock15", pre := some "if.else" })
      (x := BitVec.ofNat 8 116) rfl h7
    simpa only [hb110, gapLit_ite_zero, stateAt] using hh
  have h3 : step calls odGapRecoverBody
      (stateAt (("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) =
      .jump (stateAt (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) := by
    have hh := gapLit_step_NodeBlock13 (calls := calls)
      (env := ("%Pivot16", .int 1 0#1) :: env)
      (s := { s with pc := "NodeBlock13", pre := some "NodeBlock15" })
      (x := BitVec.ofNat 8 116) rfl h7₂
    simpa only [hb116, gapLit_ite_zero, stateAt] using hh
  have h4 : step calls odGapRecoverBody
      (stateAt (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) =
      .jump (stateAt (("%SwitchLeaf12", .int 1 1#1) :: ("%Pivot14", .int 1 0#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "if.end48", pre := some "LeafBlock11" }) := by
    have hh := gapLit_step_LeafBlock11 (calls := calls)
      (env := ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
      (s := { s with pc := "LeafBlock11", pre := some "NodeBlock13" })
      (x := BitVec.ofNat 8 116) rfl h7₃
    simpa only [heq, gapLit_ite_one, stateAt] using hh
  rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
    runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h2 (1 + (1 + k)),
    runFuel_jump_prefix h3 (1 + k),
    runFuel_jump_prefix h4 k]

/-- **`"false"`'s dispatch.**  `0x66` is below `110` and equal to `102`:
`NodeBlock15` and `LeafBlock7` reach `if.end48` through `if.then37` in four
control steps. -/
theorem gapLit_dispatch_false {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.else")
    (h7 : lookupName env "%7" = some (.int 8 (BitVec.ofNat 8 102))) :
    ∀ k, runFuel calls (4 + k) odGapRecoverBody (stateAt env s) =
      runFuel calls k odGapRecoverBody
        (stateAt (("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: env)
          { s with pc := "if.end48", pre := some "if.then37" }) := by
  intro k
  have hb110 : evalICmp .slt (BitVec.ofNat 8 102) (BitVec.ofNat 8 110) = 1#1 := by decide
  have heq : evalICmp .eq (BitVec.ofNat 8 102) (BitVec.ofNat 8 102) = 1#1 := by decide
  have h7₂ : lookupName (("%Pivot16", .int 1 1#1) :: env) "%7" =
      some (.int 8 (BitVec.ofNat 8 102)) := by
    rw [lookupName_cons_ne _ _ (by decide)]; exact h7
  have h1 : step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) :=
    gapLit_step_ifElse (calls := calls) hpc
  have h2 : step calls odGapRecoverBody
      (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
      .jump (stateAt (("%Pivot16", .int 1 1#1) :: env)
        { s with pc := "LeafBlock7", pre := some "NodeBlock15" }) := by
    have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
      (s := { s with pc := "NodeBlock15", pre := some "if.else" })
      (x := BitVec.ofNat 8 102) rfl h7
    simpa only [hb110, gapLit_ite_one, stateAt] using hh
  have h3 : step calls odGapRecoverBody
      (stateAt (("%Pivot16", .int 1 1#1) :: env)
        { s with pc := "LeafBlock7", pre := some "NodeBlock15" }) =
      .jump (stateAt (("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: env)
        { s with pc := "if.then37", pre := some "LeafBlock7" }) := by
    have hh := gapLit_step_LeafBlock7 (calls := calls)
      (env := ("%Pivot16", .int 1 1#1) :: env)
      (s := { s with pc := "LeafBlock7", pre := some "NodeBlock15" })
      (x := BitVec.ofNat 8 102) rfl h7₂
    simpa only [heq, gapLit_ite_one, stateAt] using hh
  have h4 : step calls odGapRecoverBody
      (stateAt (("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: env)
        { s with pc := "if.then37", pre := some "LeafBlock7" }) =
      .jump (stateAt (("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: env)
        { s with pc := "if.end48", pre := some "if.then37" }) :=
    gapLit_step_ifThen37 (calls := calls)
      (env := ("%SwitchLeaf8", .int 1 1#1) :: ("%Pivot16", .int 1 1#1) :: env)
      (s := { s with pc := "if.then37", pre := some "LeafBlock7" }) rfl
  rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
    runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h2 (1 + (1 + k)),
    runFuel_jump_prefix h3 (1 + k),
    runFuel_jump_prefix h4 k]

/-- **`"null"`'s dispatch.**  `0x6e` is not below `110`, is below `116`, and is
equal to `110`: `NodeBlock15`, `NodeBlock13` and `LeafBlock9` reach `if.end48`
through `if.then42` in five control steps. -/
theorem gapLit_dispatch_null {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.else")
    (h7 : lookupName env "%7" = some (.int 8 (BitVec.ofNat 8 110))) :
    ∀ k, runFuel calls (5 + k) odGapRecoverBody (stateAt env s) =
      runFuel calls k odGapRecoverBody
        (stateAt (("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
          { s with pc := "if.end48", pre := some "if.then42" }) := by
  intro k
  have hb110 : evalICmp .slt (BitVec.ofNat 8 110) (BitVec.ofNat 8 110) = 0#1 := by decide
  have hb116 : evalICmp .slt (BitVec.ofNat 8 110) (BitVec.ofNat 8 116) = 1#1 := by decide
  have heq : evalICmp .eq (BitVec.ofNat 8 110) (BitVec.ofNat 8 110) = 1#1 := by decide
  have h7₂ : lookupName (("%Pivot16", .int 1 0#1) :: env) "%7" =
      some (.int 8 (BitVec.ofNat 8 110)) := by
    rw [lookupName_cons_ne _ _ (by decide)]; exact h7
  have h7₃ : lookupName (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
      "%7" = some (.int 8 (BitVec.ofNat 8 110)) := by
    rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
    exact h7
  have h1 : step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) :=
    gapLit_step_ifElse (calls := calls) hpc
  have h2 : step calls odGapRecoverBody
      (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
      .jump (stateAt (("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) := by
    have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
      (s := { s with pc := "NodeBlock15", pre := some "if.else" })
      (x := BitVec.ofNat 8 110) rfl h7
    simpa only [hb110, gapLit_ite_zero, stateAt] using hh
  have h3 : step calls odGapRecoverBody
      (stateAt (("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) =
      .jump (stateAt (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) := by
    have hh := gapLit_step_NodeBlock13 (calls := calls)
      (env := ("%Pivot16", .int 1 0#1) :: env)
      (s := { s with pc := "NodeBlock13", pre := some "NodeBlock15" })
      (x := BitVec.ofNat 8 110) rfl h7₂
    simpa only [hb116, gapLit_ite_one, stateAt] using hh
  have h4 : step calls odGapRecoverBody
      (stateAt (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) =
      .jump (stateAt (("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "if.then42", pre := some "LeafBlock9" }) := by
    have hh := gapLit_step_LeafBlock9 (calls := calls)
      (env := ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
      (s := { s with pc := "LeafBlock9", pre := some "NodeBlock13" })
      (x := BitVec.ofNat 8 110) rfl h7₃
    simpa only [heq, gapLit_ite_one, stateAt] using hh
  have h5 : step calls odGapRecoverBody
      (stateAt (("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "if.then42", pre := some "LeafBlock9" }) =
      .jump (stateAt (("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
          ("%Pivot16", .int 1 0#1) :: env)
        { s with pc := "if.end48", pre := some "if.then42" }) :=
    gapLit_step_ifThen42 (calls := calls)
      (env := ("%SwitchLeaf10", .int 1 1#1) :: ("%Pivot14", .int 1 1#1) ::
        ("%Pivot16", .int 1 0#1) :: env)
      (s := { s with pc := "if.then42", pre := some "LeafBlock9" }) rfl
  rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
    runFuel_jump_prefix h1 (1 + (1 + (1 + (1 + k)))),
    runFuel_jump_prefix h2 (1 + (1 + (1 + k))),
    runFuel_jump_prefix h3 (1 + (1 + k)),
    runFuel_jump_prefix h4 (1 + k),
    runFuel_jump_prefix h5 k]

/-! ### The refusal

Any byte other than the three literals' first characters falls through to
`if.else43` by whichever of the switch's three leaves the signed comparisons
select, and writes the tag-3 record at `%t.0.val`.  The signed split matters: a
byte at or above `0x80` is negative under `icmp slt i8`, so it takes the left
edge however large its unsigned value is. -/

theorem gapLit_dispatch_refuse {calls : Calls} {env : Env} {s : State}
    {cur r : Nat} {t : BitVec 64} {x : BitVec 8}
    (hpc : s.pc = "if.else")
    (h7 : lookupName env "%7" = some (.int 8 x))
    (h102 : x ≠ BitVec.ofNat 8 102) (h110 : x ≠ BitVec.ofNat 8 110)
    (h116 : x ≠ BitVec.ofNat 8 116)
    (hc : lookupName env "%c" = some (.ptr cur))
    (hrec : readBytes s.mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (ht : lookupName env "%t.0.val" = some (.int 64 t)) :
    ∃ (e : State) (j : Nat), j ≤ 5 ∧ e.pc = "cleanup82" ∧ e.pre = some "if.else43" ∧
      e.mem = writeBytes
        (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8) (natToBytes t.toNat 8))
        (r + 16) (natToBytes 3 8) ∧
      lookupName e.env "%msg2.i130" = some (.ptr (r + 16)) ∧
      lookupName e.env "%off1.i129" = some (.ptr (r + 8)) ∧
      lookupName e.env "%11" = some (.ptr r) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody (stateAt env s) =
        runFuel calls k odGapRecoverBody e := by
  have heq102 : evalICmp .eq x (BitVec.ofNat 8 102) = 0#1 := gap_eq_zero h102
  have heq110 : evalICmp .eq x (BitVec.ofNat 8 110) = 0#1 := gap_eq_zero h110
  have heq116 : evalICmp .eq x (BitVec.ofNat 8 116) = 0#1 := gap_eq_zero h116
  have h1 : step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) :=
    gapLit_step_ifElse (calls := calls) hpc
  have hb110c : evalICmp .slt x (BitVec.ofNat 8 110) = 1#1 ∨
      evalICmp .slt x (BitVec.ofNat 8 110) = 0#1 := by
    rcases bitVec1_eq_zero_or_one (evalICmp .slt x (BitVec.ofNat 8 110)) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases hb110c with hb110 | hb110
  · -- `%7 < 110`: `LeafBlock7` refuses
    have h7₂ : lookupName (("%Pivot16", .int 1 1#1) :: env) "%7" = some (.int 8 x) := by
      rw [lookupName_cons_ne _ _ (by decide)]; exact h7
    have h2 : step calls odGapRecoverBody
        (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
        .jump (stateAt (("%Pivot16", .int 1 1#1) :: env)
          { s with pc := "LeafBlock7", pre := some "NodeBlock15" }) := by
      have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
        (s := { s with pc := "NodeBlock15", pre := some "if.else" }) (x := x) rfl h7
      simpa only [hb110, gapLit_ite_one, stateAt] using hh
    have h3 : step calls odGapRecoverBody
        (stateAt (("%Pivot16", .int 1 1#1) :: env)
          { s with pc := "LeafBlock7", pre := some "NodeBlock15" }) =
        .jump (stateAt (("%SwitchLeaf8", .int 1 0#1) :: ("%Pivot16", .int 1 1#1) :: env)
          { s with pc := "if.else43", pre := some "LeafBlock7" }) := by
      have hh := gapLit_step_LeafBlock7 (calls := calls)
        (env := ("%Pivot16", .int 1 1#1) :: env)
        (s := { s with pc := "LeafBlock7", pre := some "NodeBlock15" }) (x := x) rfl h7₂
      simpa only [heq102, gapLit_ite_zero, stateAt] using hh
    have hc' : lookupName (("%SwitchLeaf8", .int 1 0#1) ::
        ("%Pivot16", .int 1 1#1) :: env) "%c" = some (.ptr cur) := by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact hc
    have ht' : lookupName (("%SwitchLeaf8", .int 1 0#1) ::
        ("%Pivot16", .int 1 1#1) :: env) "%t.0.val" = some (.int 64 t) := by
      rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
      exact ht
    have h4 : step calls odGapRecoverBody
        (stateAt (("%SwitchLeaf8", .int 1 0#1) :: ("%Pivot16", .int 1 1#1) :: env)
          { s with pc := "if.else43", pre := some "LeafBlock7" }) =
        .jump (stateAt
          (gapLitElse43Env (("%SwitchLeaf8", .int 1 0#1) ::
            ("%Pivot16", .int 1 1#1) :: env) cur r)
          (gapLitSet s "cleanup82" "if.else43" (writeBytes
            (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8) (natToBytes t.toNat 8))
            (r + 16) (natToBytes 3 8)))) :=
      gapLit_step_ifElse43 (calls := calls)
        (env := ("%SwitchLeaf8", .int 1 0#1) :: ("%Pivot16", .int 1 1#1) :: env)
        (s := { s with pc := "if.else43", pre := some "LeafBlock7" })
        rfl hc' hrec hr64 ht'
    refine ⟨stateAt (gapLitElse43Env (("%SwitchLeaf8", .int 1 0#1) ::
        ("%Pivot16", .int 1 1#1) :: env) cur r)
        (gapLitSet s "cleanup82" "if.else43" (writeBytes
          (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8) (natToBytes t.toNat 8))
          (r + 16) (natToBytes 3 8))),
      4, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [stateAt, gapLitSet]
    · simp only [stateAt, gapLitSet]
    · simp only [stateAt, gapLitSet]
    · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).1
    · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.1
    · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.2
    · intro k
      rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
        runFuel_jump_prefix h1 (1 + (1 + (1 + k))),
        runFuel_jump_prefix h2 (1 + (1 + k)),
        runFuel_jump_prefix h3 (1 + k),
        runFuel_jump_prefix h4 k]
  · have hb116c : evalICmp .slt x (BitVec.ofNat 8 116) = 1#1 ∨
        evalICmp .slt x (BitVec.ofNat 8 116) = 0#1 := by
      rcases bitVec1_eq_zero_or_one (evalICmp .slt x (BitVec.ofNat 8 116)) with h | h
      · exact Or.inr h
      · exact Or.inl h
    rcases hb116c with hb116 | hb116
    · -- `110 ≤ %7 < 116`: `LeafBlock9` refuses
      have h7₂ : lookupName (("%Pivot16", .int 1 0#1) :: env) "%7" = some (.int 8 x) := by
        rw [lookupName_cons_ne _ _ (by decide)]; exact h7
      have h7₃ : lookupName (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
          "%7" = some (.int 8 x) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact h7
      have h2 : step calls odGapRecoverBody
          (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
          .jump (stateAt (("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) := by
        have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
          (s := { s with pc := "NodeBlock15", pre := some "if.else" }) (x := x) rfl h7
        simpa only [hb110, gapLit_ite_zero, stateAt] using hh
      have h3 : step calls odGapRecoverBody
          (stateAt (("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) =
          .jump (stateAt (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) := by
        have hh := gapLit_step_NodeBlock13 (calls := calls)
          (env := ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) (x := x) rfl h7₂
        simpa only [hb116, gapLit_ite_one, stateAt] using hh
      have h4 : step calls odGapRecoverBody
          (stateAt (("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) =
          .jump (stateAt
            (("%SwitchLeaf10", .int 1 0#1) :: ("%Pivot14", .int 1 1#1) ::
              ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "if.else43", pre := some "LeafBlock9" }) := by
        have hh := gapLit_step_LeafBlock9 (calls := calls)
          (env := ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "LeafBlock9", pre := some "NodeBlock13" }) (x := x) rfl h7₃
        simpa only [heq110, gapLit_ite_zero, stateAt] using hh
      have hc' : lookupName (("%SwitchLeaf10", .int 1 0#1) ::
          ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env) "%c" =
          some (.ptr cur) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hc
      have ht' : lookupName (("%SwitchLeaf10", .int 1 0#1) ::
          ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env) "%t.0.val" =
          some (.int 64 t) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact ht
      have h5 : step calls odGapRecoverBody
          (stateAt (("%SwitchLeaf10", .int 1 0#1) :: ("%Pivot14", .int 1 1#1) ::
              ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "if.else43", pre := some "LeafBlock9" }) =
          .jump (stateAt
            (gapLitElse43Env (("%SwitchLeaf10", .int 1 0#1) ::
              ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env) cur r)
            (gapLitSet s "cleanup82" "if.else43" (writeBytes
              (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8)
                (natToBytes t.toNat 8))
              (r + 16) (natToBytes 3 8)))) :=
        gapLit_step_ifElse43 (calls := calls)
          (env := ("%SwitchLeaf10", .int 1 0#1) :: ("%Pivot14", .int 1 1#1) ::
            ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "if.else43", pre := some "LeafBlock9" })
          rfl hc' hrec hr64 ht'
      refine ⟨stateAt (gapLitElse43Env (("%SwitchLeaf10", .int 1 0#1) ::
          ("%Pivot14", .int 1 1#1) :: ("%Pivot16", .int 1 0#1) :: env) cur r)
          (gapLitSet s "cleanup82" "if.else43" (writeBytes
            (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8)
              (natToBytes t.toNat 8))
            (r + 16) (natToBytes 3 8))),
        5, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stateAt, gapLitSet]
      · simp only [stateAt, gapLitSet]
      · simp only [stateAt, gapLitSet]
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).1
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.1
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.2
      · intro k
        rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
          runFuel_jump_prefix h1 (1 + (1 + (1 + (1 + k)))),
          runFuel_jump_prefix h2 (1 + (1 + (1 + k))),
          runFuel_jump_prefix h3 (1 + (1 + k)),
          runFuel_jump_prefix h4 (1 + k),
          runFuel_jump_prefix h5 k]
    · -- `116 ≤ %7`: `LeafBlock11` refuses
      have h7₂ : lookupName (("%Pivot16", .int 1 0#1) :: env) "%7" = some (.int 8 x) := by
        rw [lookupName_cons_ne _ _ (by decide)]; exact h7
      have h7₃ : lookupName (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
          "%7" = some (.int 8 x) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
        exact h7
      have h2 : step calls odGapRecoverBody
          (stateAt env { s with pc := "NodeBlock15", pre := some "if.else" }) =
          .jump (stateAt (("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) := by
        have hh := gapLit_step_NodeBlock15 (calls := calls) (env := env)
          (s := { s with pc := "NodeBlock15", pre := some "if.else" }) (x := x) rfl h7
        simpa only [hb110, gapLit_ite_zero, stateAt] using hh
      have h3 : step calls odGapRecoverBody
          (stateAt (("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) =
          .jump (stateAt (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) := by
        have hh := gapLit_step_NodeBlock13 (calls := calls)
          (env := ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "NodeBlock13", pre := some "NodeBlock15" }) (x := x) rfl h7₂
        simpa only [hb116, gapLit_ite_zero, stateAt] using hh
      have h4 : step calls odGapRecoverBody
          (stateAt (("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) =
          .jump (stateAt
            (("%SwitchLeaf12", .int 1 0#1) :: ("%Pivot14", .int 1 0#1) ::
              ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "if.else43", pre := some "LeafBlock11" }) := by
        have hh := gapLit_step_LeafBlock11 (calls := calls)
          (env := ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "LeafBlock11", pre := some "NodeBlock13" }) (x := x) rfl h7₃
        simpa only [heq116, gapLit_ite_zero, stateAt] using hh
      have hc' : lookupName (("%SwitchLeaf12", .int 1 0#1) ::
          ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env) "%c" =
          some (.ptr cur) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact hc
      have ht' : lookupName (("%SwitchLeaf12", .int 1 0#1) ::
          ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env) "%t.0.val" =
          some (.int 64 t) := by
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
          lookupName_cons_ne _ _ (by decide)]
        exact ht
      have h5 : step calls odGapRecoverBody
          (stateAt (("%SwitchLeaf12", .int 1 0#1) :: ("%Pivot14", .int 1 0#1) ::
              ("%Pivot16", .int 1 0#1) :: env)
            { s with pc := "if.else43", pre := some "LeafBlock11" }) =
          .jump (stateAt
            (gapLitElse43Env (("%SwitchLeaf12", .int 1 0#1) ::
              ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env) cur r)
            (gapLitSet s "cleanup82" "if.else43" (writeBytes
              (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8)
                (natToBytes t.toNat 8))
              (r + 16) (natToBytes 3 8)))) :=
        gapLit_step_ifElse43 (calls := calls)
          (env := ("%SwitchLeaf12", .int 1 0#1) :: ("%Pivot14", .int 1 0#1) ::
            ("%Pivot16", .int 1 0#1) :: env)
          (s := { s with pc := "if.else43", pre := some "LeafBlock11" })
          rfl hc' hrec hr64 ht'
      refine ⟨stateAt (gapLitElse43Env (("%SwitchLeaf12", .int 1 0#1) ::
          ("%Pivot14", .int 1 0#1) :: ("%Pivot16", .int 1 0#1) :: env) cur r)
          (gapLitSet s "cleanup82" "if.else43" (writeBytes
            (writeBytes (writeBytes s.mem r (natToBytes 0 4)) (r + 8)
              (natToBytes t.toNat 8))
            (r + 16) (natToBytes 3 8))),
        5, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [stateAt, gapLitSet]
      · simp only [stateAt, gapLitSet]
      · simp only [stateAt, gapLitSet]
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).1
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.1
      · simpa only [stateAt, gapLitSet] using (gapLit_else43_cells _ cur r).2.2
      · intro k
        rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
          runFuel_jump_prefix h1 (1 + (1 + (1 + (1 + k)))),
          runFuel_jump_prefix h2 (1 + (1 + (1 + k))),
          runFuel_jump_prefix h3 (1 + (1 + k)),
          runFuel_jump_prefix h4 (1 + k),
          runFuel_jump_prefix h5 k]

/-! ### The exits' continuations

The compare loop leaves at `if.then57` on a mismatch and at `for.end.i` on the
bound.  Both states carry the exit word, and the word now carries the record word
`readBytes mem (cur + 1112) 8` the two refusal sites load, so either continuation
can write its record without a second read.

`if.then57` writes the tag-2 record at the selected index plus `%t.0.val` and
returns to `cleanup82`.  `for.end.i` tests the token's length against the
literal's: equal reaches `if.end67`, and unequal falls to `if.then57` with the
`phi` selecting `%cond.i`, which is the compare length `m` — the same tag-2
record, one step further. -/

/-- `if.then57`'s cells, at the block's own environment. -/
theorem gapLit_then57_cells (env : Env) (cur r : Nat) (ew tw : BitVec 64) :
    lookupName (gapLitThen57Env env cur r ew tw) "%msg2.i132" = some (.ptr (r + 16)) ∧
    lookupName (gapLitThen57Env env cur r ew tw) "%off1.i131" = some (.ptr (r + 8)) ∧
    lookupName (gapLitThen57Env env cur r ew tw) "%add60" = some (.int 64 (ew + tw)) ∧
    lookupName (gapLitThen57Env env cur r ew tw) "%ei49.0.ph" = some (.int 64 ew) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [gapLitThen57Env]; block_lk)

/-- **The mismatch exit's continuation.**  `if.then57` entered from `for.body.i`
takes `%i.029.i` as its index, writes the tag-2 record at
`%i.029.i + %t.0.val`, and returns to `cleanup82` in one step. -/
theorem gapLit_exitThen57 {calls : Calls} {bytes litBytes : List UInt8}
    {cur t n ln m r c : Nat} {mem : Mem} {e : State}
    (hpc : e.pc = "if.then57") (hpre : e.pre = some "for.body.i")
    (hidx : lookupName e.env "%i.029.i" = some (.int 64 (BitVec.ofNat 64 c)))
    (hw : gapLitExitWord bytes litBytes cur t n ln m mem e)
    (hrec : readBytes mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64) :
    ∃ (e' : State) (j : Nat), j ≤ 1 ∧ e'.pc = "cleanup82" ∧ e'.pre = some "if.then57" ∧
      e'.mem = gapLitThen57Mem e r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t) ∧
      lookupName e'.env "%ei49.0.ph" = some (.int 64 (BitVec.ofNat 64 c)) ∧
      lookupName e'.env "%add60" = some (.int 64 (BitVec.ofNat 64 c + BitVec.ofNat 64 t)) ∧
      lookupName e'.env "%msg2.i132" = some (.ptr (r + 16)) ∧
      lookupName e'.env "%off1.i131" = some (.ptr (r + 8)) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody e = runFuel calls k odGapRecoverBody e' := by
  obtain ⟨hmem, hcur, ht, _hcond, _hsub, _hln, _hdisj, _⟩ := hw
  have hinc : phiIncoming "for.body.i"
      [("for.end.i", Operand.reg "%cond.i"), ("for.body.i", Operand.reg "%i.029.i")] =
      some (Operand.reg "%i.029.i") := by decide
  have hop : evalOperand (stateAt e.env e) (Operand.reg "%i.029.i") =
      some (.int 64 (BitVec.ofNat 64 c)) := by
    simp only [stateAt, evalOperand, hidx]
  have hrec' : readBytes e.mem (cur + 1112) 8 = some (natToBytes r 8) := by
    rw [hmem]; exact hrec
  have hstep : step calls odGapRecoverBody e =
      .jump (stateAt
        (gapLitThen57Env e.env cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t))
        (gapLitSet e "cleanup82" "if.then57"
          (gapLitThen57Mem e r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)))) := by
    have hh := gapLit_step_ifThen57 (calls := calls) (env := e.env) (s := e)
      (p := "for.body.i") (cur := cur) (r := r)
      (ew := BitVec.ofNat 64 c) (tw := BitVec.ofNat 64 t) (op := Operand.reg "%i.029.i")
      hpc hpre hinc hop hcur hrec' hr64 ht
    simpa only [stateAt] using hh
  refine ⟨stateAt (gapLitThen57Env e.env cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t))
      (gapLitSet e "cleanup82" "if.then57"
        (gapLitThen57Mem e r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t))),
    1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, gapLitSet]
  · simp only [stateAt, gapLitSet]
  · simp only [stateAt, gapLitSet]
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)).2.2.2
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)).2.2.1
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)).1
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 c) (BitVec.ofNat 64 t)).2.1
  · intro k
    rw [show 1 + k = 1 + k from rfl, runFuel_jump_prefix hstep k]

/-- **The bound exit, matched.**  `for.end.i` with the token's length equal to the
literal's leaves for `if.end67` in one step, writing nothing. -/
theorem gapLit_exitForEnd {calls : Calls} {bytes litBytes : List UInt8}
    {cur t n ln m : Nat} {mem : Mem} {e : State}
    (hpc : e.pc = "for.end.i")
    (hw : gapLitExitWord bytes litBytes cur t n ln m mem e)
    (hbit : evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1#1) :
    ∃ (e' : State) (j : Nat), j ≤ 1 ∧ e'.pc = "if.end67" ∧ e'.pre = some "for.end.i" ∧
      e'.mem = mem ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody e = runFuel calls k odGapRecoverBody e' := by
  obtain ⟨hmem, _hcur, _ht, _hcond, hsub, hln, _hdisj, _⟩ := hw
  have hstep : step calls odGapRecoverBody e =
      .jump (stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
        { e with pc := "if.end67", pre := some "for.end.i" }) := by
    have hh := gapLit_step_forEnd (calls := calls) (env := e.env) (s := e)
      (nw := BitVec.ofNat 64 n) (lnw := BitVec.ofNat 64 ln) hpc hsub hln
    have hif : (if evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1
        then "if.end67" else "if.then57") = "if.end67" := by
      rw [hbit]; decide
    rw [hif] at hh
    simpa only [stateAt] using hh
  refine ⟨stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
      { e with pc := "if.end67", pre := some "for.end.i" },
    1, by omega, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt]
  · simp only [stateAt]
  · simp only [stateAt]
    exact hmem
  · intro k
    rw [runFuel_jump_prefix hstep k]

/-- **The bound exit, unmatched.**  `for.end.i` with the token's length unequal to
the literal's falls to `if.then57`, whose `phi` selects `%cond.i` — the compare
length `m` — and writes the tag-2 record at `m + %t.0.val` before returning to
`cleanup82`. -/
theorem gapLit_exitForEndRefuse {calls : Calls} {bytes litBytes : List UInt8}
    {cur t n ln m r : Nat} {mem : Mem} {e : State}
    (hpc : e.pc = "for.end.i")
    (hw : gapLitExitWord bytes litBytes cur t n ln m mem e)
    (hrec : readBytes mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64)
    (hbit : evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 0#1) :
    ∃ (e' : State) (j : Nat), j ≤ 2 ∧ e'.pc = "cleanup82" ∧ e'.pre = some "if.then57" ∧
      e'.mem = gapLitThen57Mem e r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t) ∧
      lookupName e'.env "%ei49.0.ph" = some (.int 64 (BitVec.ofNat 64 m)) ∧
      lookupName e'.env "%add60" = some (.int 64 (BitVec.ofNat 64 m + BitVec.ofNat 64 t)) ∧
      lookupName e'.env "%msg2.i132" = some (.ptr (r + 16)) ∧
      lookupName e'.env "%off1.i131" = some (.ptr (r + 8)) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody e = runFuel calls k odGapRecoverBody e' := by
  obtain ⟨hmem, hcur, ht, hcond, hsub, hln, _hdisj, _⟩ := hw
  have hstep1 : step calls odGapRecoverBody e =
      .jump (stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
        { e with pc := "if.then57", pre := some "for.end.i" }) := by
    have hh := gapLit_step_forEnd (calls := calls) (env := e.env) (s := e)
      (nw := BitVec.ofNat 64 n) (lnw := BitVec.ofNat 64 ln) hpc hsub hln
    have hif : (if evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1
        then "if.end67" else "if.then57") = "if.then57" := by
      rw [hbit]; decide
    rw [hif] at hh
    simpa only [stateAt] using hh
  have hcond' : lookupName (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
      "%cond.i" = some (.int 64 (BitVec.ofNat 64 m)) := by
    simp only [gapLitEndEnv]; block_lk
  have hcur' : lookupName (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
      "%c" = some (.ptr cur) := by
    simp only [gapLitEndEnv]; block_lk
  have ht' : lookupName (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
      "%t.0.val" = some (.int 64 (BitVec.ofNat 64 t)) := by
    simp only [gapLitEndEnv]; block_lk
  have hinc : phiIncoming "for.end.i"
      [("for.end.i", Operand.reg "%cond.i"), ("for.body.i", Operand.reg "%i.029.i")] =
      some (Operand.reg "%cond.i") := by decide
  have hop : evalOperand
      (stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
        { e with pc := "if.then57", pre := some "for.end.i" })
      (Operand.reg "%cond.i") = some (.int 64 (BitVec.ofNat 64 m)) := by
    simp only [stateAt, evalOperand]
    rw [hcond']
  have hrec' : readBytes e.mem (cur + 1112) 8 = some (natToBytes r 8) := by
    rw [hmem]; exact hrec
  have hstep2 : step calls odGapRecoverBody
      (stateAt (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
        { e with pc := "if.then57", pre := some "for.end.i" }) =
      .jump (stateAt
        (gapLitThen57Env (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
          cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t))
        (gapLitSet { e with pc := "if.then57", pre := some "for.end.i" } "cleanup82"
          "if.then57"
          (gapLitThen57Mem { e with pc := "if.then57", pre := some "for.end.i" } r
            (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)))) := by
    have hh := gapLit_step_ifThen57 (calls := calls)
      (env := gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
      (s := { e with pc := "if.then57", pre := some "for.end.i" })
      (p := "for.end.i") (cur := cur) (r := r)
      (ew := BitVec.ofNat 64 m) (tw := BitVec.ofNat 64 t) (op := Operand.reg "%cond.i")
      rfl rfl hinc hop hcur' hrec' hr64 ht'
    exact hh
  refine ⟨stateAt
      (gapLitThen57Env (gapLitEndEnv e.env (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln))
        cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t))
      (gapLitSet { e with pc := "if.then57", pre := some "for.end.i" } "cleanup82"
        "if.then57"
        (gapLitThen57Mem { e with pc := "if.then57", pre := some "for.end.i" } r
          (BitVec.ofNat 64 m) (BitVec.ofNat 64 t))),
    2, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [stateAt, gapLitSet]
  · simp only [stateAt, gapLitSet]
  · simp only [stateAt, gapLitSet, gapLitThen57Mem]
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)).2.2.2
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)).2.2.1
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)).1
  · simpa only [stateAt, gapLitSet] using
      (gapLit_then57_cells _ cur r (BitVec.ofNat 64 m) (BitVec.ofNat 64 t)).2.1
  · intro k
    rw [show 2 + k = 1 + (1 + k) from by omega,
      runFuel_jump_prefix hstep1 (1 + k), runFuel_jump_prefix hstep2 k]

/-- **The loop's exit, continued.**  From an exit state satisfying the word, the
run reaches `if.end67` with the memory unchanged, or `cleanup82` with the tag-2
record and its own index, within three control steps. -/
theorem gapLit_exitRun {calls : Calls} {bytes litBytes : List UInt8}
    {cur t n ln m r : Nat} {mem : Mem} {e : State}
    (hblock : gapLitExitBlock e)
    (hw : gapLitExitWord bytes litBytes cur t n ln m mem e)
    (hrec : readBytes mem (cur + 1112) 8 = some (natToBytes r 8)) (hr64 : r < 2 ^ 64) :
    ∃ (e' : State) (j : Nat), j ≤ 3 ∧
      ((e'.pc = "if.end67" ∧ e'.pre = some "for.end.i" ∧ e'.mem = mem) ∨
       (e'.pc = "cleanup82" ∧ e'.pre = some "if.then57" ∧
        lookupName e'.env "%msg2.i132" = some (.ptr (r + 16)) ∧
        lookupName e'.env "%off1.i131" = some (.ptr (r + 8)) ∧
        ∃ ew : BitVec 64, lookupName e'.env "%ei49.0.ph" = some (.int 64 ew) ∧
          e'.mem = gapLitThen57Mem e r ew (BitVec.ofNat 64 t))) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody e = runFuel calls k odGapRecoverBody e' := by
  have hw' := hw
  obtain ⟨_hmem, _hcur, _ht, _hcond, _hsub, _hln, hdisj, _⟩ := hw'
  rcases hblock with hpc | hpc
  · rcases hdisj with ⟨c, _hpc1, hpre1, hidx, _hlt, _hpfx, _hne⟩ | ⟨hpc2, _hpre2, _hinc2, _hall⟩
    · obtain ⟨e', j, hj, hpc', hpre', hmem', hei, hadd, hmsg, hoff, hrun⟩ :=
        gapLit_exitThen57 hpc hpre1 hidx hw hrec hr64
      exact ⟨e', j, by omega,
        Or.inr ⟨hpc', hpre', hmsg, hoff, _, hei, hmem'⟩, hrun⟩
    · rw [hpc] at hpc2
      exact absurd hpc2 (by decide)
  · rcases hdisj with ⟨_c, hpc1, _hpre1, _hidx, _hlt, _hpfx, _hne⟩ | ⟨_hpc2, _hpre2, _hinc2, _hall⟩
    · rw [hpc] at hpc1
      exact absurd hpc1 (by decide)
    · have hb116c : evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 1#1 ∨
          evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln) = 0#1 := by
        rcases bitVec1_eq_zero_or_one
          (evalICmp .eq (BitVec.ofNat 64 n) (BitVec.ofNat 64 ln)) with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases hb116c with hb | hb
      · obtain ⟨e', j, hj, hpc', hpre', hmem', hrun⟩ :=
          gapLit_exitForEnd hpc hw hb
        exact ⟨e', j, by omega, Or.inl ⟨hpc', hpre', hmem'⟩, hrun⟩
      · obtain ⟨e', j, hj, hpc', hpre', hmem', hei, hadd, hmsg, hoff, hrun⟩ :=
          gapLit_exitForEndRefuse hpc hw hrec hr64 hb
        exact ⟨e', j, by omega,
          Or.inr ⟨hpc', hpre', hmsg, hoff, _, hei, hmem'⟩, hrun⟩

/-! ### The empty range

`if.end48`'s own test is `%ee.0.lcssa == %t.0.val`: when the token's length is
zero the block takes the `for.end.i` edge directly, so the compare loop is
skipped.  `for.end.i` then tests the zero length against the literal's and falls
to its own `if.end67`/`if.then57` branch — for the three literals' widths (four
and five) always the refusal, since a zero length is not theirs. -/

/-- **The empty range's run.**  From `if.end48` with the token's length equal to
`%t.0.val`, `for.end.i` is reached in one step and its branch in two, with the
compare length `%sub54` zero and the literal's width still bound. -/
theorem gapLit_emptyRun {calls : Calls} {env : Env} {s : State}
    {p : String} {litBase : Nat} {lnw ee t : BitVec 64} {opL opN : Operand}
    (hpc : s.pc = "if.end48") (hpre : s.pre = some p)
    (hincL : phiIncoming p
      [("if.then37", Operand.reg "%litfalse"), ("if.then42", Operand.reg "%litnull"),
       ("LeafBlock11", Operand.reg "%littrue")] = some opL)
    (hopL : evalOperand (stateAt env s) opL = some (.ptr litBase))
    (hincN : phiIncoming p
      [("if.then37", Operand.imm (Const.int 64 0x0000000000000005#64)),
       ("if.then42", Operand.imm (Const.int 64 0x0000000000000004#64)),
       ("LeafBlock11", Operand.imm (Const.int 64 0x0000000000000004#64))] = some opN)
    (hopN : evalOperand (stateAt env s) opN = some (.int 64 lnw))
    (hee : lookupName env "%ee.0.lcssa" = some (.int 64 ee))
    (htt : lookupName env "%t.0.val" = some (.int 64 t))
    (hzero : ee = t) :
    ∃ (e : State) (j : Nat), j ≤ 2 ∧ e.pre = some "for.end.i" ∧
      (e.pc = "if.end67" ∨ e.pc = "if.then57") ∧ e.mem = s.mem ∧
      lookupName e.env "%cmp11.not.i" = some (.int 1 (evalICmp .eq (ee - t) lnw)) ∧
      ∀ k, runFuel calls (j + k) odGapRecoverBody (stateAt env s) =
        runFuel calls k odGapRecoverBody e := by
  have hbit1 : evalICmp .eq ee t = 1#1 := gap_eq_one hzero
  have hstep1 : step calls odGapRecoverBody (stateAt env s) =
      .jump (stateAt (gapLitEnd48Env env litBase lnw ee t)
        { s with pc := "for.end.i", pre := some "if.end48" }) := by
    have hh := gapLit_step_ifEnd48 (calls := calls) (env := env) (s := s) (p := p)
      (litBase := litBase) (lnw := lnw) (ee := ee) (t := t) (opL := opL) (opN := opN)
      hpc hpre hincL hopL hincN hopN hee htt
    have hif : (if evalICmp .eq ee t = 1 then "for.end.i" else "for.body.i") =
        "for.end.i" := by
      rw [hbit1]; decide
    rw [hif] at hh
    simpa only [stateAt] using hh
  have hsub1 : lookupName (gapLitEnd48Env env litBase lnw ee t) "%sub54" =
      some (.int 64 (ee - t)) := by
    simp only [gapLitEnd48Env]; block_lk
  have hln1 : lookupName (gapLitEnd48Env env litBase lnw ee t) "%ln.0" =
      some (.int 64 lnw) := by
    simp only [gapLitEnd48Env]; block_lk
  have hstep2 := gapLit_step_forEnd (calls := calls)
    (env := gapLitEnd48Env env litBase lnw ee t)
    (s := { s with pc := "for.end.i", pre := some "if.end48" })
    (nw := ee - t) (lnw := lnw) rfl hsub1 hln1
  rcases bitVec1_eq_zero_or_one (evalICmp .eq (ee - t) lnw) with hb | hb
  · have hif : (if evalICmp .eq (ee - t) lnw = 1 then "if.end67" else "if.then57") =
        "if.then57" := by
      rw [hb]; decide
    have hstep2' : step calls odGapRecoverBody
        (stateAt (gapLitEnd48Env env litBase lnw ee t)
          { s with pc := "for.end.i", pre := some "if.end48" }) =
        .jump (stateAt
          (gapLitEndEnv (gapLitEnd48Env env litBase lnw ee t) (ee - t) lnw)
          { s with pc := "if.then57", pre := some "for.end.i" }) := by
      rw [hif] at hstep2
      simpa only [stateAt] using hstep2
    refine ⟨stateAt (gapLitEndEnv (gapLitEnd48Env env litBase lnw ee t) (ee - t) lnw)
        { s with pc := "if.then57", pre := some "for.end.i" },
      2, by omega, ?_, Or.inr ?_, ?_, ?_, ?_⟩
    · simp only [stateAt]
    · simp only [stateAt]
    · simp only [stateAt]
    · simp only [stateAt, gapLitEndEnv]
      block_lk
    · intro k
      rw [show 2 + k = 1 + (1 + k) from by omega,
        runFuel_jump_prefix hstep1 (1 + k), runFuel_jump_prefix hstep2' k]
  · have hif : (if evalICmp .eq (ee - t) lnw = 1 then "if.end67" else "if.then57") =
        "if.end67" := by
      rw [hb]; decide
    have hstep2' : step calls odGapRecoverBody
        (stateAt (gapLitEnd48Env env litBase lnw ee t)
          { s with pc := "for.end.i", pre := some "if.end48" }) =
        .jump (stateAt
          (gapLitEndEnv (gapLitEnd48Env env litBase lnw ee t) (ee - t) lnw)
          { s with pc := "if.end67", pre := some "for.end.i" }) := by
      rw [hif] at hstep2
      simpa only [stateAt] using hstep2
    refine ⟨stateAt (gapLitEndEnv (gapLitEnd48Env env litBase lnw ee t) (ee - t) lnw)
        { s with pc := "if.end67", pre := some "for.end.i" },
      2, by omega, ?_, Or.inl ?_, ?_, ?_, ?_⟩
    · simp only [stateAt]
    · simp only [stateAt]
    · simp only [stateAt]
    · simp only [stateAt, gapLitEndEnv]
      block_lk
    · intro k
      rw [show 2 + k = 1 + (1 + k) from by omega,
        runFuel_jump_prefix hstep1 (1 + k), runFuel_jump_prefix hstep2' k]

end LeanLLVM.Refinement
