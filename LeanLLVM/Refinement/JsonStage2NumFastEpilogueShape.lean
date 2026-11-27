/-
The epilogue's boundary, and the two cells its own blocks rewrite.

`num_fast_el1`'s fallback hands `while.end253.i.i` the ladder's two exit cells
and returns the converted double from `if.end291`.  Between them sit the rounding
loop `for.cond255.i.i` … `for.cond255.i.i.backedge` and the sign select at
`for.end359.i.i`, nineteen blocks.  `NumFastFallback.FbEpilogue` names the run
across them, and its model tie is `fbEpilogueModel`: the pre-round word in
`%.cast.i629.i.i` and `%d201.3.i.i`, and the window in `%v.i.i`.

**The tie names cells the first block rewrites.**  `while.end253.i.i`'s only
in-edge is `while.cond229.i.i` (`t3DivExitWord` fixes the predecessor), so its
`phi` selects `%d201.2.i.i` and its `bitcastToInt` computes `%.cast.i629.i.i`
from that selection.  Both of the tie's word cells are therefore overwritten by
the block before anything reads them (`epi253_denote`), and the cell the loop
actually reads — `%d201.2.i.i` — is left free by `FbEpilogue`; only its
`≠ none` is required (`t3DivExitWord`).  The same hypothesis is also silent
about `%cmp1.i`, which is the select's condition at `for.end359.i.i`
(`epi359_denote`, `epi359Env_cond366`).  That is why the boundary cannot be
discharged as stated.

**The statement is false as stated.**  `epiWitness` is a state at
`while.end253.i.i` with `while.cond229.i.i` as predecessor that satisfies every
premise of `FbEpilogue` for any `d`, `digA`, `out`, `J`: `t3DivExitWord` and
`fbEpilogueModel` hold, and `%d201.2.i.i` is an `int` rather than a `float`.  The
`phi` then binds `%d201.3.i.i` to that `int`, the `bitcastToInt` is undefined,
and the run is `ub` before the loop is entered (`epiWitness_step`,
`epiWitness_runFuel_succ`).  From a state whose run is `ub` in one step the
boundary reaches no `if.end291` state whose run is a definition
(`not_fbEpilogue`), so `FbEpilogue` has no proof.  The hypothesis is not merely
unproved: it is unsatisfiable at the shapes the model names.

**The clause that holds.**  Two things are true of the blocks and can be stated:

* `epi253_denote` — the block binds `%d201.3.i.i` to the *edge's* operand and
  `%.cast.i629.i.i` to its bitcast, whatever the incoming cells held.  The tie
  belongs on `%d201.2.i.i` (`FbEpilogueTie`), which is the cell the head's
  `phi` selects.
* `epi359_denote` — the sign select reads `%cmp1.i`, so the rounded bits are
  `if %cmp1.i then fneg else cast` (`epi359Env_cond366`).  On a well-formed
  lexeme the reader binds that cell to the decomposition's sign
  (`sl_sign_tie`), and `epiSign_of_scan` reads the tie at
  `if d.neg then 1 else 0`.

`FbEpilogueTie` and `FbEpilogueAt` are that corrected boundary: the tie names
`%d201.2.i.i` and `%cmp1.i`, the conclusion is `FbEpilogue`'s unchanged, and
`fb_tail_at` carries the fallback's tail from it.  What stays open is the loop
itself — the nineteen blocks' traversal from `for.cond255.i.i` to
`for.end359.i.i` and the fixed point the rounding reaches — which this module
does not model; it fixes the statement that traversal must be proved at.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastFallback

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3Rows
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastScanSlow
open LeanLLVM.Refinement.NumFastFallback
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine

namespace NumFastEpilogueShape

/-! ### `while.end253.i.i`: the block that feeds the loop

The block has one in-edge, `while.cond229.i.i`, so its `phi` never selects
`%div.i.i`: the loop's carried word arrives from the head's own cell and the
`bitcastToInt` is computed from it.  The tie `fbEpilogueModel` puts the
pre-round word in `%.cast.i629.i.i` and `%d201.3.i.i`; both are the block's
destinations.
-/

/-- The block's instructions, at its pin. -/
def epi253Instrs : List Instr :=
  [Instr.phi "%d201.3.i.i" Ty.double
     [("while.body232.i.i", (Operand.reg "%div.i.i")),
      ("while.cond229.i.i", (Operand.reg "%d201.2.i.i"))],
   Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")]

/-- The pin, at the named list. -/
theorem epi253_find :
    numFastBody.findBlock "while.end253.i.i" =
      some ⟨"while.end253.i.i", epi253Instrs, Term.br "for.cond255.i.i"⟩ := by
  simpa only [epi253Instrs] using numFast_findBlock_while_end253_i_i

/-- The environment the block leaves: the selected word and its bitcast, in
front of the incoming cells. -/
def epi253Env (env : Env) (b : BitVec 64) : Env :=
  ("%.cast.i629.i.i", .int 64 b) :: ("%d201.3.i.i", .float b) :: env

/-- The block's chain, from the head's edge: the `phi` selects `%d201.2.i.i`,
and the cast is that word. -/
theorem epi253_denote {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hpre : s.pre = some "while.cond229.i.i")
    (hd : lookupName env "%d201.2.i.i" = some (.float b)) :
    denoteCode calls epi253Instrs (stateAt env s) =
      some (stateAt (epi253Env env b) s) := by
  unfold epi253Instrs
  rw [denoteCode_phi calls env s "%d201.3.i.i" Ty.double
    [("while.body232.i.i", (Operand.reg "%div.i.i")),
     ("while.cond229.i.i", (Operand.reg "%d201.2.i.i"))]
    hpre (by decide)
    (evalOperand_reg_of env s "%d201.2.i.i" (.float b) hd)
    [Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")] (by rfl)]
  rw [denoteCode_bitcastToInt calls (("%d201.3.i.i", .float b) :: env) s
    "%.cast.i629.i.i" "%d201.3.i.i" (lookupName_cons_self ..) []]
  simp only [denoteCode_nil, epi253Env, stateAt]

/-- The block's step: it jumps into the loop with the selected word. -/
theorem epi253_step {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hpc : s.pc = "while.end253.i.i")
    (hpre : s.pre = some "while.cond229.i.i")
    (hd : lookupName env "%d201.2.i.i" = some (.float b)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (epi253Env env b)
        { s with pc := "for.cond255.i.i", pre := some "while.end253.i.i" }) := by
  refine numFast_step_at (s' := stateAt (epi253Env env b) s)
    (b := ⟨"while.end253.i.i", epi253Instrs, Term.br "for.cond255.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi253_find
  · simpa only [stateAt] using epi253_denote (calls := calls) hpre hd
  · simp only [execTerm, stateAt, hpc]

/-- **The tie's word cells are the block's destinations.**  The pre-state's
`%.cast.i629.i.i` and `%d201.3.i.i` do not survive the block: what it leaves is
the edge's `%d201.2.i.i`. -/
theorem epi253_cast_is_edge {env : Env} {b : BitVec 64} :
    lookupName (epi253Env env b) "%.cast.i629.i.i" = some (.int 64 b) :=
  lookupName_cons_self ..

/-! ### `for.cond255.i.i`: the loop's head

The head's `phi` takes the cast from `while.end253.i.i` and its test is the word
against zero.  Both arms leave for a body block; the traversal the boundary owes
is the run from here.
-/

/-- The head's incoming list. -/
def epi255Inc : List (String × Operand) :=
  [("while.end253.i.i", (Operand.reg "%.cast.i629.i.i")),
   ("for.cond255.i.i.backedge", (Operand.reg "%b.0.i.i.be"))]

/-- The block's instructions, at its pin. -/
def epi255Instrs : List Instr :=
  [Instr.phi "%b.0.i.i" (Ty.int 64) epi255Inc,
   Instr.icmp "%cmp256.i.i" (IPred.eq) 64 (Operand.reg "%b.0.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

/-- The pin, at the named list. -/
theorem epi255_find :
    numFastBody.findBlock "for.cond255.i.i" =
      some ⟨"for.cond255.i.i", epi255Instrs,
        Term.condbr (Operand.reg "%cmp256.i.i") "if.then258.i.i"
          "if.end264.i.i"⟩ := by
  simpa only [epi255Instrs, epi255Inc] using numFast_findBlock_for_cond255_i_i

/-- The chain: the `phi` binds the carried word, and the test is its zero
comparison. -/
theorem epi255_denote {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    {p : String} {op : Operand}
    (hpre : s.pre = some p) (hinc : phiIncoming p epi255Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 b)) :
    denoteCode calls epi255Instrs (stateAt env s) =
      some (stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env) s) := by
  unfold epi255Instrs
  rw [denoteCode_phi calls env s "%b.0.i.i" (Ty.int 64) epi255Inc hpre hinc hop
    [Instr.icmp "%cmp256.i.i" (IPred.eq) 64 (Operand.reg "%b.0.i.i")
      (Operand.imm (Const.int 64 0x0000000000000000#64))] (by rfl)]
  rw [denoteCode_icmp_eq_imm calls (("%b.0.i.i", .int 64 b) :: env) s
    "%cmp256.i.i" "%b.0.i.i" (lookupName_cons_self ..) []]
  simp only [denoteCode_nil, stateAt]

/-- The head's step at a zero word: the empty arm's body. -/
theorem epi255_step_zero {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    {p : String} {op : Operand}
    (hpc : s.pc = "for.cond255.i.i")
    (hpre : s.pre = some p) (hinc : phiIncoming p epi255Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 b))
    (hbit : evalICmp .eq b 0x0#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env)
        { s with pc := "if.then258.i.i", pre := some "for.cond255.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
      ("%b.0.i.i", .int 64 b) :: env) s)
    (b := ⟨"for.cond255.i.i", epi255Instrs,
      Term.condbr (Operand.reg "%cmp256.i.i") "if.then258.i.i"
        "if.end264.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi255_find
  · simpa only [stateAt] using epi255_denote (calls := calls) hpre hinc hop
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env) s)
      "%cmp256.i.i" "if.then258.i.i" "if.end264.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step at a nonzero word. -/
theorem epi255_step_nonzero {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    {p : String} {op : Operand}
    (hpc : s.pc = "for.cond255.i.i")
    (hpre : s.pre = some p) (hinc : phiIncoming p epi255Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 b))
    (hbit : evalICmp .eq b 0x0#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env)
        { s with pc := "if.end264.i.i", pre := some "for.cond255.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
      ("%b.0.i.i", .int 64 b) :: env) s)
    (b := ⟨"for.cond255.i.i", epi255Instrs,
      Term.condbr (Operand.reg "%cmp256.i.i") "if.then258.i.i"
        "if.end264.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi255_find
  · simpa only [stateAt] using epi255_denote (calls := calls) hpre hinc hop
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env) s)
      "%cmp256.i.i" "if.then258.i.i" "if.end264.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### `for.end359.i.i`: the sign select

The block's seven-incoming `phi` is the loop's exit word.  What follows it is
fixed by the pin and reads two cells the boundary never names: the word's
pattern is bitcast back to a double and `%cmp1.i` selects between the negation
and the pattern.  This is where the returned double's sign comes from.
-/

/-- The exit block's incoming list, in the pin's order. -/
def epi359Inc : List (String × Operand) :=
  [("if.then343.i.i", (Operand.reg "%spec.select508.i.i")),
   ("if.then309.i.i", (Operand.reg "%spec.select507.i.i")),
   ("if.end273.i.i", (Operand.reg "%b.0.i.i")),
   ("if.then298.i.i", (Operand.reg "%b.0.i.i")),
   ("if.end335.i.i", (Operand.reg "%b.0.i.i")),
   ("if.then267.i.i", (Operand.imm (Const.int 64 0x7ff0000000000000#64))),
   ("if.then258.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))]

/-- The block's instructions, at its pin. -/
def epi359Instrs : List Instr :=
  [Instr.phi "%b.6.i.i" (Ty.int 64) epi359Inc,
   Instr.bitcastToDouble "%.cast.i630.i.i" (Operand.reg "%b.6.i.i"),
   Instr.fneg "%fneg363.i.i" (Operand.reg "%.cast.i630.i.i"),
   Instr.select "%cond366.i.i" Ty.double (Operand.reg "%cmp1.i")
     (Operand.reg "%fneg363.i.i") (Operand.reg "%.cast.i630.i.i"),
   Instr.callVoid "llvm.lifetime.end.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
      (Ty.ptr, (Operand.reg "%v.i.i"))]]

/-- The pin, at the named list. -/
theorem epi359_find :
    numFastBody.findBlock "for.end359.i.i" =
      some ⟨"for.end359.i.i", epi359Instrs, Term.br "if.end291"⟩ := by
  simpa only [epi359Instrs, epi359Inc] using numFast_findBlock_for_end359_i_i

/-- The environment the block leaves: the exit word, its pattern, the negation,
and the sign-selected double. -/
def epi359Env (env : Env) (bits : BitVec 64) (bb : BitVec 1) : Env :=
  ("%cond366.i.i", .float (if bb = 1 then fnegBits bits else bits)) ::
  ("%fneg363.i.i", .float (fnegBits bits)) ::
  ("%.cast.i630.i.i", .float bits) ::
  ("%b.6.i.i", .int 64 bits) :: env

/-- `bitcast double %v to i64`'s converse: an `i64` pattern read as a double. -/
theorem step_bitcastToDouble (calls : Calls) (env : Env) (s : State)
    (d v : String) {x : BitVec 64}
    (hv : lookupName env v = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.bitcastToDouble d (.reg v)) =
      some (stateAt ((d, .float x) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hv, State.bind]

theorem denoteCode_bitcastToDouble (calls : Calls) (env : Env) (s : State)
    (d v : String) {x : BitVec 64}
    (hv : lookupName env v = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.bitcastToDouble d (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float x) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_bitcastToDouble calls env s d v hv)]

/-- The block's chain: the exit word is cast back, negated, selected by the
sign cell, and the input's lifetime ends. -/
theorem epi359_denote {calls : Calls} {env : Env} {s : State}
    {bits : BitVec 64} {bb : BitVec 1} {p : String} {op : Operand}
    {v : Nat} {r : CallOutcome}
    (hpre : s.pre = some p) (hinc : phiIncoming p epi359Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 bits))
    (hcmp : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hlife : calls "llvm.lifetime.end.p0"
      [.int 64 0x0000000000000620#64, .ptr v] s.mem s.next = some r) :
    denoteCode calls epi359Instrs (stateAt env s) =
      some (stateAt (epi359Env env bits bb) { s with mem := r.mem, next := r.next }) := by
  unfold epi359Instrs
  rw [denoteCode_phi calls env s "%b.6.i.i" (Ty.int 64) epi359Inc hpre hinc hop
    [Instr.bitcastToDouble "%.cast.i630.i.i" (Operand.reg "%b.6.i.i"),
     Instr.fneg "%fneg363.i.i" (Operand.reg "%.cast.i630.i.i"),
     Instr.select "%cond366.i.i" Ty.double (Operand.reg "%cmp1.i")
       (Operand.reg "%fneg363.i.i") (Operand.reg "%.cast.i630.i.i"),
     Instr.callVoid "llvm.lifetime.end.p0"
       [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
        (Ty.ptr, (Operand.reg "%v.i.i"))]] (by rfl)]
  rw [denoteCode_bitcastToDouble calls (("%b.6.i.i", .int 64 bits) :: env) s "%.cast.i630.i.i" "%b.6.i.i"
    (lookupName_cons_self ..)]
  rw [denoteCode_fneg calls (("%.cast.i630.i.i", .float bits) ::
      ("%b.6.i.i", .int 64 bits) :: env) s
    "%fneg363.i.i" "%.cast.i630.i.i" (lookupName_cons_self ..)]
  rw [denoteCode_select_double calls
    (("%fneg363.i.i", .float (fnegBits bits)) ::
     ("%.cast.i630.i.i", .float bits) :: ("%b.6.i.i", .int 64 bits) :: env) s
    "%cond366.i.i" "%cmp1.i" "%fneg363.i.i" "%.cast.i630.i.i"
    (by fb_lk)
    (lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  rw [denoteCode_callVoid_some calls
    (("%cond366.i.i", .float (if bb = 1 then fnegBits bits else bits)) ::
     ("%fneg363.i.i", .float (fnegBits bits)) ::
     ("%.cast.i630.i.i", .float bits) :: ("%b.6.i.i", .int 64 bits) :: env) s
    "llvm.lifetime.end.p0"
    [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
     (Ty.ptr, (Operand.reg "%v.i.i"))]
    [.int 64 0x0000000000000620#64, .ptr v] r
    (evalOperands_lifetimeMark (env :=
      (("%cond366.i.i", .float (if bb = 1 then fnegBits bits else bits)) ::
       ("%fneg363.i.i", .float (fnegBits bits)) ::
       ("%.cast.i630.i.i", .float bits) :: ("%b.6.i.i", .int 64 bits) :: env))
      (s := s) (w := 0x620) (by fb_lk))
    hlife []]
  simp only [denoteCode_nil, epi359Env, stateAt]

/-- The block's step: it jumps to `if.end291` with the sign-selected double in
`%cond366.i.i`. -/
theorem epi359_step {calls : Calls} {env : Env} {s : State}
    {bits : BitVec 64} {bb : BitVec 1} {p : String} {op : Operand}
    {v : Nat} {r : CallOutcome}
    (hpc : s.pc = "for.end359.i.i")
    (hpre : s.pre = some p) (hinc : phiIncoming p epi359Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 bits))
    (hcmp : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hlife : calls "llvm.lifetime.end.p0"
      [.int 64 0x0000000000000620#64, .ptr v] s.mem s.next = some r) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (epi359Env env bits bb)
        { s with mem := r.mem, next := r.next,
                 pc := "if.end291", pre := some "for.end359.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (epi359Env env bits bb) { s with mem := r.mem, next := r.next })
    (b := ⟨"for.end359.i.i", epi359Instrs, Term.br "if.end291"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi359_find
  · simpa only [stateAt] using epi359_denote (calls := calls) hpre hinc hop hcmp hv hlife
  · simp only [execTerm, stateAt, hpc]

/-- The sign-selected cell the edge hands `if.end291`. -/
theorem epi359Env_cond366 (env : Env) (bits : BitVec 64) (bb : BitVec 1) :
    lookupName (epi359Env env bits bb) "%cond366.i.i"
      = some (.float (if bb = 1 then fnegBits bits else bits)) :=
  lookupName_cons_self ..

/-- The select is not the identity on the pattern: `fneg` flips the sign bit, so
the two arms of `%cmp1.i` are different doubles at the zero pattern (where the
difference is `-0.0` against `0.0`). -/
theorem fnegBits_zero : fnegBits (0 : BitVec 64) = 0x8000000000000000#64 := by
  decide

theorem epi359_sign_differs :
    (if (1 : BitVec 1) = 1 then fnegBits (0 : BitVec 64) else 0)
      ≠ (if (0 : BitVec 1) = 1 then fnegBits (0 : BitVec 64) else 0) := by
  rw [ite_eq_left rfl, ite_eq_right (by decide), fnegBits_zero]
  decide

/-! ### The statement is false as stated

`epiWitness` satisfies `FbEpilogue`'s premises for every `d`, `digA`, `out`, `J`
and is stuck at the epilogue's first block: the tie leaves `%d201.2.i.i` free,
and this state puts an `int` there.
-/

/-- The witness's environment: the tie's three cells, the epilogue's read cells,
and `%d201.2.i.i` as an `int`. -/
def epiWitnessEnv (d : Decimal) (digA out : Nat) : Env :=
  [("%v.i.i", .ptr 0),
   ("%d201.3.i.i", .float (fbPreRound d)),
   ("%.cast.i629.i.i", .int 64 (fbPreRound d)),
   ("%d201.2.i.i", .int 64 0),
   ("%e10.2.i.i", .int 64 0),
   ("%dig.i.i", .ptr digA),
   ("%out", .ptr out),
   ("%cmp1.i", .int 1 0)]

/-- The witness: at the epilogue's entry, entered from the ladder's head. -/
def epiWitness (d : Decimal) (digA out : Nat) : State :=
  { env := epiWitnessEnv d digA out, mem := [], next := 0,
    pc := "while.end253.i.i", pre := some "while.cond229.i.i" }

theorem epiWitnessEnv_v (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%v.i.i" = some (.ptr 0) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_d201_3 (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%d201.3.i.i"
      = some (.float (fbPreRound d)) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_cast (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%.cast.i629.i.i"
      = some (.int 64 (fbPreRound d)) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_d201_2 (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%d201.2.i.i" = some (.int 64 0) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_e10 (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%e10.2.i.i" = some (.int 64 0) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_dig (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%dig.i.i" = some (.ptr digA) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_out (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%out" = some (.ptr out) := by
  simp only [epiWitnessEnv]
  fb_lk

theorem epiWitnessEnv_cmp (d : Decimal) (digA out : Nat) :
    lookupName (epiWitnessEnv d digA out) "%cmp1.i" = some (.int 1 0) := by
  simp only [epiWitnessEnv]
  fb_lk

/-- The witness is at the ladder's exit. -/
theorem epiWitness_divExit (d : Decimal) (digA out : Nat) :
    t3DivExitWord (epiWitness d digA out) := by
  refine ⟨rfl, ?_, ?_⟩
  · show lookupName (epiWitnessEnv d digA out) "%e10.2.i.i" ≠ none
    rw [epiWitnessEnv_e10]
    intro h
    cases h
  · show lookupName (epiWitnessEnv d digA out) "%d201.2.i.i" ≠ none
    rw [epiWitnessEnv_d201_2]
    intro h
    cases h

/-- The witness satisfies the boundary's model tie. -/
theorem epiWitness_model (d : Decimal) (digA out : Nat) :
    fbEpilogueModel d (epiWitness d digA out) := by
  refine ⟨0, ?_, ?_, ?_⟩
  · show lookupName (epiWitnessEnv d digA out) "%v.i.i" = some (.ptr 0)
    exact epiWitnessEnv_v d digA out
  · show lookupName (epiWitnessEnv d digA out) "%.cast.i629.i.i"
      = some (.int 64 (fbPreRound d))
    exact epiWitnessEnv_cast d digA out
  · show lookupName (epiWitnessEnv d digA out) "%d201.3.i.i"
      = some (.float (fbPreRound d))
    exact epiWitnessEnv_d201_3 d digA out

/-- At the witness the epilogue's first block is undefined: the `phi` selects
an `int` and the `bitcastToInt` has no meaning there. -/
theorem epi253_denote_none {calls : Calls} {env : Env} {s : State}
    (hpre : s.pre = some "while.cond229.i.i")
    (hd : lookupName env "%d201.2.i.i" = some (.int 64 0)) :
    denoteCode calls epi253Instrs (stateAt env s) = none := by
  unfold epi253Instrs
  rw [denoteCode_phi calls env s "%d201.3.i.i" Ty.double
    [("while.body232.i.i", (Operand.reg "%div.i.i")),
     ("while.cond229.i.i", (Operand.reg "%d201.2.i.i"))]
    hpre (by decide)
    (evalOperand_reg_of env s "%d201.2.i.i" (.int 64 0) hd)
    [Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")] (by rfl)]
  rw [denoteCode_cons_none calls
    (Instr.bitcastToInt "%.cast.i629.i.i" (Operand.reg "%d201.3.i.i")) []
    (stateAt (("%d201.3.i.i", .int 64 0) :: env) s) ?_]
  simp only [evalInstr]
  rw [show evalOperand (stateAt (("%d201.3.i.i", .int 64 0) :: env) s)
      (.reg "%d201.3.i.i") = some (.int 64 0) from
    evalOperand_reg_of _ _ _ _ (lookupName_cons_self ..)]

/-- The witness's first step is undefined behaviour. -/
theorem epiWitness_step (calls : Calls) (d : Decimal) (digA out : Nat) :
    step calls numFastBody (epiWitness d digA out) = .ub := by
  have hpc : (epiWitness d digA out).pc = "while.end253.i.i" := rfl
  have hfind : numFastBody.findBlock (epiWitness d digA out).pc =
      some ⟨"while.end253.i.i", epi253Instrs, Term.br "for.cond255.i.i"⟩ := by
    rw [hpc]
    exact epi253_find
  have hcode : denoteCode calls epi253Instrs (epiWitness d digA out) = none :=
    epi253_denote_none (calls := calls) (env := (epiWitness d digA out).env)
      (s := epiWitness d digA out) rfl (epiWitnessEnv_d201_2 d digA out)
  unfold step
  simp only [hfind, hcode]

/-- Any fuel past the witness's first step still reads `ub`. -/
theorem runFuel_ub_succ {calls : Calls} {f : Function} {s : State}
    (h : step calls f s = .ub) (n : Nat) :
    runFuel calls (n + 1) f s = some .ub := by
  simp only [runFuel, h]

/-- The witness's run is `ub` at every positive fuel. -/
theorem epiWitness_runFuel_succ (calls : Calls) (d : Decimal) (digA out n : Nat) :
    runFuel calls (n + 1) numFastBody (epiWitness d digA out) = some .ub :=
  runFuel_ub_succ (epiWitness_step calls d digA out) n

/-! ### The calls selection the tail needs, and the refutation

A selection that answers the lifetime marker keeps `if.end291`'s block defined,
which is all the argument needs: from the witness the run is `ub` after one step,
and a state at `if.end291` whose block runs cannot have that run.
-/

/-- A calls selection that answers the lifetime marker and nothing else. -/
def epiCalls : Calls := fun name _ mem next =>
  if name = "llvm.lifetime.end.p0" then
    some { ret := .int 32 0, mem := mem, next := next }
  else none

theorem epiCalls_lifetime (vs : List Value) (mem : Mem) (next : Nat) :
    epiCalls "llvm.lifetime.end.p0" vs mem next
      = some { ret := .int 32 0, mem := mem, next := next } := by
  simp [epiCalls]

/-- `FbEpilogue` is false as stated: its premises are satisfiable at a state the
epilogue's first block makes `ub`, and no `if.end291` state has that run. -/
theorem not_fbEpilogue {d : Decimal} {digA out J : Nat} :
    ¬ FbEpilogue epiCalls d digA out J := by
  intro h
  obtain ⟨f, j, hjJ, hfpc, hfpre, hfbits, hfdig, hfout, hrun⟩ :=
    h (epiWitness d digA out) rfl (epiWitness_divExit d digA out)
      (epiWitness_model d digA out)
  have hstepF := fb_291_step (calls := epiCalls) (env := f.env) (s := f)
    (bits := BitVec.ofNat 64
      (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)
    (digA := digA) (out := out) (r := ⟨.int 32 0, f.mem, f.next⟩)
    hfpc hfpre hfbits hfdig hfout (epiCalls_lifetime _ f.mem f.next)
  have hstepF' : step epiCalls numFastBody f =
      .jump (stateAt (("%retval.1.i.i", .float (BitVec.ofNat 64
        (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)) :: f.env)
        { f with mem := writeBytes f.mem out
                   (natToBytes (BitVec.ofNat 64
                     (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8),
                 next := f.next,
                 pc := "cleanup300", pre := some "if.end291" }) := by
    simpa only [stateAt] using hstepF
  have hnf : runFuel epiCalls 1 numFastBody f = none := by
    have hj := runFuel_jump_prefix (calls := epiCalls) (f := numFastBody) hstepF' 0
    rw [Nat.add_zero] at hj
    exact hj
  cases j with
  | zero =>
      have h1 := hrun 1
      have hud : runFuel epiCalls (0 + 1) numFastBody (epiWitness d digA out)
          = some .ub := epiWitness_runFuel_succ epiCalls d digA out 0
      rw [hud] at h1
      rw [hnf] at h1
      cases h1
  | succ m =>
      have h0 := hrun 0
      have hud : runFuel epiCalls (Nat.succ m + 0) numFastBody
          (epiWitness d digA out) = some .ub := by
        rw [show Nat.succ m + 0 = m + 1 from by omega]
        exact epiWitness_runFuel_succ epiCalls d digA out m
      rw [hud] at h0
      rw [show runFuel epiCalls 0 numFastBody f = none from rfl] at h0
      cases h0

/-! ### The clause that holds

The boundary must name the cells the blocks read rather than the ones they
write: `%d201.2.i.i` for the pre-round word and `%cmp1.i` for the sign.  The
conclusion is `FbEpilogue`'s, so the fallback's tail is unchanged.
-/

/-- The tie the epilogue's own blocks consume: the head's edge cell, and the
sign the select reads.  On a well-formed lexeme the reader binds `%cmp1.i` to
`if d.neg then 1 else 0` (`epiSign_of_scan`). -/
def FbEpilogueTie (d : Decimal) (e : State) : Prop :=
  fbEpilogueModel d e ∧
  lookupName e.env "%d201.2.i.i" = some (.float (fbPreRound d)) ∧
  lookupName e.env "%cmp1.i" = some (.int 1 (if d.neg then 1 else 0))

/-- The epilogue's boundary at the cells its blocks read. -/
def FbEpilogueAt (calls : Calls) (d : Decimal) (digA out J : Nat) : Prop :=
  ∀ (e : State), e.pc = "while.end253.i.i" → t3DivExitWord e →
    FbEpilogueTie d e →
    ∃ (f : State) (j : Nat), j ≤ J ∧
      f.pc = "if.end291" ∧ f.pre = some "for.end359.i.i" ∧
      lookupName f.env "%cond366.i.i"
        = some (.float (BitVec.ofNat 64
            (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)) ∧
      lookupName f.env "%dig.i.i" = some (.ptr digA) ∧
      lookupName f.env "%out" = some (.ptr out) ∧
      ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody f

/-- **The reader's sign cell is the decomposition's.**  The scan binds `%cmp1.i`
to the first byte's `-` test, and `sl_sign_tie` reads it as `d.neg`: this is the
sign clause `FbEpilogueAt` asks for, supplied by the seam rather than the
epilogue. -/
theorem epiSign_of_scan {env : Env} {b0 : UInt8} {d : Decimal}
    (hd : d.wellFormed) (hb : d.lexeme.toList.head? = some b0)
    (h : lookupName env "%cmp1.i" = some (.int 1 (slSignBit b0))) :
    lookupName env "%cmp1.i" = some (.int 1 (if d.neg then 1 else 0)) := by
  have ht := sl_sign_tie hd hb
  rw [ht] at h
  exact h

/-- The witness does not satisfy the corrected tie: its `%d201.2.i.i` is an
`int`, so the corrected preconditions exclude the false model. -/
theorem epiWitness_notTie (d : Decimal) (digA out : Nat) :
    ¬ FbEpilogueTie d (epiWitness d digA out) := by
  intro ht
  obtain ⟨-, hd2, -⟩ := ht
  rw [show (epiWitness d digA out).env = epiWitnessEnv d digA out from rfl] at hd2
  rw [epiWitnessEnv_d201_2] at hd2
  cases hd2

/-- **The fallback's tail from a stated epilogue run.**  The witness the
boundary supplies is all the tail reads; this is `fb_tail`'s derivation at the
tuple rather than at the hypothesis. -/
theorem fb_tail_of_witness {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed) (hStart : FbStart291 calls digA)
    (e f : State) (j : Nat) (hjJ : j ≤ J)
    (hfpc : f.pc = "if.end291") (hfpre : f.pre = some "for.end359.i.i")
    (hfbits : lookupName f.env "%cond366.i.i"
      = some (.float (BitVec.ofNat 64
          (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)))
    (hfdig : lookupName f.env "%dig.i.i" = some (.ptr digA))
    (hfout : lookupName f.env "%out" = some (.ptr out))
    (hrun : ∀ k, runFuel calls (j + k) numFastBody e = runFuel calls k numFastBody f) :
    ∃ (o : CallOutcome) (r : CallOutcome),
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨r, hr⟩ := hStart f hfpc hfpre
  have hbitsEq : (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits
      = (strtodSpec d).toBits := fb_model_bits hd
  have hstoreNat : (BitVec.ofNat 64
      (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat
      = (strtodSpec d).toBits := by
    rw [hbitsEq]
    exact fb_store_word (NumFastTier1.strtodSpec_toBits_lt d)
  have hstep1 := fb_291_step (calls := calls) (env := f.env) (s := f)
    (bits := BitVec.ofNat 64
      (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)
    (digA := digA) (out := out) (r := r) hfpc hfpre hfbits hfdig hfout hr
  have hstep2 := fb_cleanup300_step (calls := calls)
    (env := ("%retval.1.i.i", .float (BitVec.ofNat 64
      (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits)) :: f.env)
    (s := { f with
      mem := writeBytes r.mem out
        (natToBytes (BitVec.ofNat 64
          (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8),
      next := r.next, pc := "cleanup300", pre := some "if.end291" }) rfl rfl
  have hrun2 : runFuel calls 2 numFastBody f =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out
          (natToBytes (BitVec.ofNat 64
            (StrtodTier3.tier3Emitted StrtodReader.reader d.lexeme).toBits).toNat 8))) := by
    change runFuel calls 2 numFastBody (stateAt f.env f) = _
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix hstep1 1]
    simp only [runFuel, hstep2]
    rfl
  have hrest : runFuel calls 2 numFastBody f =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) := by
    have h := hrun2
    rw [hstoreNat] at h
    simpa only [wordBytes] using h
  have hprefix : runFuel calls (j + 2) numFastBody e =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) := by
    rw [hrun 2]
    exact hrest
  have hfull : runFuel calls (J + 2) numFastBody (stateAt e.env e) =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits))) := by
    rw [show stateAt e.env e = e from rfl]
    exact runFuel_mono_le (by omega) hprefix
  refine ⟨⟨.int 32 1, writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits),
    r.next⟩, r, hfull, rfl, rfl, rfl, ?_⟩
  exact (UnchangedOutside.refl' r.mem [(out, 8), (err, 8)]).write_le
    (a := out) (w := 8) (bs := wordBytes 8 (strtodSpec d).toBits)
    ⟨(out, 8), by simp, le_rfl, by omega⟩
    (by simp only [wordBytes, natToBytes_length, le_rfl])

/-- **The corrected boundary carries the fallback's tail.**  The conclusion is
`fb_tail`'s, at the tie the epilogue's blocks read. -/
theorem fb_tail_at {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed)
    (hEpi : FbEpilogueAt calls d digA out J)
    (hStart : FbStart291 calls digA)
    (e : State) (hpc : e.pc = "while.end253.i.i") (hword : t3DivExitWord e)
    (htie : FbEpilogueTie d e) :
    ∃ (o : CallOutcome) (r : CallOutcome),
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] := by
  obtain ⟨f, j, hjJ, hfpc, hfpre, hfbits, hfdig, hfout, hrun⟩ :=
    hEpi e hpc hword htie
  exact fb_tail_of_witness hd hStart e f j hjJ hfpc hfpre hfbits hfdig hfout hrun

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.epi253_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi253_step

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.epi255_step_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi255_step_zero

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.epi359_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi359_step

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.epiWitness_runFuel_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epiWitness_runFuel_succ

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.not_fbEpilogue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms not_fbEpilogue

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueShape.fb_tail_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fb_tail_at

end NumFastEpilogueShape

end LeanLLVM.Refinement
