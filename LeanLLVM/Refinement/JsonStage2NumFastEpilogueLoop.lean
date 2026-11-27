/-
The epilogue's rounding loop, and the callee it cannot run without.

`FbEpilogueAt` (`JsonStage2NumFastEpilogueShape`) asks the run from
`while.end253.i.i` to reach `if.end291`'s inlet with the model's rounded word.
The blocks in between are `for.cond255.i.i`'s rounding search: nineteen blocks
whose exit is decided by five `stk_cmp` calls, comparing the carried pattern
against the boundary the code forms.  This module states what that search is
decided by, and proves that the release selection cannot run it.

**The loop's first iteration reads `stk_cmp`, two blocks in.**  From the head's
nonzero arm the first callee is `if.end273.i.i`'s `%call291.i.i`; from the zero
arm it is `if.then258.i.i`'s `%call259.i.i`.  Both are `ub` when the selection
answers no `stk_cmp`, and so is the head's `if.then267.i.i` arm.  The entry's own
step (`epi253_step`) and the head's two arms (`epi255_step_zero`,
`epi255_step_nonzero`) are the pieces this module composes with the four blocks'
`ub` steps: from `while.end253.i.i` the run reaches `some .ub` within four
control steps (`epi253_run_ub`).

**The release selection leaves `stk_cmp` unanswered.**  `stage2NumFastCalls`
answers the conversion's three modelled callees and delegates the rest to
`s2HelperCalls`, which answers the lifetime markers, `memset` and the trap only.
`stk_cmp` is a fourth out-of-line function of the same C file and is not in the
callee half, so at that selection the loop is `ub` before its first comparison
(`stage2NumFastCalls_stk_cmp`).

**`FbEpilogueAt` is therefore false at the release selection.**  `if.end291`'s
own block resolves — its lifetime marker is answered and `cleanup300` returns —
so a state at the inlet runs to `some (.ret …)` in two steps
(`epi_tail_ne_ub`), while the entry's run is `some .ub`.  A `runFuel` prefix
cannot match `some .ub` against `some (.ret …)` at any fuel
(`not_fbEpilogueAt_of_unanswered`, and `not_fbEpilogueAt_stage2FastCalls` at the
release selection).  This is not a defect of the clause's statement at the
cells the loop reads: it says the epilogue's callee has to be part of the
selection before the loop can be stated at all.

**What the consumer needs.**  `FbStkCmpAnswered` is the callee half's fourth
entry, and `FbEpilogueAnswered` is `FbEpilogueAt` at a selection that has it.
`fb_tail_answered` is `fb_tail_at` at that clause, so the fallback's tail is
unchanged once the callee is answered; `fbEpilogueAnswered_not_release` is the
release selection failing the half.  The loop's invariant belongs at the
answered selection: its counter is the carried pattern, its exit test is the
sign the five calls return, and neither is a function of the state and the
counter alone — which is why `BoundLoop`'s `atBound : State → Nat → Bool` cannot
place this loop's exit, and why the four `ub` steps below are where the head's
iteration ends at the release selection.

There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastEpilogueShape
import LeanLLVM.Refinement.JsonStage2NumFastCalls

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR (evalInstr_icmp)
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3Rows
open LeanLLVM.Refinement.NumFastTier3Ladder
open LeanLLVM.Refinement.NumFastScanSlow
open LeanLLVM.Refinement.NumFastFallback
open LeanLLVM.Refinement.NumFastEpilogueShape
open LeanLLVM.JSON
open LeanLLVM.StrtodRefine

namespace NumFastEpilogueLoop

/-! ### The one-bit readings

`evalICmp` is `BitVec.ofBool` of the comparison, so its two values are the
predicate and its negation.  Stated here so the head's arms and the two-arm
blocks below read their terms at a bit rather than at the `if`. -/

theorem ofBool_one_of {p : Prop} [Decidable p] (h : p) :
    BitVec.ofBool p = (1 : BitVec 1) := by
  simp [BitVec.ofBool, h]

theorem ofBool_zero_of_not {p : Prop} [Decidable p] (h : ¬ p) :
    BitVec.ofBool p = (0 : BitVec 1) := by
  simp [BitVec.ofBool, h]

/-! ### The four blocks the first iteration's frontier is

`if.then258.i.i` and `if.then267.i.i` open with `stk_cmp`; `if.end264.i.i` tests
the carried word against the largest finite pattern and leaves for one of them
or for `if.end273.i.i`, whose own `stk_cmp` is its eighth instruction.  The four
pins are the trace's. -/

/-- `if.then258.i.i`, at its pin: the empty arm's `stk_cmp`, and its sign test. -/
def epi258Instrs : List Instr :=
  [Instr.call "%call259.i.i" (Ty.int 32) "stk_cmp"
     [(Ty.ptr, (Operand.reg "%v.i.i")),
      ((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000001#64))),
      ((Ty.int 64), (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)))],
   Instr.icmp "%cmp260.i.i" (IPred.sgt) 32 (Operand.reg "%call259.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem epi258_find :
    numFastBody.findBlock "if.then258.i.i" =
      some ⟨"if.then258.i.i", epi258Instrs,
        Term.condbr (Operand.reg "%cmp260.i.i") "for.cond255.i.i.backedge"
          "for.end359.i.i"⟩ := by
  simpa only [epi258Instrs] using numFast_findBlock_if_then258_i_i

/-- `if.end264.i.i`: the carried word against the largest finite pattern. -/
def epi264Instrs : List Instr :=
  [Instr.icmp "%cmp265.i.i" (IPred.ugt) 64 (Operand.reg "%b.0.i.i")
     (Operand.imm (Const.int 64 0x7fefffffffffffff#64))]

theorem epi264_find :
    numFastBody.findBlock "if.end264.i.i" =
      some ⟨"if.end264.i.i", epi264Instrs,
        Term.condbr (Operand.reg "%cmp265.i.i") "if.then267.i.i"
          "if.end273.i.i"⟩ := by
  simpa only [epi264Instrs] using numFast_findBlock_if_end264_i_i

/-- `if.then267.i.i`, at its pin: the overflow arm's `stk_cmp` and its sign. -/
def epi267Instrs : List Instr :=
  [Instr.call "%call268.i.i" (Ty.int 32) "stk_cmp"
     [(Ty.ptr, (Operand.reg "%v.i.i")),
      ((Ty.int 64), (Operand.imm (Const.int 64 0x003fffffffffffff#64))),
      ((Ty.int 64), (Operand.imm (Const.int 64 0x00000000000003ca#64)))],
   Instr.icmp "%cmp269.i.i" (IPred.slt) 32 (Operand.reg "%call268.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem epi267_find :
    numFastBody.findBlock "if.then267.i.i" =
      some ⟨"if.then267.i.i", epi267Instrs,
        Term.condbr (Operand.reg "%cmp269.i.i") "for.cond255.i.i.backedge"
          "for.end359.i.i"⟩ := by
  simpa only [epi267Instrs] using numFast_findBlock_if_then267_i_i

/-- `if.end273.i.i`, at its pin: the pattern's two fields, the three-value
boundary, and the exact `stk_cmp`. -/
def epi273Instrs : List Instr :=
  [Instr.binop "%shr.i.i" (BinOp.lshr) 64 (Operand.reg "%b.0.i.i")
     (Operand.imm (Const.int 64 0x0000000000000034#64)),
   Instr.icmp "%cmp275.i.i" (IPred.ult) 64 (Operand.reg "%b.0.i.i")
     (Operand.imm (Const.int 64 0x0010000000000000#64)),
   Instr.binop "%and280.i.i" (BinOp.and) 64 (Operand.reg "%b.0.i.i")
     (Operand.imm (Const.int 64 0x000fffffffffffff#64)),
   Instr.binop "%or.i.i" (BinOp.or) 64 (Operand.reg "%and280.i.i")
     (Operand.imm (Const.int 64 0x0010000000000000#64)),
   Instr.select "%cond282.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i")
     (Operand.reg "%b.0.i.i") (Operand.reg "%or.i.i"),
   Instr.binop "%sub288.i.i" (BinOp.add) 64 (Operand.reg "%shr.i.i")
     (Operand.imm (Const.int 64 0xfffffffffffffbcd#64)),
   Instr.select "%cond290.i.i" (Ty.int 64) (Operand.reg "%cmp275.i.i")
     (Operand.imm (Const.int 64 0xfffffffffffffbce#64)) (Operand.reg "%sub288.i.i"),
   Instr.call "%call291.i.i" (Ty.int 32) "stk_cmp"
     [(Ty.ptr, (Operand.reg "%v.i.i")),
      ((Ty.int 64), (Operand.reg "%cond282.i.i")),
      ((Ty.int 64), (Operand.reg "%cond290.i.i"))],
   Instr.icmp "%cmp292.i.i" (IPred.eq) 32 (Operand.reg "%call291.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem epi273_find :
    numFastBody.findBlock "if.end273.i.i" =
      some ⟨"if.end273.i.i", epi273Instrs,
        Term.condbr (Operand.reg "%cmp292.i.i") "for.end359.i.i"
          "if.end295.i.i"⟩ := by
  simpa only [epi273Instrs] using numFast_findBlock_if_end273_i_i

/-! ### An unanswered `call` ends a block

`denoteCode_call_none` asks for the argument list the block's own operands
produce; the four blocks below do not read their arguments' values, only whether
the callee answers, so the premise is the weaker `∀ vs, calls … = none`. -/

/-- A `call` whose callee answers nothing makes the block undefined, whatever
its operands read. -/
theorem denoteCode_call_none_any (calls : Calls) (env : Env) (s : State)
    (d : String) (ty : Ty) (callee : String) (args : List (Ty × Operand))
    (is : List Instr)
    (hnone : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls callee vs mem next = none) :
    denoteCode calls (.call d ty callee args :: is) (stateAt env s) = none := by
  simp only [denoteCode, denoteRun, evalInstr, State.bindAll]
  cases h : evalOperands (stateAt env s) args with
  | none => rfl
  | some vs =>
      simp only [hnone vs (stateAt env s).mem (stateAt env s).next]

/-- `if.then258.i.i` is undefined where `stk_cmp` is unanswered. -/
theorem epi258_denote_none {calls : Calls} {env : Env} {s : State}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none) :
    denoteCode calls epi258Instrs (stateAt env s) = none := by
  unfold epi258Instrs
  exact denoteCode_call_none_any calls env s "%call259.i.i" (Ty.int 32) "stk_cmp"
    _ _ hstk

theorem epi258_step_ub {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.then258.i.i")
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none) :
    step calls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.then258.i.i", epi258Instrs,
        Term.condbr (Operand.reg "%cmp260.i.i") "for.cond255.i.i.backedge"
          "for.end359.i.i"⟩ := by
    rw [show (stateAt env s).pc = "if.then258.i.i" from hpc]
    exact epi258_find
  simp only [step, hfind, epi258_denote_none hstk]

/-- `if.then267.i.i` is undefined where `stk_cmp` is unanswered. -/
theorem epi267_denote_none {calls : Calls} {env : Env} {s : State}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none) :
    denoteCode calls epi267Instrs (stateAt env s) = none := by
  unfold epi267Instrs
  exact denoteCode_call_none_any calls env s "%call268.i.i" (Ty.int 32) "stk_cmp"
    _ _ hstk

theorem epi267_step_ub {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "if.then267.i.i")
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none) :
    step calls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.then267.i.i", epi267Instrs,
        Term.condbr (Operand.reg "%cmp269.i.i") "for.cond255.i.i.backedge"
          "for.end359.i.i"⟩ := by
    rw [show (stateAt env s).pc = "if.then267.i.i" from hpc]
    exact epi267_find
  simp only [step, hfind, epi267_denote_none hstk]

/-- `%d = select i1 %c, <a>, %b` — the immediate-true form `if.end273.i.i`'s
second select uses. -/
theorem step_select_imm_reg (calls : Calls) (env : Env) (s : State) (d c b : String)
    {bb : BitVec 1} {y z : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int 64 z)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 64) (.reg c) (.imm (.int 64 y)) (.reg b)) =
      some (stateAt ((d, .int 64 (if bb = 1 then y else z)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [if_neg (by decide)]
    have hstep := JsonS1MasksIR.evalInstr_select_false (calls := calls)
      (s := stateAt env s) (d := d) (ty := (.int 64)) (c := (.reg c))
      (a := (.imm (.int 64 y))) (b := (.reg b))
      (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := evalOperand_lit_of _ 64 y)
      (hb := evalOperand_reg_of env s b (.int 64 z) hb)
    rw [hstep]
    simp only [stateAt, State.bind]
  · subst h
    rw [if_pos rfl]
    have hstep := JsonS1MasksIR.evalInstr_select_true (calls := calls)
      (s := stateAt env s) (d := d) (ty := (.int 64)) (c := (.reg c))
      (a := (.imm (.int 64 y))) (b := (.reg b))
      (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := evalOperand_lit_of _ 64 y)
      (hb := evalOperand_reg_of env s b (.int 64 z) hb)
    rw [hstep]
    simp only [stateAt, State.bind]

theorem denoteCode_select_imm_reg (calls : Calls) (env : Env) (s : State)
    (d c b : String) {bb : BitVec 1} {y z : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (hb : lookupName env b = some (.int 64 z)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.imm (.int 64 y)) (.reg b) :: is)
        (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int 64 (if bb = 1 then y else z)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_imm_reg calls env s d c b hc hb)]

/-! ### `if.end273.i.i`'s prefix, with its cells

The block's seven instructions read only the carried word; the environment they
build is `epi273Env`, and the block reaches its `stk_cmp` there. -/

/-- The cells `if.end273.i.i`'s prefix binds, in the pin's order. -/
def epi273Env (env : Env) (b : BitVec 64) : Env :=
  ("%cond290.i.i", .int 64
      (if evalICmp .ult b 0x0010000000000000#64 = 1 then
        0xfffffffffffffbce#64
       else (b >>> (0x0000000000000034#64).toNat) + 0xfffffffffffffbcd#64)) ::
  ("%sub288.i.i", .int 64
      ((b >>> (0x0000000000000034#64).toNat) + 0xfffffffffffffbcd#64)) ::
  ("%cond282.i.i", .int 64
      (if evalICmp .ult b 0x0010000000000000#64 = 1 then b
       else (b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
  ("%or.i.i", .int 64
      ((b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
  ("%and280.i.i", .int 64 (b &&& 0x000fffffffffffff#64)) ::
  ("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
  ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env

/-- The block's prefix, as one chain step: the seven instructions land in
`epi273Env` and the run continues at the `stk_cmp`. -/
theorem epi273_denote_call {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b)) :
    denoteCode calls epi273Instrs (stateAt env s) =
      denoteCode calls
        [Instr.call "%call291.i.i" (Ty.int 32) "stk_cmp"
           [(Ty.ptr, (Operand.reg "%v.i.i")),
            ((Ty.int 64), (Operand.reg "%cond282.i.i")),
            ((Ty.int 64), (Operand.reg "%cond290.i.i"))],
         Instr.icmp "%cmp292.i.i" (IPred.eq) 32 (Operand.reg "%call291.i.i")
           (Operand.imm (Const.int 32 0x00000000#32))]
        (stateAt (epi273Env env b) s) := by
  unfold epi273Instrs
  rw [denoteCode_lshr_imm calls env s "%shr.i.i" "%b.0.i.i" (x := b) hb]
  rw [denoteCode_icmp_ult_imm calls
    (("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%cmp275.i.i" "%b.0.i.i" (x := b) (by block_lk)]
  rw [denoteCode_and_imm calls
    (("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
      ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%and280.i.i" "%b.0.i.i" (x := b) (c := 0x000fffffffffffff#64)
    (by block_lk)]
  rw [denoteCode_or_imm calls
    (("%and280.i.i", .int 64 (b &&& 0x000fffffffffffff#64)) ::
      ("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
      ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%or.i.i" "%and280.i.i" (x := b &&& 0x000fffffffffffff#64)
    (c := 0x0010000000000000#64) (by block_lk)]
  rw [denoteCode_select_bit_reg calls
    (("%or.i.i", .int 64
        ((b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
      ("%and280.i.i", .int 64 (b &&& 0x000fffffffffffff#64)) ::
      ("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
      ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%cond282.i.i" "%cmp275.i.i" "%b.0.i.i" "%or.i.i"
    (bb := evalICmp .ult b 0x0010000000000000#64) (x := b)
    (y := (b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)
    (by block_lk) (by block_lk) (by block_lk)]
  rw [denoteCode_add_imm calls
    (("%cond282.i.i", .int 64
        (if evalICmp .ult b 0x0010000000000000#64 = 1 then b
         else (b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
      ("%or.i.i", .int 64
        ((b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
      ("%and280.i.i", .int 64 (b &&& 0x000fffffffffffff#64)) ::
      ("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
      ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%sub288.i.i" "%shr.i.i" (x := b >>> (0x0000000000000034#64).toNat)
    (c := 0xfffffffffffffbcd#64) (by block_lk)]
  rw [denoteCode_select_imm_reg calls
    (("%sub288.i.i", .int 64
        ((b >>> (0x0000000000000034#64).toNat) + 0xfffffffffffffbcd#64)) ::
      ("%cond282.i.i", .int 64
        (if evalICmp .ult b 0x0010000000000000#64 = 1 then b
         else (b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
      ("%or.i.i", .int 64
        ((b &&& 0x000fffffffffffff#64) ||| 0x0010000000000000#64)) ::
      ("%and280.i.i", .int 64 (b &&& 0x000fffffffffffff#64)) ::
      ("%cmp275.i.i", .int 1 (evalICmp .ult b 0x0010000000000000#64)) ::
      ("%shr.i.i", .int 64 (b >>> (0x0000000000000034#64).toNat)) :: env) s
    "%cond290.i.i" "%cmp275.i.i" "%sub288.i.i"
    (bb := evalICmp .ult b 0x0010000000000000#64) (y := 0xfffffffffffffbce#64)
    (z := (b >>> (0x0000000000000034#64).toNat) + 0xfffffffffffffbcd#64)
    (by block_lk) (by block_lk)]
  simp only [epi273Env]

/-- `if.end273.i.i` reaches its `stk_cmp` and is undefined there. -/
theorem epi273_denote_none {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b)) :
    denoteCode calls epi273Instrs (stateAt env s) = none := by
  rw [epi273_denote_call (calls := calls) hb]
  exact denoteCode_call_none_any calls _ _ "%call291.i.i" (Ty.int 32) "stk_cmp"
    _ _ hstk

theorem epi273_step_ub {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hpc : s.pc = "if.end273.i.i")
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b)) :
    step calls numFastBody (stateAt env s) = .ub := by
  have hfind : numFastBody.findBlock (stateAt env s).pc =
      some ⟨"if.end273.i.i", epi273Instrs,
        Term.condbr (Operand.reg "%cmp292.i.i") "for.end359.i.i"
          "if.end295.i.i"⟩ := by
    rw [show (stateAt env s).pc = "if.end273.i.i" from hpc]
    exact epi273_find
  simp only [step, hfind, epi273_denote_none hstk hb]

/-! ### `if.end264.i.i`: the two-arm block

The block is one `icmp ugt`; its terminator takes `if.then267.i.i` at `1` and
`if.end273.i.i` at `0`, both of which the previous section leaves undefined. -/

theorem epi264_denote {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b)) :
    denoteCode calls epi264Instrs (stateAt env s) =
      some (stateAt
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env)
        s) := by
  unfold epi264Instrs
  rw [denoteCode_icmp_ugt_imm calls env s "%cmp265.i.i" "%b.0.i.i" hb []]
  simp only [denoteCode_nil, stateAt]

theorem epi264_step_one {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hpc : s.pc = "if.end264.i.i")
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b))
    (hbit : evalICmp .ugt b 0x7fefffffffffffff#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env)
        { s with pc := "if.then267.i.i", pre := some "if.end264.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt
      (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env) s)
    (b := ⟨"if.end264.i.i", epi264Instrs,
      Term.condbr (Operand.reg "%cmp265.i.i") "if.then267.i.i"
        "if.end273.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi264_find
  · simpa only [stateAt] using epi264_denote (calls := calls) hb
  · rw [numFast_execTerm_condbr_one
      (s := stateAt
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env) s)
      "%cmp265.i.i" "if.then267.i.i" "if.end273.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

theorem epi264_step_zero {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hpc : s.pc = "if.end264.i.i")
    (hb : lookupName env "%b.0.i.i" = some (.int 64 b))
    (hbit : evalICmp .ugt b 0x7fefffffffffffff#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env)
        { s with pc := "if.end273.i.i", pre := some "if.end264.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt
      (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env) s)
    (b := ⟨"if.end264.i.i", epi264Instrs,
      Term.condbr (Operand.reg "%cmp265.i.i") "if.then267.i.i"
        "if.end273.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epi264_find
  · simpa only [stateAt] using epi264_denote (calls := calls) hb
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) :: env) s)
      "%cmp265.i.i" "if.then267.i.i" "if.end273.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The head's two arms, run to `ub`

`epi255_step_zero`/`epi255_step_nonzero` leave the head for `if.then258.i.i` and
`if.end264.i.i`; the blocks above end the run there.  `if.end264.i.i`'s target
depends on one `icmp`, so its arm splits on that bit. -/

/-- From the head at a zero word, the run is `ub` after two steps. -/
theorem epi255_run_ub_zero {calls : Calls} {env : Env} {s : State}
    {b : BitVec 64} {p : String} {op : Operand}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hpc : s.pc = "for.cond255.i.i")
    (hpre : s.pre = some p) (hinc : phiIncoming p epi255Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 b))
    (hbit : evalICmp .eq b 0x0#64 = (1 : BitVec 1)) :
    runFuel calls 2 numFastBody (stateAt env s) = some .ub := by
  rw [show (2 : Nat) = 1 + 1 from rfl,
    runFuel_jump_prefix
      (epi255_step_zero (calls := calls) (env := env) hpc hpre hinc hop hbit) 1]
  have hub : step calls numFastBody
      (stateAt
        (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
          ("%b.0.i.i", .int 64 b) :: env)
        { s with pc := "if.then258.i.i", pre := some "for.cond255.i.i" }) = .ub :=
    epi258_step_ub (by simp only [stateAt]) hstk
  simp only [runFuel, hub]

/-- From the head at a nonzero word, the run is `ub` after three steps,
whichever way `if.end264.i.i` leaves. -/
theorem epi255_run_ub_nonzero {calls : Calls} {env : Env} {s : State}
    {b : BitVec 64} {p : String} {op : Operand}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hpc : s.pc = "for.cond255.i.i")
    (hpre : s.pre = some p) (hinc : phiIncoming p epi255Inc = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 b))
    (hbit : evalICmp .eq b 0x0#64 = (0 : BitVec 1)) :
    runFuel calls 3 numFastBody (stateAt env s) = some .ub := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl,
    runFuel_jump_prefix
      (epi255_step_nonzero (calls := calls) (env := env) hpc hpre hinc hop hbit)
      (1 + 1)]
  have hb' : lookupName
      (("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
        ("%b.0.i.i", .int 64 b) :: env) "%b.0.i.i" = some (.int 64 b) := by
    rw [lookupName_cons_ne _ _ (by decide)]
    exact lookupName_cons_self ..
  rcases bitVec1_eq_zero_or_one (evalICmp .ugt b 0x7fefffffffffffff#64) with h | h
  · rw [show (1 + 1 : Nat) = 1 + 1 from rfl,
      runFuel_jump_prefix
        (epi264_step_zero (calls := calls) (env :=
          ("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
            ("%b.0.i.i", .int 64 b) :: env)
          (s := { s with pc := "if.end264.i.i", pre := some "for.cond255.i.i" })
          (by simp only [stateAt]) hb' h) 1]
    have hb273 : lookupName
        (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) ::
          ("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
          ("%b.0.i.i", .int 64 b) :: env) "%b.0.i.i" = some (.int 64 b) := by
      rw [lookupName_cons_ne _ _ (by decide),
        lookupName_cons_ne _ _ (by decide)]
      exact lookupName_cons_self ..
    have hub : step calls numFastBody
        (stateAt
          (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) ::
            ("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
            ("%b.0.i.i", .int 64 b) :: env)
          { s with pc := "if.end273.i.i", pre := some "if.end264.i.i" }) = .ub :=
      epi273_step_ub (by simp only [stateAt]) hstk hb273
    simp only [runFuel, hub]
  · rw [show (1 + 1 : Nat) = 1 + 1 from rfl,
      runFuel_jump_prefix
        (epi264_step_one (calls := calls) (env :=
          ("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
            ("%b.0.i.i", .int 64 b) :: env)
          (s := { s with pc := "if.end264.i.i", pre := some "for.cond255.i.i" })
          (by simp only [stateAt]) hb' h) 1]
    have hub : step calls numFastBody
        (stateAt
          (("%cmp265.i.i", .int 1 (evalICmp .ugt b 0x7fefffffffffffff#64)) ::
            ("%cmp256.i.i", .int 1 (evalICmp .eq b 0x0#64)) ::
            ("%b.0.i.i", .int 64 b) :: env)
          { s with pc := "if.then267.i.i", pre := some "if.end264.i.i" }) = .ub :=
      epi267_step_ub (by simp only [stateAt]) hstk
    simp only [runFuel, hub]

/-! ### From the epilogue's entry

The entry's own block is `epi253_step`; the head follows at either arm, and both
end in `ub` within three more steps.  Four steps cover the longer arm. -/

/-- **The loop's first iteration is `ub` where `stk_cmp` is unanswered.**  From
`while.end253.i.i`'s edge the run stops within four control steps. -/
theorem epi253_run_ub {calls : Calls} {env : Env} {s : State} {b : BitVec 64}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hpc : s.pc = "while.end253.i.i")
    (hpre : s.pre = some "while.cond229.i.i")
    (hd : lookupName env "%d201.2.i.i" = some (.float b)) :
    runFuel calls 4 numFastBody (stateAt env s) = some .ub := by
  have hstep := epi253_step (calls := calls) hpc hpre hd
  have hinc : phiIncoming "while.end253.i.i" epi255Inc =
      some (Operand.reg "%.cast.i629.i.i") := by
    simp [epi255Inc, phiIncoming]
  have hop : evalOperand
      (stateAt (epi253Env env b)
        { s with pc := "for.cond255.i.i", pre := some "while.end253.i.i" })
      (Operand.reg "%.cast.i629.i.i") = some (.int 64 b) :=
    evalOperand_reg_of _ _ _ _ (lookupName_cons_self ..)
  rcases eq_or_ne b 0 with hb0 | hbne
  · subst hb0
    have hbit : evalICmp .eq (0 : BitVec 64) 0x0#64 = (1 : BitVec 1) :=
      ofBool_one_of rfl
    have hrun := epi255_run_ub_zero (calls := calls) (env := epi253Env env 0)
      (s := { s with pc := "for.cond255.i.i", pre := some "while.end253.i.i" })
      hstk (by simp only [stateAt]) (by simp only [stateAt]) hinc hop hbit
    rw [show (4 : Nat) = 1 + (2 + 1) from rfl, runFuel_jump_prefix hstep (2 + 1)]
    exact runFuel_mono_le (by omega) hrun
  · have hbit : evalICmp .eq b 0x0#64 = (0 : BitVec 1) :=
      ofBool_zero_of_not hbne
    have hrun := epi255_run_ub_nonzero (calls := calls) (env := epi253Env env b)
      (s := { s with pc := "for.cond255.i.i", pre := some "while.end253.i.i" })
      hstk (by simp only [stateAt]) (by simp only [stateAt]) hinc hop hbit
    rw [show (4 : Nat) = 1 + (3 + 0) from rfl, runFuel_jump_prefix hstep (3 + 0)]
    simpa using hrun

/-! ### The witness, and the clause's failure at the release selection -/

/-- The witness's environment: the tie's cells, the loop's `%v.i.i`, and the
sign cell the exit reads. -/
def epiLoopEnv (d : Decimal) (v : Nat) : Env :=
  [("%v.i.i", .ptr v),
   ("%e10.2.i.i", .int 64 0),
   ("%d201.3.i.i", .float (fbPreRound d)),
   ("%.cast.i629.i.i", .int 64 (fbPreRound d)),
   ("%d201.2.i.i", .float (fbPreRound d)),
   ("%cmp1.i", .int 1 (if d.neg then 1 else 0))]

/-- The witness: at the epilogue's entry, entered from the ladder's head. -/
def epiLoopState (d : Decimal) (v : Nat) : State :=
  { env := epiLoopEnv d v, mem := [], next := 0,
    pc := "while.end253.i.i", pre := some "while.cond229.i.i" }

theorem epiLoopEnv_v (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%v.i.i" = some (.ptr v) := by
  simp only [epiLoopEnv]; fb_lk

theorem epiLoopEnv_d201_3 (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%d201.3.i.i" = some (.float (fbPreRound d)) := by
  simp only [epiLoopEnv]; fb_lk

theorem epiLoopEnv_cast (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%.cast.i629.i.i" =
      some (.int 64 (fbPreRound d)) := by
  simp only [epiLoopEnv]; fb_lk

theorem epiLoopEnv_d201_2 (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%d201.2.i.i" = some (.float (fbPreRound d)) := by
  simp only [epiLoopEnv]; fb_lk

theorem epiLoopEnv_e10 (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%e10.2.i.i" = some (.int 64 0) := by
  simp only [epiLoopEnv]; fb_lk

theorem epiLoopEnv_cmp (d : Decimal) (v : Nat) :
    lookupName (epiLoopEnv d v) "%cmp1.i" =
      some (.int 1 (if d.neg then 1 else 0)) := by
  simp only [epiLoopEnv]; fb_lk

/-- The witness is at the ladder's exit. -/
theorem epiLoop_exitWord (d : Decimal) (v : Nat) :
    t3DivExitWord (epiLoopState d v) := by
  refine ⟨rfl, ?_, ?_⟩
  · show lookupName (epiLoopEnv d v) "%e10.2.i.i" ≠ none
    rw [epiLoopEnv_e10]; intro h; cases h
  · show lookupName (epiLoopEnv d v) "%d201.2.i.i" ≠ none
    rw [epiLoopEnv_d201_2]; intro h; cases h

/-- The witness satisfies the corrected tie. -/
theorem epiLoop_tie (d : Decimal) (v : Nat) :
    FbEpilogueTie d (epiLoopState d v) := by
  refine ⟨⟨v, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show lookupName (epiLoopEnv d v) "%v.i.i" = some (.ptr v)
    exact epiLoopEnv_v d v
  · show lookupName (epiLoopEnv d v) "%.cast.i629.i.i" =
      some (.int 64 (fbPreRound d))
    exact epiLoopEnv_cast d v
  · show lookupName (epiLoopEnv d v) "%d201.3.i.i" =
      some (.float (fbPreRound d))
    exact epiLoopEnv_d201_3 d v
  · show lookupName (epiLoopEnv d v) "%d201.2.i.i" =
      some (.float (fbPreRound d))
    exact epiLoopEnv_d201_2 d v
  · show lookupName (epiLoopEnv d v) "%cmp1.i" =
      some (.int 1 (if d.neg then 1 else 0))
    exact epiLoopEnv_cmp d v

/-- At the witness, the loop's first comparison is unanswered and the run
stops. -/
theorem epiLoop_run_ub {calls : Calls}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (d : Decimal) (v : Nat) :
    runFuel calls 4 numFastBody (epiLoopState d v) = some .ub :=
  epi253_run_ub (calls := calls) (env := epiLoopEnv d v)
    (s := epiLoopState d v) (b := fbPreRound d) hstk rfl rfl
    (epiLoopEnv_d201_2 d v)

/-- **A state at `if.end291` does not run to `ub`.**  Its lifetime marker is
answered by the selection's hypothesis, so the store executes and `cleanup300`
returns; the run completes within two steps and stays completed. -/
theorem epi_tail_ne_ub {calls : Calls}
    (hlife : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, calls "llvm.lifetime.end.p0" vs mem next = some r)
    {f : State} {bits : BitVec 64} {digA out J : Nat}
    (hfpc : f.pc = "if.end291") (hfpre : f.pre = some "for.end359.i.i")
    (hbits : lookupName f.env "%cond366.i.i" = some (.float bits))
    (hdig : lookupName f.env "%dig.i.i" = some (.ptr digA))
    (hout : lookupName f.env "%out" = some (.ptr out)) :
    runFuel calls (4 + J + 2) numFastBody f ≠ some .ub := by
  obtain ⟨r, hr⟩ := hlife [.int 64 0x0000000000000300#64, .ptr digA] f.mem f.next
  have hstep1 := fb_291_step (calls := calls) (env := f.env) (s := f) (bits := bits)
    (digA := digA) (out := out) (r := r) hfpc hfpre hbits hdig hout hr
  have hstep2 := fb_cleanup300_step (calls := calls)
    (env := ("%retval.1.i.i", .float bits) :: f.env)
    (s := { f with
      mem := writeBytes r.mem out (natToBytes bits.toNat 8),
      next := r.next, pc := "cleanup300", pre := some "if.end291" }) rfl rfl
  have hrun2 : runFuel calls 2 numFastBody f =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (natToBytes bits.toNat 8))) := by
    change runFuel calls 2 numFastBody (stateAt f.env f) = _
    rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix hstep1 1]
    simp only [runFuel, hstep2]
    rfl
  have hrun : runFuel calls (4 + J + 2) numFastBody f =
      some (.ret (some (.int 32 1))
        (writeBytes r.mem out (natToBytes bits.toNat 8))) :=
    runFuel_mono_le (by omega) hrun2
  intro h
  rw [hrun] at h
  cases h

/-- **`FbEpilogueAt` fails where `stk_cmp` is unanswered and the lifetime marker
is answered.**  The entry's run is `ub` within four steps; the boundary's
witness at `if.end291` completes, so the run prefix cannot be shared. -/
theorem not_fbEpilogueAt_of_unanswered {calls : Calls}
    (hstk : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      calls "stk_cmp" vs mem next = none)
    (hlife : ∀ (vs : List Value) (mem : Mem) (next : Nat),
      ∃ r : CallOutcome, calls "llvm.lifetime.end.p0" vs mem next = some r)
    (d : Decimal) (digA out J : Nat) :
    ¬ FbEpilogueAt calls d digA out J := by
  intro h
  obtain ⟨f, j, _hjJ, hfpc, hfpre, hfbits, hfdig, hfout, hrun⟩ :=
    h (epiLoopState d 0) rfl (epiLoop_exitWord d 0) (epiLoop_tie d 0)
  have hub : runFuel calls 4 numFastBody (epiLoopState d 0) = some .ub :=
    epiLoop_run_ub hstk d 0
  have htail := epi_tail_ne_ub (calls := calls) (J := J) hlife hfpc hfpre
    hfbits hfdig hfout
  have heq := hrun (4 + J + 2)
  have hub' : runFuel calls (j + (4 + J + 2)) numFastBody (epiLoopState d 0) =
      some .ub :=
    runFuel_mono_le (by omega) hub
  rw [hub'] at heq
  exact htail heq.symm

/-! ### The release selection

`stage2NumFastCalls` answers the conversion's three modelled callees and the
walk's markers; `stk_cmp` is not among them. -/

theorem s2HelperCalls_stk_cmp (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "stk_cmp" args mem next = none := rfl

theorem s2HelperCalls_lifetime_end (args : List Value) (mem : Mem) (next : Nat) :
    s2HelperCalls "llvm.lifetime.end.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := rfl

theorem stage2NumFastCalls_stk_cmp (epow : Int → Option EPow) (args : List Value)
    (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "stk_cmp" args mem next = none := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("stk_cmp" = "num_d8_el1")),
    if_neg (by decide : ¬ ("stk_cmp" = "num_el_el1")),
    if_neg (by decide : ¬ ("stk_cmp" = "stk_mul_u64")),
    if_neg (by decide : ¬ ("stk_cmp" = "__memcpy_chk")),
    s2HelperCalls_stk_cmp]

theorem stage2NumFastCalls_lifetime_end (epow : Int → Option EPow)
    (args : List Value) (mem : Mem) (next : Nat) :
    stage2NumFastCalls epow "llvm.lifetime.end.p0" args mem next =
      some { ret := .int 1 0, mem := mem, next := next } := by
  simp only [stage2NumFastCalls, numFastCalls,
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "num_d8_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "num_el_el1")),
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "stk_mul_u64")),
    if_neg (by decide : ¬ ("llvm.lifetime.end.p0" = "__memcpy_chk")),
    s2HelperCalls_lifetime_end]

/-- **The epilogue's clause is false at the release selection.** -/
theorem not_fbEpilogueAt_stage2FastCalls (epow : Int → Option EPow)
    (d : Decimal) (digA out J : Nat) :
    ¬ FbEpilogueAt (stage2NumFastCalls epow) d digA out J := by
  refine not_fbEpilogueAt_of_unanswered
    (fun vs mem next => stage2NumFastCalls_stk_cmp epow vs mem next) ?_ d digA out J
  intro vs mem next
  exact ⟨_, stage2NumFastCalls_lifetime_end epow vs mem next⟩

/-! ### The head's invariant

The rounding search carries a pattern and reads its exit from the callee, so the
invariant a proof of the loop states is over the head's cells only.  `epi255Inv`
is that shape: the head, the two in-edges its `phi` selects between, the carried
pattern, and the caller's two read cells.  Its `r` is the iteration budget a
`BoundLoop` would charge; that instance cannot exist, because `BoundLoop`'s
`atBound : State → Nat → Bool` must name the exit and this loop's exit is the
sign of `stk_cmp`'s answers three blocks in — a fact about the selection, which
the invariant cannot carry and the state cannot show.  The release selection also
fails `FbStkCmpAnswered` (`stage2NumFastCalls_not_stkCmpAnswered`), so the loop's
`step_loop` has no inhabited case there at all. -/

/-- The head's carried state: the pattern, the in-edge, and the caller's two
read cells. -/
def epi255Inv (d : Decimal) (v : Nat) : Nat → State → Nat → Prop :=
  fun _r s c =>
    s.pc = "for.cond255.i.i" ∧
    (s.pre = some "while.end253.i.i" ∨
      s.pre = some "for.cond255.i.i.backedge") ∧
    lookupName s.env "%b.0.i.i" = some (.int 64 (BitVec.ofNat 64 c)) ∧
    lookupName s.env "%v.i.i" = some (.ptr v) ∧
    lookupName s.env "%cmp1.i" = some (.int 1 (if d.neg then 1 else 0))

theorem epi255Inv_pc {d : Decimal} {v r c : Nat} {s : State}
    (h : epi255Inv d v r s c) : s.pc = "for.cond255.i.i" := h.1

theorem epi255Inv_pre {d : Decimal} {v r c : Nat} {s : State}
    (h : epi255Inv d v r s c) :
    s.pre = some "while.end253.i.i" ∨ s.pre = some "for.cond255.i.i.backedge" :=
  h.2.1

theorem epi255Inv_word {d : Decimal} {v r c : Nat} {s : State}
    (h : epi255Inv d v r s c) :
    lookupName s.env "%b.0.i.i" = some (.int 64 (BitVec.ofNat 64 c)) := h.2.2.1

theorem epi255Inv_v {d : Decimal} {v r c : Nat} {s : State}
    (h : epi255Inv d v r s c) :
    lookupName s.env "%v.i.i" = some (.ptr v) := h.2.2.2.1

theorem epi255Inv_sign {d : Decimal} {v r c : Nat} {s : State}
    (h : epi255Inv d v r s c) :
    lookupName s.env "%cmp1.i" = some (.int 1 (if d.neg then 1 else 0)) :=
  h.2.2.2.2

/-! ### What the consumer needs

The callee half's fourth entry: a selection that answers `stk_cmp`.  At such a
selection `FbEpilogueAt` is the clause the loop is stated at, and
`fb_tail_answered` is the fallback's tail there — the same conclusion `fb_tail_at`
draws from `FbEpilogueAt` without it. -/

/-- The selection answers the epilogue's comparison. -/
def FbStkCmpAnswered (calls : Calls) : Prop :=
  ∀ (vs : List Value) (mem : Mem) (next : Nat),
    ∃ r : CallOutcome, calls "stk_cmp" vs mem next = some r

/-- The epilogue's boundary at a selection that answers its callee. -/
def FbEpilogueAnswered (calls : Calls) (d : Decimal) (digA out J : Nat) : Prop :=
  FbStkCmpAnswered calls ∧ FbEpilogueAt calls d digA out J

/-- The release selection does not answer `stk_cmp`. -/
theorem stage2NumFastCalls_not_stkCmpAnswered (epow : Int → Option EPow) :
    ¬ FbStkCmpAnswered (stage2NumFastCalls epow) := by
  intro h
  obtain ⟨r, hr⟩ := h [] [] 0
  rw [stage2NumFastCalls_stk_cmp epow [] [] 0] at hr
  cases hr

/-- **The fallback's tail at the answered selection.**  The conclusion is
`fb_tail_at`'s, at the clause the loop can be stated at. -/
theorem fb_tail_answered {calls : Calls} {d : Decimal} {out err digA J : Nat}
    (hd : d.wellFormed)
    (hEpi : FbEpilogueAnswered calls d digA out J)
    (hStart : FbStart291 calls digA)
    (e : State) (hpc : e.pc = "while.end253.i.i") (hword : t3DivExitWord e)
    (htie : FbEpilogueTie d e) :
    ∃ (o : CallOutcome) (r : CallOutcome),
      runFuel calls (J + 2) numFastBody (stateAt e.env e) =
        some (.ret (some o.ret) o.mem) ∧
      o.ret = .int 32 1 ∧
      o.next = r.next ∧
      o.mem = writeBytes r.mem out (wordBytes 8 (strtodSpec d).toBits) ∧
      UnchangedOutside r.mem o.mem [(out, 8), (err, 8)] :=
  fb_tail_at hd hEpi.2 hStart e hpc hword htie

/-- The release selection is not the epilogue's boundary: the answered clause
fails there before its run clause is read. -/
theorem fbEpilogueAnswered_not_release (epow : Int → Option EPow)
    (d : Decimal) (digA out J : Nat) :
    ¬ FbEpilogueAnswered (stage2NumFastCalls epow) d digA out J := by
  intro h
  exact stage2NumFastCalls_not_stkCmpAnswered epow h.1

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi258_step_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi258_step_ub

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi273_step_ub' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi273_step_ub

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi264_step_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi264_step_one

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi255_run_ub_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi255_run_ub_zero

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi255_run_ub_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms epi255_run_ub_nonzero

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi253_run_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms epi253_run_ub

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.epi_tail_ne_ub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms epi_tail_ne_ub

/-- info: 'LeanLLVM.Refinement.NumFastEpilogueLoop.fb_tail_answered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fb_tail_answered

-- The two long names wrap at the printer's width; their lists are
-- `[propext, Classical.choice, Quot.sound]` as well.
#print axioms not_fbEpilogueAt_of_unanswered
#print axioms not_fbEpilogueAt_stage2FastCalls

end NumFastEpilogueLoop

end LeanLLVM.Refinement
