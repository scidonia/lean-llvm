/-
A block evaluator: `denoteCode` of a straight-line block, derived by a tactic.

This repository's block proofs are written per block: `JsonEscapeListBody` spends
about nine hundred and fifty lines on three blocks, and the cost is not the
arithmetic.  It is that every instruction is a `rw` against a step lemma whose
operand and result values the author must *name*, and every register read is a
`lookupName … = some …` hypothesis the author must state and carry into the next
lemma's signature.  A body with a thirty-seven-instruction loop body in four
arm-specialised copies cannot be written that way.

This module is the vocabulary that makes the chain a computation instead of an
authoring act.  It has three parts.

**1. The environment is a builder, not a hypothesis list.**  `cells` prepends a
list of cells to an incoming environment, newest first, so the environment after
`k` instructions is *definitionally* the builder applied to the first `k` cells
of the block's own statement.  A block's statement therefore names the cells it
reads — the caller's parameters included — and no register read appears as a
hypothesis.  `JsonEscapeListBody`'s idiom states `hbs`, `hshl`, … for exactly
those cells; here they are the builder's entries.

**2. A `lookupName` is decided by `String` equality, once.**  `lookupName_cons_self`
and `lookupName_cons_ne` in `Basic.lean` are the only two facts needed, and the
`block_lk` tactic below applies them against the builder's own cells: the name is
a literal, so the disequality is `decide`-able, and the value comes from the
cell rather than from unification with a hypothesis.  The tactic's order matters
and is documented at its definition: peeling is attempted before any
definitional equation is, because a failed `isDefEq` can leave a metavariable
assigned from a branch it then rejects.

**3. One chain step per instruction shape.**  Each `denoteCode_*` lemma is the
`denoteCode_cons_of` step for one `evalInstr`-shaped wrapper — the shape this
tree already uses (`b_load64`, `step_gep64`, `phi_step`) — covering the
operand-staging instructions the pipeline's blocks use beyond the
already-automated `binop`/`load`/`icmp`: `gep`, `phi`, `trunc`, `select`, and
call-argument staging.  A step's value arguments are *implicit*, so the chain
leaves them to be decided by the block's own statement.  A step's value
arguments and its side goals share their metavariables, so the statement's
builder and the side goals name one set of values rather than two; the join
between them is made by *when* the main equation is checked, not by a formula
that identifies the two.  The first `rfl` compares the run's environment with
the builder while the values are still open, the side goals then fix them —
each register read resolved against the builder fixes the value the statement
names — and the last `rfl` closes the equation against those assignments.

**What a block proof looks like.**  State
`denoteCode calls instrs (stateAt envIn s) = some (stateAt envOut s)` where
`envIn`/`envOut` are `cells` builders, then `block_eval`.  The tactic rewrites
one instruction at a time, discharges the side goals the steps left — the
semantic facts (`readBytes`, the call's outcome, the `getelementptr` bound) from
the statement's hypotheses, and the register reads from the builder — and only
then closes the main equation by `rfl`.  Running that last check after the side
goals is what joins the statement's values to the ones the lookups assign; a
check before them is a check on unassigned metavariables.

**What it is not.**  It does not prove a block's *statement*, only compute a
block's `denoteCode`; the address bound, the memory facts and the call outcomes
are the caller's, as they are in every block proof in this tree.
-/
import LeanLLVM.Vellum.JsonS1MasksIR

set_option autoImplicit false

namespace LeanLLVM.Vellum.BlockEval

open LeanLLVM
open LeanLLVM.Vellum.JsonS1MasksIR
  (evalInstr_load evalInstr_binop evalInstr_icmp evalInstr_select_true
   evalInstr_select_false evalInstr_zext evalInstr_store evalInstr_call)

/-! ### The environment builder -/

/-- A state seen as its environment.  Everything a straight-line step does not
touch — memory, the allocator cursor, the block, the predecessor — is carried
through unchanged. -/
def stateAt (env : Env) (s : State) : State := { s with env := env }

/-- A cell list prepended to an incoming environment, newest first.  Written as
a right fold so that one step's conclusion, `(d, v) :: env`, is definitionally
the builder applied to the cells taken so far: no `show` reconciliation per
instruction. -/
def cells : List (String × Value) → Env → Env
  | [], env => env
  | c :: cs, env => c :: cells cs env

theorem stateAt_stateAt (env env' : Env) (s : State) :
    stateAt env' (stateAt env s) = stateAt env' s := rfl

theorem stateAt_mem (env : Env) (s : State) : (stateAt env s).mem = s.mem := rfl

theorem stateAt_next (env : Env) (s : State) : (stateAt env s).next = s.next := rfl

theorem stateAt_pre (env : Env) (s : State) : (stateAt env s).pre = s.pre := rfl

/-- A register read at the state's environment, from the environment's own
lookup: the hypothesis a step lemma consumes, in the one shape every wrapper
below names. -/
theorem evalOperand_reg_of (env : Env) (s : State) (n : String) (v : Value)
    (h : lookupName env n = some v) : evalOperand (stateAt env s) (.reg n) = some v := by
  simp only [stateAt, evalOperand, h]

/-- A literal integer operand reads to its value. -/
theorem evalOperand_lit_of (s : State) (w : Nat) (c : BitVec w) :
    evalOperand s (.imm (.int w c)) = some (.int w c) := rfl

/-- Straight-line composition: an instruction that resolves to a state leaves the
rest of the list to be run from it. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s') :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  simp [denoteCode, h]

/-- The eight bytes of a 64-bit word are `2 ^ 64`. -/
theorem pow256_eight : (256 : Nat) ^ 8 = 2 ^ 64 := by decide

/-- A 64-bit load at a readable byte range. -/
theorem loadValue_i64_of_readBytes {m : Mem} {a : Nat} {bs : List UInt8}
    (hr : readBytes m a 8 = some bs) :
    loadValue m (.int 64) a = some (.int 64 (BitVec.ofNat 64 (bytesToNat bs))) := by
  simp only [loadValue, show (64 + 7) / 8 = 8 from rfl,
    show (64 = 0) = False from by decide, ite_false, hr]

/-! ### The register lookup

Resolve a register read against the environment builder: unfold the builder,
peel the cells the block bound before it, take the cell the name is, or — for a
name the block did not bind — the caller's environment.

The order is the point.  Peeling is `lookupName_cons_ne` with a `decide`-able
disequality, and taking the cell is `lookupName_cons_self`; neither asks
`isDefEq` to reduce `lookupName`, which it cannot do soundly here: `lookupName`
reduces to an `if` on a `String` equality, and a definitional equation that
cannot decide that `if` can leave the value metavariable assigned from the
branch it then rejects.  `assumption` and `rfl` are tried only once the peel has
stopped, where the left-hand side is a whole cell and no `if` remains. -/
macro "block_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only [cells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | rw [lookupName_cons_self]
       | assumption
       | rfl)))

/-! ### Binary operations

Each is `evalInstr_binop` at the operation's own meaning, stated at `BitVec` so
the successor block reads a word rather than the `Nat` boundary
`evalBinopNat` passes through.  The two value arguments are implicit: a block's
statement fixes them, and the chain leaves them to it. -/

/-- `%d = or i64 %a, %b`. -/
theorem step_or_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .or 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x ||| y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x ||| y).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = and i64 %a, %b`. -/
theorem step_and_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .and 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x &&& y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x &&& y).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = xor i64 %a, %b`. -/
theorem step_xor_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .xor 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x ^^^ y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x ^^^ y).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = add i64 %a, %b`. -/
theorem step_add_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .add 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x + y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x + y).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = sub i64 %a, %b`. -/
theorem step_sub_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .sub 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (x - y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x - y).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = or i64 %a, <c>`. -/
theorem step_or_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .or 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x ||| c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x ||| c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = and i64 %a, <c>`. -/
theorem step_and_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .and 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x &&& c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x &&& c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = xor i64 %a, <c>`. -/
theorem step_xor_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .xor 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x ^^^ c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x ^^^ c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = add i64 %a, <c>`. -/
theorem step_add_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .add 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x + c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x + c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = shl i64 %a, <c>`. -/
theorem step_shl_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .shl 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x <<< c.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x <<< c.toNat).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = lshr i64 %a, <c>`. -/
theorem step_lshr_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.binop d .lshr 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 64 (x >>> c.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (x >>> c.toNat).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = shl i64 <c>, %b` — the mask form a variable shift count produces. -/
theorem step_shl_lit (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64}
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .shl 64 (.imm (.int 64 c)) (.reg b)) =
      some (stateAt ((d, .int 64 (c <<< y.toNat)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using evalInstr_binop (r := (c <<< y.toNat).toNat)
      (ha := evalOperand_lit_of _ 64 c)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-! ### Comparisons -/

/-- `%d = icmp eq i64 %a, %b`. -/
theorem step_icmp_eq_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.icmp d .eq 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)

/-- `%d = icmp eq i64 %a, <c>`. -/
theorem step_icmp_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.icmp d .eq 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)

/-- `%d = icmp ult i64 %a, <c>`. -/
theorem step_icmp_ult_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.icmp d .ult 64 (.reg a) (.imm (.int 64 c))) =
      some (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)

/-- `%d = icmp ult i64 %a, %b`. -/
theorem step_icmp_ult_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.icmp d .ult 64 (.reg a) (.reg b)) =
      some (stateAt ((d, .int 1 (evalICmp .ult x y)) :: env) s) := by
  simpa only [stateAt, State.bind]
    using evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_reg_of env s b (.int 64 y) hb)

/-! ### Selection, truncation, offset -/

/-- `%d = select i1 %c, %a, %b`, the condition set. -/
theorem step_select_reg_true (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 x) :: env) s) := by
  rw [evalInstr_select_true (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [stateAt, State.bind]

/-- `%d = select i1 %c, %a, %b`, the condition clear. -/
theorem step_select_reg_false (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 y) :: env) s) := by
  rw [evalInstr_select_false (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [stateAt, State.bind]

/-- `%d = select i1 %c, %a, <b>`, the condition set: the arm the emission writes
as a literal. -/
theorem step_select_reg_imm_true (calls : Calls) (env : Env) (s : State) (d c a : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y))) =
      some (stateAt ((d, .int 64 x) :: env) s) := by
  rw [evalInstr_select_true (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 y)]
  simp only [stateAt, State.bind]

/-- `%d = select i1 %c, %a, <b>`, the condition clear. -/
theorem step_select_reg_imm_false (calls : Calls) (env : Env) (s : State) (d c a : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y))) =
      some (stateAt ((d, .int 64 y) :: env) s) := by
  rw [evalInstr_select_false (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 y)]
  simp only [stateAt, State.bind]

/-- `%d = trunc iN %v to iM`. -/
theorem step_trunc (calls : Calls) (env : Env) (s : State) (d v : String) (wIn wOut : Nat)
    {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) :
    evalInstr calls (stateAt env s) (.trunc d wIn wOut (.reg v)) =
      some (stateAt ((d, .int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut))) :: env) s) := by
  simp only [evalInstr, evalOperand, stateAt, hv, State.bind]
  rfl

/-- `%d = zext iN %v to iM`. -/
theorem step_zext (calls : Calls) (env : Env) (s : State) (d v : String) (wIn wOut : Nat)
    {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) :
    evalInstr calls (stateAt env s) (.zext d wIn wOut (.reg v)) =
      some (stateAt ((d, .int wOut (BitVec.ofNat wOut x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s v (.int wIn x) hv)]
  simp [stateAt, State.bind]

/-- `%d = getelementptr i8, ptr %base, i64 %off`, at an index below `2 ^ 63`. -/
theorem step_gep8_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat)) :: env) s) := by
  rw [evalInstr_gep_i8 (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho) (hpos := hpos)]
  simp only [stateAt, State.bind]

/-- Every one-bit value is zero or one: the fact a data-dependent `select`
needs, since the instruction's own test is `bit = 1` and the model's other arm is
`bit = 0`. -/
theorem bitVec1_eq_zero_or_one (b : BitVec 1) : b = 0 ∨ b = 1 := by
  have hb : b = BitVec.ofNat 1 b.toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [hb]
  have hlt : b.toNat = 0 ∨ b.toNat = 1 := by omega
  rcases hlt with h | h <;> rw [h] <;> decide

/-- `%d = select i1 %c, %a, <b>` at a condition the block *computed*: the branch
is the value's own test, so a data-dependent select is a value rather than a
case split in the block's statement. -/
theorem step_select_bit_imm (calls : Calls) (env : Env) (s : State) (d c a : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y))) =
      some (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [if_neg (by decide)]
    exact step_select_reg_imm_false calls env s d c a hc ha
  · subst h
    rw [if_pos rfl]
    exact step_select_reg_imm_true calls env s d c a hc ha

/-- `%d = select i1 %c, %a, %b` at a condition the block *computed*. -/
theorem step_select_bit_reg (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.select d (.int 64) (.reg c) (.reg a) (.reg b)) =
      some (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [if_neg (by decide)]
    exact step_select_reg_false calls env s d c a b hc ha hb
  · subst h
    rw [if_pos rfl]
    exact step_select_reg_true calls env s d c a b hc ha hb

/-! ### Memory and calls -/

/-- `%d = load i64, ptr %p`, at the eight bytes a word occupies. -/
theorem step_load64 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 64}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) :
    evalInstr calls (stateAt env s) (.load d (.int 64) (.reg p)) =
      some (stateAt ((d, .int 64 v) :: env) s) := by
  have hv' : loadValue s.mem (.int 64) a = some (.int 64 v) := by
    rw [loadValue_i64_of_readBytes hv, natToBytes_toNat, pow256_eight,
      Nat.mod_eq_of_lt v.isLt]
    simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by simpa only [stateAt] using hv')]
  simp [stateAt, State.bind]

/-- `store i64 %v, ptr %p`. -/
theorem step_store64 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 64) (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [evalInstr_store (vv := .int 64 x) (a := a)
    (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
    (hv := evalOperand_reg_of env s v (.int 64 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]
  simp [storeValue, stateAt]

/-- `%d = phi i64 [ %a, %p ], [ <c>, %q ]` reached from `p`: the selected
operand's value, with the selection's own fact supplied by the caller because it
reads the predecessor field. -/
theorem step_phi (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (inc : List (String × Operand)) {p : String} {op : Operand} {v : Value}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some v) :
    evalInstr calls (stateAt env s) (.phi d ty inc) =
      some (stateAt ((d, v) :: env) s) := by
  rw [evalInstr_phi (s := stateAt env s) hpre hinc hop]
  rfl

/-- A three-pointer call that binds nothing: the mask unit's staging. -/
theorem step_callVoid3 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 o3 : Operand) {v1 v2 v3 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (hc : calls callee [v1, v2, v3] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.ptr, o1), (Ty.ptr, o2), (Ty.ptr, o3)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.ptr, o2), (Ty.ptr, o3)] = some [v1, v2, v3] := by
    simp only [evalOperands, h1, h2, h3]
  have hc' : calls callee [v1, v2, v3] (stateAt env s).mem (stateAt env s).next
      = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-- A five-argument call that binds its result: the position body's staging,
with the fourth argument a literal and the rest registers. -/
theorem step_call5 (calls : Calls) (env : Env) (s : State) (d callee : String)
    {ty : Ty} (o1 o2 o4 o5 : Operand) {v1 v2 v4 v5 : Value} {c3 : BitVec 64}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (hc : calls callee [v1, v2, .int 64 c3, v4, v5] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d ty callee [(Ty.ptr, o1), (Ty.int 64, o2),
          (Ty.int 64, .imm (.int 64 c3)), (Ty.ptr, o4), (Ty.int 64, o5)]) =
      some (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.ptr, o1), (Ty.int 64, o2), (Ty.int 64, .imm (.int 64 c3)),
        (Ty.ptr, o4), (Ty.int 64, o5)] = some [v1, v2, .int 64 c3, v4, v5] := by
    simp only [evalOperands, h1, h2, evalOperand_lit_of, h4, h5]
  have hc' : calls callee [v1, v2, .int 64 c3, v4, v5] (stateAt env s).mem
      (stateAt env s).next = some r := hc
  simp only [evalInstr, hargs, hc']
  rfl

/-! ### The chain steps

One `denoteCode` step per wrapper above: the rewrite unit the whole-block tactic
selects by the instruction's shape.  Each is the wrapper through
`denoteCode_cons_of`, and nothing else. -/

theorem denoteCode_or_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.binop d .or 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x ||| y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_or_reg calls env s d a b ha hb)]

theorem denoteCode_and_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.binop d .and 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x &&& y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_and_reg calls env s d a b ha hb)]

theorem denoteCode_xor_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.binop d .xor 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x ^^^ y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_xor_reg calls env s d a b ha hb)]

theorem denoteCode_add_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.binop d .add 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x + y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_add_reg calls env s d a b ha hb)]

theorem denoteCode_sub_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.binop d .sub 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x - y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_sub_reg calls env s d a b ha hb)]

theorem denoteCode_or_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .or 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x ||| c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_or_imm calls env s d a ha)]

theorem denoteCode_and_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .and 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x &&& c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_and_imm calls env s d a ha)]

theorem denoteCode_xor_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .xor 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x ^^^ c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_xor_imm calls env s d a ha)]

theorem denoteCode_add_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .add 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_add_imm calls env s d a ha)]

theorem denoteCode_shl_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .shl 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x <<< c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_shl_imm calls env s d a ha)]

theorem denoteCode_lshr_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.binop d .lshr 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (x >>> c.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_lshr_imm calls env s d a ha)]

theorem denoteCode_shl_lit (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64}
    (hb : lookupName env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.binop d .shl 64 (.imm (.int 64 c)) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (c <<< y.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_shl_lit calls env s d b hb)]

theorem denoteCode_icmp_eq_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.icmp d .eq 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_eq_reg calls env s d a b ha hb)]

theorem denoteCode_icmp_eq_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.icmp d .eq 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_eq_imm calls env s d a ha)]

theorem denoteCode_icmp_ult_imm (calls : Calls) (env : Env) (s : State) (d a : String)
    {x c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls (.icmp d .ult 64 (.reg a) (.imm (.int 64 c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_ult_imm calls env s d a ha)]

theorem denoteCode_icmp_ult_reg (calls : Calls) (env : Env) (s : State) (d a b : String)
    {x y : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.icmp d .ult 64 (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 1 (evalICmp .ult x y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_icmp_ult_reg calls env s d a b ha hb)]

theorem denoteCode_select_reg_true (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.select d (.int 64) (.reg c) (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 x) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_reg_true calls env s d c a b hc ha hb)]

theorem denoteCode_select_reg_false (calls : Calls) (env : Env) (s : State) (d c a b : String)
    {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y))
    (is : List Instr) :
    denoteCode calls (.select d (.int 64) (.reg c) (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 y) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_reg_false calls env s d c a b hc ha hb)]

theorem denoteCode_select_reg_imm_true (calls : Calls) (env : Env) (s : State)
    (d c a : String) {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 x) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_reg_imm_true calls env s d c a hc ha)]

theorem denoteCode_select_reg_imm_false (calls : Calls) (env : Env) (s : State)
    (d c a : String) {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 y) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_reg_imm_false calls env s d c a hc ha)]

theorem denoteCode_select_bit_imm (calls : Calls) (env : Env) (s : State)
    (d c a : String) {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x)) (is : List Instr) :
    denoteCode calls
        (.select d (.int 64) (.reg c) (.reg a) (.imm (.int 64 y)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_bit_imm calls env s d c a hc ha)]

theorem denoteCode_select_bit_reg (calls : Calls) (env : Env) (s : State)
    (d c a b : String) {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb))
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.select d (.int 64) (.reg c) (.reg a) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_bit_reg calls env s d c a b hc ha hb)]

theorem denoteCode_trunc (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) (is : List Instr) :
    denoteCode calls (.trunc d wIn wOut (.reg v) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt ((d, .int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut))) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_trunc calls env s d v wIn wOut hv)]

theorem denoteCode_zext (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) (is : List Instr) :
    denoteCode calls (.zext d wIn wOut (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int wOut (BitVec.ofNat wOut x.toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_zext calls env s d v wIn wOut hv)]

theorem denoteCode_gep8_reg (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.reg base) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_gep8_reg calls env s d base off hb ho hpos)]

theorem denoteCode_load64 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 64}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) (is : List Instr) :
    denoteCode calls (.load d (.int 64) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_load64 calls env s d p hp hv)]

theorem denoteCode_store64 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 64} {a : Nat}
    (hv : lookupName env v = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_store64 calls env s v p hv hp)]

theorem denoteCode_phi (calls : Calls) (env : Env) (s : State) (d : String) (ty : Ty)
    (inc : List (String × Operand)) {p : String} {op : Operand} {v : Value}
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (stateAt env s) op = some v) (is : List Instr) :
    denoteCode calls (.phi d ty inc :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, v) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_phi calls env s d ty inc hpre hinc hop)]

theorem denoteCode_callVoid3 (calls : Calls) (env : Env) (s : State) (callee : String)
    (o1 o2 o3 : Operand) {v1 v2 v3 : Value} {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h3 : evalOperand (stateAt env s) o3 = some v3)
    (hc : calls callee [v1, v2, v3] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.callVoid callee [(Ty.ptr, o1), (Ty.ptr, o2), (Ty.ptr, o3)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_callVoid3 calls env s callee o1 o2 o3 h1 h2 h3 hc)]

theorem denoteCode_call5 (calls : Calls) (env : Env) (s : State) (d callee : String)
    {ty : Ty} (o1 o2 o4 o5 : Operand) {v1 v2 v4 v5 : Value} {c3 : BitVec 64}
    {r : CallOutcome}
    (h1 : evalOperand (stateAt env s) o1 = some v1)
    (h2 : evalOperand (stateAt env s) o2 = some v2)
    (h4 : evalOperand (stateAt env s) o4 = some v4)
    (h5 : evalOperand (stateAt env s) o5 = some v5)
    (hc : calls callee [v1, v2, .int 64 c3, v4, v5] s.mem s.next = some r)
    (is : List Instr) :
    denoteCode calls
        (.call d ty callee [(Ty.ptr, o1), (Ty.int 64, o2),
          (Ty.int 64, .imm (.int 64 c3)), (Ty.ptr, o4), (Ty.int 64, o5)] :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env) { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_call5 calls env s d callee o1 o2 o4 o5 h1 h2 h4 h5 hc)]

/-! ### The whole-block tactic -/

/-- One instruction of a block: the chain step whose instruction shape matches.
Each branch is the step alone; the side goals are left for the phases below,
because a step's value arguments are decided by the block's statement and the
values are not available until it has been closed. -/
macro "block_step" : tactic => `(tactic|
  (first
   | rw [denoteCode_or_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_and_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_xor_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_add_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_sub_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_or_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_and_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_xor_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_shl_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_lshr_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_shl_lit _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_eq_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_icmp_eq_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_ult_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_icmp_ult_reg _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_imm _ _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_bit_reg _ _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_trunc _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_zext _ _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_gep8_reg _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_load64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store64 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_phi _ _ _ _ _ _ ?_ ?_ ?_ _]
   | rw [denoteCode_callVoid3 _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ _]
   | rw [denoteCode_call5 _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_ ?_ _]))

/-- Close a block once its chain has run: the side goals the steps left, then
the statement's own environment.

The phases are ordered by what fixes the values, and the order is the join.  A
step's side goals and its conclusion share the step's value metavariables, so
the register reads resolved against the builder fix the values the statement's
cells name; the semantic facts come from the statement's hypotheses.  The main
equation is therefore checked *after* those goals: the first `rfl` only compares
the unfolded run with the builder, the side goals assign the values, and the
last `rfl` closes the equation against those assignments.  Checking it earlier
compares the builder with values that the lookups have not yet fixed. -/
macro "block_close" : tactic => `(tactic|
  (all_goals (try (simp (config := { failIfUnchanged := false }) only [cells, denoteCode]))
   all_goals (try rfl)
   all_goals (try
     (first
      | assumption
      | block_lk
      | (simp only [phiIncoming]; rfl)
      | rfl
      | (exact evalOperand_lit_of _ _ _)))
   all_goals (try rfl)))

/-- A whole straight-line block: every instruction's chain step, then
`block_close`. -/
macro "block_eval" : tactic => `(tactic|
  (repeat block_step
   block_close))

end LeanLLVM.Vellum.BlockEval
