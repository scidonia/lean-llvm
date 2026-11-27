/-
The `to_double` interior's block steps, from the parse to the copy's entry.

`JsonStage2NumFastFallback` states the fallback's seam with two boundaries as
hypotheses: `FbCopyEntryPos`/`FbCopyEntryNeg` (the copy's entry through the
`T`/`F` parse, the lead clamps and the big multiply to the ladder's head) and
`FbEpilogue` (the rounding loop and the sign select to `if.end291`).  This
module supplies the per-edge steps those boundaries are built from, each at its
own `findBlock` pin and each with the environment its chain leaves:

* the `T`/`F` parse — `for.body.outer.i.i`'s head with its two edges, the peel's
  guard `if.then13.i.peel.i` and its exit `if.end28.i.i.loopexit609`, the inner
  loop's entry `for.inc.thread.i.peel.i`, body `for.body.i.i`, digit guard
  `if.then13.i.i`, latch `for.inc.thread.i.i` and refusal
  `if.else46.i.thread.i`, the non-digit edge `if.else46.i.i`, the parse's end
  `for.end.i.i`, the residue exit `if.end28.i.i` with its two edges, the outer
  latch `for.inc.i.i` with its four edges, and the store `if.then31.i.i`'s steps
  over `JsonStage2NumFastTier3`'s chain, and the accumulation `if.then36.i.i`;
* the parse's exit band — the exponent's entry `if.then64.i.i`, the sign's read
  `land.lhs.true68.i.i`, the switch `NodeBlock25`/`LeafBlock23`/`LeafBlock21`,
  the sign's write `if.then77.i.i`, and the merge `if.end83.i.i` with its four
  edges;
* the copy's exit and the lead clamps — `for.end100.i.i`'s exit edge,
  `if.end104.i.i`'s copy edge, the two saturating clamps
  `if.then113.i.i`/`if.then123.i.i`, the underflow test `if.end120.i.i`, and the
  staging `if.end126.i.i`, with the four instruction shapes the clamp band adds
  (`sub` at a literal's left, `select` of two floating literals, the lifetime
  call, and the two generic forms `getelementptr`/`store` at a literal offset);
* the parse's exit path — `parse_exit_run_nosign`/`parse_exit_run_sign` compose
  the steps into one `runFuel` run from `if.else46.i.i` to the copy's entry on
  both of the switch's outcomes;
* the parse's zero exit `if.then59.i.i` — the block's step and `Then59Entry`,
  with each of its five arms' runs into the return's merge `if.end291` — and the
  copy's two preheaders `for.body87.i.i.preheader`/`.preheader.new`, whose two
  boundaries are `Pre87EpilEntry` (the residual loop's entry) and
  `Pre87CopyEntry` (the copy's head), with `end83Env_i2`/`end83Env_n`/
  `end83Env_p` supplying the dispatch's copy edge's cells.

The blocks the copy's own statements already cover (`for.body87.i.i`'s nest,
its residual loop and the handoff) are composed from
`JsonStage2NumFastTier3CopyUnroll`/`JsonStage2NumFastTier3Handoff`, not
restated here; the two preheaders above are the entry those statements read.

The big multiply's layer is begun (`for.body132.i.i`'s staging edge and the
chunk loop's back edge, `stk_mul_u64.exit.i.i`'s three sites, `while.end.i.i`)
and its far end is here: `while.end176.i.i` spills the group count and tests the
residual, and `end176_run_ladder` carries that edge into the ladder's head as
the continuation `if.end198.i.i`'s own step leaves.  The spine between the two
ends is stated below: the loop's residue `for.cond.cleanup.i.i` and
`if.then148.i.i`, the staging `if.end151.i.i` with its two arms, the three
exponent routes (`if.then153.i.i`; `if.else164.i.i`, `if.then167.i.i`; and
`while.cond184.preheader.i.i`) with their rungs' tests and exits
(`while.body173.i.i` and `stk_mul_u64.exit583.i.i`, `while.body187.i.i` and
`stk_mul_u64.exit605.i.i`, `while.end190.i.i`, `if.end195.i.i`,
`while.end176.thread.i.i`), and the four nests' heads, residue joins, unroll
bounds and peeled exits.  The nests' unrolled bodies (`for.body.i527.i.i`,
`for.body.i.i544.i.i`, `for.body.i.i566.i.i`, `for.body.i.i588.i.i`,
`for.body.i.i611.i.i`), the `if.then140.i.i`/`for.body.lr.ph.i.i.i` ingest pair
with `for.body.lr.ph.i.i525.i.i`, `for.body.lr.ph.i.i542.i.i`,
`while.body.us.i.i520.i.i`, and the epilogue's blocks (`for.cond255.i.i`,
`for.end359.i.i`) are not stated here yet.  The peel loop
(`for.body.i.i`, entered from the peel and re-entered from its latch) is an
induction here (`peelRunAux`, `peelRun`); the main parse
loop's traversal (`for.body.outer.i.i` with its latch and dot back edges) and
the composition from the outer entry to the copy's entry are not stated yet.
There is no `sorry`, `admit` or `native_decide` below.
-/
import LeanLLVM.Refinement.JsonStage2NumFastFallback
import LeanLLVM.Refinement.JsonStage2NumFastTier3CopyUnroll
import LeanLLVM.Refinement.JsonStage2NumFastTier3Handoff
import LeanLLVM.Refinement.JsonStage2NumFastTier3Ladder

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.NumFastTier1
open LeanLLVM.Refinement.NumFastTier3

namespace NumFastToDouble

/-! ### The byte chains the parse reads and writes -/

/-- A one-byte load's round trip: the loaded word is the byte the memory holds. -/
theorem bytes1_toNat (v : BitVec 8) :
    bytesToNat (natToBytes v.toNat 1) = v.toNat := by
  rw [natToBytes_toNat, Nat.mod_eq_of_lt v.isLt]

/-- `%d = load i8, ptr %p`, at the one byte the read names. -/
theorem denoteCode_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {v : BitVec 8}
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 1 = some (natToBytes v.toNat 1)) (is : List Instr) :
    denoteCode calls (.load d (.int 8) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 8 v) :: env) s) := by
  have hq : (8 + 7) / 8 = 1 := by decide
  have hb : bytesToNat (natToBytes v.toNat 1) = v.toNat := bytes1_toNat v
  have hv' : loadValue s.mem (.int 8) a = some (.int 8 v) := by
    simp only [loadValue, hq, ite_eq_right (by decide : ¬ (8 = 0)), hv, hb,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [JsonS1MasksIR.evalInstr_load (s := stateAt env s)
      (hp := evalOperand_reg_of env s p (.ptr a) hp)
      (hv := by simpa only [stateAt] using hv')])]
  simp only [stateAt, State.bind]

/-- `%d = store i8 %v, ptr %p`: the byte is written at the named address. -/
theorem denoteCode_store8 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 8} {a : Nat}
    (hv : lookupName env v = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 8) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, stateAt, show (8 + 7) / 8 = 1 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 8 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) })
      (hv := evalOperand_reg_of env s v (.int 8 x) hv)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- The one-width sign extension's `Nat` reading. -/
theorem signExtend64_toNat (x : BitVec 64) : (x.signExtend 64).toNat = x.toNat :=
  NumFastTier3CopyLoop.t3_signExtend_self_toNat x

/-- `%d = add iW %a, <c>`, at any width. -/
theorem step_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x + c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (r := (x + c).toNat)
      (ha := BlockEval.evalOperand_reg_of env s a (.int w x) ha)
      (hb := BlockEval.evalOperand_lit_of _ w c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `add iW %a, <c>`. -/
theorem denoteCode_add_imm_w (calls : Calls) (env : Env) (s : State) (d a : String)
    (w : Nat) {x c : BitVec w} (ha : lookupName env a = some (.int w x))
    (is : List Instr) :
    denoteCode calls (.binop d .add w (.reg a) (.imm (.int w c)) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int w (x + c)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_add_imm_w calls env s d a w ha)]

/-! The lead clamps read four shapes the parse does not: a subtraction whose left
operand is the zero literal, a `select` of two floating literals at the sign's
bit, an unconditional lifetime call that binds nothing, and `getelementptr` and
`store` at a literal offset (`JsonScanLane`'s, joined to `inner_step` below).
They are stated here, ahead of the macro, because `inner_step` names its chain
steps when the macro is declared. -/

/-- `%d = sub i64 <c>, %b`: the clamp's negation of the lead. -/
theorem step_sub_lit (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64} (hb : lookupName env b = some (.int 64 y)) :
    evalInstr calls (stateAt env s) (.binop d .sub 64 (.imm (.int 64 c)) (.reg b)) =
      some (stateAt ((d, .int 64 (c - y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, stateAt, State.bind]
    using JsonS1MasksIR.evalInstr_binop (r := (c - y).toNat)
      (ha := BlockEval.evalOperand_lit_of _ 64 c)
      (hb := BlockEval.evalOperand_reg_of env s b (.int 64 y) hb)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- The chain step for `sub i64 <c>, %b`. -/
theorem denoteCode_sub_lit (calls : Calls) (env : Env) (s : State) (d b : String)
    {c y : BitVec 64} (hb : lookupName env b = some (.int 64 y)) (is : List Instr) :
    denoteCode calls (.binop d .sub 64 (.imm (.int 64 c)) (.reg b) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int 64 (c - y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_sub_lit calls env s d b hb)]

/-- `%d = select double %c, <x>, <y>`: the clamp's two floating literals. -/
theorem step_select_double_imm (calls : Calls) (env : Env) (s : State) (d c : String)
    {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb)) :
    evalInstr calls (stateAt env s)
        (.select d Ty.double (.reg c) (.imm (.float x)) (.imm (.float y))) =
      some (stateAt ((d, .float (if bb = 1 then x else y)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    rw [ite_eq_right (by decide)]
    rw [JsonS1MasksIR.evalInstr_select_false (s := stateAt env s)
      (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc) (ha := rfl) (hb := rfl)]
    rfl
  · subst h
    rw [ite_eq_left rfl]
    rw [JsonS1MasksIR.evalInstr_select_true (s := stateAt env s)
      (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc) (ha := rfl) (hb := rfl)]
    rfl

/-- The chain step for the clamp's `select` of two floating literals. -/
theorem denoteCode_select_double_imm (calls : Calls) (env : Env) (s : State)
    (d c : String) {bb : BitVec 1} {x y : BitVec 64}
    (hc : lookupName env c = some (.int 1 bb)) (is : List Instr) :
    denoteCode calls
        (.select d Ty.double (.reg c) (.imm (.float x)) (.imm (.float y)) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt ((d, .float (if bb = 1 then x else y)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_select_double_imm calls env s d c hc)]

/-- An unconditional lifetime marker at one word offset and the staging pointer:
it binds nothing and hands back the call's memory and cursor. -/
theorem step_callVoidLifetime (calls : Calls) (env : Env) (s : State) (callee p : String)
    {c : BitVec 64} {a : Nat} {r : CallOutcome}
    (hp : lookupName env p = some (.ptr a))
    (hc : calls callee [.int 64 c, .ptr a] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.callVoid callee [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, .reg p)]) =
      some (stateAt env { s with mem := r.mem, next := r.next }) := by
  have hargs : evalOperands (stateAt env s)
      [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, .reg p)] = some [.int 64 c, .ptr a] := by
    simp only [evalOperands, evalOperand, Const.toValue, stateAt, hp]
  simp only [evalInstr, hargs]
  rw [show calls callee [.int 64 c, .ptr a] (stateAt env s).mem (stateAt env s).next
    = some r from hc]
  rfl

/-- The chain step for the lifetime marker. -/
theorem denoteCode_callVoidLifetime (calls : Calls) (env : Env) (s : State)
    (callee p : String) {c : BitVec 64} {a : Nat} {r : CallOutcome}
    (hp : lookupName env p = some (.ptr a))
    (hc : calls callee [.int 64 c, .ptr a] s.mem s.next = some r) (is : List Instr) :
    denoteCode calls
        (.callVoid callee [(Ty.int 64, .imm (.int 64 c)), (Ty.ptr, .reg p)] :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_callVoidLifetime calls env s callee p hp hc)]

/-- The block's first-instruction shapes: `block_step`'s own steps, plus the
byte load and store and the two generic forms (`icmp` at any predicate, `mul`
by an immediate). -/

macro "inner_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8 _ _ _ _ _ ?_ ?_ _]
   | rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ _ _ _ ?_ _]
   | rw [JsonScanLane.denoteCode_and_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [JsonScanLane.denoteCode_or_reg_w _ _ _ _ _ _ ?_ ?_ _]
   | rw [JsonScanLane.denoteCode_select_bit_reg_imm_w _ _ _ _ _ _ _ ?_ ?_ _]
   | rw [NumFastTier3.denoteCode_mul_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_sub_lit _ _ _ _ _ ?_ _]
   | rw [JsonScanLane.denoteCode_gep8_lit_w _ _ _ _ _ ?_ ?_ _]
   | rw [JsonScanLane.denoteCode_store32 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_select_double_imm _ _ _ _ _ ?_ _]
   | rw [denoteCode_callVoidLifetime _ _ _ _ _ ?_ ?_ _]))

/-- A block's remaining run after its leading `phi`s. -/
macro "inner_eval" : tactic => `(tactic| (repeat inner_step; block_close))

/-- A leading `phi` run at a named state: the block's `phi`s, then the rest, are
one step of `denoteCode` and land their bindings together.  The run's values are
supplied by the caller, so a member's selected value is fixed by the statement
rather than inferred from a sibling. -/
theorem denoteCode_phiRun_at {calls : Calls} {env : Env} {s : State} {p : String}
    {specs : List PhiSpec} {vs : List (String × Value)} {rest : List Instr}
    (hpre : s.pre = some p) (hsel : PhiSelects (stateAt env s) p specs vs)
    (hst : startsWithPhi rest = false) :
    denoteCode calls (specs.map PhiSpec.instr ++ rest) (stateAt env s) =
      denoteCode calls rest (stateAt (runCells vs env) s) := by
  rw [denoteCode_phiRun (calls := calls) (s := stateAt env s) (p := p) hpre hsel hst,
    stateAt_bindAll_runCells]

/-! ### The `T`/`F` parse: `for.body.outer.i.i`

The outer parse's head loads the lexeme's byte at the cursor, adds `'0'`'s
negative, and tests `%55 <u 10`.  Its six `phi`s carry the cursor and the five
counters; the incoming cells are the entry block's on the first edge and
`for.inc.i.i`'s afterwards. -/

/-- The parse head's six `phi`s, as `PhiSpec`s. -/
def outerSpecs : List PhiSpec :=
  [{ dst := "%i.1725.ph.i.i", ty := Ty.int 64,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%i.1725.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.reg "%inc57.i344.i"))] },
   { dst := "%T.0723.ph.i.i", ty := Ty.int 64,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%T.0723.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.reg "%T.0723.i.i"))] },
   { dst := "%F.0722.ph.i.i", ty := Ty.int 64,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%F.0722.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.reg "%F.0722.i.i"))] },
   { dst := "%lead.0721.ph.i.i", ty := Ty.int 64,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%lead.0721.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.reg "%lead.0721.i.i"))] },
   { dst := "%in_frac.0718.ph.i.i", ty := Ty.int 32,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%in_frac.0718.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000001#32)))] },
   { dst := "%seen.0717.ph.i.i", ty := Ty.int 32,
     incoming := [("for.body.outer.i.outer.i", (Operand.reg "%seen.0717.ph.i.ph.i")),
                  ("if.else46.i.thread.i", (Operand.imm (Const.int 32 0x00000000#32)))] }]

/-- The values the head's `phi`s select on the entry edge. -/
def outerValues (i T F lead : BitVec 64) (inFrac seen : BitVec 32) :
    List (String × Value) :=
  [("%i.1725.ph.i.i", .int 64 i), ("%T.0723.ph.i.i", .int 64 T),
   ("%F.0722.ph.i.i", .int 64 F), ("%lead.0721.ph.i.i", .int 64 lead),
   ("%in_frac.0718.ph.i.i", .int 32 inFrac), ("%seen.0717.ph.i.i", .int 32 seen)]

/-- The head's instruction list after the `phi` run. -/
def outerRest : List Instr :=
  [Instr.icmp "%tobool.not.i.i" (IPred.ne) 32 (Operand.reg "%in_frac.0718.ph.i.i")
     (Operand.imm (Const.int 32 0x00000000#32)),
   Instr.zext "%inc18.i.i" 1 64 (Operand.reg "%tobool.not.i.i"),
   Instr.gep "%arrayidx5.i.peel.i" (Ty.int 8) (Operand.reg "%p")
     (Operand.reg "%i.1725.ph.i.i"),
   Instr.load "%54" (Ty.int 8) (Operand.reg "%arrayidx5.i.peel.i"),
   Instr.binop "%55" (BinOp.add) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0xd0#8)),
   Instr.icmp "%or.cond.i.peel.i" (IPred.ult) 8 (Operand.reg "%55")
     (Operand.imm (Const.int 8 0x0a#8))]

/-- `for.body.outer.i.i`, from its pin. -/
def outerInstrs : List Instr :=
  outerSpecs.map PhiSpec.instr ++ outerRest

theorem outer_find :
    numFastBody.findBlock "for.body.outer.i.i" =
      some ⟨"for.body.outer.i.i", outerInstrs,
        Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩ := by
  simp only [outerInstrs, outerSpecs, outerRest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_for_body_outer_i_i

/-- The environment the parse head leaves: the six selected cells, the
fraction flag's widen, the byte and its shifted value, and the digit test. -/
def outerEnv (env : Env) (i T F lead : BitVec 64) (inFrac seen : BitVec 32)
    (a : Nat) (b : BitVec 8) : Env :=
  ("%or.cond.i.peel.i", .int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) ::
  ("%55", .int 8 (b + 0xd0#8)) ::
  ("%54", .int 8 b) ::
  ("%arrayidx5.i.peel.i", .ptr a) ::
  ("%inc18.i.i", .int 64 (BitVec.ofNat 64 (evalICmp .ne inFrac 0#32).toNat)) ::
  ("%tobool.not.i.i", .int 1 (evalICmp .ne inFrac 0#32)) ::
  ("%seen.0717.ph.i.i", .int 32 seen) ::
  ("%in_frac.0718.ph.i.i", .int 32 inFrac) ::
  ("%lead.0721.ph.i.i", .int 64 lead) ::
  ("%F.0722.ph.i.i", .int 64 F) ::
  ("%T.0723.ph.i.i", .int 64 T) ::
  ("%i.1725.ph.i.i", .int 64 i) :: env

/-- The parse head's chain at its pin: the six `phi`s at
`for.body.outer.i.outer.i`'s edge, the flag's widen, the byte at the cursor, and
the digit test. -/
theorem outer_denote {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {inFrac seen : BitVec 32} {b : BitVec 8} {a : Nat}
    (hpre : s.pre = some "for.body.outer.i.outer.i")
    (hi : lookupName env "%i.1725.ph.i.ph.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.ph.i.ph.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.ph.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.ph.i" = some (.int 64 lead))
    (hin : lookupName env "%in_frac.0718.ph.i.ph.i" = some (.int 32 inFrac))
    (hseen : lookupName env "%seen.0717.ph.i.ph.i" = some (.int 32 seen))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode calls outerInstrs (stateAt env s) =
      some (stateAt (outerEnv env i T F lead inFrac seen (a + i.toNat) b) s) := by
  have hsel : PhiSelects (stateAt env s) "for.body.outer.i.outer.i"
      outerSpecs (outerValues i T F lead inFrac seen) := by
    simp only [outerSpecs, outerValues]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.ph.i.ph.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.0723.ph.i.ph.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.0722.ph.i.ph.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.ph.i.ph.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%in_frac.0718.ph.i.ph.i" (.int 32 inFrac) hin
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%seen.0717.ph.i.ph.i" (.int 32 seen) hseen
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.body.outer.i.outer.i") (specs := outerSpecs)
    (vs := outerValues i T F lead inFrac seen) (rest := outerRest)
    hpre hsel (by decide)
  unfold outerInstrs
  rw [h]
  unfold outerRest
  simp only [outerEnv]
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close
  all_goals (first
    | (simpa only [signExtend64_toNat] using hb)
    | (simpa only [signExtend64_toNat] using hi63)
    | (simp only [outerValues, runCells, denoteRun, State.bindAll, signExtend64_toNat]))

/-- The parse head's step onto its digit edge: the block computes
`%55 <u 10` true and jumps to `if.then13.i.peel.i`. -/
theorem outer_step_digit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {inFrac seen : BitVec 32} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.outer.i.i")
    (hpre : s.pre = some "for.body.outer.i.outer.i")
    (hi : lookupName env "%i.1725.ph.i.ph.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.ph.i.ph.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.ph.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.ph.i" = some (.int 64 lead))
    (hin : lookupName env "%in_frac.0718.ph.i.ph.i" = some (.int 32 inFrac))
    (hseen : lookupName env "%seen.0717.ph.i.ph.i" = some (.int 32 seen))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (outerEnv env i T F lead inFrac seen (a + i.toNat) b)
        { s with pc := "if.then13.i.peel.i", pre := some "for.body.outer.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (outerEnv env i T F lead inFrac seen (a + i.toNat) b) s)
    (b := ⟨"for.body.outer.i.i", outerInstrs,
      Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using outer_find
  · simpa only [stateAt] using outer_denote hpre hi hT hF hlead hin hseen hp hi63 hb
  · rw [numFast_execTerm_condbr_one (s := stateAt (outerEnv env i T F lead inFrac
        seen (a + i.toNat) b) s) "%or.cond.i.peel.i" "if.then13.i.peel.i" "if.else46.i.i"
        (lookupName_cons_self "%or.cond.i.peel.i"
          (Value.int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) _) hbit]
    simp only [stateAt, hpc]

/-- The parse head's step onto its non-digit edge: `%55 <u 10` is false and the
block jumps to `if.else46.i.i`. -/
theorem outer_step_nondigit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {inFrac seen : BitVec 32} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.outer.i.i")
    (hpre : s.pre = some "for.body.outer.i.outer.i")
    (hi : lookupName env "%i.1725.ph.i.ph.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.ph.i.ph.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.ph.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.ph.i" = some (.int 64 lead))
    (hin : lookupName env "%in_frac.0718.ph.i.ph.i" = some (.int 32 inFrac))
    (hseen : lookupName env "%seen.0717.ph.i.ph.i" = some (.int 32 seen))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (outerEnv env i T F lead inFrac seen (a + i.toNat) b)
        { s with pc := "if.else46.i.i", pre := some "for.body.outer.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (outerEnv env i T F lead inFrac seen (a + i.toNat) b) s)
    (b := ⟨"for.body.outer.i.i", outerInstrs,
      Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using outer_find
  · simpa only [stateAt] using outer_denote hpre hi hT hF hlead hin hseen hp hi63 hb
  · rw [numFast_execTerm_condbr_zero (s := stateAt (outerEnv env i T F lead inFrac
        seen (a + i.toNat) b) s) "%or.cond.i.peel.i" "if.then13.i.peel.i" "if.else46.i.i"
        (lookupName_cons_self "%or.cond.i.peel.i"
          (Value.int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) _) hbit]
    simp only [stateAt, hpc]

/-! ### The peel's guard: `if.then13.i.peel.i`

The outer parse's digit edge.  The two counters are the incoming `phi`s' cells
and the byte is the head's `%55`; the block's own guards are the seen flag's zero
test, the byte's zero test, and their conjunction, which chooses the inner loop's
peel entry or the outer loop's exit. -/

def peelInstrs : List Instr :=
  [Instr.binop "%inc16.i.peel.i" (BinOp.add) 64 (Operand.reg "%T.0723.ph.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.binop "%spec.select.i.peel.i" (BinOp.add) 64 (Operand.reg "%F.0722.ph.i.i")
     (Operand.reg "%inc18.i.i"),
   Instr.icmp "%tobool20.not.i.peel.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i")
     (Operand.imm (Const.int 32 0x00000000#32)),
   Instr.icmp "%cmp23.i.peel.i" (IPred.eq) 8 (Operand.reg "%55")
     (Operand.imm (Const.int 8 0x00#8)),
   Instr.binop "%or.cond510.i.peel.i" (BinOp.and) 1
     (Operand.reg "%tobool20.not.i.peel.i") (Operand.reg "%cmp23.i.peel.i")]

theorem peel_find :
    numFastBody.findBlock "if.then13.i.peel.i" =
      some ⟨"if.then13.i.peel.i", peelInstrs,
        Term.condbr (Operand.reg "%or.cond510.i.peel.i") "for.inc.thread.i.peel.i"
          "if.end28.i.i.loopexit609"⟩ := by
  simpa only [peelInstrs] using numFast_findBlock_if_then13_i_peel_i

/-- The environment the peel's guard leaves: the two counters, the flag's byte
tests and their conjunction. -/
def peelEnv (env : Env) (T F inc18 : BitVec 64) (seen : BitVec 32) (b55 : BitVec 8) : Env :=
  ("%or.cond510.i.peel.i",
    .int 1 (evalICmp .eq seen 0x00000000#32 &&& evalICmp .eq b55 0x00#8)) ::
  ("%cmp23.i.peel.i", .int 1 (evalICmp .eq b55 0x00#8)) ::
  ("%tobool20.not.i.peel.i", .int 1 (evalICmp .eq seen 0x00000000#32)) ::
  ("%spec.select.i.peel.i", .int 64 (F + inc18)) ::
  ("%inc16.i.peel.i", .int 64 (T + 0x0000000000000001#64)) :: env

/-- The peel guard's chain at its pin. -/
theorem peel_denote {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {seen : BitVec 32} {b55 : BitVec 8}
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (h55 : lookupName env "%55" = some (.int 8 b55)) :
    denoteCode calls peelInstrs (stateAt env s) =
      some (stateAt (peelEnv env T F inc18 seen b55) s) := by
  unfold peelInstrs
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The peel guard's step onto the inner loop: the conjunction holds. -/
theorem peel_step_taken {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {seen : BitVec 32} {b55 : BitVec 8}
    (hpc : s.pc = "if.then13.i.peel.i")
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (h55 : lookupName env "%55" = some (.int 8 b55))
    (hbit : evalICmp .eq seen 0x00000000#32 &&& evalICmp .eq b55 0x00#8
      = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (peelEnv env T F inc18 seen b55)
        { s with pc := "for.inc.thread.i.peel.i", pre := some "if.then13.i.peel.i" }) := by
  refine numFast_step_at (s' := stateAt (peelEnv env T F inc18 seen b55) s)
    (b := ⟨"if.then13.i.peel.i", peelInstrs,
      Term.condbr (Operand.reg "%or.cond510.i.peel.i") "for.inc.thread.i.peel.i"
        "if.end28.i.i.loopexit609"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using peel_find
  · exact peel_denote hT hF hinc hseen h55
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (peelEnv env T F inc18 seen b55) s) "%or.cond510.i.peel.i"
      "for.inc.thread.i.peel.i" "if.end28.i.i.loopexit609"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The peel guard's step onto the outer loop's exit: the conjunction fails. -/
theorem peel_step_refused {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {seen : BitVec 32} {b55 : BitVec 8}
    (hpc : s.pc = "if.then13.i.peel.i")
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (h55 : lookupName env "%55" = some (.int 8 b55))
    (hbit : evalICmp .eq seen 0x00000000#32 &&& evalICmp .eq b55 0x00#8
      = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (peelEnv env T F inc18 seen b55)
        { s with pc := "if.end28.i.i.loopexit609", pre := some "if.then13.i.peel.i" }) := by
  refine numFast_step_at (s' := stateAt (peelEnv env T F inc18 seen b55) s)
    (b := ⟨"if.then13.i.peel.i", peelInstrs,
      Term.condbr (Operand.reg "%or.cond510.i.peel.i") "for.inc.thread.i.peel.i"
        "if.end28.i.i.loopexit609"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using peel_find
  · exact peel_denote hT hF hinc hseen h55
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (peelEnv env T F inc18 seen b55) s) "%or.cond510.i.peel.i"
      "for.inc.thread.i.peel.i" "if.end28.i.i.loopexit609"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The peel's exit: `if.end28.i.i.loopexit609`

The peeled group's exit carries the sticky flag's byte into `if.end28.i.i`: the
peel test is the condition, so the counted digit's byte in the sticky slot is
either the incoming flag or one. -/

def peelExitInstrs : List Instr :=
  [Instr.select "%58" (Ty.int 32) (Operand.reg "%cmp23.i.peel.i")
     (Operand.reg "%sticky.0716.ph.i.ph.i") (Operand.imm (Const.int 32 0x00000001#32))]

theorem peelExit_find :
    numFastBody.findBlock "if.end28.i.i.loopexit609" =
      some ⟨"if.end28.i.i.loopexit609", peelExitInstrs, Term.br "if.end28.i.i"⟩ := by
  simpa only [peelExitInstrs] using numFast_findBlock_if_end28_i_i_loopexit609

/-- The environment the peel's exit leaves: the sticky byte the select chose. -/
def peelExitEnv (env : Env) (sticky : BitVec 32) (b55 : BitVec 8) : Env :=
  ("%58", .int 32
    (if evalICmp .eq b55 0x00#8 = 1 then sticky else 0x00000001#32)) :: env

/-- The peel exit's chain at its pin. -/
theorem peelExit_denote {calls : Calls} {env : Env} {s : State}
    {sticky : BitVec 32} {b55 : BitVec 8}
    (hcmp : lookupName env "%cmp23.i.peel.i" = some (.int 1 (evalICmp .eq b55 0x00#8)))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky)) :
    denoteCode calls peelExitInstrs (stateAt env s) =
      some (stateAt (peelExitEnv env sticky b55) s) := by
  unfold peelExitInstrs
  inner_step
  block_close

/-- The peel exit's step into `if.end28.i.i`. -/
theorem peelExit_step {calls : Calls} {env : Env} {s : State}
    {sticky : BitVec 32} {b55 : BitVec 8}
    (hpc : s.pc = "if.end28.i.i.loopexit609")
    (hcmp : lookupName env "%cmp23.i.peel.i" = some (.int 1 (evalICmp .eq b55 0x00#8)))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (peelExitEnv env sticky b55)
        { s with pc := "if.end28.i.i", pre := some "if.end28.i.i.loopexit609" }) := by
  refine numFast_step_at (s' := stateAt (peelExitEnv env sticky b55) s)
    (b := ⟨"if.end28.i.i.loopexit609", peelExitInstrs, Term.br "if.end28.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using peelExit_find
  · exact peelExit_denote hcmp hsticky
  · simp only [execTerm, stateAt, hpc]

/-! ### The inner loop's peel entry: `for.inc.thread.i.peel.i`

The peeled group's counter step and its end-of-lexeme test: the counter is the
head's cursor plus one, and the test compares it with `%n`. -/

def incPeelInstrs : List Instr :=
  [Instr.binop "%inc57798.i.peel.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond.not799.i.peel.i" (IPred.eq) 64
     (Operand.reg "%inc57798.i.peel.i") (Operand.reg "%n")]

theorem incPeel_find :
    numFastBody.findBlock "for.inc.thread.i.peel.i" =
      some ⟨"for.inc.thread.i.peel.i", incPeelInstrs,
        Term.condbr (Operand.reg "%exitcond.not799.i.peel.i") "if.then59.i.i"
          "for.body.i.i"⟩ := by
  simpa only [incPeelInstrs] using numFast_findBlock_for_inc_thread_i_peel_i

/-- The environment the peeled entry leaves: its counter and its test. -/
def incPeelEnv (env : Env) (i n : BitVec 64) : Env :=
  ("%exitcond.not799.i.peel.i", .int 1 (evalICmp .eq (i + 0x0000000000000001#64) n)) ::
  ("%inc57798.i.peel.i", .int 64 (i + 0x0000000000000001#64)) :: env

/-- The peeled entry's chain at its pin. -/
theorem incPeel_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls incPeelInstrs (stateAt env s) =
      some (stateAt (incPeelEnv env i n) s) := by
  unfold incPeelInstrs
  inner_step
  inner_step
  block_close

/-- The peeled entry's step to the refusal: the counter reaches `%n`. -/
theorem incPeel_step_exit {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "for.inc.thread.i.peel.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (incPeelEnv env i n)
        { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.peel.i" }) := by
  refine numFast_step_at (s' := stateAt (incPeelEnv env i n) s)
    (b := ⟨"for.inc.thread.i.peel.i", incPeelInstrs,
      Term.condbr (Operand.reg "%exitcond.not799.i.peel.i") "if.then59.i.i"
        "for.body.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using incPeel_find
  · exact incPeel_denote hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (incPeelEnv env i n) s)
      "%exitcond.not799.i.peel.i" "if.then59.i.i" "for.body.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The peeled entry's step into the inner loop: the counter is below `%n`. -/
theorem incPeel_step_body {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "for.inc.thread.i.peel.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (incPeelEnv env i n)
        { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.peel.i" }) := by
  refine numFast_step_at (s' := stateAt (incPeelEnv env i n) s)
    (b := ⟨"for.inc.thread.i.peel.i", incPeelInstrs,
      Term.condbr (Operand.reg "%exitcond.not799.i.peel.i") "if.then59.i.i"
        "for.body.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using incPeel_find
  · exact incPeel_denote hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (incPeelEnv env i n) s)
      "%exitcond.not799.i.peel.i" "if.then59.i.i" "for.body.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The inner loop's digit guard: `if.then13.i.i`

The loop's digit edge tests the byte the body read: the two counters are updated
in place, and the byte's zero test chooses the next iteration or the loop's
residue exit. -/

def thenInstrs : List Instr :=
  [Instr.binop "%inc16.i.i" (BinOp.add) 64 (Operand.reg "%T.0723.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.binop "%spec.select.i.i" (BinOp.add) 64 (Operand.reg "%F.0722.i.i")
     (Operand.reg "%inc18.i.i"),
   Instr.icmp "%cmp23.i.i" (IPred.eq) 8 (Operand.reg "%57")
     (Operand.imm (Const.int 8 0x00#8))]

theorem then_find :
    numFastBody.findBlock "if.then13.i.i" =
      some ⟨"if.then13.i.i", thenInstrs,
        Term.condbr (Operand.reg "%cmp23.i.i") "for.inc.thread.i.i" "if.end28.i.i"⟩ := by
  simpa only [thenInstrs] using numFast_findBlock_if_then13_i_i

/-- The environment the loop's digit edge leaves: its two counters and the byte's
zero test. -/
def thenEnv (env : Env) (T F inc18 : BitVec 64) (b57 : BitVec 8) : Env :=
  ("%cmp23.i.i", .int 1 (evalICmp .eq b57 0x00#8)) ::
  ("%spec.select.i.i", .int 64 (F + inc18)) ::
  ("%inc16.i.i", .int 64 (T + 0x0000000000000001#64)) :: env

/-- The loop's digit edge's chain at its pin. -/
theorem then_denote {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {b57 : BitVec 8}
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (h57 : lookupName env "%57" = some (.int 8 b57)) :
    denoteCode calls thenInstrs (stateAt env s) =
      some (stateAt (thenEnv env T F inc18 b57) s) := by
  unfold thenInstrs
  inner_step
  inner_step
  inner_step
  block_close

/-- The loop's digit edge's step to the next iteration: the byte is not zero. -/
theorem then_step_continue {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {b57 : BitVec 8}
    (hpc : s.pc = "if.then13.i.i")
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (h57 : lookupName env "%57" = some (.int 8 b57))
    (hbit : evalICmp .eq b57 0x00#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (thenEnv env T F inc18 b57)
        { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) := by
  refine numFast_step_at (s' := stateAt (thenEnv env T F inc18 b57) s)
    (b := ⟨"if.then13.i.i", thenInstrs,
      Term.condbr (Operand.reg "%cmp23.i.i") "for.inc.thread.i.i" "if.end28.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then_find
  · exact then_denote hT hF hinc h57
  · rw [numFast_execTerm_condbr_one (s := stateAt (thenEnv env T F inc18 b57) s)
      "%cmp23.i.i" "for.inc.thread.i.i" "if.end28.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The loop's digit edge's step to the residue exit: the byte is zero. -/
theorem then_step_exit {calls : Calls} {env : Env} {s : State}
    {T F inc18 : BitVec 64} {b57 : BitVec 8}
    (hpc : s.pc = "if.then13.i.i")
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hinc : lookupName env "%inc18.i.i" = some (.int 64 inc18))
    (h57 : lookupName env "%57" = some (.int 8 b57))
    (hbit : evalICmp .eq b57 0x00#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (thenEnv env T F inc18 b57)
        { s with pc := "if.end28.i.i", pre := some "if.then13.i.i" }) := by
  refine numFast_step_at (s' := stateAt (thenEnv env T F inc18 b57) s)
    (b := ⟨"if.then13.i.i", thenInstrs,
      Term.condbr (Operand.reg "%cmp23.i.i") "for.inc.thread.i.i" "if.end28.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then_find
  · exact then_denote hT hF hinc h57
  · rw [numFast_execTerm_condbr_zero (s := stateAt (thenEnv env T F inc18 b57) s)
      "%cmp23.i.i" "for.inc.thread.i.i" "if.end28.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The inner loop's latch: `for.inc.thread.i.i`

The loop's back edge: the cursor's step and its end-of-lexeme test, which chooses
the refusal or the body again. -/

def incThreadInstrs : List Instr :=
  [Instr.binop "%inc57798.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond.not799.i.i" (IPred.eq) 64 (Operand.reg "%inc57798.i.i")
     (Operand.reg "%n")]

theorem incThread_find :
    numFastBody.findBlock "for.inc.thread.i.i" =
      some ⟨"for.inc.thread.i.i", incThreadInstrs,
        Term.condbr (Operand.reg "%exitcond.not799.i.i") "if.then59.i.i"
          "for.body.i.i"⟩ := by
  simpa only [incThreadInstrs] using numFast_findBlock_for_inc_thread_i_i

/-- The latch's environment: the cursor's step and its test. -/
def incThreadEnv (env : Env) (i n : BitVec 64) : Env :=
  ("%exitcond.not799.i.i", .int 1 (evalICmp .eq (i + 0x0000000000000001#64) n)) ::
  ("%inc57798.i.i", .int 64 (i + 0x0000000000000001#64)) :: env

/-- The latch's chain at its pin. -/
theorem incThread_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls incThreadInstrs (stateAt env s) =
      some (stateAt (incThreadEnv env i n) s) := by
  unfold incThreadInstrs
  inner_step
  inner_step
  block_close

/-- The latch's step to the refusal. -/
theorem incThread_step_exit {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "for.inc.thread.i.i")
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (incThreadEnv env i n)
        { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" }) := by
  refine numFast_step_at (s' := stateAt (incThreadEnv env i n) s)
    (b := ⟨"for.inc.thread.i.i", incThreadInstrs,
      Term.condbr (Operand.reg "%exitcond.not799.i.i") "if.then59.i.i"
        "for.body.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using incThread_find
  · exact incThread_denote hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (incThreadEnv env i n) s)
      "%exitcond.not799.i.i" "if.then59.i.i" "for.body.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step into the body. -/
theorem incThread_step_body {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "for.inc.thread.i.i")
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (incThreadEnv env i n)
        { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.i" }) := by
  refine numFast_step_at (s' := stateAt (incThreadEnv env i n) s)
    (b := ⟨"for.inc.thread.i.i", incThreadInstrs,
      Term.condbr (Operand.reg "%exitcond.not799.i.i") "if.then59.i.i"
        "for.body.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using incThread_find
  · exact incThread_denote hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (incThreadEnv env i n) s)
      "%exitcond.not799.i.i" "if.then59.i.i" "for.body.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The outer loop's non-digit edge: `if.else46.i.i`

The head's refusal edge tests the byte against the decimal point; the point takes
the loop's latch and anything else leaves the parse for the exponent. -/

def dotInstrs : List Instr :=
  [Instr.icmp "%cmp48.i.i" (IPred.eq) 8 (Operand.reg "%54") (Operand.imm (Const.int 8 0x2e#8))]

theorem dot_find :
    numFastBody.findBlock "if.else46.i.i" =
      some ⟨"if.else46.i.i", dotInstrs,
        Term.condbr (Operand.reg "%cmp48.i.i") "for.inc.i.i" "for.end.i.i"⟩ := by
  simpa only [dotInstrs] using numFast_findBlock_if_else46_i_i

/-- The non-digit edge's environment: the point's test. -/
def dotEnv (env : Env) (b54 : BitVec 8) : Env :=
  ("%cmp48.i.i", .int 1 (evalICmp .eq b54 0x2e#8)) :: env

/-- The non-digit edge's chain at its pin. -/
theorem dot_denote {calls : Calls} {env : Env} {s : State} {b54 : BitVec 8}
    (h54 : lookupName env "%54" = some (.int 8 b54)) :
    denoteCode calls dotInstrs (stateAt env s) = some (stateAt (dotEnv env b54) s) := by
  unfold dotInstrs
  inner_step
  block_close

/-- The non-digit edge's step into the latch: the byte is the point. -/
theorem dot_step_point {calls : Calls} {env : Env} {s : State} {b54 : BitVec 8}
    (hpc : s.pc = "if.else46.i.i")
    (h54 : lookupName env "%54" = some (.int 8 b54))
    (hbit : evalICmp .eq b54 0x2e#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (dotEnv env b54)
        { s with pc := "for.inc.i.i", pre := some "if.else46.i.i" }) := by
  refine numFast_step_at (s' := stateAt (dotEnv env b54) s)
    (b := ⟨"if.else46.i.i", dotInstrs,
      Term.condbr (Operand.reg "%cmp48.i.i") "for.inc.i.i" "for.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using dot_find
  · exact dot_denote h54
  · rw [numFast_execTerm_condbr_one (s := stateAt (dotEnv env b54) s) "%cmp48.i.i"
      "for.inc.i.i" "for.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The non-digit edge's step out of the parse: the byte is not the point. -/
theorem dot_step_exit {calls : Calls} {env : Env} {s : State} {b54 : BitVec 8}
    (hpc : s.pc = "if.else46.i.i")
    (h54 : lookupName env "%54" = some (.int 8 b54))
    (hbit : evalICmp .eq b54 0x2e#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (dotEnv env b54)
        { s with pc := "for.end.i.i", pre := some "if.else46.i.i" }) := by
  refine numFast_step_at (s' := stateAt (dotEnv env b54) s)
    (b := ⟨"if.else46.i.i", dotInstrs,
      Term.condbr (Operand.reg "%cmp48.i.i") "for.inc.i.i" "for.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using dot_find
  · exact dot_denote h54
  · rw [numFast_execTerm_condbr_zero (s := stateAt (dotEnv env b54) s) "%cmp48.i.i"
      "for.inc.i.i" "for.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The parse's end: `for.end.i.i`

The parse's exit tests the seen flag: a seen flag clears the parse for the
exponent, and an unseen one refuses at `if.then59`. -/

def parseEndInstrs : List Instr :=
  [Instr.icmp "%tobool58.not.i.i" (IPred.eq) 32 (Operand.reg "%seen.0717.ph.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem parseEnd_find :
    numFastBody.findBlock "for.end.i.i" =
      some ⟨"for.end.i.i", parseEndInstrs,
        Term.condbr (Operand.reg "%tobool58.not.i.i") "if.then59.i.i" "if.then64.i.i"⟩ := by
  simpa only [parseEndInstrs] using numFast_findBlock_for_end_i_i

/-- The parse's exit environment: the seen flag's zero test. -/
def parseEndEnv (env : Env) (seen : BitVec 32) : Env :=
  ("%tobool58.not.i.i", .int 1 (evalICmp .eq seen 0x00000000#32)) :: env

/-- The parse's exit chain at its pin. -/
theorem parseEnd_denote {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen)) :
    denoteCode calls parseEndInstrs (stateAt env s) =
      some (stateAt (parseEndEnv env seen) s) := by
  unfold parseEndInstrs
  inner_step
  block_close

/-- The parse's exit's step to the refusal: nothing was seen. -/
theorem parseEnd_step_refuse {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hpc : s.pc = "for.end.i.i")
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (hbit : evalICmp .eq seen 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (parseEndEnv env seen)
        { s with pc := "if.then59.i.i", pre := some "for.end.i.i" }) := by
  refine numFast_step_at (s' := stateAt (parseEndEnv env seen) s)
    (b := ⟨"for.end.i.i", parseEndInstrs,
      Term.condbr (Operand.reg "%tobool58.not.i.i") "if.then59.i.i" "if.then64.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using parseEnd_find
  · exact parseEnd_denote hseen
  · rw [numFast_execTerm_condbr_one (s := stateAt (parseEndEnv env seen) s)
      "%tobool58.not.i.i" "if.then59.i.i" "if.then64.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The parse's exit's step to the exponent: the flag was seen. -/
theorem parseEnd_step_exponent {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hpc : s.pc = "for.end.i.i")
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (hbit : evalICmp .eq seen 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (parseEndEnv env seen)
        { s with pc := "if.then64.i.i", pre := some "for.end.i.i" }) := by
  refine numFast_step_at (s' := stateAt (parseEndEnv env seen) s)
    (b := ⟨"for.end.i.i", parseEndInstrs,
      Term.condbr (Operand.reg "%tobool58.not.i.i") "if.then59.i.i" "if.then64.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using parseEnd_find
  · exact parseEnd_denote hseen
  · rw [numFast_execTerm_condbr_zero (s := stateAt (parseEndEnv env seen) s)
      "%tobool58.not.i.i" "if.then59.i.i" "if.then64.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The inner loop's body: `for.body.i.i`

The loop's head: four carried `phi`s (the cursor, the two counters and the lead's
running value), the lead's step, the byte at the cursor and its digit test.  The
`phi`s take the peel's cells on the peeled entry and the latch's on the back
edge; the one statement serves both edges by its selected values. -/

/-- The loop head's four `phi`s. -/
def bodySpecs : List PhiSpec :=
  [{ dst := "%i.1725.i.i", ty := Ty.int 64,
     incoming := [("for.inc.thread.i.i", (Operand.reg "%inc57798.i.i")),
                  ("for.inc.thread.i.peel.i", (Operand.reg "%inc57798.i.peel.i"))] },
   { dst := "%T.0723.i.i", ty := Ty.int 64,
     incoming := [("for.inc.thread.i.i", (Operand.reg "%inc16.i.i")),
                  ("for.inc.thread.i.peel.i", (Operand.reg "%inc16.i.peel.i"))] },
   { dst := "%F.0722.i.i", ty := Ty.int 64,
     incoming := [("for.inc.thread.i.i", (Operand.reg "%spec.select.i.i")),
                  ("for.inc.thread.i.peel.i", (Operand.reg "%spec.select.i.peel.i"))] },
   { dst := "%lead.0721.i.in.i", ty := Ty.int 64,
     incoming := [("for.inc.thread.i.i", (Operand.reg "%lead.0721.i.i")),
                  ("for.inc.thread.i.peel.i", (Operand.reg "%lead.0721.ph.i.i"))] }]

/-- The values the head's `phi`s select on the peeled entry. -/
def bodyValuesPeel (i T F lead : BitVec 64) : List (String × Value) :=
  [("%i.1725.i.i", .int 64 i), ("%T.0723.i.i", .int 64 T),
   ("%F.0722.i.i", .int 64 F), ("%lead.0721.i.in.i", .int 64 lead)]

/-- The values the head's `phi`s select on the latch's back edge. -/
def bodyValuesBack (i T F lead : BitVec 64) : List (String × Value) :=
  bodyValuesPeel i T F lead

/-- The head's instruction list after the `phi` run. -/
def bodyRest : List Instr :=
  [Instr.binop "%lead.0721.i.i" (BinOp.add) 64 (Operand.reg "%lead.0721.i.in.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.gep "%arrayidx5.i.i" (Ty.int 8) (Operand.reg "%p")
     (Operand.reg "%i.1725.i.i"),
   Instr.load "%56" (Ty.int 8) (Operand.reg "%arrayidx5.i.i"),
   Instr.binop "%57" (BinOp.add) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0xd0#8)),
   Instr.icmp "%or.cond.i.i" (IPred.ult) 8 (Operand.reg "%57")
     (Operand.imm (Const.int 8 0x0a#8))]

/-- `for.body.i.i`, from its pin. -/
def bodyInstrs : List Instr := bodySpecs.map PhiSpec.instr ++ bodyRest

theorem body_find :
    numFastBody.findBlock "for.body.i.i" =
      some ⟨"for.body.i.i", bodyInstrs,
        Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩ := by
  simp only [bodyInstrs, bodySpecs, bodyRest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_for_body_i_i

/-- The environment the head leaves: the four selected cells, the lead's step, the
byte at the cursor and the digit test. -/
def bodyEnv (env : Env) (i T F lead : BitVec 64) (a : Nat) (b : BitVec 8) : Env :=
  ("%or.cond.i.i", .int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) ::
  ("%57", .int 8 (b + 0xd0#8)) ::
  ("%56", .int 8 b) ::
  ("%arrayidx5.i.i", .ptr a) ::
  ("%lead.0721.i.i", .int 64 (lead + 0x0000000000000001#64)) ::
  ("%lead.0721.i.in.i", .int 64 lead) ::
  ("%F.0722.i.i", .int 64 F) ::
  ("%T.0723.i.i", .int 64 T) ::
  ("%i.1725.i.i", .int 64 i) :: env

/-- The head's chain at the peeled entry. -/
theorem body_denote_peel {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpre : s.pre = some "for.inc.thread.i.peel.i")
    (hi : lookupName env "%inc57798.i.peel.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode calls bodyInstrs (stateAt env s) =
      some (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s) := by
  have hsel : PhiSelects (stateAt env s) "for.inc.thread.i.peel.i"
      bodySpecs (bodyValuesPeel i T F lead) := by
    simp only [bodySpecs, bodyValuesPeel]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc57798.i.peel.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.peel.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.peel.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.ph.i.i" (.int 64 lead) hlead
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.inc.thread.i.peel.i") (specs := bodySpecs)
    (vs := bodyValuesPeel i T F lead) (rest := bodyRest) hpre hsel (by decide)
  unfold bodyInstrs
  rw [h]
  unfold bodyRest
  simp only [bodyEnv]
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    simpa only [signExtend64_toNat] using hi63
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The head's chain on the latch's back edge. -/
theorem body_denote_back {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpre : s.pre = some "for.inc.thread.i.i")
    (hi : lookupName env "%inc57798.i.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode calls bodyInstrs (stateAt env s) =
      some (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s) := by
  have hsel : PhiSelects (stateAt env s) "for.inc.thread.i.i"
      bodySpecs (bodyValuesBack i T F lead) := by
    simp only [bodySpecs, bodyValuesBack, bodyValuesPeel]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc57798.i.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.i" (.int 64 lead) hlead
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.inc.thread.i.i") (specs := bodySpecs)
    (vs := bodyValuesBack i T F lead) (rest := bodyRest) hpre hsel (by decide)
  unfold bodyInstrs
  rw [h]
  unfold bodyRest
  simp only [bodyEnv]
  have hpos : (i.signExtend 64).toNat < 2 ^ 63 := by
    simpa only [signExtend64_toNat] using hi63
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The head's step to the digit edge, from the peeled entry. -/
theorem body_step_peel_digit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.i.i")
    (hpre : s.pre = some "for.inc.thread.i.peel.i")
    (hi : lookupName env "%inc57798.i.peel.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b)
        { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
    (b := ⟨"for.body.i.i", bodyInstrs,
      Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body_find
  · exact body_denote_peel hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
      "%or.cond.i.i" "if.then13.i.i" "if.else46.i.thread.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step to the loop's other exit, from the peeled entry. -/
theorem body_step_peel_nondigit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.i.i")
    (hpre : s.pre = some "for.inc.thread.i.peel.i")
    (hi : lookupName env "%inc57798.i.peel.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b)
        { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
    (b := ⟨"for.body.i.i", bodyInstrs,
      Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body_find
  · exact body_denote_peel hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
      "%or.cond.i.i" "if.then13.i.i" "if.else46.i.thread.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step to the digit edge, on the latch's back edge. -/
theorem body_step_back_digit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.i.i")
    (hpre : s.pre = some "for.inc.thread.i.i")
    (hi : lookupName env "%inc57798.i.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b)
        { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
    (b := ⟨"for.body.i.i", bodyInstrs,
      Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body_find
  · exact body_denote_back hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
      "%or.cond.i.i" "if.then13.i.i" "if.else46.i.thread.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The head's step to the loop's other exit, on the latch's back edge. -/
theorem body_step_back_nondigit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.i.i")
    (hpre : s.pre = some "for.inc.thread.i.i")
    (hi : lookupName env "%inc57798.i.i" = some (.int 64 i))
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + (i.signExtend 64).toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b)
        { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
    (b := ⟨"for.body.i.i", bodyInstrs,
      Term.condbr (Operand.reg "%or.cond.i.i") "if.then13.i.i" "if.else46.i.thread.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body_find
  · exact body_denote_back hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (bodyEnv env i T F lead (a + (i.signExtend 64).toNat) b) s)
      "%or.cond.i.i" "if.then13.i.i" "if.else46.i.thread.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The parse's residue exit: `if.end28.i.i`

The loop's exit block: six carried `phi`s (the two counters, the sticky byte, the
cursor, the lead's running value and the byte itself) and the retained-count
test.  The two incoming edges are the peel's exit and the loop's own digit edge;
the tests that chose them decide the sticky byte. -/

/-- The exit block's six `phi`s. -/
def end28Specs : List PhiSpec :=
  [{ dst := "%inc16.i.lcssa.i", ty := Ty.int 64,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%inc16.i.peel.i")),
                  ("if.then13.i.i", (Operand.reg "%inc16.i.i"))] },
   { dst := "%spec.select.i.lcssa.i", ty := Ty.int 64,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%spec.select.i.peel.i")),
                  ("if.then13.i.i", (Operand.reg "%spec.select.i.i"))] },
   { dst := "%cmp23.i.lcssa.i", ty := Ty.int 32,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%58")),
                  ("if.then13.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] },
   { dst := "%i.1725.i.lcssa292.i", ty := Ty.int 64,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%i.1725.ph.i.i")),
                  ("if.then13.i.i", (Operand.reg "%i.1725.i.i"))] },
   { dst := "%lead.0721.i.lcssa284.i", ty := Ty.int 64,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%lead.0721.ph.i.i")),
                  ("if.then13.i.i", (Operand.reg "%lead.0721.i.i"))] },
   { dst := "%.lcssa277.i", ty := Ty.int 8,
     incoming := [("if.end28.i.i.loopexit609", (Operand.reg "%55")),
                  ("if.then13.i.i", (Operand.reg "%57"))] }]

/-- The values the exit's `phi`s select at the peel's exit. -/
def end28ValuesExit (T F : BitVec 64) (c : BitVec 32) (i lead : BitVec 64)
    (d : BitVec 8) : List (String × Value) :=
  [("%inc16.i.lcssa.i", .int 64 T), ("%spec.select.i.lcssa.i", .int 64 F),
   ("%cmp23.i.lcssa.i", .int 32 c), ("%i.1725.i.lcssa292.i", .int 64 i),
   ("%lead.0721.i.lcssa284.i", .int 64 lead), ("%.lcssa277.i", .int 8 d)]

/-- The values the exit's `phi`s select at the loop's digit edge. -/
def end28ValuesThen (T F : BitVec 64) (i lead : BitVec 64) (d : BitVec 8) :
    List (String × Value) :=
  [("%inc16.i.lcssa.i", .int 64 T), ("%spec.select.i.lcssa.i", .int 64 F),
   ("%cmp23.i.lcssa.i", .int 32 0x00000001#32), ("%i.1725.i.lcssa292.i", .int 64 i),
   ("%lead.0721.i.lcssa284.i", .int 64 lead), ("%.lcssa277.i", .int 8 d)]

/-- The exit's remaining instruction: the retained count's test. -/
def end28Rest : List Instr :=
  [Instr.icmp "%cmp29.i.i" (IPred.ult) 64 (Operand.reg "%R.0724.ph.i.ph.i")
     (Operand.imm (Const.int 64 0x0000000000000300#64))]

/-- `if.end28.i.i`, from its pin. -/
def end28Instrs : List Instr := end28Specs.map PhiSpec.instr ++ end28Rest

theorem end28_find :
    numFastBody.findBlock "if.end28.i.i" =
      some ⟨"if.end28.i.i", end28Instrs,
        Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩ := by
  simp only [end28Instrs, end28Specs, end28Rest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_if_end28_i_i

/-- The exit's environment: the six selected cells and the retained count's test. -/
def end28Env (env : Env) (T F : BitVec 64) (c : BitVec 32) (i lead : BitVec 64)
    (d : BitVec 8) (R : BitVec 64) : Env :=
  ("%cmp29.i.i", .int 1 (evalICmp .ult R 0x0000000000000300#64)) ::
  ("%.lcssa277.i", .int 8 d) ::
  ("%lead.0721.i.lcssa284.i", .int 64 lead) ::
  ("%i.1725.i.lcssa292.i", .int 64 i) ::
  ("%cmp23.i.lcssa.i", .int 32 c) ::
  ("%spec.select.i.lcssa.i", .int 64 F) ::
  ("%inc16.i.lcssa.i", .int 64 T) :: env

/-- The exit's chain at the peel's exit. -/
theorem end28_denote_exit {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {c : BitVec 32} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpre : s.pre = some "if.end28.i.i.loopexit609")
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hc : lookupName env "%58" = some (.int 32 c))
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hd : lookupName env "%55" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R)) :
    denoteCode calls end28Instrs (stateAt env s) =
      some (stateAt (end28Env env T F c i lead d R) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end28.i.i.loopexit609"
      end28Specs (end28ValuesExit T F c i lead d) := by
    simp only [end28Specs, end28ValuesExit]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.peel.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.peel.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%58" (.int 32 c) hc
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.ph.i.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.ph.i.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%55" (.int 8 d) hd
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.end28.i.i.loopexit609") (specs := end28Specs)
    (vs := end28ValuesExit T F c i lead d) (rest := end28Rest) hpre hsel (by decide)
  unfold end28Instrs
  rw [h]
  unfold end28Rest
  simp only [end28Env]
  inner_step
  block_close

/-- The exit's chain at the loop's digit edge. -/
theorem end28_denote_then {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpre : s.pre = some "if.then13.i.i")
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hd : lookupName env "%57" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R)) :
    denoteCode calls end28Instrs (stateAt env s) =
      some (stateAt (end28Env env T F 0x00000001#32 i lead d R) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then13.i.i"
      end28Specs (end28ValuesThen T F i lead d) := by
    simp only [end28Specs, end28ValuesThen]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.i.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%57" (.int 8 d) hd
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.then13.i.i") (specs := end28Specs)
    (vs := end28ValuesThen T F i lead d) (rest := end28Rest) hpre hsel (by decide)
  unfold end28Instrs
  rw [h]
  unfold end28Rest
  simp only [end28Env]
  inner_step
  block_close

/-- The exit's step into the store's test, from the peel's exit. -/
theorem end28_step_exit_store {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {c : BitVec 32} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpc : s.pc = "if.end28.i.i")
    (hpre : s.pre = some "if.end28.i.i.loopexit609")
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hc : lookupName env "%58" = some (.int 32 c))
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hd : lookupName env "%55" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hbit : evalICmp .ult R 0x0000000000000300#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end28Env env T F c i lead d R)
        { s with pc := "if.then31.i.i", pre := some "if.end28.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end28Env env T F c i lead d R) s)
    (b := ⟨"if.end28.i.i", end28Instrs,
      Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end28_find
  · exact end28_denote_exit hpre hT hF hc hi hlead hd hR
  · rw [numFast_execTerm_condbr_one (s := stateAt (end28Env env T F c i lead d R) s)
      "%cmp29.i.i" "if.then31.i.i" "for.inc.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step to the latch, from the peel's exit. -/
theorem end28_step_exit_latch {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {c : BitVec 32} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpc : s.pc = "if.end28.i.i")
    (hpre : s.pre = some "if.end28.i.i.loopexit609")
    (hT : lookupName env "%inc16.i.peel.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.peel.i" = some (.int 64 F))
    (hc : lookupName env "%58" = some (.int 32 c))
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hd : lookupName env "%55" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hbit : evalICmp .ult R 0x0000000000000300#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end28Env env T F c i lead d R)
        { s with pc := "for.inc.i.i", pre := some "if.end28.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end28Env env T F c i lead d R) s)
    (b := ⟨"if.end28.i.i", end28Instrs,
      Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end28_find
  · exact end28_denote_exit hpre hT hF hc hi hlead hd hR
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end28Env env T F c i lead d R) s)
      "%cmp29.i.i" "if.then31.i.i" "for.inc.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step into the store's test, from the loop's digit edge. -/
theorem end28_step_then_store {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpc : s.pc = "if.end28.i.i")
    (hpre : s.pre = some "if.then13.i.i")
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hd : lookupName env "%57" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hbit : evalICmp .ult R 0x0000000000000300#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end28Env env T F 0x00000001#32 i lead d R)
        { s with pc := "if.then31.i.i", pre := some "if.end28.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end28Env env T F 0x00000001#32 i lead d R) s)
    (b := ⟨"if.end28.i.i", end28Instrs,
      Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end28_find
  · exact end28_denote_then hpre hT hF hi hlead hd hR
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (end28Env env T F 0x00000001#32 i lead d R) s)
      "%cmp29.i.i" "if.then31.i.i" "for.inc.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step to the latch, from the loop's digit edge. -/
theorem end28_step_then_latch {calls : Calls} {env : Env} {s : State}
    {T F : BitVec 64} {i lead : BitVec 64} {d : BitVec 8} {R : BitVec 64}
    (hpc : s.pc = "if.end28.i.i")
    (hpre : s.pre = some "if.then13.i.i")
    (hT : lookupName env "%inc16.i.i" = some (.int 64 T))
    (hF : lookupName env "%spec.select.i.i" = some (.int 64 F))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hd : lookupName env "%57" = some (.int 8 d))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hbit : evalICmp .ult R 0x0000000000000300#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end28Env env T F 0x00000001#32 i lead d R)
        { s with pc := "for.inc.i.i", pre := some "if.end28.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end28Env env T F 0x00000001#32 i lead d R) s)
    (b := ⟨"if.end28.i.i", end28Instrs,
      Term.condbr (Operand.reg "%cmp29.i.i") "if.then31.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end28_find
  · exact end28_denote_then hpre hT hF hi hlead hd hR
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (end28Env env T F 0x00000001#32 i lead d R) s)
      "%cmp29.i.i" "if.then31.i.i" "for.inc.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The store's continuation: `if.then36.i.i`

The retained digit's accumulation: the running value times ten, the digit's
widen, their sum and the top counter's step.  `for.body.i.i`'s retained array is
the one this block extends. -/

def mulInstrs : List Instr :=
  [Instr.binop "%mul.i.i" (BinOp.mul) 64 (Operand.reg "%top.0720.ph.i.ph.i")
     (Operand.imm (Const.int 64 0x000000000000000a#64)),
   Instr.zext "%conv37.i.i" 8 64 (Operand.reg "%.lcssa277.i"),
   Instr.binop "%add.i.i" (BinOp.add) 64 (Operand.reg "%mul.i.i") (Operand.reg "%conv37.i.i"),
   Instr.binop "%inc38.i.i" (BinOp.add) 64 (Operand.reg "%topn.0719.ph.i.ph.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64))]

theorem mul_find :
    numFastBody.findBlock "if.then36.i.i" =
      some ⟨"if.then36.i.i", mulInstrs, Term.br "for.inc.i.i"⟩ := by
  simpa only [mulInstrs] using numFast_findBlock_if_then36_i_i

/-- The accumulation's environment: the product, the digit's widen, their sum and
the top counter's step. -/
def mulEnv (env : Env) (top : BitVec 64) (d : BitVec 8) (topn : BitVec 64) : Env :=
  ("%inc38.i.i", .int 64 (topn + 0x0000000000000001#64)) ::
  ("%add.i.i", .int 64 (top * 0x000000000000000a#64
    + BitVec.ofNat 64 d.toNat)) ::
  ("%conv37.i.i", .int 64 (BitVec.ofNat 64 d.toNat)) ::
  ("%mul.i.i", .int 64 (top * 0x000000000000000a#64)) :: env

/-- The accumulation's chain at its pin. -/
theorem mul_denote {calls : Calls} {env : Env} {s : State}
    {top topn : BitVec 64} {d : BitVec 8}
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hd : lookupName env "%.lcssa277.i" = some (.int 8 d))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn)) :
    denoteCode calls mulInstrs (stateAt env s) =
      some (stateAt (mulEnv env top d topn) s) := by
  unfold mulInstrs
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The accumulation's step into the latch. -/
theorem mul_step {calls : Calls} {env : Env} {s : State}
    {top topn : BitVec 64} {d : BitVec 8}
    (hpc : s.pc = "if.then36.i.i")
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hd : lookupName env "%.lcssa277.i" = some (.int 8 d))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (mulEnv env top d topn)
        { s with pc := "for.inc.i.i", pre := some "if.then36.i.i" }) := by
  refine numFast_step_at (s' := stateAt (mulEnv env top d topn) s)
    (b := ⟨"if.then36.i.i", mulInstrs, Term.br "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using mul_find
  · exact mul_denote htop hd htopn
  · simp only [execTerm, stateAt, hpc]

/-! ### The store's own edge: `if.then31.i.i`

The retained digit's store is `JsonStage2NumFastTier3`'s block at the same pin:
`t3_copy_denote` is its chain, and the two steps below are its successors.  The
environment and the state are that module's, so the step reads the array the
window tie reads. -/

theorem store_find :
    numFastBody.findBlock "if.then31.i.i" =
      some ⟨"if.then31.i.i", t3CopyInstrs,
        Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i"⟩ := by
  simpa only [t3CopyInstrs] using numFast_findBlock_if_then31_i_i

/-- The store's step to the accumulation: the top counter is below nineteen. -/
theorem store_step_taken {calls : Calls} {env : Env} {s : State}
    {R topn : BitVec 64} {d : BitVec 8} {a : Nat}
    (hpc : s.pc = "if.then31.i.i")
    (hdig : lookupName env "%dig.i.i" = some (.ptr a))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hval : lookupName env "%.lcssa277.i" = some (.int 8 d))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (hpos : (R.signExtend 64).toNat < 2 ^ 63)
    (hbit : evalICmp .ult topn 0x13#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { t3CopyState env topn a R d s with
        pc := "if.then36.i.i", pre := some "if.then31.i.i" } := by
  refine numFast_step_at (s' := t3CopyState env topn a R d s)
    (b := ⟨"if.then31.i.i", t3CopyInstrs,
      Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using store_find
  · exact t3_copy_denote hdig hR hval htopn hpos
  · rw [numFast_execTerm_condbr_one (s := t3CopyState env topn a R d s)
      "%cmp34.i.i" "if.then36.i.i" "for.inc.i.i" ?_ hbit]
    · simp only [t3CopyState, stateAt, hpc]
    · simp only [t3CopyState, stateAt]
      exact lookupName_cons_self ..

/-- The store's step to the latch: the top counter has reached nineteen. -/
theorem store_step_skip {calls : Calls} {env : Env} {s : State}
    {R topn : BitVec 64} {d : BitVec 8} {a : Nat}
    (hpc : s.pc = "if.then31.i.i")
    (hdig : lookupName env "%dig.i.i" = some (.ptr a))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hval : lookupName env "%.lcssa277.i" = some (.int 8 d))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (hpos : (R.signExtend 64).toNat < 2 ^ 63)
    (hbit : evalICmp .ult topn 0x13#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { t3CopyState env topn a R d s with
        pc := "for.inc.i.i", pre := some "if.then31.i.i" } := by
  refine numFast_step_at (s' := t3CopyState env topn a R d s)
    (b := ⟨"if.then31.i.i", t3CopyInstrs,
      Term.condbr (Operand.reg "%cmp34.i.i") "if.then36.i.i" "for.inc.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using store_find
  · exact t3_copy_denote hdig hR hval htopn hpos
  · rw [numFast_execTerm_condbr_zero (s := t3CopyState env topn a R d s)
      "%cmp34.i.i" "if.then36.i.i" "for.inc.i.i" ?_ hbit]
    · simp only [t3CopyState, stateAt, hpc]
    · simp only [t3CopyState, stateAt]
      exact lookupName_cons_self ..

/-! ### The inner loop's non-digit edge: `if.else46.i.thread.i`

The loop's refusal: the byte's point test, the cursor's step, the end-of-lexeme
test, and the disjunction that chooses the refusal or the outer loop's head. -/

def threadInstrs : List Instr :=
  [Instr.icmp "%cmp48.i322.i" (IPred.ne) 8 (Operand.reg "%56") (Operand.imm (Const.int 8 0x2e#8)),
   Instr.binop "%inc57.i344.i" (BinOp.add) 64 (Operand.reg "%i.1725.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond.not.i345.i" (IPred.eq) 64 (Operand.reg "%inc57.i344.i")
     (Operand.reg "%n"),
   Instr.binop "%or.cond447.i" (BinOp.or) 1 (Operand.reg "%exitcond.not.i345.i")
     (Operand.reg "%cmp48.i322.i")]

theorem thread_find :
    numFastBody.findBlock "if.else46.i.thread.i" =
      some ⟨"if.else46.i.thread.i", threadInstrs,
        Term.condbr (Operand.reg "%or.cond447.i") "if.then59.i.i" "for.body.outer.i.i"⟩ := by
  simpa only [threadInstrs] using numFast_findBlock_if_else46_i_thread_i

/-- The refusal edge's environment: the byte's point test, the cursor's step and
their disjunction. -/
def threadEnv (env : Env) (b56 : BitVec 8) (i n : BitVec 64) : Env :=
  ("%or.cond447.i",
    .int 1 (evalICmp .eq (i + 0x0000000000000001#64) n ||| evalICmp .ne b56 0x2e#8)) ::
  ("%exitcond.not.i345.i", .int 1 (evalICmp .eq (i + 0x0000000000000001#64) n)) ::
  ("%inc57.i344.i", .int 64 (i + 0x0000000000000001#64)) ::
  ("%cmp48.i322.i", .int 1 (evalICmp .ne b56 0x2e#8)) :: env

/-- The refusal edge's chain at its pin. -/
theorem thread_denote {calls : Calls} {env : Env} {s : State}
    {b56 : BitVec 8} {i n : BitVec 64}
    (h56 : lookupName env "%56" = some (.int 8 b56))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls threadInstrs (stateAt env s) =
      some (stateAt (threadEnv env b56 i n) s) := by
  unfold threadInstrs
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The refusal edge's step to the refusal. -/
theorem thread_step_refuse {calls : Calls} {env : Env} {s : State}
    {b56 : BitVec 8} {i n : BitVec 64}
    (hpc : s.pc = "if.else46.i.thread.i")
    (h56 : lookupName env "%56" = some (.int 8 b56))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n ||| evalICmp .ne b56 0x2e#8
      = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (threadEnv env b56 i n)
        { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" }) := by
  refine numFast_step_at (s' := stateAt (threadEnv env b56 i n) s)
    (b := ⟨"if.else46.i.thread.i", threadInstrs,
      Term.condbr (Operand.reg "%or.cond447.i") "if.then59.i.i" "for.body.outer.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using thread_find
  · exact thread_denote h56 hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (threadEnv env b56 i n) s)
      "%or.cond447.i" "if.then59.i.i" "for.body.outer.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The refusal edge's step into the outer loop's head. -/
theorem thread_step_outer {calls : Calls} {env : Env} {s : State}
    {b56 : BitVec 8} {i n : BitVec 64}
    (hpc : s.pc = "if.else46.i.thread.i")
    (h56 : lookupName env "%56" = some (.int 8 b56))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n ||| evalICmp .ne b56 0x2e#8
      = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (threadEnv env b56 i n)
        { s with pc := "for.body.outer.i.i", pre := some "if.else46.i.thread.i" }) := by
  refine numFast_step_at (s' := stateAt (threadEnv env b56 i n) s)
    (b := ⟨"if.else46.i.thread.i", threadInstrs,
      Term.condbr (Operand.reg "%or.cond447.i") "if.then59.i.i" "for.body.outer.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using thread_find
  · exact thread_denote h56 hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (threadEnv env b56 i n) s)
      "%or.cond447.i" "if.then59.i.i" "for.body.outer.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The latch's end-of-lexeme exit: `for.end.thread.i.i`

The outer loop's counted exit tests the seen flag once more: an unseen flag
refuses, a seen one frees the parse for the exponent's entry. -/

def endThreadInstrs : List Instr :=
  [Instr.icmp "%59" (IPred.eq) 32 (Operand.reg "%seen.4.ph.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem endThread_find :
    numFastBody.findBlock "for.end.thread.i.i" =
      some ⟨"for.end.thread.i.i", endThreadInstrs,
        Term.condbr (Operand.reg "%59") "if.then59.i.i" "if.end104.i.i"⟩ := by
  simpa only [endThreadInstrs] using numFast_findBlock_for_end_thread_i_i

/-- The counted exit's environment: the seen flag's zero test. -/
def endThreadEnv (env : Env) (seen : BitVec 32) : Env :=
  ("%59", .int 1 (evalICmp .eq seen 0x00000000#32)) :: env

/-- The counted exit's chain at its pin. -/
theorem endThread_denote {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen)) :
    denoteCode calls endThreadInstrs (stateAt env s) =
      some (stateAt (endThreadEnv env seen) s) := by
  unfold endThreadInstrs
  inner_step
  block_close

/-- The counted exit's step to the refusal. -/
theorem endThread_step_refuse {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hpc : s.pc = "for.end.thread.i.i")
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen))
    (hbit : evalICmp .eq seen 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (endThreadEnv env seen)
        { s with pc := "if.then59.i.i", pre := some "for.end.thread.i.i" }) := by
  refine numFast_step_at (s' := stateAt (endThreadEnv env seen) s)
    (b := ⟨"for.end.thread.i.i", endThreadInstrs,
      Term.condbr (Operand.reg "%59") "if.then59.i.i" "if.end104.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using endThread_find
  · exact endThread_denote hseen
  · rw [numFast_execTerm_condbr_one (s := stateAt (endThreadEnv env seen) s) "%59"
      "if.then59.i.i" "if.end104.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The counted exit's step past the store, into the lead's clamps. -/
theorem endThread_step_clamps {calls : Calls} {env : Env} {s : State} {seen : BitVec 32}
    (hpc : s.pc = "for.end.thread.i.i")
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen))
    (hbit : evalICmp .eq seen 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (endThreadEnv env seen)
        { s with pc := "if.end104.i.i", pre := some "for.end.thread.i.i" }) := by
  refine numFast_step_at (s' := stateAt (endThreadEnv env seen) s)
    (b := ⟨"for.end.thread.i.i", endThreadInstrs,
      Term.condbr (Operand.reg "%59") "if.then59.i.i" "if.end104.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using endThread_find
  · exact endThread_denote hseen
  · rw [numFast_execTerm_condbr_zero (s := stateAt (endThreadEnv env seen) s) "%59"
      "if.then59.i.i" "if.end104.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The outer loop's latch: `for.inc.i.i`

The loop's back edge carries ten `phi`s — the cursor, the lead's running value,
the sticky byte, the seen and in-fraction flags, the two top counters, the two
digit counters and the retained count — and then steps the cursor and tests it.
Four edges reach it (the store's two edges, the non-digit edge and the residue
exit); the selected values differ only in which cells they name, so the three
edges that count a seen digit share one value list and the non-digit edge has its
own. -/

/-- The latch's ten `phi`s, in the pin's order. -/
def latchSpecs : List PhiSpec :=
  [{ dst := "%i.1725.i294.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                  ("if.then36.i.i", (Operand.reg "%i.1725.i.lcssa292.i")),
                  ("if.else46.i.i", (Operand.reg "%i.1725.ph.i.i")),
                  ("if.end28.i.i", (Operand.reg "%i.1725.i.lcssa292.i"))] },
   { dst := "%lead.0721.i287.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                  ("if.then36.i.i", (Operand.reg "%lead.0721.i.lcssa284.i")),
                  ("if.else46.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                  ("if.end28.i.i", (Operand.reg "%lead.0721.i.lcssa284.i"))] },
   { dst := "%sticky.4.ph.i.i", ty := Ty.int 32,
     incoming := [("if.then31.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                  ("if.then36.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                  ("if.else46.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                  ("if.end28.i.i", (Operand.reg "%cmp23.i.lcssa.i"))] },
   { dst := "%seen.4.ph.i.i", ty := Ty.int 32,
     incoming := [("if.then31.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                  ("if.then36.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                  ("if.else46.i.i", (Operand.reg "%seen.0717.ph.i.i")),
                  ("if.end28.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] },
   { dst := "%in_frac.2.ph.i.i", ty := Ty.int 32,
     incoming := [("if.then31.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                  ("if.then36.i.i", (Operand.reg "%in_frac.0718.ph.i.i")),
                  ("if.else46.i.i", (Operand.imm (Const.int 32 0x00000001#32))),
                  ("if.end28.i.i", (Operand.reg "%in_frac.0718.ph.i.i"))] },
   { dst := "%topn.4.ph.i.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                  ("if.then36.i.i", (Operand.reg "%inc38.i.i")),
                  ("if.else46.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                  ("if.end28.i.i", (Operand.reg "%topn.0719.ph.i.ph.i"))] },
   { dst := "%top.4.ph.i.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                  ("if.then36.i.i", (Operand.reg "%add.i.i")),
                  ("if.else46.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                  ("if.end28.i.i", (Operand.reg "%top.0720.ph.i.ph.i"))] },
   { dst := "%F.3.ph.i.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                  ("if.then36.i.i", (Operand.reg "%spec.select.i.lcssa.i")),
                  ("if.else46.i.i", (Operand.reg "%F.0722.ph.i.i")),
                  ("if.end28.i.i", (Operand.reg "%spec.select.i.lcssa.i"))] },
   { dst := "%T.2.ph.i.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                  ("if.then36.i.i", (Operand.reg "%inc16.i.lcssa.i")),
                  ("if.else46.i.i", (Operand.reg "%T.0723.ph.i.i")),
                  ("if.end28.i.i", (Operand.reg "%inc16.i.lcssa.i"))] },
   { dst := "%R.4.ph.i.i", ty := Ty.int 64,
     incoming := [("if.then31.i.i", (Operand.reg "%inc32.i.i")),
                  ("if.then36.i.i", (Operand.reg "%inc32.i.i")),
                  ("if.else46.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                  ("if.end28.i.i", (Operand.reg "%R.0724.ph.i.ph.i"))] }]

/-- The latch's remaining instructions: the cursor's step and its test. -/
def latchRest : List Instr :=
  [Instr.binop "%inc57.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.i294.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%exitcond.not.i.i" (IPred.eq) 64 (Operand.reg "%inc57.i.i")
     (Operand.reg "%n")]

/-- `for.inc.i.i`, from its pin. -/
def latchInstrs : List Instr := latchSpecs.map PhiSpec.instr ++ latchRest

theorem latch_find :
    numFastBody.findBlock "for.inc.i.i" =
      some ⟨"for.inc.i.i", latchInstrs,
        Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
          "for.body.outer.i.outer.i"⟩ := by
  simp only [latchInstrs, latchSpecs, latchRest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_for_inc_i_i

/-- The latch's environment: the ten selected cells, the cursor's step and its
test. -/
def latchEnv (env : Env) (i lead : BitVec 64) (sticky seen inFrac : BitVec 32)
    (topn top F T R : BitVec 64) (n : BitVec 64) : Env :=
  ("%exitcond.not.i.i", .int 1 (evalICmp .eq (i + 0x0000000000000001#64) n)) ::
  ("%inc57.i.i", .int 64 (i + 0x0000000000000001#64)) ::
  ("%R.4.ph.i.i", .int 64 R) ::
  ("%T.2.ph.i.i", .int 64 T) ::
  ("%F.3.ph.i.i", .int 64 F) ::
  ("%top.4.ph.i.i", .int 64 top) ::
  ("%topn.4.ph.i.i", .int 64 topn) ::
  ("%in_frac.2.ph.i.i", .int 32 inFrac) ::
  ("%seen.4.ph.i.i", .int 32 seen) ::
  ("%sticky.4.ph.i.i", .int 32 sticky) ::
  ("%lead.0721.i287.i", .int 64 lead) ::
  ("%i.1725.i294.i", .int 64 i) :: env

/-- The values the latch's `phi`s select on the edges that count a seen digit:
the store's two edges and the residue exit. -/
def latchValuesSeen (i lead : BitVec 64) (sticky inFrac : BitVec 32)
    (topn top F T R : BitVec 64) : List (String × Value) :=
  [("%i.1725.i294.i", .int 64 i), ("%lead.0721.i287.i", .int 64 lead),
   ("%sticky.4.ph.i.i", .int 32 sticky), ("%seen.4.ph.i.i", .int 32 0x00000001#32),
   ("%in_frac.2.ph.i.i", .int 32 inFrac), ("%topn.4.ph.i.i", .int 64 topn),
   ("%top.4.ph.i.i", .int 64 top), ("%F.3.ph.i.i", .int 64 F),
   ("%T.2.ph.i.i", .int 64 T), ("%R.4.ph.i.i", .int 64 R)]

/-- The values the latch's `phi`s select on the non-digit edge: the seen flag is
the head's and the fraction flag is set. -/
def latchValuesDot (i lead : BitVec 64) (sticky seen : BitVec 32)
    (topn top F T R : BitVec 64) : List (String × Value) :=
  [("%i.1725.i294.i", .int 64 i), ("%lead.0721.i287.i", .int 64 lead),
   ("%sticky.4.ph.i.i", .int 32 sticky), ("%seen.4.ph.i.i", .int 32 seen),
   ("%in_frac.2.ph.i.i", .int 32 0x00000001#32), ("%topn.4.ph.i.i", .int 64 topn),
   ("%top.4.ph.i.i", .int 64 top), ("%F.3.ph.i.i", .int 64 F),
   ("%T.2.ph.i.i", .int 64 T), ("%R.4.ph.i.i", .int 64 R)]

/-- The latch's chain at the store's taken edge. -/
theorem latch_denote_then31 {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpre : s.pre = some "if.then31.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls latchInstrs (stateAt env s) =
      some (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then31.i.i"
      latchSpecs (latchValuesSeen i lead sticky inFrac topn top F T R) := by
    simp only [latchSpecs, latchValuesSeen]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.i.lcssa292.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.lcssa284.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.0716.ph.i.ph.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%in_frac.0718.ph.i.i" (.int 32 inFrac) hin
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.0719.ph.i.ph.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.0720.ph.i.ph.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.lcssa.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.lcssa.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc32.i.i" (.int 64 R) hR
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.then31.i.i") (specs := latchSpecs)
    (vs := latchValuesSeen i lead sticky inFrac topn top F T R) (rest := latchRest)
    hpre hsel (by decide)
  unfold latchInstrs
  rw [h]
  unfold latchRest
  simp only [latchEnv]
  inner_step
  inner_step
  block_close

/-- The latch's chain at the accumulation's edge. -/
theorem latch_denote_then36 {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpre : s.pre = some "if.then36.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%inc38.i.i" = some (.int 64 topn))
    (htop : lookupName env "%add.i.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls latchInstrs (stateAt env s) =
      some (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then36.i.i"
      latchSpecs (latchValuesSeen i lead sticky inFrac topn top F T R) := by
    simp only [latchSpecs, latchValuesSeen]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.i.lcssa292.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.lcssa284.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.0716.ph.i.ph.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%in_frac.0718.ph.i.i" (.int 32 inFrac) hin
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc38.i.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%add.i.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.lcssa.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.lcssa.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc32.i.i" (.int 64 R) hR
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.then36.i.i") (specs := latchSpecs)
    (vs := latchValuesSeen i lead sticky inFrac topn top F T R) (rest := latchRest)
    hpre hsel (by decide)
  unfold latchInstrs
  rw [h]
  unfold latchRest
  simp only [latchEnv]
  inner_step
  inner_step
  block_close

/-- The latch's chain at the residue exit. -/
theorem latch_denote_end28 {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpre : s.pre = some "if.end28.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%cmp23.i.lcssa.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls latchInstrs (stateAt env s) =
      some (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end28.i.i"
      latchSpecs (latchValuesSeen i lead sticky inFrac topn top F T R) := by
    simp only [latchSpecs, latchValuesSeen]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.i.lcssa292.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.lcssa284.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%cmp23.i.lcssa.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%in_frac.0718.ph.i.i" (.int 32 inFrac) hin
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.0719.ph.i.ph.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.0720.ph.i.ph.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%spec.select.i.lcssa.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc16.i.lcssa.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%R.0724.ph.i.ph.i" (.int 64 R) hR
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.end28.i.i") (specs := latchSpecs)
    (vs := latchValuesSeen i lead sticky inFrac topn top F T R) (rest := latchRest)
    hpre hsel (by decide)
  unfold latchInstrs
  rw [h]
  unfold latchRest
  simp only [latchEnv]
  inner_step
  inner_step
  block_close

/-- The latch's chain at the non-digit edge. -/
theorem latch_denote_else46 {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky seen : BitVec 32} {topn top F T R n : BitVec 64}
    (hpre : s.pre = some "if.else46.i.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 (sticky : BitVec 32)))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 (seen : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls latchInstrs (stateAt env s) =
      some (stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.else46.i.i"
      latchSpecs (latchValuesDot i lead sticky seen topn top F T R) := by
    simp only [latchSpecs, latchValuesDot]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%i.1725.ph.i.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.ph.i.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.0716.ph.i.ph.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%seen.0717.ph.i.i" (.int 32 seen) hseen
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.0719.ph.i.ph.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.0720.ph.i.ph.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.0722.ph.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.0723.ph.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%R.0724.ph.i.ph.i" (.int 64 R) hR
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.else46.i.i") (specs := latchSpecs)
    (vs := latchValuesDot i lead sticky seen topn top F T R) (rest := latchRest)
    hpre hsel (by decide)
  unfold latchInstrs
  rw [h]
  unfold latchRest
  simp only [latchEnv]
  inner_step
  inner_step
  block_close

/-- The latch's step to the counted exit, at the store's taken edge. -/
theorem latch_step_then31_exit {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.then31.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.end.thread.i.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_then31 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step back into the outer loop, at the store's taken edge. -/
theorem latch_step_then31_back {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.then31.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.body.outer.i.outer.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_then31 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step to the counted exit, at the accumulation's edge. -/
theorem latch_step_then36_exit {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.then36.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%inc38.i.i" = some (.int 64 topn))
    (htop : lookupName env "%add.i.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.end.thread.i.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_then36 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step back into the outer loop, at the accumulation's edge. -/
theorem latch_step_then36_back {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.then36.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%inc38.i.i" = some (.int 64 topn))
    (htop : lookupName env "%add.i.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%inc32.i.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.body.outer.i.outer.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_then36 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step to the counted exit, at the residue exit. -/
theorem latch_step_end28_exit {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.end28.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%cmp23.i.lcssa.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.end.thread.i.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_end28 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step back into the outer loop, at the residue exit. -/
theorem latch_step_end28_back {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky inFrac : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.end28.i.i")
    (hi : lookupName env "%i.1725.i.lcssa292.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.i.lcssa284.i" = some (.int 64 lead))
    (hsticky : lookupName env "%cmp23.i.lcssa.i" = some (.int 32 sticky))
    (hin : lookupName env "%in_frac.0718.ph.i.i" = some (.int 32 (inFrac : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%spec.select.i.lcssa.i" = some (.int 64 F))
    (hT : lookupName env "%inc16.i.lcssa.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n)
        { s with pc := "for.body.outer.i.outer.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_end28 hpre hi hlead hsticky hin htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (latchEnv env i lead sticky 0x00000001#32 inFrac topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step to the counted exit, at the non-digit edge. -/
theorem latch_step_else46_exit {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky seen : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.else46.i.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 (sticky : BitVec 32)))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 (seen : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n)
        { s with pc := "for.end.thread.i.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_else46 hpre hi hlead hsticky hseen htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The latch's step back into the outer loop, at the non-digit edge. -/
theorem latch_step_else46_back {calls : Calls} {env : Env} {s : State}
    {i lead : BitVec 64} {sticky seen : BitVec 32} {topn top F T R n : BitVec 64}
    (hpc : s.pc = "for.inc.i.i")
    (hpre : s.pre = some "if.else46.i.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 (sticky : BitVec 32)))
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 (seen : BitVec 32)))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n)
        { s with pc := "for.body.outer.i.outer.i", pre := some "for.inc.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n) s)
    (b := ⟨"for.inc.i.i", latchInstrs,
      Term.condbr (Operand.reg "%exitcond.not.i.i") "for.end.thread.i.i"
        "for.body.outer.i.outer.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using latch_find
  · exact latch_denote_else46 hpre hi hlead hsticky hseen htopn htop hF hT hR hn
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (latchEnv env i lead sticky seen 0x00000001#32 topn top F T R n) s)
      "%exitcond.not.i.i" "for.end.thread.i.i" "for.body.outer.i.outer.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The exponent's entry band

The parse's exit hands the exponent to `if.then64.i.i`, which steps the cursor
past the lexeme's end and tests it; the test's taken edge reads the byte after
the end, and the two switch leaves test it for a sign, with `if.then77.i.i`
writing the sign and stepping the cursor past it.  The band ends at
`if.end83.i.i`, whose `phi`s carry the sign and the cursor and whose test chooses
the copy's entry or the copy's exit. -/

def then64Instrs : List Instr :=
  [Instr.binop "%inc65.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.icmp "%cmp66.i.i" (IPred.ult) 64 (Operand.reg "%inc65.i.i") (Operand.reg "%n")]

theorem then64_find :
    numFastBody.findBlock "if.then64.i.i" =
      some ⟨"if.then64.i.i", then64Instrs,
        Term.condbr (Operand.reg "%cmp66.i.i") "land.lhs.true68.i.i" "if.end83.i.i"⟩ := by
  simpa only [then64Instrs] using numFast_findBlock_if_then64_i_i

/-- The exponent entry's environment: the cursor's step and its test. -/
def then64Env (env : Env) (i n : BitVec 64) : Env :=
  ("%cmp66.i.i", .int 1 (evalICmp .ult (i + 0x0000000000000001#64) n)) ::
  ("%inc65.i.i", .int 64 (i + 0x0000000000000001#64)) :: env

/-- The exponent entry's chain at its pin. -/
theorem then64_denote {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls then64Instrs (stateAt env s) =
      some (stateAt (then64Env env i n) s) := by
  unfold then64Instrs
  inner_step
  inner_step
  block_close

/-- The exponent entry's step to the sign's read. -/
theorem then64_step_read {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "if.then64.i.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then64Env env i n)
        { s with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then64Env env i n) s)
    (b := ⟨"if.then64.i.i", then64Instrs,
      Term.condbr (Operand.reg "%cmp66.i.i") "land.lhs.true68.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then64_find
  · exact then64_denote hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (then64Env env i n) s) "%cmp66.i.i"
      "land.lhs.true68.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exponent entry's step past the sign's read. -/
theorem then64_step_skip {calls : Calls} {env : Env} {s : State} {i n : BitVec 64}
    (hpc : s.pc = "if.then64.i.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult (i + 0x0000000000000001#64) n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then64Env env i n)
        { s with pc := "if.end83.i.i", pre := some "if.then64.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then64Env env i n) s)
    (b := ⟨"if.then64.i.i", then64Instrs,
      Term.condbr (Operand.reg "%cmp66.i.i") "land.lhs.true68.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then64_find
  · exact then64_denote hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (then64Env env i n) s) "%cmp66.i.i"
      "land.lhs.true68.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

def land68Instrs : List Instr :=
  [Instr.gep "%arrayidx69.i.i" (Ty.int 8) (Operand.reg "%p") (Operand.reg "%inc65.i.i"),
   Instr.load "%60" (Ty.int 8) (Operand.reg "%arrayidx69.i.i")]

theorem land68_find :
    numFastBody.findBlock "land.lhs.true68.i.i" =
      some ⟨"land.lhs.true68.i.i", land68Instrs, Term.br "NodeBlock25"⟩ := by
  simpa only [land68Instrs] using numFast_findBlock_land_lhs_true68_i_i

/-- The sign's read environment: the address and the byte. -/
def land68Env (env : Env) (a0 : Nat) (inc65 : BitVec 64) (b60 : BitVec 8) : Env :=
  ("%60", .int 8 b60) ::
  ("%arrayidx69.i.i", .ptr (a0 + (inc65.signExtend 64).toNat)) :: env

/-- The sign's read chain at its pin. -/
theorem land68_denote {calls : Calls} {env : Env} {s : State}
    {inc65 : BitVec 64} {b60 : BitVec 8} {a0 : Nat}
    (hp : lookupName env "%p" = some (.ptr a0))
    (hinc : lookupName env "%inc65.i.i" = some (.int 64 inc65))
    (hi63 : inc65.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a0 + (inc65.signExtend 64).toNat) 1 = some (natToBytes b60.toNat 1)) :
    denoteCode calls land68Instrs (stateAt env s) =
      some (stateAt (land68Env env a0 inc65 b60) s) := by
  unfold land68Instrs
  have hpos : (inc65.signExtend 64).toNat < 2 ^ 63 := by
    simpa only [signExtend64_toNat] using hi63
  inner_step
  inner_step
  block_close

/-- The sign's read step into the switch's pivot. -/
theorem land68_step {calls : Calls} {env : Env} {s : State}
    {inc65 : BitVec 64} {b60 : BitVec 8} {a0 : Nat}
    (hpc : s.pc = "land.lhs.true68.i.i")
    (hp : lookupName env "%p" = some (.ptr a0))
    (hinc : lookupName env "%inc65.i.i" = some (.int 64 inc65))
    (hi63 : inc65.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a0 + (inc65.signExtend 64).toNat) 1 = some (natToBytes b60.toNat 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (land68Env env a0 inc65 b60)
        { s with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" }) := by
  refine numFast_step_at (s' := stateAt (land68Env env a0 inc65 b60) s)
    (b := ⟨"land.lhs.true68.i.i", land68Instrs, Term.br "NodeBlock25"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using land68_find
  · exact land68_denote hp hinc hi63 hb
  · simp only [execTerm, stateAt, hpc]

def pivot25Instrs : List Instr :=
  [Instr.icmp "%Pivot26" (IPred.slt) 8 (Operand.reg "%60")
     (Operand.imm (Const.int 8 0x2d#8))]

theorem pivot25_find :
    numFastBody.findBlock "NodeBlock25" =
      some ⟨"NodeBlock25", pivot25Instrs,
        Term.condbr (Operand.reg "%Pivot26") "LeafBlock21" "LeafBlock23"⟩ := by
  simpa only [pivot25Instrs] using numFast_findBlock_NodeBlock25

/-- The pivot's environment: the byte's signed comparison with `'-'`. -/
def pivot25Env (env : Env) (b60 : BitVec 8) : Env :=
  ("%Pivot26", .int 1 (evalICmp .slt b60 0x2d#8)) :: env

/-- The pivot's chain at its pin. -/
theorem pivot25_denote {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (h60 : lookupName env "%60" = some (.int 8 b60)) :
    denoteCode calls pivot25Instrs (stateAt env s) =
      some (stateAt (pivot25Env env b60) s) := by
  unfold pivot25Instrs
  inner_step
  block_close

/-- The pivot's step to the plus leaf. -/
theorem pivot25_step_plus {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "NodeBlock25")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .slt b60 0x2d#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pivot25Env env b60)
        { s with pc := "LeafBlock21", pre := some "NodeBlock25" }) := by
  refine numFast_step_at (s' := stateAt (pivot25Env env b60) s)
    (b := ⟨"NodeBlock25", pivot25Instrs,
      Term.condbr (Operand.reg "%Pivot26") "LeafBlock21" "LeafBlock23"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pivot25_find
  · exact pivot25_denote h60
  · rw [numFast_execTerm_condbr_one (s := stateAt (pivot25Env env b60) s) "%Pivot26"
      "LeafBlock21" "LeafBlock23" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The pivot's step to the minus leaf. -/
theorem pivot25_step_minus {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "NodeBlock25")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .slt b60 0x2d#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pivot25Env env b60)
        { s with pc := "LeafBlock23", pre := some "NodeBlock25" }) := by
  refine numFast_step_at (s' := stateAt (pivot25Env env b60) s)
    (b := ⟨"NodeBlock25", pivot25Instrs,
      Term.condbr (Operand.reg "%Pivot26") "LeafBlock21" "LeafBlock23"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pivot25_find
  · exact pivot25_denote h60
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pivot25Env env b60) s) "%Pivot26"
      "LeafBlock21" "LeafBlock23" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

def leaf23Instrs : List Instr :=
  [Instr.icmp "%SwitchLeaf24" (IPred.eq) 8 (Operand.reg "%60")
     (Operand.imm (Const.int 8 0x2d#8))]

theorem leaf23_find :
    numFastBody.findBlock "LeafBlock23" =
      some ⟨"LeafBlock23", leaf23Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf24") "if.then77.i.i" "if.end83.i.i"⟩ := by
  simpa only [leaf23Instrs] using numFast_findBlock_LeafBlock23

/-- The minus leaf's environment: the byte's test against `'-'`. -/
def leaf23Env (env : Env) (b60 : BitVec 8) : Env :=
  ("%SwitchLeaf24", .int 1 (evalICmp .eq b60 0x2d#8)) :: env

/-- The minus leaf's chain at its pin. -/
theorem leaf23_denote {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (h60 : lookupName env "%60" = some (.int 8 b60)) :
    denoteCode calls leaf23Instrs (stateAt env s) =
      some (stateAt (leaf23Env env b60) s) := by
  unfold leaf23Instrs
  inner_step
  block_close

/-- The minus leaf's step to the sign's write. -/
theorem leaf23_step_sign {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "LeafBlock23")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .eq b60 0x2d#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leaf23Env env b60)
        { s with pc := "if.then77.i.i", pre := some "LeafBlock23" }) := by
  refine numFast_step_at (s' := stateAt (leaf23Env env b60) s)
    (b := ⟨"LeafBlock23", leaf23Instrs,
      Term.condbr (Operand.reg "%SwitchLeaf24") "if.then77.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using leaf23_find
  · exact leaf23_denote h60
  · rw [numFast_execTerm_condbr_one (s := stateAt (leaf23Env env b60) s) "%SwitchLeaf24"
      "if.then77.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The minus leaf's step past the sign's write. -/
theorem leaf23_step_skip {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "LeafBlock23")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .eq b60 0x2d#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leaf23Env env b60)
        { s with pc := "if.end83.i.i", pre := some "LeafBlock23" }) := by
  refine numFast_step_at (s' := stateAt (leaf23Env env b60) s)
    (b := ⟨"LeafBlock23", leaf23Instrs,
      Term.condbr (Operand.reg "%SwitchLeaf24") "if.then77.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using leaf23_find
  · exact leaf23_denote h60
  · rw [numFast_execTerm_condbr_zero (s := stateAt (leaf23Env env b60) s) "%SwitchLeaf24"
      "if.then77.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

def leaf21Instrs : List Instr :=
  [Instr.icmp "%SwitchLeaf22" (IPred.eq) 8 (Operand.reg "%60")
     (Operand.imm (Const.int 8 0x2b#8))]

theorem leaf21_find :
    numFastBody.findBlock "LeafBlock21" =
      some ⟨"LeafBlock21", leaf21Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf22") "if.then77.i.i" "if.end83.i.i"⟩ := by
  simpa only [leaf21Instrs] using numFast_findBlock_LeafBlock21

/-- The plus leaf's environment: the byte's test against `'+'`. -/
def leaf21Env (env : Env) (b60 : BitVec 8) : Env :=
  ("%SwitchLeaf22", .int 1 (evalICmp .eq b60 0x2b#8)) :: env

/-- The plus leaf's chain at its pin. -/
theorem leaf21_denote {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (h60 : lookupName env "%60" = some (.int 8 b60)) :
    denoteCode calls leaf21Instrs (stateAt env s) =
      some (stateAt (leaf21Env env b60) s) := by
  unfold leaf21Instrs
  inner_step
  block_close

/-- The plus leaf's step to the sign's write. -/
theorem leaf21_step_sign {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "LeafBlock21")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .eq b60 0x2b#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leaf21Env env b60)
        { s with pc := "if.then77.i.i", pre := some "LeafBlock21" }) := by
  refine numFast_step_at (s' := stateAt (leaf21Env env b60) s)
    (b := ⟨"LeafBlock21", leaf21Instrs,
      Term.condbr (Operand.reg "%SwitchLeaf22") "if.then77.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using leaf21_find
  · exact leaf21_denote h60
  · rw [numFast_execTerm_condbr_one (s := stateAt (leaf21Env env b60) s) "%SwitchLeaf22"
      "if.then77.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The plus leaf's step past the sign's write. -/
theorem leaf21_step_skip {calls : Calls} {env : Env} {s : State} {b60 : BitVec 8}
    (hpc : s.pc = "LeafBlock21")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hbit : evalICmp .eq b60 0x2b#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (leaf21Env env b60)
        { s with pc := "if.end83.i.i", pre := some "LeafBlock21" }) := by
  refine numFast_step_at (s' := stateAt (leaf21Env env b60) s)
    (b := ⟨"LeafBlock21", leaf21Instrs,
      Term.condbr (Operand.reg "%SwitchLeaf22") "if.then77.i.i" "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using leaf21_find
  · exact leaf21_denote h60
  · rw [numFast_execTerm_condbr_zero (s := stateAt (leaf21Env env b60) s) "%SwitchLeaf22"
      "if.then77.i.i" "if.end83.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

def then77Instrs : List Instr :=
  [Instr.icmp "%cmp80.i.i" (IPred.ne) 8 (Operand.reg "%60")
     (Operand.imm (Const.int 8 0x2d#8)),
   Instr.binop "%inc82.i.i" (BinOp.add) 64 (Operand.reg "%i.1725.ph.i.i")
     (Operand.imm (Const.int 64 0x0000000000000002#64))]

theorem then77_find :
    numFastBody.findBlock "if.then77.i.i" =
      some ⟨"if.then77.i.i", then77Instrs, Term.br "if.end83.i.i"⟩ := by
  simpa only [then77Instrs] using numFast_findBlock_if_then77_i_i

/-- The sign's write environment: the sign and the cursor's two-step. -/
def then77Env (env : Env) (b60 : BitVec 8) (i : BitVec 64) : Env :=
  ("%inc82.i.i", .int 64 (i + 0x0000000000000002#64)) ::
  ("%cmp80.i.i", .int 1 (evalICmp .ne b60 0x2d#8)) :: env

/-- The sign's write chain at its pin. -/
theorem then77_denote {calls : Calls} {env : Env} {s : State}
    {b60 : BitVec 8} {i : BitVec 64}
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i)) :
    denoteCode calls then77Instrs (stateAt env s) =
      some (stateAt (then77Env env b60 i) s) := by
  unfold then77Instrs
  inner_step
  inner_step
  block_close

/-- The sign's write step into the merge. -/
theorem then77_step {calls : Calls} {env : Env} {s : State}
    {b60 : BitVec 8} {i : BitVec 64}
    (hpc : s.pc = "if.then77.i.i")
    (h60 : lookupName env "%60" = some (.int 8 b60))
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then77Env env b60 i)
        { s with pc := "if.end83.i.i", pre := some "if.then77.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then77Env env b60 i) s)
    (b := ⟨"if.then77.i.i", then77Instrs, Term.br "if.end83.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then77_find
  · exact then77_denote h60 hi
  · simp only [execTerm, stateAt, hpc]

/-- The merge's two `phi`s: the sign and the cursor the band leaves. -/
def end83Specs : List PhiSpec :=
  [{ dst := "%esign.0.i.i", ty := Ty.int 1,
     incoming := [("if.then77.i.i", (Operand.reg "%cmp80.i.i")),
                  ("if.then64.i.i", (Operand.imm (Const.int 1 0x1#1))),
                  ("LeafBlock21", (Operand.imm (Const.int 1 0x1#1))),
                  ("LeafBlock23", (Operand.imm (Const.int 1 0x1#1)))] },
   { dst := "%i.2.i.i", ty := Ty.int 64,
     incoming := [("if.then77.i.i", (Operand.reg "%inc82.i.i")),
                  ("if.then64.i.i", (Operand.reg "%inc65.i.i")),
                  ("LeafBlock21", (Operand.reg "%inc65.i.i")),
                  ("LeafBlock23", (Operand.reg "%inc65.i.i"))] }]

/-- The merge's remaining instruction: the cursor's test. -/
def end83Rest : List Instr :=
  [Instr.icmp "%cmp85733.i.i" (IPred.ult) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n")]

/-- `if.end83.i.i`, from its pin. -/
def end83Instrs : List Instr := end83Specs.map PhiSpec.instr ++ end83Rest

theorem end83_find :
    numFastBody.findBlock "if.end83.i.i" =
      some ⟨"if.end83.i.i", end83Instrs,
        Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
          "for.end100.i.i"⟩ := by
  simp only [end83Instrs, end83Specs, end83Rest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_if_end83_i_i

/-- The merge's environment: the sign, the cursor and the cursor's test. -/
def end83Env (env : Env) (esign : BitVec 1) (i2 n : BitVec 64) : Env :=
  ("%cmp85733.i.i", .int 1 (evalICmp .ult i2 n)) ::
  ("%i.2.i.i", .int 64 i2) ::
  ("%esign.0.i.i", .int 1 esign) :: env

/-- The merge's chain at the sign's write. -/
theorem end83_denote_then77 {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {i2 n : BitVec 64}
    (hpre : s.pre = some "if.then77.i.i")
    (he : lookupName env "%cmp80.i.i" = some (.int 1 esign))
    (hi : lookupName env "%inc82.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls end83Instrs (stateAt env s) =
      some (stateAt (end83Env env esign i2 n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then77.i.i"
      end83Specs [("%esign.0.i.i", .int 1 esign), ("%i.2.i.i", .int 64 i2)] := by
    simp only [end83Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%cmp80.i.i" (.int 1 esign) he
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc82.i.i" (.int 64 i2) hi
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.then77.i.i") (specs := end83Specs)
    (vs := [("%esign.0.i.i", .int 1 esign), ("%i.2.i.i", .int 64 i2)])
    (rest := end83Rest) hpre hsel (by decide)
  unfold end83Instrs
  rw [h]
  unfold end83Rest
  simp only [end83Env]
  inner_step
  block_close

/-- The merge's chain at the exponent entry's skip. -/
theorem end83_denote_then64 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpre : s.pre = some "if.then64.i.i")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls end83Instrs (stateAt env s) =
      some (stateAt (end83Env env 0x1#1 i2 n) s) := by
  have hsel : PhiSelects (stateAt env s) "if.then64.i.i"
      end83Specs [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)] := by
    simp only [end83Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 1 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc65.i.i" (.int 64 i2) hi
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.then64.i.i") (specs := end83Specs)
    (vs := [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)])
    (rest := end83Rest) hpre hsel (by decide)
  unfold end83Instrs
  rw [h]
  unfold end83Rest
  simp only [end83Env]
  inner_step
  block_close

/-- The merge's chain at the minus leaf's skip. -/
theorem end83_denote_leaf23 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpre : s.pre = some "LeafBlock23")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls end83Instrs (stateAt env s) =
      some (stateAt (end83Env env 0x1#1 i2 n) s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock23"
      end83Specs [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)] := by
    simp only [end83Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 1 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc65.i.i" (.int 64 i2) hi
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "LeafBlock23") (specs := end83Specs)
    (vs := [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)])
    (rest := end83Rest) hpre hsel (by decide)
  unfold end83Instrs
  rw [h]
  unfold end83Rest
  simp only [end83Env]
  inner_step
  block_close

/-- The merge's chain at the plus leaf's skip. -/
theorem end83_denote_leaf21 {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpre : s.pre = some "LeafBlock21")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n)) :
    denoteCode calls end83Instrs (stateAt env s) =
      some (stateAt (end83Env env 0x1#1 i2 n) s) := by
  have hsel : PhiSelects (stateAt env s) "LeafBlock21"
      end83Specs [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)] := by
    simp only [end83Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 1 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc65.i.i" (.int 64 i2) hi
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "LeafBlock21") (specs := end83Specs)
    (vs := [("%esign.0.i.i", .int 1 0x1#1), ("%i.2.i.i", .int 64 i2)])
    (rest := end83Rest) hpre hsel (by decide)
  unfold end83Instrs
  rw [h]
  unfold end83Rest
  simp only [end83Env]
  inner_step
  block_close

/-- The merge's step to the copy's entry, at the sign's write. -/
theorem end83_step_then77_copy {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "if.then77.i.i")
    (he : lookupName env "%cmp80.i.i" = some (.int 1 esign))
    (hi : lookupName env "%inc82.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env esign i2 n)
        { s with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env esign i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_then77 hpre he hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (end83Env env esign i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's exit, at the sign's write. -/
theorem end83_step_then77_exit {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "if.then77.i.i")
    (he : lookupName env "%cmp80.i.i" = some (.int 1 esign))
    (hi : lookupName env "%inc82.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env esign i2 n)
        { s with pc := "for.end100.i.i", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env esign i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_then77 hpre he hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end83Env env esign i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's entry, at the exponent entry's skip. -/
theorem end83_step_then64_copy {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "if.then64.i.i")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_then64 hpre hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's exit, at the exponent entry's skip. -/
theorem end83_step_then64_exit {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "if.then64.i.i")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.end100.i.i", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_then64 hpre hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's entry, at the minus leaf's skip. -/
theorem end83_step_leaf23_copy {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "LeafBlock23")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_leaf23 hpre hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's exit, at the minus leaf's skip. -/
theorem end83_step_leaf23_exit {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "LeafBlock23")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.end100.i.i", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_leaf23 hpre hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's entry, at the plus leaf's skip. -/
theorem end83_step_leaf21_copy {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "LeafBlock21")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_leaf21 hpre hi hn
  · rw [numFast_execTerm_condbr_one (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge's step to the copy's exit, at the plus leaf's skip. -/
theorem end83_step_leaf21_exit {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "if.end83.i.i")
    (hpre : s.pre = some "LeafBlock21")
    (hi : lookupName env "%inc65.i.i" = some (.int 64 i2))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hbit : evalICmp .ult i2 n = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end83Env env 0x1#1 i2 n)
        { s with pc := "for.end100.i.i", pre := some "if.end83.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end83Env env 0x1#1 i2 n) s)
    (b := ⟨"if.end83.i.i", end83Instrs,
      Term.condbr (Operand.reg "%cmp85733.i.i") "for.body87.i.i.preheader"
        "for.end100.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end83_find
  · exact end83_denote_leaf21 hpre hi hn
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end83Env env 0x1#1 i2 n) s)
      "%cmp85733.i.i" "for.body87.i.i.preheader" "for.end100.i.i"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The copy's exit: `for.end100.i.i`

The copy's exit merges its accumulator from three edges; the one this module
needs is `if.end83.i.i`'s, where the accumulator is zero.  The block then negates
the accumulator and selects at the sign's bit, so its result is the lead's clamp
input for a positive lexeme and the exponent's for a negative one. -/

/-- The copy exit's `phi`, in the pin's order. -/
def end100Specs : List PhiSpec :=
  [{ dst := "%e.0.lcssa.i.i", ty := Ty.int 64,
     incoming := [("if.end83.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.end100.i.i.loopexit.unr-lcssa", (Operand.reg "%e.1.i.i.lcssa.ph")),
                  ("for.inc98.i.i.epil", (Operand.reg "%e.1.i.i.epil"))] }]

/-- The copy exit's remaining instructions: the accumulator's negation and the
sign's selection. -/
def end100Rest : List Instr :=
  [Instr.binop "%sub102.i.i" (BinOp.sub) 64 (Operand.imm (Const.int 64 0x0000000000000000#64))
     (Operand.reg "%e.0.lcssa.i.i"),
   Instr.select "%cond103.i.i" (Ty.int 64) (Operand.reg "%esign.0.i.i")
     (Operand.reg "%e.0.lcssa.i.i") (Operand.reg "%sub102.i.i")]

/-- `for.end100.i.i`, from its pin. -/
def end100Instrs : List Instr := end100Specs.map PhiSpec.instr ++ end100Rest

theorem end100_find :
    numFastBody.findBlock "for.end100.i.i" =
      some ⟨"for.end100.i.i", end100Instrs, Term.br "if.end104.i.i"⟩ := by
  simp only [end100Instrs, end100Specs, end100Rest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_for_end100_i_i

/-- The copy exit's environment: the accumulator, its negation and the sign's
selection. -/
def end100Env (env : Env) (esign : BitVec 1) (e : BitVec 64) : Env :=
  ("%cond103.i.i",
    .int 64 (if esign = 1 then e else 0x0000000000000000#64 - e)) ::
  ("%sub102.i.i", .int 64 (0x0000000000000000#64 - e)) ::
  ("%e.0.lcssa.i.i", .int 64 e) :: env

/-- The copy exit's chain at the merge. -/
theorem end100_denote_exit {calls : Calls} {env : Env} {s : State} {esign : BitVec 1}
    (hpre : s.pre = some "if.end83.i.i")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign)) :
    denoteCode calls end100Instrs (stateAt env s) =
      some (stateAt (end100Env env esign 0) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end83.i.i" end100Specs
      [("%e.0.lcssa.i.i", .int 64 0)] := by
    simp only [end100Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 64 _
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.end83.i.i") (specs := end100Specs)
    (vs := [("%e.0.lcssa.i.i", .int 64 0)]) (rest := end100Rest) hpre hsel (by decide)
  unfold end100Instrs
  rw [h]
  unfold end100Rest
  simp only [end100Env]
  inner_step
  inner_step
  block_close

/-- The copy exit's step into the clamps. -/
theorem end100_step {calls : Calls} {env : Env} {s : State} {esign : BitVec 1}
    (hpc : s.pc = "for.end100.i.i")
    (hpre : s.pre = some "if.end83.i.i")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end100Env env esign 0)
        { s with pc := "if.end104.i.i", pre := some "for.end100.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end100Env env esign 0) s)
    (b := ⟨"for.end100.i.i", end100Instrs, Term.br "if.end104.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end100_find
  · exact end100_denote_exit hpre he
  · simp only [execTerm, stateAt, hpc]

/-! ### The clamps' head: `if.end104.i.i`

The clamp's head merges the counters from the two exits and forms the leading
exponent `lead + R - 1 + (exp10 - F)` and the wide exponent `T - (lead + R) + …`,
then tests the wide one against `308`: above it the run saturates to infinity,
below `-324` to zero. -/

/-- The clamp head's eight `phi`s, in the pin's order. -/
def end104Specs : List PhiSpec :=
  [{ dst := "%lead.0721.i286.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%lead.0721.ph.i.i")),
                  ("for.end.thread.i.i", (Operand.reg "%lead.0721.i287.i"))] },
   { dst := "%sticky.0714.i.i", ty := Ty.int 32,
     incoming := [("for.end100.i.i", (Operand.reg "%sticky.0716.ph.i.ph.i")),
                  ("for.end.thread.i.i", (Operand.reg "%sticky.4.ph.i.i"))] },
   { dst := "%topn.0711.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%topn.0719.ph.i.ph.i")),
                  ("for.end.thread.i.i", (Operand.reg "%topn.4.ph.i.i"))] },
   { dst := "%top.0709.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%top.0720.ph.i.ph.i")),
                  ("for.end.thread.i.i", (Operand.reg "%top.4.ph.i.i"))] },
   { dst := "%F.0705.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%F.0722.ph.i.i")),
                  ("for.end.thread.i.i", (Operand.reg "%F.3.ph.i.i"))] },
   { dst := "%T.0703.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%T.0723.ph.i.i")),
                  ("for.end.thread.i.i", (Operand.reg "%T.2.ph.i.i"))] },
   { dst := "%R.0701.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%R.0724.ph.i.ph.i")),
                  ("for.end.thread.i.i", (Operand.reg "%R.4.ph.i.i"))] },
   { dst := "%exp10.0.i.i", ty := Ty.int 64,
     incoming := [("for.end100.i.i", (Operand.reg "%cond103.i.i")),
                  ("for.end.thread.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))] }]

/-- The clamp head's remaining instructions. -/
def end104Rest : List Instr :=
  [Instr.binop "%sub105.i.i" (BinOp.sub) 64 (Operand.reg "%exp10.0.i.i")
     (Operand.reg "%F.0705.i.i"),
   Instr.binop "%69" (BinOp.add) 64 (Operand.reg "%lead.0721.i286.i")
     (Operand.reg "%R.0701.i.i"),
   Instr.binop "%sub107.i.i" (BinOp.sub) 64 (Operand.reg "%T.0703.i.i")
     (Operand.reg "%69"),
   Instr.binop "%add108.i.i" (BinOp.add) 64 (Operand.reg "%sub107.i.i")
     (Operand.reg "%sub105.i.i"),
   Instr.binop "%sub109.i.i" (BinOp.add) 64 (Operand.reg "%R.0701.i.i")
     (Operand.imm (Const.int 64 0xffffffffffffffff#64)),
   Instr.binop "%add110.i.i" (BinOp.add) 64 (Operand.reg "%sub109.i.i")
     (Operand.reg "%add108.i.i"),
   Instr.icmp "%cmp111.i.i" (IPred.sgt) 64 (Operand.reg "%add110.i.i")
     (Operand.imm (Const.int 64 0x0000000000000134#64))]

/-- `if.end104.i.i`, from its pin. -/
def end104Instrs : List Instr := end104Specs.map PhiSpec.instr ++ end104Rest

theorem end104_find :
    numFastBody.findBlock "if.end104.i.i" =
      some ⟨"if.end104.i.i", end104Instrs,
        Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩ := by
  simp only [end104Instrs, end104Specs, end104Rest, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_if_end104_i_i

/-- The clamp head's environment: the eight selected cells and the three
exponents' arithmetic. -/
def end104Env (env : Env) (lead : BitVec 64) (sticky : BitVec 32)
    (topn top F T R exp10 : BitVec 64) : Env :=
  ("%cmp111.i.i", .int 1 (evalICmp .sgt
    ((R + 0xffffffffffffffff#64) + ((T - (lead + R)) + (exp10 - F)))
    0x0000000000000134#64)) ::
  ("%add110.i.i", .int 64
    ((R + 0xffffffffffffffff#64) + ((T - (lead + R)) + (exp10 - F)))) ::
  ("%sub109.i.i", .int 64 (R + 0xffffffffffffffff#64)) ::
  ("%add108.i.i", .int 64 ((T - (lead + R)) + (exp10 - F))) ::
  ("%sub107.i.i", .int 64 (T - (lead + R))) ::
  ("%69", .int 64 (lead + R)) ::
  ("%sub105.i.i", .int 64 (exp10 - F)) ::
  ("%exp10.0.i.i", .int 64 exp10) ::
  ("%R.0701.i.i", .int 64 R) ::
  ("%T.0703.i.i", .int 64 T) ::
  ("%F.0705.i.i", .int 64 F) ::
  ("%top.0709.i.i", .int 64 top) ::
  ("%topn.0711.i.i", .int 64 topn) ::
  ("%sticky.0714.i.i", .int 32 sticky) ::
  ("%lead.0721.i286.i", .int 64 lead) :: env

/-- The clamp head's chain at the copy's exit. -/
theorem end104_denote_copy {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R exp10 : BitVec 64}
    (hpre : s.pre = some "for.end100.i.i")
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hexp : lookupName env "%cond103.i.i" = some (.int 64 exp10)) :
    denoteCode calls end104Instrs (stateAt env s) =
      some (stateAt (end104Env env lead sticky topn top F T R exp10) s) := by
  have hsel : PhiSelects (stateAt env s) "for.end100.i.i" end104Specs
      [("%lead.0721.i286.i", .int 64 lead), ("%sticky.0714.i.i", .int 32 sticky),
       ("%topn.0711.i.i", .int 64 topn), ("%top.0709.i.i", .int 64 top),
       ("%F.0705.i.i", .int 64 F), ("%T.0703.i.i", .int 64 T),
       ("%R.0701.i.i", .int 64 R), ("%exp10.0.i.i", .int 64 exp10)] := by
    simp only [end104Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.ph.i.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.0716.ph.i.ph.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.0719.ph.i.ph.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.0720.ph.i.ph.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.0722.ph.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.0723.ph.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%R.0724.ph.i.ph.i" (.int 64 R) hR
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%cond103.i.i" (.int 64 exp10) hexp
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.end100.i.i") (specs := end104Specs)
    (vs := [("%lead.0721.i286.i", .int 64 lead), ("%sticky.0714.i.i", .int 32 sticky),
      ("%topn.0711.i.i", .int 64 topn), ("%top.0709.i.i", .int 64 top),
      ("%F.0705.i.i", .int 64 F), ("%T.0703.i.i", .int 64 T),
      ("%R.0701.i.i", .int 64 R), ("%exp10.0.i.i", .int 64 exp10)])
    (rest := end104Rest) hpre hsel (by decide)
  unfold end104Instrs
  rw [h]
  unfold end104Rest
  simp only [end104Env]
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The clamp head's step to the infinity clamp. -/
theorem end104_step_over {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R exp10 : BitVec 64}
    (hpc : s.pc = "if.end104.i.i")
    (hpre : s.pre = some "for.end100.i.i")
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hexp : lookupName env "%cond103.i.i" = some (.int 64 exp10))
    (hbit : evalICmp .sgt
      ((R + 0xffffffffffffffff#64) + ((T - (lead + R)) + (exp10 - F)))
      0x0000000000000134#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end104Env env lead sticky topn top F T R exp10)
        { s with pc := "if.then113.i.i", pre := some "if.end104.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (end104Env env lead sticky topn top F T R exp10) s)
    (b := ⟨"if.end104.i.i", end104Instrs,
      Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end104_find
  · exact end104_denote_copy hpre hlead hsticky htopn htop hF hT hR hexp
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (end104Env env lead sticky topn top F T R exp10) s)
      "%cmp111.i.i" "if.then113.i.i" "if.end120.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The clamp head's step to the underflow clamp's test. -/
theorem end104_step_under {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R exp10 : BitVec 64}
    (hpc : s.pc = "if.end104.i.i")
    (hpre : s.pre = some "for.end100.i.i")
    (hlead : lookupName env "%lead.0721.ph.i.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.0719.ph.i.ph.i" = some (.int 64 topn))
    (htop : lookupName env "%top.0720.ph.i.ph.i" = some (.int 64 top))
    (hF : lookupName env "%F.0722.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.0723.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.0724.ph.i.ph.i" = some (.int 64 R))
    (hexp : lookupName env "%cond103.i.i" = some (.int 64 exp10))
    (hbit : evalICmp .sgt
      ((R + 0xffffffffffffffff#64) + ((T - (lead + R)) + (exp10 - F)))
      0x0000000000000134#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end104Env env lead sticky topn top F T R exp10)
        { s with pc := "if.end120.i.i", pre := some "if.end104.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (end104Env env lead sticky topn top F T R exp10) s)
    (b := ⟨"if.end104.i.i", end104Instrs,
      Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end104_find
  · exact end104_denote_copy hpre hlead hsticky htopn htop hF hT hR hexp
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (end104Env env lead sticky topn top F T R exp10) s)
      "%cmp111.i.i" "if.then113.i.i" "if.end120.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The two saturating clamps: `if.then113.i.i` and `if.then123.i.i`

Each is one `select` of two floating literals at the sign's bit: the infinity
clamp takes `±inf` and the underflow clamp takes `±0`.  The block's value is the
sign's, and the run leaves at `if.end291`. -/

/-- A clamp's instruction list: one `select` of two floating literals. -/
def clampInstrs (d : String) (x y : BitVec 64) : List Instr :=
  [Instr.select d Ty.double (Operand.reg "%cmp1.i") (Operand.imm (Const.float x))
     (Operand.imm (Const.float y))]

/-- The clamp's environment: the selected bits. -/
def clampEnv (env : Env) (d : String) (x y : BitVec 64) (bb : BitVec 1) : Env :=
  (d, .float (if bb = 1 then x else y)) :: env

/-- A clamp's chain at its pin. -/
theorem clamp_denote {calls : Calls} {env : Env} {s : State}
    {d : String} {x y : BitVec 64} {bb : BitVec 1}
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    denoteCode calls (clampInstrs d x y) (stateAt env s) =
      some (stateAt (clampEnv env d x y bb) s) := by
  unfold clampInstrs
  inner_step
  block_close

/-- A clamp's step to the function's return. -/
theorem clamp_step {calls : Calls} {env : Env} {s : State}
    {d : String} {x y : BitVec 64} {bb : BitVec 1} {pc : String}
    (hpc : s.pc = pc)
    (hfind : numFastBody.findBlock pc = some ⟨pc, clampInstrs d x y, Term.br "if.end291"⟩)
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (clampEnv env d x y bb)
        { s with pc := "if.end291", pre := some pc }) := by
  refine numFast_step_at (s' := stateAt (clampEnv env d x y bb) s)
    (b := ⟨pc, clampInstrs d x y, Term.br "if.end291"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hfind
  · exact clamp_denote hc
  · simp only [execTerm, stateAt, hpc]

theorem then113_find :
    numFastBody.findBlock "if.then113.i.i" =
      some ⟨"if.then113.i.i", clampInstrs "%spec.select694.i.i"
          0xfff0000000000000#64 0x7ff0000000000000#64, Term.br "if.end291"⟩ := by
  simpa only [clampInstrs] using numFast_findBlock_if_then113_i_i

theorem then123_find :
    numFastBody.findBlock "if.then123.i.i" =
      some ⟨"if.then123.i.i", clampInstrs "%cond125.i.i"
          0x8000000000000000#64 0x0000000000000000#64, Term.br "if.end291"⟩ := by
  simpa only [clampInstrs] using numFast_findBlock_if_then123_i_i

theorem then113_step {calls : Calls} {env : Env} {s : State} {bb : BitVec 1}
    (hpc : s.pc = "if.then113.i.i")
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (clampEnv env "%spec.select694.i.i" 0xfff0000000000000#64
          0x7ff0000000000000#64 bb)
        { s with pc := "if.end291", pre := some "if.then113.i.i" }) := by
  exact clamp_step hpc then113_find hc

theorem then123_step {calls : Calls} {env : Env} {s : State} {bb : BitVec 1}
    (hpc : s.pc = "if.then123.i.i")
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (clampEnv env "%cond125.i.i" 0x8000000000000000#64
          0x0000000000000000#64 bb)
        { s with pc := "if.end291", pre := some "if.then123.i.i" }) := by
  exact clamp_step hpc then123_find hc

/-! ### The underflow clamp's test: `if.end120.i.i` -/

def end120Instrs : List Instr :=
  [Instr.icmp "%cmp121.i.i" (IPred.slt) 64 (Operand.reg "%add110.i.i")
     (Operand.imm (Const.int 64 0xfffffffffffffebc#64))]

theorem end120_find :
    numFastBody.findBlock "if.end120.i.i" =
      some ⟨"if.end120.i.i", end120Instrs,
        Term.condbr (Operand.reg "%cmp121.i.i") "if.then123.i.i" "if.end126.i.i"⟩ := by
  simpa only [end120Instrs] using numFast_findBlock_if_end120_i_i

/-- The underflow test's environment: the wide exponent's comparison with
`-324`. -/
def end120Env (env : Env) (e : BitVec 64) : Env :=
  ("%cmp121.i.i", .int 1 (evalICmp .slt e 0xfffffffffffffebc#64)) :: env

/-- The underflow test's chain at its pin. -/
theorem end120_denote {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (he : lookupName env "%add110.i.i" = some (.int 64 e)) :
    denoteCode calls end120Instrs (stateAt env s) =
      some (stateAt (end120Env env e) s) := by
  unfold end120Instrs
  inner_step
  block_close

/-- The underflow test's step to the zero clamp. -/
theorem end120_step_then {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "if.end120.i.i")
    (he : lookupName env "%add110.i.i" = some (.int 64 e))
    (hbit : evalICmp .slt e 0xfffffffffffffebc#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end120Env env e)
        { s with pc := "if.then123.i.i", pre := some "if.end120.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end120Env env e) s)
    (b := ⟨"if.end120.i.i", end120Instrs,
      Term.condbr (Operand.reg "%cmp121.i.i") "if.then123.i.i" "if.end126.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end120_find
  · exact end120_denote he
  · rw [numFast_execTerm_condbr_one (s := stateAt (end120Env env e) s) "%cmp121.i.i"
      "if.then123.i.i" "if.end126.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The underflow test's step into the ladder's head. -/
theorem end120_step_end {calls : Calls} {env : Env} {s : State} {e : BitVec 64}
    (hpc : s.pc = "if.end120.i.i")
    (he : lookupName env "%add110.i.i" = some (.int 64 e))
    (hbit : evalICmp .slt e 0xfffffffffffffebc#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end120Env env e)
        { s with pc := "if.end126.i.i", pre := some "if.end120.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end120Env env e) s)
    (b := ⟨"if.end120.i.i", end120Instrs,
      Term.condbr (Operand.reg "%cmp121.i.i") "if.then123.i.i" "if.end126.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end120_find
  · exact end120_denote he
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end120Env env e) s) "%cmp121.i.i"
      "if.then123.i.i" "if.end126.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The ladder's staging: `if.end126.i.i`

The clamp's exit stages the window: the sticky byte, the scale and the retained
count, then tests the retained count for zero, which chooses the empty-array
split or the big multiply's chunk loop. -/

def end126Instrs : List Instr :=
  [Instr.callVoid "llvm.lifetime.start.p0"
     [((Ty.int 64), (Operand.imm (Const.int 64 0x0000000000000620#64))),
      (Ty.ptr, (Operand.reg "%v.i.i"))],
   Instr.gep "%sticky127.i.i" (Ty.int 8) (Operand.reg "%v.i.i")
     (Operand.imm (Const.int 64 0x0000000000000618#64)),
   Instr.store (Ty.int 32) (Operand.reg "%sticky.0714.i.i") (Operand.reg "%sticky127.i.i"),
   Instr.gep "%S128.i.i" (Ty.int 8) (Operand.reg "%v.i.i")
     (Operand.imm (Const.int 64 0x0000000000000610#64)),
   Instr.store (Ty.int 64) (Operand.reg "%add108.i.i") (Operand.reg "%S128.i.i"),
   Instr.gep "%n.i.i.i" (Ty.int 8) (Operand.reg "%v.i.i")
     (Operand.imm (Const.int 64 0x0000000000000300#64)),
   Instr.icmp "%cmp130737.not.i.i" (IPred.eq) 64 (Operand.reg "%R.0701.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem end126_find :
    numFastBody.findBlock "if.end126.i.i" =
      some ⟨"if.end126.i.i", end126Instrs,
        Term.condbr (Operand.reg "%cmp130737.not.i.i") "if.end151.i.i.sink.split"
          "for.body132.i.i"⟩ := by
  simpa only [end126Instrs] using numFast_findBlock_if_end126_i_i

/-- The staging's environment: the three addresses and the retained count's
test. -/
def end126Env (env : Env) (v : Nat) (R : BitVec 64) : Env :=
  ("%cmp130737.not.i.i", .int 1 (evalICmp .eq R 0x0000000000000000#64)) ::
  ("%n.i.i.i", .ptr (v + ((0x0000000000000300#64).signExtend 64).toNat)) ::
  ("%S128.i.i", .ptr (v + ((0x0000000000000610#64).signExtend 64).toNat)) ::
  ("%sticky127.i.i", .ptr (v + ((0x0000000000000618#64).signExtend 64).toNat)) :: env

/-- The staging's state: the same environment, the call's cursor, and the two
stores the window's bytes. -/
def end126State (env : Env) (v : Nat) (x : BitVec 64) (sticky : BitVec 32)
    (R : BitVec 64) (r : CallOutcome) (s : State) : State :=
  { stateAt (end126Env env v R) s with
      mem := writeBytes
        (writeBytes r.mem (v + ((0x0000000000000618#64).signExtend 64).toNat)
          (natToBytes sticky.toNat 4))
        (v + ((0x0000000000000610#64).signExtend 64).toNat)
        (natToBytes x.toNat 8),
      next := r.next }

/-- The staging's chain at its pin. -/
theorem end126_denote {calls : Calls} {env : Env} {s : State}
    {v : Nat} {x : BitVec 64} {sticky : BitVec 32} {R : BitVec 64} {r : CallOutcome}
    (hpv : lookupName env "%v.i.i" = some (.ptr v))
    (hr : calls "llvm.lifetime.start.p0"
      [.int 64 0x0000000000000620#64, .ptr v] s.mem s.next = some r)
    (hsticky : lookupName env "%sticky.0714.i.i" = some (.int 32 sticky))
    (hx : lookupName env "%add108.i.i" = some (.int 64 x))
    (hR : lookupName env "%R.0701.i.i" = some (.int 64 R)) :
    denoteCode calls end126Instrs (stateAt env s) =
      some (end126State env v x sticky R r s) := by
  unfold end126Instrs
  have hpos618 : (((0x0000000000000618#64)).signExtend 64).toNat < 2 ^ 63 := by decide
  have hpos610 : (((0x0000000000000610#64)).signExtend 64).toNat < 2 ^ 63 := by decide
  have hpos300 : (((0x0000000000000300#64)).signExtend 64).toNat < 2 ^ 63 := by decide
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The staging's step to the empty-array split: the retained count is zero. -/
theorem end126_step_split {calls : Calls} {env : Env} {s : State}
    {v : Nat} {x : BitVec 64} {sticky : BitVec 32} {R : BitVec 64} {r : CallOutcome}
    (hpc : s.pc = "if.end126.i.i")
    (hpv : lookupName env "%v.i.i" = some (.ptr v))
    (hr : calls "llvm.lifetime.start.p0"
      [.int 64 0x0000000000000620#64, .ptr v] s.mem s.next = some r)
    (hsticky : lookupName env "%sticky.0714.i.i" = some (.int 32 sticky))
    (hx : lookupName env "%add108.i.i" = some (.int 64 x))
    (hR : lookupName env "%R.0701.i.i" = some (.int 64 R))
    (hbit : evalICmp .eq R 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { end126State env v x sticky R r s with
        pc := "if.end151.i.i.sink.split", pre := some "if.end126.i.i" } := by
  refine numFast_step_at (s' := end126State env v x sticky R r s)
    (b := ⟨"if.end126.i.i", end126Instrs,
      Term.condbr (Operand.reg "%cmp130737.not.i.i") "if.end151.i.i.sink.split"
        "for.body132.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end126_find
  · exact end126_denote hpv hr hsticky hx hR
  · rw [numFast_execTerm_condbr_one (s := end126State env v x sticky R r s)
      "%cmp130737.not.i.i" "if.end151.i.i.sink.split" "for.body132.i.i" ?_ hbit]
    · simp only [end126State, end126Env, stateAt, hpc]
    · simp only [end126State, end126Env, stateAt]
      exact lookupName_cons_self ..

/-- The staging's step into the chunk loop: the retained count is nonzero. -/
theorem end126_step_chunks {calls : Calls} {env : Env} {s : State}
    {v : Nat} {x : BitVec 64} {sticky : BitVec 32} {R : BitVec 64} {r : CallOutcome}
    (hpc : s.pc = "if.end126.i.i")
    (hpv : lookupName env "%v.i.i" = some (.ptr v))
    (hr : calls "llvm.lifetime.start.p0"
      [.int 64 0x0000000000000620#64, .ptr v] s.mem s.next = some r)
    (hsticky : lookupName env "%sticky.0714.i.i" = some (.int 32 sticky))
    (hx : lookupName env "%add108.i.i" = some (.int 64 x))
    (hR : lookupName env "%R.0701.i.i" = some (.int 64 R))
    (hbit : evalICmp .eq R 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { end126State env v x sticky R r s with
        pc := "for.body132.i.i", pre := some "if.end126.i.i" } := by
  refine numFast_step_at (s' := end126State env v x sticky R r s)
    (b := ⟨"if.end126.i.i", end126Instrs,
      Term.condbr (Operand.reg "%cmp130737.not.i.i") "if.end151.i.i.sink.split"
        "for.body132.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end126_find
  · exact end126_denote hpv hr hsticky hx hR
  · rw [numFast_execTerm_condbr_zero (s := end126State env v x sticky R r s)
      "%cmp130737.not.i.i" "if.end151.i.i.sink.split" "for.body132.i.i" ?_ hbit]
    · simp only [end126State, end126Env, stateAt, hpc]
    · simp only [end126State, end126Env, stateAt]
      exact lookupName_cons_self ..

/-! ### The parse's exit path to the copy's entry

The steps compose: from the head's non-digit edge the run leaves the parse, takes
the exponent's entry and its sign's read, and reaches `if.end83.i.i`, whose merge
chooses the copy's entry.  Two paths reach it — the byte after the cursor is not a
sign (`if.end83`'s merge takes the cursor's own step) or it is (`if.then77` adds
two) — and each is stated as a whole `runFuel` run so a caller can spend them as
one.

The lookups the later blocks read from the environment are resolved against the
builders the earlier blocks wrote: the tactic below unfolds a stage's builders,
peels the cells the stage did not write, and takes the cell it did. -/

/-- Resolve a register read against a chain of the band's environment builders. -/
macro "band_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp only [dotEnv, parseEndEnv, then64Env, land68Env, pivot25Env, leaf23Env,
        leaf21Env, then77Env, end83Env]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | rw [lookupName_cons_self]
       | assumption
       | rfl)))

/-- A seven-step run: the seven steps compose into one `runFuel` identity. -/
theorem runFuel_chain7 {calls : Calls} {f : Function}
    {s0 s1 s2 s3 s4 s5 s6 s7 : State}
    (h1 : step calls f s0 = .jump s1) (h2 : step calls f s1 = .jump s2)
    (h3 : step calls f s2 = .jump s3) (h4 : step calls f s3 = .jump s4)
    (h5 : step calls f s4 = .jump s5) (h6 : step calls f s5 = .jump s6)
    (h7 : step calls f s6 = .jump s7) :
    runFuel calls 7 f s0 = runFuel calls 0 f s7 := by
  rw [show (7 : Nat) = 1 + 6 from rfl, runFuel_jump_prefix h1 6]
  rw [show (6 : Nat) = 1 + 5 from rfl, runFuel_jump_prefix h2 5]
  rw [show (5 : Nat) = 1 + 4 from rfl, runFuel_jump_prefix h3 4]
  rw [show (4 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix h4 3]
  rw [show (3 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix h5 2]
  rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix h6 1]
  rw [show (1 : Nat) = 1 + 0 from rfl, runFuel_jump_prefix h7 0]

/-- An eight-step run: the same, with one more step. -/
theorem runFuel_chain8 {calls : Calls} {f : Function}
    {s0 s1 s2 s3 s4 s5 s6 s7 s8 : State}
    (h1 : step calls f s0 = .jump s1) (h2 : step calls f s1 = .jump s2)
    (h3 : step calls f s2 = .jump s3) (h4 : step calls f s3 = .jump s4)
    (h5 : step calls f s4 = .jump s5) (h6 : step calls f s5 = .jump s6)
    (h7 : step calls f s6 = .jump s7) (h8 : step calls f s7 = .jump s8) :
    runFuel calls 8 f s0 = runFuel calls 0 f s8 := by
  rw [show (8 : Nat) = 1 + 7 from rfl, runFuel_jump_prefix h1 7]
  rw [show (7 : Nat) = 1 + 6 from rfl, runFuel_jump_prefix h2 6]
  rw [show (6 : Nat) = 1 + 5 from rfl, runFuel_jump_prefix h3 5]
  rw [show (5 : Nat) = 1 + 4 from rfl, runFuel_jump_prefix h4 4]
  rw [show (4 : Nat) = 1 + 3 from rfl, runFuel_jump_prefix h5 3]
  rw [show (3 : Nat) = 1 + 2 from rfl, runFuel_jump_prefix h6 2]
  rw [show (2 : Nat) = 1 + 1 from rfl, runFuel_jump_prefix h7 1]
  rw [show (1 : Nat) = 1 + 0 from rfl, runFuel_jump_prefix h8 0]

/-- **The parse's exit path when the sign is absent.**  From `if.else46.i.i` the
run leaves the parse, reads the byte after the cursor, finds no sign in the
switch and reaches `for.body87.i.i.preheader` in seven control steps. -/
theorem parse_exit_run_nosign {calls : Calls} {E0 : Env} {s0 : State}
    {b54 : BitVec 8} {seen : BitVec 32} {i n : BitVec 64} {b60 : BitVec 8} {a0 : Nat}
    (hpc : s0.pc = "if.else46.i.i") (_hpre : s0.pre = some "for.body.outer.i.i")
    (h54 : lookupName E0 "%54" = some (.int 8 b54))
    (hseen : lookupName E0 "%seen.0717.ph.i.i" = some (.int 32 seen))
    (hi : lookupName E0 "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName E0 "%n" = some (.int 64 n))
    (hp : lookupName E0 "%p" = some (.ptr a0))
    (hdot : evalICmp .eq b54 0x2e#8 = (0 : BitVec 1))
    (hseen0 : evalICmp .eq seen 0x00000000#32 = (0 : BitVec 1))
    (hread : evalICmp .ult (i + 0x0000000000000001#64) n = (1 : BitVec 1))
    (hi63 : (i + 0x0000000000000001#64).toNat < 2 ^ 63)
    (hb : readBytes s0.mem
      (a0 + ((i + 0x0000000000000001#64).signExtend 64).toNat) 1
      = some (natToBytes b60.toNat 1))
    (hpivot : evalICmp .slt b60 0x2d#8 = (0 : BitVec 1))
    (hleaf : evalICmp .eq b60 0x2d#8 = (0 : BitVec 1)) :
    runFuel calls 7 numFastBody (stateAt E0 s0) =
      runFuel calls 0 numFastBody
        (stateAt (end83Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) 0x1#1
          (i + 0x0000000000000001#64) n)
          { s0 with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  have h1 : step calls numFastBody (stateAt E0 s0) =
      .jump (stateAt (dotEnv E0 b54)
        { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" }) := by
    simpa only [stateAt, hpc] using dot_step_exit (s := s0) hpc h54 hdot
  have h2 : step calls numFastBody
      (stateAt (dotEnv E0 b54) { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" }) =
      .jump (stateAt (parseEndEnv (dotEnv E0 b54) seen)
        { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" }) := by
    simpa only [stateAt] using parseEnd_step_exponent (env := dotEnv E0 b54)
      (s := { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" })
      rfl (by band_lk) hseen0
  have h3 : step calls numFastBody
      (stateAt (parseEndEnv (dotEnv E0 b54) seen)
        { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" }) =
      .jump (stateAt (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
        { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" }) := by
    simpa only [stateAt] using then64_step_read
      (env := parseEndEnv (dotEnv E0 b54) seen)
      (s := { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" })
      rfl (by band_lk) (by band_lk) hread
  have h4 : step calls numFastBody
      (stateAt (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
        { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" }) =
      .jump (stateAt (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60)
        { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" }) := by
    simpa only [stateAt] using land68_step
      (env := then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
      (s := { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" })
      rfl (by band_lk) (by band_lk) hi63 hb
  have h5 : step calls numFastBody
      (stateAt (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60)
        { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" }) =
      .jump (stateAt (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60)
        { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" }) := by
    simpa only [stateAt] using pivot25_step_minus
      (env := land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
        (i + 0x0000000000000001#64) b60)
      (s := { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" })
      rfl (by band_lk) hpivot
  have h6 : step calls numFastBody
      (stateAt (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60)
        { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" }) =
      .jump (stateAt (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60)
        { s0 with pc := "if.end83.i.i", pre := some "LeafBlock23" }) := by
    simpa only [stateAt] using leaf23_step_skip
      (env := pivot25Env (land68Env
        (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
        (i + 0x0000000000000001#64) b60) b60)
      (s := { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" })
      rfl (by band_lk) hleaf
  have h7 : step calls numFastBody
      (stateAt (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60)
        { s0 with pc := "if.end83.i.i", pre := some "LeafBlock23" }) =
      .jump (stateAt (end83Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) 0x1#1
          (i + 0x0000000000000001#64) n)
        { s0 with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
    simpa only [stateAt] using end83_step_leaf23_copy
      (env := leaf23Env (pivot25Env
        (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60) b60) b60)
      (s := { s0 with pc := "if.end83.i.i", pre := some "LeafBlock23" })
      rfl rfl (by band_lk) (by band_lk) hread
  exact runFuel_chain7 h1 h2 h3 h4 h5 h6 h7

/-- **The parse's exit path when the sign is present.**  The same run, but the
switch takes the minus leaf and `if.then77.i.i` writes the sign's byte and adds
two: the run reaches the copy's entry in eight control steps. -/
theorem parse_exit_run_sign {calls : Calls} {E0 : Env} {s0 : State}
    {b54 : BitVec 8} {seen : BitVec 32} {i n : BitVec 64} {b60 : BitVec 8} {a0 : Nat}
    (hpc : s0.pc = "if.else46.i.i") (_hpre : s0.pre = some "for.body.outer.i.i")
    (h54 : lookupName E0 "%54" = some (.int 8 b54))
    (hseen : lookupName E0 "%seen.0717.ph.i.i" = some (.int 32 seen))
    (hi : lookupName E0 "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName E0 "%n" = some (.int 64 n))
    (hp : lookupName E0 "%p" = some (.ptr a0))
    (hdot : evalICmp .eq b54 0x2e#8 = (0 : BitVec 1))
    (hseen0 : evalICmp .eq seen 0x00000000#32 = (0 : BitVec 1))
    (hread : evalICmp .ult (i + 0x0000000000000001#64) n = (1 : BitVec 1))
    (hi63 : (i + 0x0000000000000001#64).toNat < 2 ^ 63)
    (hb : readBytes s0.mem
      (a0 + ((i + 0x0000000000000001#64).signExtend 64).toNat) 1
      = some (natToBytes b60.toNat 1))
    (hpivot : evalICmp .slt b60 0x2d#8 = (0 : BitVec 1))
    (hleaf : evalICmp .eq b60 0x2d#8 = (1 : BitVec 1))
    (hne : evalICmp .ne b60 0x2d#8 = (0 : BitVec 1))
    (hcopy : evalICmp .ult (i + 0x0000000000000002#64) n = (1 : BitVec 1)) :
    runFuel calls 8 numFastBody (stateAt E0 s0) =
      runFuel calls 0 numFastBody
        (stateAt (end83Env (then77Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) b60 i) 0x0#1
          (i + 0x0000000000000002#64) n)
          { s0 with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
  have h1 : step calls numFastBody (stateAt E0 s0) =
      .jump (stateAt (dotEnv E0 b54)
        { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" }) := by
    simpa only [stateAt, hpc] using dot_step_exit (s := s0) hpc h54 hdot
  have h2 : step calls numFastBody
      (stateAt (dotEnv E0 b54) { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" }) =
      .jump (stateAt (parseEndEnv (dotEnv E0 b54) seen)
        { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" }) := by
    simpa only [stateAt] using parseEnd_step_exponent (env := dotEnv E0 b54)
      (s := { s0 with pc := "for.end.i.i", pre := some "if.else46.i.i" })
      rfl (by band_lk) hseen0
  have h3 : step calls numFastBody
      (stateAt (parseEndEnv (dotEnv E0 b54) seen)
        { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" }) =
      .jump (stateAt (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
        { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" }) := by
    simpa only [stateAt] using then64_step_read
      (env := parseEndEnv (dotEnv E0 b54) seen)
      (s := { s0 with pc := "if.then64.i.i", pre := some "for.end.i.i" })
      rfl (by band_lk) (by band_lk) hread
  have h4 : step calls numFastBody
      (stateAt (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
        { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" }) =
      .jump (stateAt (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60)
        { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" }) := by
    simpa only [stateAt] using land68_step
      (env := then64Env (parseEndEnv (dotEnv E0 b54) seen) i n)
      (s := { s0 with pc := "land.lhs.true68.i.i", pre := some "if.then64.i.i" })
      rfl (by band_lk) (by band_lk) hi63 hb
  have h5 : step calls numFastBody
      (stateAt (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60)
        { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" }) =
      .jump (stateAt (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60)
        { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" }) := by
    simpa only [stateAt] using pivot25_step_minus
      (env := land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
        (i + 0x0000000000000001#64) b60)
      (s := { s0 with pc := "NodeBlock25", pre := some "land.lhs.true68.i.i" })
      rfl (by band_lk) hpivot
  have h6 : step calls numFastBody
      (stateAt (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60)
        { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" }) =
      .jump (stateAt (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60)
        { s0 with pc := "if.then77.i.i", pre := some "LeafBlock23" }) := by
    simpa only [stateAt] using leaf23_step_sign
      (env := pivot25Env (land68Env
        (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
        (i + 0x0000000000000001#64) b60) b60)
      (s := { s0 with pc := "LeafBlock23", pre := some "NodeBlock25" })
      rfl (by band_lk) hleaf
  have h7 : step calls numFastBody
      (stateAt (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60)
        { s0 with pc := "if.then77.i.i", pre := some "LeafBlock23" }) =
      .jump (stateAt (then77Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) b60 i)
        { s0 with pc := "if.end83.i.i", pre := some "if.then77.i.i" }) := by
    simpa only [stateAt] using then77_step
      (env := leaf23Env (pivot25Env
        (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60) b60) b60)
      (s := { s0 with pc := "if.then77.i.i", pre := some "LeafBlock23" })
      rfl (by band_lk) (by band_lk)
  have h8 : step calls numFastBody
      (stateAt (then77Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) b60 i)
        { s0 with pc := "if.end83.i.i", pre := some "if.then77.i.i" }) =
      .jump (stateAt (end83Env (then77Env (leaf23Env (pivot25Env
          (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
            (i + 0x0000000000000001#64) b60) b60) b60) b60 i) 0x0#1
          (i + 0x0000000000000002#64) n)
        { s0 with pc := "for.body87.i.i.preheader", pre := some "if.end83.i.i" }) := by
    simpa only [stateAt] using end83_step_then77_copy
      (env := then77Env (leaf23Env (pivot25Env
        (land68Env (then64Env (parseEndEnv (dotEnv E0 b54) seen) i n) a0
          (i + 0x0000000000000001#64) b60) b60) b60) b60 i)
      (s := { s0 with pc := "if.end83.i.i", pre := some "if.then77.i.i" })
      rfl rfl (by
        simp only [then77Env]
        rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self]
        exact congrArg (fun v => some (Value.int 1 v)) hne)
      (by band_lk) (by band_lk) hcopy
  exact runFuel_chain8 h1 h2 h3 h4 h5 h6 h7 h8

/-! ### The big multiply's layer

The staging's nonzero edge enters the chunk loop, which accumulates one digit per
chunk; its `cn < 19` test hands to the `10 ^ 19` nest, whose exits land at the
`stk_mul_u64` sites, and the rounding's own `while.end.i.i` merges them.  The
three blocks below are that layer's entry, its call's exit and its merge. -/

def body132Instrs : List Instr :=
  [Instr.binop "%mul133.i.i" (BinOp.mul) 64 (Operand.reg "%chunk.0738.i.i")
     (Operand.imm (Const.int 64 0x000000000000000a#64)),
   Instr.gep "%arrayidx134.i.i" (Ty.int 8) (Operand.reg "%dig.i.i")
     (Operand.reg "%j.0740.i.i"),
   Instr.load "%71" (Ty.int 8) (Operand.reg "%arrayidx134.i.i"),
   Instr.zext "%conv135.i.i" 8 64 (Operand.reg "%71"),
   Instr.binop "%add136.i.i" (BinOp.add) 64 (Operand.reg "%mul133.i.i")
     (Operand.reg "%conv135.i.i"),
   Instr.binop "%inc137.i.i" (BinOp.add) 32 (Operand.reg "%cn.0739.i.i")
     (Operand.imm (Const.int 32 0x00000001#32)),
   Instr.icmp "%cmp138.i.i" (IPred.eq) 32 (Operand.reg "%inc137.i.i")
     (Operand.imm (Const.int 32 0x00000013#32))]

/-- The chunk loop's four `phi`s, in the pin's order. -/
def body132Specs : List PhiSpec :=
  [{ dst := "%j.0740.i.i", ty := Ty.int 64,
     incoming := [("for.inc143.i.i", (Operand.reg "%inc144.i.i")),
                  ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))] },
   { dst := "%cn.0739.i.i", ty := Ty.int 32,
     incoming := [("for.inc143.i.i", (Operand.reg "%cn.1.i.i")),
                  ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] },
   { dst := "%chunk.0738.i.i", ty := Ty.int 64,
     incoming := [("for.inc143.i.i", (Operand.reg "%chunk.1.i.i")),
                  ("if.end126.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64)))] },
   { dst := "%70", ty := Ty.int 32,
     incoming := [("for.inc143.i.i", (Operand.reg "%78")),
                  ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] }]

def body132Block : List Instr := body132Specs.map PhiSpec.instr ++ body132Instrs

theorem body132_find :
    numFastBody.findBlock "for.body132.i.i" =
      some ⟨"for.body132.i.i", body132Block,
        Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩ := by
  simp only [body132Block, body132Instrs, body132Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_for_body132_i_i

/-- The chunk loop's environment: the four selected cells, the chunk's product,
the digit at the cursor and the `cn < 19` test. -/
def body132Env (env : Env) (j chunk : BitVec 64) (cn v70 : BitVec 32) (a0 : Nat)
    (b71 : BitVec 8) : Env :=
  ("%cmp138.i.i", .int 1 (evalICmp .eq (cn + 0x00000001#32) 0x00000013#32)) ::
  ("%inc137.i.i", .int 32 (cn + 0x00000001#32)) ::
  ("%add136.i.i", .int 64 (chunk * 0x000000000000000a#64
    + BitVec.ofNat 64 b71.toNat)) ::
  ("%conv135.i.i", .int 64 (BitVec.ofNat 64 b71.toNat)) ::
  ("%71", .int 8 b71) ::
  ("%arrayidx134.i.i", .ptr (a0 + (j.signExtend 64).toNat)) ::
  ("%mul133.i.i", .int 64 (chunk * 0x000000000000000a#64)) ::
  ("%70", .int 32 v70) ::
  ("%chunk.0738.i.i", .int 64 chunk) ::
  ("%cn.0739.i.i", .int 32 cn) ::
  ("%j.0740.i.i", .int 64 j) :: env

/-- The chunk loop's chain at the staging's edge: the four carried cells are the
staging's zeros, so the block's product is the digit at the array's start. -/
theorem body132_denote_staging {calls : Calls} {env : Env} {s : State}
    {a0 : Nat} {b71 : BitVec 8}
    (hpre : s.pre = some "if.end126.i.i")
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hb : readBytes s.mem a0 1 = some (natToBytes b71.toNat 1)) :
    denoteCode calls body132Block (stateAt env s) =
      some (stateAt (body132Env env 0 0 0 0 a0 b71) s) := by
  have hsel : PhiSelects (stateAt env s) "if.end126.i.i" body132Specs
      [("%j.0740.i.i", .int 64 0), ("%cn.0739.i.i", .int 32 0),
       ("%chunk.0738.i.i", .int 64 0), ("%70", .int 32 0)] := by
    simp only [body132Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 64 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 64 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.end126.i.i") (specs := body132Specs)
    (vs := [("%j.0740.i.i", .int 64 0), ("%cn.0739.i.i", .int 32 0),
      ("%chunk.0738.i.i", .int 64 0), ("%70", .int 32 0)]) (rest := body132Instrs)
    hpre hsel (by decide)
  unfold body132Block
  rw [h]
  unfold body132Instrs
  simp only [body132Env]
  have hpos : (((0 : BitVec 64)).signExtend 64).toNat < 2 ^ 63 := by decide
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The chunk loop's step into the `10 ^ 19` nest's test. -/
theorem body132_step_nest {calls : Calls} {env : Env} {s : State}
    {a0 : Nat} {b71 : BitVec 8}
    (hpc : s.pc = "for.body132.i.i")
    (hpre : s.pre = some "if.end126.i.i")
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hb : readBytes s.mem a0 1 = some (natToBytes b71.toNat 1))
    (hbit : evalICmp .eq (0x00000000#32 + 0x00000001#32) 0x00000013#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body132Env env 0 0 0 0 a0 b71)
        { s with pc := "if.then140.i.i", pre := some "for.body132.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body132Env env 0 0 0 0 a0 b71) s)
    (b := ⟨"for.body132.i.i", body132Block,
      Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body132_find
  · exact body132_denote_staging hpre hdig hb
  · rw [numFast_execTerm_condbr_one (s := stateAt (body132Env env 0 0 0 0 a0 b71) s)
      "%cmp138.i.i" "if.then140.i.i" "for.inc143.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The chunk loop's step into its latch. -/
theorem body132_step_latch {calls : Calls} {env : Env} {s : State}
    {a0 : Nat} {b71 : BitVec 8}
    (hpc : s.pc = "for.body132.i.i")
    (hpre : s.pre = some "if.end126.i.i")
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hb : readBytes s.mem a0 1 = some (natToBytes b71.toNat 1))
    (hbit : evalICmp .eq (0x00000000#32 + 0x00000001#32) 0x00000013#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body132Env env 0 0 0 0 a0 b71)
        { s with pc := "for.inc143.i.i", pre := some "for.body132.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body132Env env 0 0 0 0 a0 b71) s)
    (b := ⟨"for.body132.i.i", body132Block,
      Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body132_find
  · exact body132_denote_staging hpre hdig hb
  · rw [numFast_execTerm_condbr_zero (s := stateAt (body132Env env 0 0 0 0 a0 b71) s)
      "%cmp138.i.i" "if.then140.i.i" "for.inc143.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The `stk_mul_u64` site's exit: three counters and the index's test. -/
def stkExitInstrs : List Instr :=
  [Instr.binop "%sub158.i.i" (BinOp.add) 64 (Operand.reg "%k.0748.i.i")
     (Operand.imm (Const.int 64 0xffffffffffffffe5#64)),
   Instr.icmp "%cmp155.i.i" (IPred.sgt) 64 (Operand.reg "%k.0748.i.i")
     (Operand.imm (Const.int 64 0x0000000000000035#64))]

/-- The exit's `phi`s, in the pin's order. -/
def stkExitSpecs : List PhiSpec :=
  [{ dst := "%inc12.us.i.i744.i.i", ty := Ty.int 32,
     incoming := [("while.body.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                  ("while.cond.preheader.i.i.i.i", (Operand.reg "%inc12.us.i.i745747.i.i")),
                  ("while.body.us.i.i.i.i", (Operand.reg "%inc12.us.i.i.i.i"))] }]

def stkExitBlock : List Instr := stkExitSpecs.map PhiSpec.instr ++ stkExitInstrs

theorem stkExit_find :
    numFastBody.findBlock "stk_mul_u64.exit.i.i" =
      some ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
        Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩ := by
  simp only [stkExitBlock, stkExitInstrs, stkExitSpecs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_stk_mul_u64_exit_i_i

/-- The exit's environment: the carried counter, the index's clamp and its test. -/
def stkExitEnv (env : Env) (inc12 : BitVec 32) (k : BitVec 64) : Env :=
  ("%cmp155.i.i", .int 1 (evalICmp .sgt k 0x0000000000000035#64)) ::
  ("%sub158.i.i", .int 64 (k + 0xffffffffffffffe5#64)) ::
  ("%inc12.us.i.i744.i.i", .int 32 inc12) :: env

/-- The exit's chain at the chunk loop's back edge. -/
theorem stkExit_denote_body {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpre : s.pre = some "while.body.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k)) :
    denoteCode calls stkExitBlock (stateAt env s) =
      some (stateAt (stkExitEnv env inc12 k) s) := by
  have hsel : PhiSelects (stateAt env s) "while.body.i.i" stkExitSpecs
      [("%inc12.us.i.i744.i.i", .int 32 inc12)] := by
    simp only [stkExitSpecs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc12.us.i.i745747.i.i" (.int 32 inc12) hinc
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "while.body.i.i") (specs := stkExitSpecs)
    (vs := [("%inc12.us.i.i744.i.i", .int 32 inc12)]) (rest := stkExitInstrs)
    hpre hsel (by decide)
  unfold stkExitBlock
  rw [h]
  unfold stkExitInstrs
  simp only [stkExitEnv]
  inner_step
  inner_step
  block_close

/-- The exit's step back into the chunk loop. -/
theorem stkExit_step_body {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.body.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.body.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_body hpre hinc hk
  · rw [numFast_execTerm_condbr_one (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step into the merge. -/
theorem stkExit_step_end {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.body.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.end.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_body hpre hinc hk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The merge: the counter's store, the two tests and their disjunction. -/
def whileEndInstrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i744.i.i") (Operand.reg "%n.i539.i.i"),
   Instr.icmp "%tobool159.not.i.i" (IPred.ne) 64 (Operand.reg "%sub158.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64)),
   Instr.icmp "%cmp28.i.i541.i.i" (IPred.sgt) 32 (Operand.reg "%inc12.us.i.i744.i.i")
     (Operand.imm (Const.int 32 0x00000000#32)),
   Instr.select "%or.cond864.i.i" (Ty.int 1) (Operand.reg "%tobool159.not.i.i")
     (Operand.reg "%cmp28.i.i541.i.i") (Operand.imm (Const.int 1 0x0#1))]

theorem whileEnd_find :
    numFastBody.findBlock "while.end.i.i" =
      some ⟨"while.end.i.i", whileEndInstrs,
        Term.condbr (Operand.reg "%or.cond864.i.i") "for.body.lr.ph.i.i542.i.i"
          "if.end198.i.i"⟩ := by
  simpa only [whileEndInstrs] using numFast_findBlock_while_end_i_i

/-- The merge's environment: the two tests and their disjunction. -/
def whileEndEnv (env : Env) (inc12 : BitVec 32) (d : BitVec 64) : Env :=
  ("%or.cond864.i.i", .int 1
    (if evalICmp .ne d 0x0000000000000000#64 = 1 then evalICmp .sgt inc12 0x00000000#32
      else 0x0#1)) ::
  ("%cmp28.i.i541.i.i", .int 1 (evalICmp .sgt inc12 0x00000000#32)) ::
  ("%tobool159.not.i.i", .int 1 (evalICmp .ne d 0x0000000000000000#64)) :: env

/-- The merge's state: the counter's store at `%n.i539.i.i`. -/
def whileEndState (env : Env) (inc12 : BitVec 32) (d : BitVec 64) (r : Nat) (s : State) :
    State :=
  { stateAt (whileEndEnv env inc12 d) s with
      mem := writeBytes s.mem r (natToBytes inc12.toNat 4) }

/-- The merge's chain at its pin. -/
theorem whileEnd_denote {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {d : BitVec 64} {r : Nat}
    (hn : lookupName env "%n.i539.i.i" = some (.ptr r))
    (hinc : lookupName env "%inc12.us.i.i744.i.i" = some (.int 32 inc12))
    (hd : lookupName env "%sub158.i.i" = some (.int 64 d)) :
    denoteCode calls whileEndInstrs (stateAt env s) =
      some (whileEndState env inc12 d r s) := by
  unfold whileEndInstrs
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The merge's step into the rounding's chunk loop. -/
theorem whileEnd_step_chunks {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {d : BitVec 64} {r : Nat}
    (hpc : s.pc = "while.end.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr r))
    (hinc : lookupName env "%inc12.us.i.i744.i.i" = some (.int 32 inc12))
    (hd : lookupName env "%sub158.i.i" = some (.int 64 d))
    (hbit : (if evalICmp .ne d 0x0000000000000000#64 = 1
      then evalICmp .sgt inc12 0x00000000#32 else 0x0#1) = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { whileEndState env inc12 d r s with
        pc := "for.body.lr.ph.i.i542.i.i", pre := some "while.end.i.i" } := by
  refine numFast_step_at (s' := whileEndState env inc12 d r s)
    (b := ⟨"while.end.i.i", whileEndInstrs,
      Term.condbr (Operand.reg "%or.cond864.i.i") "for.body.lr.ph.i.i542.i.i"
        "if.end198.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using whileEnd_find
  · exact whileEnd_denote hn hinc hd
  · rw [numFast_execTerm_condbr_one (s := whileEndState env inc12 d r s)
      "%or.cond864.i.i" "for.body.lr.ph.i.i542.i.i" "if.end198.i.i" ?_ hbit]
    · simp only [whileEndState, whileEndEnv, stateAt, hpc]
    · simp only [whileEndState, whileEndEnv, stateAt]
      exact lookupName_cons_self ..

/-- The merge's step to the ladder's head. -/
theorem whileEnd_step_ladder {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {d : BitVec 64} {r : Nat}
    (hpc : s.pc = "while.end.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr r))
    (hinc : lookupName env "%inc12.us.i.i744.i.i" = some (.int 32 inc12))
    (hd : lookupName env "%sub158.i.i" = some (.int 64 d))
    (hbit : (if evalICmp .ne d 0x0000000000000000#64 = 1
      then evalICmp .sgt inc12 0x00000000#32 else 0x0#1) = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { whileEndState env inc12 d r s with
        pc := "if.end198.i.i", pre := some "while.end.i.i" } := by
  refine numFast_step_at (s' := whileEndState env inc12 d r s)
    (b := ⟨"while.end.i.i", whileEndInstrs,
      Term.condbr (Operand.reg "%or.cond864.i.i") "for.body.lr.ph.i.i542.i.i"
        "if.end198.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using whileEnd_find
  · exact whileEnd_denote hn hinc hd
  · rw [numFast_execTerm_condbr_zero (s := whileEndState env inc12 d r s)
      "%or.cond864.i.i" "for.body.lr.ph.i.i542.i.i" "if.end198.i.i" ?_ hbit]
    · simp only [whileEndState, whileEndEnv, stateAt, hpc]
    · simp only [whileEndState, whileEndEnv, stateAt]
      exact lookupName_cons_self ..

/-! ### The edges the composition reads that the block map did not yet state

`for.end100.i.i`'s accumulator arrives from three blocks: `if.end83.i.i`'s zero
(stated above), the copy's unrolled exit `%e.1.i.i.lcssa.ph`, and its peeled
residue `%e.1.i.i.epil`.  `if.end104.i.i` merges the counters from the copy's
exit and from the parse's counted exit `for.end.thread.i.i`, whose edge carries
the exponent from the accumulator's place as the zero.  The big multiply's chunk
loop re-enters its head from `for.inc143.i.i`, and `stk_mul_u64.exit.i.i` merges
its counter from the three `stk_mul_u64` sites.  Each statement below is the
block's already-proved chain at the predecessor the edge names. -/

/-- The copy exit's chain at the unrolled exit. -/
theorem end100_denote_loopexit {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {e : BitVec 64}
    (hpre : s.pre = some "for.end100.i.i.loopexit.unr-lcssa")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign))
    (hl : lookupName env "%e.1.i.i.lcssa.ph" = some (.int 64 e)) :
    denoteCode calls end100Instrs (stateAt env s) =
      some (stateAt (end100Env env esign e) s) := by
  have hsel : PhiSelects (stateAt env s) "for.end100.i.i.loopexit.unr-lcssa"
      end100Specs [("%e.0.lcssa.i.i", .int 64 e)] := by
    simp only [end100Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%e.1.i.i.lcssa.ph" (.int 64 e) hl
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.end100.i.i.loopexit.unr-lcssa") (specs := end100Specs)
    (vs := [("%e.0.lcssa.i.i", .int 64 e)]) (rest := end100Rest) hpre hsel (by decide)
  unfold end100Instrs
  rw [h]
  unfold end100Rest
  simp only [end100Env]
  inner_step
  inner_step
  block_close

/-- The copy exit's step into the clamps at the unrolled exit. -/
theorem end100_step_loopexit {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {e : BitVec 64}
    (hpc : s.pc = "for.end100.i.i")
    (hpre : s.pre = some "for.end100.i.i.loopexit.unr-lcssa")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign))
    (hl : lookupName env "%e.1.i.i.lcssa.ph" = some (.int 64 e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end100Env env esign e)
        { s with pc := "if.end104.i.i", pre := some "for.end100.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end100Env env esign e) s)
    (b := ⟨"for.end100.i.i", end100Instrs, Term.br "if.end104.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end100_find
  · exact end100_denote_loopexit hpre he hl
  · simp only [execTerm, stateAt, hpc]

/-- The copy exit's chain at the peeled residue. -/
theorem end100_denote_epil {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {e : BitVec 64}
    (hpre : s.pre = some "for.inc98.i.i.epil")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign))
    (hl : lookupName env "%e.1.i.i.epil" = some (.int 64 e)) :
    denoteCode calls end100Instrs (stateAt env s) =
      some (stateAt (end100Env env esign e) s) := by
  have hsel : PhiSelects (stateAt env s) "for.inc98.i.i.epil"
      end100Specs [("%e.0.lcssa.i.i", .int 64 e)] := by
    simp only [end100Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%e.1.i.i.epil" (.int 64 e) hl
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.inc98.i.i.epil") (specs := end100Specs)
    (vs := [("%e.0.lcssa.i.i", .int 64 e)]) (rest := end100Rest) hpre hsel (by decide)
  unfold end100Instrs
  rw [h]
  unfold end100Rest
  simp only [end100Env]
  inner_step
  inner_step
  block_close

/-- The copy exit's step into the clamps at the peeled residue. -/
theorem end100_step_epil {calls : Calls} {env : Env} {s : State}
    {esign : BitVec 1} {e : BitVec 64}
    (hpc : s.pc = "for.end100.i.i")
    (hpre : s.pre = some "for.inc98.i.i.epil")
    (he : lookupName env "%esign.0.i.i" = some (.int 1 esign))
    (hl : lookupName env "%e.1.i.i.epil" = some (.int 64 e)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end100Env env esign e)
        { s with pc := "if.end104.i.i", pre := some "for.end100.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end100Env env esign e) s)
    (b := ⟨"for.end100.i.i", end100Instrs, Term.br "if.end104.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end100_find
  · exact end100_denote_epil hpre he hl
  · simp only [execTerm, stateAt, hpc]

/-- The clamp head's chain at the parse's counted exit. -/
theorem end104_denote_thread {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R : BitVec 64}
    (hpre : s.pre = some "for.end.thread.i.i")
    (hlead : lookupName env "%lead.0721.i287.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.4.ph.i.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.4.ph.i.i" = some (.int 64 topn))
    (htop : lookupName env "%top.4.ph.i.i" = some (.int 64 top))
    (hF : lookupName env "%F.3.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.2.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.4.ph.i.i" = some (.int 64 R)) :
    denoteCode calls end104Instrs (stateAt env s) =
      some (stateAt (end104Env env lead sticky topn top F T R 0) s) := by
  have hsel : PhiSelects (stateAt env s) "for.end.thread.i.i" end104Specs
      [("%lead.0721.i286.i", .int 64 lead), ("%sticky.0714.i.i", .int 32 sticky),
       ("%topn.0711.i.i", .int 64 topn), ("%top.0709.i.i", .int 64 top),
       ("%F.0705.i.i", .int 64 F), ("%T.0703.i.i", .int 64 T),
       ("%R.0701.i.i", .int 64 R), ("%exp10.0.i.i", .int 64 0)] := by
    simp only [end104Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i287.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.4.ph.i.i" (.int 32 sticky) hsticky
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.4.ph.i.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.4.ph.i.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.3.ph.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.2.ph.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%R.4.ph.i.i" (.int 64 R) hR
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 64 _
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.end.thread.i.i") (specs := end104Specs)
    (vs := [("%lead.0721.i286.i", .int 64 lead), ("%sticky.0714.i.i", .int 32 sticky),
      ("%topn.0711.i.i", .int 64 topn), ("%top.0709.i.i", .int 64 top),
      ("%F.0705.i.i", .int 64 F), ("%T.0703.i.i", .int 64 T),
      ("%R.0701.i.i", .int 64 R), ("%exp10.0.i.i", .int 64 0)])
    (rest := end104Rest) hpre hsel (by decide)
  unfold end104Instrs
  rw [h]
  unfold end104Rest
  simp only [end104Env]
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The clamp head's step to the infinity clamp at the parse's counted exit. -/
theorem end104_step_thread_over {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R : BitVec 64}
    (hpc : s.pc = "if.end104.i.i")
    (hpre : s.pre = some "for.end.thread.i.i")
    (hlead : lookupName env "%lead.0721.i287.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.4.ph.i.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.4.ph.i.i" = some (.int 64 topn))
    (htop : lookupName env "%top.4.ph.i.i" = some (.int 64 top))
    (hF : lookupName env "%F.3.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.2.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.4.ph.i.i" = some (.int 64 R))
    (hbit : evalICmp .sgt
      ((R + 0xffffffffffffffff#64)
        + ((T - (lead + R)) + (0x0000000000000000#64 - F)))
      0x0000000000000134#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end104Env env lead sticky topn top F T R 0)
        { s with pc := "if.then113.i.i", pre := some "if.end104.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (end104Env env lead sticky topn top F T R 0) s)
    (b := ⟨"if.end104.i.i", end104Instrs,
      Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end104_find
  · exact end104_denote_thread hpre hlead hsticky htopn htop hF hT hR
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (end104Env env lead sticky topn top F T R 0) s)
      "%cmp111.i.i" "if.then113.i.i" "if.end120.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The clamp head's step to the underflow test at the parse's counted exit. -/
theorem end104_step_thread_under {calls : Calls} {env : Env} {s : State}
    {lead : BitVec 64} {sticky : BitVec 32} {topn top F T R : BitVec 64}
    (hpc : s.pc = "if.end104.i.i")
    (hpre : s.pre = some "for.end.thread.i.i")
    (hlead : lookupName env "%lead.0721.i287.i" = some (.int 64 lead))
    (hsticky : lookupName env "%sticky.4.ph.i.i" = some (.int 32 sticky))
    (htopn : lookupName env "%topn.4.ph.i.i" = some (.int 64 topn))
    (htop : lookupName env "%top.4.ph.i.i" = some (.int 64 top))
    (hF : lookupName env "%F.3.ph.i.i" = some (.int 64 F))
    (hT : lookupName env "%T.2.ph.i.i" = some (.int 64 T))
    (hR : lookupName env "%R.4.ph.i.i" = some (.int 64 R))
    (hbit : evalICmp .sgt
      ((R + 0xffffffffffffffff#64)
        + ((T - (lead + R)) + (0x0000000000000000#64 - F)))
      0x0000000000000134#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end104Env env lead sticky topn top F T R 0)
        { s with pc := "if.end120.i.i", pre := some "if.end104.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (end104Env env lead sticky topn top F T R 0) s)
    (b := ⟨"if.end104.i.i", end104Instrs,
      Term.condbr (Operand.reg "%cmp111.i.i") "if.then113.i.i" "if.end120.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end104_find
  · exact end104_denote_thread hpre hlead hsticky htopn htop hF hT hR
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (end104Env env lead sticky topn top F T R 0) s)
      "%cmp111.i.i" "if.then113.i.i" "if.end120.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The chunk loop's chain on its latch's back edge: the four carried cells are
the latch's, so the block's product is the latch's chunk times ten plus the
digit at the index it names. -/
theorem body132_denote_back {calls : Calls} {env : Env} {s : State}
    {j chunk : BitVec 64} {cn v70 : BitVec 32}
    {a0 : Nat} {b71 : BitVec 8}
    (hpre : s.pre = some "for.inc143.i.i")
    (hj : lookupName env "%inc144.i.i" = some (.int 64 j))
    (hcn : lookupName env "%cn.1.i.i" = some (.int 32 cn))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk))
    (h70 : lookupName env "%78" = some (.int 32 v70))
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hpos : (j.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (a0 + (j.signExtend 64).toNat) 1
      = some (natToBytes b71.toNat 1)) :
    denoteCode calls body132Block (stateAt env s) =
      some (stateAt (body132Env env j chunk cn v70 a0 b71) s) := by
  have hsel : PhiSelects (stateAt env s) "for.inc143.i.i" body132Specs
      [("%j.0740.i.i", .int 64 j), ("%cn.0739.i.i", .int 32 cn),
       ("%chunk.0738.i.i", .int 64 chunk), ("%70", .int 32 v70)] := by
    simp only [body132Specs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc144.i.i" (.int 64 j) hj
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%cn.1.i.i" (.int 32 cn) hcn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%chunk.1.i.i" (.int 64 chunk) hchunk
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%78" (.int 32 v70) h70
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.inc143.i.i") (specs := body132Specs)
    (vs := [("%j.0740.i.i", .int 64 j), ("%cn.0739.i.i", .int 32 cn),
      ("%chunk.0738.i.i", .int 64 chunk), ("%70", .int 32 v70)]) (rest := body132Instrs)
    hpre hsel (by decide)
  unfold body132Block
  rw [h]
  unfold body132Instrs
  simp only [body132Env]
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The chunk loop's step into the `10 ^ 19` nest's test on the back edge. -/
theorem body132_step_back_nest {calls : Calls} {env : Env} {s : State}
    {j chunk : BitVec 64} {cn v70 : BitVec 32}
    {a0 : Nat} {b71 : BitVec 8}
    (hpc : s.pc = "for.body132.i.i")
    (hpre : s.pre = some "for.inc143.i.i")
    (hj : lookupName env "%inc144.i.i" = some (.int 64 j))
    (hcn : lookupName env "%cn.1.i.i" = some (.int 32 cn))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk))
    (h70 : lookupName env "%78" = some (.int 32 v70))
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hpos : (j.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (a0 + (j.signExtend 64).toNat) 1
      = some (natToBytes b71.toNat 1))
    (hbit : evalICmp .eq (cn + 0x00000001#32) 0x00000013#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body132Env env j chunk cn v70 a0 b71)
        { s with pc := "if.then140.i.i", pre := some "for.body132.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body132Env env j chunk cn v70 a0 b71) s)
    (b := ⟨"for.body132.i.i", body132Block,
      Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body132_find
  · exact body132_denote_back hpre hj hcn hchunk h70 hdig hpos hb
  · rw [numFast_execTerm_condbr_one (s := stateAt (body132Env env j chunk cn v70 a0 b71) s)
      "%cmp138.i.i" "if.then140.i.i" "for.inc143.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The chunk loop's step into its latch on the back edge. -/
theorem body132_step_back_latch {calls : Calls} {env : Env} {s : State}
    {j chunk : BitVec 64} {cn v70 : BitVec 32}
    {a0 : Nat} {b71 : BitVec 8}
    (hpc : s.pc = "for.body132.i.i")
    (hpre : s.pre = some "for.inc143.i.i")
    (hj : lookupName env "%inc144.i.i" = some (.int 64 j))
    (hcn : lookupName env "%cn.1.i.i" = some (.int 32 cn))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk))
    (h70 : lookupName env "%78" = some (.int 32 v70))
    (hdig : lookupName env "%dig.i.i" = some (.ptr a0))
    (hpos : (j.signExtend 64).toNat < 2 ^ 63)
    (hb : readBytes s.mem (a0 + (j.signExtend 64).toNat) 1
      = some (natToBytes b71.toNat 1))
    (hbit : evalICmp .eq (cn + 0x00000001#32) 0x00000013#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body132Env env j chunk cn v70 a0 b71)
        { s with pc := "for.inc143.i.i", pre := some "for.body132.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body132Env env j chunk cn v70 a0 b71) s)
    (b := ⟨"for.body132.i.i", body132Block,
      Term.condbr (Operand.reg "%cmp138.i.i") "if.then140.i.i" "for.inc143.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body132_find
  · exact body132_denote_back hpre hj hcn hchunk h70 hdig hpos hb
  · rw [numFast_execTerm_condbr_zero (s := stateAt (body132Env env j chunk cn v70 a0 b71) s)
      "%cmp138.i.i" "if.then140.i.i" "for.inc143.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The `stk_mul_u64` exit's chain at the `while.cond` site. -/
theorem stkExit_denote_cond {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpre : s.pre = some "while.cond.preheader.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k)) :
    denoteCode calls stkExitBlock (stateAt env s) =
      some (stateAt (stkExitEnv env inc12 k) s) := by
  have hsel : PhiSelects (stateAt env s) "while.cond.preheader.i.i.i.i" stkExitSpecs
      [("%inc12.us.i.i744.i.i", .int 32 inc12)] := by
    simp only [stkExitSpecs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc12.us.i.i745747.i.i" (.int 32 inc12) hinc
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "while.cond.preheader.i.i.i.i") (specs := stkExitSpecs)
    (vs := [("%inc12.us.i.i744.i.i", .int 32 inc12)]) (rest := stkExitInstrs)
    hpre hsel (by decide)
  unfold stkExitBlock
  rw [h]
  unfold stkExitInstrs
  simp only [stkExitEnv]
  inner_step
  inner_step
  block_close

/-- The `stk_mul_u64` exit's chain at the `while.body.us` site. -/
theorem stkExit_denote_us {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpre : s.pre = some "while.body.us.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k)) :
    denoteCode calls stkExitBlock (stateAt env s) =
      some (stateAt (stkExitEnv env inc12 k) s) := by
  have hsel : PhiSelects (stateAt env s) "while.body.us.i.i.i.i" stkExitSpecs
      [("%inc12.us.i.i744.i.i", .int 32 inc12)] := by
    simp only [stkExitSpecs]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc12.us.i.i.i.i" (.int 32 inc12) hinc
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "while.body.us.i.i.i.i") (specs := stkExitSpecs)
    (vs := [("%inc12.us.i.i744.i.i", .int 32 inc12)]) (rest := stkExitInstrs)
    hpre hsel (by decide)
  unfold stkExitBlock
  rw [h]
  unfold stkExitInstrs
  simp only [stkExitEnv]
  inner_step
  inner_step
  block_close

/-- The exit's step back into the chunk loop at the `while.cond` site. -/
theorem stkExit_step_cond_body {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.body.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_cond hpre hinc hk
  · rw [numFast_execTerm_condbr_one (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step into the merge at the `while.cond` site. -/
theorem stkExit_step_cond_end {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.cond.preheader.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i745747.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.end.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_cond hpre hinc hk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step back into the chunk loop at the `while.body.us` site. -/
theorem stkExit_step_us_body {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.body.us.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.body.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_us hpre hinc hk
  · rw [numFast_execTerm_condbr_one (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The exit's step into the merge at the `while.body.us` site. -/
theorem stkExit_step_us_end {calls : Calls} {env : Env} {s : State}
    {inc12 : BitVec 32} {k : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit.i.i")
    (hpre : s.pre = some "while.body.us.i.i.i.i")
    (hinc : lookupName env "%inc12.us.i.i.i.i" = some (.int 32 inc12))
    (hk : lookupName env "%k.0748.i.i" = some (.int 64 k))
    (hbit : evalICmp .sgt k 0x0000000000000035#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (stkExitEnv env inc12 k)
        { s with pc := "while.end.i.i", pre := some "stk_mul_u64.exit.i.i" }) := by
  refine numFast_step_at (s' := stateAt (stkExitEnv env inc12 k) s)
    (b := ⟨"stk_mul_u64.exit.i.i", stkExitBlock,
      Term.condbr (Operand.reg "%cmp155.i.i") "while.body.i.i" "while.end.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using stkExit_find
  · exact stkExit_denote_us hpre hinc hk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (stkExitEnv env inc12 k) s)
      "%cmp155.i.i" "while.body.i.i" "while.end.i.i" (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ### The parse head's phi block, and its thread edge

`for.body.outer.i.outer.i` is the parse head's phi block: ten carried cells
selected from `if.then143.i` or the outer latch `for.inc.i.i`, and a branch to the
head.  The head reads the block's cells on that edge, so the outer loop's back
edge is this block's own step.  The head's other edge,
`if.else46.i.thread.i`, is the inner loop's dot exit: the head's `phi`s select the
thread's cells and the two constants (`in_frac` set, `seen` cleared), so the head
has a chain at that predecessor too. -/

/-- The head's values on the parse phi block's two edges. -/
def outerPhiValues (i R T F lead top topn : BitVec 64) (inFrac seen sticky : BitVec 32) :
    List (String × Value) :=
  [("%i.1725.ph.i.ph.i", .int 64 i), ("%R.0724.ph.i.ph.i", .int 64 R),
   ("%T.0723.ph.i.ph.i", .int 64 T), ("%F.0722.ph.i.ph.i", .int 64 F),
   ("%lead.0721.ph.i.ph.i", .int 64 lead), ("%top.0720.ph.i.ph.i", .int 64 top),
   ("%topn.0719.ph.i.ph.i", .int 64 topn), ("%in_frac.0718.ph.i.ph.i", .int 32 inFrac),
   ("%seen.0717.ph.i.ph.i", .int 32 seen), ("%sticky.0716.ph.i.ph.i", .int 32 sticky)]

/-- The parse phi block's ten `phi`s, in the pin's order. -/
def outerPhiSpecs : List PhiSpec :=
  [{ dst := "%i.1725.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.reg "%i.0.i")),
                  ("for.inc.i.i", (Operand.reg "%inc57.i.i"))] },
   { dst := "%R.0724.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%R.4.ph.i.i"))] },
   { dst := "%T.0723.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%T.2.ph.i.i"))] },
   { dst := "%F.0722.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%F.3.ph.i.i"))] },
   { dst := "%lead.0721.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%lead.0721.i287.i"))] },
   { dst := "%top.0720.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%top.4.ph.i.i"))] },
   { dst := "%topn.0719.ph.i.ph.i", ty := Ty.int 64,
     incoming := [("if.then143.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.inc.i.i", (Operand.reg "%topn.4.ph.i.i"))] },
   { dst := "%in_frac.0718.ph.i.ph.i", ty := Ty.int 32,
     incoming := [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                  ("for.inc.i.i", (Operand.reg "%in_frac.2.ph.i.i"))] },
   { dst := "%seen.0717.ph.i.ph.i", ty := Ty.int 32,
     incoming := [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                  ("for.inc.i.i", (Operand.reg "%seen.4.ph.i.i"))] },
   { dst := "%sticky.0716.ph.i.ph.i", ty := Ty.int 32,
     incoming := [("if.then143.i", (Operand.imm (Const.int 32 0x00000000#32))),
                  ("for.inc.i.i", (Operand.reg "%sticky.4.ph.i.i"))] }]

/-- The phi block, from its pin. -/
def outerPhiBlock : List Instr := outerPhiSpecs.map PhiSpec.instr

theorem outerPhi_find :
    numFastBody.findBlock "for.body.outer.i.outer.i" =
      some ⟨"for.body.outer.i.outer.i", outerPhiBlock, Term.br "for.body.outer.i.i"⟩ := by
  simp only [outerPhiBlock, outerPhiSpecs, PhiSpec.instr,
    List.map_cons, List.map_nil]
  exact numFast_findBlock_for_body_outer_i_outer_i

/-- The phi block's environment: the ten cells it selects. -/
def outerPhiEnv (env : Env) (i R T F lead top topn : BitVec 64)
    (inFrac seen sticky : BitVec 32) : Env :=
  runCells (outerPhiValues i R T F lead top topn inFrac seen sticky) env

/-- The phi block's chain on the outer latch's back edge. -/
theorem outerPhi_denote_back {calls : Calls} {env : Env} {s : State}
    {i R T F lead top topn : BitVec 64} {inFrac seen sticky : BitVec 32}
    (hpre : s.pre = some "for.inc.i.i")
    (hi : lookupName env "%inc57.i.i" = some (.int 64 i))
    (hR : lookupName env "%R.4.ph.i.i" = some (.int 64 R))
    (hT : lookupName env "%T.2.ph.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.3.ph.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i287.i" = some (.int 64 lead))
    (htop : lookupName env "%top.4.ph.i.i" = some (.int 64 top))
    (htopn : lookupName env "%topn.4.ph.i.i" = some (.int 64 topn))
    (hin : lookupName env "%in_frac.2.ph.i.i" = some (.int 32 inFrac))
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen))
    (hsticky : lookupName env "%sticky.4.ph.i.i" = some (.int 32 sticky)) :
    denoteCode calls outerPhiBlock (stateAt env s) =
      some (stateAt (outerPhiEnv env i R T F lead top topn inFrac seen sticky) s) := by
  have hsel : PhiSelects (stateAt env s) "for.inc.i.i" outerPhiSpecs
      (outerPhiValues i R T F lead top topn inFrac seen sticky) := by
    simp only [outerPhiSpecs, outerPhiValues]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc57.i.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%R.4.ph.i.i" (.int 64 R) hR
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.2.ph.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.3.ph.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i287.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%top.4.ph.i.i" (.int 64 top) htop
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%topn.4.ph.i.i" (.int 64 topn) htopn
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%in_frac.2.ph.i.i" (.int 32 inFrac) hin
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%seen.4.ph.i.i" (.int 32 seen) hseen
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%sticky.4.ph.i.i" (.int 32 sticky) hsticky
    exact PhiSelects.nil
  rw [outerPhiBlock]
  rw [show List.map PhiSpec.instr outerPhiSpecs
      = List.map PhiSpec.instr outerPhiSpecs ++ [] from (List.append_nil _).symm]
  rw [denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "for.inc.i.i") (specs := outerPhiSpecs)
    (vs := outerPhiValues i R T F lead top topn inFrac seen sticky) (rest := [])
    hpre hsel (by decide)]
  simp only [denoteCode_nil, outerPhiEnv]

/-- The phi block's step from the outer latch into the head. -/
theorem outerPhi_step_back {calls : Calls} {env : Env} {s : State}
    {i R T F lead top topn : BitVec 64} {inFrac seen sticky : BitVec 32}
    (hpc : s.pc = "for.body.outer.i.outer.i")
    (hpre : s.pre = some "for.inc.i.i")
    (hi : lookupName env "%inc57.i.i" = some (.int 64 i))
    (hR : lookupName env "%R.4.ph.i.i" = some (.int 64 R))
    (hT : lookupName env "%T.2.ph.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.3.ph.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i287.i" = some (.int 64 lead))
    (htop : lookupName env "%top.4.ph.i.i" = some (.int 64 top))
    (htopn : lookupName env "%topn.4.ph.i.i" = some (.int 64 topn))
    (hin : lookupName env "%in_frac.2.ph.i.i" = some (.int 32 inFrac))
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen))
    (hsticky : lookupName env "%sticky.4.ph.i.i" = some (.int 32 sticky)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (outerPhiEnv env i R T F lead top topn inFrac seen sticky)
        { s with pc := "for.body.outer.i.i", pre := some "for.body.outer.i.outer.i" }) := by
  refine numFast_step_at
    (s' := stateAt (outerPhiEnv env i R T F lead top topn inFrac seen sticky) s)
    (b := ⟨"for.body.outer.i.outer.i", outerPhiBlock, Term.br "for.body.outer.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using outerPhi_find
  · exact outerPhi_denote_back hpre hi hR hT hF hlead htop htopn hin hseen hsticky
  · simp only [execTerm, stateAt, hpc]

/-- The head's chain on the inner loop's dot edge: the `phi`s select the thread's
cells, with `in_frac` set and `seen` cleared. -/
theorem outer_denote_thread {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpre : s.pre = some "if.else46.i.thread.i")
    (hi : lookupName env "%inc57.i344.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1)) :
    denoteCode calls outerInstrs (stateAt env s) =
      some (stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32
        (a + i.toNat) b) s) := by
  have hsel : PhiSelects (stateAt env s) "if.else46.i.thread.i" outerSpecs
      (outerValues i T F lead 0x00000001#32 0x00000000#32) := by
    simp only [outerSpecs, outerValues]
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%inc57.i344.i" (.int 64 i) hi
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%T.0723.i.i" (.int 64 T) hT
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%F.0722.i.i" (.int 64 F) hF
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_reg_of env s "%lead.0721.i.i" (.int 64 lead) hlead
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    constructor
    · simp [phiIncoming]; rfl
    · exact evalOperand_lit_of _ 32 _
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := "if.else46.i.thread.i") (specs := outerSpecs)
    (vs := outerValues i T F lead 0x00000001#32 0x00000000#32) (rest := outerRest)
    hpre hsel (by decide)
  unfold outerInstrs
  rw [h]
  unfold outerRest
  simp only [outerEnv]
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  inner_step
  block_close
  all_goals (first
    | (simpa only [signExtend64_toNat] using hb)
    | (simpa only [signExtend64_toNat] using hi63)
    | (simp only [outerValues, runCells, denoteRun, State.bindAll, signExtend64_toNat]))

/-- The head's step onto its digit edge, on the inner loop's dot edge. -/
theorem outer_step_thread_digit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.outer.i.i")
    (hpre : s.pre = some "if.else46.i.thread.i")
    (hi : lookupName env "%inc57.i344.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32
          (a + i.toNat) b)
        { s with pc := "if.then13.i.peel.i", pre := some "for.body.outer.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32 (a + i.toNat) b) s)
    (b := ⟨"for.body.outer.i.i", outerInstrs,
      Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using outer_find
  · simpa only [stateAt] using outer_denote_thread hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_one
      (s := stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32
        (a + i.toNat) b) s) "%or.cond.i.peel.i" "if.then13.i.peel.i" "if.else46.i.i"
      (lookupName_cons_self "%or.cond.i.peel.i"
        (Value.int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) _) hbit]
    simp only [stateAt, hpc]

/-- The head's step onto its non-digit edge, on the inner loop's dot edge. -/
theorem outer_step_thread_nondigit {calls : Calls} {env : Env} {s : State}
    {i T F lead : BitVec 64} {b : BitVec 8} {a : Nat}
    (hpc : s.pc = "for.body.outer.i.i")
    (hpre : s.pre = some "if.else46.i.thread.i")
    (hi : lookupName env "%inc57.i344.i" = some (.int 64 i))
    (hT : lookupName env "%T.0723.i.i" = some (.int 64 T))
    (hF : lookupName env "%F.0722.i.i" = some (.int 64 F))
    (hlead : lookupName env "%lead.0721.i.i" = some (.int 64 lead))
    (hp : lookupName env "%p" = some (.ptr a))
    (hi63 : i.toNat < 2 ^ 63)
    (hb : readBytes s.mem (a + i.toNat) 1 = some (natToBytes b.toNat 1))
    (hbit : evalICmp .ult (b + 0xd0#8) 0x0a#8 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32
          (a + i.toNat) b)
        { s with pc := "if.else46.i.i", pre := some "for.body.outer.i.i" }) := by
  refine numFast_step_at
    (s' := stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32 (a + i.toNat) b) s)
    (b := ⟨"for.body.outer.i.i", outerInstrs,
      Term.condbr (Operand.reg "%or.cond.i.peel.i") "if.then13.i.peel.i" "if.else46.i.i"⟩)
    ?_ ?_ ?_
  · simpa only [stateAt, hpc] using outer_find
  · simpa only [stateAt] using outer_denote_thread hpre hi hT hF hlead hp hi63 hb
  · rw [numFast_execTerm_condbr_zero
      (s := stateAt (outerEnv env i T F lead 0x00000001#32 0x00000000#32
        (a + i.toNat) b) s) "%or.cond.i.peel.i" "if.then13.i.peel.i" "if.else46.i.i"
      (lookupName_cons_self "%or.cond.i.peel.i"
        (Value.int 1 (evalICmp .ult (b + 0xd0#8) 0x0a#8)) _) hbit]
    simp only [stateAt, hpc]

/-! ### The peel loop's traversal: `for.body.i.i`

The inner loop is entered from the peel (`for.inc.thread.i.peel.i`) and re-entered
from its latch (`for.inc.thread.i.i`).  A visit loads the byte at the cursor: a
nonzero digit leaves for `if.end28.i.i`, a non-digit leaves for the thread block
(which refuses or hands the outer head the dot's edge), and a zero digit steps the
cursor and re-enters unless the cursor reaches `%n`.  The measure is the distance
to `%n`: a visit advances the cursor by one, so the loop's cost is four control
steps per unit of the length. -/

open LeanLLVM.JSON

/-- The peel loop's byte at an index: the read's `UInt8` as the register form the
chain steps take. -/
def peelByteAt (bs : List UInt8) (j : Nat) : BitVec 8 :=
  JsonScanLane.vByte (bs.getD j 0)

/-- The equality test of two `ofNat` words is the equality of their values. -/
theorem parse_evalICmp_eq_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    evalICmp .eq (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = (1 : BitVec 1) ↔ a = b := by
  by_cases h : a = b
  · subst h
    rw [evalICmp_eq_refl]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · have hne : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
      intro hh
      have h2 := congrArg BitVec.toNat hh
      simp only [BitVec.toNat_ofNat] at h2
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
      exact h h2
    rw [evalICmp_eq_ne hne]
    exact ⟨fun hh => absurd hh (by decide), fun hh => absurd hh h⟩

/-- A byte's one-byte encoding is the byte. -/
theorem parse_natToBytes_one (u : UInt8) : natToBytes u.toNat 1 = [u] := by
  simp [natToBytes]

/-- A one-byte read of a present byte, in the chain steps' form. -/
theorem parse_readBytes_one {m : Mem} {a : Nat} {u : UInt8}
    (h : readByte m a = some u) :
    readBytes m a 1 = some (natToBytes (JsonScanLane.vByte u).toNat 1) := by
  rw [readBytes_one_some.mpr h, JsonScanLane.vByte_toNat, parse_natToBytes_one]

/-- The byte at an index inside a readable range, in the chain steps' form. -/
theorem parse_readBytes_one_at {m : Mem} {p n j : Nat} {bs : List UInt8}
    (h : readBytes m p n = some bs) (hj : j < n) :
    readBytes m (p + j) 1 = some (natToBytes (peelByteAt bs j).toNat 1) :=
  parse_readBytes_one (readByte_of_readBytes h hj)

/-- Whether the byte at the cursor is a digit, read from the loop's own memory. -/
def peelDigit (mem0 : Mem) (p j : Nat) : Bool :=
  match readByte mem0 (p + j) with
  | some b => IsDigitB b
  | none => false

theorem peelDigit_eq_true {mem0 : Mem} {p j : Nat} :
    peelDigit mem0 p j = true ↔
      ∃ b : UInt8, readByte mem0 (p + j) = some b ∧ IsDigitB b = true := by
  unfold peelDigit
  cases h : readByte mem0 (p + j) with
  | none => simp [h]
  | some b => simp [h]

/-- The peel loop's exit test: the cursor reaches the end, the byte is not a
digit, or the digit is not zero. -/
def peelAtBound (mem0 : Mem) (p n : Nat) (bs : List UInt8) : State → Nat → Bool :=
  fun _ j => decide (n ≤ j + 1) || !peelDigit mem0 p j ||
    decide (peelByteAt bs j + 0xd0#8 ≠ 0x00#8)

/-- The peel loop's edge: the four `phi` cells the head reads, at either
predecessor it can have. -/
def PeelEdge (s : State) (i T F lead : BitVec 64) : Prop :=
  (s.pre = some "for.inc.thread.i.peel.i" ∧
    lookupName s.env "%inc57798.i.peel.i" = some (.int 64 i) ∧
    lookupName s.env "%inc16.i.peel.i" = some (.int 64 T) ∧
    lookupName s.env "%spec.select.i.peel.i" = some (.int 64 F) ∧
    lookupName s.env "%lead.0721.ph.i.i" = some (.int 64 lead))
  ∨ (s.pre = some "for.inc.thread.i.i" ∧
    lookupName s.env "%inc57798.i.i" = some (.int 64 i) ∧
    lookupName s.env "%inc16.i.i" = some (.int 64 T) ∧
    lookupName s.env "%spec.select.i.i" = some (.int 64 F) ∧
    lookupName s.env "%lead.0721.i.i" = some (.int 64 lead))

/-- The peel loop's state at its head. -/
def PeelInv (mem0 : Mem) (p n digA : Nat) (bs : List UInt8)
    (i T F lead inc18 R top topn : BitVec 64) (sticky seen inFrac : BitVec 32)
    (r : Nat) (s : State) (j : Nat) : Prop :=
  s.pc = "for.body.i.i" ∧
  s.mem = mem0 ∧
  n < 2 ^ 63 ∧
  j < n ∧
  n ≤ j + r ∧
  readBytes mem0 p n = some bs ∧
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName s.env "%dig.i.i" = some (.ptr digA) ∧
  lookupName s.env "%inc18.i.i" = some (.int 64 inc18) ∧
  lookupName s.env "%R.0724.ph.i.ph.i" = some (.int 64 R) ∧
  lookupName s.env "%top.0720.ph.i.ph.i" = some (.int 64 top) ∧
  lookupName s.env "%topn.0719.ph.i.ph.i" = some (.int 64 topn) ∧
  lookupName s.env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky) ∧
  lookupName s.env "%seen.0717.ph.i.ph.i" = some (.int 32 seen) ∧
  lookupName s.env "%in_frac.0718.ph.i.ph.i" = some (.int 32 inFrac) ∧
  i.toNat = j ∧
  PeelEdge s i T F lead

/-- The peel loop's exit states. -/
def PeelExit (s : State) : Prop :=
  (s.pc = "if.end28.i.i" ∧ s.pre = some "if.then13.i.i") ∨
  s.pc = "if.then59.i.i" ∨
  (s.pc = "for.body.outer.i.i" ∧ s.pre = some "if.else46.i.thread.i")

/-- The peel loop's exit word: the parse's carried cells, and the cells the
continuation reads at whichever exit it left by. -/
def PeelOut (p n digA : Nat) (R top topn : BitVec 64) (sticky seen inFrac : BitVec 32)
    (s : State) : Prop :=
  lookupName s.env "%p" = some (.ptr p) ∧
  lookupName s.env "%n" = some (.int 64 (BitVec.ofNat 64 n)) ∧
  lookupName s.env "%dig.i.i" = some (.ptr digA) ∧
  lookupName s.env "%R.0724.ph.i.ph.i" = some (.int 64 R) ∧
  lookupName s.env "%top.0720.ph.i.ph.i" = some (.int 64 top) ∧
  lookupName s.env "%topn.0719.ph.i.ph.i" = some (.int 64 topn) ∧
  lookupName s.env "%sticky.0716.ph.i.ph.i" = some (.int 32 sticky) ∧
  lookupName s.env "%seen.0717.ph.i.ph.i" = some (.int 32 seen) ∧
  lookupName s.env "%in_frac.0718.ph.i.ph.i" = some (.int 32 inFrac) ∧
  (∃ (i T F lead : BitVec 64) (d : BitVec 8),
      (s.pc = "if.end28.i.i" ∧ s.pre = some "if.then13.i.i" ∧
        lookupName s.env "%inc16.i.i" = some (.int 64 T) ∧
        lookupName s.env "%spec.select.i.i" = some (.int 64 F) ∧
        lookupName s.env "%i.1725.i.i" = some (.int 64 i) ∧
        lookupName s.env "%lead.0721.i.i" = some (.int 64 lead) ∧
        lookupName s.env "%57" = some (.int 8 d))
    ∨ (s.pc = "if.then59.i.i")
    ∨ (s.pc = "for.body.outer.i.i" ∧ s.pre = some "if.else46.i.thread.i" ∧
        lookupName s.env "%inc57.i344.i" = some (.int 64 i) ∧
        lookupName s.env "%T.0723.i.i" = some (.int 64 T) ∧
        lookupName s.env "%F.0722.i.i" = some (.int 64 F) ∧
        lookupName s.env "%lead.0721.i.i" = some (.int 64 lead) ∧
        lookupName s.env "%56" = some (.int 8 d)))

/-- Resolve a cell through the parse's environment builders. -/
macro "parse_lk" : tactic => `(tactic|
  (first
   | assumption
   | (simp (config := { failIfUnchanged := false }) only
        [bodyEnv, thenEnv, incThreadEnv, threadEnv, incPeelEnv, end28Env, t3CopyEnv,
         mulEnv, latchEnv, outerPhiEnv, outerEnv, peelEnv, peelExitEnv, parseEndEnv,
         dotEnv, runCells]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
       | rw [lookupName_cons_self]
       | assumption
       | rfl)))

/-- **The peel loop's exit arm.**  The cursor reaches the end, the byte is not a
digit, or the digit is not zero; each leaves the loop in at most three control
steps, and the exit word names the cells the continuation reads. -/
theorem peelStepExit {calls : Calls} {mem0 : Mem} {p n digA : Nat} {bs : List UInt8}
    {i T F lead inc18 R top topn : BitVec 64} {sticky seen inFrac : BitVec 32}
    {r : Nat} {s : State} {j : Nat}
    (hinv : PeelInv mem0 p n digA bs i T F lead inc18 R top topn sticky seen inFrac r s j)
    (hb : peelAtBound mem0 p n bs s j = true) :
    ∃ (e : State) (steps : Nat), steps ≤ 4 ∧ PeelExit e ∧
      PeelOut p n digA R top topn sticky seen inFrac e ∧
      ∀ k, runFuel calls (steps + k) numFastBody (stateAt s.env s) =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hn63, hjn, hbud, hread, hp, hn, hdig, hinc18, hR, htop, htopn,
    hsticky, hseen, hin, hi, hedge⟩ := hinv
  have hby : readBytes mem0 (p + j) 1 = some (natToBytes (peelByteAt bs j).toNat 1) :=
    parse_readBytes_one_at hread hjn
  have hb' : readBytes s.mem (p + (i.signExtend 64).toNat) 1
      = some (natToBytes (peelByteAt bs j).toNat 1) := by
    rw [hmem, signExtend64_toNat, hi]; exact hby
  have hi63 : i.toNat < 2 ^ 63 := by omega
  by_cases hdigB : IsDigitB (bs.getD j 0) = true
  · -- the byte is a digit
    have hult : evalICmp .ult (JsonScanLane.vByte (bs.getD j 0) + 0xd0#8) 0x0a#8
        = (1 : BitVec 1) := by
      have h := evalICmp_ult_digit (bs.getD j 0)
      rw [h, hdigB]; rfl
    -- the body's step onto the digit edge
    rcases hedge with ⟨hpre, hc1, hc2, hc3, hc4⟩ | ⟨hpre, hc1, hc2, hc3, hc4⟩
    · have hstep1 : step calls numFastBody (stateAt s.env s) =
          .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
        simpa only [stateAt] using body_step_peel_digit (calls := calls) (env := s.env) (s := s)
          hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
      have hT' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%T.0723.i.i" = some (.int 64 T) := by parse_lk
      have hF' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%F.0722.i.i" = some (.int 64 F) := by parse_lk
      have h57' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%57" = some (.int 8 (peelByteAt bs j + 0xd0#8)) := by parse_lk
      have hii' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%i.1725.i.i" = some (.int 64 i) := by parse_lk
      have hll' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%lead.0721.i.i"
          = some (.int 64 (lead + 0x1#64)) := by parse_lk
      have hb56 : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%56" = some (.int 8 (peelByteAt bs j)) := by parse_lk
      by_cases hz : peelByteAt bs j + 0xd0#8 = 0x00#8
      · -- a zero digit: the cursor's step ends the loop only at `%n`
        have hpeelDig : peelDigit mem0 p j = true := by
          rw [peelDigit_eq_true]
          exact ⟨bs.getD j 0, readByte_of_readBytes hread hjn, hdigB⟩
        have hbnd : n ≤ j + 1 := by
          unfold peelAtBound at hb
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq] at hb
          rcases hb with (h | h) | h
          · exact h
          · have hd : peelDigit mem0 p j = false := by simpa using h
            exact absurd hpeelDig (by rw [hd]; decide)
          · exact absurd hz h
        have hjeq : j + 1 = n := by omega
        have hzero1 : evalICmp .eq (peelByteAt bs j + 0xd0#8) 0x00#8 = (1 : BitVec 1) := by
          rw [hz]
          exact evalICmp_eq_refl _
        have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) := by
          simpa only [stateAt] using then_step_continue (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
            (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
            rfl hT' hF' hinc18 h57' hzero1
        have hlatch1 : evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) = (1 : BitVec 1) := by
          have hi' : i = BitVec.ofNat 64 j := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hi]
          have hadd : i + 0x1#64 = BitVec.ofNat 64 (j + 1) := by
            rw [hi']; exact ofNat64_add_one (by omega)
          rw [hadd]
          exact (parse_evalICmp_eq_ofNat (by omega) (by omega)).mpr hjeq
        have hinc' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%i.1725.i.i"
            = some (.int 64 i) := by parse_lk
        have hnn' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%n"
            = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
        have hstep3 : step calls numFastBody
            (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) =
            .jump (stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
                (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
                (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
              { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" }) := by
          simpa only [stateAt] using incThread_step_exit (calls := calls)
            (env := thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
            (s := { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" })
            (i := i) (n := BitVec.ofNat 64 n) rfl hinc' hnn' hlatch1
        refine ⟨stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
            (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
            (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
            { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" },
          3, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inl rfl)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨0, 0, 0, 0, 0, Or.inr (Or.inl rfl)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2, hstep3]
      · -- a nonzero digit: the digit is counted and the loop is left
        have hzero0 : evalICmp .eq (peelByteAt bs j + 0xd0#8) 0x00#8 = (0 : BitVec 1) := by
          apply evalICmp_eq_ne
          intro hc
          exact hz hc
        have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "if.end28.i.i", pre := some "if.then13.i.i" }) := by
          simpa only [stateAt] using then_step_exit (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
            (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
            rfl hT' hF' hinc18 h57' hzero0
        refine ⟨stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
            { s with pc := "if.end28.i.i", pre := some "if.then13.i.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨i, T + 0x1#64, F + inc18, lead + 0x1#64,
              peelByteAt bs j + 0xd0#8,
              Or.inl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]
    · have hstep1 : step calls numFastBody (stateAt s.env s) =
          .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
        simpa only [stateAt] using body_step_back_digit (calls := calls) (env := s.env) (s := s)
          hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
      have hT' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%T.0723.i.i" = some (.int 64 T) := by parse_lk
      have hF' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%F.0722.i.i" = some (.int 64 F) := by parse_lk
      have h57' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%57" = some (.int 8 (peelByteAt bs j + 0xd0#8)) := by parse_lk
      have hii' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%i.1725.i.i" = some (.int 64 i) := by parse_lk
      have hll' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%lead.0721.i.i" = some (.int 64 (lead + 0x1#64)) := by parse_lk
      by_cases hz : peelByteAt bs j + 0xd0#8 = 0x00#8
      · have hpeelDig : peelDigit mem0 p j = true := by
          rw [peelDigit_eq_true]
          exact ⟨bs.getD j 0, readByte_of_readBytes hread hjn, hdigB⟩
        have hbnd : n ≤ j + 1 := by
          unfold peelAtBound at hb
          simp only [Bool.or_eq_true_iff, decide_eq_true_eq] at hb
          rcases hb with (h | h) | h
          · exact h
          · have hd : peelDigit mem0 p j = false := by simpa using h
            exact absurd hpeelDig (by rw [hd]; decide)
          · exact absurd hz h
        have hjeq : j + 1 = n := by omega
        have hzero1 : evalICmp .eq (peelByteAt bs j + 0xd0#8) 0x00#8 = (1 : BitVec 1) := by
          rw [hz]
          exact evalICmp_eq_refl _
        have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) := by
          simpa only [stateAt] using then_step_continue (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
            (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
            rfl hT' hF' hinc18 h57' hzero1
        have hlatch1 : evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) = (1 : BitVec 1) := by
          have hi' : i = BitVec.ofNat 64 j := by
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hi]
          have hadd : i + 0x1#64 = BitVec.ofNat 64 (j + 1) := by
            rw [hi']; exact ofNat64_add_one (by omega)
          rw [hadd]
          exact (parse_evalICmp_eq_ofNat (by omega) (by omega)).mpr hjeq
        have hinc' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%i.1725.i.i"
            = some (.int 64 i) := by parse_lk
        have hnn' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%n"
            = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
        have hstep3 : step calls numFastBody
            (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) =
            .jump (stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
                (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
                (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
              { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" }) := by
          simpa only [stateAt] using incThread_step_exit (calls := calls)
            (env := thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
            (s := { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" })
            (i := i) (n := BitVec.ofNat 64 n) rfl hinc' hnn' hlatch1
        refine ⟨stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
            (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
            (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
            { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" },
          3, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inl rfl)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨0, 0, 0, 0, 0, Or.inr (Or.inl rfl)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2, hstep3]
      · have hzero0 : evalICmp .eq (peelByteAt bs j + 0xd0#8) 0x00#8 = (0 : BitVec 1) := by
          apply evalICmp_eq_ne
          intro hc
          exact hz hc
        have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
              { s with pc := "if.end28.i.i", pre := some "if.then13.i.i" }) := by
          simpa only [stateAt] using then_step_exit (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
            (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
            rfl hT' hF' hinc18 h57' hzero0
        refine ⟨stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
            { s with pc := "if.end28.i.i", pre := some "if.then13.i.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨i, T + 0x1#64, F + inc18, lead + 0x1#64,
              peelByteAt bs j + 0xd0#8,
              Or.inl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]
  · -- the byte is not a digit
    have hdigB0 : IsDigitB (bs.getD j 0) = false := by
      cases h : IsDigitB (bs.getD j 0) <;> simp_all
    have hult : evalICmp .ult (JsonScanLane.vByte (bs.getD j 0) + 0xd0#8) 0x0a#8
        = (0 : BitVec 1) := by
      have h := evalICmp_ult_digit (bs.getD j 0)
      rw [h, hdigB0]; rfl
    rcases hedge with ⟨hpre, hc1, hc2, hc3, hc4⟩ | ⟨hpre, hc1, hc2, hc3, hc4⟩
    · have hstep1 : step calls numFastBody (stateAt s.env s) =
          .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) := by
        simpa only [stateAt] using body_step_peel_nondigit (calls := calls) (env := s.env)
          (s := s) hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
      have h56' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%56" = some (.int 8 (peelByteAt bs j)) := by parse_lk
      have hii' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%i.1725.i.i" = some (.int 64 i) := by parse_lk
      have hnn' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
      have hor : evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8 = (1 : BitVec 1) ∨
          evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8 = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one
          (evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8) with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases hor with hor | hor
      · have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
              { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" }) := by
          simpa only [stateAt] using thread_step_refuse (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" })
            (b56 := peelByteAt bs j) (i := i) (n := BitVec.ofNat 64 n) rfl h56' hii' hnn' hor
        refine ⟨stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
            { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inl rfl)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨0, 0, 0, 0, 0, Or.inr (Or.inl rfl)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]
      · have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
              { s with pc := "for.body.outer.i.i", pre := some "if.else46.i.thread.i" }) := by
          simpa only [stateAt] using thread_step_outer (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" })
            (b56 := peelByteAt bs j) (i := i) (n := BitVec.ofNat 64 n) rfl h56' hii' hnn' hor
        refine ⟨stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
            { s with pc := "for.body.outer.i.i", pre := some "if.else46.i.thread.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨i + 0x1#64, T, F, lead + 0x1#64, peelByteAt bs j,
              Or.inr (Or.inr ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]
    · have hstep1 : step calls numFastBody (stateAt s.env s) =
          .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) := by
        simpa only [stateAt] using body_step_back_nondigit (calls := calls) (env := s.env)
          (s := s) hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
      have h56' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%56" = some (.int 8 (peelByteAt bs j)) := by parse_lk
      have hii' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%i.1725.i.i" = some (.int 64 i) := by parse_lk
      have hnn' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) "%n" = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
      have hor : evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8 = (1 : BitVec 1) ∨
          evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8 = (0 : BitVec 1) := by
        rcases bitVec1_eq_zero_or_one
          (evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) |||
            evalICmp .ne (peelByteAt bs j) 0x2e#8) with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases hor with hor | hor
      · have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
              { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" }) := by
          simpa only [stateAt] using thread_step_refuse (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" })
            (b56 := peelByteAt bs j) (i := i) (n := BitVec.ofNat 64 n) rfl h56' hii' hnn' hor
        refine ⟨stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
            { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inl rfl)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨0, 0, 0, 0, 0, Or.inr (Or.inl rfl)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]
      · have hstep2 : step calls numFastBody
            (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
              (peelByteAt bs j)) { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" }) =
            .jump (stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
                (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
              { s with pc := "for.body.outer.i.i", pre := some "if.else46.i.thread.i" }) := by
          simpa only [stateAt] using thread_step_outer (calls := calls)
            (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
            (s := { s with pc := "if.else46.i.thread.i", pre := some "for.body.i.i" })
            (b56 := peelByteAt bs j) (i := i) (n := BitVec.ofNat 64 n) rfl h56' hii' hnn' hor
        refine ⟨stateAt (threadEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) (peelByteAt bs j) i (BitVec.ofNat 64 n))
            { s with pc := "for.body.outer.i.i", pre := some "if.else46.i.thread.i" },
          2, by decide, ?_, ?_, ?_⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ⟨i + 0x1#64, T, F, lead + 0x1#64, peelByteAt bs j,
              Or.inr (Or.inr ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩)⟩⟩
          all_goals parse_lk
        · intro k
          rw [show 2 + k = (k + 1) + 1 from by omega]
          simp only [runFuel, hstep1, hstep2]

/-- **The peel loop's back edge.**  The byte is a zero digit inside the lexeme, so
the cursor's step does not reach `%n`: the visit re-enters the head in three
control steps carrying the counted digit and the advanced cursor. -/
theorem peelStepLoop {calls : Calls} {mem0 : Mem} {p n digA : Nat} {bs : List UInt8}
    {i T F lead inc18 R top topn : BitVec 64} {sticky seen inFrac : BitVec 32}
    {r : Nat} {s : State} {j : Nat}
    (hinv : PeelInv mem0 p n digA bs i T F lead inc18 R top topn sticky seen inFrac (r + 1) s j)
    (hb : peelAtBound mem0 p n bs s j = false) :
    ∃ (e : State) (j' : Nat) (steps : Nat), steps ≤ 4 ∧ e.pc = "for.body.i.i" ∧
      j < j' ∧
      PeelInv mem0 p n digA bs (i + 0x1#64) (T + 0x1#64) (F + inc18) (lead + 0x1#64)
        inc18 R top topn sticky seen inFrac r e j' ∧
      ∀ k, runFuel calls (steps + k) numFastBody (stateAt s.env s) =
        runFuel calls k numFastBody e := by
  obtain ⟨hpc, hmem, hn63, hjn, hbud, hread, hp, hn, hdig, hinc18, hR, htop, htopn,
    hsticky, hseen, hin, hi, hedge⟩ := hinv
  unfold peelAtBound at hb
  rw [Bool.or_eq_false_iff] at hb
  obtain ⟨hb1, hB⟩ := hb
  rw [Bool.or_eq_false_iff] at hb1
  obtain ⟨hA, hd⟩ := hb1
  have hle : ¬(n ≤ j + 1) := by simpa using hA
  have hpeel' : peelDigit mem0 p j = true := by simpa using hd
  have hB' : ¬(peelByteAt bs j + 0xd0#8 ≠ 0x00#8) := by simpa using hB
  obtain ⟨b5, hb5, hd5⟩ := peelDigit_eq_true.mp hpeel'
  rw [readByte_of_readBytes hread hjn] at hb5
  have hb5' : b5 = bs.getD j 0 := (Option.some.inj hb5).symm
  have hdigB : IsDigitB (bs.getD j 0) = true := by rw [← hb5']; exact hd5
  have hlt : j + 1 < n := by omega
  have hult : evalICmp .ult (JsonScanLane.vByte (bs.getD j 0) + 0xd0#8) 0x0a#8
      = (1 : BitVec 1) := by
    have h := evalICmp_ult_digit (bs.getD j 0)
    rw [h, hdigB]; rfl
  have hby : readBytes mem0 (p + j) 1 = some (natToBytes (peelByteAt bs j).toNat 1) :=
    parse_readBytes_one_at hread hjn
  have hb' : readBytes s.mem (p + (i.signExtend 64).toNat) 1
      = some (natToBytes (peelByteAt bs j).toNat 1) := by
    rw [hmem, signExtend64_toNat, hi]; exact hby
  have hi63 : i.toNat < 2 ^ 63 := by omega
  have hzero1 : evalICmp .eq (peelByteAt bs j + 0xd0#8) 0x00#8 = (1 : BitVec 1) := by
    have hz : peelByteAt bs j + 0xd0#8 = 0x00#8 := by
      by_contra hc
      exact hB' hc
    rw [hz]
    exact evalICmp_eq_refl _
  have hnext : readBytes mem0 (p + (j + 1)) 1
      = some (natToBytes (peelByteAt bs (j + 1)).toNat 1) :=
    parse_readBytes_one_at hread hlt
  have hi' : i = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hi]
  have hadd : i + 0x1#64 = BitVec.ofNat 64 (j + 1) := by
    rw [hi']; exact ofNat64_add_one (by omega)
  have hlatch0 : evalICmp .eq (i + 0x1#64) (BitVec.ofNat 64 n) = (0 : BitVec 1) := by
    apply evalICmp_eq_ne
    rw [hadd]
    intro hc
    have h2 := congrArg BitVec.toNat hc
    simp only [BitVec.toNat_ofNat] at h2
    rw [Nat.mod_eq_of_lt (by omega : j + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] at h2
    omega
  have hi1 : (i + 0x1#64).toNat = j + 1 := by rw [hadd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases hedge with ⟨hpre, hc1, hc2, hc3, hc4⟩ | ⟨hpre, hc1, hc2, hc3, hc4⟩
  · -- the peeled entry
    have hstep1 : step calls numFastBody (stateAt s.env s) =
        .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
      simpa only [stateAt] using body_step_peel_digit (calls := calls) (env := s.env) (s := s)
        hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
    have hT' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%T.0723.i.i" = some (.int 64 T) := by parse_lk
    have hF' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%F.0722.i.i" = some (.int 64 F) := by parse_lk
    have h57' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%57" = some (.int 8 (peelByteAt bs j + 0xd0#8)) := by parse_lk
    have hstep2 : step calls numFastBody
        (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
        .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
          { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) := by
      simpa only [stateAt] using then_step_continue (calls := calls)
        (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
        (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
        (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
        rfl hT' hF' hinc18 h57' hzero1
    have hinc' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%i.1725.i.i"
        = some (.int 64 i) := by parse_lk
    have hnn' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%n"
        = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
    have hstep3 : step calls numFastBody
        (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
          { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) =
        .jump (stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
            (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
            (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
          { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.i" }) := by
      simpa only [stateAt] using incThread_step_body (calls := calls)
        (env := thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
        (s := { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" })
        (i := i) (n := BitVec.ofNat 64 n) rfl hinc' hnn' hlatch0
    refine ⟨stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
        (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
        (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
        { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.i" },
      j + 1, 3, by decide, rfl, by omega, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_, by omega, hread, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hi1, Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
      all_goals parse_lk
    · intro k
      rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2, hstep3]
  · -- the latch's back edge
    have hstep1 : step calls numFastBody (stateAt s.env s) =
        .jump (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) := by
      simpa only [stateAt] using body_step_back_digit (calls := calls) (env := s.env) (s := s)
        hpc hpre hc1 hc2 hc3 hc4 hp hi63 hb' hult
    have hT' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%T.0723.i.i" = some (.int 64 T) := by parse_lk
    have hF' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%F.0722.i.i" = some (.int 64 F) := by parse_lk
    have h57' : lookupName (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) "%57" = some (.int 8 (peelByteAt bs j + 0xd0#8)) := by parse_lk
    have hstep2 : step calls numFastBody
        (stateAt (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) { s with pc := "if.then13.i.i", pre := some "for.body.i.i" }) =
        .jump (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
            (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
          { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) := by
      simpa only [stateAt] using then_step_continue (calls := calls)
        (env := bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat) (peelByteAt bs j))
        (s := { s with pc := "if.then13.i.i", pre := some "for.body.i.i" })
        (T := T) (F := F) (inc18 := inc18) (b57 := peelByteAt bs j + 0xd0#8)
        rfl hT' hF' hinc18 h57' hzero1
    have hinc' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%i.1725.i.i"
        = some (.int 64 i) := by parse_lk
    have hnn' : lookupName (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
        (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8)) "%n"
        = some (.int 64 (BitVec.ofNat 64 n)) := by parse_lk
    have hstep3 : step calls numFastBody
        (stateAt (thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
          { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" }) =
        .jump (stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
            (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
            (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
          { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.i" }) := by
      simpa only [stateAt] using incThread_step_body (calls := calls)
        (env := thenEnv (bodyEnv s.env i T F lead (p + (i.signExtend 64).toNat)
          (peelByteAt bs j)) T F inc18 (peelByteAt bs j + 0xd0#8))
        (s := { s with pc := "for.inc.thread.i.i", pre := some "if.then13.i.i" })
        (i := i) (n := BitVec.ofNat 64 n) rfl hinc' hnn' hlatch0
    refine ⟨stateAt (incThreadEnv (thenEnv (bodyEnv s.env i T F lead
        (p + (i.signExtend 64).toNat) (peelByteAt bs j)) T F inc18
        (peelByteAt bs j + 0xd0#8)) i (BitVec.ofNat 64 n))
        { s with pc := "for.body.i.i", pre := some "for.inc.thread.i.i" },
      j + 1, 3, by decide, rfl, by omega, ?_, ?_⟩
    · refine ⟨rfl, ?_, ?_, ?_, by omega, hread, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hi1, Or.inr ⟨rfl, ?_, ?_, ?_, ?_⟩⟩
      all_goals parse_lk
    · intro k
      rw [show 3 + k = ((k + 1) + 1) + 1 from by omega]
      simp only [runFuel, hstep1, hstep2, hstep3]

/-- **The peel loop's traversal, by induction on the remaining distance.**  From
the body head with `r` visits left (the cursor is `n - r` short of the length),
the run reaches one of the loop's three exits within `4 * (r + 1)` control steps,
with the exit word the continuation reads.  An exit spends at most three steps; a
visit spends three and re-enters with one unit fewer. -/
theorem peelRunAux {calls : Calls} {mem0 : Mem} {p n digA : Nat} {bs : List UInt8} :
    ∀ (r : Nat) (s : State) (j : Nat)
      (i T F lead inc18 R top topn : BitVec 64) (sticky seen inFrac : BitVec 32),
      PeelInv mem0 p n digA bs i T F lead inc18 R top topn sticky seen inFrac r s j →
      ∃ (e : State) (steps : Nat), steps ≤ 4 * (r + 1) ∧ PeelExit e ∧
        PeelOut p n digA R top topn sticky seen inFrac e ∧
        ∀ k, runFuel calls (steps + k) numFastBody (stateAt s.env s) =
          runFuel calls k numFastBody e
  | 0, s, j, i, T, F, lead, inc18, R, top, topn, sticky, seen, inFrac, h => by
      obtain ⟨-, -, -, hjn, hbud, -⟩ := h
      exact absurd hbud (by omega)
  | r + 1, s, j, i, T, F, lead, inc18, R, top, topn, sticky, seen, inFrac, h => by
      by_cases hb : peelAtBound mem0 p n bs s j = true
      · obtain ⟨e, steps, hj, hexit, hout, hrun⟩ := peelStepExit h hb
        exact ⟨e, steps, by omega, hexit, hout, hrun⟩
      · have hb' : peelAtBound mem0 p n bs s j = false := by
          cases h' : peelAtBound mem0 p n bs s j
          · rfl
          · exact absurd h' hb
        obtain ⟨e, j', steps, hj, hpc, hlt, hinv', hrun⟩ := peelStepLoop h hb'
        obtain ⟨e', steps', hj', hexit', hout', hrun'⟩ :=
          peelRunAux r e j' (i + 0x1#64) (T + 0x1#64) (F + inc18) (lead + 0x1#64)
            inc18 R top topn sticky seen inFrac hinv'
        refine ⟨e', steps + steps', by omega, hexit', hout', fun k => ?_⟩
        rw [show steps + steps' + k = steps + (steps' + k) from by omega]
        rw [hrun (steps' + k)]
        exact hrun' k

/-- **The peel loop's traversal.**  From the body head with the cursor at `j`, the
run reaches one of the loop's three exits within `4 * (n - j + 1)` control steps,
with the exit word the continuation reads. -/
theorem peelRun {calls : Calls} (mem0 : Mem) (p n digA : Nat) (bs : List UInt8)
    (i T F lead inc18 R top topn : BitVec 64) (sticky seen inFrac : BitVec 32)
    (s : State) (j : Nat)
    (hinv : PeelInv mem0 p n digA bs i T F lead inc18 R top topn sticky seen inFrac
      (n - j) s j)
    (k : Nat) {o : Outcome}
    (hcont : ∀ (e : State), PeelExit e →
      PeelOut p n digA R top topn sticky seen inFrac e →
      runFuel calls k numFastBody e = some o) :
    runFuel calls (4 * (n - j + 1) + k) numFastBody (stateAt s.env s) = some o := by
  obtain ⟨e, steps, hj, hexit, hout, hrun⟩ :=
    peelRunAux (n - j) s j i T F lead inc18 R top topn sticky seen inFrac hinv
  have hone : runFuel calls (steps + k) numFastBody (stateAt s.env s) = some o := by
    rw [hrun]
    exact hcont e hexit hout
  exact runFuel_mono_le (by omega) hone

/-! ### The parse's zero exit: `if.then59.i.i`

Every arm of the parse that ends with nothing to convert lands here — the peel
latch's and the inner latch's counted exits, the parse's end, the outer latch's
counted exit, and the inner loop's non-digit refusal — and the block selects the
lexeme's zero: `-0.0` at `%cmp1.i`'s bit, `0.0` otherwise.  It hands the double
to the return's merge `if.end291`, whose leading `phi` reads this block's
`%cond.i.i` on this edge; `Then59Entry` names that entry, and each arm's run is
the arm's own step followed by `then59_step`.

The select has the clamps' shape, so the block adds no chain step: `clamp_step`
at `if.then59.i.i`'s own pin is its step, and the arms differ only in the
environment that carries `%cmp1.i` forward. -/

/-- `if.then59.i.i`, from its pin: the clamp's one `select`, with `-0.0` on the
sign's side. -/
theorem then59_find :
    numFastBody.findBlock "if.then59.i.i" =
      some ⟨"if.then59.i.i",
        clampInstrs "%cond.i.i" 0x8000000000000000#64 0x0000000000000000#64,
        Term.br "if.end291"⟩ := by
  simpa only [clampInstrs] using numFast_findBlock_if_then59_i_i

/-- The zero exit's step into the return's merge. -/
theorem then59_step {calls : Calls} {env : Env} {s : State} {bb : BitVec 1}
    (hpc : s.pc = "if.then59.i.i")
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (clampEnv env "%cond.i.i" 0x8000000000000000#64
          0x0000000000000000#64 bb)
        { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  exact clamp_step hpc then59_find hc

/-- The merge's entry on the zero exit's edge: its leading `phi` reads
`%cond.i.i`, the double this block selected. -/
def Then59Entry (bb : BitVec 1) (s : State) : Prop :=
  s.pc = "if.end291" ∧
  s.pre = some "if.then59.i.i" ∧
  lookupName s.env "%cond.i.i" =
    some (.float (if bb = 1 then 0x8000000000000000#64
      else 0x0000000000000000#64))

theorem then59_entry (env : Env) (bb : BitVec 1) (s : State) :
    Then59Entry bb
      { stateAt (clampEnv env "%cond.i.i" 0x8000000000000000#64
          0x0000000000000000#64 bb) s with
          pc := "if.end291", pre := some "if.then59.i.i" } := by
  refine ⟨rfl, rfl, ?_⟩
  exact lookupName_cons_self ..

/-- The peel latch's environment keeps the sign's bit. -/
theorem incPeelEnv_cmp1 {env : Env} {i n : BitVec 64} {bb : BitVec 1}
    (h : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    lookupName (incPeelEnv env i n) "%cmp1.i" = some (.int 1 bb) := by
  simp only [incPeelEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The refusal edge's environment keeps the sign's bit. -/
theorem threadEnv_cmp1 {env : Env} {b56 : BitVec 8} {i n : BitVec 64}
    {bb : BitVec 1} (h : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    lookupName (threadEnv env b56 i n) "%cmp1.i" = some (.int 1 bb) := by
  simp only [threadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The inner latch's environment keeps the sign's bit. -/
theorem incThreadEnv_cmp1 {env : Env} {i n : BitVec 64} {bb : BitVec 1}
    (h : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    lookupName (incThreadEnv env i n) "%cmp1.i" = some (.int 1 bb) := by
  simp only [incThreadEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The parse end's environment keeps the sign's bit. -/
theorem parseEndEnv_cmp1 {env : Env} {seen : BitVec 32} {bb : BitVec 1}
    (h : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    lookupName (parseEndEnv env seen) "%cmp1.i" = some (.int 1 bb) := by
  simp only [parseEndEnv]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The counted exit's environment keeps the sign's bit. -/
theorem endThreadEnv_cmp1 {env : Env} {seen : BitVec 32} {bb : BitVec 1}
    (h : lookupName env "%cmp1.i" = some (.int 1 bb)) :
    lookupName (endThreadEnv env seen) "%cmp1.i" = some (.int 1 bb) := by
  simp only [endThreadEnv]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact h

/-- **The peel latch's refusal arm, through the zero exit.**  Two steps to the
return's merge. -/
theorem then59_run_incPeel {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64} {bb : BitVec 1}
    (hpc : s.pc = "for.inc.thread.i.peel.i")
    (hi : lookupName env "%i.1725.ph.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (clampEnv (incPeelEnv env i n) "%cond.i.i"
            0x8000000000000000#64 0x0000000000000000#64 bb)
          { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  intro j
  have h1 := incPeel_step_exit (calls := calls) hpc hi hn hbit
  have h2 := then59_step (calls := calls)
    (env := incPeelEnv env i n)
    (s := { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.peel.i" })
    rfl (incPeelEnv_cmp1 hc)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-- **The refusal edge's arm, through the zero exit.**  Two steps to the
return's merge. -/
theorem then59_run_thread {calls : Calls} {env : Env} {s : State}
    {b56 : BitVec 8} {i n : BitVec 64} {bb : BitVec 1}
    (hpc : s.pc = "if.else46.i.thread.i")
    (h56 : lookupName env "%56" = some (.int 8 b56))
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n ||| evalICmp .ne b56 0x2e#8
      = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (clampEnv (threadEnv env b56 i n) "%cond.i.i"
            0x8000000000000000#64 0x0000000000000000#64 bb)
          { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  intro j
  have h1 := thread_step_refuse (calls := calls) hpc h56 hi hn hbit
  have h2 := then59_step (calls := calls)
    (env := threadEnv env b56 i n)
    (s := { s with pc := "if.then59.i.i", pre := some "if.else46.i.thread.i" })
    rfl (threadEnv_cmp1 hc)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-- **The inner latch's refusal arm, through the zero exit.**  Two steps to the
return's merge. -/
theorem then59_run_incThread {calls : Calls} {env : Env} {s : State}
    {i n : BitVec 64} {bb : BitVec 1}
    (hpc : s.pc = "for.inc.thread.i.i")
    (hi : lookupName env "%i.1725.i.i" = some (.int 64 i))
    (hn : lookupName env "%n" = some (.int 64 n))
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hbit : evalICmp .eq (i + 0x0000000000000001#64) n = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (clampEnv (incThreadEnv env i n) "%cond.i.i"
            0x8000000000000000#64 0x0000000000000000#64 bb)
          { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  intro j
  have h1 := incThread_step_exit (calls := calls) hpc hi hn hbit
  have h2 := then59_step (calls := calls)
    (env := incThreadEnv env i n)
    (s := { s with pc := "if.then59.i.i", pre := some "for.inc.thread.i.i" })
    rfl (incThreadEnv_cmp1 hc)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-- **The parse end's refusal arm, through the zero exit.**  Two steps to the
return's merge. -/
theorem then59_run_parseEnd {calls : Calls} {env : Env} {s : State}
    {seen : BitVec 32} {bb : BitVec 1}
    (hpc : s.pc = "for.end.i.i")
    (hseen : lookupName env "%seen.0717.ph.i.i" = some (.int 32 seen))
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hbit : evalICmp .eq seen 0x00000000#32 = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (clampEnv (parseEndEnv env seen) "%cond.i.i"
            0x8000000000000000#64 0x0000000000000000#64 bb)
          { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  intro j
  have h1 := parseEnd_step_refuse (calls := calls) hpc hseen hbit
  have h2 := then59_step (calls := calls)
    (env := parseEndEnv env seen)
    (s := { s with pc := "if.then59.i.i", pre := some "for.end.i.i" })
    rfl (parseEndEnv_cmp1 hc)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-- **The outer latch's counted exit, through the zero exit.**  Two steps to the
return's merge. -/
theorem then59_run_endThread {calls : Calls} {env : Env} {s : State}
    {seen : BitVec 32} {bb : BitVec 1}
    (hpc : s.pc = "for.end.thread.i.i")
    (hseen : lookupName env "%seen.4.ph.i.i" = some (.int 32 seen))
    (hc : lookupName env "%cmp1.i" = some (.int 1 bb))
    (hbit : evalICmp .eq seen 0x00000000#32 = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (clampEnv (endThreadEnv env seen) "%cond.i.i"
            0x8000000000000000#64 0x0000000000000000#64 bb)
          { s with pc := "if.end291", pre := some "if.then59.i.i" }) := by
  intro j
  have h1 := endThread_step_refuse (calls := calls) hpc hseen hbit
  have h2 := then59_step (calls := calls)
    (env := endThreadEnv env seen)
    (s := { s with pc := "if.then59.i.i", pre := some "for.end.thread.i.i" })
    rfl (endThreadEnv_cmp1 hc)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-! ### The copy's two preheaders: `for.body87.i.i.preheader` and its unrolled
successor

The dispatch's copy edge (`if.end83.i.i`'s taken test) enters the preheader,
which forms the residual count `%61 = n - i`, the scalar tail's count
`%xtraiter = %61 & 3` and the wrap test `%63 = (%i - n) >u -4` on `%62 = i - n`.
With fewer than four visits left, `i - n` is within three of `2^64`, so the test
is taken and the residual loop's entry `for.end100.i.i.loopexit.unr-lcssa` takes
the tail; otherwise the unrolled preheader forms the trip count
`%unroll_iter = %61 & -4` and the three `invariant.gep` bases the copy's stores
read, and enters `for.body87.i.i`.

Both blocks are straight lines over their pin's instructions.  The cells the two
boundaries read are named rather than assumed: `Pre87CopyEntry` is
`Tier3CopyUnroll`'s frame on the `.new` edge — `%i.2.i.i` for the head's first
`phi` and the three `invariant.gep` bases — and `Pre87EpilEntry` is the cells
`for.end100.i.i.loopexit.unr-lcssa`'s three `phi`s and its `%lcmp.mod.not` test
read.  The blocks under either boundary are not stated here. -/

def pre87Instrs : List Instr :=
  [Instr.binop "%61" (BinOp.sub) 64 (Operand.reg "%n") (Operand.reg "%i.2.i.i"),
   Instr.binop "%xtraiter" (BinOp.and) 64 (Operand.reg "%61")
     (Operand.imm (Const.int 64 0x0000000000000003#64)),
   Instr.binop "%62" (BinOp.sub) 64 (Operand.reg "%i.2.i.i") (Operand.reg "%n"),
   Instr.icmp "%63" (IPred.ugt) 64 (Operand.reg "%62")
     (Operand.imm (Const.int 64 0xfffffffffffffffc#64))]

theorem pre87_find :
    numFastBody.findBlock "for.body87.i.i.preheader" =
      some ⟨"for.body87.i.i.preheader", pre87Instrs,
        Term.condbr (Operand.reg "%63") "for.end100.i.i.loopexit.unr-lcssa"
          "for.body87.i.i.preheader.new"⟩ := by
  simpa only [pre87Instrs] using numFast_findBlock_for_body87_i_i_preheader

/-- The preheader's environment: the residual count, the tail's count, the
opposite difference and the wrap test. -/
def pre87Env (env : Env) (i2 n : BitVec 64) : Env :=
  ("%63", .int 1 (evalICmp .ugt (i2 - n) 0xfffffffffffffffc#64)) ::
  ("%62", .int 64 (i2 - n)) ::
  ("%xtraiter", .int 64 ((n - i2) &&& 0x0000000000000003#64)) ::
  ("%61", .int 64 (n - i2)) :: env

/-- The residual count, through the environment the block builds. -/
theorem pre87Env_61 {env : Env} {i2 n : BitVec 64} :
    lookupName (pre87Env env i2 n) "%61" = some (.int 64 (n - i2)) := by
  simp only [pre87Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The tail's count, through the environment the block builds. -/
theorem pre87Env_xt {env : Env} {i2 n : BitVec 64} :
    lookupName (pre87Env env i2 n) "%xtraiter" =
      some (.int 64 ((n - i2) &&& 0x0000000000000003#64)) := by
  simp only [pre87Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The dispatched cursor, through the block's four cells. -/
theorem pre87Env_i2 {env : Env} {i2 n : BitVec 64}
    (h : lookupName env "%i.2.i.i" = some (.int 64 i2)) :
    lookupName (pre87Env env i2 n) "%i.2.i.i" = some (.int 64 i2) := by
  simp only [pre87Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%n`, through the block's four cells. -/
theorem pre87Env_n {env : Env} {i2 n nn : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nn)) :
    lookupName (pre87Env env i2 n) "%n" = some (.int 64 nn) := by
  simp only [pre87Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- `%p`, through the block's four cells. -/
theorem pre87Env_p {env : Env} {i2 n : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (pre87Env env i2 n) "%p" = some (.ptr p) := by
  simp only [pre87Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The preheader's chain at its pin. -/
theorem pre87_denote {calls : Calls} {env : Env} {s : State} {i2 n : BitVec 64}
    (hn : lookupName env "%n" = some (.int 64 n))
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2)) :
    denoteCode calls pre87Instrs (stateAt env s) =
      some (stateAt (pre87Env env i2 n) s) := by
  unfold pre87Instrs
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- **The preheader's taken test: the residual loop's entry.**  At most three
visits are left, so the tail is the residual loop's. -/
theorem pre87_step_lcssa {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.preheader")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2))
    (hbit : evalICmp .ugt (i2 - n) 0xfffffffffffffffc#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre87Env env i2 n)
        { s with pc := "for.end100.i.i.loopexit.unr-lcssa",
                 pre := some "for.body87.i.i.preheader" }) := by
  refine numFast_step_at (s' := stateAt (pre87Env env i2 n) s)
    (b := ⟨"for.body87.i.i.preheader", pre87Instrs,
      Term.condbr (Operand.reg "%63") "for.end100.i.i.loopexit.unr-lcssa"
        "for.body87.i.i.preheader.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre87_find
  · exact pre87_denote hn hi
  · rw [numFast_execTerm_condbr_one (s := stateAt (pre87Env env i2 n) s) "%63"
      "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i.preheader.new"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The preheader's untaken test: the unrolled successor.**  At least four
visits are left, so the unrolled nest runs. -/
theorem pre87_step_new {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64}
    (hpc : s.pc = "for.body87.i.i.preheader")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2))
    (hbit : evalICmp .ugt (i2 - n) 0xfffffffffffffffc#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre87Env env i2 n)
        { s with pc := "for.body87.i.i.preheader.new",
                 pre := some "for.body87.i.i.preheader" }) := by
  refine numFast_step_at (s' := stateAt (pre87Env env i2 n) s)
    (b := ⟨"for.body87.i.i.preheader", pre87Instrs,
      Term.condbr (Operand.reg "%63") "for.end100.i.i.loopexit.unr-lcssa"
        "for.body87.i.i.preheader.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre87_find
  · exact pre87_denote hn hi
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pre87Env env i2 n) s) "%63"
      "for.end100.i.i.loopexit.unr-lcssa" "for.body87.i.i.preheader.new"
      (lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- The residual loop's entry on the preheader's taken test: the cells
`for.end100.i.i.loopexit.unr-lcssa`'s three `phi`s and its `%lcmp.mod.not` test
read. -/
def Pre87EpilEntry (i2 n : BitVec 64) (s : State) : Prop :=
  s.pc = "for.end100.i.i.loopexit.unr-lcssa" ∧
  s.pre = some "for.body87.i.i.preheader" ∧
  lookupName s.env "%i.2.i.i" = some (.int 64 i2) ∧
  lookupName s.env "%xtraiter" =
    some (.int 64 ((n - i2) &&& 0x0000000000000003#64))

theorem pre87_epil_entry {env : Env} {i2 n : BitVec 64}
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2)) (s : State) :
    Pre87EpilEntry i2 n
      { stateAt (pre87Env env i2 n) s with
          pc := "for.end100.i.i.loopexit.unr-lcssa",
          pre := some "for.body87.i.i.preheader" } := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact pre87Env_i2 hi
  · exact pre87Env_xt

def pre87newInstrs : List Instr :=
  [Instr.binop "%unroll_iter" (BinOp.and) 64 (Operand.reg "%61")
     (Operand.imm (Const.int 64 0xfffffffffffffffc#64)),
   Instr.gep "%invariant.gep" (Ty.int 8) (Operand.reg "%p")
     (Operand.imm (Const.int 64 0x0000000000000001#64)),
   Instr.gep "%invariant.gep1191" (Ty.int 8) (Operand.reg "%p")
     (Operand.imm (Const.int 64 0x0000000000000002#64)),
   Instr.gep "%invariant.gep1193" (Ty.int 8) (Operand.reg "%p")
     (Operand.imm (Const.int 64 0x0000000000000003#64))]

theorem pre87new_find :
    numFastBody.findBlock "for.body87.i.i.preheader.new" =
      some ⟨"for.body87.i.i.preheader.new", pre87newInstrs,
        Term.br "for.body87.i.i"⟩ := by
  simpa only [pre87newInstrs] using numFast_findBlock_for_body87_i_i_preheader_new

/-- The unrolled preheader's environment: the trip count and the three bases. -/
def pre87newEnv (env : Env) (x61 : BitVec 64) (p : Nat) : Env :=
  ("%invariant.gep1193",
    .ptr (p + ((0x0000000000000003#64).signExtend 64).toNat)) ::
  ("%invariant.gep1191",
    .ptr (p + ((0x0000000000000002#64).signExtend 64).toNat)) ::
  ("%invariant.gep",
    .ptr (p + ((0x0000000000000001#64).signExtend 64).toNat)) ::
  ("%unroll_iter", .int 64 (x61 &&& 0xfffffffffffffffc#64)) :: env

/-- The trip count, through the environment the block builds. -/
theorem pre87newEnv_unroll {env : Env} {x61 : BitVec 64} {p : Nat} :
    lookupName (pre87newEnv env x61 p) "%unroll_iter" =
      some (.int 64 (x61 &&& 0xfffffffffffffffc#64)) := by
  simp only [pre87newEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The first base, through the environment the block builds. -/
theorem pre87newEnv_gep {env : Env} {x61 : BitVec 64} {p : Nat} :
    lookupName (pre87newEnv env x61 p) "%invariant.gep" =
      some (.ptr (p + ((0x0000000000000001#64).signExtend 64).toNat)) := by
  simp only [pre87newEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The second base, through the environment the block builds. -/
theorem pre87newEnv_gep1191 {env : Env} {x61 : BitVec 64} {p : Nat} :
    lookupName (pre87newEnv env x61 p) "%invariant.gep1191" =
      some (.ptr (p + ((0x0000000000000002#64).signExtend 64).toNat)) := by
  simp only [pre87newEnv]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The third base, through the environment the block builds. -/
theorem pre87newEnv_gep1193 {env : Env} {x61 : BitVec 64} {p : Nat} :
    lookupName (pre87newEnv env x61 p) "%invariant.gep1193" =
      some (.ptr (p + ((0x0000000000000003#64).signExtend 64).toNat)) := by
  simp only [pre87newEnv]
  exact lookupName_cons_self ..

/-- The dispatched cursor, through the unrolled preheader's four cells. -/
theorem pre87newEnv_i2 {env : Env} {x61 : BitVec 64} {p : Nat} {nn : BitVec 64}
    (h : lookupName env "%i.2.i.i" = some (.int 64 nn)) :
    lookupName (pre87newEnv env x61 p) "%i.2.i.i" = some (.int 64 nn) := by
  simp only [pre87newEnv]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The unrolled preheader's chain at its pin. -/
theorem pre87new_denote {calls : Calls} {env : Env} {s : State}
    {x61 : BitVec 64} {p : Nat}
    (h61 : lookupName env "%61" = some (.int 64 x61))
    (hp : lookupName env "%p" = some (.ptr p)) :
    denoteCode calls pre87newInstrs (stateAt env s) =
      some (stateAt (pre87newEnv env x61 p) s) := by
  unfold pre87newInstrs
  have hpos1 : ((0x0000000000000001#64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hpos2 : ((0x0000000000000002#64).signExtend 64).toNat < 2 ^ 63 := by decide
  have hpos3 : ((0x0000000000000003#64).signExtend 64).toNat < 2 ^ 63 := by decide
  inner_step
  inner_step
  inner_step
  inner_step
  block_close

/-- The state the unrolled preheader hands the copy's head. -/
def pre87BodyState (env : Env) (i2 n : BitVec 64) (p : Nat) (s : State) : State :=
  { stateAt (pre87newEnv (pre87Env env i2 n) (n - i2) p) s with
      pc := "for.body87.i.i", pre := some "for.body87.i.i.preheader.new" }

/-- The unrolled preheader's step into the copy's head. -/
theorem pre87new_step {calls : Calls} {env : Env} {s : State}
    {x61 : BitVec 64} {p : Nat}
    (hpc : s.pc = "for.body87.i.i.preheader.new")
    (h61 : lookupName env "%61" = some (.int 64 x61))
    (hp : lookupName env "%p" = some (.ptr p)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre87newEnv env x61 p)
        { s with pc := "for.body87.i.i",
                 pre := some "for.body87.i.i.preheader.new" }) := by
  refine numFast_step_at (s' := stateAt (pre87newEnv env x61 p) s)
    (b := ⟨"for.body87.i.i.preheader.new", pre87newInstrs,
      Term.br "for.body87.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre87new_find
  · exact pre87new_denote h61 hp
  · simp only [execTerm, stateAt, hpc]

/-- The copy's head on the unrolled preheader's edge: the cells
`Tier3CopyUnroll`'s frame and the head's first `phi` read. -/
def Pre87CopyEntry (i2 n : BitVec 64) (p : Nat) (s : State) : Prop :=
  s.pc = "for.body87.i.i" ∧
  s.pre = some "for.body87.i.i.preheader.new" ∧
  lookupName s.env "%i.2.i.i" = some (.int 64 i2) ∧
  lookupName s.env "%unroll_iter" =
    some (.int 64 ((n - i2) &&& 0xfffffffffffffffc#64)) ∧
  lookupName s.env "%invariant.gep" = some (.ptr (p + 1)) ∧
  lookupName s.env "%invariant.gep1191" = some (.ptr (p + 2)) ∧
  lookupName s.env "%invariant.gep1193" = some (.ptr (p + 3))

theorem pre87_copy_entry {env : Env} {i2 n : BitVec 64} {p : Nat}
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2)) (s : State) :
    Pre87CopyEntry i2 n p (pre87BodyState env i2 n p s) := by
  have hone : ((0x0000000000000001#64 : BitVec 64).signExtend 64).toNat = 1 := by
    decide
  have htwo : ((0x0000000000000002#64 : BitVec 64).signExtend 64).toNat = 2 := by
    decide
  have hthree : ((0x0000000000000003#64 : BitVec 64).signExtend 64).toNat = 3 := by
    decide
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact pre87newEnv_i2 (pre87Env_i2 hi)
  · exact pre87newEnv_unroll
  · calc lookupName (pre87BodyState env i2 n p s).env "%invariant.gep"
        = some (.ptr (p + ((0x0000000000000001#64).signExtend 64).toNat)) :=
          pre87newEnv_gep
      _ = some (.ptr (p + 1)) := by rw [hone]
  · calc lookupName (pre87BodyState env i2 n p s).env "%invariant.gep1191"
        = some (.ptr (p + ((0x0000000000000002#64).signExtend 64).toNat)) :=
          pre87newEnv_gep1191
      _ = some (.ptr (p + 2)) := by rw [htwo]
  · calc lookupName (pre87BodyState env i2 n p s).env "%invariant.gep1193"
        = some (.ptr (p + ((0x0000000000000003#64).signExtend 64).toNat)) :=
          pre87newEnv_gep1193
      _ = some (.ptr (p + 3)) := by rw [hthree]

/-- **The preheader's run into the copy's head.**  Two control steps when at
least four visits are left; the state it leaves is `Pre87CopyEntry`'s. -/
theorem pre87_run_copy {calls : Calls} {env : Env} {s : State}
    {i2 n : BitVec 64} {p : Nat}
    (hpc : s.pc = "for.body87.i.i.preheader")
    (hn : lookupName env "%n" = some (.int 64 n))
    (hi : lookupName env "%i.2.i.i" = some (.int 64 i2))
    (hp : lookupName env "%p" = some (.ptr p))
    (hbit : evalICmp .ugt (i2 - n) 0xfffffffffffffffc#64 = (0 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody (pre87BodyState env i2 n p s) := by
  intro j
  have h1 := pre87_step_new (calls := calls) hpc hn hi hbit
  have h2 := pre87new_step (calls := calls)
    (env := pre87Env env i2 n)
    (s := { s with pc := "for.body87.i.i.preheader.new",
                     pre := some "for.body87.i.i.preheader" })
    rfl (pre87Env_61 (env := env) (i2 := i2) (n := n)) (pre87Env_p hp)
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]
  simp only [pre87BodyState, stateAt]

/-- The dispatch's copy edge leaves the preheader's cursor: `if.end83.i.i`'s arm
lands on `end83Env`, whose second cell is `%i.2.i.i`. -/
theorem end83Env_i2 {env : Env} {esign : BitVec 1} {i2 n : BitVec 64} :
    lookupName (end83Env env esign i2 n) "%i.2.i.i" = some (.int 64 i2) := by
  simp only [end83Env]
  rw [lookupName_cons_ne _ _ (by decide)]
  exact lookupName_cons_self ..

/-- The dispatch's copy edge keeps `%n`, the preheader's other cell. -/
theorem end83Env_n {env : Env} {esign : BitVec 1} {i2 n nn : BitVec 64}
    (h : lookupName env "%n" = some (.int 64 nn)) :
    lookupName (end83Env env esign i2 n) "%n" = some (.int 64 nn) := by
  simp only [end83Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

/-- The dispatch's copy edge keeps `%p`, the unrolled preheader's base. -/
theorem end83Env_p {env : Env} {esign : BitVec 1} {i2 n : BitVec 64} {p : Nat}
    (h : lookupName env "%p" = some (.ptr p)) :
    lookupName (end83Env env esign i2 n) "%p" = some (.ptr p) := by
  simp only [end83Env]
  rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
    lookupName_cons_ne _ _ (by decide)]
  exact h

/-! ### The outer multiply's exit: `while.end176.i.i`

The block where the `%pow` chunk multiply hands the ladder its start.
`%n.i539.i.i` is the frame's `+ 0x608` field, set at `if.end151.i.i`; the store
spills the group count `%inc12.us.i.i581758.i.i` back into it.  The test is the
residual group's own: `%sub175.i.i` is `%k168.0762.i.i - 19`, so the word is zero
exactly at nineteen groups, and that arm opens `if.end198.i.i` — the block that
forms the ladder's two inputs — while a non-zero word takes `if.then178.i.i`'s
`stk_mul_u64`.

Both steps are at the block's own pin, and `end176_run_ladder` composes the
exit's step with `NumFastTier3Fold.t3_fold_step`, so the interior that starts at
the copy's entry has its far end: the run it owes `FbCopyEntryPos` continues
from this block's word into `while.cond203.i.i` without re-deriving the fold's
block.  The store binds no cell, so the two lookups below are the incoming ones.
-/

/-- A four-byte store: `store i32 %v, ptr %p` at the word the address names. -/
theorem denoteCode_store32 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 32} {a : Nat}
    (hv : lookupName env v = some (.int 32 x))
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.reg v) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hs : storeValue (stateAt env s) (.int 32) (.int 32 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [storeValue, stateAt, show (32 + 7) / 8 = 4 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 32 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
      (hv := evalOperand_reg_of env s v (.int 32 x) hv)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- The block's instructions. -/
def end176Instrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i581758.i.i")
     (Operand.reg "%n.i539.i.i"),
   Instr.icmp "%tobool177.not.i.i" (IPred.eq) 64 (Operand.reg "%sub175.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem end176_find :
    numFastBody.findBlock "while.end176.i.i" =
      some ⟨"while.end176.i.i", end176Instrs,
        Term.condbr (Operand.reg "%tobool177.not.i.i") "if.end198.i.i"
          "if.then178.i.i"⟩ := by
  simpa only [end176Instrs] using numFast_findBlock_while_end176_i_i

/-- The environment the block leaves: the residual test's bit in front of the
incoming cells. -/
def end176Env (env : Env) (r : BitVec 64) : Env :=
  ("%tobool177.not.i.i", .int 1 (evalICmp .eq r 0x0#64)) :: env

/-- A lookup through the cell the block binds. -/
theorem end176Env_lookup {env : Env} {r : BitVec 64} {d : String} {v : Value}
    (h : lookupName env d = some v) (hne : d ≠ "%tobool177.not.i.i") :
    lookupName (end176Env env r) d = some v := by
  have h' : lookupName (("%tobool177.not.i.i", .int 1 (evalICmp .eq r 0x0#64)) :: env) d
      = lookupName env d :=
    lookupName_cons_ne _ _ (Ne.symm hne)
  rw [show end176Env env r
      = ("%tobool177.not.i.i", .int 1 (evalICmp .eq r 0x0#64)) :: env from rfl, h', h]

/-- The block's chain: the count's spill at the frame's `+ 0x608`, then the
residual test. -/
theorem end176_denote {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {n : Nat} {r : BitVec 64}
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r)) :
    denoteCode calls end176Instrs (stateAt env s) =
      some (stateAt (end176Env env r)
        { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) }) := by
  unfold end176Instrs
  rw [denoteCode_store32 calls env s "%inc12.us.i.i581758.i.i" "%n.i539.i.i" hk hn]
  rw [denoteCode_icmp_eq_imm calls env
    { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) }
    "%tobool177.not.i.i" "%sub175.i.i" hr]
  simp only [denoteCode_nil, end176Env, stateAt]

/-- **The exit step: the residual group is empty.**  The count is spilled and the
run continues at `if.end198.i.i`, the block that forms the ladder's inputs. -/
theorem end176_step_end {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {n : Nat} {r : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hbit : evalICmp .eq r 0x0#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end176Env env r)
        { s with mem := writeBytes s.mem n (natToBytes k.toNat 4),
                 pc := "if.end198.i.i", pre := some "while.end176.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end176Env env r)
      { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) })
    (b := ⟨"while.end176.i.i", end176Instrs,
      Term.condbr (Operand.reg "%tobool177.not.i.i") "if.end198.i.i"
        "if.then178.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end176_find
  · simpa only [stateAt] using end176_denote (calls := calls) hk hn hr
  · rw [numFast_execTerm_condbr_one (s := stateAt (end176Env env r)
        { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) })
      "%tobool177.not.i.i" "if.end198.i.i" "if.then178.i.i"
      (by simp [end176Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- **The exit step: a residual group is left.**  The count is spilled and the
run continues at `if.then178.i.i`, the table row's `stk_mul_u64`. -/
theorem end176_step_then {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {n : Nat} {r : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hbit : evalICmp .eq r 0x0#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end176Env env r)
        { s with mem := writeBytes s.mem n (natToBytes k.toNat 4),
                 pc := "if.then178.i.i", pre := some "while.end176.i.i" }) := by
  refine numFast_step_at (s' := stateAt (end176Env env r)
      { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) })
    (b := ⟨"while.end176.i.i", end176Instrs,
      Term.condbr (Operand.reg "%tobool177.not.i.i") "if.end198.i.i"
        "if.then178.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end176_find
  · simpa only [stateAt] using end176_denote (calls := calls) hk hn hr
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end176Env env r)
        { s with mem := writeBytes s.mem n (natToBytes k.toNat 4) })
      "%tobool177.not.i.i" "if.end198.i.i" "if.then178.i.i"
      (by simp [end176Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The spill reads back: the four bytes the block writes at the frame's
`+ 0x608` field are the count it held. -/
theorem end176_store_read {m : Mem} {k : BitVec 32} {n : Nat} :
    readBytes (writeBytes m n (natToBytes k.toNat 4)) n 4
      = some (natToBytes k.toNat 4) := by
  have h := readBytes_writeBytes_same m (natToBytes k.toNat 4) (addr := n)
  rwa [natToBytes_length] at h

/-- The ladder's full run leaves no residual group: `%sub175.i.i` is `%k - 19`,
and at nineteen the residual is empty — the bit that opens `if.end198.i.i`. -/
theorem end176_residual_empty :
    (0x0000000000000013#64 + 0xffffffffffffffed#64) = (0x0#64 : BitVec 64) := by
  decide

/-- **The exit's run into the ladder's head.**  From `while.end176.i.i` with an
empty residual, the two control steps reach `while.cond203.i.i` with the fold's
environment — the residual exponent and the widened head — and the spilled
count's memory.  This is the far end of the interior `FbCopyEntryPos` states. -/
theorem end176_run_ladder {calls : Calls} {env : Env} {s : State}
    {k : BitVec 32} {n : Nat} {r u re top : BitVec 64}
    (hpc : s.pc = "while.end176.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n))
    (hk : lookupName env "%inc12.us.i.i581758.i.i" = some (.int 32 k))
    (hr : lookupName env "%sub175.i.i" = some (.int 64 r))
    (hu : lookupName env "%add110.i.i" = some (.int 64 u))
    (htn : lookupName env "%topn.0711.i.i" = some (.int 64 re))
    (ht : lookupName env "%top.0709.i.i" = some (.int 64 top))
    (hbit : evalICmp .eq r 0x0#64 = (1 : BitVec 1)) :
    ∀ j, runFuel calls (2 + j) numFastBody (stateAt env s) =
      runFuel calls j numFastBody
        (stateAt (NumFastTier3Fold.t3FoldEnv (end176Env env r) u re top.toNat)
          { s with pc := "while.cond203.i.i", pre := some "if.end198.i.i",
                   mem := writeBytes s.mem n (natToBytes k.toNat 4) }) := by
  intro j
  have h1 := end176_step_end (calls := calls) hpc hn hk hr hbit
  have h2 := NumFastTier3Fold.t3_fold_step (calls := calls)
    (env := end176Env env r)
    (s := { s with mem := writeBytes s.mem n (natToBytes k.toNat 4), pc := "if.end198.i.i", pre := some "while.end176.i.i" })
    (u := u) (re := re) (top := top) rfl
    (end176Env_lookup hu (by decide))
    (end176Env_lookup htn (by decide))
    (end176Env_lookup ht (by decide))
  rw [show 2 + j = 1 + (1 + j) from by omega]
  rw [runFuel_jump_prefix h1]
  rw [runFuel_jump_prefix h2]

/-! ### The chunk multiply's spine between the rungs

The region `while.end176.i.i` is the exit of: the chunk loop
`for.body132.i.i`/`for.inc143.i.i` and its `cn < 19` ingest nest, then the
residual test `for.cond.cleanup.i.i`/`if.then148.i.i`, and the staging
`if.end151.i.i` that sets `%pow.i.i = 1` and `%n.i539.i.i = 1`.  From there the
multiply is three routes that all meet at `if.end198.i.i`:

* the sticky route `if.then153.i.i` into the peel `while.body.i.i`, whose merge
  `while.end.i.i` opens the `%92`-count rung `for.body.lr.ph.i.i542.i.i`;
* the negative-exponent route `if.else164.i.i`/`if.then167.i.i` into
  `while.body173.i.i`, its nest and `stk_mul_u64.exit583.i.i`, whose `while.end176.i.i`
  the template already states;
* the non-negative route `while.cond184.preheader.i.i` into `while.body187.i.i`,
  its nest and `stk_mul_u64.exit605.i.i`, whose merge `while.end190.i.i` either
  opens the `%116`-count rung `for.body.lr.ph.i.i608.i.i` or branches to
  `if.end195.i.i`'s zero store.

Each block below carries its instructions at its own captured pin, the
environment its chain leaves, and a step for each edge its successor relation
names.  The four nests' bodies are not restated: the digit-ingest chain's
arithmetic shapes are `JsonStage2NumFastTier3`'s (`t3_epil_denote` and the
width-generic `mul`/`add`/`lshr` steps), and this section states the nest heads
and exits that connect them to the spine.

The `sext` the rung heads need (the `%pow.i.i` index from a 32-bit counter),
and the literal-valued stores the staging and the zeroing write, were not
among the file's generic shapes; they are added once, below.
-/

/-- `%d = sext iN %v to iM`. -/
theorem step_sext (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) :
    evalInstr calls (stateAt env s) (.sext d wIn wOut (.reg v)) =
      some (stateAt ((d, .int wOut (BitVec.ofNat wOut
        (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat)) :: env) s) := by
  simp [evalInstr, evalOperand, stateAt, hv, State.bind]

theorem denoteCode_sext (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) (is : List Instr) :
    denoteCode calls (.sext d wIn wOut (.reg v) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .int wOut (BitVec.ofNat wOut
        (BitVec.signExtend wOut (BitVec.ofNat wIn x.toNat)).toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _ (step_sext calls env s d v wIn wOut hv)]

/-- A store of a 32-bit immediate. -/
theorem denoteCode_store32_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 32) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 32) (.imm (.int 32 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hs : storeValue (stateAt env s) (.int 32) (.int 32 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [storeValue, stateAt, show (32 + 7) / 8 = 4 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 32 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
      (hv := evalOperand_lit_of (stateAt env s) 32 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- A store of a 64-bit immediate. -/
theorem denoteCode_store64_imm (calls : Calls) (env : Env) (s : State)
    (x : BitVec 64) (p : String) {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is) (stateAt env s) =
      denoteCode calls is
        (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  have hs : storeValue (stateAt env s) (.int 64) (.int 64 x) a
      = some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
    simp [storeValue, stateAt, show (64 + 7) / 8 = 8 from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (by
    rw [JsonS1MasksIR.evalInstr_store (s := stateAt env s)
      (vv := .int 64 x) (a := a)
      (s' := stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
      (hv := evalOperand_lit_of (stateAt env s) 64 x)
      (hp := evalOperand_reg_of env s p (.ptr a) hp) (hs := hs)])]

/-- `%d = getelementptr i8, ptr @sym, i64 %off`: the global base's form of the
table read, at an index below `2 ^ 63`. -/
theorem step_gep8_global_reg (calls : Calls) (env : Env) (s : State)
    (d sym off : String) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env sym = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.global sym) (.reg off)) =
      some (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat)) :: env) s) := by
  have hb' : evalOperand (stateAt env s) (.global sym) = some (.ptr a) := by
    simp only [evalOperand, stateAt, hb]
  have h := evalInstr_gep (calls := calls) (s := stateAt env s) (d := d)
    (elemTy := .int 8) (base := (.global sym)) (off := (.reg off)) (a := a)
    (w := 64) (n := idx) hb'
    (evalOperand_reg_of env s off (.int 64 idx) ho) hpos
  simpa only [show (Ty.int 8).sizeBytes = 1 from by decide, Nat.mul_one, stateAt,
    State.bind] using h

theorem denoteCode_gep8_global_reg (calls : Calls) (env : Env) (s : State)
    (d sym off : String) {a : Nat} {idx : BitVec 64}
    (hb : lookupName env sym = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : (idx.signExtend 64).toNat < 2 ^ 63) (is : List Instr) :
    denoteCode calls (.gep d (.int 8) (.global sym) (.reg off) :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, .ptr (a + (idx.signExtend 64).toNat)) :: env) s) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (step_gep8_global_reg calls env s d sym off hb ho hpos)]

/-! #### The chunk loop's exit: `for.cond.cleanup.i.i` and `if.then148.i.i` -/

/-- The count's spill at `%n.i.i.i` and the empty-count test. -/
def cleanupInstrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.reg "%78") (Operand.reg "%n.i.i.i"),
   Instr.icmp "%tobool147.not.i.i" (IPred.eq) 32 (Operand.reg "%cn.1.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem cleanup_find :
    numFastBody.findBlock "for.cond.cleanup.i.i" =
      some ⟨"for.cond.cleanup.i.i", cleanupInstrs,
        Term.condbr (Operand.reg "%tobool147.not.i.i") "if.end151.i.i"
          "if.then148.i.i"⟩ := by
  simpa only [cleanupInstrs] using numFast_findBlock_for_cond_cleanup_i_i

/-- The environment the block leaves: the empty-count test in front of the
incoming cells. -/
def cleanupEnv (env : Env) (c : BitVec 32) : Env :=
  ("%tobool147.not.i.i", .int 1 (evalICmp .eq c 0x00000000#32)) :: env

theorem cleanup_denote {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {a : Nat} {c : BitVec 32}
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c)) :
    denoteCode calls cleanupInstrs (stateAt env s) =
      some (stateAt (cleanupEnv env c)
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  unfold cleanupInstrs
  rw [denoteCode_store32 calls env s "%78" "%n.i.i.i" hx hn]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls env
    { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }
    "%tobool147.not.i.i" "%cn.1.i.i" .eq hc]
  simp only [denoteCode_nil, cleanupEnv, stateAt]

/-- **The cleanup's step: no digits.** -/
theorem cleanup_step_end {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {a : Nat} {c : BitVec 32}
    (hpc : s.pc = "for.cond.cleanup.i.i")
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c))
    (hbit : evalICmp .eq c 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cleanupEnv env c)
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4),
                 pc := "if.end151.i.i", pre := some "for.cond.cleanup.i.i" }) := by
  refine numFast_step_at (s' := stateAt (cleanupEnv env c)
      { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (b := ⟨"for.cond.cleanup.i.i", cleanupInstrs,
      Term.condbr (Operand.reg "%tobool147.not.i.i") "if.end151.i.i"
        "if.then148.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using cleanup_find
  · simpa only [stateAt] using cleanup_denote hx hn hc
  · rw [numFast_execTerm_condbr_one (s := stateAt (cleanupEnv env c)
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
      "%tobool147.not.i.i" "if.end151.i.i" "if.then148.i.i"
      (by simp [cleanupEnv, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- **The cleanup's step: a residual count.** -/
theorem cleanup_step_residue {calls : Calls} {env : Env} {s : State}
    {x : BitVec 32} {a : Nat} {c : BitVec 32}
    (hpc : s.pc = "for.cond.cleanup.i.i")
    (hx : lookupName env "%78" = some (.int 32 x))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a))
    (hc : lookupName env "%cn.1.i.i" = some (.int 32 c))
    (hbit : evalICmp .eq c 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cleanupEnv env c)
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4),
                 pc := "if.then148.i.i", pre := some "for.cond.cleanup.i.i" }) := by
  refine numFast_step_at (s' := stateAt (cleanupEnv env c)
      { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
    (b := ⟨"for.cond.cleanup.i.i", cleanupInstrs,
      Term.condbr (Operand.reg "%tobool147.not.i.i") "if.end151.i.i"
        "if.then148.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using cleanup_find
  · simpa only [stateAt] using cleanup_denote hx hn hc
  · rw [numFast_execTerm_condbr_zero (s := stateAt (cleanupEnv env c)
        { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) })
      "%tobool147.not.i.i" "if.end151.i.i" "if.then148.i.i"
      (by simp [cleanupEnv, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The residual count's chunk widen and its nonzero test. -/
def then148Instrs : List Instr :=
  [Instr.zext "%conv.i514.i.i" 64 128 (Operand.reg "%chunk.1.i.i"),
   Instr.icmp "%cmp28.i516.i.i" (IPred.sgt) 32 (Operand.reg "%78")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem then148_find :
    numFastBody.findBlock "if.then148.i.i" =
      some ⟨"if.then148.i.i", then148Instrs,
        Term.condbr (Operand.reg "%cmp28.i516.i.i") "for.body.lr.ph.i525.i.i"
          "while.cond.preheader.i517.i.i"⟩ := by
  simpa only [then148Instrs] using numFast_findBlock_if_then148_i_i

/-- The environment the block leaves: the widen and the count's test. -/
def then148Env (env : Env) (c : BitVec 32) (chunk : BitVec 64) : Env :=
  ("%cmp28.i516.i.i", .int 1 (evalICmp .sgt c 0x00000000#32)) ::
  ("%conv.i514.i.i", .int 128 (BitVec.ofNat 128 chunk.toNat)) :: env

theorem then148_denote {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {chunk : BitVec 64}
    (hc : lookupName env "%78" = some (.int 32 c))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk)) :
    denoteCode calls then148Instrs (stateAt env s) =
      some (stateAt (then148Env env c chunk) s) := by
  unfold then148Instrs
  rw [denoteCode_zext calls env s "%conv.i514.i.i" "%chunk.1.i.i" 64 128 hchunk]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%conv.i514.i.i", .int 128 (BitVec.ofNat 128 chunk.toNat)) :: env) s
    "%cmp28.i516.i.i" "%78" .sgt
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hc)]
  simp only [denoteCode_nil, then148Env, stateAt]

/-- **The residue's step into the `%cn`-count rung.** -/
theorem then148_step_nest {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {chunk : BitVec 64}
    (hpc : s.pc = "if.then148.i.i")
    (hc : lookupName env "%78" = some (.int 32 c))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk))
    (hbit : evalICmp .sgt c 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then148Env env c chunk)
        { s with pc := "for.body.lr.ph.i525.i.i", pre := some "if.then148.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then148Env env c chunk) s)
    (b := ⟨"if.then148.i.i", then148Instrs,
      Term.condbr (Operand.reg "%cmp28.i516.i.i") "for.body.lr.ph.i525.i.i"
        "while.cond.preheader.i517.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then148_find
  · simpa only [stateAt] using then148_denote hc hchunk
  · rw [numFast_execTerm_condbr_one (s := stateAt (then148Env env c chunk) s)
      "%cmp28.i516.i.i" "for.body.lr.ph.i525.i.i" "while.cond.preheader.i517.i.i"
      (by simp [then148Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- **The residue's step past the rung: the chunk is zero.** -/
theorem then148_step_carry {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {chunk : BitVec 64}
    (hpc : s.pc = "if.then148.i.i")
    (hc : lookupName env "%78" = some (.int 32 c))
    (hchunk : lookupName env "%chunk.1.i.i" = some (.int 64 chunk))
    (hbit : evalICmp .sgt c 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then148Env env c chunk)
        { s with pc := "while.cond.preheader.i517.i.i", pre := some "if.then148.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then148Env env c chunk) s)
    (b := ⟨"if.then148.i.i", then148Instrs,
      Term.condbr (Operand.reg "%cmp28.i516.i.i") "for.body.lr.ph.i525.i.i"
        "while.cond.preheader.i517.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then148_find
  · simpa only [stateAt] using then148_denote hc hchunk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (then148Env env c chunk) s)
      "%cmp28.i516.i.i" "for.body.lr.ph.i525.i.i" "while.cond.preheader.i517.i.i"
      (by simp [then148Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! #### The staging: `if.end151.i.i.sink.split` and `if.end151.i.i` -/

/-- The rung's counter spill: the `phi` and `store i32`. -/
def sinkSplitSpecs : List PhiSpec :=
  [{ dst := "%inc12.us.i522.i.i.sink", ty := Ty.int 32,
     incoming := [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
                  ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] }]

def sinkSplitInstrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i522.i.i.sink")
     (Operand.reg "%n.i.i.i")]

def sinkSplitBlock : List Instr := sinkSplitSpecs.map PhiSpec.instr ++ sinkSplitInstrs

theorem sinkSplit_find :
    numFastBody.findBlock "if.end151.i.i.sink.split" =
      some ⟨"if.end151.i.i.sink.split", sinkSplitBlock, Term.br "if.end151.i.i"⟩ := by
  simp only [sinkSplitBlock, sinkSplitInstrs, sinkSplitSpecs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_if_end151_i_i_sink_split

theorem sinkSplit_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {a : Nat}
    (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a)) :
    denoteCode calls sinkSplitBlock (stateAt env s) =
      some (stateAt (("%inc12.us.i522.i.i.sink", .int 32 k) :: env)
        { s with mem := writeBytes s.mem a (natToBytes k.toNat 4) }) := by
  have hsel : PhiSelects (stateAt env s) pre sinkSplitSpecs
      [("%inc12.us.i522.i.i.sink", .int 32 k)] := by
    simp only [sinkSplitSpecs]
    constructor
    · exact hop
    · exact hov
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := sinkSplitSpecs) (vs := [("%inc12.us.i522.i.i.sink", .int 32 k)])
    (rest := sinkSplitInstrs) hpre hsel (by decide)
  unfold sinkSplitBlock
  rw [h]
  simp only [runCells]
  unfold sinkSplitInstrs
  rw [denoteCode_store32 calls (("%inc12.us.i522.i.i.sink", .int 32 k) :: env) s
    "%inc12.us.i522.i.i.sink" "%n.i.i.i" (lookupName_cons_self ..) hn]
  simp only [denoteCode_nil, stateAt]

/-- **The spill's step into the staging.** -/
theorem sinkSplit_step {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {a : Nat}
    (hpc : s.pc = "if.end151.i.i.sink.split") (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body.us.i520.i.i", (Operand.reg "%inc12.us.i522.i.i")),
       ("if.end126.i.i", (Operand.imm (Const.int 32 0x00000000#32)))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (("%inc12.us.i522.i.i.sink", .int 32 k) :: env)
        { s with mem := writeBytes s.mem a (natToBytes k.toNat 4),
                 pc := "if.end151.i.i", pre := some "if.end151.i.i.sink.split" }) := by
  refine numFast_step_at (s' := stateAt (("%inc12.us.i522.i.i.sink", .int 32 k) :: env)
      { s with mem := writeBytes s.mem a (natToBytes k.toNat 4) })
    (b := ⟨"if.end151.i.i.sink.split", sinkSplitBlock, Term.br "if.end151.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using sinkSplit_find
  · simpa only [stateAt] using sinkSplit_denote hpre hop hov hn
  · simp only [execTerm, stateAt, hpc]

/-- The two staging stores and the sticky test. -/
def end151Instrs : List Instr :=
  [Instr.gep "%pow.i.i" (Ty.int 8) (Operand.reg "%v.i.i")
     (Operand.imm (Const.int 64 0x0000000000000308#64)),
   Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000001#64))
     (Operand.reg "%pow.i.i"),
   Instr.gep "%n.i539.i.i" (Ty.int 8) (Operand.reg "%v.i.i")
     (Operand.imm (Const.int 64 0x0000000000000608#64)),
   Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32))
     (Operand.reg "%n.i539.i.i"),
   Instr.icmp "%tobool152.not.i.i" (IPred.eq) 32 (Operand.reg "%sticky.0714.i.i")
     (Operand.imm (Const.int 32 0x00000000#32))]

theorem end151_find :
    numFastBody.findBlock "if.end151.i.i" =
      some ⟨"if.end151.i.i", end151Instrs,
        Term.condbr (Operand.reg "%tobool152.not.i.i") "if.else164.i.i"
          "if.then153.i.i"⟩ := by
  simpa only [end151Instrs] using numFast_findBlock_if_end151_i_i

/-- The staging's environment: the power and count pointers, and the sticky
test. -/
def end151Env (env : Env) (v : Nat) (st : BitVec 32) : Env :=
  ("%tobool152.not.i.i", .int 1 (evalICmp .eq st 0x00000000#32)) ::
  ("%n.i539.i.i", .ptr (v + ((0x0000000000000608#64).signExtend 64).toNat)) ::
  ("%pow.i.i", .ptr (v + ((0x0000000000000308#64).signExtend 64).toNat)) :: env

theorem end151_denote {calls : Calls} {env : Env} {s : State}
    {v : Nat} {st : BitVec 32}
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st)) :
    denoteCode calls end151Instrs (stateAt env s) =
      some (stateAt (end151Env env v st)
        { s with
            mem := writeBytes (writeBytes s.mem
              (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
              (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) }) := by
  unfold end151Instrs
  rw [JsonScanLane.denoteCode_gep8_lit_w calls env s "%pow.i.i" "%v.i.i" hv (by decide)]
  rw [denoteCode_store64_imm calls
    (("%pow.i.i", .ptr (v + ((0x0000000000000308#64).signExtend 64).toNat)) :: env) s
    0x0000000000000001#64 "%pow.i.i" (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_gep8_lit_w calls (("%pow.i.i",
      .ptr (v + ((0x0000000000000308#64).signExtend 64).toNat)) :: env)
    { s with
        mem := writeBytes s.mem
          (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8) }
    "%n.i539.i.i" "%v.i.i" (by rw [lookupName_cons_ne _ _ (by decide)]; exact hv)
    (by decide)]
  rw [denoteCode_store32_imm calls (("%n.i539.i.i",
      .ptr (v + ((0x0000000000000608#64).signExtend 64).toNat)) ::
      ("%pow.i.i", .ptr (v + ((0x0000000000000308#64).signExtend 64).toNat)) :: env)
    { s with
        mem := writeBytes s.mem
          (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8) }
    0x00000001#32 "%n.i539.i.i" (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%n.i539.i.i", .ptr (v + ((0x0000000000000608#64).signExtend 64).toNat)) ::
      ("%pow.i.i", .ptr (v + ((0x0000000000000308#64).signExtend 64).toNat)) :: env)
    { s with
        mem := writeBytes (writeBytes s.mem
          (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
          (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) }
    "%tobool152.not.i.i" "%sticky.0714.i.i" .eq
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hst)]
  simp only [denoteCode_nil, end151Env, stateAt]

/-- **The staging's step into the negative-exponent branch.** -/
theorem end151_step_else {calls : Calls} {env : Env} {s : State}
    {v : Nat} {st : BitVec 32}
    (hpc : s.pc = "if.end151.i.i")
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st))
    (hbit : evalICmp .eq st 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end151Env env v st)
        { s with pc := "if.else164.i.i", pre := some "if.end151.i.i",
                 mem := writeBytes (writeBytes s.mem
                   (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
                   (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) }) := by
  refine numFast_step_at (s' := stateAt (end151Env env v st)
      { s with
          mem := writeBytes (writeBytes s.mem
            (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
            (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) })
    (b := ⟨"if.end151.i.i", end151Instrs,
      Term.condbr (Operand.reg "%tobool152.not.i.i") "if.else164.i.i"
        "if.then153.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end151_find
  · simpa only [stateAt] using end151_denote hv hst
  · rw [numFast_execTerm_condbr_one (s := stateAt (end151Env env v st)
        { s with
            mem := writeBytes (writeBytes s.mem
              (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
              (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) })
      "%tobool152.not.i.i" "if.else164.i.i" "if.then153.i.i"
      (by simp only [end151Env, stateAt]; exact lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-- **The staging's step into the sticky branch.** -/
theorem end151_step_then {calls : Calls} {env : Env} {s : State}
    {v : Nat} {st : BitVec 32}
    (hpc : s.pc = "if.end151.i.i")
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hst : lookupName env "%sticky.0714.i.i" = some (.int 32 st))
    (hbit : evalICmp .eq st 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (end151Env env v st)
        { s with pc := "if.then153.i.i", pre := some "if.end151.i.i",
                 mem := writeBytes (writeBytes s.mem
                   (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
                   (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) }) := by
  refine numFast_step_at (s' := stateAt (end151Env env v st)
      { s with
          mem := writeBytes (writeBytes s.mem
            (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
            (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) })
    (b := ⟨"if.end151.i.i", end151Instrs,
      Term.condbr (Operand.reg "%tobool152.not.i.i") "if.else164.i.i"
        "if.then153.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end151_find
  · simpa only [stateAt] using end151_denote hv hst
  · rw [numFast_execTerm_condbr_zero (s := stateAt (end151Env env v st)
        { s with
            mem := writeBytes (writeBytes s.mem
              (v + ((0x0000000000000308#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#64).toNat 8))
              (v + ((0x0000000000000608#64).signExtend 64).toNat) (natToBytes (0x0000000000000001#32).toNat 4) })
      "%tobool152.not.i.i" "if.else164.i.i" "if.then153.i.i"
      (by simp only [end151Env, stateAt]; exact lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! #### The three routes: `if.then153.i.i`, `if.else164.i.i`, `if.then167.i.i` -/

/-- The sticky route's negated exponent and its `> 26` test. -/
def then153Instrs : List Instr :=
  [Instr.binop "%sub154.i.i" (BinOp.sub) 64
     (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
   Instr.icmp "%cmp155746.i.i" (IPred.sgt) 64 (Operand.reg "%sub154.i.i")
     (Operand.imm (Const.int 64 0x000000000000001a#64))]

theorem then153_find :
    numFastBody.findBlock "if.then153.i.i" =
      some ⟨"if.then153.i.i", then153Instrs,
        Term.condbr (Operand.reg "%cmp155746.i.i") "while.body.i.i"
          "while.end.thread.i.i"⟩ := by
  simpa only [then153Instrs] using numFast_findBlock_if_then153_i_i

def then153Env (env : Env) (a : BitVec 64) : Env :=
  ("%cmp155746.i.i", .int 1 (evalICmp .sgt (0x0000000000000000#64 - a)
    0x000000000000001a#64)) ::
  ("%sub154.i.i", .int 64 (0x0000000000000000#64 - a)) :: env

theorem then153_denote {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (ha : lookupName env "%add108.i.i" = some (.int 64 a)) :
    denoteCode calls then153Instrs (stateAt env s) =
      some (stateAt (then153Env env a) s) := by
  unfold then153Instrs
  rw [denoteCode_sub_lit calls env s "%sub154.i.i" "%add108.i.i" ha]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%sub154.i.i", .int 64 (0x0000000000000000#64 - a)) :: env) s
    "%cmp155746.i.i" "%sub154.i.i" .sgt (lookupName_cons_self ..)]
  simp only [denoteCode_nil, then153Env, stateAt]

theorem then153_step_peel {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.then153.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .sgt (0x0000000000000000#64 - a) 0x000000000000001a#64
      = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then153Env env a)
        { s with pc := "while.body.i.i", pre := some "if.then153.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then153Env env a) s)
    (b := ⟨"if.then153.i.i", then153Instrs,
      Term.condbr (Operand.reg "%cmp155746.i.i") "while.body.i.i"
        "while.end.thread.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then153_find
  · simpa only [stateAt] using then153_denote ha
  · rw [numFast_execTerm_condbr_one (s := stateAt (then153Env env a) s)
      "%cmp155746.i.i" "while.body.i.i" "while.end.thread.i.i"
      (by simp [then153Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem then153_step_thread {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.then153.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .sgt (0x0000000000000000#64 - a) 0x000000000000001a#64
      = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then153Env env a)
        { s with pc := "while.end.thread.i.i", pre := some "if.then153.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then153Env env a) s)
    (b := ⟨"if.then153.i.i", then153Instrs,
      Term.condbr (Operand.reg "%cmp155746.i.i") "while.body.i.i"
        "while.end.thread.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then153_find
  · simpa only [stateAt] using then153_denote ha
  · rw [numFast_execTerm_condbr_zero (s := stateAt (then153Env env a) s)
      "%cmp155746.i.i" "while.body.i.i" "while.end.thread.i.i"
      (by simp [then153Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The staging's else branch: the exponent's sign test. -/
def else164Instrs : List Instr :=
  [Instr.icmp "%cmp165.i.i" (IPred.slt) 64 (Operand.reg "%add108.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

theorem else164_find :
    numFastBody.findBlock "if.else164.i.i" =
      some ⟨"if.else164.i.i", else164Instrs,
        Term.condbr (Operand.reg "%cmp165.i.i") "if.then167.i.i"
          "while.cond184.preheader.i.i"⟩ := by
  simpa only [else164Instrs] using numFast_findBlock_if_else164_i_i

def else164Env (env : Env) (a : BitVec 64) : Env :=
  ("%cmp165.i.i", .int 1 (evalICmp .slt a 0x0000000000000000#64)) :: env

theorem else164_denote {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (ha : lookupName env "%add108.i.i" = some (.int 64 a)) :
    denoteCode calls else164Instrs (stateAt env s) =
      some (stateAt (else164Env env a) s) := by
  unfold else164Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls env s "%cmp165.i.i" "%add108.i.i" .slt ha]
  simp only [denoteCode_nil, else164Env, stateAt]

theorem else164_step_negative {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.else164.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .slt a 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (else164Env env a)
        { s with pc := "if.then167.i.i", pre := some "if.else164.i.i" }) := by
  refine numFast_step_at (s' := stateAt (else164Env env a) s)
    (b := ⟨"if.else164.i.i", else164Instrs,
      Term.condbr (Operand.reg "%cmp165.i.i") "if.then167.i.i"
        "while.cond184.preheader.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using else164_find
  · simpa only [stateAt] using else164_denote ha
  · rw [numFast_execTerm_condbr_one (s := stateAt (else164Env env a) s)
      "%cmp165.i.i" "if.then167.i.i" "while.cond184.preheader.i.i"
      (by simp [else164Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem else164_step_positive {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.else164.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .slt a 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (else164Env env a)
        { s with pc := "while.cond184.preheader.i.i", pre := some "if.else164.i.i" }) := by
  refine numFast_step_at (s' := stateAt (else164Env env a) s)
    (b := ⟨"if.else164.i.i", else164Instrs,
      Term.condbr (Operand.reg "%cmp165.i.i") "if.then167.i.i"
        "while.cond184.preheader.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using else164_find
  · simpa only [stateAt] using else164_denote ha
  · rw [numFast_execTerm_condbr_zero (s := stateAt (else164Env env a) s)
      "%cmp165.i.i" "if.then167.i.i" "while.cond184.preheader.i.i"
      (by simp [else164Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The negative route's negated exponent and its `> 18` test. -/
def then167Instrs : List Instr :=
  [Instr.binop "%sub169.i.i" (BinOp.sub) 64
     (Operand.imm (Const.int 64 0x0000000000000000#64)) (Operand.reg "%add108.i.i"),
   Instr.icmp "%cmp171760.i.i" (IPred.sgt) 64 (Operand.reg "%sub169.i.i")
     (Operand.imm (Const.int 64 0x0000000000000012#64))]

theorem then167_find :
    numFastBody.findBlock "if.then167.i.i" =
      some ⟨"if.then167.i.i", then167Instrs,
        Term.condbr (Operand.reg "%cmp171760.i.i") "while.body173.i.i"
          "while.end176.thread.i.i"⟩ := by
  simpa only [then167Instrs] using numFast_findBlock_if_then167_i_i

def then167Env (env : Env) (a : BitVec 64) : Env :=
  ("%cmp171760.i.i", .int 1 (evalICmp .sgt (0x0000000000000000#64 - a)
    0x0000000000000012#64)) ::
  ("%sub169.i.i", .int 64 (0x0000000000000000#64 - a)) :: env

theorem then167_denote {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (ha : lookupName env "%add108.i.i" = some (.int 64 a)) :
    denoteCode calls then167Instrs (stateAt env s) =
      some (stateAt (then167Env env a) s) := by
  unfold then167Instrs
  rw [denoteCode_sub_lit calls env s "%sub169.i.i" "%add108.i.i" ha]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%sub169.i.i", .int 64 (0x0000000000000000#64 - a)) :: env) s
    "%cmp171760.i.i" "%sub169.i.i" .sgt (lookupName_cons_self ..)]
  simp only [denoteCode_nil, then167Env, stateAt]

theorem then167_step_body {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.then167.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .sgt (0x0000000000000000#64 - a) 0x0000000000000012#64
      = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then167Env env a)
        { s with pc := "while.body173.i.i", pre := some "if.then167.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then167Env env a) s)
    (b := ⟨"if.then167.i.i", then167Instrs,
      Term.condbr (Operand.reg "%cmp171760.i.i") "while.body173.i.i"
        "while.end176.thread.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then167_find
  · simpa only [stateAt] using then167_denote ha
  · rw [numFast_execTerm_condbr_one (s := stateAt (then167Env env a) s)
      "%cmp171760.i.i" "while.body173.i.i" "while.end176.thread.i.i"
      (by simp [then167Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem then167_step_thread {calls : Calls} {env : Env} {s : State}
    {a : BitVec 64} (hpc : s.pc = "if.then167.i.i")
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .sgt (0x0000000000000000#64 - a) 0x0000000000000012#64
      = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (then167Env env a)
        { s with pc := "while.end176.thread.i.i", pre := some "if.then167.i.i" }) := by
  refine numFast_step_at (s' := stateAt (then167Env env a) s)
    (b := ⟨"if.then167.i.i", then167Instrs,
      Term.condbr (Operand.reg "%cmp171760.i.i") "while.body173.i.i"
        "while.end176.thread.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using then167_find
  · simpa only [stateAt] using then167_denote ha
  · rw [numFast_execTerm_condbr_zero (s := stateAt (then167Env env a) s)
      "%cmp171760.i.i" "while.body173.i.i" "while.end176.thread.i.i"
      (by simp [then167Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The negative route's fallback: the count's `1` store, then `if.then178.i.i`. -/
def end176ThreadInstrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.imm (Const.int 32 0x00000001#32))
     (Operand.reg "%n.i539.i.i")]

theorem end176Thread_find :
    numFastBody.findBlock "while.end176.thread.i.i" =
      some ⟨"while.end176.thread.i.i", end176ThreadInstrs,
        Term.br "if.then178.i.i"⟩ := by
  simpa only [end176ThreadInstrs] using numFast_findBlock_while_end176_thread_i_i

theorem end176Thread_denote {calls : Calls} {env : Env} {s : State} {n : Nat}
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    denoteCode calls end176ThreadInstrs (stateAt env s) =
      some (stateAt env
        { s with mem := writeBytes s.mem n (natToBytes (0x00000001#32).toNat 4) }) := by
  unfold end176ThreadInstrs
  rw [denoteCode_store32_imm calls env s 0x00000001#32 "%n.i539.i.i" hn]
  simp only [denoteCode_nil, stateAt]

theorem end176Thread_step {calls : Calls} {env : Env} {s : State} {n : Nat}
    (hpc : s.pc = "while.end176.thread.i.i")
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env
        { s with mem := writeBytes s.mem n (natToBytes (0x00000001#32).toNat 4),
                 pc := "if.then178.i.i", pre := some "while.end176.thread.i.i" }) := by
  refine numFast_step_at (s' := stateAt env
      { s with mem := writeBytes s.mem n (natToBytes (0x00000001#32).toNat 4) })
    (b := ⟨"while.end176.thread.i.i", end176ThreadInstrs, Term.br "if.then178.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end176Thread_find
  · simpa only [stateAt] using end176Thread_denote hn
  · simp only [execTerm, stateAt, hpc]

/-! #### The negative route's loop: `while.body173.i.i` and its exit

The block is the rung's test: the two `phi`s carry the residual index and the
group count from `if.then167.i.i` and from the rung's own exit
`stk_mul_u64.exit583.i.i`, and the `> 0` test decides between the digit-ingest
nest and that exit. (`stk_mul_u64.exit583.i.i` is `JsonStage2NumFastTier3PeelTie`'s
`t3TieExit`, whose two steps this block's two edges meet.)
-/

def body173Specs : List PhiSpec :=
  [{ dst := "%k168.0762.i.i", ty := Ty.int 64,
     incoming := [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
                  ("if.then167.i.i", (Operand.reg "%sub169.i.i"))] },
   { dst := "%inc12.us.i.i581759761.i.i", ty := Ty.int 32,
     incoming := [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
                  ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] }]

def body173Instrs : List Instr :=
  [Instr.icmp "%cmp28.i.i563.i.i" (IPred.sgt) 32
     (Operand.reg "%inc12.us.i.i581759761.i.i") (Operand.imm (Const.int 32 0x00000000#32))]

def body173Block : List Instr := body173Specs.map PhiSpec.instr ++ body173Instrs

theorem body173_find :
    numFastBody.findBlock "while.body173.i.i" =
      some ⟨"while.body173.i.i", body173Block,
        Term.condbr (Operand.reg "%cmp28.i.i563.i.i") "for.body.lr.ph.i.i564.i.i"
          "stk_mul_u64.exit583.i.i"⟩ := by
  simp only [body173Block, body173Instrs, body173Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_body173_i_i

def body173Env (env : Env) (kk : BitVec 64) (c : BitVec 32) : Env :=
  ("%cmp28.i.i563.i.i", .int 1 (evalICmp .sgt c 0x00000000#32)) ::
  ("%inc12.us.i.i581759761.i.i", .int 32 c) ::
  ("%k168.0762.i.i", .int 64 kk) :: env

theorem body173_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
       ("if.then167.i.i", (Operand.reg "%sub169.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
       ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c)) :
    denoteCode calls body173Block (stateAt env s) =
      some (stateAt (body173Env env kk c) s) := by
  have hsel : PhiSelects (stateAt env s) pre body173Specs
      [("%k168.0762.i.i", .int 64 kk),
       ("%inc12.us.i.i581759761.i.i", .int 32 c)] := by
    simp only [body173Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := body173Specs)
    (vs := [("%k168.0762.i.i", .int 64 kk),
      ("%inc12.us.i.i581759761.i.i", .int 32 c)])
    (rest := body173Instrs) hpre hsel (by decide)
  unfold body173Block
  rw [h]
  simp only [runCells]
  unfold body173Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%inc12.us.i.i581759761.i.i", .int 32 c) ::
      ("%k168.0762.i.i", .int 64 kk) :: env) s
    "%cmp28.i.i563.i.i" "%inc12.us.i.i581759761.i.i" .sgt (lookupName_cons_self ..)]
  simp only [denoteCode_nil, body173Env, stateAt]

theorem body173_step_nest {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "while.body173.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
       ("if.then167.i.i", (Operand.reg "%sub169.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
       ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c))
    (hbit : evalICmp .sgt c 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body173Env env kk c)
        { s with pc := "for.body.lr.ph.i.i564.i.i", pre := some "while.body173.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body173Env env kk c) s)
    (b := ⟨"while.body173.i.i", body173Block,
      Term.condbr (Operand.reg "%cmp28.i.i563.i.i") "for.body.lr.ph.i.i564.i.i"
        "stk_mul_u64.exit583.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body173_find
  · simpa only [stateAt] using body173_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_one (s := stateAt (body173Env env kk c) s)
      "%cmp28.i.i563.i.i" "for.body.lr.ph.i.i564.i.i" "stk_mul_u64.exit583.i.i"
      (by simp [body173Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem body173_step_exit {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "while.body173.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%sub175.i.i")),
       ("if.then167.i.i", (Operand.reg "%sub169.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit583.i.i", (Operand.reg "%inc12.us.i.i581758.i.i")),
       ("if.then167.i.i", (Operand.imm (Const.int 32 0x00000001#32)))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c))
    (hbit : evalICmp .sgt c 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body173Env env kk c)
        { s with pc := "stk_mul_u64.exit583.i.i", pre := some "while.body173.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body173Env env kk c) s)
    (b := ⟨"while.body173.i.i", body173Block,
      Term.condbr (Operand.reg "%cmp28.i.i563.i.i") "for.body.lr.ph.i.i564.i.i"
        "stk_mul_u64.exit583.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body173_find
  · simpa only [stateAt] using body173_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_zero (s := stateAt (body173Env env kk c) s)
      "%cmp28.i.i563.i.i" "for.body.lr.ph.i.i564.i.i" "stk_mul_u64.exit583.i.i"
      (by simp [body173Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! #### The non-negative route's head: `while.cond184.preheader.i.i` -/

def cond184Instrs : List Instr :=
  [Instr.load "%n.i.promoted751.i.i" (Ty.int 32) (Operand.reg "%n.i.i.i"),
   Instr.icmp "%cmp185753.i.i" (IPred.ugt) 64 (Operand.reg "%add108.i.i")
     (Operand.imm (Const.int 64 0x0000000000000012#64))]

theorem cond184_find :
    numFastBody.findBlock "while.cond184.preheader.i.i" =
      some ⟨"while.cond184.preheader.i.i", cond184Instrs,
        Term.condbr (Operand.reg "%cmp185753.i.i") "while.body187.i.i"
          "while.end190.i.i"⟩ := by
  simpa only [cond184Instrs] using numFast_findBlock_while_cond184_preheader_i_i

def cond184Env (env : Env) (w : BitVec 32) (a : BitVec 64) : Env :=
  ("%cmp185753.i.i", .int 1 (evalICmp .ugt a 0x0000000000000012#64)) ::
  ("%n.i.promoted751.i.i", .int 32 w) :: env

theorem cond184_denote {calls : Calls} {env : Env} {s : State}
    {w : BitVec 32} {a : BitVec 64} {n : Nat}
    (hn : lookupName env "%n.i.i.i" = some (.ptr n))
    (hw : readBytes s.mem n 4 = some (natToBytes w.toNat 4))
    (ha : lookupName env "%add108.i.i" = some (.int 64 a)) :
    denoteCode calls cond184Instrs (stateAt env s) =
      some (stateAt (cond184Env env w a) s) := by
  unfold cond184Instrs
  rw [JsonScanLane.denoteCode_load_i32 calls env s "%n.i.promoted751.i.i" "%n.i.i.i" hn hw]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%n.i.promoted751.i.i", .int 32 w) :: env) s
    "%cmp185753.i.i" "%add108.i.i" .ugt
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact ha)]
  simp only [denoteCode_nil, cond184Env, stateAt]

theorem cond184_step_body {calls : Calls} {env : Env} {s : State}
    {w : BitVec 32} {a : BitVec 64} {n : Nat}
    (hpc : s.pc = "while.cond184.preheader.i.i")
    (hn : lookupName env "%n.i.i.i" = some (.ptr n))
    (hw : readBytes s.mem n 4 = some (natToBytes w.toNat 4))
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .ugt a 0x0000000000000012#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cond184Env env w a)
        { s with pc := "while.body187.i.i",
                 pre := some "while.cond184.preheader.i.i" }) := by
  refine numFast_step_at (s' := stateAt (cond184Env env w a) s)
    (b := ⟨"while.cond184.preheader.i.i", cond184Instrs,
      Term.condbr (Operand.reg "%cmp185753.i.i") "while.body187.i.i"
        "while.end190.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using cond184_find
  · simpa only [stateAt] using cond184_denote hn hw ha
  · rw [numFast_execTerm_condbr_one (s := stateAt (cond184Env env w a) s)
      "%cmp185753.i.i" "while.body187.i.i" "while.end190.i.i"
      (by simp [cond184Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem cond184_step_end {calls : Calls} {env : Env} {s : State}
    {w : BitVec 32} {a : BitVec 64} {n : Nat}
    (hpc : s.pc = "while.cond184.preheader.i.i")
    (hn : lookupName env "%n.i.i.i" = some (.ptr n))
    (hw : readBytes s.mem n 4 = some (natToBytes w.toNat 4))
    (ha : lookupName env "%add108.i.i" = some (.int 64 a))
    (hbit : evalICmp .ugt a 0x0000000000000012#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (cond184Env env w a)
        { s with pc := "while.end190.i.i",
                 pre := some "while.cond184.preheader.i.i" }) := by
  refine numFast_step_at (s' := stateAt (cond184Env env w a) s)
    (b := ⟨"while.cond184.preheader.i.i", cond184Instrs,
      Term.condbr (Operand.reg "%cmp185753.i.i") "while.body187.i.i"
        "while.end190.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using cond184_find
  · simpa only [stateAt] using cond184_denote hn hw ha
  · rw [numFast_execTerm_condbr_zero (s := stateAt (cond184Env env w a) s)
      "%cmp185753.i.i" "while.body187.i.i" "while.end190.i.i"
      (by simp [cond184Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! #### The non-negative route's rung: `while.body187.i.i` and its exit -/

def body187Specs : List PhiSpec :=
  [{ dst := "%k183.0754.i.i", ty := Ty.int 64,
     incoming := [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
                  ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))] },
   { dst := "%108", ty := Ty.int 32,
     incoming := [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
                  ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))] }]

def body187Instrs : List Instr :=
  [Instr.icmp "%cmp28.i.i585.i.i" (IPred.sgt) 32 (Operand.reg "%108")
     (Operand.imm (Const.int 32 0x00000000#32))]

def body187Block : List Instr := body187Specs.map PhiSpec.instr ++ body187Instrs

theorem body187_find :
    numFastBody.findBlock "while.body187.i.i" =
      some ⟨"while.body187.i.i", body187Block,
        Term.condbr (Operand.reg "%cmp28.i.i585.i.i") "for.body.lr.ph.i.i586.i.i"
          "stk_mul_u64.exit605.i.i"⟩ := by
  simp only [body187Block, body187Instrs, body187Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_body187_i_i

def body187Env (env : Env) (kk : BitVec 64) (c : BitVec 32) : Env :=
  ("%cmp28.i.i585.i.i", .int 1 (evalICmp .sgt c 0x00000000#32)) ::
  ("%108", .int 32 c) :: ("%k183.0754.i.i", .int 64 kk) :: env

theorem body187_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
       ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
       ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c)) :
    denoteCode calls body187Block (stateAt env s) =
      some (stateAt (body187Env env kk c) s) := by
  have hsel : PhiSelects (stateAt env s) pre body187Specs
      [("%k183.0754.i.i", .int 64 kk), ("%108", .int 32 c)] := by
    simp only [body187Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := body187Specs)
    (vs := [("%k183.0754.i.i", .int 64 kk), ("%108", .int 32 c)])
    (rest := body187Instrs) hpre hsel (by decide)
  unfold body187Block
  rw [h]
  simp only [runCells]
  unfold body187Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%108", .int 32 c) :: ("%k183.0754.i.i", .int 64 kk) :: env) s
    "%cmp28.i.i585.i.i" "%108" .sgt (lookupName_cons_self ..)]
  simp only [denoteCode_nil, body187Env, stateAt]

theorem body187_step_nest {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "while.body187.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
       ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
       ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c))
    (hbit : evalICmp .sgt c 0x00000000#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body187Env env kk c)
        { s with pc := "for.body.lr.ph.i.i586.i.i", pre := some "while.body187.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body187Env env kk c) s)
    (b := ⟨"while.body187.i.i", body187Block,
      Term.condbr (Operand.reg "%cmp28.i.i585.i.i") "for.body.lr.ph.i.i586.i.i"
        "stk_mul_u64.exit605.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body187_find
  · simpa only [stateAt] using body187_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_one (s := stateAt (body187Env env kk c) s)
      "%cmp28.i.i585.i.i" "for.body.lr.ph.i.i586.i.i" "stk_mul_u64.exit605.i.i"
      (by simp [body187Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem body187_step_exit {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {kk : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "while.body187.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i")),
       ("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 64 kk))
    (hop2 : phiIncoming pre
      [("stk_mul_u64.exit605.i.i", (Operand.reg "%115")),
       ("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 32 c))
    (hbit : evalICmp .sgt c 0x00000000#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (body187Env env kk c)
        { s with pc := "stk_mul_u64.exit605.i.i", pre := some "while.body187.i.i" }) := by
  refine numFast_step_at (s' := stateAt (body187Env env kk c) s)
    (b := ⟨"while.body187.i.i", body187Block,
      Term.condbr (Operand.reg "%cmp28.i.i585.i.i") "for.body.lr.ph.i.i586.i.i"
        "stk_mul_u64.exit605.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using body187_find
  · simpa only [stateAt] using body187_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_zero (s := stateAt (body187Env env kk c) s)
      "%cmp28.i.i585.i.i" "for.body.lr.ph.i.i586.i.i" "stk_mul_u64.exit605.i.i"
      (by simp [body187Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The rung's exit: the counter's `phi`, the residual and the `> 37` test. -/
def exit605Specs : List PhiSpec :=
  [{ dst := "%115", ty := Ty.int 32,
     incoming := [("while.body187.i.i", (Operand.reg "%108")),
                  ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
                  ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))] }]

def exit605Instrs : List Instr :=
  [Instr.binop "%sub189.i.i" (BinOp.add) 64 (Operand.reg "%k183.0754.i.i")
     (Operand.imm (Const.int 64 0xffffffffffffffed#64)),
   Instr.icmp "%cmp185.i.i" (IPred.sgt) 64 (Operand.reg "%k183.0754.i.i")
     (Operand.imm (Const.int 64 0x0000000000000025#64))]

def exit605Block : List Instr := exit605Specs.map PhiSpec.instr ++ exit605Instrs

theorem exit605_find :
    numFastBody.findBlock "stk_mul_u64.exit605.i.i" =
      some ⟨"stk_mul_u64.exit605.i.i", exit605Block,
        Term.condbr (Operand.reg "%cmp185.i.i") "while.body187.i.i"
          "while.end190.i.i"⟩ := by
  simp only [exit605Block, exit605Instrs, exit605Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_stk_mul_u64_exit605_i_i

def exit605Env (env : Env) (k : BitVec 32) (kk : BitVec 64) : Env :=
  ("%cmp185.i.i", .int 1 (evalICmp .sgt kk 0x0000000000000025#64)) ::
  ("%sub189.i.i", .int 64 (kk + 0xffffffffffffffed#64)) ::
  ("%115", .int 32 k) :: env

theorem exit605_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {kk : BitVec 64}
    (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body187.i.i", (Operand.reg "%108")),
       ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
       ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hk : lookupName env "%k183.0754.i.i" = some (.int 64 kk)) :
    denoteCode calls exit605Block (stateAt env s) =
      some (stateAt (exit605Env env k kk) s) := by
  have hsel : PhiSelects (stateAt env s) pre exit605Specs [("%115", .int 32 k)] := by
    simp only [exit605Specs]
    constructor
    · exact hop
    · exact hov
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := exit605Specs) (vs := [("%115", .int 32 k)])
    (rest := exit605Instrs) hpre hsel (by decide)
  unfold exit605Block
  rw [h]
  simp only [runCells]
  unfold exit605Instrs
  rw [JsonScanLane.denoteCode_add_imm_w calls (("%115", .int 32 k) :: env) s
    "%sub189.i.i" "%k183.0754.i.i" 64
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hk)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%sub189.i.i", .int 64 (kk + 0xffffffffffffffed#64)) ::
      ("%115", .int 32 k) :: env) s
    "%cmp185.i.i" "%k183.0754.i.i" .sgt
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hk)]
  simp only [denoteCode_nil, exit605Env, stateAt]

theorem exit605_step_body {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit605.i.i") (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body187.i.i", (Operand.reg "%108")),
       ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
       ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hk : lookupName env "%k183.0754.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (exit605Env env k kk)
        { s with pc := "while.body187.i.i",
                 pre := some "stk_mul_u64.exit605.i.i" }) := by
  refine numFast_step_at (s' := stateAt (exit605Env env k kk) s)
    (b := ⟨"stk_mul_u64.exit605.i.i", exit605Block,
      Term.condbr (Operand.reg "%cmp185.i.i") "while.body187.i.i"
        "while.end190.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using exit605_find
  · simpa only [stateAt] using exit605_denote hpre hop hov hk
  · rw [numFast_execTerm_condbr_one (s := stateAt (exit605Env env k kk) s)
      "%cmp185.i.i" "while.body187.i.i" "while.end190.i.i"
      (by simp [exit605Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem exit605_step_end {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {k : BitVec 32} {kk : BitVec 64}
    (hpc : s.pc = "stk_mul_u64.exit605.i.i") (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("while.body187.i.i", (Operand.reg "%108")),
       ("while.cond.preheader.i.i599.i.i", (Operand.reg "%108")),
       ("while.body.us.i.i601.i.i", (Operand.reg "%inc12.us.i.i603.i.i"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 32 k))
    (hk : lookupName env "%k183.0754.i.i" = some (.int 64 kk))
    (hbit : evalICmp .sgt kk 0x0000000000000025#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (exit605Env env k kk)
        { s with pc := "while.end190.i.i",
                 pre := some "stk_mul_u64.exit605.i.i" }) := by
  refine numFast_step_at (s' := stateAt (exit605Env env k kk) s)
    (b := ⟨"stk_mul_u64.exit605.i.i", exit605Block,
      Term.condbr (Operand.reg "%cmp185.i.i") "while.body187.i.i"
        "while.end190.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using exit605_find
  · simpa only [stateAt] using exit605_denote hpre hop hov hk
  · rw [numFast_execTerm_condbr_zero (s := stateAt (exit605Env env k kk) s)
      "%cmp185.i.i" "while.body187.i.i" "while.end190.i.i"
      (by simp [exit605Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! #### The rung's merge: `while.end190.i.i` and `if.end195.i.i` -/

def end190Specs : List PhiSpec :=
  [{ dst := "%116", ty := Ty.int 32,
     incoming := [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
                  ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] },
   { dst := "%k183.0.lcssa.i.i", ty := Ty.int 64,
     incoming := [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
                  ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] }]

def end190Instrs : List Instr :=
  [Instr.store (Ty.int 32) (Operand.reg "%116") (Operand.reg "%n.i.i.i"),
   Instr.icmp "%tobool191.not.i.i" (IPred.ne) 64 (Operand.reg "%k183.0.lcssa.i.i")
     (Operand.imm (Const.int 64 0x0000000000000000#64)),
   Instr.icmp "%cmp28.i.i607.i.i" (IPred.sgt) 32 (Operand.reg "%116")
     (Operand.imm (Const.int 32 0x00000000#32)),
   Instr.select "%or.cond865.i.i" (Ty.int 1) (Operand.reg "%tobool191.not.i.i")
     (Operand.reg "%cmp28.i.i607.i.i") (Operand.imm (Const.int 1 0x0#1))]

def end190Block : List Instr := end190Specs.map PhiSpec.instr ++ end190Instrs

theorem end190_find :
    numFastBody.findBlock "while.end190.i.i" =
      some ⟨"while.end190.i.i", end190Block,
        Term.condbr (Operand.reg "%or.cond865.i.i") "for.body.lr.ph.i.i608.i.i"
          "if.end195.i.i"⟩ := by
  simp only [end190Block, end190Instrs, end190Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_end190_i_i

def end190Env (env : Env) (c : BitVec 32) (kk : BitVec 64) : Env :=
  ("%or.cond865.i.i", .int 1
    (if evalICmp .ne kk 0x0000000000000000#64 = 1
      then evalICmp .sgt c 0x00000000#32 else 0x0#1)) ::
  ("%cmp28.i.i607.i.i", .int 1 (evalICmp .sgt c 0x00000000#32)) ::
  ("%tobool191.not.i.i", .int 1 (evalICmp .ne kk 0x0000000000000000#64)) ::
  ("%k183.0.lcssa.i.i", .int 64 kk) :: ("%116", .int 32 c) :: env

def end190State (env : Env) (c : BitVec 32) (kk : BitVec 64) (a : Nat)
    (s : State) : State :=
  { stateAt (end190Env env c kk) s with
      mem := writeBytes s.mem a (natToBytes c.toNat 4) }

theorem end190_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {c : BitVec 32} {kk : BitVec 64} {a : Nat}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 32 c))
    (hop2 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 kk))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a)) :
    denoteCode calls end190Block (stateAt env s) = some (end190State env c kk a s) := by
  have hsel : PhiSelects (stateAt env s) pre end190Specs
      [("%116", .int 32 c), ("%k183.0.lcssa.i.i", .int 64 kk)] := by
    simp only [end190Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := end190Specs)
    (vs := [("%116", .int 32 c), ("%k183.0.lcssa.i.i", .int 64 kk)])
    (rest := end190Instrs) hpre hsel (by decide)
  unfold end190Block
  rw [h]
  simp only [runCells]
  unfold end190Instrs
  rw [denoteCode_store32 calls
    (("%k183.0.lcssa.i.i", .int 64 kk) :: ("%116", .int 32 c) :: env) s
    "%116" "%n.i.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..) hn]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%k183.0.lcssa.i.i", .int 64 kk) :: ("%116", .int 32 c) :: env)
    { s with mem := writeBytes s.mem a (natToBytes c.toNat 4) }
    "%tobool191.not.i.i" "%k183.0.lcssa.i.i" .ne
    (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%tobool191.not.i.i", .int 1 (evalICmp .ne kk 0x0000000000000000#64)) ::
      ("%k183.0.lcssa.i.i", .int 64 kk) :: ("%116", .int 32 c) :: env)
    { s with mem := writeBytes s.mem a (natToBytes c.toNat 4) }
    "%cmp28.i.i607.i.i" "%116" .sgt
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_select_bit_reg_imm_w calls
    (("%cmp28.i.i607.i.i", .int 1 (evalICmp .sgt c 0x00000000#32)) ::
      ("%tobool191.not.i.i", .int 1 (evalICmp .ne kk 0x0000000000000000#64)) ::
      ("%k183.0.lcssa.i.i", .int 64 kk) :: ("%116", .int 32 c) :: env)
    { s with mem := writeBytes s.mem a (natToBytes c.toNat 4) }
    "%or.cond865.i.i" "%tobool191.not.i.i" "%cmp28.i.i607.i.i" 1
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (lookupName_cons_self ..)]
  simp only [denoteCode_nil, end190Env, end190State, stateAt]

theorem end190_step_rung {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {c : BitVec 32} {kk : BitVec 64} {a : Nat}
    (hpc : s.pc = "while.end190.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 32 c))
    (hop2 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 kk))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a))
    (hbit : (if evalICmp .ne kk 0x0000000000000000#64 = 1
      then evalICmp .sgt c 0x00000000#32 else 0x0#1) = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { end190State env c kk a s with
        pc := "for.body.lr.ph.i.i608.i.i", pre := some "while.end190.i.i" } := by
  refine numFast_step_at (s' := end190State env c kk a s)
    (b := ⟨"while.end190.i.i", end190Block,
      Term.condbr (Operand.reg "%or.cond865.i.i") "for.body.lr.ph.i.i608.i.i"
        "if.end195.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end190_find
  · simpa only [stateAt] using end190_denote hpre hop1 hov1 hop2 hov2 hn
  · rw [numFast_execTerm_condbr_one (s := end190State env c kk a s)
      "%or.cond865.i.i" "for.body.lr.ph.i.i608.i.i" "if.end195.i.i" ?_ hbit]
    · simp only [end190State, end190Env, stateAt, hpc]
    · simp only [end190State, end190Env, stateAt]
      exact lookupName_cons_self ..

theorem end190_step_end {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {c : BitVec 32} {kk : BitVec 64} {a : Nat}
    (hpc : s.pc = "while.end190.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%n.i.promoted751.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%115"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 32 c))
    (hop2 : phiIncoming pre
      [("while.cond184.preheader.i.i", (Operand.reg "%add108.i.i")),
       ("stk_mul_u64.exit605.i.i", (Operand.reg "%sub189.i.i"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 kk))
    (hn : lookupName env "%n.i.i.i" = some (.ptr a))
    (hbit : (if evalICmp .ne kk 0x0000000000000000#64 = 1
      then evalICmp .sgt c 0x00000000#32 else 0x0#1) = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump { end190State env c kk a s with
        pc := "if.end195.i.i", pre := some "while.end190.i.i" } := by
  refine numFast_step_at (s' := end190State env c kk a s)
    (b := ⟨"while.end190.i.i", end190Block,
      Term.condbr (Operand.reg "%or.cond865.i.i") "for.body.lr.ph.i.i608.i.i"
        "if.end195.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end190_find
  · simpa only [stateAt] using end190_denote hpre hop1 hov1 hop2 hov2 hn
  · rw [numFast_execTerm_condbr_zero (s := end190State env c kk a s)
      "%or.cond865.i.i" "for.body.lr.ph.i.i608.i.i" "if.end195.i.i" ?_ hbit]
    · simp only [end190State, end190Env, stateAt, hpc]
    · simp only [end190State, end190Env, stateAt]
      exact lookupName_cons_self ..

/-- The scratch count's zeroing. -/
def end195Instrs : List Instr :=
  [Instr.store (Ty.int 64) (Operand.imm (Const.int 64 0x0000000000000000#64))
     (Operand.reg "%S128.i.i")]

theorem end195_find :
    numFastBody.findBlock "if.end195.i.i" =
      some ⟨"if.end195.i.i", end195Instrs, Term.br "if.end198.i.i"⟩ := by
  simpa only [end195Instrs] using numFast_findBlock_if_end195_i_i

theorem end195_denote {calls : Calls} {env : Env} {s : State} {a : Nat}
    (hS : lookupName env "%S128.i.i" = some (.ptr a)) :
    denoteCode calls end195Instrs (stateAt env s) =
      some (stateAt env
        { s with mem := writeBytes s.mem a (natToBytes (0x0000000000000000#64).toNat 8) }) := by
  unfold end195Instrs
  rw [denoteCode_store64_imm calls env s 0x0000000000000000#64 "%S128.i.i" hS]
  simp only [denoteCode_nil, stateAt]

theorem end195_step {calls : Calls} {env : Env} {s : State} {a : Nat}
    (hpc : s.pc = "if.end195.i.i")
    (hS : lookupName env "%S128.i.i" = some (.ptr a)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt env
        { s with mem := writeBytes s.mem a (natToBytes (0x0000000000000000#64).toNat 8),
                 pc := "if.end198.i.i", pre := some "if.end195.i.i" }) := by
  refine numFast_step_at (s' := stateAt env
      { s with mem := writeBytes s.mem a (natToBytes (0x0000000000000000#64).toNat 8) })
    (b := ⟨"if.end195.i.i", end195Instrs, Term.br "if.end198.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using end195_find
  · simpa only [stateAt] using end195_denote hS
  · simp only [execTerm, stateAt, hpc]

/-! #### The nests' exits and unroll bounds

Each digit-ingest nest peels its trip count's residue and truncates the last
visit's `i128` sum to the word its store writes.  The `…loopexit.unr-lcssa`
block takes the unrolled body's last shifted sum, the `…epilog-lcssa` block the
peeled loop's, and the `.new` block's `and` forms the unrolled trip count.  The
nest bodies are `JsonStage2NumFastTier3`'s epilogue chain (its `t3_epil_denote`)
and the width-generic `mul`/`add`/`lshr` steps stated there.
-/

/-- A one-`trunc` block's chain: the low word of an `i128` value. -/
theorem denoteCode_trunc_one (calls : Calls) (env : Env) (s : State)
    (d v : String) {carry : BitVec 128}
    (hv : lookupName env v = some (.int 128 carry)) :
    denoteCode calls [Instr.trunc d 128 64 (.reg v)] (stateAt env s) =
      some (stateAt ((d, .int 64 (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) :: env) s) := by
  rw [denoteCode_trunc calls env s d v 128 64 hv]
  simp only [denoteCode_nil]

/-- A one-`and` block's chain: the unrolled trip count. -/
theorem denoteCode_and_one (calls : Calls) (env : Env) (s : State)
    (d a : String) {x : BitVec 64} {c : BitVec 64}
    (ha : lookupName env a = some (.int 64 x)) :
    denoteCode calls [Instr.binop d .and 64 (.reg a) (.imm (.int 64 c))] (stateAt env s) =
      some (stateAt ((d, .int 64 (x &&& c)) :: env) s) := by
  rw [denoteCode_and_imm calls env s d a ha]
  simp only [denoteCode_nil]

/-- The `%92`-count rung's unrolled-body exit. -/
def loopexit555Instrs : List Instr :=
  [Instr.trunc "%extract.t1093" 128 64 (Operand.reg "%shr.i.i552.i.i.3")]

theorem loopexit555_find :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit" =
      some ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", loopexit555Instrs,
        Term.br "while.cond.preheader.i.i555.i.i.unr-lcssa"⟩ := by
  simpa only [loopexit555Instrs]
    using numFast_findBlock_while_cond_preheader_i_i555_i_i_unr_lcssa_loopexit

def loopexit555Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1093", .int 64 o) :: env

theorem loopexit555_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i552.i.i.3" = some (.int 128 carry)) :
    denoteCode calls loopexit555Instrs (stateAt env s) =
      some (stateAt (loopexit555Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold loopexit555Instrs loopexit555Env
  exact denoteCode_trunc_one calls env s "%extract.t1093" "%shr.i.i552.i.i.3" hc

theorem loopexit555_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit")
    (hc : lookupName env "%shr.i.i552.i.i.3" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (loopexit555Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i555.i.i.unr-lcssa",
                 pre := some "while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit" }) := by
  refine numFast_step_at (s' := stateAt (loopexit555Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", loopexit555Instrs,
      Term.br "while.cond.preheader.i.i555.i.i.unr-lcssa"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using loopexit555_find
  · simpa only [stateAt] using loopexit555_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `%92`-count rung's peeled-loop exit. -/
def epilog555Instrs : List Instr :=
  [Instr.trunc "%extract.t1092" 128 64 (Operand.reg "%shr.i.i552.i.i.epil")]

theorem epilog555_find :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.epilog-lcssa" =
      some ⟨"while.cond.preheader.i.i555.i.i.epilog-lcssa", epilog555Instrs,
        Term.br "while.cond.preheader.i.i555.i.i"⟩ := by
  simpa only [epilog555Instrs]
    using numFast_findBlock_while_cond_preheader_i_i555_i_i_epilog_lcssa

def epilog555Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1092", .int 64 o) :: env

theorem epilog555_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i552.i.i.epil" = some (.int 128 carry)) :
    denoteCode calls epilog555Instrs (stateAt env s) =
      some (stateAt (epilog555Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold epilog555Instrs epilog555Env
  exact denoteCode_trunc_one calls env s "%extract.t1092" "%shr.i.i552.i.i.epil" hc

theorem epilog555_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i.epilog-lcssa")
    (hc : lookupName env "%shr.i.i552.i.i.epil" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (epilog555Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i555.i.i",
                 pre := some "while.cond.preheader.i.i555.i.i.epilog-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (epilog555Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i.epilog-lcssa", epilog555Instrs,
      Term.br "while.cond.preheader.i.i555.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epilog555_find
  · simpa only [stateAt] using epilog555_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `%inc12`-count rung's unrolled-body exit. -/
def loopexit577Instrs : List Instr :=
  [Instr.trunc "%extract.t1099" 128 64 (Operand.reg "%shr.i.i574.i.i.3")]

theorem loopexit577_find :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit" =
      some ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", loopexit577Instrs,
        Term.br "while.cond.preheader.i.i577.i.i.unr-lcssa"⟩ := by
  simpa only [loopexit577Instrs]
    using numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa_loopexit

def loopexit577Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1099", .int 64 o) :: env

theorem loopexit577_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i574.i.i.3" = some (.int 128 carry)) :
    denoteCode calls loopexit577Instrs (stateAt env s) =
      some (stateAt (loopexit577Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold loopexit577Instrs loopexit577Env
  exact denoteCode_trunc_one calls env s "%extract.t1099" "%shr.i.i574.i.i.3" hc

theorem loopexit577_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit")
    (hc : lookupName env "%shr.i.i574.i.i.3" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (loopexit577Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit" }) := by
  refine numFast_step_at (s' := stateAt (loopexit577Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", loopexit577Instrs,
      Term.br "while.cond.preheader.i.i577.i.i.unr-lcssa"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using loopexit577_find
  · simpa only [stateAt] using loopexit577_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `%108`-count rung's unrolled-body exit. -/
def loopexit599Instrs : List Instr :=
  [Instr.trunc "%extract.t1095" 128 64 (Operand.reg "%shr.i.i596.i.i.3")]

theorem loopexit599_find :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit" =
      some ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", loopexit599Instrs,
        Term.br "while.cond.preheader.i.i599.i.i.unr-lcssa"⟩ := by
  simpa only [loopexit599Instrs]
    using numFast_findBlock_while_cond_preheader_i_i599_i_i_unr_lcssa_loopexit

def loopexit599Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1095", .int 64 o) :: env

theorem loopexit599_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i596.i.i.3" = some (.int 128 carry)) :
    denoteCode calls loopexit599Instrs (stateAt env s) =
      some (stateAt (loopexit599Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold loopexit599Instrs loopexit599Env
  exact denoteCode_trunc_one calls env s "%extract.t1095" "%shr.i.i596.i.i.3" hc

theorem loopexit599_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit")
    (hc : lookupName env "%shr.i.i596.i.i.3" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (loopexit599Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i599.i.i.unr-lcssa",
                 pre := some "while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit" }) := by
  refine numFast_step_at (s' := stateAt (loopexit599Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", loopexit599Instrs,
      Term.br "while.cond.preheader.i.i599.i.i.unr-lcssa"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using loopexit599_find
  · simpa only [stateAt] using loopexit599_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `%108`-count rung's peeled-loop exit. -/
def epilog599Instrs : List Instr :=
  [Instr.trunc "%extract.t1094" 128 64 (Operand.reg "%shr.i.i596.i.i.epil")]

theorem epilog599_find :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.epilog-lcssa" =
      some ⟨"while.cond.preheader.i.i599.i.i.epilog-lcssa", epilog599Instrs,
        Term.br "while.cond.preheader.i.i599.i.i"⟩ := by
  simpa only [epilog599Instrs]
    using numFast_findBlock_while_cond_preheader_i_i599_i_i_epilog_lcssa

def epilog599Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1094", .int 64 o) :: env

theorem epilog599_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i596.i.i.epil" = some (.int 128 carry)) :
    denoteCode calls epilog599Instrs (stateAt env s) =
      some (stateAt (epilog599Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold epilog599Instrs epilog599Env
  exact denoteCode_trunc_one calls env s "%extract.t1094" "%shr.i.i596.i.i.epil" hc

theorem epilog599_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i.epilog-lcssa")
    (hc : lookupName env "%shr.i.i596.i.i.epil" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (epilog599Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i599.i.i",
                 pre := some "while.cond.preheader.i.i599.i.i.epilog-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (epilog599Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i.epilog-lcssa", epilog599Instrs,
      Term.br "while.cond.preheader.i.i599.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epilog599_find
  · simpa only [stateAt] using epilog599_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `if.end195`-reaching rung's unrolled-body exit. -/
def loopexit622Instrs : List Instr :=
  [Instr.trunc "%extract.t1097" 128 64 (Operand.reg "%shr.i.i619.i.i.3")]

theorem loopexit622_find :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit" =
      some ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", loopexit622Instrs,
        Term.br "while.cond.preheader.i.i622.i.i.unr-lcssa"⟩ := by
  simpa only [loopexit622Instrs]
    using numFast_findBlock_while_cond_preheader_i_i622_i_i_unr_lcssa_loopexit

def loopexit622Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1097", .int 64 o) :: env

theorem loopexit622_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i619.i.i.3" = some (.int 128 carry)) :
    denoteCode calls loopexit622Instrs (stateAt env s) =
      some (stateAt (loopexit622Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold loopexit622Instrs loopexit622Env
  exact denoteCode_trunc_one calls env s "%extract.t1097" "%shr.i.i619.i.i.3" hc

theorem loopexit622_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit")
    (hc : lookupName env "%shr.i.i619.i.i.3" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (loopexit622Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i622.i.i.unr-lcssa",
                 pre := some "while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit" }) := by
  refine numFast_step_at (s' := stateAt (loopexit622Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", loopexit622Instrs,
      Term.br "while.cond.preheader.i.i622.i.i.unr-lcssa"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using loopexit622_find
  · simpa only [stateAt] using loopexit622_denote hc
  · simp only [execTerm, stateAt, hpc]

/-- The `%108`-count rung's peeled-loop exit at `if.end195`. -/
def epilog622Instrs : List Instr :=
  [Instr.trunc "%extract.t1096" 128 64 (Operand.reg "%shr.i.i619.i.i.epil")]

theorem epilog622_find :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.epilog-lcssa" =
      some ⟨"while.cond.preheader.i.i622.i.i.epilog-lcssa", epilog622Instrs,
        Term.br "while.cond.preheader.i.i622.i.i"⟩ := by
  simpa only [epilog622Instrs]
    using numFast_findBlock_while_cond_preheader_i_i622_i_i_epilog_lcssa

def epilog622Env (env : Env) (o : BitVec 64) : Env :=
  ("%extract.t1096", .int 64 o) :: env

theorem epilog622_denote {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hc : lookupName env "%shr.i.i619.i.i.epil" = some (.int 128 carry)) :
    denoteCode calls epilog622Instrs (stateAt env s) =
      some (stateAt (epilog622Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s) := by
  unfold epilog622Instrs epilog622Env
  exact denoteCode_trunc_one calls env s "%extract.t1096" "%shr.i.i619.i.i.epil" hc

theorem epilog622_step {calls : Calls} {env : Env} {s : State} {carry : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i.epilog-lcssa")
    (hc : lookupName env "%shr.i.i619.i.i.epil" = some (.int 128 carry)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (epilog622Env env (BitVec.ofNat 64 (carry.toNat % 2 ^ 64)))
        { s with pc := "while.cond.preheader.i.i622.i.i",
                 pre := some "while.cond.preheader.i.i622.i.i.epilog-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (epilog622Env env
      (BitVec.ofNat 64 (carry.toNat % 2 ^ 64))) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i.epilog-lcssa", epilog622Instrs,
      Term.br "while.cond.preheader.i.i622.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using epilog622_find
  · simpa only [stateAt] using epilog622_denote hc
  · simp only [execTerm, stateAt, hpc]

/-! ##### The unroll bounds -/

def new525Instrs : List Instr :=
  [Instr.binop "%unroll_iter1053" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i526.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

theorem new525_find :
    numFastBody.findBlock "for.body.lr.ph.i525.i.i.new" =
      some ⟨"for.body.lr.ph.i525.i.i.new", new525Instrs,
        Term.br "for.body.i527.i.i"⟩ := by
  simpa only [new525Instrs] using numFast_findBlock_for_body_lr_ph_i525_i_i_new

def new525Env (env : Env) (w : BitVec 64) : Env :=
  ("%unroll_iter1053", .int 64 (w &&& 0x000000007ffffffc#64)) :: env

theorem new525_denote {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i526.i.i" = some (.int 64 w)) :
    denoteCode calls new525Instrs (stateAt env s) =
      some (stateAt (new525Env env w) s) := by
  unfold new525Instrs new525Env
  exact denoteCode_and_one calls env s "%unroll_iter1053" "%wide.trip.count.i526.i.i" hw

theorem new525_step {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i525.i.i.new")
    (hw : lookupName env "%wide.trip.count.i526.i.i" = some (.int 64 w)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (new525Env env w)
        { s with pc := "for.body.i527.i.i", pre := some "for.body.lr.ph.i525.i.i.new" }) := by
  refine numFast_step_at (s' := stateAt (new525Env env w) s)
    (b := ⟨"for.body.lr.ph.i525.i.i.new", new525Instrs,
      Term.br "for.body.i527.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using new525_find
  · simpa only [stateAt] using new525_denote hw
  · simp only [execTerm, stateAt, hpc]

def new542Instrs : List Instr :=
  [Instr.binop "%unroll_iter1067" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i543.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

theorem new542_find :
    numFastBody.findBlock "for.body.lr.ph.i.i542.i.i.new" =
      some ⟨"for.body.lr.ph.i.i542.i.i.new", new542Instrs,
        Term.br "for.body.i.i544.i.i"⟩ := by
  simpa only [new542Instrs] using numFast_findBlock_for_body_lr_ph_i_i542_i_i_new

def new542Env (env : Env) (w : BitVec 64) : Env :=
  ("%unroll_iter1067", .int 64 (w &&& 0x000000007ffffffc#64)) :: env

theorem new542_denote {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 w)) :
    denoteCode calls new542Instrs (stateAt env s) =
      some (stateAt (new542Env env w) s) := by
  unfold new542Instrs new542Env
  exact denoteCode_and_one calls env s "%unroll_iter1067" "%wide.trip.count.i.i543.i.i" hw

theorem new542_step {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i.i542.i.i.new")
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 w)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (new542Env env w)
        { s with pc := "for.body.i.i544.i.i", pre := some "for.body.lr.ph.i.i542.i.i.new" }) := by
  refine numFast_step_at (s' := stateAt (new542Env env w) s)
    (b := ⟨"for.body.lr.ph.i.i542.i.i.new", new542Instrs,
      Term.br "for.body.i.i544.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using new542_find
  · simpa only [stateAt] using new542_denote hw
  · simp only [execTerm, stateAt, hpc]

def new564Instrs : List Instr :=
  [Instr.binop "%unroll_iter1088" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

theorem new564_find :
    numFastBody.findBlock "for.body.lr.ph.i.i564.i.i.new" =
      some ⟨"for.body.lr.ph.i.i564.i.i.new", new564Instrs,
        Term.br "for.body.i.i566.i.i"⟩ := by
  simpa only [new564Instrs] using numFast_findBlock_for_body_lr_ph_i_i564_i_i_new

def new564Env (env : Env) (w : BitVec 64) : Env :=
  ("%unroll_iter1088", .int 64 (w &&& 0x000000007ffffffc#64)) :: env

theorem new564_denote {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i.i565.i.i" = some (.int 64 w)) :
    denoteCode calls new564Instrs (stateAt env s) =
      some (stateAt (new564Env env w) s) := by
  unfold new564Instrs new564Env
  exact denoteCode_and_one calls env s "%unroll_iter1088" "%wide.trip.count.i.i565.i.i" hw

theorem new564_step {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i.new")
    (hw : lookupName env "%wide.trip.count.i.i565.i.i" = some (.int 64 w)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (new564Env env w)
        { s with pc := "for.body.i.i566.i.i", pre := some "for.body.lr.ph.i.i564.i.i.new" }) := by
  refine numFast_step_at (s' := stateAt (new564Env env w) s)
    (b := ⟨"for.body.lr.ph.i.i564.i.i.new", new564Instrs,
      Term.br "for.body.i.i566.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using new564_find
  · simpa only [stateAt] using new564_denote hw
  · simp only [execTerm, stateAt, hpc]

def new586Instrs : List Instr :=
  [Instr.binop "%unroll_iter1074" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

theorem new586_find :
    numFastBody.findBlock "for.body.lr.ph.i.i586.i.i.new" =
      some ⟨"for.body.lr.ph.i.i586.i.i.new", new586Instrs,
        Term.br "for.body.i.i588.i.i"⟩ := by
  simpa only [new586Instrs] using numFast_findBlock_for_body_lr_ph_i_i586_i_i_new

def new586Env (env : Env) (w : BitVec 64) : Env :=
  ("%unroll_iter1074", .int 64 (w &&& 0x000000007ffffffc#64)) :: env

theorem new586_denote {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i.i587.i.i" = some (.int 64 w)) :
    denoteCode calls new586Instrs (stateAt env s) =
      some (stateAt (new586Env env w) s) := by
  unfold new586Instrs new586Env
  exact denoteCode_and_one calls env s "%unroll_iter1074" "%wide.trip.count.i.i587.i.i" hw

theorem new586_step {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i.i586.i.i.new")
    (hw : lookupName env "%wide.trip.count.i.i587.i.i" = some (.int 64 w)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (new586Env env w)
        { s with pc := "for.body.i.i588.i.i", pre := some "for.body.lr.ph.i.i586.i.i.new" }) := by
  refine numFast_step_at (s' := stateAt (new586Env env w) s)
    (b := ⟨"for.body.lr.ph.i.i586.i.i.new", new586Instrs,
      Term.br "for.body.i.i588.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using new586_find
  · simpa only [stateAt] using new586_denote hw
  · simp only [execTerm, stateAt, hpc]

def new608Instrs : List Instr :=
  [Instr.binop "%unroll_iter1081" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x000000007ffffffc#64))]

theorem new608_find :
    numFastBody.findBlock "for.body.lr.ph.i.i608.i.i.new" =
      some ⟨"for.body.lr.ph.i.i608.i.i.new", new608Instrs,
        Term.br "for.body.i.i611.i.i"⟩ := by
  simpa only [new608Instrs] using numFast_findBlock_for_body_lr_ph_i_i608_i_i_new

def new608Env (env : Env) (w : BitVec 64) : Env :=
  ("%unroll_iter1081", .int 64 (w &&& 0x000000007ffffffc#64)) :: env

theorem new608_denote {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 w)) :
    denoteCode calls new608Instrs (stateAt env s) =
      some (stateAt (new608Env env w) s) := by
  unfold new608Instrs new608Env
  exact denoteCode_and_one calls env s "%unroll_iter1081" "%wide.trip.count.i.i610.i.i" hw

theorem new608_step {calls : Calls} {env : Env} {s : State} {w : BitVec 64}
    (hpc : s.pc = "for.body.lr.ph.i.i608.i.i.new")
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 w)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (new608Env env w)
        { s with pc := "for.body.i.i611.i.i", pre := some "for.body.lr.ph.i.i608.i.i.new" }) := by
  refine numFast_step_at (s' := stateAt (new608Env env w) s)
    (b := ⟨"for.body.lr.ph.i.i608.i.i.new", new608Instrs,
      Term.br "for.body.i.i611.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using new608_find
  · simpa only [stateAt] using new608_denote hw
  · simp only [execTerm, stateAt, hpc]

/-! ##### The `%cn`-count rung's test and the nest heads

`for.body.lr.ph.i564.i.i` and its sibling `i586` widen the group count, take the
unroll residue's bound and test it against four; `while.body.us.i.i557.i.i` and
`i601` store the `i128` carry's high word past the retained groups.  The 517
rung's test `while.cond.preheader.i517.i.i` is the carry's `== 0`.
-/

def pre517Specs : List PhiSpec :=
  [{ dst := "%carry.0.lcssa.i518.i.i", ty := Ty.int 128,
     incoming := [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
                  ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
                  ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))] }]

def pre517Instrs : List Instr :=
  [Instr.icmp "%tobool.not31.i519.i.i" (IPred.eq) 128
     (Operand.reg "%carry.0.lcssa.i518.i.i")
     (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))]

def pre517Block : List Instr := pre517Specs.map PhiSpec.instr ++ pre517Instrs

theorem pre517_find :
    numFastBody.findBlock "while.cond.preheader.i517.i.i" =
      some ⟨"while.cond.preheader.i517.i.i", pre517Block,
        Term.condbr (Operand.reg "%tobool.not31.i519.i.i") "if.end151.i.i"
          "while.body.us.i520.i.i"⟩ := by
  simp only [pre517Block, pre517Instrs, pre517Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i517_i_i

def pre517Env (env : Env) (a : BitVec 128) : Env :=
  ("%tobool.not31.i519.i.i", .int 1 (evalICmp .eq a
    0x00000000000000000000000000000000#128)) ::
  ("%carry.0.lcssa.i518.i.i", .int 128 a) :: env

theorem pre517_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {a : BitVec 128}
    (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
       ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 128 a)) :
    denoteCode calls pre517Block (stateAt env s) =
      some (stateAt (pre517Env env a) s) := by
  have hsel : PhiSelects (stateAt env s) pre pre517Specs
      [("%carry.0.lcssa.i518.i.i", .int 128 a)] := by
    simp only [pre517Specs]
    constructor
    · exact hop
    · exact hov
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := pre517Specs)
    (vs := [("%carry.0.lcssa.i518.i.i", .int 128 a)])
    (rest := pre517Instrs) hpre hsel (by decide)
  unfold pre517Block
  rw [h]
  simp only [runCells]
  unfold pre517Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.0.lcssa.i518.i.i", .int 128 a) :: env) s
    "%tobool.not31.i519.i.i" "%carry.0.lcssa.i518.i.i" .eq (lookupName_cons_self ..)]
  simp only [denoteCode_nil, pre517Env, stateAt]

theorem pre517_step_ladder {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {a : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i517.i.i") (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
       ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 128 a))
    (hbit : evalICmp .eq a 0x00000000000000000000000000000000#128 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre517Env env a)
        { s with pc := "if.end151.i.i", pre := some "while.cond.preheader.i517.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre517Env env a) s)
    (b := ⟨"while.cond.preheader.i517.i.i", pre517Block,
      Term.condbr (Operand.reg "%tobool.not31.i519.i.i") "if.end151.i.i"
        "while.body.us.i520.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre517_find
  · simpa only [stateAt] using pre517_denote hpre hop hov
  · rw [numFast_execTerm_condbr_one (s := stateAt (pre517Env env a) s)
      "%tobool.not31.i519.i.i" "if.end151.i.i" "while.body.us.i520.i.i"
      (by simp [pre517Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem pre517_step_store {calls : Calls} {env : Env} {s : State}
    {pre : String} {op : Operand} {a : BitVec 128}
    (hpc : s.pc = "while.cond.preheader.i517.i.i") (hpre : s.pre = some pre)
    (hop : phiIncoming pre
      [("if.then148.i.i", (Operand.reg "%conv.i514.i.i")),
       ("while.cond.preheader.i517.i.i.loopexit.unr-lcssa", (Operand.reg "%shr.i535.i.i.lcssa.ph")),
       ("for.body.i527.i.i.epil", (Operand.reg "%shr.i535.i.i.epil"))] = some op)
    (hov : evalOperand (stateAt env s) op = some (.int 128 a))
    (hbit : evalICmp .eq a 0x00000000000000000000000000000000#128 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre517Env env a)
        { s with pc := "while.body.us.i520.i.i",
                 pre := some "while.cond.preheader.i517.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre517Env env a) s)
    (b := ⟨"while.cond.preheader.i517.i.i", pre517Block,
      Term.condbr (Operand.reg "%tobool.not31.i519.i.i") "if.end151.i.i"
        "while.body.us.i520.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre517_find
  · simpa only [stateAt] using pre517_denote hpre hop hov
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pre517Env env a) s)
      "%tobool.not31.i519.i.i" "if.end151.i.i" "while.body.us.i520.i.i"
      (by simp [pre517Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `%inc12` rung's head: the count's widen, the unroll bound and the
`< 4` test. -/
def lrph564Instrs : List Instr :=
  [Instr.zext "%wide.trip.count.i.i565.i.i" 32 64
     (Operand.reg "%inc12.us.i.i581759761.i.i"),
   Instr.binop "%xtraiter1083" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i565.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
   Instr.icmp "%101" (IPred.ult) 32 (Operand.reg "%inc12.us.i.i581759761.i.i")
     (Operand.imm (Const.int 32 0x0000000000000004#32))]

theorem lrph564_find :
    numFastBody.findBlock "for.body.lr.ph.i.i564.i.i" =
      some ⟨"for.body.lr.ph.i.i564.i.i", lrph564Instrs,
        Term.condbr (Operand.reg "%101") "while.cond.preheader.i.i577.i.i.unr-lcssa"
          "for.body.lr.ph.i.i564.i.i.new"⟩ := by
  simpa only [lrph564Instrs] using numFast_findBlock_for_body_lr_ph_i_i564_i_i

def lrph564Env (env : Env) (c : BitVec 32) : Env :=
  ("%101", .int 1 (evalICmp .ult c 0x0000000000000004#32)) ::
  ("%xtraiter1083", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
  ("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env

theorem lrph564_denote {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c)) :
    denoteCode calls lrph564Instrs (stateAt env s) =
      some (stateAt (lrph564Env env c) s) := by
  unfold lrph564Instrs
  rw [denoteCode_zext calls env s "%wide.trip.count.i.i565.i.i"
    "%inc12.us.i.i581759761.i.i" 32 64 hc]
  rw [denoteCode_and_imm calls
    (("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) s
    "%xtraiter1083" "%wide.trip.count.i.i565.i.i" (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%xtraiter1083", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
      ("%wide.trip.count.i.i565.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) s
    "%101" "%inc12.us.i.i581759761.i.i" .ult
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc)]
  simp only [denoteCode_nil, lrph564Env, stateAt]

theorem lrph564_step_join {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph564Env env c)
        { s with pc := "while.cond.preheader.i.i577.i.i.unr-lcssa",
                 pre := some "for.body.lr.ph.i.i564.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph564Env env c) s)
    (b := ⟨"for.body.lr.ph.i.i564.i.i", lrph564Instrs,
      Term.condbr (Operand.reg "%101") "while.cond.preheader.i.i577.i.i.unr-lcssa"
        "for.body.lr.ph.i.i564.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph564_find
  · simpa only [stateAt] using lrph564_denote hc
  · rw [numFast_execTerm_condbr_one (s := stateAt (lrph564Env env c) s)
      "%101" "while.cond.preheader.i.i577.i.i.unr-lcssa"
      "for.body.lr.ph.i.i564.i.i.new" (by simp [lrph564Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem lrph564_step_unroll {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i564.i.i")
    (hc : lookupName env "%inc12.us.i.i581759761.i.i" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph564Env env c)
        { s with pc := "for.body.lr.ph.i.i564.i.i.new",
                 pre := some "for.body.lr.ph.i.i564.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph564Env env c) s)
    (b := ⟨"for.body.lr.ph.i.i564.i.i", lrph564Instrs,
      Term.condbr (Operand.reg "%101") "while.cond.preheader.i.i577.i.i.unr-lcssa"
        "for.body.lr.ph.i.i564.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph564_find
  · simpa only [stateAt] using lrph564_denote hc
  · rw [numFast_execTerm_condbr_zero (s := stateAt (lrph564Env env c) s)
      "%101" "while.cond.preheader.i.i577.i.i.unr-lcssa"
      "for.body.lr.ph.i.i564.i.i.new" (by simp [lrph564Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `%108` rung's head. -/
def lrph586Instrs : List Instr :=
  [Instr.zext "%wide.trip.count.i.i587.i.i" 32 64 (Operand.reg "%108"),
   Instr.binop "%xtraiter1069" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i587.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
   Instr.icmp "%109" (IPred.ult) 32 (Operand.reg "%108")
     (Operand.imm (Const.int 32 0x0000000000000004#32))]

theorem lrph586_find :
    numFastBody.findBlock "for.body.lr.ph.i.i586.i.i" =
      some ⟨"for.body.lr.ph.i.i586.i.i", lrph586Instrs,
        Term.condbr (Operand.reg "%109") "while.cond.preheader.i.i599.i.i.unr-lcssa"
          "for.body.lr.ph.i.i586.i.i.new"⟩ := by
  simpa only [lrph586Instrs] using numFast_findBlock_for_body_lr_ph_i_i586_i_i

def lrph586Env (env : Env) (c : BitVec 32) : Env :=
  ("%109", .int 1 (evalICmp .ult c 0x0000000000000004#32)) ::
  ("%xtraiter1069", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
  ("%wide.trip.count.i.i587.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env

theorem lrph586_denote {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hc : lookupName env "%108" = some (.int 32 c)) :
    denoteCode calls lrph586Instrs (stateAt env s) =
      some (stateAt (lrph586Env env c) s) := by
  unfold lrph586Instrs
  rw [denoteCode_zext calls env s "%wide.trip.count.i.i587.i.i" "%108" 32 64 hc]
  rw [denoteCode_and_imm calls
    (("%wide.trip.count.i.i587.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) s
    "%xtraiter1069" "%wide.trip.count.i.i587.i.i" (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%xtraiter1069", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
      ("%wide.trip.count.i.i587.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) :: env) s
    "%109" "%108" .ult
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc)]
  simp only [denoteCode_nil, lrph586Env, stateAt]

theorem lrph586_step_join {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i586.i.i")
    (hc : lookupName env "%108" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph586Env env c)
        { s with pc := "while.cond.preheader.i.i599.i.i.unr-lcssa",
                 pre := some "for.body.lr.ph.i.i586.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph586Env env c) s)
    (b := ⟨"for.body.lr.ph.i.i586.i.i", lrph586Instrs,
      Term.condbr (Operand.reg "%109") "while.cond.preheader.i.i599.i.i.unr-lcssa"
        "for.body.lr.ph.i.i586.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph586_find
  · simpa only [stateAt] using lrph586_denote hc
  · rw [numFast_execTerm_condbr_one (s := stateAt (lrph586Env env c) s)
      "%109" "while.cond.preheader.i.i599.i.i.unr-lcssa"
      "for.body.lr.ph.i.i586.i.i.new" (by simp [lrph586Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem lrph586_step_unroll {calls : Calls} {env : Env} {s : State} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i586.i.i")
    (hc : lookupName env "%108" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph586Env env c)
        { s with pc := "for.body.lr.ph.i.i586.i.i.new",
                 pre := some "for.body.lr.ph.i.i586.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph586Env env c) s)
    (b := ⟨"for.body.lr.ph.i.i586.i.i", lrph586Instrs,
      Term.condbr (Operand.reg "%109") "while.cond.preheader.i.i599.i.i.unr-lcssa"
        "for.body.lr.ph.i.i586.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph586_find
  · simpa only [stateAt] using lrph586_denote hc
  · rw [numFast_execTerm_condbr_zero (s := stateAt (lrph586Env env c) s)
      "%109" "while.cond.preheader.i.i599.i.i.unr-lcssa"
      "for.body.lr.ph.i.i586.i.i.new" (by simp [lrph586Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `%92` rung's carry store: the counter, the table row and the high word. -/
def bus557Instrs : List Instr :=
  [Instr.binop "%inc12.us.i.i559.i.i" (BinOp.add) 32 (Operand.reg "%92")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.gep "%arrayidx14.us.i.i560.i.i" (Ty.int 64) (Operand.reg "%pow.i.i")
     (Operand.reg "%wide.trip.count.i.i543.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i552.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i560.i.i"),
   Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i559.i.i")
     (Operand.reg "%n.i539.i.i")]

theorem bus557_find :
    numFastBody.findBlock "while.body.us.i.i557.i.i" =
      some ⟨"while.body.us.i.i557.i.i", bus557Instrs, Term.br "if.end198.i.i"⟩ := by
  simpa only [bus557Instrs] using numFast_findBlock_while_body_us_i_i557_i_i

def bus557Env (env : Env) (pow : Nat) (w : Nat) (c : BitVec 32) : Env :=
  ("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
  ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env

theorem bus557_denote {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {pow w : Nat} {wv off : BitVec 64} {n : Nat}
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    denoteCode calls bus557Instrs (stateAt env s) =
      some (stateAt (bus557Env env pow w c)
        { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) }) := by
  unfold bus557Instrs
  rw [JsonScanLane.denoteCode_add_imm_w calls env s "%inc12.us.i.i559.i.i" "%92" 32 h92]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%arrayidx14.us.i.i560.i.i" "%pow.i.i" "%wide.trip.count.i.i543.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hpow)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hw) (by rw [hwv]; exact hpos)]
  rw [hwv]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
      ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%shr.i.i552.i.i.lcssa.off0" "%arrayidx14.us.i.i560.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hoff)
    (lookupName_cons_self ..)]
  rw [denoteCode_store32 calls
    (("%arrayidx14.us.i.i560.i.i", .ptr (pow + w * 8)) ::
      ("%inc12.us.i.i559.i.i", .int 32 (c + 0x00000001#32)) :: env)
    { s with mem := writeBytes s.mem (pow + w * 8) (natToBytes off.toNat 8) }
    "%inc12.us.i.i559.i.i" "%n.i539.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hn)]
  simp only [denoteCode_nil, bus557Env, stateAt]

theorem bus557_step {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {pow w : Nat} {wv off : BitVec 64} {n : Nat}
    (hpc : s.pc = "while.body.us.i.i557.i.i")
    (h92 : lookupName env "%92" = some (.int 32 c))
    (hpow : lookupName env "%pow.i.i" = some (.ptr pow))
    (hw : lookupName env "%wide.trip.count.i.i543.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i552.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i539.i.i" = some (.ptr n)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus557Env env pow w c)
        { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4),
                 pc := "if.end198.i.i", pre := some "while.body.us.i.i557.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus557Env env pow w c)
      { s with mem := writeBytes (writeBytes s.mem (pow + w * 8)
          (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) })
    (b := ⟨"while.body.us.i.i557.i.i", bus557Instrs, Term.br "if.end198.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus557_find
  · simpa only [stateAt] using bus557_denote h92 hpow hw hwv hpos hoff hn
  · simp only [execTerm, stateAt, hpc]

/-- The `%108` rung's carry store. -/
def bus601Instrs : List Instr :=
  [Instr.binop "%inc12.us.i.i603.i.i" (BinOp.add) 32 (Operand.reg "%108")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.gep "%arrayidx14.us.i.i604.i.i" (Ty.int 64) (Operand.reg "%v.i.i")
     (Operand.reg "%wide.trip.count.i.i587.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i596.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i604.i.i")]

theorem bus601_find :
    numFastBody.findBlock "while.body.us.i.i601.i.i" =
      some ⟨"while.body.us.i.i601.i.i", bus601Instrs, Term.br "stk_mul_u64.exit605.i.i"⟩ := by
  simpa only [bus601Instrs] using numFast_findBlock_while_body_us_i_i601_i_i

def bus601Env (env : Env) (v : Nat) (w : Nat) (c : BitVec 32) : Env :=
  ("%arrayidx14.us.i.i604.i.i", .ptr (v + w * 8)) ::
  ("%inc12.us.i.i603.i.i", .int 32 (c + 0x00000001#32)) :: env

theorem bus601_denote {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64}
    (hc : lookupName env "%108" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i587.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i596.i.i.lcssa.off0" = some (.int 64 off)) :
    denoteCode calls bus601Instrs (stateAt env s) =
      some (stateAt (bus601Env env v w c)
        { s with mem := writeBytes s.mem (v + w * 8) (natToBytes off.toNat 8) }) := by
  unfold bus601Instrs
  rw [JsonScanLane.denoteCode_add_imm_w calls env s "%inc12.us.i.i603.i.i" "%108" 32 hc]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%inc12.us.i.i603.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%arrayidx14.us.i.i604.i.i" "%v.i.i" "%wide.trip.count.i.i587.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hv)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hw) (by rw [hwv]; exact hpos)]
  rw [hwv]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i604.i.i", .ptr (v + w * 8)) ::
      ("%inc12.us.i.i603.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%shr.i.i596.i.i.lcssa.off0" "%arrayidx14.us.i.i604.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hoff)
    (lookupName_cons_self ..)]
  simp only [denoteCode_nil, bus601Env, stateAt]

theorem bus601_step {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64}
    (hpc : s.pc = "while.body.us.i.i601.i.i")
    (hc : lookupName env "%108" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i587.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i596.i.i.lcssa.off0" = some (.int 64 off)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus601Env env v w c)
        { s with mem := writeBytes s.mem (v + w * 8) (natToBytes off.toNat 8),
                 pc := "stk_mul_u64.exit605.i.i",
                 pre := some "while.body.us.i.i601.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus601Env env v w c)
      { s with mem := writeBytes s.mem (v + w * 8) (natToBytes off.toNat 8) })
    (b := ⟨"while.body.us.i.i601.i.i", bus601Instrs,
      Term.br "stk_mul_u64.exit605.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus601_find
  · simpa only [stateAt] using bus601_denote hc hv hw hwv hpos hoff
  · simp only [execTerm, stateAt, hpc]

/-- The `%92`-count rung's residue join. -/
def unr555Specs : List PhiSpec :=
  [{ dst := "%add4.i.i550.i.i.lcssa.ph", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))] },
   { dst := "%shr.i.i552.i.i.lcssa.ph.off0", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))] },
   { dst := "%indvars.iv.i.i545.i.i.unr", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))] },
   { dst := "%carry.029.i.i546.i.i.unr", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                  ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))] }]

def unr555Instrs : List Instr :=
  [Instr.icmp "%lcmp.mod1064.not" (IPred.eq) 64 (Operand.reg "%xtraiter1062")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

def unr555Block : List Instr := unr555Specs.map PhiSpec.instr ++ unr555Instrs

theorem unr555_find :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i.unr-lcssa" =
      some ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa", unr555Block,
        Term.condbr (Operand.reg "%lcmp.mod1064.not")
          "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"⟩ := by
  simp only [unr555Block, unr555Instrs, unr555Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i555_i_i_unr_lcssa

def unr555Env (env : Env) (a4 : BitVec 128) (off : BitVec 64) (iv : BitVec 64)
    (cy : BitVec 128) (xt : BitVec 64) : Env :=
  ("%lcmp.mod1064.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i.i546.i.i.unr", .int 128 cy) ::
  ("%indvars.iv.i.i545.i.i.unr", .int 64 iv) ::
  ("%shr.i.i552.i.i.lcssa.ph.off0", .int 64 off) ::
  ("%add4.i.i550.i.i.lcssa.ph", .int 128 a4) :: env

theorem unr555_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1062" = some (.int 64 xt)) :
    denoteCode calls unr555Block (stateAt env s) =
      some (stateAt (unr555Env env a4 off iv cy xt) s) := by
  have hsel : PhiSelects (stateAt env s) pre unr555Specs
      [("%add4.i.i550.i.i.lcssa.ph", .int 128 a4),
       ("%shr.i.i552.i.i.lcssa.ph.off0", .int 64 off),
       ("%indvars.iv.i.i545.i.i.unr", .int 64 iv),
       ("%carry.029.i.i546.i.i.unr", .int 128 cy)] := by
    simp only [unr555Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    constructor
    · exact hop3
    · exact hov3
    constructor
    · exact hop4
    · exact hov4
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := unr555Specs)
    (vs := [("%add4.i.i550.i.i.lcssa.ph", .int 128 a4),
      ("%shr.i.i552.i.i.lcssa.ph.off0", .int 64 off),
      ("%indvars.iv.i.i545.i.i.unr", .int 64 iv),
      ("%carry.029.i.i546.i.i.unr", .int 128 cy)])
    (rest := unr555Instrs) hpre hsel (by decide)
  unfold unr555Block
  rw [h]
  simp only [runCells]
  unfold unr555Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.029.i.i546.i.i.unr", .int 128 cy) ::
      ("%indvars.iv.i.i545.i.i.unr", .int 64 iv) ::
      ("%shr.i.i552.i.i.lcssa.ph.off0", .int 64 off) ::
      ("%add4.i.i550.i.i.lcssa.ph", .int 128 a4) :: env) s
    "%lcmp.mod1064.not" "%xtraiter1062" .eq
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact hxt)]
  simp only [denoteCode_nil, unr555Env, stateAt]

theorem unr555_step_join {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1062" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr555Env env a4 off iv cy xt)
        { s with pc := "while.cond.preheader.i.i555.i.i",
                 pre := some "while.cond.preheader.i.i555.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr555Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa", unr555Block,
      Term.condbr (Operand.reg "%lcmp.mod1064.not")
        "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr555_find
  · simpa only [stateAt] using unr555_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_one (s := stateAt (unr555Env env a4 off iv cy xt) s)
      "%lcmp.mod1064.not" "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"
      (by simp [unr555Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem unr555_step_peel {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i550.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1093"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i553.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i542.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i555.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i552.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1062" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr555Env env a4 off iv cy xt)
        { s with pc := "for.body.i.i544.i.i.epil",
                 pre := some "while.cond.preheader.i.i555.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr555Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i.unr-lcssa", unr555Block,
      Term.condbr (Operand.reg "%lcmp.mod1064.not")
        "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr555_find
  · simpa only [stateAt] using unr555_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_zero (s := stateAt (unr555Env env a4 off iv cy xt) s)
      "%lcmp.mod1064.not" "while.cond.preheader.i.i555.i.i" "for.body.i.i544.i.i.epil"
      (by simp [unr555Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! ##### The residue joins of the other two nests -/

/-- The `%inc12`-count rung's residue join. -/
def unr577Specs : List PhiSpec :=
  [{ dst := "%add4.i.i572.i.i.lcssa.ph", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))] },
   { dst := "%shr.i.i574.i.i.lcssa.ph.off0", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))] },
   { dst := "%indvars.iv.i.i567.i.i.unr", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))] },
   { dst := "%carry.029.i.i568.i.i.unr", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                  ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))] }]

def unr577Instrs : List Instr :=
  [Instr.icmp "%lcmp.mod1085.not" (IPred.eq) 64 (Operand.reg "%xtraiter1083")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

def unr577Block : List Instr := unr577Specs.map PhiSpec.instr ++ unr577Instrs

theorem unr577_find :
    numFastBody.findBlock "while.cond.preheader.i.i577.i.i.unr-lcssa" =
      some ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", unr577Block,
        Term.condbr (Operand.reg "%lcmp.mod1085.not")
          "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩ := by
  simp only [unr577Block, unr577Instrs, unr577Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i577_i_i_unr_lcssa

def unr577Env (env : Env) (a4 : BitVec 128) (off : BitVec 64) (iv : BitVec 64)
    (cy : BitVec 128) (xt : BitVec 64) : Env :=
  ("%lcmp.mod1085.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i.i568.i.i.unr", .int 128 cy) ::
  ("%indvars.iv.i.i567.i.i.unr", .int 64 iv) ::
  ("%shr.i.i574.i.i.lcssa.ph.off0", .int 64 off) ::
  ("%add4.i.i572.i.i.lcssa.ph", .int 128 a4) :: env

theorem unr577_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 xt)) :
    denoteCode calls unr577Block (stateAt env s) =
      some (stateAt (unr577Env env a4 off iv cy xt) s) := by
  have hsel : PhiSelects (stateAt env s) pre unr577Specs
      [("%add4.i.i572.i.i.lcssa.ph", .int 128 a4),
       ("%shr.i.i574.i.i.lcssa.ph.off0", .int 64 off),
       ("%indvars.iv.i.i567.i.i.unr", .int 64 iv),
       ("%carry.029.i.i568.i.i.unr", .int 128 cy)] := by
    simp only [unr577Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    constructor
    · exact hop3
    · exact hov3
    constructor
    · exact hop4
    · exact hov4
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := unr577Specs)
    (vs := [("%add4.i.i572.i.i.lcssa.ph", .int 128 a4),
      ("%shr.i.i574.i.i.lcssa.ph.off0", .int 64 off),
      ("%indvars.iv.i.i567.i.i.unr", .int 64 iv),
      ("%carry.029.i.i568.i.i.unr", .int 128 cy)])
    (rest := unr577Instrs) hpre hsel (by decide)
  unfold unr577Block
  rw [h]
  simp only [runCells]
  unfold unr577Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.029.i.i568.i.i.unr", .int 128 cy) ::
      ("%indvars.iv.i.i567.i.i.unr", .int 64 iv) ::
      ("%shr.i.i574.i.i.lcssa.ph.off0", .int 64 off) ::
      ("%add4.i.i572.i.i.lcssa.ph", .int 128 a4) :: env) s
    "%lcmp.mod1085.not" "%xtraiter1083" .eq
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact hxt)]
  simp only [denoteCode_nil, unr577Env, stateAt]

theorem unr577_step_join {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr577Env env a4 off iv cy xt)
        { s with pc := "while.cond.preheader.i.i577.i.i",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr577Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", unr577Block,
      Term.condbr (Operand.reg "%lcmp.mod1085.not")
        "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr577_find
  · simpa only [stateAt] using unr577_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_one (s := stateAt (unr577Env env a4 off iv cy xt) s)
      "%lcmp.mod1085.not" "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"
      (by simp [unr577Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem unr577_step_peel {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i577.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i572.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1099"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i575.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i564.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i577.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i574.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1083" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr577Env env a4 off iv cy xt)
        { s with pc := "for.body.i.i566.i.i.epil",
                 pre := some "while.cond.preheader.i.i577.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr577Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i577.i.i.unr-lcssa", unr577Block,
      Term.condbr (Operand.reg "%lcmp.mod1085.not")
        "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr577_find
  · simpa only [stateAt] using unr577_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_zero (s := stateAt (unr577Env env a4 off iv cy xt) s)
      "%lcmp.mod1085.not" "while.cond.preheader.i.i577.i.i" "for.body.i.i566.i.i.epil"
      (by simp [unr577Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `%108`-count rung's residue join. -/
def unr599Specs : List PhiSpec :=
  [{ dst := "%add4.i.i594.i.i.lcssa.ph", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))] },
   { dst := "%shr.i.i596.i.i.lcssa.ph.off0", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))] },
   { dst := "%indvars.iv.i.i589.i.i.unr", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))] },
   { dst := "%carry.029.i.i590.i.i.unr", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                  ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))] }]

def unr599Instrs : List Instr :=
  [Instr.icmp "%lcmp.mod1071.not" (IPred.eq) 64 (Operand.reg "%xtraiter1069")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

def unr599Block : List Instr := unr599Specs.map PhiSpec.instr ++ unr599Instrs

theorem unr599_find :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i.unr-lcssa" =
      some ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa", unr599Block,
        Term.condbr (Operand.reg "%lcmp.mod1071.not")
          "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"⟩ := by
  simp only [unr599Block, unr599Instrs, unr599Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i599_i_i_unr_lcssa

def unr599Env (env : Env) (a4 : BitVec 128) (off : BitVec 64) (iv : BitVec 64)
    (cy : BitVec 128) (xt : BitVec 64) : Env :=
  ("%lcmp.mod1071.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i.i590.i.i.unr", .int 128 cy) ::
  ("%indvars.iv.i.i589.i.i.unr", .int 64 iv) ::
  ("%shr.i.i596.i.i.lcssa.ph.off0", .int 64 off) ::
  ("%add4.i.i594.i.i.lcssa.ph", .int 128 a4) :: env

theorem unr599_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1069" = some (.int 64 xt)) :
    denoteCode calls unr599Block (stateAt env s) =
      some (stateAt (unr599Env env a4 off iv cy xt) s) := by
  have hsel : PhiSelects (stateAt env s) pre unr599Specs
      [("%add4.i.i594.i.i.lcssa.ph", .int 128 a4),
       ("%shr.i.i596.i.i.lcssa.ph.off0", .int 64 off),
       ("%indvars.iv.i.i589.i.i.unr", .int 64 iv),
       ("%carry.029.i.i590.i.i.unr", .int 128 cy)] := by
    simp only [unr599Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    constructor
    · exact hop3
    · exact hov3
    constructor
    · exact hop4
    · exact hov4
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := unr599Specs)
    (vs := [("%add4.i.i594.i.i.lcssa.ph", .int 128 a4),
      ("%shr.i.i596.i.i.lcssa.ph.off0", .int 64 off),
      ("%indvars.iv.i.i589.i.i.unr", .int 64 iv),
      ("%carry.029.i.i590.i.i.unr", .int 128 cy)])
    (rest := unr599Instrs) hpre hsel (by decide)
  unfold unr599Block
  rw [h]
  simp only [runCells]
  unfold unr599Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.029.i.i590.i.i.unr", .int 128 cy) ::
      ("%indvars.iv.i.i589.i.i.unr", .int 64 iv) ::
      ("%shr.i.i596.i.i.lcssa.ph.off0", .int 64 off) ::
      ("%add4.i.i594.i.i.lcssa.ph", .int 128 a4) :: env) s
    "%lcmp.mod1071.not" "%xtraiter1069" .eq
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact hxt)]
  simp only [denoteCode_nil, unr599Env, stateAt]

theorem unr599_step_join {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1069" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr599Env env a4 off iv cy xt)
        { s with pc := "while.cond.preheader.i.i599.i.i",
                 pre := some "while.cond.preheader.i.i599.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr599Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa", unr599Block,
      Term.condbr (Operand.reg "%lcmp.mod1071.not")
        "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr599_find
  · simpa only [stateAt] using unr599_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_one (s := stateAt (unr599Env env a4 off iv cy xt) s)
      "%lcmp.mod1071.not" "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"
      (by simp [unr599Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem unr599_step_peel {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i594.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1095"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i597.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i586.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i599.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i596.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1069" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr599Env env a4 off iv cy xt)
        { s with pc := "for.body.i.i588.i.i.epil",
                 pre := some "while.cond.preheader.i.i599.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr599Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i.unr-lcssa", unr599Block,
      Term.condbr (Operand.reg "%lcmp.mod1071.not")
        "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr599_find
  · simpa only [stateAt] using unr599_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_zero (s := stateAt (unr599Env env a4 off iv cy xt) s)
      "%lcmp.mod1071.not" "while.cond.preheader.i.i599.i.i" "for.body.i.i588.i.i.epil"
      (by simp [unr599Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `if.end195`-reaching nest's residue join. -/
def unr622Specs : List PhiSpec :=
  [{ dst := "%add4.i.i617.i.i.lcssa.ph", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))] },
   { dst := "%shr.i.i619.i.i.lcssa.ph.off0", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
                  ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))] },
   { dst := "%indvars.iv.i.i612.i.i.unr", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))] },
   { dst := "%carry.029.i.i613.i.i.unr", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
                  ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))] }]

def unr622Instrs : List Instr :=
  [Instr.icmp "%lcmp.mod1078.not" (IPred.eq) 64 (Operand.reg "%xtraiter1076")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

def unr622Block : List Instr := unr622Specs.map PhiSpec.instr ++ unr622Instrs

theorem unr622_find :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i.unr-lcssa" =
      some ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa", unr622Block,
        Term.condbr (Operand.reg "%lcmp.mod1078.not")
          "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"⟩ := by
  simp only [unr622Block, unr622Instrs, unr622Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i622_i_i_unr_lcssa

def unr622Env (env : Env) (a4 : BitVec 128) (off : BitVec 64) (iv : BitVec 64)
    (cy : BitVec 128) (xt : BitVec 64) : Env :=
  ("%lcmp.mod1078.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i.i613.i.i.unr", .int 128 cy) ::
  ("%indvars.iv.i.i612.i.i.unr", .int 64 iv) ::
  ("%shr.i.i619.i.i.lcssa.ph.off0", .int 64 off) ::
  ("%add4.i.i617.i.i.lcssa.ph", .int 128 a4) :: env

theorem unr622_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1076" = some (.int 64 xt)) :
    denoteCode calls unr622Block (stateAt env s) =
      some (stateAt (unr622Env env a4 off iv cy xt) s) := by
  have hsel : PhiSelects (stateAt env s) pre unr622Specs
      [("%add4.i.i617.i.i.lcssa.ph", .int 128 a4),
       ("%shr.i.i619.i.i.lcssa.ph.off0", .int 64 off),
       ("%indvars.iv.i.i612.i.i.unr", .int 64 iv),
       ("%carry.029.i.i613.i.i.unr", .int 128 cy)] := by
    simp only [unr622Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    constructor
    · exact hop3
    · exact hov3
    constructor
    · exact hop4
    · exact hov4
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := unr622Specs)
    (vs := [("%add4.i.i617.i.i.lcssa.ph", .int 128 a4),
      ("%shr.i.i619.i.i.lcssa.ph.off0", .int 64 off),
      ("%indvars.iv.i.i612.i.i.unr", .int 64 iv),
      ("%carry.029.i.i613.i.i.unr", .int 128 cy)])
    (rest := unr622Instrs) hpre hsel (by decide)
  unfold unr622Block
  rw [h]
  simp only [runCells]
  unfold unr622Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.029.i.i613.i.i.unr", .int 128 cy) ::
      ("%indvars.iv.i.i612.i.i.unr", .int 64 iv) ::
      ("%shr.i.i619.i.i.lcssa.ph.off0", .int 64 off) ::
      ("%add4.i.i617.i.i.lcssa.ph", .int 128 a4) :: env) s
    "%lcmp.mod1078.not" "%xtraiter1076" .eq
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide)]; exact hxt)]
  simp only [denoteCode_nil, unr622Env, stateAt]

theorem unr622_step_join {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1076" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr622Env env a4 off iv cy xt)
        { s with pc := "while.cond.preheader.i.i622.i.i",
                 pre := some "while.cond.preheader.i.i622.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr622Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa", unr622Block,
      Term.condbr (Operand.reg "%lcmp.mod1078.not")
        "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr622_find
  · simpa only [stateAt] using unr622_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_one (s := stateAt (unr622Env env a4 off iv cy xt) s)
      "%lcmp.mod1078.not" "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"
      (by simp [unr622Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem unr622_step_peel {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 op4 : Operand}
    {a4 : BitVec 128} {off : BitVec 64} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i.unr-lcssa") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%add4.i.i617.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a4))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm Const.poison)),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%extract.t1097"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%indvars.iv.next.i.i620.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 64 iv))
    (hop4 : phiIncoming pre
      [("for.body.lr.ph.i.i608.i.i", (Operand.imm (Const.int 128 0x00000000000000000000000000000000#128))),
       ("while.cond.preheader.i.i622.i.i.unr-lcssa.loopexit", (Operand.reg "%shr.i.i619.i.i.3"))] = some op4)
    (hov4 : evalOperand (stateAt env s) op4 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1076" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr622Env env a4 off iv cy xt)
        { s with pc := "for.body.i.i611.i.i.epil",
                 pre := some "while.cond.preheader.i.i622.i.i.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr622Env env a4 off iv cy xt) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i.unr-lcssa", unr622Block,
      Term.condbr (Operand.reg "%lcmp.mod1078.not")
        "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr622_find
  · simpa only [stateAt] using unr622_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hop4 hov4 hxt
  · rw [numFast_execTerm_condbr_zero (s := stateAt (unr622Env env a4 off iv cy xt) s)
      "%lcmp.mod1078.not" "while.cond.preheader.i.i622.i.i" "for.body.i.i611.i.i.epil"
      (by simp [unr622Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `if.end195`-reaching carry store. -/
def bus624Instrs : List Instr :=
  [Instr.binop "%inc12.us.i.i626.i.i" (BinOp.add) 32 (Operand.reg "%116")
     (Operand.imm (Const.int 32 0x0000000000000001#32)),
   Instr.gep "%arrayidx14.us.i.i627.i.i" (Ty.int 64) (Operand.reg "%v.i.i")
     (Operand.reg "%wide.trip.count.i.i610.i.i"),
   Instr.store (Ty.int 64) (Operand.reg "%shr.i.i619.i.i.lcssa.off0")
     (Operand.reg "%arrayidx14.us.i.i627.i.i"),
   Instr.store (Ty.int 32) (Operand.reg "%inc12.us.i.i626.i.i")
     (Operand.reg "%n.i.i.i")]

theorem bus624_find :
    numFastBody.findBlock "while.body.us.i.i624.i.i" =
      some ⟨"while.body.us.i.i624.i.i", bus624Instrs, Term.br "if.end195.i.i"⟩ := by
  simpa only [bus624Instrs] using numFast_findBlock_while_body_us_i_i624_i_i

def bus624Env (env : Env) (v : Nat) (w : Nat) (c : BitVec 32) : Env :=
  ("%arrayidx14.us.i.i627.i.i", .ptr (v + w * 8)) ::
  ("%inc12.us.i.i626.i.i", .int 32 (c + 0x00000001#32)) :: env

theorem bus624_denote {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64} {n : Nat}
    (hc : lookupName env "%116" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i619.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i.i.i" = some (.ptr n)) :
    denoteCode calls bus624Instrs (stateAt env s) =
      some (stateAt (bus624Env env v w c)
        { s with mem := writeBytes (writeBytes s.mem (v + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) }) := by
  unfold bus624Instrs
  rw [JsonScanLane.denoteCode_add_imm_w calls env s "%inc12.us.i.i626.i.i" "%116" 32 hc]
  rw [NumFastTier1.denoteCode_gep64_reg calls
    (("%inc12.us.i.i626.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%arrayidx14.us.i.i627.i.i" "%v.i.i" "%wide.trip.count.i.i610.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hv)
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact hw) (by rw [hwv]; exact hpos)]
  rw [hwv]
  rw [denoteCode_store64 calls
    (("%arrayidx14.us.i.i627.i.i", .ptr (v + w * 8)) ::
      ("%inc12.us.i.i626.i.i", .int 32 (c + 0x00000001#32)) :: env) s
    "%shr.i.i619.i.i.lcssa.off0" "%arrayidx14.us.i.i627.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hoff)
    (lookupName_cons_self ..)]
  rw [denoteCode_store32 calls
    (("%arrayidx14.us.i.i627.i.i", .ptr (v + w * 8)) ::
      ("%inc12.us.i.i626.i.i", .int 32 (c + 0x00000001#32)) :: env)
    { s with mem := writeBytes s.mem (v + w * 8) (natToBytes off.toNat 8) }
    "%inc12.us.i.i626.i.i" "%n.i.i.i"
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)
    (by rw [lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hn)]
  simp only [denoteCode_nil, bus624Env, stateAt]

theorem bus624_step {calls : Calls} {env : Env} {s : State}
    {c : BitVec 32} {v w : Nat} {wv off : BitVec 64} {n : Nat}
    (hpc : s.pc = "while.body.us.i.i624.i.i")
    (hc : lookupName env "%116" = some (.int 32 c))
    (hv : lookupName env "%v.i.i" = some (.ptr v))
    (hw : lookupName env "%wide.trip.count.i.i610.i.i" = some (.int 64 wv))
    (hwv : (wv.signExtend 64).toNat = w) (hpos : w < 2 ^ 63)
    (hoff : lookupName env "%shr.i.i619.i.i.lcssa.off0" = some (.int 64 off))
    (hn : lookupName env "%n.i.i.i" = some (.ptr n)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (bus624Env env v w c)
        { s with mem := writeBytes (writeBytes s.mem (v + w * 8)
            (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4),
                 pc := "if.end195.i.i", pre := some "while.body.us.i.i624.i.i" }) := by
  refine numFast_step_at (s' := stateAt (bus624Env env v w c)
      { s with mem := writeBytes (writeBytes s.mem (v + w * 8)
          (natToBytes off.toNat 8)) n (natToBytes (c + 0x00000001#32).toNat 4) })
    (b := ⟨"while.body.us.i.i624.i.i", bus624Instrs, Term.br "if.end195.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using bus624_find
  · simpa only [stateAt] using bus624_denote hc hv hw hwv hpos hoff hn
  · simp only [execTerm, stateAt, hpc]

/-- The `if.end195`-reaching nest's head: the table row, its widen and the
unroll bound. -/
def lrph608Instrs : List Instr :=
  [Instr.gep "%arrayidx194.i.i" (Ty.int 64) (Operand.global "@NUMF_EL1_P10")
     (Operand.reg "%k183.0.lcssa.i.i"),
   Instr.load "%117" (Ty.int 64) (Operand.reg "%arrayidx194.i.i"),
   Instr.zext "%conv3.i.i609.i.i" 64 128 (Operand.reg "%117"),
   Instr.zext "%wide.trip.count.i.i610.i.i" 32 64 (Operand.reg "%116"),
   Instr.binop "%xtraiter1076" (BinOp.and) 64
     (Operand.reg "%wide.trip.count.i.i610.i.i") (Operand.imm (Const.int 64 0x0000000000000003#64)),
   Instr.icmp "%118" (IPred.ult) 32 (Operand.reg "%116")
     (Operand.imm (Const.int 32 0x0000000000000004#32))]

theorem lrph608_find :
    numFastBody.findBlock "for.body.lr.ph.i.i608.i.i" =
      some ⟨"for.body.lr.ph.i.i608.i.i", lrph608Instrs,
        Term.condbr (Operand.reg "%118") "while.cond.preheader.i.i622.i.i.unr-lcssa"
          "for.body.lr.ph.i.i608.i.i.new"⟩ := by
  simpa only [lrph608Instrs] using numFast_findBlock_for_body_lr_ph_i_i608_i_i

def lrph608Env (env : Env) (p : Nat) (kk : BitVec 64) (w : BitVec 64) (c : BitVec 32) : Env :=
  ("%118", .int 1 (evalICmp .ult c 0x0000000000000004#32)) ::
  ("%xtraiter1076", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
  ("%wide.trip.count.i.i610.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) ::
  ("%conv3.i.i609.i.i", .int 128 (BitVec.ofNat 128 w.toNat)) ::
  ("%117", .int 64 w) ::
  ("%arrayidx194.i.i", .ptr (p + (kk.signExtend 64).toNat * 8)) :: env

theorem lrph608_denote {calls : Calls} {env : Env} {s : State} {p : Nat}
    {kk w : BitVec 64} {c : BitVec 32}
    (hP : lookupName env "@NUMF_EL1_P10" = some (.ptr p))
    (hkk : lookupName env "%k183.0.lcssa.i.i" = some (.int 64 kk))
    (hpos : (kk.signExtend 64).toNat < 2 ^ 63)
    (hw : readBytes s.mem (p + (kk.signExtend 64).toNat * 8) 8
      = some (natToBytes w.toNat 8))
    (hc : lookupName env "%116" = some (.int 32 c)) :
    denoteCode calls lrph608Instrs (stateAt env s) =
      some (stateAt (lrph608Env env p kk w c) s) := by
  unfold lrph608Instrs
  rw [NumFastTier1.denoteCode_gep64_global calls env s "%arrayidx194.i.i"
    "@NUMF_EL1_P10" "%k183.0.lcssa.i.i" hP hkk hpos]
  rw [denoteCode_load64 calls (("%arrayidx194.i.i",
      .ptr (p + (kk.signExtend 64).toNat * 8)) :: env) s "%117" "%arrayidx194.i.i"
    (lookupName_cons_self ..) hw]
  rw [denoteCode_zext calls
    (("%117", .int 64 w) :: ("%arrayidx194.i.i",
      .ptr (p + (kk.signExtend 64).toNat * 8)) :: env) s
    "%conv3.i.i609.i.i" "%117" 64 128 (lookupName_cons_self ..)]
  rw [denoteCode_zext calls
    (("%conv3.i.i609.i.i", .int 128 (BitVec.ofNat 128 w.toNat)) ::
      ("%117", .int 64 w) :: ("%arrayidx194.i.i",
      .ptr (p + (kk.signExtend 64).toNat * 8)) :: env) s
    "%wide.trip.count.i.i610.i.i" "%116" 32 64
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc)]
  rw [denoteCode_and_imm calls
    (("%wide.trip.count.i.i610.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) ::
      ("%conv3.i.i609.i.i", .int 128 (BitVec.ofNat 128 w.toNat)) ::
      ("%117", .int 64 w) :: ("%arrayidx194.i.i",
      .ptr (p + (kk.signExtend 64).toNat * 8)) :: env) s
    "%xtraiter1076" "%wide.trip.count.i.i610.i.i" (lookupName_cons_self ..)]
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%xtraiter1076", .int 64 (BitVec.ofNat 64 c.toNat &&& 0x0000000000000003#64)) ::
      ("%wide.trip.count.i.i610.i.i", .int 64 (BitVec.ofNat 64 c.toNat)) ::
      ("%conv3.i.i609.i.i", .int 128 (BitVec.ofNat 128 w.toNat)) ::
      ("%117", .int 64 w) :: ("%arrayidx194.i.i",
      .ptr (p + (kk.signExtend 64).toNat * 8)) :: env) s
    "%118" "%116" .ult
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hc)]
  simp only [denoteCode_nil, lrph608Env, stateAt]

theorem lrph608_step_join {calls : Calls} {env : Env} {s : State} {p : Nat}
    {kk w : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i608.i.i")
    (hP : lookupName env "@NUMF_EL1_P10" = some (.ptr p))
    (hkk : lookupName env "%k183.0.lcssa.i.i" = some (.int 64 kk))
    (hpos : (kk.signExtend 64).toNat < 2 ^ 63)
    (hw : readBytes s.mem (p + (kk.signExtend 64).toNat * 8) 8
      = some (natToBytes w.toNat 8))
    (hc : lookupName env "%116" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph608Env env p kk w c)
        { s with pc := "while.cond.preheader.i.i622.i.i.unr-lcssa",
                 pre := some "for.body.lr.ph.i.i608.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph608Env env p kk w c) s)
    (b := ⟨"for.body.lr.ph.i.i608.i.i", lrph608Instrs,
      Term.condbr (Operand.reg "%118") "while.cond.preheader.i.i622.i.i.unr-lcssa"
        "for.body.lr.ph.i.i608.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph608_find
  · simpa only [stateAt] using lrph608_denote hP hkk hpos hw hc
  · rw [numFast_execTerm_condbr_one (s := stateAt (lrph608Env env p kk w c) s)
      "%118" "while.cond.preheader.i.i622.i.i.unr-lcssa"
      "for.body.lr.ph.i.i608.i.i.new" (by simp only [lrph608Env, stateAt]; exact lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

theorem lrph608_step_unroll {calls : Calls} {env : Env} {s : State} {p : Nat}
    {kk w : BitVec 64} {c : BitVec 32}
    (hpc : s.pc = "for.body.lr.ph.i.i608.i.i")
    (hP : lookupName env "@NUMF_EL1_P10" = some (.ptr p))
    (hkk : lookupName env "%k183.0.lcssa.i.i" = some (.int 64 kk))
    (hpos : (kk.signExtend 64).toNat < 2 ^ 63)
    (hw : readBytes s.mem (p + (kk.signExtend 64).toNat * 8) 8
      = some (natToBytes w.toNat 8))
    (hc : lookupName env "%116" = some (.int 32 c))
    (hbit : evalICmp .ult c 0x0000000000000004#32 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (lrph608Env env p kk w c)
        { s with pc := "for.body.lr.ph.i.i608.i.i.new",
                 pre := some "for.body.lr.ph.i.i608.i.i" }) := by
  refine numFast_step_at (s' := stateAt (lrph608Env env p kk w c) s)
    (b := ⟨"for.body.lr.ph.i.i608.i.i", lrph608Instrs,
      Term.condbr (Operand.reg "%118") "while.cond.preheader.i.i622.i.i.unr-lcssa"
        "for.body.lr.ph.i.i608.i.i.new"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using lrph608_find
  · simpa only [stateAt] using lrph608_denote hP hkk hpos hw hc
  · rw [numFast_execTerm_condbr_zero (s := stateAt (lrph608Env env p kk w c) s)
      "%118" "while.cond.preheader.i.i622.i.i.unr-lcssa"
      "for.body.lr.ph.i.i608.i.i.new" (by simp only [lrph608Env, stateAt]; exact lookupName_cons_self ..) hbit]
    simp only [stateAt, hpc]

/-! ##### The residue joins: `…unr-lcssa`

The four `phi`s take the unrolled body's last values on the loop-exit edge and
`poison` on the direct head edge; the test is the residue count's zero.  The
statement keeps the selected operands and their values as hypotheses, so both
edges are instances of it.
-/

def unr517Specs : List PhiSpec :=
  [{ dst := "%shr.i535.i.i.lcssa.ph", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
                  ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] },
   { dst := "%indvars.iv.i528.i.i.unr", ty := Ty.int 64,
     incoming := [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
                  ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))] },
   { dst := "%carry.029.i529.i.i.unr", ty := Ty.int 128,
     incoming := [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
                  ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] }]

def unr517Instrs : List Instr :=
  [Instr.icmp "%lcmp.mod1051.not" (IPred.eq) 64 (Operand.reg "%xtraiter1049")
     (Operand.imm (Const.int 64 0x0000000000000000#64))]

def unr517Block : List Instr := unr517Specs.map PhiSpec.instr ++ unr517Instrs

theorem unr517_find :
    numFastBody.findBlock "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" =
      some ⟨"while.cond.preheader.i517.i.i.loopexit.unr-lcssa", unr517Block,
        Term.condbr (Operand.reg "%lcmp.mod1051.not")
          "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"⟩ := by
  simp only [unr517Block, unr517Instrs, unr517Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i517_i_i_loopexit_unr_lcssa

def unr517Env (env : Env) (shr : BitVec 128) (iv : BitVec 64) (cy : BitVec 128)
    (xt : BitVec 64) : Env :=
  ("%lcmp.mod1051.not", .int 1 (evalICmp .eq xt 0x0000000000000000#64)) ::
  ("%carry.029.i529.i.i.unr", .int 128 cy) ::
  ("%indvars.iv.i528.i.i.unr", .int 64 iv) ::
  ("%shr.i535.i.i.lcssa.ph", .int 128 shr) :: env

theorem unr517_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 : Operand}
    {shr : BitVec 128} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 shr))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 iv))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1049" = some (.int 64 xt)) :
    denoteCode calls unr517Block (stateAt env s) =
      some (stateAt (unr517Env env shr iv cy xt) s) := by
  have hsel : PhiSelects (stateAt env s) pre unr517Specs
      [("%shr.i535.i.i.lcssa.ph", .int 128 shr),
       ("%indvars.iv.i528.i.i.unr", .int 64 iv),
       ("%carry.029.i529.i.i.unr", .int 128 cy)] := by
    simp only [unr517Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    constructor
    · exact hop3
    · exact hov3
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := unr517Specs)
    (vs := [("%shr.i535.i.i.lcssa.ph", .int 128 shr),
      ("%indvars.iv.i528.i.i.unr", .int 64 iv),
      ("%carry.029.i529.i.i.unr", .int 128 cy)])
    (rest := unr517Instrs) hpre hsel (by decide)
  unfold unr517Block
  rw [h]
  simp only [runCells]
  unfold unr517Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%carry.029.i529.i.i.unr", .int 128 cy) ::
      ("%indvars.iv.i528.i.i.unr", .int 64 iv) ::
      ("%shr.i535.i.i.lcssa.ph", .int 128 shr) :: env) s
    "%lcmp.mod1051.not" "%xtraiter1049" .eq
    (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_ne _ _ (by decide),
      lookupName_cons_ne _ _ (by decide)]; exact hxt)]
  simp only [denoteCode_nil, unr517Env, stateAt]

theorem unr517_step_join {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 : Operand}
    {shr : BitVec 128} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i517.i.i.loopexit.unr-lcssa")
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 shr))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 iv))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1049" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr517Env env shr iv cy xt)
        { s with pc := "while.cond.preheader.i517.i.i",
                 pre := some "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr517Env env shr iv cy xt) s)
    (b := ⟨"while.cond.preheader.i517.i.i.loopexit.unr-lcssa", unr517Block,
      Term.condbr (Operand.reg "%lcmp.mod1051.not")
        "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr517_find
  · simpa only [stateAt] using unr517_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hxt
  · rw [numFast_execTerm_condbr_one (s := stateAt (unr517Env env shr iv cy xt) s)
      "%lcmp.mod1051.not" "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"
      (by simp [unr517Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem unr517_step_peel {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 op3 : Operand}
    {shr : BitVec 128} {iv : BitVec 64} {cy : BitVec 128} {xt : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i517.i.i.loopexit.unr-lcssa")
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm Const.poison)),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 shr))
    (hop2 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.imm (Const.int 64 0x0000000000000000#64))),
       ("for.body.i527.i.i", (Operand.reg "%indvars.iv.next.i536.i.i.3"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 iv))
    (hop3 : phiIncoming pre
      [("for.body.lr.ph.i525.i.i", (Operand.reg "%conv.i514.i.i")),
       ("for.body.i527.i.i", (Operand.reg "%shr.i535.i.i.3"))] = some op3)
    (hov3 : evalOperand (stateAt env s) op3 = some (.int 128 cy))
    (hxt : lookupName env "%xtraiter1049" = some (.int 64 xt))
    (hbit : evalICmp .eq xt 0x0000000000000000#64 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (unr517Env env shr iv cy xt)
        { s with pc := "for.body.i527.i.i.epil",
                 pre := some "while.cond.preheader.i517.i.i.loopexit.unr-lcssa" }) := by
  refine numFast_step_at (s' := stateAt (unr517Env env shr iv cy xt) s)
    (b := ⟨"while.cond.preheader.i517.i.i.loopexit.unr-lcssa", unr517Block,
      Term.condbr (Operand.reg "%lcmp.mod1051.not")
        "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using unr517_find
  · simpa only [stateAt] using unr517_denote hpre hop1 hov1 hop2 hov2 hop3 hov3 hxt
  · rw [numFast_execTerm_condbr_zero (s := stateAt (unr517Env env shr iv cy xt) s)
      "%lcmp.mod1051.not" "while.cond.preheader.i517.i.i" "for.body.i527.i.i.epil"
      (by simp [unr517Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! ##### The rungs' tests

The two carried `phi`s (the `i128` sum and its shifted word) meet the peeled
loop's value, and the `2 ^ 64` comparison decides whether the carry's high word
is stored past the retained nineteen groups.
-/

def pre555Specs : List PhiSpec :=
  [{ dst := "%add4.i.i550.i.i.lcssa", ty := Ty.int 128,
     incoming := [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
                  ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))] },
   { dst := "%shr.i.i552.i.i.lcssa.off0", ty := Ty.int 64,
     incoming := [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
                  ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))] }]

def pre555Instrs : List Instr :=
  [Instr.icmp "%tobool.not31.i.i556.i.i" (IPred.ult) 128
     (Operand.reg "%add4.i.i550.i.i.lcssa")
     (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))]

def pre555Block : List Instr := pre555Specs.map PhiSpec.instr ++ pre555Instrs

theorem pre555_find :
    numFastBody.findBlock "while.cond.preheader.i.i555.i.i" =
      some ⟨"while.cond.preheader.i.i555.i.i", pre555Block,
        Term.condbr (Operand.reg "%tobool.not31.i.i556.i.i") "if.end198.i.i"
          "while.body.us.i.i557.i.i"⟩ := by
  simp only [pre555Block, pre555Instrs, pre555Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i555_i_i

def pre555Env (env : Env) (a : BitVec 128) (off : BitVec 64) : Env :=
  ("%tobool.not31.i.i556.i.i", .int 1 (evalICmp .ult a
    0x00000000000000010000000000000000#128)) ::
  ("%shr.i.i552.i.i.lcssa.off0", .int 64 off) ::
  ("%add4.i.i550.i.i.lcssa", .int 128 a) :: env

theorem pre555_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off)) :
    denoteCode calls pre555Block (stateAt env s) =
      some (stateAt (pre555Env env a off) s) := by
  have hsel : PhiSelects (stateAt env s) pre pre555Specs
      [("%add4.i.i550.i.i.lcssa", .int 128 a),
       ("%shr.i.i552.i.i.lcssa.off0", .int 64 off)] := by
    simp only [pre555Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := pre555Specs)
    (vs := [("%add4.i.i550.i.i.lcssa", .int 128 a),
      ("%shr.i.i552.i.i.lcssa.off0", .int 64 off)])
    (rest := pre555Instrs) hpre hsel (by decide)
  unfold pre555Block
  rw [h]
  simp only [runCells]
  unfold pre555Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%shr.i.i552.i.i.lcssa.off0", .int 64 off) ::
      ("%add4.i.i550.i.i.lcssa", .int 128 a) :: env) s
    "%tobool.not31.i.i556.i.i" "%add4.i.i550.i.i.lcssa" .ult
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, pre555Env, stateAt]

theorem pre555_step_ladder {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre555Env env a off)
        { s with pc := "if.end198.i.i",
                 pre := some "while.cond.preheader.i.i555.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre555Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i", pre555Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i556.i.i") "if.end198.i.i"
        "while.body.us.i.i557.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre555_find
  · simpa only [stateAt] using pre555_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_one (s := stateAt (pre555Env env a off) s)
      "%tobool.not31.i.i556.i.i" "if.end198.i.i" "while.body.us.i.i557.i.i"
      (by simp [pre555Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem pre555_step_store {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i555.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%add4.i.i550.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%add4.i.i550.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i555.i.i.unr-lcssa", (Operand.reg "%shr.i.i552.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i555.i.i.epilog-lcssa", (Operand.reg "%extract.t1092"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre555Env env a off)
        { s with pc := "while.body.us.i.i557.i.i",
                 pre := some "while.cond.preheader.i.i555.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre555Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i555.i.i", pre555Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i556.i.i") "if.end198.i.i"
        "while.body.us.i.i557.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre555_find
  · simpa only [stateAt] using pre555_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pre555Env env a off) s)
      "%tobool.not31.i.i556.i.i" "if.end198.i.i" "while.body.us.i.i557.i.i"
      (by simp [pre555Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `%108`-count rung's test, at `stk_mul_u64.exit605.i.i` and its store. -/
def pre599Specs : List PhiSpec :=
  [{ dst := "%add4.i.i594.i.i.lcssa", ty := Ty.int 128,
     incoming := [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
                  ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))] },
   { dst := "%shr.i.i596.i.i.lcssa.off0", ty := Ty.int 64,
     incoming := [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
                  ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))] }]

def pre599Instrs : List Instr :=
  [Instr.icmp "%tobool.not31.i.i600.i.i" (IPred.ult) 128
     (Operand.reg "%add4.i.i594.i.i.lcssa")
     (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))]

def pre599Block : List Instr := pre599Specs.map PhiSpec.instr ++ pre599Instrs

theorem pre599_find :
    numFastBody.findBlock "while.cond.preheader.i.i599.i.i" =
      some ⟨"while.cond.preheader.i.i599.i.i", pre599Block,
        Term.condbr (Operand.reg "%tobool.not31.i.i600.i.i") "stk_mul_u64.exit605.i.i"
          "while.body.us.i.i601.i.i"⟩ := by
  simp only [pre599Block, pre599Instrs, pre599Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i599_i_i

def pre599Env (env : Env) (a : BitVec 128) (off : BitVec 64) : Env :=
  ("%tobool.not31.i.i600.i.i", .int 1 (evalICmp .ult a
    0x00000000000000010000000000000000#128)) ::
  ("%shr.i.i596.i.i.lcssa.off0", .int 64 off) ::
  ("%add4.i.i594.i.i.lcssa", .int 128 a) :: env

theorem pre599_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off)) :
    denoteCode calls pre599Block (stateAt env s) =
      some (stateAt (pre599Env env a off) s) := by
  have hsel : PhiSelects (stateAt env s) pre pre599Specs
      [("%add4.i.i594.i.i.lcssa", .int 128 a),
       ("%shr.i.i596.i.i.lcssa.off0", .int 64 off)] := by
    simp only [pre599Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := pre599Specs)
    (vs := [("%add4.i.i594.i.i.lcssa", .int 128 a),
      ("%shr.i.i596.i.i.lcssa.off0", .int 64 off)])
    (rest := pre599Instrs) hpre hsel (by decide)
  unfold pre599Block
  rw [h]
  simp only [runCells]
  unfold pre599Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%shr.i.i596.i.i.lcssa.off0", .int 64 off) ::
      ("%add4.i.i594.i.i.lcssa", .int 128 a) :: env) s
    "%tobool.not31.i.i600.i.i" "%add4.i.i594.i.i.lcssa" .ult
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, pre599Env, stateAt]

theorem pre599_step_exit {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre599Env env a off)
        { s with pc := "stk_mul_u64.exit605.i.i",
                 pre := some "while.cond.preheader.i.i599.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre599Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i", pre599Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i600.i.i") "stk_mul_u64.exit605.i.i"
        "while.body.us.i.i601.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre599_find
  · simpa only [stateAt] using pre599_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_one (s := stateAt (pre599Env env a off) s)
      "%tobool.not31.i.i600.i.i" "stk_mul_u64.exit605.i.i" "while.body.us.i.i601.i.i"
      (by simp [pre599Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem pre599_step_store {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i599.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%add4.i.i594.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%add4.i.i594.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i599.i.i.unr-lcssa", (Operand.reg "%shr.i.i596.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i599.i.i.epilog-lcssa", (Operand.reg "%extract.t1094"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre599Env env a off)
        { s with pc := "while.body.us.i.i601.i.i",
                 pre := some "while.cond.preheader.i.i599.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre599Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i599.i.i", pre599Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i600.i.i") "stk_mul_u64.exit605.i.i"
        "while.body.us.i.i601.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre599_find
  · simpa only [stateAt] using pre599_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pre599Env env a off) s)
      "%tobool.not31.i.i600.i.i" "stk_mul_u64.exit605.i.i" "while.body.us.i.i601.i.i"
      (by simp [pre599Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-- The `if.end195`-reaching rung's test. -/
def pre622Specs : List PhiSpec :=
  [{ dst := "%add4.i.i617.i.i.lcssa", ty := Ty.int 128,
     incoming := [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
                  ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))] },
   { dst := "%shr.i.i619.i.i.lcssa.off0", ty := Ty.int 64,
     incoming := [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
                  ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))] }]

def pre622Instrs : List Instr :=
  [Instr.icmp "%tobool.not31.i.i623.i.i" (IPred.ult) 128
     (Operand.reg "%add4.i.i617.i.i.lcssa")
     (Operand.imm (Const.int 128 0x00000000000000010000000000000000#128))]

def pre622Block : List Instr := pre622Specs.map PhiSpec.instr ++ pre622Instrs

theorem pre622_find :
    numFastBody.findBlock "while.cond.preheader.i.i622.i.i" =
      some ⟨"while.cond.preheader.i.i622.i.i", pre622Block,
        Term.condbr (Operand.reg "%tobool.not31.i.i623.i.i") "if.end195.i.i"
          "while.body.us.i.i624.i.i"⟩ := by
  simp only [pre622Block, pre622Instrs, pre622Specs, PhiSpec.instr,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  exact numFast_findBlock_while_cond_preheader_i_i622_i_i

def pre622Env (env : Env) (a : BitVec 128) (off : BitVec 64) : Env :=
  ("%tobool.not31.i.i623.i.i", .int 1 (evalICmp .ult a
    0x00000000000000010000000000000000#128)) ::
  ("%shr.i.i619.i.i.lcssa.off0", .int 64 off) ::
  ("%add4.i.i617.i.i.lcssa", .int 128 a) :: env

theorem pre622_denote {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off)) :
    denoteCode calls pre622Block (stateAt env s) =
      some (stateAt (pre622Env env a off) s) := by
  have hsel : PhiSelects (stateAt env s) pre pre622Specs
      [("%add4.i.i617.i.i.lcssa", .int 128 a),
       ("%shr.i.i619.i.i.lcssa.off0", .int 64 off)] := by
    simp only [pre622Specs]
    constructor
    · exact hop1
    · exact hov1
    constructor
    · exact hop2
    · exact hov2
    exact PhiSelects.nil
  have h := denoteCode_phiRun_at (calls := calls) (env := env) (s := s)
    (p := pre) (specs := pre622Specs)
    (vs := [("%add4.i.i617.i.i.lcssa", .int 128 a),
      ("%shr.i.i619.i.i.lcssa.off0", .int 64 off)])
    (rest := pre622Instrs) hpre hsel (by decide)
  unfold pre622Block
  rw [h]
  simp only [runCells]
  unfold pre622Instrs
  rw [JsonScanLane.denoteCode_icmp_imm_w calls
    (("%shr.i.i619.i.i.lcssa.off0", .int 64 off) ::
      ("%add4.i.i617.i.i.lcssa", .int 128 a) :: env) s
    "%tobool.not31.i.i623.i.i" "%add4.i.i617.i.i.lcssa" .ult
    (by rw [lookupName_cons_ne _ _ (by decide)]; exact lookupName_cons_self ..)]
  simp only [denoteCode_nil, pre622Env, stateAt]

theorem pre622_step_end {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (1 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre622Env env a off)
        { s with pc := "if.end195.i.i",
                 pre := some "while.cond.preheader.i.i622.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre622Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i", pre622Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i623.i.i") "if.end195.i.i"
        "while.body.us.i.i624.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre622_find
  · simpa only [stateAt] using pre622_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_one (s := stateAt (pre622Env env a off) s)
      "%tobool.not31.i.i623.i.i" "if.end195.i.i" "while.body.us.i.i624.i.i"
      (by simp [pre622Env, stateAt]) hbit]
    simp only [stateAt, hpc]

theorem pre622_step_store {calls : Calls} {env : Env} {s : State}
    {pre : String} {op1 op2 : Operand} {a : BitVec 128} {off : BitVec 64}
    (hpc : s.pc = "while.cond.preheader.i.i622.i.i") (hpre : s.pre = some pre)
    (hop1 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%add4.i.i617.i.i.lcssa.ph")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%add4.i.i617.i.i.epil"))] = some op1)
    (hov1 : evalOperand (stateAt env s) op1 = some (.int 128 a))
    (hop2 : phiIncoming pre
      [("while.cond.preheader.i.i622.i.i.unr-lcssa", (Operand.reg "%shr.i.i619.i.i.lcssa.ph.off0")),
       ("while.cond.preheader.i.i622.i.i.epilog-lcssa", (Operand.reg "%extract.t1096"))] = some op2)
    (hov2 : evalOperand (stateAt env s) op2 = some (.int 64 off))
    (hbit : evalICmp .ult a 0x00000000000000010000000000000000#128 = (0 : BitVec 1)) :
    step calls numFastBody (stateAt env s) =
      .jump (stateAt (pre622Env env a off)
        { s with pc := "while.body.us.i.i624.i.i",
                 pre := some "while.cond.preheader.i.i622.i.i" }) := by
  refine numFast_step_at (s' := stateAt (pre622Env env a off) s)
    (b := ⟨"while.cond.preheader.i.i622.i.i", pre622Block,
      Term.condbr (Operand.reg "%tobool.not31.i.i623.i.i") "if.end195.i.i"
        "while.body.us.i.i624.i.i"⟩) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using pre622_find
  · simpa only [stateAt] using pre622_denote hpre hop1 hov1 hop2 hov2
  · rw [numFast_execTerm_condbr_zero (s := stateAt (pre622Env env a off) s)
      "%tobool.not31.i.i623.i.i" "if.end195.i.i" "while.body.us.i.i624.i.i"
      (by simp [pre622Env, stateAt]) hbit]
    simp only [stateAt, hpc]

/-! ### Axiom footprints -/

#print axioms NumFastToDouble.denoteCode_store32
#print axioms NumFastToDouble.end176_find
#print axioms NumFastToDouble.end176_denote
#print axioms NumFastToDouble.end176_step_end
#print axioms NumFastToDouble.end176_step_then
#print axioms NumFastToDouble.end176_store_read
#print axioms NumFastToDouble.end176_residual_empty
#print axioms NumFastToDouble.end176_run_ladder
#print axioms NumFastToDouble.then59_find
#print axioms NumFastToDouble.then59_step
#print axioms NumFastToDouble.then59_entry
#print axioms NumFastToDouble.then59_run_incPeel
#print axioms NumFastToDouble.then59_run_thread
#print axioms NumFastToDouble.then59_run_incThread
#print axioms NumFastToDouble.then59_run_parseEnd
#print axioms NumFastToDouble.then59_run_endThread
#print axioms NumFastToDouble.pre87_find
#print axioms NumFastToDouble.pre87_denote
#print axioms NumFastToDouble.pre87_step_lcssa
#print axioms NumFastToDouble.pre87_step_new
#print axioms NumFastToDouble.pre87_epil_entry
#print axioms NumFastToDouble.pre87new_find
#print axioms NumFastToDouble.pre87new_denote
#print axioms NumFastToDouble.pre87new_step
#print axioms NumFastToDouble.pre87_copy_entry
#print axioms NumFastToDouble.pre87_run_copy
#print axioms NumFastToDouble.end83Env_i2
#print axioms NumFastToDouble.end83Env_n
#print axioms NumFastToDouble.end83Env_p
#print axioms NumFastToDouble.step_sext
#print axioms NumFastToDouble.denoteCode_sext
#print axioms NumFastToDouble.denoteCode_store32_imm
#print axioms NumFastToDouble.denoteCode_store64_imm
#print axioms NumFastToDouble.step_gep8_global_reg
#print axioms NumFastToDouble.denoteCode_gep8_global_reg
#print axioms NumFastToDouble.cleanup_find
#print axioms NumFastToDouble.cleanup_denote
#print axioms NumFastToDouble.cleanup_step_end
#print axioms NumFastToDouble.cleanup_step_residue
#print axioms NumFastToDouble.then148_find
#print axioms NumFastToDouble.then148_denote
#print axioms NumFastToDouble.then148_step_nest
#print axioms NumFastToDouble.then148_step_carry
#print axioms NumFastToDouble.sinkSplit_find
#print axioms NumFastToDouble.sinkSplit_denote
#print axioms NumFastToDouble.sinkSplit_step
#print axioms NumFastToDouble.end151_find
#print axioms NumFastToDouble.end151_denote
#print axioms NumFastToDouble.end151_step_else
#print axioms NumFastToDouble.end151_step_then
#print axioms NumFastToDouble.then153_find
#print axioms NumFastToDouble.then153_denote
#print axioms NumFastToDouble.then153_step_peel
#print axioms NumFastToDouble.then153_step_thread
#print axioms NumFastToDouble.else164_find
#print axioms NumFastToDouble.else164_denote
#print axioms NumFastToDouble.else164_step_negative
#print axioms NumFastToDouble.else164_step_positive
#print axioms NumFastToDouble.then167_find
#print axioms NumFastToDouble.then167_denote
#print axioms NumFastToDouble.then167_step_body
#print axioms NumFastToDouble.then167_step_thread
#print axioms NumFastToDouble.end176Thread_find
#print axioms NumFastToDouble.end176Thread_denote
#print axioms NumFastToDouble.end176Thread_step
#print axioms NumFastToDouble.body173_find
#print axioms NumFastToDouble.body173_denote
#print axioms NumFastToDouble.body173_step_nest
#print axioms NumFastToDouble.body173_step_exit
#print axioms NumFastToDouble.cond184_find
#print axioms NumFastToDouble.cond184_denote
#print axioms NumFastToDouble.cond184_step_body
#print axioms NumFastToDouble.cond184_step_end
#print axioms NumFastToDouble.body187_find
#print axioms NumFastToDouble.body187_denote
#print axioms NumFastToDouble.body187_step_nest
#print axioms NumFastToDouble.body187_step_exit
#print axioms NumFastToDouble.exit605_find
#print axioms NumFastToDouble.exit605_denote
#print axioms NumFastToDouble.exit605_step_body
#print axioms NumFastToDouble.exit605_step_end
#print axioms NumFastToDouble.end190_find
#print axioms NumFastToDouble.end190_denote
#print axioms NumFastToDouble.end190_step_rung
#print axioms NumFastToDouble.end190_step_end
#print axioms NumFastToDouble.end195_find
#print axioms NumFastToDouble.end195_denote
#print axioms NumFastToDouble.end195_step
#print axioms NumFastToDouble.denoteCode_trunc_one
#print axioms NumFastToDouble.denoteCode_and_one
#print axioms NumFastToDouble.loopexit555_find
#print axioms NumFastToDouble.loopexit555_denote
#print axioms NumFastToDouble.loopexit555_step
#print axioms NumFastToDouble.epilog555_find
#print axioms NumFastToDouble.epilog555_denote
#print axioms NumFastToDouble.epilog555_step
#print axioms NumFastToDouble.loopexit577_find
#print axioms NumFastToDouble.loopexit577_denote
#print axioms NumFastToDouble.loopexit577_step
#print axioms NumFastToDouble.loopexit599_find
#print axioms NumFastToDouble.loopexit599_denote
#print axioms NumFastToDouble.loopexit599_step
#print axioms NumFastToDouble.epilog599_find
#print axioms NumFastToDouble.epilog599_denote
#print axioms NumFastToDouble.epilog599_step
#print axioms NumFastToDouble.loopexit622_find
#print axioms NumFastToDouble.loopexit622_denote
#print axioms NumFastToDouble.loopexit622_step
#print axioms NumFastToDouble.epilog622_find
#print axioms NumFastToDouble.epilog622_denote
#print axioms NumFastToDouble.epilog622_step
#print axioms NumFastToDouble.new525_find
#print axioms NumFastToDouble.new525_denote
#print axioms NumFastToDouble.new525_step
#print axioms NumFastToDouble.new542_find
#print axioms NumFastToDouble.new542_denote
#print axioms NumFastToDouble.new542_step
#print axioms NumFastToDouble.new564_find
#print axioms NumFastToDouble.new564_denote
#print axioms NumFastToDouble.new564_step
#print axioms NumFastToDouble.new586_find
#print axioms NumFastToDouble.new586_denote
#print axioms NumFastToDouble.new586_step
#print axioms NumFastToDouble.new608_find
#print axioms NumFastToDouble.new608_denote
#print axioms NumFastToDouble.new608_step
#print axioms NumFastToDouble.unr517_find
#print axioms NumFastToDouble.unr517_denote
#print axioms NumFastToDouble.unr517_step_join
#print axioms NumFastToDouble.unr517_step_peel
#print axioms NumFastToDouble.pre555_find
#print axioms NumFastToDouble.pre555_denote
#print axioms NumFastToDouble.pre555_step_ladder
#print axioms NumFastToDouble.pre555_step_store
#print axioms NumFastToDouble.pre599_find
#print axioms NumFastToDouble.pre599_denote
#print axioms NumFastToDouble.pre599_step_exit
#print axioms NumFastToDouble.pre599_step_store
#print axioms NumFastToDouble.pre622_find
#print axioms NumFastToDouble.pre622_denote
#print axioms NumFastToDouble.pre622_step_end
#print axioms NumFastToDouble.pre622_step_store
#print axioms NumFastToDouble.pre517_find
#print axioms NumFastToDouble.pre517_denote
#print axioms NumFastToDouble.pre517_step_ladder
#print axioms NumFastToDouble.pre517_step_store
#print axioms NumFastToDouble.lrph564_find
#print axioms NumFastToDouble.lrph564_denote
#print axioms NumFastToDouble.lrph564_step_join
#print axioms NumFastToDouble.lrph564_step_unroll
#print axioms NumFastToDouble.lrph586_find
#print axioms NumFastToDouble.lrph586_denote
#print axioms NumFastToDouble.lrph586_step_join
#print axioms NumFastToDouble.lrph586_step_unroll
#print axioms NumFastToDouble.bus557_find
#print axioms NumFastToDouble.bus557_denote
#print axioms NumFastToDouble.bus557_step
#print axioms NumFastToDouble.bus601_find
#print axioms NumFastToDouble.bus601_denote
#print axioms NumFastToDouble.bus601_step
#print axioms NumFastToDouble.unr555_find
#print axioms NumFastToDouble.unr555_denote
#print axioms NumFastToDouble.unr555_step_join
#print axioms NumFastToDouble.unr555_step_peel
#print axioms NumFastToDouble.unr577_find
#print axioms NumFastToDouble.unr577_denote
#print axioms NumFastToDouble.unr577_step_join
#print axioms NumFastToDouble.unr577_step_peel
#print axioms NumFastToDouble.unr599_find
#print axioms NumFastToDouble.unr599_denote
#print axioms NumFastToDouble.unr599_step_join
#print axioms NumFastToDouble.unr599_step_peel
#print axioms NumFastToDouble.unr622_find
#print axioms NumFastToDouble.unr622_denote
#print axioms NumFastToDouble.unr622_step_join
#print axioms NumFastToDouble.unr622_step_peel
#print axioms NumFastToDouble.bus624_find
#print axioms NumFastToDouble.bus624_denote
#print axioms NumFastToDouble.bus624_step
#print axioms NumFastToDouble.lrph608_find
#print axioms NumFastToDouble.lrph608_denote
#print axioms NumFastToDouble.lrph608_step_join
#print axioms NumFastToDouble.lrph608_step_unroll

end NumFastToDouble

end LeanLLVM.Refinement
