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
  both of the switch's outcomes.

The blocks the copy's own statements already cover (`for.body87.i.i`'s nest,
its residual loop and the handoff) are composed from
`JsonStage2NumFastTier3CopyUnroll`/`JsonStage2NumFastTier3Handoff`, not
restated here.

The big multiply (`for.body132.i.i`'s chunk loop, the `10 ^ 19` nest and the
`stk_mul_u64` sites) and the epilogue's blocks (`for.cond255.i.i` and
`for.end359.i.i`) are not stated here yet, and the parse's loop traversals are
the steps above composed by their caller rather than an induction here.  There
is no `sorry`, `admit` or `native_decide` below.
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

end NumFastToDouble

end LeanLLVM.Refinement
