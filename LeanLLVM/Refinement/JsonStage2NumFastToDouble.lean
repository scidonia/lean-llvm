/-
The `to_double` interior's block steps and the epilogue's.

`JsonStage2NumFastFallback` states the fallback's seam with two boundaries as
hypotheses: `FbCopyEntryPos`/`FbCopyEntryNeg` (the copy's entry through the
`T`/`F` parse, the lead clamps and the big multiply to the ladder's head) and
`FbEpilogue` (the rounding loop and the sign select to `if.end291`).  This
module supplies the per-edge steps those boundaries are built from, each at its
own `findBlock` pin and each with the environment its chain leaves:

* the `T`/`F` parse's blocks — `for.body.outer.i.i`, the peel's
  `if.then13.i.peel.i`/`for.inc.thread.i.peel.i`, `for.body.i.i`,
  `if.then13.i.i`, `if.end28.i.i`, `if.then31.i.i`, `if.then36.i.i`,
  `if.else46.i.i`, `for.inc.i.i`, `for.end.i.i`, and the exponent's entry
  `if.then64.i.i` through `if.end83.i.i`;
* the copy's exit and the lead clamps — `for.end100.i.i`, `if.end104.i.i`,
  `if.then113.i.i`, `if.end120.i.i`, `if.then123.i.i`, `if.end126.i.i`;
* the big multiply — the chunk loop's `for.body132.i.i`, the `10 ^ 19` nest's
  `for.body.i.i.i`, and the `stk_mul_u64` site's `stk_mul_u64.exit.i.i` and
  `while.end.i.i`, the call answered by the caller's selection;
* the epilogue — `for.cond255.i.i`'s rounding loop and `for.end359.i.i`'s sign
  select.

The blocks the copy's own statements already cover (`for.body87.i.i`'s nest,
its residual loop and the handoff) are composed from
`JsonStage2NumFastTier3CopyUnroll`/`JsonStage2NumFastTier3Handoff`, not
restated here.  There is no `sorry`, `admit` or `native_decide` below.
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

/-- The block's first-instruction shapes: `block_step`'s own steps, plus the
byte load and store and the two generic forms (`icmp` at any predicate, `mul`
by an immediate). -/
macro "inner_step" : tactic => `(tactic|
  (first
   | block_step
   | rw [denoteCode_load8 _ _ _ _ _ ?_ ?_ _]
   | rw [denoteCode_store8 _ _ _ _ _ ?_ ?_ _]
   | rw [JsonScanLane.denoteCode_icmp_imm_w _ _ _ _ _ _ ?_ _]
   | rw [NumFastTier3.denoteCode_mul_imm_w _ _ _ _ _ _ ?_ _]
   | rw [denoteCode_add_imm_w _ _ _ _ _ _ ?_ _]))

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

end NumFastToDouble

end LeanLLVM.Refinement
