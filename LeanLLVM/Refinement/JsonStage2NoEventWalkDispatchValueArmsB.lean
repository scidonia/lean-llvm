/-
The no-event walk's value arms: the number and literal paths below `if.end457`,
their count stores at `if.end545`, and the separator skip to `after_value`.

`JsonStage2NoEventWalkValue` leaves the walk at `if.then471` or `if.else495`,
with `%ee.1` the scalar token's end, `%idxprom.lcssa` its start and `%cond` the
next entry's position (or the document's length).  This module runs what follows:

* the **number arm**: `if.then471` stages `%d` and `%ei`, calls `num_fast_el1`
  on the token `[lane, q)`, and on the accepted answer `cleanup491` reloads the
  conversion word and adds the `7`-byte number tag's fixed part;
* the **literal arm**: `if.else495`'s dispatch selects one of `true`/`false`/
  `null` and `if.end519`'s pinned compare chain checks the token against the
  packed literal; the accepted answer lands at `if.end545` with the literal's tag
  as its count contribution;
* `if.end545`'s `%add489.pn` selection, its `tokens + 1` and `terms + pn` stores,
  and its extent test;
* the **separator loop** (`land.rhs552` → `NodeBlock83` → `NodeBlock81` → the
  three leaves → `while.body557`): the whitespace run from the token's end to
  `%cond`, which on a fully whitespace run advances the cursor to `%cond` and
  enters `after_value`.

The number payload is the model's: `stage2NumFast`'s accepted answer writes
`strtodSpec`'s bits into `%d`, and the arm reads that word back.  The helper
body's faithfulness (`num_fast_el1`/`od_scalar_value`) is not claimed here.

Each block is one generic step: its denotation binds exactly the cells it writes
over an abstract incoming environment, parameterised by the incoming values, and
the loop is an induction on the distance from the token's end to `%cond`.  No
environment suffix is carried: a block's step reads what it needs through
`lookupName` and the cells it adds are the only ones any later step reads back.
-/
import LeanLLVM.Refinement.JsonStage2NoEventWalkValue
import LeanLLVM.Refinement.JsonStage2NoEventLiteral
import LeanLLVM.Refinement.JsonStage2Hsem
import LeanLLVM.Refinement.JsonStage2NoEventWalkCycleA
import LeanLLVM.Refinement.JsonStage2NoEventWalkContainers

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonStage2NoEventIR
open LeanLLVM.Refinement.BlockEval

/-! ### Instruction steps the arms need

`BlockEval` has the two-argument lifetime marker through `WalkTerminal`, and
`WalkScalar` the eight-bit load.  The three shapes below are the arms' own: a
store of an immediate, the four-argument call that binds its result, and the
`num_fast_el1` selection.
-/

/-- `store i64 <imm>, ptr %p`. -/
theorem valueArms_step_store64_imm (calls : Calls) (env : Env) (s : State)
    (p : String) {x : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s)
        (.store (.int 64) (.imm (.int 64 x)) (.reg p)) =
      some (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x.toNat 8)) s.next)) := by
  rw [JsonS1MasksIR.evalInstr_store (vv := .int 64 x) (a := a)
    (s' := stateAt env
      (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x.toNat 8)) s.next))
    (hv := by simp only [stateAt, evalOperand, Const.toValue])
    (hp := by simp only [stateAt, evalOperand, hp])]
  simp [storeValue, stateAt, State.bind, stage2NoEventStepState, natToBytes_length]

/-- `store i64 <imm>, ptr %p`, as a chain step. -/
theorem valueArms_denote_store64_imm (calls : Calls) (env : Env) (s : State)
    (p : String) {x : BitVec 64} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) (is : List Instr) :
    denoteCode calls (.store (.int 64) (.imm (.int 64 x)) (.reg p) :: is)
        (stateAt env s) =
      denoteCode calls is (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem a (natToBytes x.toNat 8)) s.next)) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (valueArms_step_store64_imm calls env s p hp)]

/-- A four-argument call that binds its `i32` result. -/
theorem valueArms_step_call4 (calls : Calls) (env : Env) (s : State)
    (d callee p n o e : String) {pa : Nat} {nv : BitVec 64} {oa ea : Nat}
    {r : CallOutcome}
    (hp : lookupName env p = some (.ptr pa))
    (hn : lookupName env n = some (.int 64 nv))
    (ho : lookupName env o = some (.ptr oa))
    (he : lookupName env e = some (.ptr ea))
    (hc : calls callee [.ptr pa, .int 64 nv, .ptr oa, .ptr ea] s.mem s.next = some r) :
    evalInstr calls (stateAt env s)
        (.call d (.int 32) callee
          [(Ty.ptr, .reg p), (Ty.int 64, .reg n), (Ty.ptr, .reg o), (Ty.ptr, .reg e)]) =
      some (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  have ha' : evalOperands (stateAt env s)
      [(Ty.ptr, .reg p), (Ty.int 64, .reg n), (Ty.ptr, .reg o), (Ty.ptr, .reg e)] =
      some [.ptr pa, .int 64 nv, .ptr oa, .ptr ea] := by
    simp [evalOperands, evalOperand, stateAt, hp, hn, ho, he]
  simpa only [stateAt] using
    (JsonS1MasksIR.evalInstr_call (calls := calls) (s := stateAt env s) (d := d) (ty := Ty.int 32)
      (callee := callee) (args :=
        [(Ty.ptr, .reg p), (Ty.int 64, .reg n), (Ty.ptr, .reg o), (Ty.ptr, .reg e)])
      (vs := [.ptr pa, .int 64 nv, .ptr oa, .ptr ea]) (r := r) ha' hc)

/-- The four-argument call, as a chain step. -/
theorem valueArms_denote_call4 (calls : Calls) (env : Env) (s : State)
    (d callee p n o e : String) {pa : Nat} {nv : BitVec 64} {oa ea : Nat}
    {r : CallOutcome}
    (hp : lookupName env p = some (.ptr pa))
    (hn : lookupName env n = some (.int 64 nv))
    (ho : lookupName env o = some (.ptr oa))
    (he : lookupName env e = some (.ptr ea))
    (hc : calls callee [.ptr pa, .int 64 nv, .ptr oa, .ptr ea] s.mem s.next = some r)
    (is : List Instr) :
    denoteCode calls
        (.call d (.int 32) callee
          [(Ty.ptr, .reg p), (Ty.int 64, .reg n), (Ty.ptr, .reg o), (Ty.ptr, .reg e)]
          :: is) (stateAt env s) =
      denoteCode calls is (stateAt ((d, r.ret) :: env)
        { s with mem := r.mem, next := r.next }) := by
  rw [denoteCode_cons_of _ _ _ _ _
    (valueArms_step_call4 calls env s d callee p n o e hp hn ho he hc)]

/-- **The walk's selection answers `num_fast_el1` at the model.** -/
theorem valueArms_num_fast_calls {gap : Calls} (args : List Value) (mem : Mem)
    (next : Nat) :
    stage2NoEventCalls gap "num_fast_el1" args mem next = stage2NumFast args mem next := by
  have hne : "num_fast_el1" ≠ "od_gap_recover" := by decide
  unfold stage2NoEventCalls
  rw [ite_eq_right hne]
  exact stage2Calls_num_fast_el1 args mem next

/-- Reducing a value modulo `256 ^ n` before encoding its low `n` bytes. -/
theorem valueArms_natToBytes_mod (v n : Nat) :
    natToBytes (v % 256 ^ n) n = natToBytes v n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
      simp only [natToBytes]
      rw [Nat.pow_succ]
      congr 1
      · rw [Nat.mul_comm (256 ^ n) 256, Nat.mod_mul_right_mod]
      · rw [Nat.mul_comm (256 ^ n) 256, Nat.mod_mul_right_div_self]
        exact ih (v / 256)

/-- **The word an eight-byte read names is the `natToBytes` of its own word.** -/
theorem valueArms_wordBytes_natToBytes (bits : Nat) :
    natToBytes (BitVec.ofNat 64 bits).toNat 8 = wordBytes 8 bits := by
  rw [wordBytes, BitVec.toNat_ofNat]
  exact valueArms_natToBytes_mod bits 8

/-- **`ofNat 64` subtraction is natural subtraction** at an ordered pair. -/
theorem valueArms_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]
  have h : 2 ^ 64 - b + a = (a - b) + 2 ^ 64 := by omega
  rw [h, Nat.add_mod, Nat.mod_self, Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64),
    Nat.add_zero, Nat.mod_eq_of_lt (by omega : a - b < 2 ^ 64)]

/-! ### The blocks, pinned -/

def valueArmsIfThen471Instrs : List Instr :=
[
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d"))],
  Instr.callVoid "llvm.lifetime.start.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei"))],
  Instr.store (Ty.int 64) (Operand.imm (.int 64 (BitVec.ofNat 64 0))) (Operand.reg "%ei"),
  Instr.binop "%sub475" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
  Instr.call "%call476" (Ty.int 32) "num_fast_el1" [(Ty.ptr, (Operand.reg "%arrayidx6.le1046")), ((Ty.int 64), (Operand.reg "%sub475")), (Ty.ptr, (Operand.reg "%d")), (Ty.ptr, (Operand.reg "%ei"))],
  Instr.icmp "%tobool477.not.not" IPred.eq 32 (Operand.reg "%call476") (Operand.imm (.int 32 (BitVec.ofNat 32 0)))
]

theorem valueArms_find_if_then471 :
    stage2NoEventBody.findBlock "if.then471" =
      some ⟨"if.then471", valueArmsIfThen471Instrs,
        Term.condbr (Operand.reg "%tobool477.not.not") "cleanup491.thread" "cleanup491"⟩ := by
  decide

def valueArmsCleanup491Instrs : List Instr :=
[
  Instr.load "%62" (Ty.int 64) (Operand.reg "%d"),
  Instr.binop "%add489" BinOp.add 64 (Operand.reg "%62") (Operand.imm (.int 64 (BitVec.ofNat 64 7))),
  Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%ei"))],
  Instr.callVoid "llvm.lifetime.end.p0" [((Ty.int 64), (Operand.imm (.int 64 (BitVec.ofNat 64 8)))), (Ty.ptr, (Operand.reg "%d"))]
]

theorem valueArms_find_cleanup491 :
    stage2NoEventBody.findBlock "cleanup491" =
      some ⟨"cleanup491", valueArmsCleanup491Instrs, Term.br "if.end545"⟩ := by
  decide

def valueArmsIfEnd545Instrs : List Instr :=
[
  Instr.phi "%add489.pn" (Ty.int 64) [("cleanup491", (Operand.reg "%add489")), ("for.end.i", (Operand.reg "%tag.0"))],
  Instr.binop "%tokens.12" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1073") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
  Instr.binop "%terms.12" BinOp.add 64 (Operand.reg "%add489.pn") (Operand.reg "%terms.0.lcssa1079"),
  Instr.icmp "%cmp546" IPred.ult 64 (Operand.reg "%ee.1") (Operand.reg "%cond")
]

theorem valueArms_find_if_end545 :
    stage2NoEventBody.findBlock "if.end545" =
      some ⟨"if.end545", valueArmsIfEnd545Instrs,
        Term.condbr (Operand.reg "%cmp546") "land.rhs552" "after_value"⟩ := by
  decide

def valueArmsIfElse495Instrs : List Instr := []

theorem valueArms_find_if_else495 :
    stage2NoEventBody.findBlock "if.else495" =
      some ⟨"if.else495", valueArmsIfElse495Instrs, Term.br "NodeBlock72"⟩ := by
  decide

def valueArmsNodeBlock72Instrs : List Instr :=
[
  Instr.icmp "%Pivot73" IPred.slt 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
]

theorem valueArms_find_nodeBlock72 :
    stage2NoEventBody.findBlock "NodeBlock72" =
      some ⟨"NodeBlock72", valueArmsNodeBlock72Instrs,
        Term.condbr (Operand.reg "%Pivot73") "LeafBlock64" "NodeBlock70"⟩ := by
  decide

def valueArmsNodeBlock70Instrs : List Instr :=
[
  Instr.icmp "%Pivot71" IPred.slt 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
]

theorem valueArms_find_nodeBlock70 :
    stage2NoEventBody.findBlock "NodeBlock70" =
      some ⟨"NodeBlock70", valueArmsNodeBlock70Instrs,
        Term.condbr (Operand.reg "%Pivot71") "LeafBlock66" "LeafBlock68"⟩ := by
  decide

def valueArmsLeafBlock68Instrs : List Instr :=
[
  Instr.icmp "%SwitchLeaf69" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 116)))
]

theorem valueArms_find_leafBlock68 :
    stage2NoEventBody.findBlock "LeafBlock68" =
      some ⟨"LeafBlock68", valueArmsLeafBlock68Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf69") "if.end519" "if.else510"⟩ := by
  decide

def valueArmsLeafBlock66Instrs : List Instr :=
[
  Instr.icmp "%SwitchLeaf67" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 110)))
]

theorem valueArms_find_leafBlock66 :
    stage2NoEventBody.findBlock "LeafBlock66" =
      some ⟨"LeafBlock66", valueArmsLeafBlock66Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf67") "if.then509" "if.else510"⟩ := by
  decide

def valueArmsLeafBlock64Instrs : List Instr :=
[
  Instr.icmp "%SwitchLeaf65" IPred.eq 8 (Operand.reg "%.lcssa") (Operand.imm (.int 8 (BitVec.ofNat 8 102)))
]

theorem valueArms_find_leafBlock64 :
    stage2NoEventBody.findBlock "LeafBlock64" =
      some ⟨"LeafBlock64", valueArmsLeafBlock64Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf65") "if.then504" "if.else510"⟩ := by
  decide

def valueArmsIfThen504Instrs : List Instr := []

theorem valueArms_find_if_then504 :
    stage2NoEventBody.findBlock "if.then504" =
      some ⟨"if.then504", valueArmsIfThen504Instrs, Term.br "if.end519"⟩ := by
  decide

def valueArmsIfThen509Instrs : List Instr := []

theorem valueArms_find_if_then509 :
    stage2NoEventBody.findBlock "if.then509" =
      some ⟨"if.then509", valueArmsIfThen509Instrs, Term.br "if.end519"⟩ := by
  decide

def valueArmsLandRhs552Instrs : List Instr :=
[
  Instr.phi "%q.01062" (Ty.int 64) [("while.body557", (Operand.reg "%inc558")), ("if.end545", (Operand.reg "%ee.1"))],
  Instr.gep "%arrayidx553" (Ty.int 8) (Operand.reg "%b") (Operand.reg "%q.01062"),
  Instr.load "%75" (Ty.int 8) (Operand.reg "%arrayidx553")
]

theorem valueArms_find_land_rhs552 :
    stage2NoEventBody.findBlock "land.rhs552" =
      some ⟨"land.rhs552", valueArmsLandRhs552Instrs, Term.br "NodeBlock83"⟩ := by
  decide

def valueArmsNodeBlock83Instrs : List Instr :=
[
  Instr.icmp "%Pivot84" IPred.slt 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
]

theorem valueArms_find_nodeBlock83 :
    stage2NoEventBody.findBlock "NodeBlock83" =
      some ⟨"NodeBlock83", valueArmsNodeBlock83Instrs,
        Term.condbr (Operand.reg "%Pivot84") "LeafBlock74" "NodeBlock81"⟩ := by
  decide

def valueArmsNodeBlock81Instrs : List Instr :=
[
  Instr.icmp "%Pivot82" IPred.slt 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
]

theorem valueArms_find_nodeBlock81 :
    stage2NoEventBody.findBlock "NodeBlock81" =
      some ⟨"NodeBlock81", valueArmsNodeBlock81Instrs,
        Term.condbr (Operand.reg "%Pivot82") "LeafBlock77" "LeafBlock79"⟩ := by
  decide

def valueArmsLeafBlock79Instrs : List Instr :=
[
  Instr.icmp "%SwitchLeaf80" IPred.eq 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 32)))
]

theorem valueArms_find_leafBlock79 :
    stage2NoEventBody.findBlock "LeafBlock79" =
      some ⟨"LeafBlock79", valueArmsLeafBlock79Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf80") "while.body557" "if.then562"⟩ := by
  decide

def valueArmsLeafBlock77Instrs : List Instr :=
[
  Instr.icmp "%SwitchLeaf78" IPred.eq 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 13)))
]

theorem valueArms_find_leafBlock77 :
    stage2NoEventBody.findBlock "LeafBlock77" =
      some ⟨"LeafBlock77", valueArmsLeafBlock77Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf78") "while.body557" "if.then562"⟩ := by
  decide

def valueArmsLeafBlock74Instrs : List Instr :=
[
  Instr.binop "%.off75" BinOp.add 8 (Operand.reg "%75") (Operand.imm (.int 8 (BitVec.ofNat 8 247))),
  Instr.icmp "%SwitchLeaf76" IPred.ule 8 (Operand.reg "%.off75") (Operand.imm (.int 8 (BitVec.ofNat 8 1)))
]

theorem valueArms_find_leafBlock74 :
    stage2NoEventBody.findBlock "LeafBlock74" =
      some ⟨"LeafBlock74", valueArmsLeafBlock74Instrs,
        Term.condbr (Operand.reg "%SwitchLeaf76") "while.body557" "if.then562"⟩ := by
  decide

def valueArmsWhileBody557Instrs : List Instr :=
[
  Instr.binop "%inc558" BinOp.add 64 (Operand.reg "%q.01062") (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
  Instr.icmp "%exitcond1171.not" IPred.eq 64 (Operand.reg "%inc558") (Operand.reg "%cond")
]

theorem valueArms_find_while_body557 :
    stage2NoEventBody.findBlock "while.body557" =
      some ⟨"while.body557", valueArmsWhileBody557Instrs,
        Term.condbr (Operand.reg "%exitcond1171.not") "after_value" "land.rhs552"⟩ := by
  decide

/-! ### Generic control steps at the pinned blocks -/

/-- One control step from a block whose instruction list denotes to `s'` and
whose terminator `execTerm` gives `c`. -/
theorem valueArms_step_at_block {calls : Calls} {f : Function}
    {s s' : State} {b : Block} {c : Ctrl} (hfind : f.findBlock s.pc = some b)
    (hcode : denoteCode calls b.instrs s = some s')
    (hterm : execTerm s' b.term = c) : step calls f s = c := by
  simp only [step, hfind, hcode, hterm]

/-- An empty block with an unconditional branch. -/
theorem valueArms_step_br (calls : Calls) (env : Env) (s : State)
    {name dest : String} {b : Block}
    (hpc : s.pc = name) (hfind : stage2NoEventBody.findBlock name = some b)
    (hinstrs : b.instrs = []) (hterm : b.term = Term.br dest) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt env { s with pc := dest, pre := some name }) := by
  refine valueArms_step_at_block (s := stateAt env s) (s' := stateAt env s)
    (b := b) (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hfind
  · rw [hinstrs]; rfl
  · rw [hterm]
    simp only [execTerm, stateAt, hpc]

/-- A single `icmp` against an immediate, with its conditional branch. -/
theorem valueArms_step_icmp_imm (calls : Calls) (env : Env) (s : State)
    {name d a t f : String} {pr : IPred} {w : Nat} {x c : BitVec w} {b : Block}
    (hpc : s.pc = name) (hfind : stage2NoEventBody.findBlock name = some b)
    (hinstrs : b.instrs = [Instr.icmp d pr w (.reg a) (.imm (.int w c))])
    (hterm : b.term = Term.condbr (.reg d) t f)
    (ha : lookupName env a = some (.int w x)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt ((d, .int 1 (evalICmp pr x c)) :: env)
        { s with pc := if evalICmp pr x c = 1 then t else f, pre := some name }) := by
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt ((d, .int 1 (evalICmp pr x c)) :: env) s) (b := b) (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using hfind
  · rw [hinstrs]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := calls) (env := env) (s := s)
      (d := d) (a := a) (p := pr) (w := w) (x := x) (c := c) ha (is := [])]
    rfl
  · rw [hterm]
    exact stage2NoEventLitChain_execTerm_condbr (stateAt ((d, .int 1 (evalICmp pr x c)) :: env) s)
      d t f name (by simp only [stateAt, hpc])
      (evalOperand_reg_of ((d, .int 1 (evalICmp pr x c)) :: env) s d
        (.int 1 (evalICmp pr x c)) (by simp only [lookupName_cons_self]))

/-! ### The dispatch below `if.else495` -/

theorem valueArms_step_if_else495 (calls : Calls) (env : Env) (s : State)
    (hpc : s.pc = "if.else495") :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt env { s with pc := "NodeBlock72", pre := some "if.else495" }) :=
  valueArms_step_br calls env s hpc valueArms_find_if_else495 rfl rfl

theorem valueArms_step_nodeBlock72 (calls : Calls) (env : Env) (s : State)
    {lc : BitVec 8} (hpc : s.pc = "NodeBlock72")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot73", .int 1 (evalICmp .slt lc (BitVec.ofNat 8 110))) :: env)
        { s with pc := if evalICmp .slt lc (BitVec.ofNat 8 110) = 1
                        then "LeafBlock64" else "NodeBlock70",
                 pre := some "NodeBlock72" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_nodeBlock72 rfl rfl hlc

theorem valueArms_step_nodeBlock70 (calls : Calls) (env : Env) (s : State)
    {lc : BitVec 8} (hpc : s.pc = "NodeBlock70")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot71", .int 1 (evalICmp .slt lc (BitVec.ofNat 8 116))) :: env)
        { s with pc := if evalICmp .slt lc (BitVec.ofNat 8 116) = 1
                        then "LeafBlock66" else "LeafBlock68",
                 pre := some "NodeBlock70" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_nodeBlock70 rfl rfl hlc

theorem valueArms_step_leafBlock68 (calls : Calls) (env : Env) (s : State)
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock68")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf69", .int 1 (evalICmp .eq lc (BitVec.ofNat 8 116))) :: env)
        { s with pc := if evalICmp .eq lc (BitVec.ofNat 8 116) = 1
                        then "if.end519" else "if.else510",
                 pre := some "LeafBlock68" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_leafBlock68 rfl rfl hlc

theorem valueArms_step_leafBlock66 (calls : Calls) (env : Env) (s : State)
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock66")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf67", .int 1 (evalICmp .eq lc (BitVec.ofNat 8 110))) :: env)
        { s with pc := if evalICmp .eq lc (BitVec.ofNat 8 110) = 1
                        then "if.then509" else "if.else510",
                 pre := some "LeafBlock66" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_leafBlock66 rfl rfl hlc

theorem valueArms_step_leafBlock64 (calls : Calls) (env : Env) (s : State)
    {lc : BitVec 8} (hpc : s.pc = "LeafBlock64")
    (hlc : lookupName env "%.lcssa" = some (.int 8 lc)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf65", .int 1 (evalICmp .eq lc (BitVec.ofNat 8 102))) :: env)
        { s with pc := if evalICmp .eq lc (BitVec.ofNat 8 102) = 1
                        then "if.then504" else "if.else510",
                 pre := some "LeafBlock64" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_leafBlock64 rfl rfl hlc

theorem valueArms_step_if_then504 (calls : Calls) (env : Env) (s : State)
    (hpc : s.pc = "if.then504") :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt env { s with pc := "if.end519", pre := some "if.then504" }) :=
  valueArms_step_br calls env s hpc valueArms_find_if_then504 rfl rfl

theorem valueArms_step_if_then509 (calls : Calls) (env : Env) (s : State)
    (hpc : s.pc = "if.then509") :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt env { s with pc := "if.end519", pre := some "if.then509" }) :=
  valueArms_step_br calls env s hpc valueArms_find_if_then509 rfl rfl


/-! ### The number arm's blocks -/

/-- The `num_fast_el1` `phi` selection's predecessors. -/
def valueArmsIfEnd545Incoming : List (String × Operand) :=
  [("cleanup491", (Operand.reg "%add489")), ("for.end.i", (Operand.reg "%tag.0"))]

/-- `if.then471`'s cells: the staged call's result, its token length and the
branch test. -/
abbrev valueArmsIfThen471Cells (env : Env) (nv : BitVec 64) (r : CallOutcome) : Env :=
  ("%tobool477.not.not", .int 1 0) ::
    ("%call476", r.ret) :: ("%sub475", .int 64 nv) :: env

/-- `icmp eq` is zero off the diagonal. -/
theorem valueArms_icmp_eq_zero {w : Nat} {x c : BitVec w} (h : x ≠ c) :
    evalICmp .eq x c = 0 := by
  simp [evalICmp, h]

/-- **`icmp ult` is zero on the diagonal.** -/
theorem valueArms_ult_self {w : Nat} (x : BitVec w) : evalICmp .ult x x = 0 := by
  simp [evalICmp, BitVec.ult]

/-- **`icmp slt` is zero on the diagonal.** -/
theorem valueArms_slt_self {w : Nat} (x : BitVec w) : evalICmp .slt x x = 0 := by
  simp [evalICmp, BitVec.slt]

theorem valueArms_step_if_then471 {gap : Calls} {env : Env} {s : State}
    {dd eiAddr pa : Nat} {ee idx nv : BitVec 64} {r : CallOutcome}
    (hpc : s.pc = "if.then471")
    (hd : lookupName env "%d" = some (.ptr dd))
    (hei : lookupName env "%ei" = some (.ptr eiAddr))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName env "%idxprom.lcssa" = some (.int 64 idx))
    (harr : lookupName env "%arrayidx6.le1046" = some (.ptr pa))
    (hsub : ee - idx = nv)
    (hc : stage2NoEventCalls gap "num_fast_el1"
      [.ptr pa, .int 64 nv, .ptr dd, .ptr eiAddr]
      (writeBytes s.mem eiAddr (natToBytes 0 8)) s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsIfThen471Cells env nv r)
        { s with mem := r.mem, next := r.next,
                 pc := "cleanup491", pre := some "if.then471" }) := by
  have hz : evalICmp .eq (BitVec.ofNat 32 1) (BitVec.ofNat 32 0) = 0 :=
    valueArms_icmp_eq_zero (by decide)
  have hcode : denoteCode (stage2NoEventCalls gap) valueArmsIfThen471Instrs
      (stateAt env s) =
      some (stateAt (valueArmsIfThen471Cells env nv r)
        { s with mem := r.mem, next := r.next }) := by
    unfold valueArmsIfThen471Instrs
    rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap) (env := env) (s := s)
      (p := "%d") (sz := 8) (a := dd) hd]
    rw [stage2NoEventWalk_denote_lifetimeStart (gap := gap) (env := env) (s := s)
      (p := "%ei") (sz := 8) (a := eiAddr) hei]
    rw [valueArms_denote_store64_imm (calls := stage2NoEventCalls gap)
      (env := env) (s := s) (p := "%ei") (x := BitVec.ofNat 64 0) hei]
    change denoteCode (stage2NoEventCalls gap)
      [Instr.binop "%sub475" BinOp.sub 64 (Operand.reg "%ee.1") (Operand.reg "%idxprom.lcssa"),
       Instr.call "%call476" (Ty.int 32) "num_fast_el1"
         [(Ty.ptr, Operand.reg "%arrayidx6.le1046"), (Ty.int 64, Operand.reg "%sub475"),
          (Ty.ptr, Operand.reg "%d"), (Ty.ptr, Operand.reg "%ei")],
       Instr.icmp "%tobool477.not.not" IPred.eq 32 (Operand.reg "%call476")
         (Operand.imm (.int 32 (BitVec.ofNat 32 0)))]
      (stateAt env
        (stage2NoEventStepState s (writeBytes s.mem eiAddr (natToBytes 0 8)) s.next)) = _
    rw [denoteCode_sub_reg (calls := stage2NoEventCalls gap) (env := env)
      (s := stage2NoEventStepState s (writeBytes s.mem eiAddr (natToBytes 0 8)) s.next)
      (d := "%sub475") (a := "%ee.1") (b := "%idxprom.lcssa") hee hidx (is := _)]
    rw [valueArms_denote_call4 (calls := stage2NoEventCalls gap)
      (env := ("%sub475", .int 64 (ee - idx)) :: env)
      (s := stage2NoEventStepState s (writeBytes s.mem eiAddr (natToBytes 0 8)) s.next)
      (d := "%call476") (callee := "num_fast_el1")
      (p := "%arrayidx6.le1046") (n := "%sub475") (o := "%d") (e := "%ei")
      (pa := pa) (nv := ee - idx) (oa := dd) (ea := eiAddr) (r := r)
      (by skip_lk)
      (by simp only [lookupName_cons_self])
      (by skip_lk)
      (by skip_lk)
      (by rw [hsub]; exact hc) (is := _)]
    rw [hret]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := stage2NoEventCalls gap)
      (env := ("%call476", .int 32 (BitVec.ofNat 32 1)) ::
        ("%sub475", .int 64 (ee - idx)) :: env)
      (s := { stage2NoEventStepState s (writeBytes s.mem eiAddr (natToBytes 0 8)) s.next with
                mem := r.mem, next := r.next })
      (d := "%tobool477.not.not") (a := "%call476") (p := .eq) (w := 32)
      (x := BitVec.ofNat 32 1) (c := BitVec.ofNat 32 0)
      (by simp only [lookupName_cons_self]) (is := [])]
    rw [hz]
    simp only [denoteCode_nil, valueArmsIfThen471Cells]
    rw [hret, ← hsub]
    rfl
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsIfThen471Cells env nv r)
      { s with mem := r.mem, next := r.next })
    (b := ⟨"if.then471", valueArmsIfThen471Instrs,
      Term.condbr (Operand.reg "%tobool477.not.not") "cleanup491.thread" "cleanup491"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_if_then471
  · exact hcode
  · rw [stage2NoEventLitChain_execTerm_condbr
      (stateAt (valueArmsIfThen471Cells env nv r)
        { s with mem := r.mem, next := r.next }) "%tobool477.not.not"
      "cleanup491.thread" "cleanup491" "if.then471"
      (by simp only [stateAt, valueArmsIfThen471Cells, hpc])
      (evalOperand_reg_of (valueArmsIfThen471Cells env nv r) _ "%tobool477.not.not"
        (.int 1 0) (by simp only [valueArmsIfThen471Cells, lookupName_cons_self]))]
    rfl

/-- `cleanup491`'s cells: the conversion word and its `7`-byte addend. -/
abbrev valueArmsCleanup491Cells (env : Env) (bits : BitVec 64) : Env :=
  ("%add489", .int 64 (bits + BitVec.ofNat 64 7)) ::
    ("%62", .int 64 bits) :: env

theorem valueArms_step_cleanup491 {gap : Calls} {env : Env} {s : State}
    {dd eiAddr : Nat} {bits : BitVec 64}
    (hpc : s.pc = "cleanup491")
    (hd : lookupName env "%d" = some (.ptr dd))
    (hload : readBytes s.mem dd 8 = some (natToBytes bits.toNat 8))
    (hei : lookupName env "%ei" = some (.ptr eiAddr)) :
    step (stage2NoEventCalls gap) stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsCleanup491Cells env bits)
        { s with pc := "if.end545", pre := some "cleanup491" }) := by
  have hcode : denoteCode (stage2NoEventCalls gap) valueArmsCleanup491Instrs
      (stateAt env s) = some (stateAt (valueArmsCleanup491Cells env bits) s) := by
    unfold valueArmsCleanup491Instrs
    rw [denoteCode_load64 (calls := stage2NoEventCalls gap) (env := env) (s := s)
      (d := "%62") (p := "%d") (a := dd) (v := bits) hd hload]
    rw [stage2NoEventWalk_denote_add_imm_w (calls := stage2NoEventCalls gap)
      (env := ("%62", .int 64 bits) :: env) (s := s)
      (d := "%add489") (a := "%62") (w := 64) (x := bits) (c := BitVec.ofNat 64 7)
      (by simp only [lookupName_cons_self])]
    rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
      (env := ("%add489", .int 64 (bits + BitVec.ofNat 64 7)) ::
        ("%62", .int 64 bits) :: env) (s := s) (p := "%ei") (sz := 8) (a := eiAddr)
      (by skip_lk)]
    rw [stage2NoEventWalk_denote_lifetimeEnd (gap := gap)
      (env := ("%add489", .int 64 (bits + BitVec.ofNat 64 7)) ::
        ("%62", .int 64 bits) :: env) (s := s) (p := "%d") (sz := 8) (a := dd)
      (by skip_lk)]
    simp only [denoteCode_nil, valueArmsCleanup491Cells]
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsCleanup491Cells env bits) s)
    (b := ⟨"cleanup491", valueArmsCleanup491Instrs, Term.br "if.end545"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_cleanup491
  · exact hcode
  · simp only [execTerm, stateAt, hpc]

/-- `if.end545`'s cells: the count selection and the extent test. -/
abbrev valueArmsIfEnd545Cells (env : Env) (pn tk0 tm0 ee cd : BitVec 64) : Env :=
  ("%cmp546", .int 1 (evalICmp .ult ee cd)) ::
    ("%terms.12", .int 64 (pn + tm0)) ::
      ("%tokens.12", .int 64 (tk0 + BitVec.ofNat 64 1)) ::
        ("%add489.pn", .int 64 pn) :: env

theorem valueArms_step_if_end545 (calls : Calls) (env : Env) (s : State)
    {pn tk0 tm0 ee cd : BitVec 64} {p : String} {op : Operand}
    (hpc : s.pc = "if.end545")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p valueArmsIfEnd545Incoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 pn))
    (htk : lookupName env "%tokens.0.lcssa1073" = some (.int 64 tk0))
    (htm : lookupName env "%terms.0.lcssa1079" = some (.int 64 tm0))
    (hee : lookupName env "%ee.1" = some (.int 64 ee))
    (hcd : lookupName env "%cond" = some (.int 64 cd)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd)
        { s with pc := if evalICmp .ult ee cd = 1 then "land.rhs552" else "after_value",
                 pre := some "if.end545" }) := by
  have hcode : denoteCode calls valueArmsIfEnd545Instrs (stateAt env s) =
      some (stateAt (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd) s) := by
    unfold valueArmsIfEnd545Instrs
    block_phi_run
    · change denoteCode calls
        [Instr.binop "%tokens.12" BinOp.add 64 (Operand.reg "%tokens.0.lcssa1073")
           (Operand.imm (.int 64 (BitVec.ofNat 64 1))),
         Instr.binop "%terms.12" BinOp.add 64 (Operand.reg "%add489.pn")
           (Operand.reg "%terms.0.lcssa1079"),
         Instr.icmp "%cmp546" IPred.ult 64 (Operand.reg "%ee.1")
           (Operand.reg "%cond")]
        (stateAt (("%add489.pn", .int 64 pn) :: env) s) =
        some (stateAt (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd) s)
      rw [stage2NoEventWalk_denote_add_imm_w (calls := calls)
        (env := ("%add489.pn", .int 64 pn) :: env) (s := s)
        (d := "%tokens.12") (a := "%tokens.0.lcssa1073") (w := 64) (x := tk0)
        (c := BitVec.ofNat 64 1)
        (by rw [lookupName_cons_ne _ _ (by decide)]; exact htk)]
      rw [denoteCode_add_reg (calls := calls)
        (env := ("%tokens.12", .int 64 (tk0 + BitVec.ofNat 64 1)) ::
          ("%add489.pn", .int 64 pn) :: env) (s := s)
        (d := "%terms.12") (a := "%add489.pn") (b := "%terms.0.lcssa1079")
        (x := pn) (y := tm0)
        (by rw [lookupName_cons_ne _ _ (by decide), lookupName_cons_self])
        (by skip_lk) (is := _)]
      rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
        (env := ("%terms.12", .int 64 (pn + tm0)) ::
          ("%tokens.12", .int 64 (tk0 + BitVec.ofNat 64 1)) ::
            ("%add489.pn", .int 64 pn) :: env) (s := s)
        (d := "%cmp546") (a := "%ee.1") (b := "%cond") (p := .ult) (w := 64)
        (x := ee) (y := cd)
        (by skip_lk)
        (by skip_lk) (is := [])]
      simp only [denoteCode_nil, valueArmsIfEnd545Cells]
    · exact hpre
    · rfl
    · exact hinc
    · exact hop
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd) s)
    (b := ⟨"if.end545", valueArmsIfEnd545Instrs,
      Term.condbr (Operand.reg "%cmp546") "land.rhs552" "after_value"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_if_end545
  · exact hcode
  · rw [stage2NoEventLitChain_execTerm_condbr
      (stateAt (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd) s) "%cmp546"
      "land.rhs552" "after_value" "if.end545"
      (by simp only [stateAt, hpc])
      (evalOperand_reg_of (valueArmsIfEnd545Cells env pn tk0 tm0 ee cd) s "%cmp546"
        (.int 1 (evalICmp .ult ee cd))
        (by simp only [valueArmsIfEnd545Cells, lookupName_cons_self]))]
    rfl

/-! ### The separator loop's blocks -/

/-- The separator `phi`'s predecessors. -/
def valueArmsLandRhs552Incoming : List (String × Operand) :=
  [("while.body557", (Operand.reg "%inc558")), ("if.end545", (Operand.reg "%ee.1"))]

theorem valueArms_landRhs552_incoming_ifEnd545 :
    phiIncoming "if.end545" valueArmsLandRhs552Incoming = some (.reg "%ee.1") := by
  decide

theorem valueArms_landRhs552_incoming_whileBody :
    phiIncoming "while.body557" valueArmsLandRhs552Incoming = some (.reg "%inc558") := by
  decide

/-- `land.rhs552`'s cells: the cursor, its address and the byte. -/
abbrev valueArmsLandRhs552Cells (env : Env) (b : Nat) (r : BitVec 64) (u : UInt8) : Env :=
  ("%75", .int 8 (BitVec.ofNat 8 u.toNat)) ::
    ("%arrayidx553", .ptr (b + (r.signExtend 64).toNat)) ::
      ("%q.01062", .int 64 r) :: env

theorem valueArms_step_land_rhs552 (calls : Calls) (env : Env) (s : State)
    {b : Nat} {r : BitVec 64} {u : UInt8} {p : String} {op : Operand}
    (hpc : s.pc = "land.rhs552")
    (hpre : s.pre = some p)
    (hinc : phiIncoming p valueArmsLandRhs552Incoming = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 64 r))
    (hb : lookupName env "%b" = some (.ptr b))
    (hrpos : (r.signExtend 64).toNat < 2 ^ 63)
    (hu : readByte s.mem (b + (r.signExtend 64).toNat) = some u) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsLandRhs552Cells env b r u)
        { s with pc := "NodeBlock83", pre := some "land.rhs552" }) := by
  have hcode : denoteCode calls valueArmsLandRhs552Instrs (stateAt env s) =
      some (stateAt (valueArmsLandRhs552Cells env b r u) s) := by
    unfold valueArmsLandRhs552Instrs
    block_phi_run
    · change denoteCode calls
        [Instr.gep "%arrayidx553" (Ty.int 8) (Operand.reg "%b")
           (Operand.reg "%q.01062"),
         Instr.load "%75" (Ty.int 8) (Operand.reg "%arrayidx553")]
        (stateAt (("%q.01062", .int 64 r) :: env) s) =
        some (stateAt (valueArmsLandRhs552Cells env b r u) s)
      rw [denoteCode_gep8_reg (calls := calls)
        (env := ("%q.01062", .int 64 r) :: env) (s := s)
        (d := "%arrayidx553") (base := "%b") (off := "%q.01062") (a := b) (idx := r)
        (by rw [lookupName_cons_ne _ _ (by decide)]; exact hb)
        (by simp only [lookupName_cons_self]) hrpos]
      rw [stage2Skip_denote_load8 (calls := calls)
        (env := ("%arrayidx553", .ptr (b + (r.signExtend 64).toNat)) ::
          ("%q.01062", .int 64 r) :: env) (s := s)
        (d := "%75") (p := "%arrayidx553") (a := b + (r.signExtend 64).toNat) (u := u)
        (by simp only [lookupName_cons_self]) hu]
      simp only [denoteCode_nil, valueArmsLandRhs552Cells]
    · exact hpre
    · rfl
    · exact hinc
    · exact hop
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsLandRhs552Cells env b r u) s)
    (b := ⟨"land.rhs552", valueArmsLandRhs552Instrs, Term.br "NodeBlock83"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_land_rhs552
  · exact hcode
  · simp only [execTerm, stateAt, hpc]

theorem valueArms_step_nodeBlock83 (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (hpc : s.pc = "NodeBlock83")
    (h75 : lookupName env "%75" = some (.int 8 v)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot84", .int 1 (evalICmp .slt v (BitVec.ofNat 8 13))) :: env)
        { s with pc := if evalICmp .slt v (BitVec.ofNat 8 13) = 1
                        then "LeafBlock74" else "NodeBlock81",
                 pre := some "NodeBlock83" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_nodeBlock83 rfl rfl h75

theorem valueArms_step_nodeBlock81 (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (hpc : s.pc = "NodeBlock81")
    (h75 : lookupName env "%75" = some (.int 8 v)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%Pivot82", .int 1 (evalICmp .slt v (BitVec.ofNat 8 32))) :: env)
        { s with pc := if evalICmp .slt v (BitVec.ofNat 8 32) = 1
                        then "LeafBlock77" else "LeafBlock79",
                 pre := some "NodeBlock81" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_nodeBlock81 rfl rfl h75

theorem valueArms_step_leafBlock79 (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (hpc : s.pc = "LeafBlock79")
    (h75 : lookupName env "%75" = some (.int 8 v)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf80", .int 1 (evalICmp .eq v (BitVec.ofNat 8 32))) :: env)
        { s with pc := if evalICmp .eq v (BitVec.ofNat 8 32) = 1
                        then "while.body557" else "if.then562",
                 pre := some "LeafBlock79" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_leafBlock79 rfl rfl h75

theorem valueArms_step_leafBlock77 (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (hpc : s.pc = "LeafBlock77")
    (h75 : lookupName env "%75" = some (.int 8 v)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt
        (("%SwitchLeaf78", .int 1 (evalICmp .eq v (BitVec.ofNat 8 13))) :: env)
        { s with pc := if evalICmp .eq v (BitVec.ofNat 8 13) = 1
                        then "while.body557" else "if.then562",
                 pre := some "LeafBlock77" }) :=
  valueArms_step_icmp_imm calls env s hpc valueArms_find_leafBlock77 rfl rfl h75

/-- `LeafBlock74`'s cells: the shifted byte and its membership test. -/
abbrev valueArmsLeafBlock74Cells (env : Env) (v : BitVec 8) : Env :=
  ("%SwitchLeaf76",
      .int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1))) ::
    ("%.off75", .int 8 (v + BitVec.ofNat 8 247)) :: env

theorem valueArms_step_leafBlock74 (calls : Calls) (env : Env) (s : State)
    {v : BitVec 8} (hpc : s.pc = "LeafBlock74")
    (h75 : lookupName env "%75" = some (.int 8 v)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsLeafBlock74Cells env v)
        { s with pc := if evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1
                        then "while.body557" else "if.then562",
                 pre := some "LeafBlock74" }) := by
  have hcode : denoteCode calls valueArmsLeafBlock74Instrs (stateAt env s) =
      some (stateAt (valueArmsLeafBlock74Cells env v) s) := by
    unfold valueArmsLeafBlock74Instrs
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
      (d := "%.off75") (a := "%75") (w := 8) (x := v) (c := BitVec.ofNat 8 247) h75]
    rw [stage2NoEventWalk_denote_icmp_imm (calls := calls)
      (env := ("%.off75", .int 8 (v + BitVec.ofNat 8 247)) :: env) (s := s)
      (d := "%SwitchLeaf76") (a := "%.off75") (p := .ule) (w := 8)
      (x := v + BitVec.ofNat 8 247) (c := BitVec.ofNat 8 1)
      (by simp only [lookupName_cons_self]) (is := [])]
    simp only [denoteCode_nil, valueArmsLeafBlock74Cells]
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsLeafBlock74Cells env v) s)
    (b := ⟨"LeafBlock74", valueArmsLeafBlock74Instrs,
      Term.condbr (Operand.reg "%SwitchLeaf76") "while.body557" "if.then562"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_leafBlock74
  · exact hcode
  · rw [stage2NoEventLitChain_execTerm_condbr
      (stateAt (valueArmsLeafBlock74Cells env v) s) "%SwitchLeaf76"
      "while.body557" "if.then562" "LeafBlock74" (by simp only [stateAt, hpc])
      (evalOperand_reg_of (valueArmsLeafBlock74Cells env v) s "%SwitchLeaf76"
        (.int 1 (evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1)))
        (by simp only [valueArmsLeafBlock74Cells, lookupName_cons_self]))]
    rfl

/-- `while.body557`'s cells: the increment and its test. -/
abbrev valueArmsWhileBody557Cells (env : Env) (r cd : BitVec 64) : Env :=
  ("%exitcond1171.not", .int 1 (evalICmp .eq (r + BitVec.ofNat 64 1) cd)) ::
    ("%inc558", .int 64 (r + BitVec.ofNat 64 1)) :: env

theorem valueArms_step_while_body557 (calls : Calls) (env : Env) (s : State)
    {r cd : BitVec 64} (hpc : s.pc = "while.body557")
    (hq : lookupName env "%q.01062" = some (.int 64 r))
    (hcd : lookupName env "%cond" = some (.int 64 cd)) :
    step calls stage2NoEventBody (stateAt env s) =
      .jump (stateAt (valueArmsWhileBody557Cells env r cd)
        { s with pc := if evalICmp .eq (r + BitVec.ofNat 64 1) cd = 1
                        then "after_value" else "land.rhs552",
                 pre := some "while.body557" }) := by
  have hcode : denoteCode calls valueArmsWhileBody557Instrs (stateAt env s) =
      some (stateAt (valueArmsWhileBody557Cells env r cd) s) := by
    unfold valueArmsWhileBody557Instrs
    rw [stage2NoEventWalk_denote_add_imm_w (calls := calls) (env := env) (s := s)
      (d := "%inc558") (a := "%q.01062") (w := 64) (x := r) (c := BitVec.ofNat 64 1) hq]
    rw [stage2NoEventWalk_denote_icmp_reg (calls := calls)
      (env := ("%inc558", .int 64 (r + BitVec.ofNat 64 1)) :: env) (s := s)
      (d := "%exitcond1171.not") (a := "%inc558") (b := "%cond") (p := .eq) (w := 64)
      (x := r + BitVec.ofNat 64 1) (y := cd)
      (by simp only [lookupName_cons_self])
      (by rw [lookupName_cons_ne _ _ (by decide)]; exact hcd) (is := [])]
    simp only [denoteCode_nil, valueArmsWhileBody557Cells]
  refine valueArms_step_at_block (s := stateAt env s)
    (s' := stateAt (valueArmsWhileBody557Cells env r cd) s)
    (b := ⟨"while.body557", valueArmsWhileBody557Instrs,
      Term.condbr (Operand.reg "%exitcond1171.not") "after_value" "land.rhs552"⟩)
    (c := _) ?_ ?_ ?_
  · simpa only [stateAt, hpc] using valueArms_find_while_body557
  · exact hcode
  · rw [stage2NoEventLitChain_execTerm_condbr
      (stateAt (valueArmsWhileBody557Cells env r cd) s) "%exitcond1171.not"
      "after_value" "land.rhs552" "while.body557" (by simp only [stateAt, hpc])
      (evalOperand_reg_of (valueArmsWhileBody557Cells env r cd) s "%exitcond1171.not"
        (.int 1 (evalICmp .eq (r + BitVec.ofNat 64 1) cd))
        (by simp only [valueArmsWhileBody557Cells, lookupName_cons_self]))]
    rfl


/-! ### The separator loop -/

/-- Resolve a register read through a `cells` builder: unfold the list and peel
the block's own cells until the incoming lookup is reached. -/
macro "cells_lk" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [stateAt, cells]
   repeat first
    | rw [lookupName_cons_self]
    | rw [lookupName_cons_ne _ _ (by decide)]
    | assumption))

/-- **A state viewed at its own environment is itself.** -/
theorem valueArms_stateAt_self (s : State) : stateAt s.env s = s := by
  cases s; rfl

/-- **A sign-extended `ofNat` word is its number.** -/
theorem valueArms_signExtend_ofNat {r : Nat} (h : r < 2 ^ 64) :
    ((BitVec.ofNat 64 r).signExtend 64).toNat = r := by
  rw [BitVec.signExtend_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **A successor at 64 bits.** -/
theorem valueArms_ofNat64_succ {r : Nat} (h : r + 1 < 2 ^ 64) :
    BitVec.ofNat 64 r + BitVec.ofNat 64 1 = BitVec.ofNat 64 (r + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp [Nat.mod_eq_of_lt (by omega : r < 2 ^ 64), Nat.mod_eq_of_lt h]

/-! ### The entry chain's base lookups

The arms' blocks add `phi` cells, comparisons and staging cells, and none of them
binds a parameter or an entry-chain cell.  Each step therefore keeps
`Stage2NoEventWalkBaseLookups`; its side condition is a Boolean check that the
step's own cell list avoids the base names.
-/

/-- Whether a cell list binds none of the entry chain's base names. -/
def valueArmsCellsOutsideBase (cs : List (String × Value)) : Bool :=
  cs.all fun p => decide (p.1 ∉ stage2NoEventWalkBaseNames)

private theorem valueArmsCellsOutsideBase_spec {cs : List (String × Value)}
    (h : valueArmsCellsOutsideBase cs = true) :
    ∀ n, n ∈ stage2NoEventWalkBaseNames → n ∉ cs.map (·.1) := by
  intro n hn hmem
  obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hmem
  have hp' : p.1 ∉ stage2NoEventWalkBaseNames :=
    of_decide_eq_true ((List.all_eq_true.mp h) p hp)
  exact hp' (hpn ▸ hn)

/-- A name that is not in a cell list reads through its `cells` builder. -/
private theorem valueArms_cells_notin :
    ∀ (cs : List (String × Value)) (n : String) (env : Env),
      n ∉ cs.map (·.1) → lookupName (cells cs env) n = lookupName env n
  | [], _, _, _ => rfl
  | (k, w) :: cs, n, env, h => by
      have hk : k ≠ n := by intro hkn; exact h (by subst hkn; simp)
      simp only [cells, lookupName_cons_ne w (cells cs env) hk]
      exact valueArms_cells_notin cs n env (fun hc => h (List.mem_cons_of_mem _ hc))

/-- **The base lookups transport across a step's cell list.** -/
theorem valueArms_baseLookups_env {K : Stage2NoEventWalkCarry} {s s0 : State}
    {cs : List (String × Value)}
    (h : Stage2NoEventWalkBaseLookups K s0)
    (he : s.env = cells cs s0.env)
    (hd : valueArmsCellsOutsideBase cs = true) :
    Stage2NoEventWalkBaseLookups K s := by
  intro n v hv
  show lookupName s.env n = some v
  rw [he, valueArms_cells_notin cs n s0.env ?_]
  exact h n v hv
  · have hmem : n ∈ (stage2NoEventWalkBaseValues K).map (·.1) := List.mem_map_of_mem hv
    rw [stage2NoEventWalkBaseValues_names] at hmem
    exact valueArmsCellsOutsideBase_spec hd n hmem

/-- **A base name list avoids a written list**, from its Boolean check. -/
theorem valueArms_baseNames_notin {l : List String}
    (h : stage2NoEventWalkBaseNames.all (fun n => decide (n ∉ l)) = true) :
    ∀ n, n ∈ stage2NoEventWalkBaseNames → n ∉ l := by
  intro n hn
  exact of_decide_eq_true ((List.all_eq_true.mp h) n hn)

/-- **The `after_value` entry state**: the seven `phi` operands and the block. -/
structure valueArmsAfter (K : Stage2NoEventWalkCarry) (fr sp knext : Nat)
    (tk tm : BitVec 64) (s : State) : Prop where
  pc : s.pc = "after_value"
  pre : s.pre = some "while.body557" ∨ s.pre = some "if.end545"
  frame : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 (BitVec.ofNat 8 fr))
  spLk : lookupName s.env "%sp.0.lcssa1091.wide" =
    some (.int 32 (BitVec.ofNat 32 sp))
  kLk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext))
  alen : lookupName s.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arena : lookupName s.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  terms : lookupName s.env "%terms.12" = some (.int 64 tm)
  tokens : lookupName s.env "%tokens.12" = some (.int 64 tk)

/-- **The separator loop's invariant**: the cursor's `phi` selection, the byte at
it, the document's base and bound, and the cells the loop leaves alone. -/
structure valueArmsSepInv (K : Stage2NoEventWalkCarry) (b cond fr sp knext : Nat)
    (tk tm : BitVec 64) (σ : Nat → UInt8) (mem : Mem) (r : Nat) (s : State) : Prop where
  pc : s.pc = "land.rhs552"
  phi : ∃ (p : String) (op : Operand), s.pre = some p ∧
    phiIncoming p valueArmsLandRhs552Incoming = some op ∧
    evalOperand (stateAt s.env s) op = some (.int 64 (BitVec.ofNat 64 r))
  bLk : lookupName s.env "%b" = some (.ptr b)
  condLk : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond))
  memEq : s.mem = mem
  byte : readByte mem (b + r) = some (σ r)
  frame : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 (BitVec.ofNat 8 fr))
  spLk : lookupName s.env "%sp.0.lcssa1091.wide" =
    some (.int 32 (BitVec.ofNat 32 sp))
  kLk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext))
  alen : lookupName s.env "%alen.0.ph1405" =
    some (.int 64 (BitVec.ofNat 64 K.arena.length))
  arena : lookupName s.env "%arena.0.ph1406" =
    some (.int 64 (BitVec.ofNat 64 K.arenaWord))
  terms : lookupName s.env "%terms.12" = some (.int 64 tm)
  tokens : lookupName s.env "%tokens.12" = some (.int 64 tk)

/-- **The loop's last iteration**: `while.body557` increments the cursor and
either reaches `after_value` at the bound or returns to the loop head. -/
theorem valueArms_sepTail {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {σ : Nat → UInt8} {b cond fr sp knext : Nat} {tk tm : BitVec 64} {r : Nat}
    {s : State}
    (hpc : s.pc = "while.body557")
    (hq : lookupName s.env "%q.01062" = some (.int 64 (BitVec.ofNat 64 r)))
    (hcd : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hm : s.mem = mem)
    (hbytes : ∀ i, i < cond → readByte mem (b + i) = some (σ i))
    (hframe : lookupName s.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hterms : lookupName s.env "%terms.12" = some (.int 64 tm))
    (htokens : lookupName s.env "%tokens.12" = some (.int 64 tk))
    (hr : r < cond) (hcond63 : cond < 2 ^ 63)
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 1 ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      ((r + 1 = cond ∧ valueArmsAfter K fr sp knext tk tm s') ∨
       (r + 1 < cond ∧ valueArmsSepInv K b cond fr sp knext tk tm σ mem (r + 1) s')) ∧
      s'.mem = s.mem ∧ Stage2NoEventWalkBaseLookups K s' := by
  have hsucc : BitVec.ofNat 64 r + BitVec.ofNat 64 1 = BitVec.ofNat 64 (r + 1) :=
    valueArms_ofNat64_succ (by omega)
  by_cases hlast : r + 1 = cond
  · have heq : evalICmp .eq (BitVec.ofNat 64 (r + 1)) (BitVec.ofNat 64 cond) = 1 := by
      rw [hlast]; simp [evalICmp]
    let S : State := stateAt
      (valueArmsWhileBody557Cells s.env (BitVec.ofNat 64 r) (BitVec.ofNat 64 cond))
      { s with pc := "after_value", pre := some "while.body557" }
    have hstep : step calls stage2NoEventBody s = .jump S := by
      rw [← valueArms_stateAt_self s]
      simpa [S, hsucc, heq] using
        valueArms_step_while_body557 calls s.env s hpc hq hcd
    have hSb : Stage2NoEventWalkBaseLookups K S :=
      valueArms_baseLookups_env
        (cs := valueArmsWhileBody557Cells [] (BitVec.ofNat 64 r) (BitVec.ofNat 64 cond))
        (s0 := s) hbase (by rfl) (by rfl)
    refine ⟨S, 1, le_rfl, fun k => runFuel_jump_prefix hstep k, Or.inl ⟨hlast, ?_⟩,
      by simp only [S, stateAt], hSb⟩
    refine ⟨rfl, Or.inl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
  · have hnext : r + 1 < cond := by omega
    have hne : BitVec.ofNat 64 (r + 1) ≠ BitVec.ofNat 64 cond := by
      intro h
      have h2 := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at h2
      omega
    have hz : evalICmp .eq (BitVec.ofNat 64 (r + 1)) (BitVec.ofNat 64 cond) = 0 :=
      valueArms_icmp_eq_zero hne
    let S : State := stateAt
      (valueArmsWhileBody557Cells s.env (BitVec.ofNat 64 r) (BitVec.ofNat 64 cond))
      { s with pc := "land.rhs552", pre := some "while.body557" }
    have hstep : step calls stage2NoEventBody s = .jump S := by
      rw [← valueArms_stateAt_self s]
      simpa [S, hsucc, hz] using
        valueArms_step_while_body557 calls s.env s hpc hq hcd
    have hSb : Stage2NoEventWalkBaseLookups K S :=
      valueArms_baseLookups_env
        (cs := valueArmsWhileBody557Cells [] (BitVec.ofNat 64 r) (BitVec.ofNat 64 cond))
        (s0 := s) hbase (by rfl) (by rfl)
    refine ⟨S, 1, le_rfl, fun k => runFuel_jump_prefix hstep k, Or.inr ⟨hnext, ?_⟩,
      by simp only [S, stateAt], hSb⟩
    refine ⟨rfl,
      ⟨"while.body557", .reg "%inc558", rfl, by decide,
        evalOperand_reg_of S.env S "%inc558" (.int 64 (BitVec.ofNat 64 (r + 1)))
          (by dsimp only [S]; cells_lk; rw [hsucc])⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · simpa [S, stateAt] using hm
    · exact hbytes (r + 1) hnext
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk

/-- **One separator-loop iteration**: the head, the three-block classification,
and the increment; either the exit or the head at the next cursor. -/
theorem valueArms_sepStep {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {σ : Nat → UInt8} {b cond fr sp knext : Nat} {tk tm : BitVec 64} {r : Nat}
    {s : State}
    (hinv : valueArmsSepInv K b cond fr sp knext tk tm σ mem r s)
    (hr : r < cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte mem (b + i) = some (σ i))
    (hws : ∀ i, r ≤ i → i < cond → stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 5 ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      ((r + 1 = cond ∧ valueArmsAfter K fr sp knext tk tm s') ∨
       (r + 1 < cond ∧ valueArmsSepInv K b cond fr sp knext tk tm σ mem (r + 1) s')) ∧
      s'.mem = s.mem ∧ Stage2NoEventWalkBaseLookups K s' := by
  obtain ⟨hpc, ⟨pre, op, hpre, hinc, hop⟩, hb, hcd, hmem, hbyte, hframe, hsp, hk,
    halen, harena, hterms, htokens⟩ := hinv
  have hpos : ((BitVec.ofNat 64 r).signExtend 64).toNat < 2 ^ 63 := by
    rw [valueArms_signExtend_ofNat (by omega)]; omega
  have hu : readByte s.mem (b + ((BitVec.ofNat 64 r).signExtend 64).toNat) =
      some (σ r) := by
    rw [valueArms_signExtend_ofNat (by omega), hmem]; exact hbyte
  let v : BitVec 8 := BitVec.ofNat 8 (σ r).toNat
  have hwsr : stage2SkipWs v = true := hws r le_rfl hr
  let S1 : State := stateAt (valueArmsLandRhs552Cells s.env b (BitVec.ofNat 64 r) (σ r))
    { s with pc := "NodeBlock83", pre := some "land.rhs552" }
  have hs1 : step calls stage2NoEventBody s = .jump S1 := by
    rw [← valueArms_stateAt_self s]
    simpa [S1, hmem] using
      valueArms_step_land_rhs552 calls s.env s hpc hpre hinc hop hb hpos hu
  have hSb1 : Stage2NoEventWalkBaseLookups K S1 :=
    valueArms_baseLookups_env
      (cs := valueArmsLandRhs552Cells [] b (BitVec.ofNat 64 r) (σ r))
      (s0 := s) hbase (by rfl) (by rfl)
  have h75₁ : lookupName S1.env "%75" = some (.int 8 v) := by
    dsimp only [S1, v]; cells_lk
  by_cases h13 : v.slt (BitVec.ofNat 8 13) = true
  · have hpiv : evalICmp .slt v (BitVec.ofNat 8 13) = 1 := by
      rw [show evalICmp .slt v (BitVec.ofNat 8 13) =
        BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) from rfl, h13]; rfl
    let S2 : State := stateAt (("%Pivot84", .int 1 1) :: S1.env)
      { S1 with pc := "LeafBlock74", pre := some "NodeBlock83" }
    have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
      valueArms_baseLookups_env (cs := [("%Pivot84", .int 1 1)]) (s0 := S1) hSb1
        (by rfl) (by rfl)
    have hs2 : step calls stage2NoEventBody S1 = .jump S2 := by
      rw [← valueArms_stateAt_self S1]
      simpa [S2, hpiv] using
        valueArms_step_nodeBlock83 calls S1.env S1 rfl h75₁
    have hleaf : (v + BitVec.ofNat 8 247).ule (BitVec.ofNat 8 1) = true := by
      rw [← stage2SkipLeaf_slt13_true h13, stage2SkipLeaf_eq_ws]; exact hwsr
    have hleafE : evalICmp .ule (v + BitVec.ofNat 8 247) (BitVec.ofNat 8 1) = 1 :=
      stage2Skip_ule_one_of hleaf
    let S3 : State := stateAt (valueArmsLeafBlock74Cells S2.env v)
      { S2 with pc := "while.body557", pre := some "LeafBlock74" }
    have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
      valueArms_baseLookups_env (cs := valueArmsLeafBlock74Cells [] v) (s0 := S2) hSb2
        (by rfl) (by rfl)
    have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
      rw [← valueArms_stateAt_self S2]
      rw [valueArms_step_leafBlock74 calls S2.env S2 rfl
        (by dsimp only [S2, S1, v]; cells_lk)]
      simp only [S3]
      simp only [v, stage2Skip_uint8_toBitVec] at hleafE ⊢
      simp [hleafE]
    have hm3 : S3.mem = mem := by
      simpa [S3, S2, S1, stateAt] using hmem
    obtain ⟨s', jt, hjt, hrun, hcase, hmemT, hbaseT⟩ :=
      valueArms_sepTail (calls := calls) (K := K) (mem := mem) (σ := σ)
      (b := b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
      (tk := tk) (tm := tm) (r := r) (s := S3)
      (by simp only [S3, S2, stateAt]) (by dsimp only [S3, S2, S1, v]; cells_lk)
      (by dsimp only [S3, S2, S1, v]; cells_lk) (by dsimp only [S3, S2, S1, v]; cells_lk) hm3
      hbytes (by dsimp only [S3, S2, S1, v]; cells_lk) (by dsimp only [S3, S2, S1, v]; cells_lk)
      (by dsimp only [S3, S2, S1, v]; cells_lk) (by dsimp only [S3, S2, S1, v]; cells_lk)
      (by dsimp only [S3, S2, S1, v]; cells_lk) (by dsimp only [S3, S2, S1, v]; cells_lk)
      (by dsimp only [S3, S2, S1, v]; cells_lk) hr hcond63 hSb3
    refine ⟨s', 3 + jt, by omega, ?_, hcase, hmemT.trans (hm3.trans hmem.symm), hbaseT⟩
    intro k
    rw [show 3 + jt + k = 1 + (1 + (1 + (jt + k))) from by omega]
    rw [runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3]
    exact hrun k
  · have h13f : v.slt (BitVec.ofNat 8 13) = false := by
      cases h : v.slt (BitVec.ofNat 8 13) <;> simp_all
    have hpiv : evalICmp .slt v (BitVec.ofNat 8 13) = 0 := by
      rw [show evalICmp .slt v (BitVec.ofNat 8 13) =
        BitVec.ofBool (v.slt (BitVec.ofNat 8 13)) from rfl, h13f]; rfl
    let S2 : State := stateAt (("%Pivot84", .int 1 0) :: S1.env)
      { S1 with pc := "NodeBlock81", pre := some "NodeBlock83" }
    have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
      valueArms_baseLookups_env (cs := [("%Pivot84", .int 1 0)]) (s0 := S1) hSb1
        (by rfl) (by rfl)
    have hs2 : step calls stage2NoEventBody S1 = .jump S2 := by
      rw [← valueArms_stateAt_self S1]
      simpa [S2, hpiv] using
        valueArms_step_nodeBlock83 calls S1.env S1 rfl h75₁
    have h75₂ : lookupName S2.env "%75" = some (.int 8 v) := by
      dsimp only [S2, S1, v]; cells_lk
    by_cases h32 : v.slt (BitVec.ofNat 8 32) = true
    · have hpiv2 : evalICmp .slt v (BitVec.ofNat 8 32) = 1 := by
        rw [show evalICmp .slt v (BitVec.ofNat 8 32) =
          BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) from rfl, h32]; rfl
      let S3 : State := stateAt (("%Pivot82", .int 1 1) :: S2.env)
        { S2 with pc := "LeafBlock77", pre := some "NodeBlock81" }
      have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
        valueArms_baseLookups_env (cs := [("%Pivot82", .int 1 1)]) (s0 := S2) hSb2
          (by rfl) (by rfl)
      have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
        rw [← valueArms_stateAt_self S2]
        simpa [S3, hpiv2] using
          valueArms_step_nodeBlock81 calls S2.env S2 rfl h75₂
      have hleaf : (v == BitVec.ofNat 8 13) = true := by
        rw [← stage2SkipLeaf_slt32_true h13f h32, stage2SkipLeaf_eq_ws]; exact hwsr
      have hleafE : evalICmp .eq v (BitVec.ofNat 8 13) = 1 :=
        stage2Skip_beq_one_of hleaf
      let S4 : State := stateAt (("%SwitchLeaf78", .int 1 1) :: S3.env)
        { S3 with pc := "while.body557", pre := some "LeafBlock77" }
      have hSb4 : Stage2NoEventWalkBaseLookups K S4 :=
        valueArms_baseLookups_env (cs := [("%SwitchLeaf78", .int 1 1)]) (s0 := S3) hSb3
          (by rfl) (by rfl)
      have hs4 : step calls stage2NoEventBody S3 = .jump S4 := by
        rw [← valueArms_stateAt_self S3]
        rw [valueArms_step_leafBlock77 calls S3.env S3 rfl
          (by dsimp only [S3, S2, S1, v]; cells_lk)]
        simp only [S4]
        simp only [v, stage2Skip_uint8_toBitVec] at hleafE ⊢
        simp [hleafE]
      have hm4 : S4.mem = mem := by
        simpa [S4, S3, S2, S1, stateAt] using hmem
      obtain ⟨s', jt, hjt, hrun, hcase, hmemT, hbaseT⟩ :=
        valueArms_sepTail (calls := calls) (K := K) (mem := mem) (σ := σ)
          (b := b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
          (tk := tk) (tm := tm) (r := r) (s := S4)
          (by simp only [S4, S3, stateAt]) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk) hm4
          hbytes (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) hr hcond63 hSb4
      refine ⟨s', 4 + jt, by omega, ?_, hcase, hmemT.trans (hm4.trans hmem.symm), hbaseT⟩
      intro k
      rw [show 4 + jt + k = 1 + (1 + (1 + (1 + (jt + k)))) from by omega]
      rw [runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3,
        runFuel_jump_prefix hs4]
      exact hrun k
    · have h32f : v.slt (BitVec.ofNat 8 32) = false := by
        cases h : v.slt (BitVec.ofNat 8 32) <;> simp_all
      have hpiv2 : evalICmp .slt v (BitVec.ofNat 8 32) = 0 := by
        rw [show evalICmp .slt v (BitVec.ofNat 8 32) =
          BitVec.ofBool (v.slt (BitVec.ofNat 8 32)) from rfl, h32f]; rfl
      let S3 : State := stateAt (("%Pivot82", .int 1 0) :: S2.env)
        { S2 with pc := "LeafBlock79", pre := some "NodeBlock81" }
      have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
        valueArms_baseLookups_env (cs := [("%Pivot82", .int 1 0)]) (s0 := S2) hSb2
          (by rfl) (by rfl)
      have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
        rw [← valueArms_stateAt_self S2]
        simpa [S3, hpiv2] using
          valueArms_step_nodeBlock81 calls S2.env S2 rfl h75₂
      have hleaf : (v == BitVec.ofNat 8 32) = true := by
        rw [← stage2SkipLeaf_slt32_false h13f h32f, stage2SkipLeaf_eq_ws]; exact hwsr
      have hleafE : evalICmp .eq v (BitVec.ofNat 8 32) = 1 :=
        stage2Skip_beq_one_of hleaf
      let S4 : State := stateAt (("%SwitchLeaf80", .int 1 1) :: S3.env)
        { S3 with pc := "while.body557", pre := some "LeafBlock79" }
      have hSb4 : Stage2NoEventWalkBaseLookups K S4 :=
        valueArms_baseLookups_env (cs := [("%SwitchLeaf80", .int 1 1)]) (s0 := S3) hSb3
          (by rfl) (by rfl)
      have hs4 : step calls stage2NoEventBody S3 = .jump S4 := by
        rw [← valueArms_stateAt_self S3]
        rw [valueArms_step_leafBlock79 calls S3.env S3 rfl
          (by dsimp only [S3, S2, S1, v]; cells_lk)]
        simp only [S4]
        simp only [v, stage2Skip_uint8_toBitVec] at hleafE ⊢
        simp [hleafE]
      have hm4 : S4.mem = mem := by
        simpa [S4, S3, S2, S1, stateAt] using hmem
      obtain ⟨s', jt, hjt, hrun, hcase, hmemT, hbaseT⟩ :=
        valueArms_sepTail (calls := calls) (K := K) (mem := mem) (σ := σ)
          (b := b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
          (tk := tk) (tm := tm) (r := r) (s := S4)
          (by simp only [S4, S3, stateAt]) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk) hm4
          hbytes (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) (by dsimp only [S4, S3, S2, S1, v]; cells_lk)
          (by dsimp only [S4, S3, S2, S1, v]; cells_lk) hr hcond63 hSb4
      refine ⟨s', 4 + jt, by omega, ?_, hcase, hmemT.trans (hm4.trans hmem.symm), hbaseT⟩
      intro k
      rw [show 4 + jt + k = 1 + (1 + (1 + (1 + (jt + k)))) from by omega]
      rw [runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3,
        runFuel_jump_prefix hs4]
      exact hrun k

/-- **The separator loop, from its head.**  `5 * (cond - r)` iterations' worth of
fuel suffice, and the run ends at `after_value`'s entry with the cells the loop
left untouched. -/
theorem valueArms_sepLoop {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {σ : Nat → UInt8} {b cond fr sp knext : Nat} {tk tm : BitVec 64} :
    ∀ (r : Nat) (s : State), valueArmsSepInv K b cond fr sp knext tk tm σ mem r s →
      r < cond → cond < 2 ^ 63 →
      (∀ i, i < cond → readByte mem (b + i) = some (σ i)) →
      (∀ i, r ≤ i → i < cond → stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) →
      Stage2NoEventWalkBaseLookups K s →
      ∃ s' j, j ≤ 5 * (cond - r) ∧
        (∀ k, runFuel calls (j + k) stage2NoEventBody s =
          runFuel calls k stage2NoEventBody s') ∧
        valueArmsAfter K fr sp knext tk tm s' ∧ s'.mem = s.mem ∧
        Stage2NoEventWalkBaseLookups K s' := by
  intro r s
  have key : ∀ d (r : Nat) (s : State), cond - r = d →
      valueArmsSepInv K b cond fr sp knext tk tm σ mem r s → r < cond →
      cond < 2 ^ 63 → (∀ i, i < cond → readByte mem (b + i) = some (σ i)) →
      (∀ i, r ≤ i → i < cond → stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true) →
      Stage2NoEventWalkBaseLookups K s →
      ∃ s' j, j ≤ 5 * (cond - r) ∧
        (∀ k, runFuel calls (j + k) stage2NoEventBody s =
          runFuel calls k stage2NoEventBody s') ∧
        valueArmsAfter K fr sp knext tk tm s' ∧ s'.mem = s.mem ∧
        Stage2NoEventWalkBaseLookups K s' := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
        intro r s hd hinv hr hcond63 hbytes hws hbase
        obtain ⟨s1, j1, hj1, hrun1, hcase, hmem1, hbase1⟩ :=
          valueArms_sepStep (calls := calls) (K := K) (mem := mem) (σ := σ)
            (b := b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
            (tk := tk) (tm := tm) (r := r) (s := s) hinv hr hcond63 hbytes hws hbase
        rcases hcase with ⟨hlast, hafter⟩ | ⟨hnext, hinv'⟩
        · exact ⟨s1, j1, by omega, hrun1, hafter, hmem1, hbase1⟩
        · have hd' : cond - (r + 1) < d := by omega
          obtain ⟨s2, j2, hj2, hrun2, hafter, hmem2, hbase2⟩ :=
            ih (cond - (r + 1)) hd' (r + 1) s1 rfl hinv' hnext hcond63 hbytes
              (fun i hi hlt => hws i (by omega) hlt) hbase1
          refine ⟨s2, j1 + j2, by omega, ?_, hafter, hmem2.trans hmem1, hbase2⟩
          intro k
          rw [show j1 + j2 + k = j1 + (j2 + k) from by omega, hrun1 (j2 + k)]
          exact hrun2 k
  exact key (cond - r) r s rfl


/-! ### `if.end545` to `after_value` -/

/-- **`if.end545`'s selection, its count stores and the separator skip.**  From
the merge's entry the block selects the number's `%add489` or the literal's tag,
stores the incremented counts, and either leaves directly (`q = cond`) or runs
the separator loop to `after_value`'s entry. -/
theorem valueArms_ifEnd545 {calls : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {σ : Nat → UInt8} {b cond fr sp knext : Nat} {tk0 tm0 pn : BitVec 64}
    {q : Nat} {s : State} {p : String} {op : Operand}
    (hpc : s.pc = "if.end545") (hpre : s.pre = some p)
    (hinc : phiIncoming p valueArmsIfEnd545Incoming = some op)
    (hop : evalOperand (stateAt s.env s) op = some (.int 64 pn))
    (htk : lookupName s.env "%tokens.0.lcssa1073" = some (.int 64 tk0))
    (htm : lookupName s.env "%terms.0.lcssa1079" = some (.int 64 tm0))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hcd : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hframe : lookupName s.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63) (hmem : s.mem = mem)
    (hbytes : ∀ i, i < cond → readByte mem (b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond → stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 1 + 5 * (cond - q) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      valueArmsAfter K fr sp knext (tk0 + BitVec.ofNat 64 1) (pn + tm0) s' ∧
      s'.mem = s.mem ∧ Stage2NoEventWalkBaseLookups K s' := by
  have hstep := valueArms_step_if_end545 calls s.env s hpc hpre hinc hop htk htm hee hcd
  by_cases hqlt : q < cond
  · have hcmp : evalICmp .ult (BitVec.ofNat 64 q) (BitVec.ofNat 64 cond) = 1 :=
      stage2NoEventICmp_ult_one (by omega) (by omega) hqlt
    let S : State := stateAt
      (valueArmsIfEnd545Cells s.env pn tk0 tm0 (BitVec.ofNat 64 q) (BitVec.ofNat 64 cond))
      { s with pc := "land.rhs552", pre := some "if.end545" }
    have hS : step calls stage2NoEventBody s = .jump S := by
      rw [← valueArms_stateAt_self s]
      simpa [S, hcmp] using hstep
    have hinv : valueArmsSepInv K b cond fr sp knext
        (tk0 + BitVec.ofNat 64 1) (pn + tm0) σ mem q S := by
      refine ⟨rfl, ⟨"if.end545", .reg "%ee.1", rfl, by decide, ?_⟩, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact evalOperand_reg_of S.env S "%ee.1" (.int 64 (BitVec.ofNat 64 q))
          (by dsimp only [S]; cells_lk)
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · simpa [S, stateAt] using hmem
      · exact hbytes q hqlt
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
      · dsimp only [S]; cells_lk
    have hSb : Stage2NoEventWalkBaseLookups K S :=
      valueArms_baseLookups_env
        (cs := valueArmsIfEnd545Cells [] pn tk0 tm0 (BitVec.ofNat 64 q)
          (BitVec.ofNat 64 cond))
        (s0 := s) hbase (by rfl) (by rfl)
    obtain ⟨s', j, hj, hrun, hafter, hmemS, hbaseS⟩ :=
      valueArms_sepLoop (calls := calls) q S hinv hqlt hcond63 hbytes hws hSb
    refine ⟨s', 1 + j, by omega, ?_, hafter, hmemS.trans (by simp only [S, stateAt]),
      hbaseS⟩
    intro k
    rw [show 1 + j + k = 1 + (j + k) from by omega, runFuel_jump_prefix hS]
    exact hrun k
  · have hqeq : q = cond := by omega
    have hcmp : evalICmp .ult (BitVec.ofNat 64 q) (BitVec.ofNat 64 cond) = 0 := by
      rw [hqeq]; exact valueArms_ult_self _
    let S : State := stateAt
      (valueArmsIfEnd545Cells s.env pn tk0 tm0 (BitVec.ofNat 64 q) (BitVec.ofNat 64 cond))
      { s with pc := "after_value", pre := some "if.end545" }
    have hS : step calls stage2NoEventBody s = .jump S := by
      rw [← valueArms_stateAt_self s]
      simpa [S, hcmp] using hstep
    have hSb : Stage2NoEventWalkBaseLookups K S :=
      valueArms_baseLookups_env
        (cs := valueArmsIfEnd545Cells [] pn tk0 tm0 (BitVec.ofNat 64 q)
          (BitVec.ofNat 64 cond))
        (s0 := s) hbase (by rfl) (by rfl)
    refine ⟨S, 1, by omega, fun k => runFuel_jump_prefix hS k, ?_,
      by simp only [S, stateAt], hSb⟩
    refine ⟨rfl, Or.inr rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk
    · dsimp only [S]; cells_lk


/-! ### The number arm -/

/-- **The number arm to `after_value`.**  `if.then471`'s staged call, `cleanup491`'s
word and `+7`, the merge at `if.end545`, and the separator loop.  The call's
answer is the model's: its output word is `bw`, which `cleanup491` adds the
number tag's fixed part to. -/
theorem valueArms_numberRoute {gap : Calls} {K : Stage2NoEventWalkCarry}
    {σ : Nat → UInt8} {lane q cond fr sp knext : Nat} {bw : BitVec 64}
    {tok0 tm0 : Nat} {r : CallOutcome} {s : State}
    (hpc : s.pc = "if.then471")
    (hd : lookupName s.env "%d" = some (.ptr K.d))
    (hei : lookupName s.env "%ei" = some (.ptr (K.next0 + 24)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64)
    (hr : stage2NoEventCalls gap "num_fast_el1"
      [.ptr (K.b + lane), .int 64 (BitVec.ofNat 64 (q - lane)), .ptr K.d,
        .ptr (K.next0 + 24)]
      (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) s.next = some r)
    (hret : r.ret = .int 32 (BitVec.ofNat 32 1))
    (hload : readBytes r.mem K.d 8 = some (natToBytes bw.toNat 8))
    (hframe : lookupName s.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 tok0)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 tm0)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte r.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 3 + 5 * (cond - q) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K fr sp knext (BitVec.ofNat 64 tok0 + BitVec.ofNat 64 1)
        ((bw + BitVec.ofNat 64 7) + BitVec.ofNat 64 tm0) s' ∧
      s'.mem = r.mem ∧ Stage2NoEventWalkBaseLookups K s' := by
  have hsub : BitVec.ofNat 64 q - BitVec.ofNat 64 lane = BitVec.ofNat 64 (q - lane) :=
    valueArms_sub_ofNat hlaneq hq64
  let S1 : State := stateAt (valueArmsIfThen471Cells s.env (BitVec.ofNat 64 (q - lane)) r)
    { s with mem := r.mem, next := r.next,
             pc := "cleanup491", pre := some "if.then471" }
  have hs1 : step (stage2NoEventCalls gap) stage2NoEventBody s = .jump S1 := by
    rw [← valueArms_stateAt_self s]
    simpa [S1] using
      valueArms_step_if_then471 (gap := gap) (env := s.env) (s := s)
        hpc hd hei hee hidx harr hsub hr hret
  have hSb1 : Stage2NoEventWalkBaseLookups K S1 :=
    valueArms_baseLookups_env
      (cs := valueArmsIfThen471Cells [] (BitVec.ofNat 64 (q - lane)) r)
      (s0 := s) hbase (by rfl) (by rfl)
  let S2 : State := stateAt (valueArmsCleanup491Cells S1.env bw)
    { S1 with pc := "if.end545", pre := some "cleanup491" }
  have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
    valueArms_baseLookups_env (cs := valueArmsCleanup491Cells [] bw) (s0 := S1) hSb1
      (by rfl) (by rfl)
  have hs2 : step (stage2NoEventCalls gap) stage2NoEventBody S1 = .jump S2 := by
    rw [← valueArms_stateAt_self S1]
    simpa [S2] using
      valueArms_step_cleanup491 (gap := gap) (env := S1.env) (s := S1)
        rfl (by dsimp only [S1]; cells_lk)
        (by simpa only [S1, stateAt] using hload)
        (by dsimp only [S1]; cells_lk)
  obtain ⟨s', j, hj, hrun, hafter, hmemEnd, hbaseEnd⟩ :=
    valueArms_ifEnd545 (calls := stage2NoEventCalls gap) (K := K) (mem := r.mem)
      (σ := σ) (b := K.b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
      (tk0 := BitVec.ofNat 64 tok0) (tm0 := BitVec.ofNat 64 tm0)
      (pn := bw + BitVec.ofNat 64 7) (q := q) (s := S2)
      rfl rfl
      (by decide : phiIncoming "cleanup491" valueArmsIfEnd545Incoming =
        some (.reg "%add489"))
      (evalOperand_reg_of S2.env S2 "%add489"
        (.int 64 (bw + BitVec.ofNat 64 7)) (by dsimp only [S2, S1]; cells_lk))
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      (by dsimp only [S2, S1]; cells_lk)
      hqle hcond63 rfl
      (by simpa only [S2, S1, stateAt] using hbytes) hws hSb2
  refine ⟨s', 2 + j, by omega, ?_, hafter,
    by simpa only [S2, S1, stateAt] using hmemEnd, hbaseEnd⟩
  intro k
  rw [show 2 + j + k = 1 + (1 + (j + k)) from by omega,
    runFuel_jump_prefix hs1, runFuel_jump_prefix hs2]
  exact hrun k

/-! ### The number event at the model -/

/-- **The model's accepted number word.** -/
theorem valueArms_numFast_model {gap : Calls} {K : Stage2NoEventWalkCarry} {mem : Mem}
    {s : State} {lane q : Nat} {d : Decimal}
    (hInv : Stage2NoEventWalkInv K mem s) (hlaneq : lane ≤ q) (hqle : q ≤ K.n)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some d.lexeme.data.toList)
    (hwf : d.wellFormed) (hscan : (numLexScan d.lexeme.data.toList).2 = true) :
    stage2NoEventCalls gap "num_fast_el1"
      [.ptr (K.b + lane), .int 64 (BitVec.ofNat 64 (q - lane)), .ptr K.d,
        .ptr (K.next0 + 24)]
      (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) s.next =
    some { ret := .int 32 (BitVec.ofNat 32 1),
           mem := writeBytes (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8))
             K.d (wordBytes 8 (strtodSpec d).toBits), next := s.next } := by
  have hmemw : (K.b, K.n + stage2ReadTail) ∈
      stage2NoEventRegions K.b K.n K.ep K.nep K.xp K.nxp K.scratch K.scratchcap
        K.tokensOut K.valuesOut K.sumOut K.err := by
    simp [stage2NoEventRegions]
  have hbnd := hInv.watermark (K.b, K.n + stage2ReadTail) hmemw
  have hbound : (K.b + lane) + (q - lane) ≤ K.next0 + 24 := by
    have h1 : K.b + lane + (q - lane) = K.b + q := by
      rw [Nat.add_assoc, Nat.add_sub_of_le hlaneq]
    have h2 : K.b + q ≤ K.next0 := by omega
    omega
  have hread : readBytes (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8))
      (K.b + lane) (q - lane) = some d.lexeme.data.toList := by
    rw [readBytes_writeBytes_below s.mem (natToBytes 0 8) (q - lane) (K.b + lane)
      (K.next0 + 24) hbound]
    exact hlex
  have hreadn : readBytes (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8))
      (K.b + lane) (BitVec.ofNat 64 (q - lane)).toNat = some d.lexeme.data.toList := by
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le q lane)
        (Nat.lt_of_le_of_lt hqle hInv.nLt))]
    exact hread
  rw [valueArms_num_fast_calls]
  exact stage2NumFast_writes_strtodSpec hwf hreadn hscan

/-- **The arena bound is preserved by a number event.** -/
theorem valueArms_arenaBound_number (arena : List UInt8) (bits : Nat) :
    Stage2NoEventArenaBound arena [ConsumerEvent.number bits] := by
  intro e he htag _
  simp only [List.mem_singleton] at he
  subst he
  simp only [ConsumerEvent.number, stage2TagNum] at htag
  rcases htag with h | h <;> exact absurd h (by decide)

/-- **The number event appends to a trace.** -/
theorem valueArms_trace_number {K K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start stop : Nat} {d : Decimal}
    (hwf : d.wellFormed) (hstop : stop = start + d.lexeme.length)
    (hslice : (K.bs.drop start).take (stop - start) = d.lexeme.data.toList)
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + 1)
    (hterms : K'.terms = K.terms + (7 + (strtodSpec d).toBits)) :
    Stage2NoEventWalkTrace K' := by
  refine h.step (K' := K')
    (evs := [ConsumerEvent.number (strtodSpec d).toBits])
    (toks := [Token.number ⟨start, stop⟩]) ?_ ?_ hbs harena htok hterms
  · exact Stage2NoEvent.number (StrtodReader.reader_lexeme hwf) hstop hslice Stage2NoEvent.nil
  · exact valueArms_arenaBound_number K.arena _

/-! ### The number arm's export -/

/-- **The number arm, end to end, at the model.**  From `if.then471`'s entry to
`after_value`'s entry: the staged call's accepted answer (the model writes
`strtodSpec`'s bits into `%d`), the merge's `+1`/`+7+bits` stores, the
separator skip, and the trace's one number event.  The run is inside
`3 + 5 * (cond - q)`, this slice's own count; the preceding provider slice's count is separate, and this is not the class price. -/
theorem stage2NoEventWalkValueNumber {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32} {d : Decimal}
    {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.then471")
    (hd : lookupName s.env "%d" = some (.ptr K.d))
    (hei : lookupName s.env "%ei" = some (.ptr (K.next0 + 24)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hqleK : q ≤ K.n)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some d.lexeme.data.toList)
    (hwf : d.wellFormed) (hscan : (numLexScan d.lexeme.data.toList).2 = true)
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond →
      readByte
        (writeBytes (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) K.d
          (wordBytes 8 (strtodSpec d).toBits)) (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + d.lexeme.length)
    (hslice : (K.bs.drop lane).take (q - lane) = d.lexeme.data.toList)
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 3 + 5 * (cond - q) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        ((BitVec.ofNat 64 (strtodSpec d).toBits + BitVec.ofNat 64 7) +
          BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + (7 + (strtodSpec d).toBits) ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  let bits : Nat := (strtodSpec d).toBits
  let K' : Stage2NoEventWalkCarry :=
    { K with tok := K.tok + 1, terms := K.terms + (7 + (strtodSpec d).toBits) }
  let rmem : Mem := writeBytes
    (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) K.d (wordBytes 8 bits)
  let rout : CallOutcome :=
    { ret := .int 32 (BitVec.ofNat 32 1), mem := rmem, next := s.next }
  have hr : stage2NoEventCalls gap "num_fast_el1"
      [.ptr (K.b + lane), .int 64 (BitVec.ofNat 64 (q - lane)), .ptr K.d,
        .ptr (K.next0 + 24)]
      (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) s.next = some rout :=
    valueArms_numFast_model hInv hlaneq hqleK hlex hwf hscan
  have hload : readBytes rmem K.d 8 = some (natToBytes (BitVec.ofNat 64 bits).toNat 8) := by
    have h := readBytes_writeBytes_same
      (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) (wordBytes 8 bits) (addr := K.d)
    rw [show (wordBytes 8 bits).length = 8 from by rw [wordBytes]; exact natToBytes_length bits 8] at h
    rw [h, ← valueArms_wordBytes_natToBytes bits]
  obtain ⟨s', j, hj, hrun, hafter, hmemEnd, hbaseEnd⟩ :=
    valueArms_numberRoute (gap := gap) (K := K') (tok0 := K.tok) (tm0 := K.terms)
      (fr := frb.toNat) (sp := spb.toNat)
      hpc (by simpa only [K'] using hd) (by simpa only [K'] using hei) hee hidx
      (by simpa only [K'] using harr) hlaneq hq64 (by simpa only [K'] using hr)
      (by rfl) (by simpa only [K'] using hload)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hframe)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hsp) hk
      (by simpa only [K'] using halen) (by simpa only [K'] using harena)
      (by simpa only [K'] using hb) htk0 htm0 hcond hqle hcond63
      (by simpa only [K', rout, rmem, bits] using hbytes) hws
      hbase
  have hK'tok : K'.tok = K.tok + 1 := rfl
  have hK'terms : K'.terms = K.terms + (7 + (strtodSpec d).toBits) := rfl
  have hK'bs : K'.bs = K.bs := rfl
  have hK'arena : K'.arena = K.arena := rfl
  have hInvAt : Stage2NoEventWalkInv K mem s' := by
    have hkm : ∀ k, k < (natToBytes 0 8).length → inRegions
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]) (K.next0 + 24 + k) := by
      intro k hk
      have hk8 : k < 8 := by rwa [natToBytes_length] at hk
      have hstat := hInv.nextEnd_static
      simp only [stage2BootstrapExtent] at hstat
      exact ⟨(K.next0, K.nextEnd - K.next0), by simp, by omega, by omega⟩
    have hkd : ∀ k, k < (wordBytes 8 bits).length → inRegions
        (stage2NoEventRunRegions K.scratch K.scratchcap K.stk K.e K.c K.d ++
          [(K.next0, K.nextEnd - K.next0)]) (K.d + k) := by
      intro k hk
      have hk8 : k < 8 := by rwa [wordBytes, natToBytes_length] at hk
      refine ⟨(K.d, stage2NoEventNumExtent), ?_, by omega, ?_⟩
      · simp only [stage2NoEventRunRegions, stage2NoEventStagedRegions]
        simp
      · simp only [stage2NoEventNumExtent]; omega
    have h1 := Stage2NoEventWalkInv.stack_write (h := hInv)
      (a := K.next0 + 24) (bs := natToBytes 0 8) hkm
    have h2 := Stage2NoEventWalkInv.stack_write (h := h1)
      (a := K.d) (bs := wordBytes 8 bits) hkd
    exact Stage2NoEventWalkInv.mem_congr h2 (s' := s')
      (by simpa only [rmem, rout] using hmemEnd)
  refine ⟨s', j, K', by omega, hrun, hafter, ?_, hK'tok, hK'terms, hK'bs, hK'arena,
    rfl, rfl, rfl, rfl, rfl,
    valueArms_trace_number htrace hwf hstop hslice hK'bs hK'arena hK'tok hK'terms,
    frb.isLt, (fun h => hfrNe (BitVec.eq_of_toNat_eq (by simp [h]))),
    spb.isLt, (fun h => hspNe (BitVec.eq_of_toNat_eq (by simp [h]))), hbaseEnd⟩
  exact Stage2NoEventWalkInv.count (h := hInvAt) (t := 1)
    (c := 7 + (strtodSpec d).toBits) (by omega)

/-! ### The literal dispatch to `if.end519` -/

/-- **`true`**: `if.else495` → `NodeBlock72` → `NodeBlock70` → `LeafBlock68` →
`if.end519`, in four steps. -/
theorem valueArms_literalDispatchTrue {calls : Calls} {s : State}
    {K : Stage2NoEventWalkCarry}
    {ee idx p b : Nat} {cd tk tm : BitVec 64} {fr : BitVec 8} {spv : BitVec 32}
    {knext alen arena : BitVec 64}
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 116)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr p))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hcond : lookupName s.env "%cond" = some (.int 64 cd))
    (htk : lookupName s.env "%tokens.0.lcssa1073" = some (.int 64 tk))
    (htm : lookupName s.env "%terms.0.lcssa1079" = some (.int 64 tm))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spv))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 knext))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 4 ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      s'.pc = "if.end519" ∧ s'.pre = some "LeafBlock68" ∧ s'.mem = s.mem ∧
      lookupName s'.env "%ee.1" = some (.int 64 ee) ∧
      lookupName s'.env "%idxprom.lcssa" = some (.int 64 idx) ∧
      lookupName s'.env "%arrayidx6.le1046" = some (.ptr p) ∧
      lookupName s'.env "%b" = some (.ptr b) ∧
      lookupName s'.env "%cond" = some (.int 64 cd) ∧
      lookupName s'.env "%tokens.0.lcssa1073" = some (.int 64 tk) ∧
      lookupName s'.env "%terms.0.lcssa1079" = some (.int 64 tm) ∧
      lookupName s'.env "%frame.0.lcssa1097" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1091.wide" = some (.int 32 spv) ∧
      lookupName s'.env "%inc.lcssa" = some (.int 64 knext) ∧
      lookupName s'.env "%alen.0.ph1405" = some (.int 64 alen) ∧
      lookupName s'.env "%arena.0.ph1406" = some (.int 64 arena) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  let S1 : State := stateAt s.env { s with pc := "NodeBlock72", pre := some "if.else495" }
  have hSb1 : Stage2NoEventWalkBaseLookups K S1 :=
    valueArms_baseLookups_env (cs := []) (s0 := s) hbase (by rfl) (by rfl)
  have hs1 : step calls stage2NoEventBody s = .jump S1 := by
    rw [← valueArms_stateAt_self s]
    simpa [S1] using valueArms_step_if_else495 calls s.env s hpc
  let S2 : State := stateAt
    (("%Pivot73", .int 1 0) :: S1.env)
    { S1 with pc := "NodeBlock70", pre := some "NodeBlock72" }
  have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
    valueArms_baseLookups_env (cs := [("%Pivot73", .int 1 0)]) (s0 := S1) hSb1
      (by rfl) (by rfl)
  have h73 : evalICmp .slt (BitVec.ofNat 8 116) (BitVec.ofNat 8 110) = 0 := by decide
  have hs2 : step calls stage2NoEventBody S1 = .jump S2 := by
    rw [← valueArms_stateAt_self S1]
    rw [valueArms_step_nodeBlock72 calls S1.env S1 rfl (by dsimp only [S1]; cells_lk)]
    simp only [S2]
    rw [h73, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
  let S3 : State := stateAt
    (("%Pivot71", .int 1 0) :: S2.env)
    { S2 with pc := "LeafBlock68", pre := some "NodeBlock70" }
  have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
    valueArms_baseLookups_env (cs := [("%Pivot71", .int 1 0)]) (s0 := S2) hSb2
      (by rfl) (by rfl)
  have h71 : evalICmp .slt (BitVec.ofNat 8 116) (BitVec.ofNat 8 116) = 0 :=
    valueArms_slt_self _
  have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
    rw [← valueArms_stateAt_self S2]
    rw [valueArms_step_nodeBlock70 calls S2.env S2 rfl (by dsimp only [S2, S1]; cells_lk)]
    simp only [S3]
    rw [h71, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
  let S4 : State := stateAt
    (("%SwitchLeaf69", .int 1 1) :: S3.env)
    { S3 with pc := "if.end519", pre := some "LeafBlock68" }
  have hSb4 : Stage2NoEventWalkBaseLookups K S4 :=
    valueArms_baseLookups_env (cs := [("%SwitchLeaf69", .int 1 1)]) (s0 := S3) hSb3
      (by rfl) (by rfl)
  have h69 : evalICmp .eq (BitVec.ofNat 8 116) (BitVec.ofNat 8 116) = 1 := by
    simp [evalICmp]
  have hs4 : step calls stage2NoEventBody S3 = .jump S4 := by
    rw [← valueArms_stateAt_self S3]
    rw [valueArms_step_leafBlock68 calls S3.env S3 rfl
      (by dsimp only [S3, S2, S1]; cells_lk)]
    simp only [S4]
    rw [h69, if_pos rfl]
  refine ⟨S4, 4, by omega, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hSb4⟩
  · intro k
    rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
      runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3,
      runFuel_jump_prefix hs4]
  all_goals (dsimp only [S4, S3, S2, S1]; cells_lk)

/-- **`null`**: five steps to `if.end519` through `LeafBlock66`/`if.then509`. -/
theorem valueArms_literalDispatchNull {calls : Calls} {s : State}
    {K : Stage2NoEventWalkCarry}
    {ee idx p b : Nat} {cd tk tm : BitVec 64} {fr : BitVec 8} {spv : BitVec 32}
    {knext alen arena : BitVec 64}
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 110)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr p))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hcond : lookupName s.env "%cond" = some (.int 64 cd))
    (htk : lookupName s.env "%tokens.0.lcssa1073" = some (.int 64 tk))
    (htm : lookupName s.env "%terms.0.lcssa1079" = some (.int 64 tm))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spv))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 knext))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 5 ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      s'.pc = "if.end519" ∧ s'.pre = some "if.then509" ∧ s'.mem = s.mem ∧
      lookupName s'.env "%ee.1" = some (.int 64 ee) ∧
      lookupName s'.env "%idxprom.lcssa" = some (.int 64 idx) ∧
      lookupName s'.env "%arrayidx6.le1046" = some (.ptr p) ∧
      lookupName s'.env "%b" = some (.ptr b) ∧
      lookupName s'.env "%cond" = some (.int 64 cd) ∧
      lookupName s'.env "%tokens.0.lcssa1073" = some (.int 64 tk) ∧
      lookupName s'.env "%terms.0.lcssa1079" = some (.int 64 tm) ∧
      lookupName s'.env "%frame.0.lcssa1097" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1091.wide" = some (.int 32 spv) ∧
      lookupName s'.env "%inc.lcssa" = some (.int 64 knext) ∧
      lookupName s'.env "%alen.0.ph1405" = some (.int 64 alen) ∧
      lookupName s'.env "%arena.0.ph1406" = some (.int 64 arena) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  let S1 : State := stateAt s.env { s with pc := "NodeBlock72", pre := some "if.else495" }
  have hSb1 : Stage2NoEventWalkBaseLookups K S1 :=
    valueArms_baseLookups_env (cs := []) (s0 := s) hbase (by rfl) (by rfl)
  have hs1 : step calls stage2NoEventBody s = .jump S1 := by
    rw [← valueArms_stateAt_self s]
    simpa [S1] using valueArms_step_if_else495 calls s.env s hpc
  let S2 : State := stateAt
    (("%Pivot73", .int 1 0) :: S1.env)
    { S1 with pc := "NodeBlock70", pre := some "NodeBlock72" }
  have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
    valueArms_baseLookups_env (cs := [("%Pivot73", .int 1 0)]) (s0 := S1) hSb1
      (by rfl) (by rfl)
  have h73 : evalICmp .slt (BitVec.ofNat 8 110) (BitVec.ofNat 8 110) = 0 :=
    valueArms_slt_self _
  have hs2 : step calls stage2NoEventBody S1 = .jump S2 := by
    rw [← valueArms_stateAt_self S1]
    rw [valueArms_step_nodeBlock72 calls S1.env S1 rfl (by dsimp only [S1]; cells_lk)]
    simp only [S2]
    rw [h73, if_neg (by decide : ¬ ((0 : BitVec 1) = 1))]
  let S3 : State := stateAt
    (("%Pivot71", .int 1 1) :: S2.env)
    { S2 with pc := "LeafBlock66", pre := some "NodeBlock70" }
  have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
    valueArms_baseLookups_env (cs := [("%Pivot71", .int 1 1)]) (s0 := S2) hSb2
      (by rfl) (by rfl)
  have h71 : evalICmp .slt (BitVec.ofNat 8 110) (BitVec.ofNat 8 116) = 1 := by decide
  have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
    rw [← valueArms_stateAt_self S2]
    rw [valueArms_step_nodeBlock70 calls S2.env S2 rfl (by dsimp only [S2, S1]; cells_lk)]
    simp only [S3]
    rw [h71, if_pos rfl]
  let S4 : State := stateAt
    (("%SwitchLeaf67", .int 1 1) :: S3.env)
    { S3 with pc := "if.then509", pre := some "LeafBlock66" }
  have hSb4 : Stage2NoEventWalkBaseLookups K S4 :=
    valueArms_baseLookups_env (cs := [("%SwitchLeaf67", .int 1 1)]) (s0 := S3) hSb3
      (by rfl) (by rfl)
  have h67 : evalICmp .eq (BitVec.ofNat 8 110) (BitVec.ofNat 8 110) = 1 := by
    simp [evalICmp]
  have hs4 : step calls stage2NoEventBody S3 = .jump S4 := by
    rw [← valueArms_stateAt_self S3]
    rw [valueArms_step_leafBlock66 calls S3.env S3 rfl
      (by dsimp only [S3, S2, S1]; cells_lk)]
    simp only [S4]
    rw [h67, if_pos rfl]
  let S5 : State := stateAt S4.env
    { S4 with pc := "if.end519", pre := some "if.then509" }
  have hSb5 : Stage2NoEventWalkBaseLookups K S5 :=
    valueArms_baseLookups_env (cs := []) (s0 := S4) hSb4 (by rfl) (by rfl)
  have hs5 : step calls stage2NoEventBody S4 = .jump S5 := by
    rw [← valueArms_stateAt_self S4]
    simpa [S5] using valueArms_step_if_then509 calls S4.env S4 rfl
  refine ⟨S5, 5, by omega, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hSb5⟩
  · intro k
    rw [show 5 + k = 1 + (1 + (1 + (1 + (1 + k)))) from by omega,
      runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3,
      runFuel_jump_prefix hs4, runFuel_jump_prefix hs5]
  all_goals (dsimp only [S5, S4, S3, S2, S1, stateAt]; cells_lk)

/-- **`false`**: four steps to `if.end519` through `LeafBlock64`/`if.then504`. -/
theorem valueArms_literalDispatchFalse {calls : Calls} {s : State}
    {K : Stage2NoEventWalkCarry}
    {ee idx p b : Nat} {cd tk tm : BitVec 64} {fr : BitVec 8} {spv : BitVec 32}
    {knext alen arena : BitVec 64}
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 102)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 ee))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 idx))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr p))
    (hb : lookupName s.env "%b" = some (.ptr b))
    (hcond : lookupName s.env "%cond" = some (.int 64 cd))
    (htk : lookupName s.env "%tokens.0.lcssa1073" = some (.int 64 tk))
    (htm : lookupName s.env "%terms.0.lcssa1079" = some (.int 64 tm))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 fr))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spv))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 knext))
    (halen : lookupName s.env "%alen.0.ph1405" = some (.int 64 alen))
    (harena : lookupName s.env "%arena.0.ph1406" = some (.int 64 arena))
    (hbase : Stage2NoEventWalkBaseLookups K s) :
    ∃ s' j, j ≤ 4 ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody s =
        runFuel calls k stage2NoEventBody s') ∧
      s'.pc = "if.end519" ∧ s'.pre = some "if.then504" ∧ s'.mem = s.mem ∧
      lookupName s'.env "%ee.1" = some (.int 64 ee) ∧
      lookupName s'.env "%idxprom.lcssa" = some (.int 64 idx) ∧
      lookupName s'.env "%arrayidx6.le1046" = some (.ptr p) ∧
      lookupName s'.env "%b" = some (.ptr b) ∧
      lookupName s'.env "%cond" = some (.int 64 cd) ∧
      lookupName s'.env "%tokens.0.lcssa1073" = some (.int 64 tk) ∧
      lookupName s'.env "%terms.0.lcssa1079" = some (.int 64 tm) ∧
      lookupName s'.env "%frame.0.lcssa1097" = some (.int 8 fr) ∧
      lookupName s'.env "%sp.0.lcssa1091.wide" = some (.int 32 spv) ∧
      lookupName s'.env "%inc.lcssa" = some (.int 64 knext) ∧
      lookupName s'.env "%alen.0.ph1405" = some (.int 64 alen) ∧
      lookupName s'.env "%arena.0.ph1406" = some (.int 64 arena) ∧
      Stage2NoEventWalkBaseLookups K s' := by
  let S1 : State := stateAt s.env { s with pc := "NodeBlock72", pre := some "if.else495" }
  have hSb1 : Stage2NoEventWalkBaseLookups K S1 :=
    valueArms_baseLookups_env (cs := []) (s0 := s) hbase (by rfl) (by rfl)
  have hs1 : step calls stage2NoEventBody s = .jump S1 := by
    rw [← valueArms_stateAt_self s]
    simpa [S1] using valueArms_step_if_else495 calls s.env s hpc
  let S2 : State := stateAt
    (("%Pivot73", .int 1 1) :: S1.env)
    { S1 with pc := "LeafBlock64", pre := some "NodeBlock72" }
  have hSb2 : Stage2NoEventWalkBaseLookups K S2 :=
    valueArms_baseLookups_env (cs := [("%Pivot73", .int 1 1)]) (s0 := S1) hSb1
      (by rfl) (by rfl)
  have h73 : evalICmp .slt (BitVec.ofNat 8 102) (BitVec.ofNat 8 110) = 1 := by decide
  have hs2 : step calls stage2NoEventBody S1 = .jump S2 := by
    rw [← valueArms_stateAt_self S1]
    rw [valueArms_step_nodeBlock72 calls S1.env S1 rfl (by dsimp only [S1]; cells_lk)]
    simp only [S2]
    rw [h73, if_pos rfl]
  let S3 : State := stateAt
    (("%SwitchLeaf65", .int 1 1) :: S2.env)
    { S2 with pc := "if.then504", pre := some "LeafBlock64" }
  have hSb3 : Stage2NoEventWalkBaseLookups K S3 :=
    valueArms_baseLookups_env (cs := [("%SwitchLeaf65", .int 1 1)]) (s0 := S2) hSb2
      (by rfl) (by rfl)
  have h65 : evalICmp .eq (BitVec.ofNat 8 102) (BitVec.ofNat 8 102) = 1 := by
    simp [evalICmp]
  have hs3 : step calls stage2NoEventBody S2 = .jump S3 := by
    rw [← valueArms_stateAt_self S2]
    rw [valueArms_step_leafBlock64 calls S2.env S2 rfl
      (by dsimp only [S2, S1]; cells_lk)]
    simp only [S3]
    rw [h65, if_pos rfl]
  let S4 : State := stateAt S3.env
    { S3 with pc := "if.end519", pre := some "if.then504" }
  have hSb4 : Stage2NoEventWalkBaseLookups K S4 :=
    valueArms_baseLookups_env (cs := []) (s0 := S3) hSb3 (by rfl) (by rfl)
  have hs4 : step calls stage2NoEventBody S3 = .jump S4 := by
    rw [← valueArms_stateAt_self S3]
    simpa [S4] using valueArms_step_if_then504 calls S3.env S3 rfl
  refine ⟨S4, 4, by omega, ?_, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hSb4⟩
  · intro k
    rw [show 4 + k = 1 + (1 + (1 + (1 + k))) from by omega,
      runFuel_jump_prefix hs1, runFuel_jump_prefix hs2, runFuel_jump_prefix hs3,
      runFuel_jump_prefix hs4]
  all_goals (dsimp only [S4, S3, S2, S1, stateAt]; cells_lk)

/-! ### The literal event's trace steps -/

/-- **A literal kind event appends to a trace.** -/
theorem valueArms_trace_kind {K K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {tag : Nat} {tok : Token}
    (htag : tag = 8 ∨ tag = 9 ∨ tag = 10)
    (hstep : Stage2NoEvent K.bs K.arena [ConsumerEvent.kind tag] [tok])
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + 1) (hterms : K'.terms = K.terms + tag) :
    Stage2NoEventWalkTrace K' := by
  refine h.step (K' := K') hstep ?_ hbs harena htok hterms
  intro e he htag' _
  simp only [List.mem_singleton] at he
  subst he
  simp [ConsumerEvent.kind, EventRecord.tagKey, EventRecord.tagStr] at htag'
  rcases htag with h | h | h <;> subst h <;> omega

/-- The arena bound of one literal event. -/
theorem valueArms_arenaBound_kind (arena : List UInt8) (tag : Nat)
    (htag : tag = 8 ∨ tag = 9 ∨ tag = 10) :
    Stage2NoEventArenaBound arena [ConsumerEvent.kind tag] := by
  intro e he htag' _
  simp only [List.mem_singleton] at he
  subst he
  simp [ConsumerEvent.kind, EventRecord.tagKey, EventRecord.tagStr] at htag'
  rcases htag with h | h | h <;> subst h <;> omega

/-- **`true`'s trace step**, terms `8`. -/
theorem valueArms_trace_trueTag {K K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start stop : Nat}
    (hspan : stop = start + 4)
    (hbytes : (K.bs.drop start).take 4 = [0x74, 0x72, 0x75, 0x65])
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + 1) (hterms : K'.terms = K.terms + 8) :
    Stage2NoEventWalkTrace K' := by
  refine valueArms_trace_kind h (tag := 8) (tok := Token.bool true ⟨start, stop⟩)
    (Or.inl rfl)
    (hstep := Stage2NoEvent.trueTag (s := ⟨start, stop⟩) hbytes ?_ Stage2NoEvent.nil)
    hbs harena htok ?_
  · simpa using hspan
  · simpa using hterms

/-- **`false`'s trace step**, terms `9`. -/
theorem valueArms_trace_falseTag {K K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start stop : Nat}
    (hspan : stop = start + 5)
    (hbytes : (K.bs.drop start).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + 1) (hterms : K'.terms = K.terms + 9) :
    Stage2NoEventWalkTrace K' := by
  refine valueArms_trace_kind h (tag := 9) (tok := Token.bool false ⟨start, stop⟩)
    (Or.inr (Or.inl rfl))
    (hstep := Stage2NoEvent.falseTag (s := ⟨start, stop⟩) hbytes ?_ Stage2NoEvent.nil)
    hbs harena htok ?_
  · simpa using hspan
  · simpa using hterms

/-- **`null`'s trace step**, terms `10`. -/
theorem valueArms_trace_nullTag {K K' : Stage2NoEventWalkCarry}
    (h : Stage2NoEventWalkTrace K) {start stop : Nat}
    (hspan : stop = start + 4)
    (hbytes : (K.bs.drop start).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
    (hbs : K'.bs = K.bs) (harena : K'.arena = K.arena)
    (htok : K'.tok = K.tok + 1) (hterms : K'.terms = K.terms + 10) :
    Stage2NoEventWalkTrace K' := by
  refine valueArms_trace_kind h (tag := 10) (tok := Token.null ⟨start, stop⟩)
    (Or.inr (Or.inr rfl))
    (hstep := Stage2NoEvent.nullTag (s := ⟨start, stop⟩) hbytes ?_ Stage2NoEvent.nil)
    hbs harena htok ?_
  · simpa using hspan
  · simpa using hterms

#print axioms valueArms_literalDispatchTrue
#print axioms valueArms_trace_kind
#print axioms valueArms_trace_trueTag
#print axioms valueArms_trace_falseTag
#print axioms valueArms_trace_nullTag

/-! ### The literal merge and the separator -/

def valueArmsLitLit : List (String × Operand) :=
  [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 435728179558)))),
   ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 1819047278)))),
   ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 1702195828))))]

def valueArmsLitSel : List (String × Operand) :=
  [("if.then504", (Operand.imm (.int 1 (BitVec.ofNat 1 0)))),
   ("if.then509", (Operand.imm (.int 1 (BitVec.ofNat 1 1)))),
   ("LeafBlock68", (Operand.imm (.int 1 (BitVec.ofNat 1 1))))]

def valueArmsLitLn : List (String × Operand) :=
  [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 5)))),
   ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 4)))),
   ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 4))))]

def valueArmsLitTag : List (String × Operand) :=
  [("if.then504", (Operand.imm (.int 64 (BitVec.ofNat 64 9)))),
   ("if.then509", (Operand.imm (.int 64 (BitVec.ofNat 64 10)))),
   ("LeafBlock68", (Operand.imm (.int 64 (BitVec.ofNat 64 8))))]

/-- **The literal chain and the merge to `after_value`.**  From `if.end519`'s
entry: the pinned compare chain's accepting run, then `if.end545`'s `%add489.pn`
selection at the literal's tag, its count stores, and the separator loop. -/
theorem valueArms_literalAfter {calls : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond fr sp knext : Nat}
    {lit tagVec : BitVec 64} {ln : Nat} {b : BitVec 1} {qbytes : List UInt8}
    {tok0 tm0 : Nat} {S : State} {p : String}
    (hpc : S.pc = "if.end519") (hpre : S.pre = some p)
    (hincLit : phiIncoming p valueArmsLitLit = some (.imm (.int 64 lit)))
    (hincB : phiIncoming p valueArmsLitSel = some (.imm (.int 1 b)))
    (hincLn : phiIncoming p valueArmsLitLn =
      some (.imm (.int 64 (BitVec.ofNat 64 ln))))
    (hincTag : phiIncoming p valueArmsLitTag = some (.imm (.int 64 tagVec)))
    (hee : lookupName S.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName S.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName S.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hq : readBytes S.mem (K.b + lane) (q - lane) = some qbytes)
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hwidth : (BitVec.ofNat 64 ln = BitVec.ofNat 64 4 ∧ b = 1) ∨
              (BitVec.ofNat 64 ln = BitVec.ofNat 64 5 ∧ b = 0))
    (hval : neLitCheck qbytes (litBytes lit (BitVec.ofNat 64 ln).toNat) = none)
    (hb : lookupName S.env "%b" = some (.ptr K.b))
    (hcond : lookupName S.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName S.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 tok0)))
    (htm0 : lookupName S.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 tm0)))
    (hframe : lookupName S.env "%frame.0.lcssa1097" =
      some (.int 8 (BitVec.ofNat 8 fr)))
    (hsp : lookupName S.env "%sp.0.lcssa1091.wide" =
      some (.int 32 (BitVec.ofNat 32 sp)))
    (hk : lookupName S.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName S.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName S.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63) (hmem : S.mem = mem)
    (hbytes : ∀ i, i < cond → readByte mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hbase : Stage2NoEventWalkBaseLookups K S) :
    ∃ s' j, j ≤ 14 + 5 * (cond - q) ∧
      (∀ k, runFuel calls (j + k) stage2NoEventBody S =
        runFuel calls k stage2NoEventBody s') ∧
      valueArmsAfter K fr sp knext (BitVec.ofNat 64 tok0 + BitVec.ofNat 64 1)
        (tagVec + BitVec.ofNat 64 tm0) s' ∧ s'.mem = S.mem ∧
      Stage2NoEventWalkBaseLookups K s' := by
  have hn : q - lane < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.sub_le q lane) hq64
  have hsub := valueArms_sub_ofNat hlaneq hq64
  obtain ⟨e, jc, hjc, hemem, hacc, htag0, hpres, hrunC⟩ :=
    stage2NoEventLitChain_accept calls S.env S p hpc hpre hincLit hincB hincLn
      hincTag hee hidx hn hsub harr hq hwidth hval
  obtain ⟨hacpc, hacpre⟩ := hacc
  have hbaseE : Stage2NoEventWalkBaseLookups K e := by
    intro n v hv
    have hbn : n ∈ stage2NoEventWalkBaseNames := by
      have hm : n ∈ (stage2NoEventWalkBaseValues K).map (·.1) := List.mem_map_of_mem hv
      rwa [stage2NoEventWalkBaseValues_names] at hm
    rw [hpres n (valueArms_baseNames_notin (l := litAcceptWritten) (by decide) n hbn)]
    exact hbase n v hv
  obtain ⟨s', jL, hjL, hrunL, hafter, hmemL, hbaseL⟩ :=
    valueArms_ifEnd545 (calls := calls) (K := K) (mem := mem) (σ := σ)
      (b := K.b) (cond := cond) (fr := fr) (sp := sp) (knext := knext)
      (tk0 := BitVec.ofNat 64 tok0) (tm0 := BitVec.ofNat 64 tm0)
      (pn := tagVec) (q := q) (s := e)
      hacpc hacpre (by decide)
      (evalOperand_reg_of e.env e "%tag.0" (.int 64 tagVec) htag0)
      (by rw [hpres "%tokens.0.lcssa1073" (by decide)]; exact htk0)
      (by rw [hpres "%terms.0.lcssa1079" (by decide)]; exact htm0)
      (by rw [hpres "%ee.1" (by decide)]; exact hee)
      (by rw [hpres "%cond" (by decide)]; exact hcond)
      (by rw [hpres "%b" (by decide)]; exact hb)
      (by rw [hpres "%frame.0.lcssa1097" (by decide)]; exact hframe)
      (by rw [hpres "%sp.0.lcssa1091.wide" (by decide)]; exact hsp)
      (by rw [hpres "%inc.lcssa" (by decide)]; exact hk)
      (by rw [hpres "%alen.0.ph1405" (by decide)]; exact halen)
      (by rw [hpres "%arena.0.ph1406" (by decide)]; exact harena)
      hqle hcond63 (hemem.trans hmem) hbytes hws hbaseE
  refine ⟨s', jc + jL, by omega, ?_, hafter, hmemL.trans hemem, hbaseL⟩
  intro k
  rw [← valueArms_stateAt_self S]
  rw [show jc + jL + k = jc + (jL + k) from by omega, hrunC (jL + k)]
  exact hrunL k

/-! ### The literal arm's exports -/

/-- **`true`**, end to end: the dispatch, the chain, the merge at tag `8`, the
separator skip, and the trace's one `true` event. -/
theorem stage2NoEventWalkValueLiteralTrue {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 116)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1702195828) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x74, 0x72, 0x75, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - q) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 8 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 8 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨S, jd, hjd, hrunD, hpcS, hpreS, hmemS, heeS, hidxS, harrS, hbS, hcdS,
    htkS, htmS, hfrS, hspS, hkS, halS, harS, hbaseS⟩ :=
    valueArms_literalDispatchTrue (calls := stage2NoEventCalls gap) (K := K)
      hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hbase
  let K' : Stage2NoEventWalkCarry := { K with tok := K.tok + 1, terms := K.terms + 8 }
  obtain ⟨s', j, hj, hrunL, hafter, hmemL, hbaseL⟩ :=
    valueArms_literalAfter (calls := stage2NoEventCalls gap) (K := K')
      (mem := s.mem) (tok0 := K.tok) (tm0 := K.terms)
      (fr := frb.toNat) (sp := spb.toNat)
      (lit := BitVec.ofNat 64 1702195828) (tagVec := BitVec.ofNat 64 8)
      (ln := 4) (b := 1) hpcS hpreS (by decide) (by decide) (by decide) (by decide)
      heeS hidxS (by simpa only [K'] using harrS) (by simpa only [K', hmemS] using hlex)
      hlaneq hq64 hq4
      (Or.inl ⟨rfl, rfl⟩)
      (by
        show neLitCheck qbytes
          (litBytes (BitVec.ofNat 64 1702195828) (BitVec.ofNat 64 4).toNat) = none
        rw [show (BitVec.ofNat 64 4).toNat = 4 from by decide]
        exact hval)
      (by simpa only [K'] using hbS) hcdS htkS htmS
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hfrS)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hspS) hkS
      (by simpa only [K'] using halS) (by simpa only [K'] using harS)
      hqle hcond63 hmemS hbytes hws hbaseS
  refine ⟨s', jd + j, K', by omega, ?_, hafter, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    valueArms_trace_trueTag htrace hstop hslice rfl rfl rfl rfl,
    frb.isLt, (fun h => hfrNe (BitVec.eq_of_toNat_eq (by simp [h]))),
    spb.isLt, (fun h => hspNe (BitVec.eq_of_toNat_eq (by simp [h]))), hbaseL⟩
  · intro k
    rw [show jd + j + k = jd + (j + k) from by omega, hrunD (j + k)]
    exact hrunL k
  · exact (Stage2NoEventWalkInv.count (h := hInv) (t := 1) (c := 8) (by omega)).mem_congr
      (hmemL.trans hmemS)
/-- **`null`**, end to end: dispatch through `LeafBlock66`/`if.then509`, the chain, the merge at tag `10`, the separator skip, and the `null` event. -/
theorem stage2NoEventWalkValueLiteralNull {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 110)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1819047278) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 19 + 5 * (cond - q) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 10 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 10 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨S, jd, hjd, hrunD, hpcS, hpreS, hmemS, heeS, hidxS, harrS, hbS, hcdS,
    htkS, htmS, hfrS, hspS, hkS, halS, harS, hbaseS⟩ :=
    valueArms_literalDispatchNull (calls := stage2NoEventCalls gap) (K := K)
      hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hbase
  let K' : Stage2NoEventWalkCarry := { K with tok := K.tok + 1, terms := K.terms + 10 }
  obtain ⟨s', j, hj, hrunL, hafter, hmemL, hbaseL⟩ :=
    valueArms_literalAfter (calls := stage2NoEventCalls gap) (K := K')
      (mem := s.mem) (tok0 := K.tok) (tm0 := K.terms)
      (fr := frb.toNat) (sp := spb.toNat)
      (lit := BitVec.ofNat 64 1819047278) (tagVec := BitVec.ofNat 64 10)
      (ln := 4) (b := 1) hpcS hpreS (by decide) (by decide) (by decide) (by decide)
      heeS hidxS (by simpa only [K'] using harrS) (by simpa only [K', hmemS] using hlex)
      hlaneq hq64 hq4
      (Or.inl ⟨rfl, rfl⟩)
      (by
        show neLitCheck qbytes
          (litBytes (BitVec.ofNat 64 1819047278) (BitVec.ofNat 64 4).toNat) = none
        rw [show (BitVec.ofNat 64 4).toNat = 4 from by decide]
        exact hval)
      (by simpa only [K'] using hbS) hcdS htkS htmS
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hfrS)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hspS) hkS
      (by simpa only [K'] using halS) (by simpa only [K'] using harS)
      hqle hcond63 hmemS hbytes hws hbaseS
  refine ⟨s', jd + j, K', by omega, ?_, hafter, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    valueArms_trace_nullTag htrace hstop hslice rfl rfl rfl rfl,
    frb.isLt, (fun h => hfrNe (BitVec.eq_of_toNat_eq (by simp [h]))),
    spb.isLt, (fun h => hspNe (BitVec.eq_of_toNat_eq (by simp [h]))), hbaseL⟩
  · intro k
    rw [show jd + j + k = jd + (j + k) from by omega, hrunD (j + k)]
    exact hrunL k
  · exact (Stage2NoEventWalkInv.count (h := hInv) (t := 1) (c := 10) (by omega)).mem_congr
      (hmemL.trans hmemS)
/-- **`false`**, end to end: dispatch through `LeafBlock64`/`if.then504`, the chain, the merge at tag `9`, the separator skip, and the `false` event. -/
theorem stage2NoEventWalkValueLiteralFalse {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 102)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 435728179558) 5) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 5)
    (hslice : (K.bs.drop lane).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - q) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 9 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 9 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨S, jd, hjd, hrunD, hpcS, hpreS, hmemS, heeS, hidxS, harrS, hbS, hcdS,
    htkS, htmS, hfrS, hspS, hkS, halS, harS, hbaseS⟩ :=
    valueArms_literalDispatchFalse (calls := stage2NoEventCalls gap) (K := K)
      hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hbase
  let K' : Stage2NoEventWalkCarry := { K with tok := K.tok + 1, terms := K.terms + 9 }
  obtain ⟨s', j, hj, hrunL, hafter, hmemL, hbaseL⟩ :=
    valueArms_literalAfter (calls := stage2NoEventCalls gap) (K := K')
      (mem := s.mem) (tok0 := K.tok) (tm0 := K.terms)
      (fr := frb.toNat) (sp := spb.toNat)
      (lit := BitVec.ofNat 64 435728179558) (tagVec := BitVec.ofNat 64 9)
      (ln := 5) (b := 0) hpcS hpreS (by decide) (by decide) (by decide) (by decide)
      heeS hidxS (by simpa only [K'] using harrS) (by simpa only [K', hmemS] using hlex)
      hlaneq hq64 hq4
      (Or.inr ⟨rfl, rfl⟩)
      (by
        show neLitCheck qbytes
          (litBytes (BitVec.ofNat 64 435728179558) (BitVec.ofNat 64 5).toNat) = none
        rw [show (BitVec.ofNat 64 5).toNat = 5 from by decide]
        exact hval)
      (by simpa only [K'] using hbS) hcdS htkS htmS
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hfrS)
      (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hspS) hkS
      (by simpa only [K'] using halS) (by simpa only [K'] using harS)
      hqle hcond63 hmemS hbytes hws hbaseS
  refine ⟨s', jd + j, K', by omega, ?_, hafter, ?_, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl,
    valueArms_trace_falseTag htrace hstop hslice rfl rfl rfl rfl,
    frb.isLt, (fun h => hfrNe (BitVec.eq_of_toNat_eq (by simp [h]))),
    spb.isLt, (fun h => hspNe (BitVec.eq_of_toNat_eq (by simp [h]))), hbaseL⟩
  · intro k
    rw [show jd + j + k = jd + (j + k) from by omega, hrunD (j + k)]
    exact hrunL k
  · exact (Stage2NoEventWalkInv.count (h := hInv) (t := 1) (c := 9) (by omega)).mem_congr
      (hmemL.trans hmemS)
/-- **The class-level bound for the `stage2NoEventWalkValueNumber` slice.**  The number slice's price is `3 + 5 * (cond - q)`: two blocks at the arms entry, the merge, and the separator skip. This is the slice's own count, not the class price. -/
-- This weakens the slice's own price to `18 + 5 * (cond - lane)`.
-- It is not a composed class price and does not add the provider slice's count.
theorem stage2NoEventWalkValueNumber_classBound {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32} {d : Decimal}
    {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.then471")
    (hd : lookupName s.env "%d" = some (.ptr K.d))
    (hei : lookupName s.env "%ei" = some (.ptr (K.next0 + 24)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" = some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hqleK : q ≤ K.n)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some d.lexeme.data.toList)
    (hwf : d.wellFormed) (hscan : (numLexScan d.lexeme.data.toList).2 = true)
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond →
      readByte
        (writeBytes (writeBytes s.mem (K.next0 + 24) (natToBytes 0 8)) K.d
          (wordBytes 8 (strtodSpec d).toBits)) (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + d.lexeme.length)
    (hslice : (K.bs.drop lane).take (q - lane) = d.lexeme.data.toList)
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - lane) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        ((BitVec.ofNat 64 (strtodSpec d).toBits + BitVec.ofNat 64 7) +
          BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + (7 + (strtodSpec d).toBits) ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨s', j, K', hj, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩ :=
    stage2NoEventWalkValueNumber (mem := mem) hInv hpc hd hei hee hidx harr hlaneq hq64 hqleK hlex hwf hscan hframe hsp hk halen harena hb htk0 htm0 hcond hqle hcond63 hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  exact ⟨s', j, K', by omega, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩

/-- **The class-level bound for the `stage2NoEventWalkValueLiteralTrue` slice.**  The `true` slice's price is `4 + 13 + 1 + 5 * (cond - q)`: four dispatch steps, the chain's thirteen, the merge and the skip. -/
-- This weakens the slice's own price to `18 + 5 * (cond - lane)`.
-- It is not a composed class price and does not add the provider slice's count.
theorem stage2NoEventWalkValueLiteralTrue_classBound {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 116)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1702195828) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x74, 0x72, 0x75, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - lane) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 8 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 8 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨s', j, K', hj, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩ :=
    stage2NoEventWalkValueLiteralTrue (mem := mem) hInv hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63 hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  exact ⟨s', j, K', by omega, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩

/-- **The class-level bound for the `stage2NoEventWalkValueLiteralNull` slice.**  The `null` slice's price is `5 + 13 + 1 + 5 * (cond - q)`: five dispatch steps, the chain's thirteen, the merge and the skip. -/
-- This weakens the slice's own price to `18 + 5 * (cond - lane)`.
-- It is not a composed class price and does not add the provider slice's count.
theorem stage2NoEventWalkValueLiteralNull_classBound {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 110)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 1819047278) 4) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 4)
    (hslice : (K.bs.drop lane).take 4 = [0x6E, 0x75, 0x6C, 0x6C])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - lane) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 10 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 10 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨s', j, K', hj, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩ :=
    stage2NoEventWalkValueLiteralNull (mem := mem) hInv hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63 hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  exact ⟨s', j, K', by omega, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩

/-- **The class-level bound for the `stage2NoEventWalkValueLiteralFalse` slice.**  The `false` slice's price is `4 + 13 + 1 + 5 * (cond - q)`: four dispatch steps, the chain's thirteen, the merge and the skip. -/
-- This weakens the slice's own price to `18 + 5 * (cond - lane)`.
-- It is not a composed class price and does not add the provider slice's count.
theorem stage2NoEventWalkValueLiteralFalse_classBound {gap : Calls} {K : Stage2NoEventWalkCarry}
    {mem : Mem} {σ : Nat → UInt8} {lane q cond knext : Nat}
    {frb : BitVec 8} {spb : BitVec 32}
    {qbytes : List UInt8} {s : State}
    (hInv : Stage2NoEventWalkInv K mem s)
    (hpc : s.pc = "if.else495")
    (hlc : lookupName s.env "%.lcssa" = some (.int 8 (BitVec.ofNat 8 102)))
    (hee : lookupName s.env "%ee.1" = some (.int 64 (BitVec.ofNat 64 q)))
    (hidx : lookupName s.env "%idxprom.lcssa" =
      some (.int 64 (BitVec.ofNat 64 lane)))
    (harr : lookupName s.env "%arrayidx6.le1046" = some (.ptr (K.b + lane)))
    (hb : lookupName s.env "%b" = some (.ptr K.b))
    (hcond : lookupName s.env "%cond" = some (.int 64 (BitVec.ofNat 64 cond)))
    (htk0 : lookupName s.env "%tokens.0.lcssa1073" =
      some (.int 64 (BitVec.ofNat 64 K.tok)))
    (htm0 : lookupName s.env "%terms.0.lcssa1079" =
      some (.int 64 (BitVec.ofNat 64 K.terms)))
    (hframe : lookupName s.env "%frame.0.lcssa1097" = some (.int 8 frb))
    (hsp : lookupName s.env "%sp.0.lcssa1091.wide" = some (.int 32 spb))
    (hk : lookupName s.env "%inc.lcssa" = some (.int 64 (BitVec.ofNat 64 knext)))
    (halen : lookupName s.env "%alen.0.ph1405" =
      some (.int 64 (BitVec.ofNat 64 K.arena.length)))
    (harena : lookupName s.env "%arena.0.ph1406" =
      some (.int 64 (BitVec.ofNat 64 K.arenaWord)))
    (hlaneq : lane ≤ q) (hq64 : q < 2 ^ 64) (hq4 : 4 ≤ q - lane)
    (hlex : readBytes s.mem (K.b + lane) (q - lane) = some qbytes)
    (hval : neLitCheck qbytes (litBytes (BitVec.ofNat 64 435728179558) 5) = none)
    (hqle : q ≤ cond) (hcond63 : cond < 2 ^ 63)
    (hbytes : ∀ i, i < cond → readByte s.mem (K.b + i) = some (σ i))
    (hws : ∀ i, q ≤ i → i < cond →
      stage2SkipWs (BitVec.ofNat 8 (σ i).toNat) = true)
    (hstop : q = lane + 5)
    (hslice : (K.bs.drop lane).take 5 = [0x66, 0x61, 0x6C, 0x73, 0x65])
    (htrace : Stage2NoEventWalkTrace K)
    (htokn : K.tok < K.n)
    (hbase : Stage2NoEventWalkBaseLookups K s)
    (hfrNe : frb ≠ 0) (hspNe : spb ≠ 0) :
    ∃ s' j K', j ≤ 18 + 5 * (cond - lane) ∧
      (∀ k, runFuel (stage2NoEventCalls gap) (j + k) stage2NoEventBody s =
        runFuel (stage2NoEventCalls gap) k stage2NoEventBody s') ∧
      valueArmsAfter K' frb.toNat spb.toNat knext
        (BitVec.ofNat 64 K.tok + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 9 + BitVec.ofNat 64 K.terms) s' ∧
      Stage2NoEventWalkInv K' mem s' ∧
      K'.tok = K.tok + 1 ∧ K'.terms = K.terms + 9 ∧
      K'.bs = K.bs ∧ K'.arena = K.arena ∧
      K'.nep = K.nep ∧ K'.n = K.n ∧ K'.ent = K.ent ∧ K'.a12 = K.a12 ∧
      K'.next0 = K.next0 ∧ Stage2NoEventWalkTrace K' ∧
      frb.toNat < 2 ^ 8 ∧ frb.toNat ≠ 0 ∧
      spb.toNat < 2 ^ 32 ∧ spb.toNat ≠ 0 ∧
      Stage2NoEventWalkBaseLookups K' s' := by
  obtain ⟨s', j, K', hj, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩ :=
    stage2NoEventWalkValueLiteralFalse (mem := mem) hInv hpc hlc hee hidx harr hb hcond htk0 htm0 hframe hsp hk halen harena hlaneq hq64 hq4 hlex hval hqle hcond63 hbytes hws hstop hslice htrace htokn hbase hfrNe hspNe
  exact ⟨s', j, K', by omega, hrun, hafter, hinv', htok, hterms, hbs, harena,
    hstat1, hstat2, hstat3, hstat4, hstat5, htrace, hfrLt', hfrNe', hspLt', hspNe',
    hbaseEnd⟩

/-- **The value arms' measured counts, as compositions.**  The number arm is the
two blocks at its entry, the merge and the separator skip: `2 + 1 + 5·(cond−q)`.
The literal chain and merge are `13 + 1 + 5·(cond−q)`; the dispatch is four
steps for `true` (width 4) and `false` (width 5), five for `null` (width 4).
The composed totals are therefore `3 + 5·(cond−q)` (number), `18 + 5·(cond−q)`
(`true`/`false`) and `19 + 5·(cond−q)` (`null`).  These are the arms' own
counts; the class price is the sum of this slice and its provider slice's
measured count. -/
theorem valueArms_measuredTotals (q cond : Nat) :
    (3 + 5 * (cond - q) = 2 + 1 + 5 * (cond - q)) ∧
    (14 + 5 * (cond - q) = 13 + 1 + 5 * (cond - q)) ∧
    (18 + 5 * (cond - q) = 4 + 13 + 1 + 5 * (cond - q)) ∧
    (19 + 5 * (cond - q) = 5 + 13 + 1 + 5 * (cond - q)) := by
  omega

/-! ### Axiom footprints -/

#print axioms valueArms_literalDispatchTrue
#print axioms valueArms_trace_kind
#print axioms valueArms_trace_trueTag
#print axioms valueArms_literalAfter
#print axioms valueArms_measuredTotals
#print axioms stage2NoEventWalkValueLiteralTrue
#print axioms valueArms_literalDispatchNull
#print axioms valueArms_literalDispatchFalse
#print axioms stage2NoEventWalkValueLiteralNull
#print axioms stage2NoEventWalkValueLiteralFalse
#print axioms valueArms_trace_falseTag
#print axioms valueArms_trace_nullTag
#print axioms valueArms_step_if_then471
#print axioms valueArms_step_cleanup491
#print axioms valueArms_ifEnd545
#print axioms valueArms_numberRoute
#print axioms valueArms_numFast_model
#print axioms valueArms_trace_number
#print axioms stage2NoEventWalkValueNumber
#print axioms stage2NoEventWalkValueNumber_classBound
#print axioms stage2NoEventWalkValueLiteralTrue_classBound
#print axioms stage2NoEventWalkValueLiteralNull_classBound
#print axioms stage2NoEventWalkValueLiteralFalse_classBound

end LeanLLVM.Refinement
