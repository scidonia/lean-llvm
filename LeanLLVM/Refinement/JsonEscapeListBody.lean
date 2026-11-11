/-
The list body's entry blocks, read as the seed the doubling map starts from.

`JsonEscapeListFixpoint` states the map and its two halves; `JsonEscapeListLanes`
identifies the loop's word with the position rule.  Between them and the body sits
the trace: `entry`, `if.then.i` and `if.end.i` compute `escapeSeed` from the
caller's masks and carry, and the `xl_lanes` loop iterates the map from it.  This
module proves that trace, so the record's post can name the pinned body's run
rather than an authored one.

The trace is stated block by block, each lemma concluding the jump it makes and
the cells the successor block reads.  That is the shape the follow-on needs:
`step` returns a state, but the *next* block's meaning is decided by a handful of
registers, and a conclusion that names them lets the next lemma be stated without
its predecessor's whole environment.

Two facts about the loop are the ones that matter, and both are about the exit
test rather than the iteration count:

* the loop stops exactly when `stepWord` fixes the word (`loop_test_eq`), so the
  word it leaves is a fixed point whatever the number of iterations was;
* a fixed point reached from the seed is the rule's word (`stepN_fixed_spec`),
  because the rule's word is reached by iteration thirty-two and iterating a fixed
  point is the identity.
-/
import LeanLLVM.Refinement.JsonEscapeListLanes
import LeanLLVM.Refinement.JsonEscapeBatchEntries
import LeanLLVM.Refinement.JsonEscapeSteps

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEscapeIR
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.BitLanes

/-! ### Reading and writing a word

The body's two memory accesses at the ABI's words: a 64-bit load at eight readable
bytes, and a 64-bit store, which `loadValue_storeValue_64` already states. -/

/-- A 64-bit load at a readable byte range. -/
theorem loadValue_i64_of_readBytes {m : Mem} {a : Nat} {bs : List UInt8}
    (hr : readBytes m a 8 = some bs) :
    loadValue m (.int 64) a = some (.int 64 (BitVec.ofNat 64 (bytesToNat bs))) := by
  simp only [loadValue, show (64 + 7) / 8 = 8 from rfl,
    show (64 = 0) = False from by decide, ite_false, hr]

/-- `%d = load i64, ptr %p` at the eight bytes a 64-bit word occupies. -/
theorem b_load64 (env : Env) (s : State) (d p : String) (a : Nat) (v : BitVec 64)
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) :
    evalInstr escapeCalls (withEnv env s) (.load d (.int 64) (.reg p)) =
      some (withEnv ((d, .int 64 v) :: env) s) := by
  have hv' : loadValue s.mem (.int 64) a = some (.int 64 v) := by
    rw [loadValue_i64_of_readBytes hv, natToBytes_toNat,
      show (256 : Nat) ^ 8 = 2 ^ 64 from by decide, Nat.mod_eq_of_lt v.isLt]
    simp [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp) (hv := hv')

/-- `store i64 %v, ptr %p`. -/
theorem b_store64 (env : Env) (s : State) (r p : String) (x : BitVec 64) (a : Nat)
    (hv : lookupName env r = some (.int 64 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr escapeCalls (withEnv env s) (.store (.int 64) (.reg r) (.reg p)) =
      some (withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) }) := by
  rw [evalInstr_store (vv := .int 64 x) (a := a)
    (s' := withEnv env { s with mem := writeBytes s.mem a (natToBytes x.toNat 8) })
    (hv := evalOperand_reg_of env s r (.int 64 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]
  simp [storeValue, withEnv]

/-! ### The arithmetic operations the seed blocks use

Each is `evalInstr_binop` at the operation's own meaning, written at `BitVec` so
the successor block reads a word rather than a `Nat`. -/

/-- `%d = or i64 %a, %b`. -/
theorem b_or64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .or 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 (x ||| y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x ||| y).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = shl i64 %a, 1`. -/
theorem b_shl64_one (env : Env) (s : State) (d a : String) (x : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .shl 64 (.reg a) (.imm (.int 64 (BitVec.ofInt 64 1)))) =
      some (withEnv ((d, .int 64 (x <<< 1)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x <<< 1).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 (BitVec.ofInt 64 1))
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = shl i64 %a, 2`. -/
theorem b_shl64_two (env : Env) (s : State) (d a : String) (x : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .shl 64 (.reg a) (.imm (.int 64 (BitVec.ofInt 64 2)))) =
      some (withEnv ((d, .int 64 (x <<< 2)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x <<< 2).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 (BitVec.ofInt 64 2))
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = xor i64 %a, -1`. -/
theorem b_xor64_neg_one (env : Env) (s : State) (d a : String) (x : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .xor 64 (.reg a) (.imm (.int 64 (BitVec.ofInt 64 (-1))))) =
      some (withEnv ((d, .int 64 (x ^^^ (-1))) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x ^^^ (-1)).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 (BitVec.ofInt 64 (-1)))
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = lshr i64 %a, 63`. -/
theorem b_lshr64_63 (env : Env) (s : State) (d a : String) (x : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .lshr 64 (.reg a) (.imm (.int 64 (BitVec.ofInt 64 63)))) =
      some (withEnv ((d, .int 64 (x >>> 63)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x >>> 63).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 (BitVec.ofInt 64 63))
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = shl i32 %a, 6`. -/
theorem b_shl32_six (env : Env) (s : State) (d a : String) (x : BitVec 32)
    (ha : lookupName env a = some (.int 32 x)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .shl 32 (.reg a) (.imm (.int 32 (BitVec.ofInt 32 6)))) =
      some (withEnv ((d, .int 32 (x <<< 6)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x <<< 6).toNat)
    (ha := evalOperand_reg_of env s a (.int 32 x) ha)
    (hb := evalOperand_lit_of _ 32 (BitVec.ofInt 32 6))
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = add i64 %a, %b`. -/
theorem b_add64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.binop d .add 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 (x + y)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (r := (x + y).toNat)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)
    (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- `%d = icmp eq i64 %a, %b`. -/
theorem b_icmp_eq64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d .eq 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (evalICmp .eq x y)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

/-- `%d = icmp ugt i64 %a, %b`. -/
theorem b_icmp_ugt64 (env : Env) (s : State) (d a b : String) (x y : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.icmp d .ugt 64 (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (evalICmp .ugt x y)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

/-- A decided proposition's bool, read as the one-bit value, is `1` exactly when
it holds. -/
theorem ofBool_decide_one_iff (p : Prop) [Decidable p] :
    BitVec.ofBool (decide p) = (1 : BitVec 1) ↔ p := by
  constructor
  · intro h
    cases hd : decide p with
    | false => rw [hd] at h; exact absurd h (by decide)
    | true => exact of_decide_eq_true hd
  · intro hp
    rw [decide_eq_true hp]
    rfl

theorem ofBool_decide_zero_iff (p : Prop) [Decidable p] :
    BitVec.ofBool (decide p) = (0 : BitVec 1) ↔ ¬ p := by
  constructor
  · intro h
    cases hd : decide p with
    | false => exact of_decide_eq_false hd
    | true => rw [hd] at h; exact absurd h (by decide)
  · intro hnp
    rw [decide_eq_false hnp]
    rfl

/-- The equality test reads as its proposition. -/
theorem evalICmp_eq_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .eq x y = (1 : BitVec 1) ↔ x = y := by
  rw [show evalICmp .eq x y = BitVec.ofBool (decide (x = y)) from rfl]
  exact ofBool_decide_one_iff _

theorem evalICmp_eq_zero_iff {w : Nat} (x y : BitVec w) :
    evalICmp .eq x y = (0 : BitVec 1) ↔ x ≠ y := by
  rw [show evalICmp .eq x y = BitVec.ofBool (decide (x = y)) from rfl]
  exact ofBool_decide_zero_iff _

/-- The unsigned-greater test reads as its proposition. -/
theorem evalICmp_ugt_one_iff {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (1 : BitVec 1) ↔ BitVec.ult y x := by
  rw [show evalICmp .ugt x y = BitVec.ofBool (BitVec.ult y x) from rfl]
  by_cases h : BitVec.ult y x <;> simp [h]

/-- The unsigned-greater test reads as its `Nat` proposition. -/
theorem evalICmp_ugt_one_iff_toNat {w : Nat} (x y : BitVec w) :
    evalICmp .ugt x y = (1 : BitVec 1) ↔ y.toNat < x.toNat := by
  rw [evalICmp_ugt_one_iff, BitVec.ult_iff_toNat_lt]

/-- `%d = select i1 %c, i64 %a, i64 %b` at a decided condition. -/
theorem b_select64_true (env : Env) (s : State) (d c a b : String) (x y : BitVec 64)
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.select d (.int 64) (.reg c) (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 x) :: env) s) := by
  rw [evalInstr_select_true (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

/-- `%d = select i1 %c, i64 %a, i64 %b` at a clear condition. -/
theorem b_select64_false (env : Env) (s : State) (d c a b : String) (x y : BitVec 64)
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : lookupName env a = some (.int 64 x))
    (hb : lookupName env b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.select d (.int 64) (.reg c) (.reg a) (.reg b)) =
      some (withEnv ((d, .int 64 y) :: env) s) := by
  rw [evalInstr_select_false (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
    (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_reg_of env s b (.int 64 y) hb)]
  simp only [withEnv, State.bind]

/-! ### The body's blocks

The pinned body's ten blocks, by index, and the entry point's lookup at each name.
Both are decidable on the pinned AST, which is what lets a block lemma name the
block it runs rather than restating its instructions. -/

/-- A block by index, so a block can be named without restating it. -/
def blockAt (f : Function) (i : Nat) (h : i < f.blocks.length) : Block := f.blocks[i]

def lstEntry := blockAt escapeListFunction 0 (by decide)
def lstIfThen := blockAt escapeListFunction 1 (by decide)
def lstIfEnd := blockAt escapeListFunction 2 (by decide)
def lstDoBody := blockAt escapeListFunction 3 (by decide)
def lstLanesExit := blockAt escapeListFunction 4 (by decide)
def lstIfEnd4 := blockAt escapeListFunction 5 (by decide)
def lstForPre := blockAt escapeListFunction 6 (by decide)
def lstWhilePre := blockAt escapeListFunction 7 (by decide)
def lstWhileBody := blockAt escapeListFunction 8 (by decide)
def lstEmitExit := blockAt escapeListFunction 9 (by decide)

theorem findBlock_entry : escapeListFunction.findBlock "entry" = some lstEntry := by decide

theorem findBlock_ifThen : escapeListFunction.findBlock "if.then.i" = some lstIfThen := by
  decide

theorem findBlock_ifEnd : escapeListFunction.findBlock "if.end.i" = some lstIfEnd := by decide

theorem findBlock_doBody : escapeListFunction.findBlock "do.body.i" = some lstDoBody := by
  decide

theorem findBlock_lanesExit : escapeListFunction.findBlock "xl_lanes.exit" = some lstLanesExit := by
  decide

theorem findBlock_ifEnd4 : escapeListFunction.findBlock "if.end.i4" = some lstIfEnd4 := by
  decide

theorem findBlock_forPre :
    escapeListFunction.findBlock "for.body.preheader.i.i" = some lstForPre := by decide

theorem findBlock_whilePre :
    escapeListFunction.findBlock "while.body.preheader.i.i" = some lstWhilePre := by decide

theorem findBlock_whileBody :
    escapeListFunction.findBlock "while.body.i.i" = some lstWhileBody := by decide

theorem findBlock_emitExit :
    escapeListFunction.findBlock "xl_emit.exit" = some lstEmitExit := by decide

/-- One block's step: its instructions, then its terminator. -/
theorem step_of (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : escapeListFunction.findBlock name = some b)
    (hbody : denoteCode escapeCalls b.instrs s = some s') :
    step escapeCalls escapeListFunction s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

/-- A jump spends one step of fuel. -/
theorem runFuel_jump {s s' : State} {n : Nat} {f : Function}
    (h : step escapeCalls f s = .jump s') :
    runFuel escapeCalls (n + 1) f s = runFuel escapeCalls n f s' := by
  simp [runFuel, h]

/-- A return ends the run. -/
theorem runFuel_ret {s s' : State} {v : Option Value} {n : Nat} {f : Function}
    (h : step escapeCalls f s = .ret v s') :
    runFuel escapeCalls (n + 1) f s = some (.ret v s'.mem) := by
  simp [runFuel, h]

/-- The `condbr` taken arm, at a one-bit condition. -/
theorem execTerm_condbr_one (s : State) (c : Operand) (t f : String) (v : BitVec 1)
    (h : evalOperand s c = some (.int 1 v)) (hv : v = 1) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h, hv]

/-- The `condbr` untaken arm, at a clear condition. -/
theorem execTerm_condbr_zero (s : State) (c : Operand) (t f : String) (v : BitVec 1)
    (h : evalOperand s c = some (.int 1 v)) (hv : v = 0) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h, hv]

/-- A register's cell, read out of a binding prefix.  The prefix is the block's
bindings zipped with their values; the key is either one of them or a name the
block did not touch, in which case the lookup is the incoming environment's. -/
macro "lk" : tactic => `(tactic|
  (first
   | assumption
   | (repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
      | rw [lookupName_cons_self]
      | assumption)
   | (simp only [List.zip_cons_cons, List.zip_nil_right,
        List.cons_append, List.nil_append]
      repeat rw [lookupName_cons_ne _ _ (by decide)]
      first
      | rw [lookupName_cons_self]
      | assumption)))


/-! ### Two more instruction shapes

The seed blocks compare and mask against immediates, so the register-only helpers
above are joined by the two that take a literal. -/

/-- `%d = and i64 %a, <c>`. -/
theorem b_and64_imm (env : Env) (s : State) (d a : String) (x c : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.binop d .and 64 (.reg a) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 64 (x &&& c)) :: env) s) := by
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, withEnv, State.bind]
    using evalInstr_binop (op := .and) (r := (x &&& c).toNat)
      (ha := evalOperand_reg_of env s a (.int 64 x) ha)
      (hb := evalOperand_lit_of _ 64 c)
      (hr := by simp [evalBinopNat, evalBinop, BitVec.ofNat_toNat])

/-- `%d = icmp eq i64 %a, <c>`. -/
theorem b_icmp_eq64_imm (env : Env) (s : State) (d a : String) (x c : BitVec 64)
    (ha : lookupName env a = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.icmp d .eq 64 (.reg a) (.imm (.int 64 c))) =
      some (withEnv ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int 64 x) ha)
    (hb := evalOperand_lit_of _ 64 c)]
  simp only [withEnv, State.bind]

/-- `%d = select i1 %c, <a>, <b>` at a set condition, both arms arbitrary operands. -/
theorem b_select64_true' (env : Env) (s : State) (d c : String) (a b : Operand)
    (x y : BitVec 64)
    (hc : lookupName env c = some (.int 1 (1 : BitVec 1)))
    (ha : evalOperand (withEnv env s) a = some (.int 64 x))
    (hb : evalOperand (withEnv env s) b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.select d (.int 64) (.reg c) a b) =
      some (withEnv ((d, .int 64 x) :: env) s) := by
  rw [evalInstr_select_true (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
    (ha := ha) (hb := hb)]
  simp only [withEnv, State.bind]

/-- `%d = select i1 %c, <a>, <b>` at a clear condition. -/
theorem b_select64_false' (env : Env) (s : State) (d c : String) (a b : Operand)
    (x y : BitVec 64)
    (hc : lookupName env c = some (.int 1 (0 : BitVec 1)))
    (ha : evalOperand (withEnv env s) a = some (.int 64 x))
    (hb : evalOperand (withEnv env s) b = some (.int 64 y)) :
    evalInstr escapeCalls (withEnv env s) (.select d (.int 64) (.reg c) a b) =
      some (withEnv ((d, .int 64 y) :: env) s) := by
  rw [evalInstr_select_false (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
    (ha := ha) (hb := hb)]
  simp only [withEnv, State.bind]

/-! ### The three seed blocks' instruction lists

Naming the pinned instructions once per block is what lets the run below be a
`denoteCode` chain rather than a restatement.  Each equality is decided on the
pinned AST, so a change to the fixture that moved an instruction would fail it. -/

theorem lstEntry_instrs :
    lstEntry.instrs =
      [ .gep "%arrayidx1" (.int 8) (.reg "%carry") (.imm (.int 64 (BitVec.ofInt 64 8))),
        .load "%0" (.int 64) (.reg "%carry"),
        .binop "%shl.i" .shl 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 1))),
        .binop "%or.i" .or 64 (.reg "%0") (.reg "%shl.i"),
        .binop "%not.i" .xor 64 (.reg "%or.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%and.i" .and 64 (.reg "%bs") (.reg "%not.i"),
        .binop "%and1.i" .and 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 1))),
        .binop "%and2.i" .and 64 (.reg "%and1.i") (.reg "%0"),
        .icmp "%tobool.not.i" .eq 64 (.reg "%and2.i") (.imm (.int 64 (BitVec.ofInt 64 0)))] := by
  decide

theorem lstEntry_term :
    lstEntry.term = .condbr (.reg "%tobool.not.i") "if.end.i" "if.then.i" := by decide

theorem lstIfThen_instrs :
    lstIfThen.instrs =
      [ .load "%1" (.int 64) (.reg "%arrayidx1"),
        .icmp "%tobool3.not.i" .eq 64 (.reg "%1") (.imm (.int 64 (BitVec.ofInt 64 0))),
        .binop "%and4.i" .and 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .select "%cond.i" (.int 64) (.reg "%tobool3.not.i")
          (.imm (.int 64 (BitVec.ofInt 64 1))) (.reg "%and4.i"),
        .binop "%or5.i" .or 64 (.reg "%cond.i") (.reg "%and.i")] := by
  decide

theorem lstIfThen_term : lstIfThen.term = .br "if.end.i" := by decide

theorem lstIfEnd_instrs :
    lstIfEnd.instrs =
      [ .phi "%e.0.i" (.int 64) [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")],
        .binop "%and7.i" .and 64 (.reg "%shl.i") (.reg "%bs"),
        .binop "%shl8.i" .shl 64 (.reg "%e.0.i") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .binop "%and9.i" .and 64 (.reg "%shl8.i") (.reg "%and7.i"),
        .binop "%or10.i" .or 64 (.reg "%and9.i") (.reg "%e.0.i"),
        .binop "%shl11.i" .shl 64 (.reg "%or10.i") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .binop "%and12.i" .and 64 (.reg "%shl11.i") (.reg "%and7.i"),
        .binop "%or13.i" .or 64 (.reg "%and12.i") (.reg "%or10.i"),
        .binop "%shl14.i" .shl 64 (.reg "%or13.i") (.imm (.int 64 (BitVec.ofInt 64 2))),
        .binop "%not16.i" .xor 64 (.reg "%or13.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
        .binop "%2" .and 64 (.reg "%shl14.i") (.reg "%not16.i"),
        .binop "%and17.i" .and 64 (.reg "%2") (.reg "%and7.i"),
        .icmp "%cmp.not.i" .eq 64 (.reg "%and17.i")
          (.imm (.int 64 (BitVec.ofInt 64 0)))] := by
  decide

theorem lstIfEnd_term :
    lstIfEnd.term = .condbr (.reg "%cmp.not.i") "xl_lanes.exit" "do.body.i" := by decide

/-! ### `entry`: the run-start word and the lane-0 test -/

/-- The entry block's environment. -/
def entryEnv (env : Env) (bs w0 : BitVec 64) (carry : Nat) : Env :=
  (["%tobool.not.i", "%and2.i", "%and1.i", "%and.i", "%not.i", "%or.i", "%shl.i",
    "%0", "%arrayidx1"] : List String).zip
    ([.int 1 (evalICmp .eq ((bs &&& (BitVec.ofInt 64 1)) &&& w0) (BitVec.ofInt 64 0)),
      .int 64 ((bs &&& (BitVec.ofInt 64 1)) &&& w0),
      .int 64 (bs &&& (BitVec.ofInt 64 1)),
      .int 64 (bs &&& ((w0 ||| (bs <<< 1)) ^^^ (-1))),
      .int 64 ((w0 ||| (bs <<< 1)) ^^^ (-1)),
      .int 64 (w0 ||| (bs <<< 1)),
      .int 64 (bs <<< 1),
      .int 64 w0,
      .ptr (carry + 8)] : List Value) ++ env

theorem entry_denote (env : Env) (s : State) (bs w0 : BitVec 64) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld : readBytes s.mem carry 8 = some (natToBytes w0.toNat 8)) :
    denoteCode escapeCalls lstEntry.instrs (withEnv env s) =
      some (withEnv (entryEnv env bs w0 carry) s) := by
  rw [lstEntry_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_gep8_imm _ s "%arrayidx1" "%carry" carry 8
    (BitVec.ofInt 64 8) (by lk) (by decide) (by decide))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load64 _ s "%0" "%carry" carry w0 (by lk) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_shl64_one _ s "%shl.i" "%bs" bs (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or.i" "%0" "%shl.i" w0 (bs <<< 1)
    (by lk) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_xor64_neg_one _ s "%not.i" "%or.i"
    (w0 ||| (bs <<< 1)) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and.i" "%bs" "%not.i" bs
    ((w0 ||| (bs <<< 1)) ^^^ (-1)) (by lk) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64_imm _ s "%and1.i" "%bs" bs
    (BitVec.ofInt 64 1) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and2.i" "%and1.i" "%0"
    (bs &&& (BitVec.ofInt 64 1)) w0 (by lk) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64_imm _ s "%tobool.not.i" "%and2.i"
    ((bs &&& (BitVec.ofInt 64 1)) &&& w0) (BitVec.ofInt 64 0) (by lk))]
  simp only [denoteCode, denoteRun, State.bindAll, entryEnv, List.zip_cons_cons, List.zip_nil_right,
    List.zip_nil_right, List.cons_append, List.nil_append]

/-- The cells the successor blocks read, out of the entry block's environment. -/
theorem entry_cells (env : Env) (bs w0 : BitVec 64) (carry : Nat) :
    lookupName (entryEnv env bs w0 carry) "%and.i" =
        some (.int 64 (bs &&& ((w0 ||| (bs <<< 1)) ^^^ (-1)))) ∧
      lookupName (entryEnv env bs w0 carry) "%shl.i" = some (.int 64 (bs <<< 1)) ∧
      lookupName (entryEnv env bs w0 carry) "%and2.i" =
        some (.int 64 ((bs &&& (BitVec.ofInt 64 1)) &&& w0)) ∧
      lookupName (entryEnv env bs w0 carry) "%tobool.not.i" =
        some (.int 1 (evalICmp .eq ((bs &&& (BitVec.ofInt 64 1)) &&& w0) (BitVec.ofInt 64 0))) ∧
      lookupName (entryEnv env bs w0 carry) "%arrayidx1" = some (.ptr (carry + 8)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (simp only [entryEnv]; lk)

/-! ### The exit test is the fixed-point test

The loop's two exit tests are the same proposition: `do.body.i` compares the step's
result with its input, and `if.end.i` tests the step's *new* lanes for emptiness.
This is the identity that makes both exits mean "the map has stopped", which is
what lets the exit word be read off without counting iterations. -/

/-- `-1` at sixty-four lanes is the all-ones word. -/
theorem neg_one_64 : (-1 : BitVec 64) = BitVec.allOnes 64 := by decide

/-- Complementing is xoring with `-1`, at the word width the body uses. -/
theorem xor_neg_one_eq_not (x : BitVec 64) : x ^^^ (-1) = ~~~x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_xor, neg_one_64, allOnes_getLsbD_of_lt hk, getLsbD_not_of_lt x hk]
  cases x.getLsbD k <;> rfl

/-- A word is unchanged by or-ing a second exactly when the second has no lane the
first does not. -/
theorem or_eq_left_iff_and_not_zero {w : Nat} (x y : BitVec w) :
    x ||| y = x ↔ y &&& ~~~x = 0 := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hl : (y.getLsbD k && !(x.getLsbD k)) = false := by
      have hh : (x.getLsbD k || y.getLsbD k) = x.getLsbD k := by
        rw [← BitVec.getLsbD_or, h]
      cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp_all
    rw [show (y &&& ~~~x).getLsbD k = (y.getLsbD k && !x.getLsbD k) by
      rw [BitVec.getLsbD_and, getLsbD_not_of_lt x hk]]
    rw [hl]
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    have hl : (y.getLsbD k && !(x.getLsbD k)) = false := by
      have hh : (y &&& ~~~x).getLsbD k = (0 : BitVec w).getLsbD k := by rw [h]
      rw [BitVec.getLsbD_and, getLsbD_not_of_lt x hk] at hh
      have hz : (0 : BitVec w).getLsbD k = false := by simp
      rw [hz] at hh
      exact hh
    rw [BitVec.getLsbD_or]
    cases hx : x.getLsbD k <;> cases hy : y.getLsbD k <;> simp_all

/-- The two sides of the step's new-lane test commute with the step's mask. -/
theorem and_and_swap (a b c : BitVec 64) : ((a &&& b) &&& c) = ((a &&& c) &&& b) := by
  rw [BitVec.and_assoc, BitVec.and_assoc]
  congr 1
  exact BitVec.and_comm _ _

/-- **The exit test is the fixed-point test.**  `%and17.i` is zero exactly when
`stepWord` leaves `%or13.i` alone, which is the same condition `do.body.i`'s own
comparison states. -/
theorem stepWord_fixed_iff (bs e0 : BitVec 64) :
    ((e0 <<< 2) &&& (e0 ^^^ (-1))) &&& stepMask bs = (0 : BitVec 64) ↔
      stepWord bs e0 = e0 := by
  rw [xor_neg_one_eq_not, stepWord, or_eq_left_iff_and_not_zero, and_and_swap]

/-! ### `if.then.i`: the boundary select

Taken when the lane-0 test is set: the block loads the second carry word and
selects `1` or `bs & 2` by it, which is `escapeSeed`'s boundary correction. -/

/-- The boundary select's value: the first carry word's second lane when the
previous block's run was open, and `1` otherwise. -/
def ifThenCond (bs w1 : BitVec 64) : BitVec 64 :=
  if w1 = BitVec.ofInt 64 0 then BitVec.ofInt 64 1 else bs &&& BitVec.ofInt 64 2

def ifThenEnv (env : Env) (bs w1 andI : BitVec 64) : Env :=
  (["%or5.i", "%cond.i", "%and4.i", "%tobool3.not.i", "%1"] : List String).zip
    ([.int 64 (ifThenCond bs w1 ||| andI),
      .int 64 (ifThenCond bs w1),
      .int 64 (bs &&& BitVec.ofInt 64 2),
      .int 1 (evalICmp .eq w1 (BitVec.ofInt 64 0)),
      .int 64 w1] : List Value) ++ env

-- the environment after the first three instructions, named once
def ft3 (env : Env) (bs w1 : BitVec 64) : Env :=
  (["%and4.i", "%tobool3.not.i", "%1"] : List String).zip
    ([.int 64 (bs &&& BitVec.ofInt 64 2),
      .int 1 (evalICmp .eq w1 (BitVec.ofInt 64 0)),
      .int 64 w1] : List Value) ++ env

theorem ifThen_denote (env : Env) (s : State) (bs w1 andI : BitVec 64) (a : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (handI : lookupName env "%and.i" = some (.int 64 andI))
    (harr : lookupName env "%arrayidx1" = some (.ptr a))
    (hld : readBytes s.mem a 8 = some (natToBytes w1.toNat 8)) :
    denoteCode escapeCalls lstIfThen.instrs (withEnv env s) =
      some (withEnv (ifThenEnv env bs w1 andI) s) := by
  rw [lstIfThen_instrs]
  rw [denoteCode_cons_of _ _ _ _ _ (b_load64 _ s "%1" "%arrayidx1" a w1 (by lk) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64_imm _ s "%tobool3.not.i" "%1" w1
    (BitVec.ofInt 64 0) (by lk))]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64_imm _ s "%and4.i" "%bs" bs
    (BitVec.ofInt 64 2) (by lk))]
  change denoteCode escapeCalls
      [ .select "%cond.i" (.int 64) (.reg "%tobool3.not.i")
          (.imm (.int 64 (BitVec.ofInt 64 1))) (.reg "%and4.i"),
        .binop "%or5.i" .or 64 (.reg "%cond.i") (.reg "%and.i")]
      (withEnv (ft3 env bs w1) s) =
    some (withEnv (ifThenEnv env bs w1 andI) s)
  have hcond : lookupName (ft3 env bs w1) "%tobool3.not.i" =
      some (.int 1 (evalICmp .eq w1 (BitVec.ofInt 64 0))) := by
    show lookupName ((["%and4.i", "%tobool3.not.i", "%1"] : List String).zip
      ([.int 64 (bs &&& BitVec.ofInt 64 2),
        .int 1 (evalICmp .eq w1 (BitVec.ofInt 64 0)),
        .int 64 w1] : List Value) ++ env) "%tobool3.not.i" = _
    lk
  have hand4 : lookupName (ft3 env bs w1) "%and4.i" =
      some (.int 64 (bs &&& BitVec.ofInt 64 2)) := by
    show lookupName ((["%and4.i", "%tobool3.not.i", "%1"] : List String).zip
      ([.int 64 (bs &&& BitVec.ofInt 64 2),
        .int 1 (evalICmp .eq w1 (BitVec.ofInt 64 0)),
        .int 64 w1] : List Value) ++ env) "%and4.i" = _
    lk
  by_cases h0 : w1 = BitVec.ofInt 64 0
  · have hc : evalICmp .eq w1 (BitVec.ofInt 64 0) = (1 : BitVec 1) :=
      (evalICmp_eq_one_iff w1 (BitVec.ofInt 64 0)).mpr h0
    rw [denoteCode_cons_of _ _ _ _ _ (b_select64_true' (ft3 env bs w1) s "%cond.i"
      "%tobool3.not.i" (.imm (.int 64 (BitVec.ofInt 64 1))) (.reg "%and4.i")
      (BitVec.ofInt 64 1) (bs &&& BitVec.ofInt 64 2)
      (by rw [show (1 : BitVec 1) = evalICmp .eq w1 (BitVec.ofInt 64 0) from hc.symm]
          exact hcond)
      (by rfl) (by exact hand4))]
    rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or5.i" "%cond.i" "%and.i"
      (BitVec.ofInt 64 1) andI (by lk) (by lk))]
    simp only [denoteCode, denoteRun, State.bindAll, ifThenEnv, ft3, List.zip_cons_cons, List.zip_nil_right,
      List.zip_nil_right, List.cons_append, List.nil_append]
    rw [show ifThenCond bs w1 = BitVec.ofInt 64 1 from by
      unfold ifThenCond; exact ite_eq_left h0]
  · have hc : evalICmp .eq w1 (BitVec.ofInt 64 0) = (0 : BitVec 1) :=
      (evalICmp_eq_zero_iff w1 (BitVec.ofInt 64 0)).mpr h0
    rw [denoteCode_cons_of _ _ _ _ _ (b_select64_false' (ft3 env bs w1) s "%cond.i"
      "%tobool3.not.i" (.imm (.int 64 (BitVec.ofInt 64 1))) (.reg "%and4.i")
      (BitVec.ofInt 64 1) (bs &&& BitVec.ofInt 64 2)
      (by rw [show (0 : BitVec 1) = evalICmp .eq w1 (BitVec.ofInt 64 0) from hc.symm]
          exact hcond)
      (by rfl) (by exact hand4))]
    rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or5.i" "%cond.i" "%and.i"
      (bs &&& BitVec.ofInt 64 2) andI (by lk) (by lk))]
    simp only [denoteCode, denoteRun, State.bindAll, ifThenEnv, ft3, List.zip_cons_cons, List.zip_nil_right,
      List.zip_nil_right, List.cons_append, List.nil_append]
    rw [show ifThenCond bs w1 = bs &&& BitVec.ofInt 64 2 from by
      unfold ifThenCond; exact ite_eq_right h0]

/-! ### `if.end.i`: two doublings and the new-lane test

`%or10.i` is the first doubling and `%or13.i` the second, both masked by
`%and7.i = stepMask`.  `%and17.i` is the second step's *new* lanes, so the block's
terminator branches to the loop exactly when the map has not stopped. -/

/-- The intermediate words the block writes, so the environment aliases below stay
readable. -/
def em1 (bs e0 : BitVec 64) : BitVec 64 := (bs <<< 1) &&& bs
def em2 (bs e0 : BitVec 64) : BitVec 64 := e0 <<< 2
def em3 (bs e0 : BitVec 64) : BitVec 64 := em2 bs e0 &&& em1 bs e0
def em4 (bs e0 : BitVec 64) : BitVec 64 := em3 bs e0 ||| e0
def em5 (bs e0 : BitVec 64) : BitVec 64 := em4 bs e0 <<< 2
def em6 (bs e0 : BitVec 64) : BitVec 64 := em5 bs e0 &&& em1 bs e0
def em7 (bs e0 : BitVec 64) : BitVec 64 := em6 bs e0 ||| em4 bs e0
def em8 (bs e0 : BitVec 64) : BitVec 64 := em7 bs e0 <<< 2
def em9 (bs e0 : BitVec 64) : BitVec 64 := em7 bs e0 ^^^ (-1)
def em10 (bs e0 : BitVec 64) : BitVec 64 := em8 bs e0 &&& em9 bs e0
def em11 (bs e0 : BitVec 64) : BitVec 64 := em10 bs e0 &&& em1 bs e0
def em12 (bs e0 : BitVec 64) : BitVec 1 := evalICmp .eq (em11 bs e0) (BitVec.ofInt 64 0)

/-- The first step is the first doubling: `em4` is `stepWord`'s value. -/
theorem em4_eq (bs e0 : BitVec 64) : em4 bs e0 = stepWord bs e0 := by
  rw [stepWord, BitVec.or_comm]
  rfl

/-- The second doubling. -/
theorem em7_eq (bs e0 : BitVec 64) :
    em7 bs e0 = stepWord bs (stepWord bs e0) := by
  unfold em7 em6 em5
  rw [em4_eq, stepWord, BitVec.or_comm]
  rfl

/-- The new-lane test, at the word the second doubling leaves. -/
theorem em11_eq (bs e0 : BitVec 64) :
    em11 bs e0 = ((em7 bs e0 <<< 2) &&& (em7 bs e0 ^^^ (-1))) &&& stepMask bs := rfl

/-- The block's environment, one alias per instruction: `ie k` is the environment
after `k` of the block's thirteen instructions. -/
def ie1 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%e.0.i"] : List String).zip ([.int 64 e0] : List Value) ++ env
def ie2 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%and7.i"] : List String).zip ([.int 64 (em1 bs e0)] : List Value) ++ ie1 env bs e0
def ie3 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%shl8.i"] : List String).zip ([.int 64 (em2 bs e0)] : List Value) ++ ie2 env bs e0
def ie4 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%and9.i"] : List String).zip ([.int 64 (em3 bs e0)] : List Value) ++ ie3 env bs e0
def ie5 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%or10.i"] : List String).zip ([.int 64 (em4 bs e0)] : List Value) ++ ie4 env bs e0
def ie6 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%shl11.i"] : List String).zip ([.int 64 (em5 bs e0)] : List Value) ++ ie5 env bs e0
def ie7 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%and12.i"] : List String).zip ([.int 64 (em6 bs e0)] : List Value) ++ ie6 env bs e0
def ie8 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%or13.i"] : List String).zip ([.int 64 (em7 bs e0)] : List Value) ++ ie7 env bs e0
def ie9 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%shl14.i"] : List String).zip ([.int 64 (em8 bs e0)] : List Value) ++ ie8 env bs e0
def ie10 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%not16.i"] : List String).zip ([.int 64 (em9 bs e0)] : List Value) ++ ie9 env bs e0
def ie11 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%2"] : List String).zip ([.int 64 (em10 bs e0)] : List Value) ++ ie10 env bs e0
def ie12 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%and17.i"] : List String).zip ([.int 64 (em11 bs e0)] : List Value) ++ ie11 env bs e0
def ie13 (env : Env) (bs e0 : BitVec 64) : Env :=
  (["%cmp.not.i"] : List String).zip ([.int 1 (em12 bs e0)] : List Value) ++ ie12 env bs e0

/-- Unfolding every alias, so a lookup is again a walk over a cons chain. -/
macro "ie_simp" : tactic => `(tactic|
  (simp only [ie13, ie12, ie11, ie10, ie9, ie8, ie7, ie6, ie5, ie4, ie3, ie2, ie1,
    List.zip_cons_cons, List.zip_nil_right, List.cons_append,
    List.nil_append]))

theorem ifEnd_denote (env : Env) (s : State) (bs e0 : BitVec 64) (p : String) (op : Operand)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hshl : lookupName env "%shl.i" = some (.int 64 (bs <<< 1)))
    (hpre : (withEnv env s).pre = some p)
    (hinc : phiIncoming p [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")] = some op)
    (hop : evalOperand (withEnv env s) op = some (.int 64 e0)) :
    denoteCode escapeCalls lstIfEnd.instrs (withEnv env s) =
      some (withEnv (ie13 env bs e0) s) := by
  rw [lstIfEnd_instrs]
  rw [phiRun_one escapeCalls env s "%e.0.i" (.int 64) _ _ hpre hinc hop]
  all_goals (first | rfl | decide | skip)
  rw [show withEnv (("%e.0.i", .int 64 e0) :: env) s = withEnv (ie1 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and7.i" "%shl.i" "%bs" (bs <<< 1) bs (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%and7.i", .int 64 ((bs <<< 1) &&& bs)) :: ie1 env bs e0) s = withEnv (ie2 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_shl64_two _ s "%shl8.i" "%e.0.i" e0 (by ie_simp; lk))]
  rw [show withEnv (("%shl8.i", .int 64 (e0 <<< 2)) :: ie2 env bs e0) s = withEnv (ie3 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and9.i" "%shl8.i" "%and7.i" (em2 bs e0) (em1 bs e0) (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%and9.i", .int 64 (em2 bs e0 &&& em1 bs e0)) :: ie3 env bs e0) s = withEnv (ie4 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or10.i" "%and9.i" "%e.0.i" (em3 bs e0) e0 (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%or10.i", .int 64 (em3 bs e0 ||| e0)) :: ie4 env bs e0) s = withEnv (ie5 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_shl64_two _ s "%shl11.i" "%or10.i" (em4 bs e0) (by ie_simp; lk))]
  rw [show withEnv (("%shl11.i", .int 64 (em4 bs e0 <<< 2)) :: ie5 env bs e0) s = withEnv (ie6 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and12.i" "%shl11.i" "%and7.i" (em5 bs e0) (em1 bs e0) (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%and12.i", .int 64 (em5 bs e0 &&& em1 bs e0)) :: ie6 env bs e0) s = withEnv (ie7 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_or64 _ s "%or13.i" "%and12.i" "%or10.i" (em6 bs e0) (em4 bs e0) (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%or13.i", .int 64 (em6 bs e0 ||| em4 bs e0)) :: ie7 env bs e0) s = withEnv (ie8 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_shl64_two _ s "%shl14.i" "%or13.i" (em7 bs e0) (by ie_simp; lk))]
  rw [show withEnv (("%shl14.i", .int 64 (em7 bs e0 <<< 2)) :: ie8 env bs e0) s = withEnv (ie9 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_xor64_neg_one _ s "%not16.i" "%or13.i" (em7 bs e0) (by ie_simp; lk))]
  rw [show withEnv (("%not16.i", .int 64 (em7 bs e0 ^^^ (-1))) :: ie9 env bs e0) s = withEnv (ie10 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%2" "%shl14.i" "%not16.i" (em8 bs e0) (em9 bs e0) (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%2", .int 64 (em8 bs e0 &&& em9 bs e0)) :: ie10 env bs e0) s = withEnv (ie11 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_and64 _ s "%and17.i" "%2" "%and7.i" (em10 bs e0) (em1 bs e0) (by ie_simp; lk) (by ie_simp; lk))]
  rw [show withEnv (("%and17.i", .int 64 (em10 bs e0 &&& em1 bs e0)) :: ie11 env bs e0) s = withEnv (ie12 env bs e0) s from rfl]
  rw [denoteCode_cons_of _ _ _ _ _ (b_icmp_eq64_imm _ s "%cmp.not.i" "%and17.i" (em11 bs e0) (BitVec.ofInt 64 0) (by ie_simp; lk))]
  rw [show withEnv (("%cmp.not.i", .int 1 (evalICmp .eq (em11 bs e0) (BitVec.ofInt 64 0))) :: ie12 env bs e0) s = withEnv (ie13 env bs e0) s from rfl]
  simp only [denoteCode, denoteRun, State.bindAll]

/-! ### The seed, as the three blocks compute it

`entry` forms `%and.i`, `if.then.i` the boundary select, and `if.end.i` reads one
of the two by the predecessor — exactly `escapeSeed`'s `select`.  The equality is
stated once here so the composition below can name the seed rather than the three
blocks' words. -/

theorem prevBackslashWord_toNat (b : Bool) :
    (prevBackslashWord b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- `escapeSeed`, in the form the three blocks compute: the run-start word, the
lane-0 test, and `if.then.i`'s select on the second carry word. -/
theorem seed_eq (bs : BitVec 64) (prevb prevs : Bool) :
    escapeSeed bs prevb prevs =
      (let aw := prevBackslashWord prevb
       let andI := bs &&& ((aw ||| (bs <<< 1)) ^^^ (-1))
       if ((bs &&& (BitVec.ofInt 64 1)) &&& aw) = (0 : BitVec 64) then andI
       else andI ||| ifThenCond bs (prevBackslashWord prevs)) := by
  cases prevb <;> cases prevs <;>
    simp [escapeSeed, ifThenCond, prevBackslashWord, ← xor_neg_one_eq_not,
      BitVec.or_comm]

/-! ### The seed blocks, as control steps

A state is named by its environment, the block it is in and the predecessor it
arrived from, so a block lemma's conclusion is the block the run is in next rather
than a record update the next lemma has to read through. -/

/-- A state at a block, with a predecessor. -/
def site (env : Env) (s : State) (pc : String) (pre : Option String) : State :=
  { s with env := env, pc := pc, pre := pre }

theorem site_pc (env : Env) (s : State) (pc : String) (pre : Option String) :
    (site env s pc pre).pc = pc := rfl

theorem site_pre (env : Env) (s : State) (pc : String) (pre : Option String) :
    (site env s pc pre).pre = pre := rfl

/-- The entry block's instruction run, at a state's block and predecessor. -/
theorem entry_denote' (env : Env) (s : State) (pc : String) (pre : Option String)
    (bs w0 : BitVec 64) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld : readBytes s.mem carry 8 = some (natToBytes w0.toNat 8)) :
    denoteCode escapeCalls lstEntry.instrs (site env s pc pre) =
      some (site (entryEnv env bs w0 carry) s pc pre) :=
  entry_denote env { s with pc := pc, pre := pre } bs w0 carry hbs hcarry hld

/-- The `if.then.i` run, at a state's block and predecessor. -/
theorem ifThen_denote' (env : Env) (s : State) (pc : String) (pre : Option String)
    (bs w1 andI : BitVec 64) (a : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (handI : lookupName env "%and.i" = some (.int 64 andI))
    (harr : lookupName env "%arrayidx1" = some (.ptr a))
    (hld : readBytes s.mem a 8 = some (natToBytes w1.toNat 8)) :
    denoteCode escapeCalls lstIfThen.instrs (site env s pc pre) =
      some (site (ifThenEnv env bs w1 andI) s pc pre) :=
  ifThen_denote env { s with pc := pc, pre := pre } bs w1 andI a hbs handI harr hld

/-- The `if.end.i` run, at a state's block and predecessor. -/
theorem ifEnd_denote' (env : Env) (s : State) (pc : String) (pre : Option String)
    (bs e0 : BitVec 64) (p : String) (op : Operand)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hshl : lookupName env "%shl.i" = some (.int 64 (bs <<< 1)))
    (hpre : pre = some p)
    (hinc : phiIncoming p [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")] = some op)
    (hop : evalOperand (site env s pc pre) op = some (.int 64 e0)) :
    denoteCode escapeCalls lstIfEnd.instrs (site env s pc pre) =
      some (site (ie13 env bs e0) s pc pre) := by
  exact ifEnd_denote env { s with pc := pc, pre := pre } bs e0 p op hbs hshl
    (by show pre = some p; exact hpre) hinc (by
      show evalOperand (withEnv env { s with pc := pc, pre := pre }) op = some (.int 64 e0)
      exact hop)

/-- The `entry` block's step: the run-start word and the lane-0 test decide which
block is next. -/
theorem entry_step (env : Env) (s : State) (pre : Option String) (bs w0 : BitVec 64)
    (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld : readBytes s.mem carry 8 = some (natToBytes w0.toNat 8)) :
    step escapeCalls escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs w0 carry) s
        (if ((bs &&& (BitVec.ofInt 64 1)) &&& w0) = (0 : BitVec 64)
          then "if.end.i" else "if.then.i")
        (some "entry")) := by
  have hbody := entry_denote' env s "entry" pre bs w0 carry hbs hcarry hld
  rw [step_of (site env s "entry" pre) "entry" lstEntry _ (by rfl) findBlock_entry hbody]
  rw [lstEntry_term]
  have hval : evalOperand (site (entryEnv env bs w0 carry) s "entry" pre) (.reg "%tobool.not.i") =
      some (.int 1 (evalICmp .eq ((bs &&& (BitVec.ofInt 64 1)) &&& w0) (BitVec.ofInt 64 0))) :=
    (entry_cells env bs w0 carry).2.2.2.1
  by_cases h0 : ((bs &&& (BitVec.ofInt 64 1)) &&& w0) = (0 : BitVec 64)
  · rw [execTerm_condbr_one _ _ _ _ _ hval ((evalICmp_eq_one_iff _ _).mpr h0)]
    rw [ite_eq_left h0]
    rfl
  · rw [execTerm_condbr_zero _ _ _ _ _ hval ((evalICmp_eq_zero_iff _ _).mpr h0)]
    rw [ite_eq_right h0]
    rfl

/-- The `if.then.i` block's step: `%or5.i` is the seed's taken arm. -/
theorem ifThen_step (env : Env) (s : State) (pre : Option String) (bs w1 andI : BitVec 64)
    (a : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (handI : lookupName env "%and.i" = some (.int 64 andI))
    (harr : lookupName env "%arrayidx1" = some (.ptr a))
    (hld : readBytes s.mem a 8 = some (natToBytes w1.toNat 8)) :
    step escapeCalls escapeListFunction (site env s "if.then.i" pre) =
      .jump (site (ifThenEnv env bs w1 andI) s "if.end.i" (some "if.then.i")) := by
  have hbody := ifThen_denote' env s "if.then.i" pre bs w1 andI a hbs handI harr hld
  rw [step_of (site env s "if.then.i" pre) "if.then.i" lstIfThen _ (by rfl) findBlock_ifThen hbody]
  rw [lstIfThen_term]
  rfl

/-- The `if.end.i` block's step, to either exit. -/
theorem ifEnd_step (env : Env) (s : State) (pre : Option String) (bs e0 : BitVec 64)
    (p : String) (op : Operand)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hshl : lookupName env "%shl.i" = some (.int 64 (bs <<< 1)))
    (hpre : pre = some p)
    (hinc : phiIncoming p [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")] = some op)
    (hop : evalOperand (site env s "if.end.i" pre) op = some (.int 64 e0)) :
    step escapeCalls escapeListFunction (site env s "if.end.i" pre) =
      .jump (site (ie13 env bs e0) s
        (if em11 bs e0 = (0 : BitVec 64) then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  have hbody := ifEnd_denote' env s "if.end.i" pre bs e0 p op hbs hshl hpre hinc hop
  rw [step_of (site env s "if.end.i" pre) "if.end.i" lstIfEnd _ (by rfl) findBlock_ifEnd hbody]
  rw [lstIfEnd_term]
  have hval : evalOperand (site (ie13 env bs e0) s "if.end.i" pre) (.reg "%cmp.not.i") =
      some (.int 1 (em12 bs e0)) := by
    show lookupName (ie13 env bs e0) "%cmp.not.i" = some (.int 1 (em12 bs e0))
    ie_simp; lk
  by_cases h0 : em11 bs e0 = (0 : BitVec 64)
  · rw [execTerm_condbr_one _ _ _ _ _ hval (by
      show evalICmp .eq (em11 bs e0) (BitVec.ofInt 64 0) = (1 : BitVec 1)
      exact (evalICmp_eq_one_iff _ _).mpr h0)]
    rw [ite_eq_left h0]
    rfl
  · rw [execTerm_condbr_zero _ _ _ _ _ hval (by
      show evalICmp .eq (em11 bs e0) (BitVec.ofInt 64 0) = (0 : BitVec 1)
      exact (evalICmp_eq_zero_iff _ _).mpr h0)]
    rw [ite_eq_right h0]
    rfl

/-! ### The seed's jump chain

The three blocks composed: `entry` always, `if.then.i` only when the lane-0 test
is set, then `if.end.i`.  A chain of jumps is stated with its length, because the
consumer's fuel term is the length plus its own. -/

/-- A chain of jumps, with its length. -/
inductive LRun (f : Function) : Nat → State → State → Prop
  | zero (s : State) : LRun f 0 s s
  | succ {n : Nat} {s s' t : State} :
      step escapeCalls f s = .jump s' → LRun f n s' t → LRun f (n + 1) s t

/-- Chains compose. -/
theorem LRun.comp {f : Function} :
    ∀ {a : Nat} {s t u : State}, LRun f a s t → LRun f b t u → LRun f (a + b) s u
  | 0, s, t, u, h1, h2 => by
      cases h1 with
      | zero => simpa using h2
  | a + 1, s, t, u, h1, h2 => by
      cases h1 with
      | succ hstep hrest =>
          rw [show a + 1 + b = (a + b) + 1 from by omega]
          exact LRun.succ hstep (LRun.comp hrest h2)

/-- A chain of jumps is a `runFuel` prefix. -/
theorem LRun.runFuel {f : Function} :
    ∀ {n : Nat} {s t : State}, LRun f n s t →
      ∀ m, runFuel escapeCalls (n + m) f s = runFuel escapeCalls m f t
  | 0, s, t, h, m => by cases h with | zero => rw [Nat.zero_add]
  | n + 1, s, t, h, m => by
      cases h with
      | succ hstep hrest =>
          rw [show n + 1 + m = (n + m) + 1 from by omega, runFuel_jump hstep,
            LRun.runFuel hrest m]

/-- Unfolding the environments the seed blocks build, so a lookup is again a walk
over conses. -/
macro "env_simp" : tactic => `(tactic|
  (simp only [entryEnv, ifThenEnv, ie13, ie12, ie11, ie10, ie9, ie8, ie7, ie6, ie5,
    ie4, ie3, ie2, ie1, ft3, List.zip_cons_cons, List.zip_nil_left, List.zip_nil_right,
    List.cons_append, List.nil_append]))

/-- The seed's value in the taken arm, out of `seed_eq`. -/
theorem seed_then_word (bs : BitVec 64) (prevb prevs : Bool)
    (hne : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) ≠ (0 : BitVec 64)) :
    ifThenCond bs (prevBackslashWord prevs) |||
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))) =
      escapeSeed bs prevb prevs := by
  rw [seed_eq, ite_eq_right hne, BitVec.or_comm]

/-- The seed's value in the untaken arm. -/
theorem seed_entry_word (bs : BitVec 64) (prevb prevs : Bool)
    (hz : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) = (0 : BitVec 64)) :
    bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)) =
      escapeSeed bs prevb prevs := by
  rw [seed_eq, ite_eq_left hz]

/-- The chain through `if.then.i`, when the lane-0 test is set. -/
theorem seed_then_run (env : Env) (s : State) (pre : Option String) (bs : BitVec 64)
    (prevb prevs : Bool) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld0 : readBytes s.mem carry 8 =
      some (natToBytes (prevBackslashWord prevb).toNat 8))
    (hld1 : readBytes s.mem (carry + 8) 8 =
      some (natToBytes (prevBackslashWord prevs).toNat 8))
    (hne : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) ≠ (0 : BitVec 64)) :
    LRun escapeListFunction 3 (site env s "entry" pre)
      (site (ie13 (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (prevBackslashWord prevs)
          (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
        bs (escapeSeed bs prevb prevs)) s
        (if em11 bs (escapeSeed bs prevb prevs) = (0 : BitVec 64)
          then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  have h1 : step escapeCalls escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.then.i"
        (some "entry")) := by
    rw [entry_step env s pre bs (prevBackslashWord prevb) carry hbs hcarry hld0,
      ite_eq_right hne]
  have h2 : step escapeCalls escapeListFunction
      (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.then.i"
        (some "entry")) =
      .jump (site (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (prevBackslashWord prevs)
          (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) s "if.end.i"
        (some "if.then.i")) :=
    ifThen_step (entryEnv env bs (prevBackslashWord prevb) carry) s (some "entry") bs
      (prevBackslashWord prevs)
      (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))) (carry + 8)
      (by env_simp; lk)
      (entry_cells env bs (prevBackslashWord prevb) carry).1
      (entry_cells env bs (prevBackslashWord prevb) carry).2.2.2.2 hld1
  refine LRun.succ h1 (LRun.succ h2 (LRun.succ ?_ (LRun.zero _)))
  rw [← seed_then_word bs prevb prevs hne]
  exact ifEnd_step
    (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
      (prevBackslashWord prevs) (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
    s (some "if.then.i") bs
    (ifThenCond bs (prevBackslashWord prevs) |||
      (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1))))
    "if.then.i" (.reg "%or5.i")
    (by env_simp; lk)
    (by env_simp; lk)
    rfl (by decide)
    (by
      show lookupName (ifThenEnv (entryEnv env bs (prevBackslashWord prevb) carry) bs
        (prevBackslashWord prevs)
        (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))) "%or5.i" = _
      env_simp; lk)

/-- The chain through `entry`, when the lane-0 test is clear. -/
theorem seed_entry_run (env : Env) (s : State) (pre : Option String) (bs : BitVec 64)
    (prevb prevs : Bool) (carry : Nat)
    (hbs : lookupName env "%bs" = some (.int 64 bs))
    (hcarry : lookupName env "%carry" = some (.ptr carry))
    (hld0 : readBytes s.mem carry 8 =
      some (natToBytes (prevBackslashWord prevb).toNat 8))
    (hz : ((bs &&& (BitVec.ofInt 64 1)) &&& prevBackslashWord prevb) = (0 : BitVec 64)) :
    LRun escapeListFunction 2 (site env s "entry" pre)
      (site (ie13 (entryEnv env bs (prevBackslashWord prevb) carry) bs
          (escapeSeed bs prevb prevs)) s
        (if em11 bs (escapeSeed bs prevb prevs) = (0 : BitVec 64)
          then "xl_lanes.exit" else "do.body.i")
        (some "if.end.i")) := by
  have h1 : step escapeCalls escapeListFunction (site env s "entry" pre) =
      .jump (site (entryEnv env bs (prevBackslashWord prevb) carry) s "if.end.i"
        (some "entry")) := by
    rw [entry_step env s pre bs (prevBackslashWord prevb) carry hbs hcarry hld0, ite_eq_left hz]
  refine LRun.succ h1 (LRun.succ ?_ (LRun.zero _))
  rw [← seed_entry_word bs prevb prevs hz]
  exact ifEnd_step (entryEnv env bs (prevBackslashWord prevb) carry) s (some "entry") bs
    (bs &&& ((prevBackslashWord prevb ||| (bs <<< 1)) ^^^ (-1)))
    "entry" (.reg "%and.i")
    (by env_simp; lk)
    (by env_simp; lk)
    rfl (by decide)
    (by
      show lookupName (entryEnv env bs (prevBackslashWord prevb) carry) "%and.i" = _
      env_simp; lk)

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.stepWord_fixed_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms stepWord_fixed_iff

/-- info: 'LeanLLVM.Refinement.entry_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_denote

/-- info: 'LeanLLVM.Refinement.entry_cells' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_cells

/-- info: 'LeanLLVM.Refinement.ifThen_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifThen_denote

/-- info: 'LeanLLVM.Refinement.ifEnd_denote' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_denote

/-- info: 'LeanLLVM.Refinement.seed_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_eq

/-- info: 'LeanLLVM.Refinement.em7_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms em7_eq

/-- info: 'LeanLLVM.Refinement.entry_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms entry_step

/-- info: 'LeanLLVM.Refinement.ifThen_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifThen_step

/-- info: 'LeanLLVM.Refinement.ifEnd_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ifEnd_step

/-- info: 'LeanLLVM.Refinement.seed_then_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_then_word

/-- info: 'LeanLLVM.Refinement.seed_entry_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_entry_word

/-- info: 'LeanLLVM.Refinement.seed_then_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_then_run

/-- info: 'LeanLLVM.Refinement.seed_entry_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms seed_entry_run

/-- info: 'LeanLLVM.Refinement.LRun.runFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LRun.runFuel

end LeanLLVM.Refinement
