/-
The two helper bodies `JsonStage2HelperIR` pins, proved of their contracts.

`JsonStage2HelperIR` pins `s2_value_pos`'s and `s2_after_value`'s emitted
`define` blocks to the ASTs they parse to.  This module takes the next step:
each body runs at the staging its `HelperContract` states, and its outcome
satisfies that contract's post and frame.

**The route.**  The bodies are short but branching, and the semantics' fuel
makes a `simp`-only evaluation of a whole block too costly.  Each block is
therefore one `denoteCode` chain over the emitters' environment builder
(`stateAt`/`cells` from `BlockEval`): one step lemma per instruction shape, then
`denoteCode_cons_of` per instruction, exactly as `BlockEval`'s header prescribes.
The `phi` in `s2_value_pos`'s `return` is `denoteCode_phiRun`'s leading run, so
its incoming operand is read at the state the edge delivered.  Each block is
then one `step` lemma, and the three (resp. two) control paths are compositions of
those steps read as run prefixes (`s2_runFuel_jump`, `s2_runFuel_ret`, joined by
`runFuel_prefix_trans`/`runFuel_prefix_some`); `execTerm`'s control forms are
`s2_execTerm_*`.

**What is proved.**  `s2ValuePosBody_contract` and `s2AfterValueBody_contract`
read the contract instances' own `pre`, `post` and `foot` — `s2ValuePosContract`
and `s2AfterValueContract` from `JsonStage2Helpers` — and produce the body's run,
its post and its frame at the same footprint; `*_satisfies` states that at the
instances' projections.  Nothing is restated or widened: the memory the body
leaves is the model's memory, and the byte `s2_after_value` writes is the
model's `UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)`, not merely a byte of the
same width (`s2_convBytes`).

**The byte plumbing.**  A `load i8` binds `b.toBitVec` where the
model reads the byte's `UInt8`, so the body's comparisons are stated at the
`BitVec` and the model's at the `UInt8`: `s2_bv8_eq_ofNat` transfers them one
immediate at a time, `s2_ofNat8_toNat` reads the loaded word's `toNat` as the
byte's, and `s2_and253_eq_zero_iff` transfers the `and i8, -3` test —
enumerated over the 256 values an eight-bit word admits by a kernel computation,
since `253` clears every bit but the second, with `s2_land253_pin` as the
enumeration's control and `s2_land253_pin_control` the discriminating one.  The
`i32` `-1` is `s2MinusOne_toNat` under a nonzero depth, and the `i64` index the
zero-extension produces is `s2TopIdx`.

**The fuel.**  The depth-zero arm of `s2_value_pos` finishes in three control
steps and the two other arms in four; the contract is stated at four for all
three, the zero arm by `runFuel_succ_some`.  `s2_after_value`'s two arms both
finish in three.
-/
import LeanLLVM.Refinement.JsonStage2HelperIR
import LeanLLVM.Refinement.BlockEval
import LeanLLVM.Refinement.JsonS1MasksIR

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonS1MasksIR

/-- Resolve a register read against the environment builder: peel the cells the
block bound, deciding each literal string equality with `lookupName_cons_ne`'s
own `decide`, and close with the cell the name is — by the hypothesis that states
it, when the read is one the caller supplies, or by reflexivity when the name is
one of the block's own.  Written as a tactic because the goal is one `if` per
cell, and the peeling is a rewrite per cell rather than a `simp` over the whole
environment: a `simp [lookupName]` duplicates the terms on both sides of each
`if`, and the goals here carry `BitVec.ofNat 64 (…).toNat` readings that make
that duplication cost gigabytes.

The peel comes *before* `assumption`, and that order is load-bearing: `assumption`
compares each candidate hypothesis' type with the goal definitionally, and on the
nine-cell environment of the depth-above-zero arms that comparison is what hits
`maximum recursion depth` — a limit raised to 200 000 does not move it, because
it is the comparison's own recursion rather than the elaborator's option.  At the
goal where it fired (the `%1` read of `s2_value_pos`'s `if.then3`) the bare
`rw [lookupName_cons_self]` closes it, so the peel-first order both avoids the
comparison and costs less. -/
macro "s2_lk" : tactic => `(tactic|
  (simp (config := { failIfUnchanged := false }) only [stateAt, evalOperand, cells]
   repeat rw [lookupName_cons_ne _ _ (by decide)]
   first
   | rw [lookupName_cons_self]
   | assumption
   | rfl))

/-! ### The blocks, found

`s2ValuePosBody.findBlock "entry"` is a closed computation — a literal block list
searched by name — so each lookup is a `decide`d equation rather than a `simp`
over the whole function.  The step lemmas below rewrite with the one they need,
which keeps the block resolution out of the simplifier: the whole-function
unfolding a full `simp` performs on a statement this size is what the memory
ceiling rejected. -/

theorem s2ValuePos_findBlock_entry :
    s2ValuePosBody.findBlock "entry" =
      some ⟨"entry",
        [Instr.icmp "%cmp" .eq 32 (.reg "%sp") (.imm (.int 32 0x00000000#32))],
        Term.condbr (.reg "%cmp") "if.then" "if.end"⟩ := by decide

theorem s2ValuePos_findBlock_ifThen :
    s2ValuePosBody.findBlock "if.then" =
      some ⟨"if.then",
        [Instr.icmp "%tobool.not" .eq 32 (.reg "%root_done")
          (.imm (.int 32 0x00000000#32))],
        Term.br "return"⟩ := by decide

theorem s2ValuePos_findBlock_ifEnd :
    s2ValuePosBody.findBlock "if.end" =
      some ⟨"if.end",
        [Instr.binop "%sub" .add 32 (.reg "%sp") (.imm (.int 32 0xffffffff#32)),
         Instr.zext "%idxprom" 32 64 (.reg "%sub"),
         Instr.gep "%arrayidx" (.int 8) (.reg "%ct") (.reg "%idxprom"),
         Instr.load "%0" (.int 8) (.reg "%arrayidx"),
         Instr.icmp "%cmp1" .eq 8 (.reg "%0") (.imm (.int 8 0x01#8)),
         Instr.gep "%arrayidx5" (.int 8) (.reg "%cs") (.reg "%idxprom"),
         Instr.load "%1" (.int 8) (.reg "%arrayidx5")],
        Term.condbr (.reg "%cmp1") "if.then3" "if.end9"⟩ := by decide

theorem s2ValuePos_findBlock_ifThen3 :
    s2ValuePosBody.findBlock "if.then3" =
      some ⟨"if.then3",
        [Instr.icmp "%cmp7" .eq 8 (.reg "%1") (.imm (.int 8 0x02#8))],
        Term.br "return"⟩ := by decide

theorem s2ValuePos_findBlock_ifEnd9 :
    s2ValuePosBody.findBlock "if.end9" =
      some ⟨"if.end9",
        [Instr.binop "%2" .and 8 (.reg "%1") (.imm (.int 8 0xfd#8)),
         Instr.icmp "%narrow" .eq 8 (.reg "%2") (.imm (.int 8 0x00#8))],
        Term.br "return"⟩ := by decide

theorem s2ValuePos_findBlock_return :
    s2ValuePosBody.findBlock "return" =
      some ⟨"return",
        [Instr.phi "%retval.1.in" (.int 1)
           [("if.then", .reg "%tobool.not"), ("if.then3", .reg "%cmp7"),
            ("if.end9", .reg "%narrow")],
         Instr.zext "%retval.1" 1 32 (.reg "%retval.1.in")],
        Term.ret (.int 32) (some (.reg "%retval.1"))⟩ := by decide

theorem s2AfterValue_findBlock_entry :
    s2AfterValueBody.findBlock "entry" =
      some ⟨"entry",
        [Instr.icmp "%cmp" .eq 32 (.reg "%sp.0.val") (.imm (.int 32 0x00000000#32))],
        Term.condbr (.reg "%cmp") "if.then" "if.end"⟩ := by decide

theorem s2AfterValue_findBlock_ifThen :
    s2AfterValueBody.findBlock "if.then" =
      some ⟨"if.then",
        [Instr.store (.int 32) (.imm (.int 32 0x00000001#32)) (.reg "%root_done")],
        Term.br "return"⟩ := by decide

theorem s2AfterValue_findBlock_ifEnd :
    s2AfterValueBody.findBlock "if.end" =
      some ⟨"if.end",
        [Instr.binop "%sub" .add 32 (.reg "%sp.0.val") (.imm (.int 32 0xffffffff#32)),
         Instr.zext "%idxprom" 32 64 (.reg "%sub"),
         Instr.gep "%arrayidx" (.int 8) (.reg "%ct") (.reg "%idxprom"),
         Instr.load "%0" (.int 8) (.reg "%arrayidx"),
         Instr.icmp "%cmp1" .eq 8 (.reg "%0") (.imm (.int 8 0x01#8)),
         Instr.select "%conv3" (.int 8) (.reg "%cmp1") (.imm (.int 8 0x03#8))
           (.imm (.int 8 0x01#8)),
         Instr.gep "%arrayidx5" (.int 8) (.reg "%cs") (.reg "%idxprom"),
         Instr.store (.int 8) (.reg "%conv3") (.reg "%arrayidx5")],
        Term.br "return"⟩ := by decide

theorem s2AfterValue_findBlock_return :
    s2AfterValueBody.findBlock "return" =
      some ⟨"return", [], Term.ret .void none⟩ := by decide

/-! ### One-instruction steps, at the environment builder -/

theorem s2_icmp_eq_imm_w (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.icmp d .eq w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int 1 (evalICmp .eq x c)) :: env) s) := by
  rw [evalInstr_icmp (calls := calls) (s := stateAt env s)
    (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of (stateAt env s) w c)]
  simp only [stateAt, State.bind]

theorem s2_add_imm_w (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .add w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x + c)) :: env) s) := by
  have hr : evalBinopNat BinOp.add w x.toNat c.toNat = some (x + c).toNat := by
    simp only [evalBinopNat, evalBinop, Option.map_some, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  rw [evalInstr_binop (calls := calls) (s := stateAt env s)
    (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of (stateAt env s) w c) (hr := hr)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, State.bind, stateAt]

theorem s2_and_imm_w (calls : Calls) (env : Env) (s : State)
    (d a : String) (w : Nat) {x c : BitVec w}
    (ha : lookupName env a = some (.int w x)) :
    evalInstr calls (stateAt env s) (.binop d .and w (.reg a) (.imm (.int w c))) =
      some (stateAt ((d, .int w (x &&& c)) :: env) s) := by
  have hr : evalBinopNat BinOp.and w x.toNat c.toNat = some (x &&& c).toNat := by
    simp only [evalBinopNat, evalBinop, Option.map_some, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  rw [evalInstr_binop (calls := calls) (s := stateAt env s)
    (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_lit_of (stateAt env s) w c) (hr := hr)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, State.bind, stateAt]

theorem s2_zext_w (calls : Calls) (env : Env) (s : State) (d v : String)
    (wIn wOut : Nat) {x : BitVec wIn}
    (hv : lookupName env v = some (.int wIn x)) :
    evalInstr calls (stateAt env s) (.zext d wIn wOut (.reg v)) =
      some (stateAt ((d, .int wOut (BitVec.ofNat wOut x.toNat)) :: env) s) := by
  rw [evalInstr_zext (calls := calls) (s := stateAt env s)
    (hv := evalOperand_reg_of env s v (.int wIn x) hv)]
  simp only [stateAt, State.bind]

theorem s2_gep8_64 (calls : Calls) (env : Env) (s : State) (d base off : String)
    {a : Nat} {idx : BitVec 64}
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr calls (stateAt env s) (.gep d (.int 8) (.reg base) (.reg off)) =
      some (stateAt ((d, .ptr (a + idx.toNat)) :: env) s) := by
  rw [evalInstr_gep_i8 (calls := calls) (s := stateAt env s)
    (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho) (hpos := by simpa using hpos)]
  simp only [stateAt, State.bind, BitVec.signExtend_eq]

theorem s2_load8 (calls : Calls) (env : Env) (s : State) (d p : String)
    {a : Nat} {b : UInt8}
    (hp : lookupName env p = some (.ptr a))
    (hb : readByte s.mem a = some b) :
    evalInstr calls (stateAt env s) (.load d (.int 8) (.reg p)) =
      some (stateAt ((d, .int 8 (b.toBitVec)) :: env) s) := by
  have hload : loadValue s.mem (.int 8) a = some (.int 8 b.toBitVec) := by
    rw [show b.toBitVec = BitVec.ofNat 8 b.toNat from (BitVec.ofNat_uInt8ToNat b).symm]
    simp only [loadValue, show ¬ (8 = 0) from by decide, ite_false]
    simp only [show (8 + 7) / 8 = 1 from rfl, readBytes, hb, bytesToNat,
      Nat.add_zero, Nat.mul_zero]
  rw [evalInstr_load (calls := calls) (s := stateAt env s)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by simpa only [stateAt] using hload)]
  simp only [stateAt, State.bind]

theorem s2_store8 (calls : Calls) (env : Env) (s : State) (v p : String)
    {x : BitVec 8} {a : Nat}
    (hv : lookupName env v = some (.int 8 x))
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 8) (.reg v) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
  have hs : storeValue (stateAt env s) (.int 8) (.int 8 x) a =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 1) }) := by
    simp [storeValue, show (8 + 7) / 8 = 1 from rfl, stateAt]
  rw [evalInstr_store (calls := calls) (s := stateAt env s) (vv := .int 8 x) (a := a)
    (hs := hs)
    (hv := evalOperand_reg_of env s v (.int 8 x) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]

theorem s2_store32_imm (calls : Calls) (env : Env) (s : State) (p : String)
    {x : BitVec 32} {a : Nat}
    (hp : lookupName env p = some (.ptr a)) :
    evalInstr calls (stateAt env s) (.store (.int 32) (.imm (.int 32 x)) (.reg p)) =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
  have hs : storeValue (stateAt env s) (.int 32) (.int 32 x) a =
      some (stateAt env { s with mem := writeBytes s.mem a (natToBytes x.toNat 4) }) := by
    simp [storeValue, show (32 + 7) / 8 = 4 from rfl, stateAt]
  rw [evalInstr_store (calls := calls) (s := stateAt env s) (vv := .int 32 x) (a := a)
    (hs := hs)
    (hv := evalOperand_lit_of (stateAt env s) 32 x)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)]

theorem s2_select8_bit (calls : Calls) (env : Env) (s : State) (d c : String)
    {bb : BitVec 1} (hc : lookupName env c = some (.int 1 bb)) :
    evalInstr calls (stateAt env s)
        (.select d (.int 8) (.reg c) (.imm (.int 8 0x03#8)) (.imm (.int 8 0x01#8))) =
      some (stateAt ((d, .int 8 (if bb = 1 then BitVec.ofNat 8 3 else BitVec.ofNat 8 1)) :: env) s) := by
  rcases bitVec1_eq_zero_or_one bb with h | h
  · subst h
    refine (evalInstr_select_false (hc := evalOperand_reg_of env s c (.int 1 (0 : BitVec 1)) hc)
      (ha := evalOperand_lit_of (stateAt env s) 8 (BitVec.ofNat 8 3))
      (hb := evalOperand_lit_of (stateAt env s) 8 (BitVec.ofNat 8 1))).trans ?_
    simp only [stateAt, State.bind]
    rfl
  · subst h
    refine (evalInstr_select_true (hc := evalOperand_reg_of env s c (.int 1 (1 : BitVec 1)) hc)
      (ha := evalOperand_lit_of (stateAt env s) 8 (BitVec.ofNat 8 3))
      (hb := evalOperand_lit_of (stateAt env s) 8 (BitVec.ofNat 8 1))).trans ?_
    simp only [stateAt, State.bind]
    rfl

/-! ### Control-flow steps -/

theorem s2_execTerm_condbr (s : State) (c t f : String) {bit : BitVec 1}
    (hc : lookupName s.env c = some (.int 1 bit)) :
    execTerm s (.condbr (.reg c) t f) =
      (if bit = 1 then .jump { s with pc := t, pre := some s.pc }
       else .jump { s with pc := f, pre := some s.pc }) := by
  simp only [execTerm, evalOperand, hc]
  rcases bitVec1_eq_zero_or_one bit with h | h <;> subst h <;> simp

theorem s2_execTerm_br (s : State) (dest : String) :
    execTerm s (.br dest) = .jump { s with pc := dest, pre := some s.pc } := rfl

theorem s2_execTerm_ret32 (s : State) (r : String) {v : BitVec 32}
    (hv : lookupName s.env r = some (.int 32 v)) :
    execTerm s (.ret (.int 32) (some (.reg r))) = .ret (some (.int 32 v)) s := by
  simp only [execTerm, evalOperand, hv]

theorem s2_execTerm_retVoid (s : State) :
    execTerm s (.ret .void none) = .ret none s := rfl

/-! ### A step, read as a run prefix

The arms below take four (three) control steps, and `runFuel`'s equation turns
each into a `match` on `step`.  Composing them as a single `runFuel` unfolding
chain puts the *whole* body state of every later step into the goal the next
`rw` has to reduce, and a `rw` that matches a state literal against a state
literal pays for the nine-cell environment it contains at every step.  Measured
on that form: one arm's closing chain peaked at 9.4 GB.

Stated as a prefix instead, each step is its own small equality — `runFuel` at
the step's fuel against `runFuel` at the continuation — so the composition meets
`runFuel k f t` and never a `match` over a run, and `runFuel_prefix_some` carries
the last step's outcome.  Measured on the same arm: 3 s and a 2.2 GB peak for the
module's whole elaboration (`/usr/bin/time`, `maxrss`), against the 9.4 GB peak
the unfolding chain was killed at; every arm was then restated this way, and the
two depth-zero arms with them. -/

/-- One control step, as a run prefix: the fuel is spent and the run continues at
the state the step jumped to, with the remaining fuel as a parameter so prefixes
compose through `runFuel_prefix_trans`. -/
theorem s2_runFuel_jump {calls : Calls} {f : Function} {s t : State}
    (h : step calls f s = .jump t) :
    ∀ k, runFuel calls (1 + k) f s = runFuel calls k f t := by
  intro k
  rw [show 1 + k = k + 1 from Nat.add_comm 1 k, runFuel.eq_2, h]

/-- The terminating step: one control step's `ret`, as a completed one-step run. -/
theorem s2_runFuel_ret {calls : Calls} {f : Function} {s s' : State} {v : Option Value}
    (h : step calls f s = .ret v s') : runFuel calls 1 f s = some (.ret v s'.mem) := by
  rw [show (1 : Nat) = 0 + 1 from rfl, runFuel.eq_2, h]

/-! ### The depth index and the byte tests -/

/-- The immediate the depth step adds: `-1` at `i32`. -/
abbrev s2MinusOne (sp : BitVec 32) : BitVec 32 := sp + 0xffffffff#32

/-- The top-container index the body computes: the `i32` difference
zero-extended to `i64` and read back. -/
abbrev s2TopIdx (sp : BitVec 32) : Nat := (BitVec.ofNat 64 (s2MinusOne sp).toNat).toNat

theorem s2MinusOne_toNat (sp : BitVec 32) (h : sp.toNat ≠ 0) :
    (s2MinusOne sp).toNat = sp.toNat - 1 := by
  show (sp + 0xffffffff#32).toNat = sp.toNat - 1
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hmod : 4294967295 % 2 ^ 32 = 4294967295 := by decide
  rw [hmod]
  have hlt := sp.isLt
  have hk : sp.toNat - 1 < 2 ^ 32 := by omega
  have hsum : (sp.toNat + 4294967295) = (2 ^ 32 + (sp.toNat - 1)) := by omega
  rw [hsum, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hk]

theorem s2TopIdx_lt (sp : BitVec 32) : s2TopIdx sp < 2 ^ 63 := by
  show (BitVec.ofNat 64 (s2MinusOne sp).toNat).toNat < 2 ^ 63
  rw [BitVec.toNat_ofNat]
  have hlt := (s2MinusOne sp).isLt
  have hmod : (s2MinusOne sp).toNat % 2 ^ 64 = (s2MinusOne sp).toNat :=
    Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  omega

theorem s2_ofBool_one {p : Prop} [Decidable p] :
    (BitVec.ofBool p = (1 : BitVec 1)) ↔ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

theorem s2_ofBool_zero {p : Prop} [Decidable p] :
    (BitVec.ofBool p = (0 : BitVec 1)) ↔ ¬ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

theorem s2_ofBool_toNat {p : Prop} [Decidable p] :
    (BitVec.ofBool p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

theorem s2_evalICmp_eq_toNat {w : Nat} (x c : BitVec w) :
    (evalICmp .eq x c).toNat = if x = c then 1 else 0 := by
  simp only [evalICmp, s2_ofBool_toNat]

theorem s2_evalICmp_eq_one {w : Nat} {x c : BitVec w} (h : x = c) :
    evalICmp .eq x c = 1 := by
  simp only [evalICmp]
  exact s2_ofBool_one.mpr h

theorem s2_evalICmp_eq_zero {w : Nat} {x c : BitVec w} (h : x ≠ c) :
    evalICmp .eq x c = 0 := by
  simp only [evalICmp]
  exact s2_ofBool_zero.mpr h

/-- An `i1` comparison's result is one exactly at the equality it tests. -/
theorem s2_evalICmp_eq_one_iff {w : Nat} (x c : BitVec w) :
    (evalICmp .eq x c = 1) ↔ x = c := by
  constructor
  · intro h
    by_contra hne
    rw [s2_evalICmp_eq_zero hne] at h
    exact absurd h (by decide)
  · intro h
    rw [h]
    exact s2_evalICmp_eq_one rfl

theorem s2_eq_zero_of_toNat {w : Nat} {x : BitVec w} (h : x.toNat = 0) : x = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [h]
  rfl

theorem s2_eq_zero_iff_toNat {w : Nat} (x : BitVec w) : (x = 0) ↔ x.toNat = 0 := by
  constructor
  · intro h; rw [h]; rfl
  · exact s2_eq_zero_of_toNat

/-- An eight-bit word is the immediate `n` exactly when its value is, for `n` below
the width's bound: the modulus `BitVec.ofNat` applies leaves the value alone. -/
theorem s2_bv8_eq_ofNat {n : Nat} (hn : n < 2 ^ 8) (x : BitVec 8) :
    (x = BitVec.ofNat 8 n) ↔ x.toNat = n := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

set_option maxRecDepth 100000 in
/-- The mask `253` is every bit but the second, so an eight-bit value meets it in
zero exactly when the value is `0` or `2`.  Enumerated over the 256 values the
width admits; the pin is a kernel computation, not a `decide` on the variable. -/
theorem s2_land253_pin :
    (List.range 256).all (fun a => decide ((a &&& 253 = 0) ↔ (a = 0 ∨ a = 2))) = true := by
  decide

set_option maxRecDepth 100000 in
/-- The same enumeration at a reading that does not hold, so the pin above is not
a search that accepts anything. -/
theorem s2_land253_pin_control :
    (List.range 256).all (fun a => decide ((a &&& 253 = 0) ↔ (a = 0 ∨ a = 4))) = false := by
  decide

theorem s2_land253 {a : Nat} (ha : a < 256) :
    (a &&& 253 = 0) ↔ a = 0 ∨ a = 2 := by
  have hall := List.all_eq_true.mp s2_land253_pin
  have h := hall a (List.mem_range.mpr ha)
  exact of_decide_eq_true h

theorem s2_and253_eq_zero_iff (b : BitVec 8) :
    (b &&& 0xfd#8 = 0) ↔ b.toNat = 0 ∨ b.toNat = 2 := by
  have htoNat : (b &&& 0xfd#8).toNat = b.toNat &&& 253 := by
    show (b &&& BitVec.ofNat 8 253).toNat = b.toNat &&& 253
    rw [BitVec.toNat_and]
    rfl
  rw [s2_eq_zero_iff_toNat, htoNat]
  exact s2_land253 (by have := b.isLt; omega)

/-! ### `s2_value_pos`: the entry block -/

theorem s2ValuePos_entry_denote {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hsp : lookupName env "%sp" = some (.int 32 sp)) :
    denoteCode calls
        [Instr.icmp "%cmp" .eq 32 (.reg "%sp") (.imm (.int 32 0x00000000#32))]
        (stateAt env s) =
      some (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls env s "%cmp" "%sp" 32 hsp)]
  rfl

theorem s2ValuePos_step_entry {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp" = some (.int 32 sp)) :
    step calls s2ValuePosBody (stateAt env s) =
      (if evalICmp .eq sp 0x00000000#32 = 1
       then .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
              { s with pc := "if.then", pre := some "entry" })
       else .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
              { s with pc := "if.end", pre := some "entry" })) := by
  have hpc' : (stateAt env s).pc = "entry" := hpc
  have hden := s2ValuePos_entry_denote (calls := calls) (env := env) (s := s) hsp
  simp only [step, hpc', s2ValuePos_findBlock_entry]
  rw [hden]
  change execTerm (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s)
      (Term.condbr (.reg "%cmp") "if.then" "if.end") = _
  rw [s2_execTerm_condbr (bit := evalICmp .eq sp 0x00000000#32)
    (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s)
    "%cmp" "if.then" "if.end" (by s2_lk)]
  simp only [stateAt, hpc]

/-! ### `s2_value_pos`: the branch blocks -/

theorem s2ValuePos_ifThen_denote {calls : Calls} {env : Env} {s : State}
    {rd : BitVec 32} (hrd : lookupName env "%root_done" = some (.int 32 rd)) :
    denoteCode calls
        [Instr.icmp "%tobool.not" .eq 32 (.reg "%root_done") (.imm (.int 32 0x00000000#32))]
        (stateAt env s) =
      some (stateAt (("%tobool.not", .int 1 (evalICmp .eq rd 0x00000000#32)) :: env) s) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls env s "%tobool.not" "%root_done" 32 hrd)]
  rfl

theorem s2ValuePos_ifThen3_denote {calls : Calls} {env : Env} {s : State}
    {csv : UInt8} (h1 : lookupName env "%1" = some (.int 8 (csv.toBitVec))) :
    denoteCode calls
        [Instr.icmp "%cmp7" .eq 8 (.reg "%1") (.imm (.int 8 0x02#8))]
        (stateAt env s) =
      some (stateAt
        (("%cmp7", .int 1 (evalICmp .eq (csv.toBitVec) 0x02#8)) :: env) s) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls env s "%cmp7" "%1" 8 h1)]
  rfl

theorem s2ValuePos_ifEnd9_denote {calls : Calls} {env : Env} {s : State}
    {csv : UInt8} (h1 : lookupName env "%1" = some (.int 8 (csv.toBitVec))) :
    denoteCode calls
        [Instr.binop "%2" .and 8 (.reg "%1") (.imm (.int 8 0xfd#8)),
         Instr.icmp "%narrow" .eq 8 (.reg "%2") (.imm (.int 8 0x00#8))]
        (stateAt env s) =
      some (stateAt
        (("%narrow", .int 1 (evalICmp .eq (csv.toBitVec &&& 0xfd#8) 0x00#8)) ::
          ("%2", .int 8 (csv.toBitVec &&& 0xfd#8)) :: env) s) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_and_imm_w calls env s "%2" "%1" 8 h1)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls (("%2", .int 8 (csv.toBitVec &&& 0xfd#8)) :: env) s
      "%narrow" "%2" 8 (x := csv.toBitVec &&& 0xfd#8) (by s2_lk))]
  rfl

theorem s2ValuePos_ifEnd_denote {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv csv : UInt8}
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv)
    (hcsv : readByte s.mem (cs + s2TopIdx sp) = some csv) :
    denoteCode calls
        [Instr.binop "%sub" .add 32 (.reg "%sp") (.imm (.int 32 0xffffffff#32)),
         Instr.zext "%idxprom" 32 64 (.reg "%sub"),
         Instr.gep "%arrayidx" (.int 8) (.reg "%ct") (.reg "%idxprom"),
         Instr.load "%0" (.int 8) (.reg "%arrayidx"),
         Instr.icmp "%cmp1" .eq 8 (.reg "%0") (.imm (.int 8 0x01#8)),
         Instr.gep "%arrayidx5" (.int 8) (.reg "%cs") (.reg "%idxprom"),
         Instr.load "%1" (.int 8) (.reg "%arrayidx5")]
        (stateAt env s) =
      some (stateAt
        (("%1", .int 8 (csv.toBitVec)) ::
          ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
          ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
          ("%0", .int 8 (ctv.toBitVec)) ::
          ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
          ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
          ("%sub", .int 32 (s2MinusOne sp)) :: env) s) := by
  have hpos : (BitVec.ofNat 64 (s2MinusOne sp).toNat).toNat < 2 ^ 63 := s2TopIdx_lt sp
  have e1 : lookupName env "%sp" = some (.int 32 sp) := hsp
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_add_imm_w calls env s "%sub" "%sp" 32 e1)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_zext_w calls _ s "%idxprom" "%sub" 32 64 (by s2_lk))]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_gep8_64 calls _ s "%arrayidx" "%ct" "%idxprom" (by s2_lk)
      (by s2_lk) hpos)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_load8 calls _ s "%0" "%arrayidx" (by s2_lk) hctv)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls _ s "%cmp1" "%0" 8 (by s2_lk))]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_gep8_64 calls _ s "%arrayidx5" "%cs" "%idxprom" (by s2_lk)
      (by s2_lk) hpos)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_load8 calls _ s "%1" "%arrayidx5" (by s2_lk) hcsv)]
  rfl

/-! ### `s2_value_pos`: the blocks that jump, and the return -/

theorem s2ValuePos_return_denote {calls : Calls} {env : Env} {s : State}
    {pred : String} {op : Operand} {v : BitVec 1}
    (hpre : s.pre = some pred)
    (hinc : phiIncoming pred
      [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
       ("if.end9", Operand.reg "%narrow")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 1 v)) :
    denoteCode calls
        [Instr.phi "%retval.1.in" (.int 1)
           [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
            ("if.end9", Operand.reg "%narrow")],
         Instr.zext "%retval.1" 1 32 (.reg "%retval.1.in")]
        (stateAt env s) =
      some (stateAt
        (("%retval.1", .int 32 (BitVec.ofNat 32 v.toNat)) ::
          ("%retval.1.in", .int 1 v) :: env) s) := by
  have hsel : PhiSelects (stateAt env s) pred
      [⟨"%retval.1.in", .int 1,
         [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
          ("if.end9", Operand.reg "%narrow")]⟩]
      [("%retval.1.in", .int 1 v)] :=
    PhiSelects.cons hinc hop PhiSelects.nil
  have hsplit :
      [Instr.phi "%retval.1.in" (.int 1)
         [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
          ("if.end9", Operand.reg "%narrow")],
       Instr.zext "%retval.1" 1 32 (.reg "%retval.1.in")] =
      List.map PhiSpec.instr
          [⟨"%retval.1.in", .int 1,
             [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
              ("if.end9", Operand.reg "%narrow")]⟩] ++
        [Instr.zext "%retval.1" 1 32 (.reg "%retval.1.in")] := rfl
  rw [hsplit]
  rw [denoteCode_phiRun (s := stateAt env s) (p := pred)
    (specs := [⟨"%retval.1.in", .int 1,
        [("if.then", Operand.reg "%tobool.not"),
          ("if.then3", Operand.reg "%cmp7"), ("if.end9", Operand.reg "%narrow")]⟩])
    (vs := [("%retval.1.in", .int 1 v)])
    (rest := [Instr.zext "%retval.1" 1 32 (.reg "%retval.1.in")]) hpre hsel (by rfl)]
  rw [show (stateAt env s).bindAll [("%retval.1.in", .int 1 v)]
      = stateAt (("%retval.1.in", .int 1 v) :: env) s from rfl]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_zext_w calls (("%retval.1.in", .int 1 v) :: env) s "%retval.1" "%retval.1.in"
      1 32 (by s2_lk))]
  rfl

theorem s2ValuePos_step_ifThen {calls : Calls} {env : Env} {s : State}
    {rd : BitVec 32} (hpc : s.pc = "if.then")
    (hrd : lookupName env "%root_done" = some (.int 32 rd)) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt (("%tobool.not", .int 1 (evalICmp .eq rd 0x00000000#32)) :: env)
        { s with pc := "return", pre := some "if.then" }) := by
  have hpc' : (stateAt env s).pc = "if.then" := hpc
  have hden := s2ValuePos_ifThen_denote (calls := calls) (env := env) (s := s) hrd
  simp only [step, hpc', s2ValuePos_findBlock_ifThen]
  rw [hden]
  change execTerm (stateAt (("%tobool.not", .int 1 (evalICmp .eq rd 0x00000000#32)) :: env) s)
      (Term.br "return") = _
  rw [s2_execTerm_br]
  simp only [stateAt, hpc]

theorem s2ValuePos_step_ifThen3 {calls : Calls} {env : Env} {s : State}
    {csv : UInt8} (hpc : s.pc = "if.then3")
    (h1 : lookupName env "%1" = some (.int 8 (csv.toBitVec))) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt
        (("%cmp7", .int 1 (evalICmp .eq (csv.toBitVec) 0x02#8)) :: env)
        { s with pc := "return", pre := some "if.then3" }) := by
  have hpc' : (stateAt env s).pc = "if.then3" := hpc
  have hden := s2ValuePos_ifThen3_denote (calls := calls) (env := env) (s := s) h1
  simp only [step, hpc', s2ValuePos_findBlock_ifThen3]
  rw [hden]
  change execTerm (stateAt (("%cmp7", .int 1 (evalICmp .eq (csv.toBitVec) 0x02#8))
      :: env) s) (Term.br "return") = _
  rw [s2_execTerm_br]
  simp only [stateAt, hpc]

theorem s2ValuePos_step_ifEnd9 {calls : Calls} {env : Env} {s : State}
    {csv : UInt8} (hpc : s.pc = "if.end9")
    (h1 : lookupName env "%1" = some (.int 8 (csv.toBitVec))) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt
        (("%narrow", .int 1 (evalICmp .eq (csv.toBitVec &&& 0xfd#8) 0x00#8)) ::
          ("%2", .int 8 (csv.toBitVec &&& 0xfd#8)) :: env)
        { s with pc := "return", pre := some "if.end9" }) := by
  have hpc' : (stateAt env s).pc = "if.end9" := hpc
  have hden := s2ValuePos_ifEnd9_denote (calls := calls) (env := env) (s := s) h1
  simp only [step, hpc', s2ValuePos_findBlock_ifEnd9]
  rw [hden]
  change execTerm (stateAt
      (("%narrow", .int 1 (evalICmp .eq (csv.toBitVec &&& 0xfd#8) 0x00#8)) ::
        ("%2", .int 8 (csv.toBitVec &&& 0xfd#8)) :: env) s)
      (Term.br "return") = _
  rw [s2_execTerm_br]
  simp only [stateAt, hpc]

theorem s2ValuePos_step_ifEnd {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv csv : UInt8} (hpc : s.pc = "if.end")
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv)
    (hcsv : readByte s.mem (cs + s2TopIdx sp) = some csv) :
    step calls s2ValuePosBody (stateAt env s) =
      (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
       then .jump (stateAt
         (("%1", .int 8 (csv.toBitVec)) ::
           ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
           ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
           ("%0", .int 8 (ctv.toBitVec)) ::
           ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
           ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
           ("%sub", .int 32 (s2MinusOne sp)) :: env)
         { s with pc := "if.then3", pre := some "if.end" })
       else .jump (stateAt
         (("%1", .int 8 (csv.toBitVec)) ::
           ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
           ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
           ("%0", .int 8 (ctv.toBitVec)) ::
           ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
           ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
           ("%sub", .int 32 (s2MinusOne sp)) :: env)
         { s with pc := "if.end9", pre := some "if.end" })) := by
  have hpc' : (stateAt env s).pc = "if.end" := hpc
  have hden := s2ValuePos_ifEnd_denote (calls := calls) (env := env) (s := s)
    hsp hct hcs hctv hcsv
  let OUT : Env := ("%1", .int 8 (csv.toBitVec)) ::
      ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) :: env
  have hden' : denoteCode calls
      [Instr.binop "%sub" .add 32 (.reg "%sp") (.imm (.int 32 0xffffffff#32)),
       Instr.zext "%idxprom" 32 64 (.reg "%sub"),
       Instr.gep "%arrayidx" (.int 8) (.reg "%ct") (.reg "%idxprom"),
       Instr.load "%0" (.int 8) (.reg "%arrayidx"),
       Instr.icmp "%cmp1" .eq 8 (.reg "%0") (.imm (.int 8 0x01#8)),
       Instr.gep "%arrayidx5" (.int 8) (.reg "%cs") (.reg "%idxprom"),
       Instr.load "%1" (.int 8) (.reg "%arrayidx5")]
      (stateAt env s) = some (stateAt OUT s) := hden
  simp only [step, hpc', s2ValuePos_findBlock_ifEnd]
  rw [hden']
  change execTerm (stateAt OUT s) (Term.condbr (.reg "%cmp1") "if.then3" "if.end9") = _
  rw [s2_execTerm_condbr (bit := evalICmp .eq (ctv.toBitVec) 0x01#8)
    (stateAt OUT s) "%cmp1" "if.then3" "if.end9" (by simp only [OUT]; s2_lk)]
  simp only [stateAt, hpc]
  rfl

theorem s2ValuePos_step_return {calls : Calls} {env : Env} {s : State}
    {pred : String} {op : Operand} {v : BitVec 1} (hpc : s.pc = "return")
    (hpre : s.pre = some pred)
    (hinc : phiIncoming pred
      [("if.then", Operand.reg "%tobool.not"), ("if.then3", Operand.reg "%cmp7"),
       ("if.end9", Operand.reg "%narrow")] = some op)
    (hop : evalOperand (stateAt env s) op = some (.int 1 v)) :
    step calls s2ValuePosBody (stateAt env s) =
      .ret (some (.int 32 (BitVec.ofNat 32 v.toNat)))
        (stateAt
          (("%retval.1", .int 32 (BitVec.ofNat 32 v.toNat)) ::
            ("%retval.1.in", .int 1 v) :: env) s) := by
  have hpc' : (stateAt env s).pc = "return" := hpc
  have hden := s2ValuePos_return_denote (calls := calls) (env := env) (s := s)
    hpre hinc hop
  simp only [step, hpc', s2ValuePos_findBlock_return]
  rw [hden]
  change execTerm (stateAt
      (("%retval.1", .int 32 (BitVec.ofNat 32 v.toNat)) ::
        ("%retval.1.in", .int 1 v) :: env) s)
      (Term.ret (.int 32) (some (.reg "%retval.1"))) = _
  rw [s2_execTerm_ret32
    (s := stateAt (("%retval.1", .int 32 (BitVec.ofNat 32 v.toNat)) ::
      ("%retval.1.in", .int 1 v) :: env) s)
    (r := "%retval.1") (v := BitVec.ofNat 32 v.toNat) (by s2_lk)]

theorem s2_ofNat8_toNat (q : UInt8) : (q.toBitVec : BitVec 8).toNat = q.toNat :=
  UInt8.toNat_toBitVec q

/-- The depth test's `i1` comparison, read at the model's condition: `sp` is zero
exactly when its value is. -/
theorem s2_ite_zero32 (rd : BitVec 32) :
    (if rd = 0#32 then (1 : Nat) else 0) = if rd.toNat = 0 then 1 else 0 := by
  by_cases h : rd = 0#32
  · rw [ite_eq_left h, ite_eq_left ((s2_eq_zero_iff_toNat rd).mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h ((s2_eq_zero_iff_toNat rd).mpr hh))]

/-- An eight-bit comparison with the immediate `1`, read at the model's condition. -/
theorem s2_ite_one8 (b : BitVec 8) :
    (if b = 1#8 then (1 : Nat) else 0) = if b.toNat = 1 then 1 else 0 := by
  by_cases h : b = 1#8
  · rw [ite_eq_left h, ite_eq_left (by rw [h]; rfl)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (by rw [← BitVec.toNat_inj]; simpa using hh))]

/-- An eight-bit comparison with the immediate `2`, read at the model's condition. -/
theorem s2_ite_two8 (b : BitVec 8) :
    (if b = 2#8 then (1 : Nat) else 0) = if b.toNat = 2 then 1 else 0 := by
  by_cases h : b = 2#8
  · rw [ite_eq_left h, ite_eq_left (by rw [h]; rfl)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (by rw [← BitVec.toNat_inj]; simpa using hh))]

/-- The `and i8, -3` test's `i1` comparison, read at the model's condition: the
mask clears every bit but the second, so the word meets it in zero exactly at the
two values the second arm accepts. -/
theorem s2_ite_mask8 (b : BitVec 8) :
    (if b &&& 0xfd#8 = 0x00#8 then (1 : Nat) else 0) =
      if b.toNat = 0 ∨ b.toNat = 2 then 1 else 0 := by
  have hiff : (b &&& 0xfd#8 = 0x00#8) ↔ b.toNat = 0 ∨ b.toNat = 2 := by
    simpa using s2_and253_eq_zero_iff b
  by_cases h : b &&& 0xfd#8 = 0x00#8
  · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h (hiff.mpr hh))]

/-- The word `s2_value_pos` returns at depth zero: the body's `zext` of the root
test, read at the model's `if root_done = 0 then 1 else 0`. -/
theorem s2_res_zero32 (rd : BitVec 32) :
    BitVec.ofNat 32 (evalICmp .eq rd 0x00000000#32).toNat =
      BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0) := by
  rw [s2_evalICmp_eq_toNat, s2_ite_zero32]

/-- The word `s2_value_pos` returns on the object arm: the body's `zext` of the
container byte's test, read at the model's `if csv = 2 then 1 else 0`. -/
theorem s2_res_two8 (b : BitVec 8) :
    BitVec.ofNat 32 (evalICmp .eq b 0x02#8).toNat =
      BitVec.ofNat 32 (if b.toNat = 2 then 1 else 0) := by
  rw [s2_evalICmp_eq_toNat, s2_ite_two8]

/-- The word `s2_value_pos` returns on the array arm: the body's `zext` of the
`and i8, -3` test, read at the model's two accepted byte values. -/
theorem s2_res_mask8 (b : BitVec 8) :
    BitVec.ofNat 32 (evalICmp .eq (b &&& 0xfd#8) 0x00#8).toNat =
      BitVec.ofNat 32 (if b.toNat = 0 ∨ b.toNat = 2 then 1 else 0) := by
  rw [s2_evalICmp_eq_toNat, s2_ite_mask8]


/-! ### `s2_value_pos`: the resolved branch steps -/

theorem s2ValuePos_step_entry_then {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hbit : evalICmp .eq sp 0x00000000#32 = 1) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
        { s with pc := "if.then", pre := some "entry" }) := by
  rw [s2ValuePos_step_entry hpc hsp]
  simp only [hbit]
  rw [ite_eq_left trivial]

theorem s2ValuePos_step_entry_end {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hbit : evalICmp .eq sp 0x00000000#32 = 0) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
        { s with pc := "if.end", pre := some "entry" }) := by
  rw [s2ValuePos_step_entry hpc hsp]
  simp only [hbit]
  rw [ite_eq_right (by decide)]

theorem s2ValuePos_step_ifEnd_then3 {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv csv : UInt8} (hpc : s.pc = "if.end")
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv)
    (hcsv : readByte s.mem (cs + s2TopIdx sp) = some csv)
    (hbit : evalICmp .eq (ctv.toBitVec) 0x01#8 = 1) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt
        (("%1", .int 8 (csv.toBitVec)) ::
          ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
          ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
          ("%0", .int 8 (ctv.toBitVec)) ::
          ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
          ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
          ("%sub", .int 32 (s2MinusOne sp)) :: env)
        { s with pc := "if.then3", pre := some "if.end" }) := by
  rw [s2ValuePos_step_ifEnd hpc hsp hct hcs hctv hcsv]
  simp only [hbit]
  rw [ite_eq_left trivial]

theorem s2ValuePos_step_ifEnd_end9 {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv csv : UInt8} (hpc : s.pc = "if.end")
    (hsp : lookupName env "%sp" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv)
    (hcsv : readByte s.mem (cs + s2TopIdx sp) = some csv)
    (hbit : evalICmp .eq (ctv.toBitVec) 0x01#8 = 0) :
    step calls s2ValuePosBody (stateAt env s) =
      .jump (stateAt
        (("%1", .int 8 (csv.toBitVec)) ::
          ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
          ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
          ("%0", .int 8 (ctv.toBitVec)) ::
          ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
          ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
          ("%sub", .int 32 (s2MinusOne sp)) :: env)
        { s with pc := "if.end9", pre := some "if.end" }) := by
  rw [s2ValuePos_step_ifEnd hpc hsp hct hcs hctv hcsv]
  simp only [hbit]
  rw [ite_eq_right (by decide)]

/-! ### `s2_value_pos`: the three arms' runs

`sp.toNat = 0`: the root test.  The entry test is taken, its `icmp` result is the
`phi`'s incoming value, and the run leaves the caller's memory alone. -/
theorem s2ValuePos_run_zero {sp rd : BitVec 32} {ct cs : Nat} {mem : Mem} {next : Nat}
    (hsp : sp.toNat = 0) :
    runFuel s2HelperCalls 3 s2ValuePosBody
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) =
      some (.ret (some (.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)))) mem) := by
  have hbit : evalICmp .eq sp 0x00000000#32 = 1 :=
    s2_evalICmp_eq_one (s2_eq_zero_of_toNat hsp)
  have h0 : (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
      = stateAt (cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
          ("%cs", .ptr cs)] [])
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) := rfl
  rw [h0]
  have h1 := s2ValuePos_step_entry_then (calls := s2HelperCalls)
    (env := cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
      ("%cs", .ptr cs)] [])
    (s := stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
    rfl (by s2_lk) hbit
  have h2 := s2ValuePos_step_ifThen (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "if.then", pre := some "entry" }) rfl (by s2_lk)
  have h3 := s2ValuePos_step_return (calls := s2HelperCalls)
    (env := ("%tobool.not", .int 1 (evalICmp .eq rd 0x00000000#32)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "return", pre := some "if.then" })
    (pred := "if.then") (op := Operand.reg "%tobool.not")
    (v := evalICmp .eq rd 0x00000000#32) rfl rfl (by simp [phiIncoming])
    (by s2_lk)
  have s1 := s2_runFuel_jump h1
  have s2 := s2_runFuel_jump h2
  have s3 := s2_runFuel_ret h3
  have hs := runFuel_prefix_some (runFuel_prefix_trans s1 s2) s3
  refine hs.trans ?_
  rw [s2_res_zero32]
  rfl

theorem s2TopIdx_eq (sp : BitVec 32) : s2TopIdx sp = (s2MinusOne sp).toNat := by
  show (BitVec.ofNat 64 (s2MinusOne sp).toNat).toNat = (s2MinusOne sp).toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by have := (s2MinusOne sp).isLt; omega)

/-! ### `s2_value_pos`: the two depth-above-zero arms -/

theorem s2ValuePos_run_object {sp rd : BitVec 32} {ct cs : Nat} {mem : Mem} {next : Nat}
    {ctv csv : UInt8} (hsp : sp.toNat ≠ 0)
    (hctv : readByte mem (ct + (sp.toNat - 1)) = some ctv)
    (hcsv : readByte mem (cs + (sp.toNat - 1)) = some csv)
    (hctv1 : ctv.toNat = 1) :
    runFuel s2HelperCalls 4 s2ValuePosBody
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) =
      some (.ret (some (.int 32 (BitVec.ofNat 32 (if csv.toNat = 2 then 1 else 0)))) mem) := by
  have hne : sp ≠ 0 := fun h => hsp ((s2_eq_zero_iff_toNat sp).mp h)
  have hbit0 : evalICmp .eq sp 0x00000000#32 = 0 := s2_evalICmp_eq_zero hne
  have hctv' : readByte mem (ct + s2TopIdx sp) = some ctv := by
    rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp]; exact hctv
  have hcsv' : readByte mem (cs + s2TopIdx sp) = some csv := by
    rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp]; exact hcsv
  have hbit1 : evalICmp .eq ctv.toBitVec 0x01#8 = 1 := by
    refine s2_evalICmp_eq_one ?_
    exact (s2_bv8_eq_ofNat (n := 1) (by decide) ctv.toBitVec).mpr
      (by simpa using hctv1)
  have h0 : (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
      = stateAt (cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
          ("%cs", .ptr cs)] [])
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) := rfl
  rw [h0]
  have h1 := s2ValuePos_step_entry_end (calls := s2HelperCalls)
    (env := cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
      ("%cs", .ptr cs)] [])
    (s := stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
    rfl (by s2_lk) hbit0
  have h2 := s2ValuePos_step_ifEnd_then3 (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "if.end", pre := some "entry" })
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hctv' hcsv' hbit1
  have h3 := s2ValuePos_step_ifThen3 (calls := s2HelperCalls)
    (env := ("%1", .int 8 (csv.toBitVec)) ::
      ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "if.then3", pre := some "if.end" })
    rfl (by s2_lk)
  have h4 := s2ValuePos_step_return (calls := s2HelperCalls)
    (env := ("%cmp7", .int 1 (evalICmp .eq (csv.toBitVec) 0x02#8)) ::
      ("%1", .int 8 (csv.toBitVec)) ::
      ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "return", pre := some "if.then3" })
    (pred := "if.then3") (op := Operand.reg "%cmp7")
    (v := evalICmp .eq (csv.toBitVec) 0x02#8) rfl rfl (by simp [phiIncoming])
    (by s2_lk)
  have s1 := s2_runFuel_jump h1
  have s2 := s2_runFuel_jump h2
  have s3 := s2_runFuel_jump h3
  have s4 := s2_runFuel_ret h4
  have hs := runFuel_prefix_some
    (runFuel_prefix_trans (runFuel_prefix_trans s1 s2) s3) s4
  rw [h0]
  refine hs.trans ?_
  rw [s2_res_two8, s2_ofNat8_toNat]
  rfl

theorem s2ValuePos_run_array {sp rd : BitVec 32} {ct cs : Nat} {mem : Mem} {next : Nat}
    {ctv csv : UInt8} (hsp : sp.toNat ≠ 0)
    (hctv : readByte mem (ct + (sp.toNat - 1)) = some ctv)
    (hcsv : readByte mem (cs + (sp.toNat - 1)) = some csv)
    (hctv1 : ctv.toNat ≠ 1) :
    runFuel s2HelperCalls 4 s2ValuePosBody
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) =
      some (.ret (some (.int 32 (BitVec.ofNat 32
        (if csv.toNat = 0 ∨ csv.toNat = 2 then 1 else 0)))) mem) := by
  have hne : sp ≠ 0 := fun h => hsp ((s2_eq_zero_iff_toNat sp).mp h)
  have hbit0 : evalICmp .eq sp 0x00000000#32 = 0 := s2_evalICmp_eq_zero hne
  have hctv' : readByte mem (ct + s2TopIdx sp) = some ctv := by
    rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp]; exact hctv
  have hcsv' : readByte mem (cs + s2TopIdx sp) = some csv := by
    rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp]; exact hcsv
  have hbit1 : evalICmp .eq ctv.toBitVec 0x01#8 = 0 := by
    refine s2_evalICmp_eq_zero ?_
    intro h
    exact hctv1 (by simpa using
      ((s2_bv8_eq_ofNat (n := 1) (by decide) ctv.toBitVec).mp h))
  have h0 : (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
      = stateAt (cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
          ("%cs", .ptr cs)] [])
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) := rfl
  rw [h0]
  have h1 := s2ValuePos_step_entry_end (calls := s2HelperCalls)
    (env := cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
      ("%cs", .ptr cs)] [])
    (s := stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next)
    rfl (by s2_lk) hbit0
  have h2 := s2ValuePos_step_ifEnd_end9 (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "if.end", pre := some "entry" })
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hctv' hcsv' hbit1
  have h3 := s2ValuePos_step_ifEnd9 (calls := s2HelperCalls)
    (env := ("%1", .int 8 (csv.toBitVec)) ::
      ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "if.end9", pre := some "if.end" })
    rfl (by s2_lk)
  have h4 := s2ValuePos_step_return (calls := s2HelperCalls)
    (env := ("%narrow", .int 1 (evalICmp .eq (csv.toBitVec &&& 0xfd#8) 0x00#8)) ::
      ("%2", .int 8 (csv.toBitVec &&& 0xfd#8)) ::
      ("%1", .int 8 (csv.toBitVec)) ::
      ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp", .int 32 sp), ("%root_done", .int 32 rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next with
      pc := "return", pre := some "if.end9" })
    (pred := "if.end9") (op := Operand.reg "%narrow")
    (v := evalICmp .eq (csv.toBitVec &&& 0xfd#8) 0x00#8) rfl rfl
    (by simp [phiIncoming]) (by s2_lk)
  have s1 := s2_runFuel_jump h1
  have s2 := s2_runFuel_jump h2
  have s3 := s2_runFuel_jump h3
  have s4 := s2_runFuel_ret h4
  have hs := runFuel_prefix_some
    (runFuel_prefix_trans (runFuel_prefix_trans s1 s2) s3) s4
  rw [h0]
  refine hs.trans ?_
  rw [s2_res_mask8, s2_ofNat8_toNat]
  rfl

/-! ### `s2_value_pos`: the contract -/

theorem s2ValuePosBody_contract {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ValuePosPre args mem next) :
    ∃ o : CallOutcome,
      runFuel s2HelperCalls 4 s2ValuePosBody
          (stagedState s2ValuePosBody args mem next) = some (.ret (some o.ret) o.mem) ∧
      s2ValuePosPost args mem next o ∧
      UnchangedOutside mem o.mem (s2ValuePosFoot args mem next) := by
  obtain ⟨sp, rd, ct, cs, rfl, hcond⟩ := hpre
  have hfoot : s2ValuePosFoot [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next = [] := rfl
  rcases Nat.eq_zero_or_pos sp.toNat with hsp0 | hspPos
  · have hrun : runFuel s2HelperCalls 4 s2ValuePosBody
        (stagedState s2ValuePosBody [.int 32 sp, .int 32 rd, .ptr ct, .ptr cs] mem next) =
        some (.ret (some (.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)))) mem) :=
      runFuel_succ_some (s2ValuePos_run_zero (rd := rd) (ct := ct) (cs := cs)
        (mem := mem) (next := next) hsp0)
    refine ⟨⟨.int 32 (BitVec.ofNat 32 (if rd.toNat = 0 then 1 else 0)), mem, next⟩,
      hrun, ?_, ?_⟩
    · refine ⟨if rd.toNat = 0 then 1 else 0, ?_, rfl, rfl, rfl⟩
      simp only [stage2ValuePos, hsp0, ite_true]
    · rw [hfoot]; exact UnchangedOutside.refl' mem []
  · have hsp : sp.toNat ≠ 0 := by omega
    rcases hcond with h0 | ⟨⟨ctv, hctv⟩, ⟨csv, hcsv⟩⟩
    · exact absurd h0 hsp
    · by_cases hctv1 : ctv.toNat = 1
      · have hrun := s2ValuePos_run_object (rd := rd) (mem := mem) (next := next)
          hsp hctv hcsv hctv1
        refine ⟨⟨.int 32 (BitVec.ofNat 32 (if csv.toNat = 2 then 1 else 0)), mem, next⟩,
          hrun, ?_, ?_⟩
        · refine ⟨if csv.toNat = 2 then 1 else 0, ?_, rfl, rfl, rfl⟩
          simp only [stage2ValuePos, hsp, hctv, hcsv, hctv1, ite_true, ite_false]
        · rw [hfoot]; exact UnchangedOutside.refl' mem []
      · have hrun := s2ValuePos_run_array (rd := rd) (mem := mem) (next := next)
          hsp hctv hcsv hctv1
        refine ⟨⟨.int 32 (BitVec.ofNat 32
            (if csv.toNat = 0 ∨ csv.toNat = 2 then 1 else 0)), mem, next⟩,
          hrun, ?_, ?_⟩
        · refine ⟨if csv.toNat = 0 ∨ csv.toNat = 2 then 1 else 0, ?_, rfl, rfl, rfl⟩
          simp only [stage2ValuePos, hsp, hctv, hcsv, hctv1, ite_false]
        · rw [hfoot]; exact UnchangedOutside.refl' mem []

/-! ### `s2_after_value`: the four blocks

The body writes one place: the root flag at depth zero, or the top container's
state byte.  Its `select` is the model's `if ctv.toNat = 1 then 3 else 1`, and the
byte's value at the store is that expression's `i8` reading. -/

theorem s2_natToBytes_one_toNat (x : BitVec 8) :
    natToBytes x.toNat 1 = [UInt8.ofNat x.toNat] := by
  simp only [natToBytes]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem s2_bitVec_if_toNat (b : BitVec 1) :
    (if b = 1 then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat
      = if b = 1 then 3 else 1 := by
  split <;> simp

/-- The byte the store writes is the one the model names.  The body computes the
value at an `i8` `select`; the model writes the same bytes as a one-byte run. -/
theorem s2_convBytes (ctv : UInt8) :
    natToBytes
        (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
          then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat 1 =
      [UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)] := by
  rw [s2_natToBytes_one_toNat, s2_bitVec_if_toNat]
  have hiff : (evalICmp .eq ctv.toBitVec 0x01#8 = 1) ↔ ctv.toNat = 1 := by
    rw [s2_evalICmp_eq_one_iff]
    exact s2_bv8_eq_ofNat (n := 1) (by decide) ctv.toBitVec |>.trans
      (by simp [UInt8.toNat_toBitVec])
  by_cases h : ctv.toNat = 1
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (hiff.mp hh)), ite_eq_right h]

theorem s2_store1_bytes : natToBytes (BitVec.ofNat 32 1).toNat 4 = natToBytes 1 4 := by
  congr 1

theorem s2AfterValue_entry_denote {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hsp : lookupName env "%sp.0.val" = some (.int 32 sp)) :
    denoteCode calls
        [Instr.icmp "%cmp" .eq 32 (.reg "%sp.0.val") (.imm (.int 32 0x00000000#32))]
        (stateAt env s) =
      some (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls env s "%cmp" "%sp.0.val" 32 hsp)]
  rfl

theorem s2AfterValue_ifThen_denote {calls : Calls} {env : Env} {s : State}
    {rd : Nat} (hrd : lookupName env "%root_done" = some (.ptr rd)) :
    denoteCode calls
        [Instr.store (.int 32) (.imm (.int 32 0x00000001#32)) (.reg "%root_done")]
        (stateAt env s) =
      some (stateAt env { s with mem := writeBytes s.mem rd (natToBytes 1 4) }) := by
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_store32_imm calls env s "%root_done" hrd)]
  rw [s2_store1_bytes]
  rfl

theorem s2AfterValue_ifEnd_denote {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv : UInt8}
    (hsp : lookupName env "%sp.0.val" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv) :
    denoteCode calls
        [Instr.binop "%sub" .add 32 (.reg "%sp.0.val") (.imm (.int 32 0xffffffff#32)),
         Instr.zext "%idxprom" 32 64 (.reg "%sub"),
         Instr.gep "%arrayidx" (.int 8) (.reg "%ct") (.reg "%idxprom"),
         Instr.load "%0" (.int 8) (.reg "%arrayidx"),
         Instr.icmp "%cmp1" .eq 8 (.reg "%0") (.imm (.int 8 0x01#8)),
         Instr.select "%conv3" (.int 8) (.reg "%cmp1") (.imm (.int 8 0x03#8))
           (.imm (.int 8 0x01#8)),
         Instr.gep "%arrayidx5" (.int 8) (.reg "%cs") (.reg "%idxprom"),
         Instr.store (.int 8) (.reg "%conv3") (.reg "%arrayidx5")]
        (stateAt env s) =
      some (stateAt
        (("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
          ("%conv3", .int 8
            (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
              then BitVec.ofNat 8 3 else BitVec.ofNat 8 1)) ::
          ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
          ("%0", .int 8 (ctv.toBitVec)) ::
          ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
          ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
          ("%sub", .int 32 (s2MinusOne sp)) :: env)
        { s with
          mem := (writeBytes s.mem (cs + s2TopIdx sp)
            (natToBytes (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
              then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat 1)) }) := by
  have hpos : (BitVec.ofNat 64 (s2MinusOne sp).toNat).toNat < 2 ^ 63 := s2TopIdx_lt sp
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_add_imm_w calls env s "%sub" "%sp.0.val" 32 hsp)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_zext_w calls _ s "%idxprom" "%sub" 32 64 (by s2_lk))]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_gep8_64 calls _ s "%arrayidx" "%ct" "%idxprom" (by s2_lk)
      (by s2_lk) hpos)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_load8 calls _ s "%0" "%arrayidx" (by s2_lk) hctv)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_icmp_eq_imm_w calls _ s "%cmp1" "%0" 8 (by s2_lk))]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_select8_bit (bb := evalICmp .eq (ctv.toBitVec) 0x01#8)
      calls _ s "%conv3" "%cmp1" (by s2_lk))]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_gep8_64 calls _ s "%arrayidx5" "%cs" "%idxprom" (by s2_lk)
      (by s2_lk) hpos)]
  rw [LeanLLVM.denoteCode_cons_of _ _ _ _ _
    (s2_store8 calls _ s "%conv3" "%arrayidx5" (by s2_lk)
      (by s2_lk))]
  rfl

theorem s2AfterValue_step_entry {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp.0.val" = some (.int 32 sp)) :
    step calls s2AfterValueBody (stateAt env s) =
      (if evalICmp .eq sp 0x00000000#32 = 1
       then .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
              { s with pc := "if.then", pre := some "entry" })
       else .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
              { s with pc := "if.end", pre := some "entry" })) := by
  have hpc' : (stateAt env s).pc = "entry" := hpc
  have hden := s2AfterValue_entry_denote (calls := calls) (env := env) (s := s) hsp
  simp only [step, hpc', s2AfterValue_findBlock_entry]
  rw [hden]
  change execTerm (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s)
      (Term.condbr (.reg "%cmp") "if.then" "if.end") = _
  rw [s2_execTerm_condbr (bit := evalICmp .eq sp 0x00000000#32)
    (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env) s)
    "%cmp" "if.then" "if.end" (by s2_lk)]
  simp only [stateAt, hpc]

theorem s2AfterValue_step_entry_then {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp.0.val" = some (.int 32 sp))
    (hbit : evalICmp .eq sp 0x00000000#32 = 1) :
    step calls s2AfterValueBody (stateAt env s) =
      .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
        { s with pc := "if.then", pre := some "entry" }) := by
  rw [s2AfterValue_step_entry hpc hsp]
  simp only [hbit]
  rw [ite_eq_left trivial]

theorem s2AfterValue_step_entry_end {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} (hpc : s.pc = "entry")
    (hsp : lookupName env "%sp.0.val" = some (.int 32 sp))
    (hbit : evalICmp .eq sp 0x00000000#32 = 0) :
    step calls s2AfterValueBody (stateAt env s) =
      .jump (stateAt (("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) :: env)
        { s with pc := "if.end", pre := some "entry" }) := by
  rw [s2AfterValue_step_entry hpc hsp]
  simp only [hbit]
  rw [ite_eq_right (by decide)]

theorem s2AfterValue_step_ifThen {calls : Calls} {env : Env} {s : State}
    {rd : Nat} (hpc : s.pc = "if.then")
    (hrd : lookupName env "%root_done" = some (.ptr rd)) :
    step calls s2AfterValueBody (stateAt env s) =
      .jump (stateAt env
        { s with
          mem := writeBytes s.mem rd (natToBytes 1 4),
          pc := "return", pre := some "if.then" }) := by
  have hpc' : (stateAt env s).pc = "if.then" := hpc
  have hden := s2AfterValue_ifThen_denote (calls := calls) (env := env) (s := s) hrd
  simp only [step, hpc', s2AfterValue_findBlock_ifThen]
  rw [hden]
  change execTerm (stateAt env { s with mem := writeBytes s.mem rd (natToBytes 1 4) })
      (Term.br "return") = _
  rw [s2_execTerm_br]
  simp only [stateAt, hpc]

theorem s2AfterValue_step_ifEnd {calls : Calls} {env : Env} {s : State}
    {sp : BitVec 32} {ct cs : Nat} {ctv : UInt8} (hpc : s.pc = "if.end")
    (hsp : lookupName env "%sp.0.val" = some (.int 32 sp))
    (hct : lookupName env "%ct" = some (.ptr ct))
    (hcs : lookupName env "%cs" = some (.ptr cs))
    (hctv : readByte s.mem (ct + s2TopIdx sp) = some ctv) :
    step calls s2AfterValueBody (stateAt env s) =
      .jump (stateAt
        (("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
          ("%conv3", .int 8
            (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
              then BitVec.ofNat 8 3 else BitVec.ofNat 8 1)) ::
          ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
          ("%0", .int 8 (ctv.toBitVec)) ::
          ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
          ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
          ("%sub", .int 32 (s2MinusOne sp)) :: env)
        ({ s with
          mem := (writeBytes s.mem (cs + s2TopIdx sp)
            (natToBytes (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
              then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat 1)),
          pc := "return", pre := some "if.end" })) := by
  have hpc' : (stateAt env s).pc = "if.end" := hpc
  have hden := s2AfterValue_ifEnd_denote (calls := calls) (env := env) (s := s)
    hsp hct hcs hctv
  simp only [step, hpc', s2AfterValue_findBlock_ifEnd]
  rw [hden]
  change execTerm (stateAt
      (("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
        ("%conv3", .int 8
          (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
            then BitVec.ofNat 8 3 else BitVec.ofNat 8 1)) ::
        ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
        ("%0", .int 8 (ctv.toBitVec)) ::
        ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
        ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
        ("%sub", .int 32 (s2MinusOne sp)) :: env)
      { s with
        mem := writeBytes s.mem (cs + s2TopIdx sp)
          (natToBytes (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
            then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat 1) })
      (Term.br "return") = _
  rw [s2_execTerm_br]
  simp only [stateAt, hpc]

theorem s2AfterValue_step_return {calls : Calls} {env : Env} {s : State}
    (hpc : s.pc = "return") :
    step calls s2AfterValueBody (stateAt env s) = .ret none (stateAt env s) := by
  have hpc' : (stateAt env s).pc = "return" := hpc
  simp only [step, hpc', s2AfterValue_findBlock_return]
  change execTerm (stateAt env s) (Term.ret .void none) = _
  rw [s2_execTerm_retVoid]

/-! ### `s2_after_value`: the two arms' runs -/

theorem s2AfterValue_run_zero {sp : BitVec 32} {rd ct cs : Nat} {mem : Mem} {next : Nat}
    (hsp : sp.toNat = 0) :
    runFuel s2HelperCalls 3 s2AfterValueBody
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next) =
      some (.ret none (writeBytes mem rd (natToBytes 1 4))) := by
  have hbit : evalICmp .eq sp 0x00000000#32 = 1 :=
    s2_evalICmp_eq_one (s2_eq_zero_of_toNat hsp)
  have h0 : (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next)
      = stateAt (cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
          ("%cs", .ptr cs)] [])
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next) := rfl
  rw [h0]
  have h1 := s2AfterValue_step_entry_then (calls := s2HelperCalls)
    (env := cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
      ("%cs", .ptr cs)] [])
    (s := stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next)
    rfl (by s2_lk) hbit
  have h2 := s2AfterValue_step_ifThen (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next with
      pc := "if.then", pre := some "entry" }) rfl (by s2_lk)
  have h3 := s2AfterValue_step_return (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next with
      mem := writeBytes
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next).mem
        rd (natToBytes 1 4),
      pc := "return", pre := some "if.then" }) rfl
  have s1 := s2_runFuel_jump h1
  have s2 := s2_runFuel_jump h2
  have s3 := s2_runFuel_ret h3
  have hs := runFuel_prefix_some (runFuel_prefix_trans s1 s2) s3
  exact hs

theorem s2AfterValue_run_above {sp : BitVec 32} {rd ct cs : Nat} {mem : Mem} {next : Nat}
    {ctv : UInt8} (hsp : sp.toNat ≠ 0)
    (hctv : readByte mem (ct + (sp.toNat - 1)) = some ctv) :
    runFuel s2HelperCalls 3 s2AfterValueBody
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next) =
      some (.ret none (writeBytes mem (cs + (sp.toNat - 1))
        [UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)])) := by
  have hne : sp ≠ 0 := fun h => hsp ((s2_eq_zero_iff_toNat sp).mp h)
  have hbit0 : evalICmp .eq sp 0x00000000#32 = 0 := s2_evalICmp_eq_zero hne
  have hctv' : readByte mem (ct + s2TopIdx sp) = some ctv := by
    rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp]; exact hctv
  have h0 : (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next)
      = stateAt (cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
          ("%cs", .ptr cs)] [])
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next) := rfl
  rw [h0]
  have h1 := s2AfterValue_step_entry_end (calls := s2HelperCalls)
    (env := cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
      ("%cs", .ptr cs)] [])
    (s := stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next)
    rfl (by s2_lk) hbit0
  have h2 := s2AfterValue_step_ifEnd (calls := s2HelperCalls)
    (env := ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next with
      pc := "if.end", pre := some "entry" })
    rfl (by s2_lk) (by s2_lk) (by s2_lk) hctv'
  have h3 := s2AfterValue_step_return (calls := s2HelperCalls)
    (env := ("%arrayidx5", .ptr (cs + s2TopIdx sp)) ::
      ("%conv3", .int 8
        (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
          then BitVec.ofNat 8 3 else BitVec.ofNat 8 1)) ::
      ("%cmp1", .int 1 (evalICmp .eq (ctv.toBitVec) 0x01#8)) ::
      ("%0", .int 8 (ctv.toBitVec)) ::
      ("%arrayidx", .ptr (ct + s2TopIdx sp)) ::
      ("%idxprom", .int 64 (BitVec.ofNat 64 (s2MinusOne sp).toNat)) ::
      ("%sub", .int 32 (s2MinusOne sp)) ::
      ("%cmp", .int 1 (evalICmp .eq sp 0x00000000#32)) ::
      cells [("%sp.0.val", .int 32 sp), ("%root_done", .ptr rd), ("%ct", .ptr ct),
        ("%cs", .ptr cs)] [])
    (s := { stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next with
      mem := writeBytes
        (stagedState s2AfterValueBody [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next).mem
        (cs + s2TopIdx sp)
        (natToBytes (if evalICmp .eq (ctv.toBitVec) 0x01#8 = 1
          then BitVec.ofNat 8 3 else BitVec.ofNat 8 1).toNat 1),
      pc := "return", pre := some "if.end" }) rfl
  have s1 := s2_runFuel_jump h1
  have s2 := s2_runFuel_jump h2
  have s3 := s2_runFuel_ret h3
  have hs := runFuel_prefix_some (runFuel_prefix_trans s1 s2) s3
  rw [h0]
  refine hs.trans ?_
  rw [s2TopIdx_eq, s2MinusOne_toNat sp hsp, s2_convBytes]
  rfl

/-! ### `s2_after_value`: the contract -/

theorem s2AfterValueBody_contract {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2AfterValuePre args mem next) :
    ∃ o : CallOutcome,
      runFuel s2HelperCalls 3 s2AfterValueBody
          (stagedState s2AfterValueBody args mem next) = some (.ret none o.mem) ∧
      s2AfterValuePost args mem next o ∧
      UnchangedOutside mem o.mem (s2AfterValueFoot args mem next) := by
  obtain ⟨sp, rd, ct, cs, rfl, hcond⟩ := hpre
  rcases Nat.eq_zero_or_pos sp.toNat with hsp0 | hspPos
  · have hrun := s2AfterValue_run_zero (rd := rd) (ct := ct) (cs := cs)
      (mem := mem) (next := next) hsp0
    refine ⟨⟨voidRet, writeBytes mem rd (natToBytes 1 4), next⟩, hrun, ?_, ?_⟩
    · refine ⟨writeBytes mem rd (natToBytes 1 4), ?_, rfl, rfl, rfl⟩
      simp only [stage2AfterValue, hsp0, ite_true, wordBytes]
    · have hfoot : s2AfterValueFoot [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next
          = [(rd, 4)] := by simp [s2AfterValueFoot, hsp0]
      rw [hfoot]
      refine UnchangedOutside.write_le (w := 4) (UnchangedOutside.refl' mem [(rd, 4)])
        ⟨(rd, 4), List.mem_cons_self .., le_rfl, by omega⟩ ?_
      simp [natToBytes]
  · have hsp : sp.toNat ≠ 0 := by omega
    rcases hcond with h0 | ⟨ctv, hctv⟩
    · exact absurd h0 hsp
    · have hrun := s2AfterValue_run_above (rd := rd) (cs := cs) (mem := mem) (next := next)
        hsp hctv
      refine ⟨⟨voidRet, writeBytes mem (cs + (sp.toNat - 1))
          [UInt8.ofNat (if ctv.toNat = 1 then 3 else 1)], next⟩, hrun, ?_, ?_⟩
      · refine ⟨_, ?_, rfl, rfl, rfl⟩
        simp only [stage2AfterValue, hsp, hctv, ite_false]
      · have hfoot : s2AfterValueFoot [.int 32 sp, .ptr rd, .ptr ct, .ptr cs] mem next
            = [(cs + (sp.toNat - 1), 1)] := by simp [s2AfterValueFoot, hsp]
        rw [hfoot]
        refine UnchangedOutside.write_le (w := 1)
          (UnchangedOutside.refl' mem [(cs + (sp.toNat - 1), 1)])
          ⟨(cs + (sp.toNat - 1), 1), List.mem_cons_self .., le_rfl, by omega⟩ ?_
        simp

/-! ### The contracts, read through their instances -/

theorem s2ValuePosBody_satisfies {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2ValuePosContract.pre args mem next) :
    ∃ o : CallOutcome,
      runFuel s2HelperCalls 4 s2ValuePosBody
          (stagedState s2ValuePosBody args mem next) = some (.ret (some o.ret) o.mem) ∧
      s2ValuePosContract.post args mem next o ∧
      UnchangedOutside mem o.mem (s2ValuePosContract.foot args mem next) :=
  s2ValuePosBody_contract hpre

theorem s2AfterValueBody_satisfies {args : List Value} {mem : Mem} {next : Nat}
    (hpre : s2AfterValueContract.pre args mem next) :
    ∃ o : CallOutcome,
      runFuel s2HelperCalls 3 s2AfterValueBody
          (stagedState s2AfterValueBody args mem next) = some (.ret none o.mem) ∧
      s2AfterValueContract.post args mem next o ∧
      UnchangedOutside mem o.mem (s2AfterValueContract.foot args mem next) :=
  s2AfterValueBody_contract hpre

/-! ### Axiom footprints

The two bodies' contract statements, the instances they read through, and the
runs they compose, pinned with `#guard_msgs` so the build checks the footprint
rather than printing it.  The carrier is the `gep` step's (`BitVec.signExtend`'s
core lemma), the same one `JsonStage2HelperIR`'s pins name; the instrument's
discriminating control is recorded there, on a throwaway `sorry`.  The two
depth-zero runs take no `gep` step and measure without `Classical.choice`: their
pins read `[propext, Quot.sound]`, and every other pin here reads
`[propext, Classical.choice, Quot.sound]`.  No `sorry` is in this module. -/
/-- info: 'LeanLLVM.Refinement.s2ValuePosBody_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2ValuePosBody_contract

/-- info: 'LeanLLVM.Refinement.s2AfterValueBody_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2AfterValueBody_contract

/-- info: 'LeanLLVM.Refinement.s2ValuePosBody_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2ValuePosBody_satisfies

/-- info: 'LeanLLVM.Refinement.s2AfterValueBody_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2AfterValueBody_satisfies

/-- info: 'LeanLLVM.Refinement.s2ValuePos_run_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms s2ValuePos_run_zero

/-- info: 'LeanLLVM.Refinement.s2ValuePos_run_object' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2ValuePos_run_object

/-- info: 'LeanLLVM.Refinement.s2ValuePos_run_array' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2ValuePos_run_array

/-- info: 'LeanLLVM.Refinement.s2AfterValue_run_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms s2AfterValue_run_zero

/-- info: 'LeanLLVM.Refinement.s2AfterValue_run_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms s2AfterValue_run_above

end LeanLLVM.Refinement
