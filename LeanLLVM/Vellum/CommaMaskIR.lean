/-
An emitted-IR bridge for the pure comma-mask seam.

`probes/install/ir/baseline.ll` and `probes/install/ir/candidate.ll` are the
emissions of the probe's two seam objects; `probes/install/ir/capture.sh` records
the exact clang and `opt` invocations and every piece of textual syntax that was
removed before the parser saw them.  This module

1. parses both files;
2. pins the parsed ASTs against the literals below (`#guard`, because the
   parser runs on `String` primitives, which the kernel does not reduce, so a
   proposition about a `parseModule` result cannot be closed by `rfl`);
3. proves, in `LeanLLVM.Semantics`, that each parsed function returns the Lean
   body of the corresponding `CommaMask` function on every argument list --
   `swar` for the baseline (the packed no-borrow mask) and `byteLoop` for the
   candidate (the eight-lane fold);
4. concludes `LeanLLVM.Refines candidateFunction baselineFunction`.

Step 3 needs no bit-blasting: the fixtures are emitted at `-O0`, so their
instruction sequences are the source expressions operation for operation, and
the equalities below are rewrites.  The `CommaMask` side enters through
`byteLoop_eq_spec` and `swar_eq_spec`, whose `bv_decide`
footprint is pinned in `LeanLLVMTest/Vellum.lean` and is unchanged here.
-/
import LeanLLVM.Parser
import LeanLLVM.Semantics
import LeanLLVM.Vellum.CommaMask
import LeanLLVM.Vellum.CommaMaskKernel
import Std.Tactic.BVDecide

namespace LeanLLVM.Vellum.CommaMaskIR

open LeanLLVM

/-! ### The fixtures -/

/-- The baseline seam as emitted (`probes/install/ir/baseline.ll`). -/
def baselineSrc : String := include_str "../../probes/install/ir/baseline.ll"

/-- The candidate seam as emitted (`probes/install/ir/candidate.ll`). -/
def candidateSrc : String := include_str "../../probes/install/ir/candidate.ll"

/-- Parse a fixture and take its single function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-- A 64-bit constant, in the form `parseConst` produces: the parser reads an
integer literal with `parseInt` and wraps it in `BitVec.ofInt`. -/
def c (v : Int) : BitVec 64 := BitVec.ofInt 64 v

/-- An immediate operand at the width the fixtures use. -/
abbrev lit (v : Int) : Operand := .imm (.int 64 (c v))

/-- `%arg` and `arg` are the parameter name and value in both fixtures. -/
abbrev argName : String := "%arg"

/-! ### The baseline body, register by register

`probes/install/ir/baseline.ll` has two blocks: `bb` is empty and branches to
`bb1`, which computes the packed mask.  The values below are what each register
holds. -/

/-- `%i`: the comma-XOR word. -/
def baseW (x : BitVec 64) : BitVec 64 := x ^^^ c 3182967604875373612
/-- `%i2`: the borrow mask. -/
def baseMasked (x : BitVec 64) : BitVec 64 := baseW x &&& c 9187201950435737471
/-- `%i3`: the bias addition. -/
def baseBiased (x : BitVec 64) : BitVec 64 := baseMasked x + c 9187201950435737471
/-- `%i4`: the bias OR-ed with the XOR word. -/
def baseOr (x : BitVec 64) : BitVec 64 := baseBiased x ||| baseW x
/-- `%i5`: the complement of the bias word. -/
def baseNot (x : BitVec 64) : BitVec 64 := baseOr x ^^^ c (-1)
/-- `%i6`: the packed mask. -/
def baseOut (x : BitVec 64) : BitVec 64 := baseNot x &&& c (-9187201950435737472)

/-- The instruction list of `bb1`, as an AST. -/
def baselineInstrs : List Instr := [
  .binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612),
  .binop "%i2" .and 64 (.reg "%i") (lit 9187201950435737471),
  .binop "%i3" .add 64 (.reg "%i2") (lit 9187201950435737471),
  .binop "%i4" .or 64 (.reg "%i3") (.reg "%i"),
  .binop "%i5" .xor 64 (.reg "%i4") (lit (-1)),
  .binop "%i6" .and 64 (.reg "%i5") (lit (-9187201950435737472))]

/-- The entry block: nothing to do, fall through to `bb1`. -/
def baselineEntry : Block := { name := "bb", instrs := [], term := .br "bb1" }

/-- The body block. -/
def baselineBody : Block :=
  { name := "bb1", instrs := baselineInstrs, term := .ret (.int 64) (some (.reg "%i6")) }

/-- `probes/install/ir/baseline.ll`, as an AST. -/
def baselineFunction : Function :=
  { name := "leanllvm_comma_mask8", retTy := .int 64, params := [(argName, .int 64)],
    blocks := [baselineEntry, baselineBody] }

#guard decide (firstFunction baselineSrc = some baselineFunction)

/-! ### The candidate body, register by register

`probes/install/ir/candidate.ll` is one block: the XOR word, then eight lanes of
"take byte `k`, test it, or the lane's bit into the accumulator".  Lane `k`'s
test is `BitVec.ofBool ((byte k) = 0)`, the value `select` binds is the usual
`i64`, and `0x80 <<< 8k` is the lane's bit as clang folded it. -/

/-- `%i`: the comma-XOR word. -/
def candW (x : BitVec 64) : BitVec 64 := x ^^^ c 3182967604875373612

/-- The shift a `lshr` instruction applies: `(c k).toNat`, which is `k` for the
literals clang emitted. -/
def sh (k : Int) : Nat := (c k).toNat

/-- `%i1`, `%i6`, ...: byte `k` of the XOR word. -/
def candByte (x : BitVec 64) (k : Int) : BitVec 64 := (candW x >>> sh k) &&& c 255

/-- `%i3`, `%i8`, ...: the test bit of lane `k`. -/
def candTest (x : BitVec 64) (k : Int) : BitVec 1 := BitVec.ofBool (candByte x k = c 0)

/-- Lane `k`'s contribution: OR the lane bit in when the byte is zero. -/
def candLane (acc : BitVec 64) (x : BitVec 64) (k : Int) (bit : Int) : BitVec 64 :=
  if candTest x k = (1 : BitVec 1) then acc ||| c bit else acc

/-- The accumulator after lane `k`, in the order the `select` instructions bind
it.  Lane 0 ORs `0x80` into the initial `0`; every later lane ORs its bit into
the accumulator the previous `select` bound. -/
def candA0 (x : BitVec 64) : BitVec 64 := candLane (c 0) x 0 128
def candA1 (x : BitVec 64) : BitVec 64 := candLane (candA0 x) x 8 32768
def candA2 (x : BitVec 64) : BitVec 64 := candLane (candA1 x) x 16 8388608
def candA3 (x : BitVec 64) : BitVec 64 := candLane (candA2 x) x 24 2147483648
def candA4 (x : BitVec 64) : BitVec 64 := candLane (candA3 x) x 32 549755813888
def candA5 (x : BitVec 64) : BitVec 64 := candLane (candA4 x) x 40 140737488355328
def candA6 (x : BitVec 64) : BitVec 64 := candLane (candA5 x) x 48 36028797018963968
def candA7 (x : BitVec 64) : BitVec 64 := candLane (candA6 x) x 56 (-9223372036854775808)

/-- The value the candidate seam returns. -/
def candOut (x : BitVec 64) : BitVec 64 := candA7 x

/-- The body, as an AST. -/
def candidateInstrs : List Instr := [
  .binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612),
  .binop "%i1" .lshr 64 (.reg "%i") (lit 0),
  .binop "%i2" .and 64 (.reg "%i1") (lit 255),
  .icmp "%i3" .eq 64 (.reg "%i2") (lit 0),
  .binop "%i4" .or 64 (lit 0) (lit 128),
  .select "%i5" (.int 64) (.reg "%i3") (.reg "%i4") (lit 0),
  .binop "%i6" .lshr 64 (.reg "%i") (lit 8),
  .binop "%i7" .and 64 (.reg "%i6") (lit 255),
  .icmp "%i8" .eq 64 (.reg "%i7") (lit 0),
  .binop "%i9" .or 64 (.reg "%i5") (lit 32768),
  .select "%i10" (.int 64) (.reg "%i8") (.reg "%i9") (.reg "%i5"),
  .binop "%i11" .lshr 64 (.reg "%i") (lit 16),
  .binop "%i12" .and 64 (.reg "%i11") (lit 255),
  .icmp "%i13" .eq 64 (.reg "%i12") (lit 0),
  .binop "%i14" .or 64 (.reg "%i10") (lit 8388608),
  .select "%i15" (.int 64) (.reg "%i13") (.reg "%i14") (.reg "%i10"),
  .binop "%i16" .lshr 64 (.reg "%i") (lit 24),
  .binop "%i17" .and 64 (.reg "%i16") (lit 255),
  .icmp "%i18" .eq 64 (.reg "%i17") (lit 0),
  .binop "%i19" .or 64 (.reg "%i15") (lit 2147483648),
  .select "%i20" (.int 64) (.reg "%i18") (.reg "%i19") (.reg "%i15"),
  .binop "%i21" .lshr 64 (.reg "%i") (lit 32),
  .binop "%i22" .and 64 (.reg "%i21") (lit 255),
  .icmp "%i23" .eq 64 (.reg "%i22") (lit 0),
  .binop "%i24" .or 64 (.reg "%i20") (lit 549755813888),
  .select "%i25" (.int 64) (.reg "%i23") (.reg "%i24") (.reg "%i20"),
  .binop "%i26" .lshr 64 (.reg "%i") (lit 40),
  .binop "%i27" .and 64 (.reg "%i26") (lit 255),
  .icmp "%i28" .eq 64 (.reg "%i27") (lit 0),
  .binop "%i29" .or 64 (.reg "%i25") (lit 140737488355328),
  .select "%i30" (.int 64) (.reg "%i28") (.reg "%i29") (.reg "%i25"),
  .binop "%i31" .lshr 64 (.reg "%i") (lit 48),
  .binop "%i32" .and 64 (.reg "%i31") (lit 255),
  .icmp "%i33" .eq 64 (.reg "%i32") (lit 0),
  .binop "%i34" .or 64 (.reg "%i30") (lit 36028797018963968),
  .select "%i35" (.int 64) (.reg "%i33") (.reg "%i34") (.reg "%i30"),
  .binop "%i36" .lshr 64 (.reg "%i") (lit 56),
  .binop "%i37" .and 64 (.reg "%i36") (lit 255),
  .icmp "%i38" .eq 64 (.reg "%i37") (lit 0),
  .binop "%i39" .or 64 (.reg "%i35") (lit (-9223372036854775808)),
  .select "%i40" (.int 64) (.reg "%i38") (.reg "%i39") (.reg "%i35")]

/-- The body block. -/
def candidateBody : Block :=
  { name := "bb", instrs := candidateInstrs, term := .ret (.int 64) (some (.reg "%i40")) }

/-- `probes/install/ir/candidate.ll`, as an AST. -/
def candidateFunction : Function :=
  { name := "leanllvm_comma_mask8", retTy := .int 64, params := [(argName, .int 64)],
    blocks := [candidateBody] }

#guard decide (firstFunction candidateSrc = some candidateFunction)

/-! ### Small facts -/

/-- `BitVec 1` has two values, so a bit that is not `1` is `0`.  `select` needs
this to know that its condition is never a third value. -/
theorem bv1_eq_zero_of_ne_one (b : BitVec 1) (h : b ≠ 1) : b = 0 := by
  have hlt : b.toNat < 2 := by simpa using b.isLt
  have hne : b.toNat ≠ 1 := by
    intro hc
    apply h
    rw [← BitVec.toNat_inj]
    simpa using hc
  have h0 : b.toNat = 0 := by omega
  rw [← BitVec.toNat_inj]
  simpa using h0

/-- A `select` between two `i64` registers binds an `i64` whose value is the
`if` decided at the `BitVec` level. -/
theorem bind_ite_int (s : State) (d : String) (p : Prop) [Decidable p] (a b : BitVec 64) :
    s.bind d (if p then (.int 64 a : Value) else .int 64 b)
      = s.bind d (.int 64 (if p then a else b)) := by
  by_cases h : p <;> simp [h]

/-- A `BitVec.ofBool` test read at the `BitVec 1` level. -/
theorem ofBool_eq_one {p : Prop} [Decidable p] : (BitVec.ofBool p = (1 : BitVec 1)) ↔ p := by
  by_cases h : p <;> simp [BitVec.ofBool, h]

/-- The `Nat`-level shape `evalBinopNat` leaves for `add`, read back as a
`BitVec`. -/
theorem ofNat_add_toNat (a b : BitVec 64) :
    BitVec.ofNat 64 ((a.toNat + b.toNat) % 18446744073709551616) = a + b := by
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_ofNat, BitVec.toNat_add]

/-- The `Nat`-level shape `evalBinopNat` leaves for `lshr`, read back as a
`BitVec`.  The shift stays below the width, so the `Nat` modulus is the identity. -/
theorem ofNat_ushiftRight_toNat (a : BitVec 64) (n : Nat) :
    BitVec.ofNat 64 (a.toNat >>> n) = a >>> n := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  rw [Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.isLt

/-- The complement instruction clang emits for a `UInt64` complement. -/
theorem xor_ofInt_neg_one (x : BitVec 64) : x ^^^ c (-1) = ~~~x := by
  have h : c (-1) = BitVec.allOnes 64 := by decide
  rw [h, BitVec.not_def, BitVec.xor_comm]

/-! ### One instruction at a time

`evalInstr` reads integer operands at the `Nat` level and rebuilds the result
with `BitVec.ofNat`, so unfolding it for a whole block in one `simp` copies the
register environment at every step.  The lemmas below state the same step with
the value kept at the `BitVec` level and the operand lookup left as an explicit
`match`; that makes them unconditional rewrite rules -- the `match` reduces once
the environment is known -- and keeps the environment out of the goal. -/

theorem evalInstr_and_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.binop d .and 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a &&& b)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_xor_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.binop d .xor 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a ^^^ b)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_add_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.binop d .add 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a + b)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat, ofNat_add_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_or_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.binop d .or 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a ||| b)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_lshr_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.binop d .lshr 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 64 (a >>> b.toNat)))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat,
          ofNat_ushiftRight_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

/-- Two immediates need no lookup: the result is a constant. -/
theorem evalInstr_or_imm_imm (s : State) (d : String) (a b : BitVec 64) :
    evalInstr s (.binop d .or 64 (.imm (.int 64 a)) (.imm (.int 64 b))) =
      some (s.bind d (.int 64 (a ||| b))) := by
  simp [evalInstr, evalOperand, Const.toValue, Value.intToNat, evalBinopNat,
    evalBinop, BitVec.ofNat_toNat]

theorem evalInstr_or_reg (s : State) (d r₁ r₂ : String) :
    evalInstr s (.binop d .or 64 (.reg r₁) (.reg r₂)) =
      (match lookupName s.env r₁, lookupName s.env r₂ with
       | some (.int 64 a), some (.int 64 b) => some (s.bind d (.int 64 (a ||| b)))
       | _, _ => none) := by
  simp only [evalInstr, evalOperand]
  cases lookupName s.env r₁ with
  | none => simp
  | some v₁ =>
    cases lookupName s.env r₂ with
    | none => simp
    | some v₂ =>
      cases v₁ with
      | int w a =>
        cases v₂ with
        | int w' b =>
          by_cases hw : w = 64
          · by_cases hw' : w' = 64
            · subst hw; subst hw'
              simp [Value.intToNat, evalBinopNat, evalBinop, BitVec.ofNat_toNat]
            · simp [Value.intToNat, hw']
          · simp [Value.intToNat, hw]
        | ptr b => simp [Value.intToNat]
      | ptr a => simp [Value.intToNat]

theorem evalInstr_icmp_eq_imm (s : State) (d r : String) (b : BitVec 64) :
    evalInstr s (.icmp d .eq 64 (.reg r) (.imm (.int 64 b))) =
      (match lookupName s.env r with
       | some (.int 64 a) => some (s.bind d (.int 1 (BitVec.ofBool (a = b))))
       | _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases v with
    | int w a =>
      by_cases hw : w = 64
      · subst hw
        simp [Value.intToNat, evalICmpNat, evalICmp, BitVec.ofNat_toNat]
      · simp [Value.intToNat, hw]
    | ptr a => simp [Value.intToNat]

theorem evalInstr_select_reg_imm (s : State) (d r r₁ : String) (b : BitVec 64) :
    evalInstr s (.select d (.int 64) (.reg r) (.reg r₁) (.imm (.int 64 b))) =
      (match lookupName s.env r, lookupName s.env r₁ with
       | some (.int 1 c), some va =>
           some (s.bind d (if c = (1 : BitVec 1) then va else .int 64 b))
       | _, _ => none) := by
  simp only [evalInstr, evalOperand, Const.toValue]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases lookupName s.env r₁ with
    | none => simp
    | some v₁ =>
      cases v with
      | ptr a => simp
      | int w c =>
        by_cases hw : w = 1
        · subst hw
          by_cases hc : c = (1 : BitVec 1)
          · simp [hc]
          · have h0 : c = 0 := bv1_eq_zero_of_ne_one c hc
            simp [h0]
        · simp [hw]

theorem evalInstr_select_reg (s : State) (d r r₁ r₂ : String) :
    evalInstr s (.select d (.int 64) (.reg r) (.reg r₁) (.reg r₂)) =
      (match lookupName s.env r, lookupName s.env r₁, lookupName s.env r₂ with
       | some (.int 1 c), some va, some vb =>
           some (s.bind d (if c = (1 : BitVec 1) then va else vb))
       | _, _, _ => none) := by
  simp only [evalInstr, evalOperand]
  cases lookupName s.env r with
  | none => simp
  | some v =>
    cases lookupName s.env r₁ with
    | none => simp
    | some v₁ =>
      cases lookupName s.env r₂ with
      | none => simp
      | some v₂ =>
        cases v with
        | ptr a => simp
        | int w c =>
          by_cases hw : w = 1
          · subst hw
            by_cases hc : c = (1 : BitVec 1)
            · simp [hc]
            · have h0 : c = 0 := bv1_eq_zero_of_ne_one c hc
              simp [h0]
          · simp [hw]

/-! ### Blocks -/

/-- Peel one instruction from a straight-line block whose effect is known. -/
theorem denoteCode_cons_of (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr s i = some s') : denoteCode (i :: is) s = denoteCode is s' := by
  simp only [denoteCode, h]

/-- The baseline body, stage by stage, in the order the instructions bind. -/
def b1 (s : State) (x : BitVec 64) : State := s.bind "%i" (.int 64 (baseW x))
def b2 (s : State) (x : BitVec 64) : State := s.bind "%i2" (.int 64 (baseMasked x))
def b3 (s : State) (x : BitVec 64) : State := s.bind "%i3" (.int 64 (baseBiased x))
def b4 (s : State) (x : BitVec 64) : State := s.bind "%i4" (.int 64 (baseOr x))
def b5 (s : State) (x : BitVec 64) : State := s.bind "%i5" (.int 64 (baseNot x))
def b6 (s : State) (x : BitVec 64) : State := s.bind "%i6" (.int 64 (baseOut x))

/-- The state the body reaches from `s`, register by register. -/
def baselineRun (s : State) (x : BitVec 64) : State :=
  b6 (b5 (b4 (b3 (b2 (b1 s x) x) x) x) x) x

theorem baselineStep1 (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) :
    evalInstr s (.binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612))
      = some (b1 s x) := by
  simp [evalInstr_xor_imm, h0, b1, State.bind, baseW, argName]

theorem baselineStep2 (s : State) (x : BitVec 64) :
    evalInstr (b1 s x) (.binop "%i2" .and 64 (.reg "%i") (lit 9187201950435737471))
      = some (b2 (b1 s x) x) := by
  simp [evalInstr_and_imm, b1, b2, State.bind, baseW, baseMasked, lookupName]

theorem baselineStep3 (s : State) (x : BitVec 64) :
    evalInstr (b2 (b1 s x) x) (.binop "%i3" .add 64 (.reg "%i2") (lit 9187201950435737471))
      = some (b3 (b2 (b1 s x) x) x) := by
  simp [evalInstr_add_imm, b1, b2, b3, State.bind, baseW, baseMasked, baseBiased, lookupName]

theorem baselineStep4 (s : State) (x : BitVec 64) :
    evalInstr (b3 (b2 (b1 s x) x) x) (.binop "%i4" .or 64 (.reg "%i3") (.reg "%i"))
      = some (b4 (b3 (b2 (b1 s x) x) x) x) := by
  simp [evalInstr_or_reg, b1, b2, b3, b4, State.bind, baseW, baseMasked, baseBiased, baseOr,
    lookupName]

theorem baselineStep5 (s : State) (x : BitVec 64) :
    evalInstr (b4 (b3 (b2 (b1 s x) x) x) x) (.binop "%i5" .xor 64 (.reg "%i4") (lit (-1)))
      = some (b5 (b4 (b3 (b2 (b1 s x) x) x) x) x) := by
  simp [evalInstr_xor_imm, b1, b2, b3, b4, b5, State.bind, baseW, baseMasked, baseBiased, baseOr,
    baseNot, lookupName]

theorem baselineStep6 (s : State) (x : BitVec 64) :
    evalInstr (b5 (b4 (b3 (b2 (b1 s x) x) x) x) x)
        (.binop "%i6" .and 64 (.reg "%i5") (lit (-9187201950435737472)))
      = some (b6 (b5 (b4 (b3 (b2 (b1 s x) x) x) x) x) x) := by
  simp [evalInstr_and_imm, b1, b2, b3, b4, b5, b6, State.bind, baseW, baseMasked, baseBiased,
    baseOr, baseNot, baseOut, lookupName]

theorem baseline_block (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) :
    denoteCode baselineInstrs s = some (baselineRun s x) := by
  have h1 := baselineStep1 s x h0
  have h2 := baselineStep2 s x
  have h3 := baselineStep3 s x
  have h4 := baselineStep4 s x
  have h5 := baselineStep5 s x
  have h6 := baselineStep6 s x
  rw [show baselineInstrs =
      [.binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612),
       .binop "%i2" .and 64 (.reg "%i") (lit 9187201950435737471),
       .binop "%i3" .add 64 (.reg "%i2") (lit 9187201950435737471),
       .binop "%i4" .or 64 (.reg "%i3") (.reg "%i"),
       .binop "%i5" .xor 64 (.reg "%i4") (lit (-1)),
       .binop "%i6" .and 64 (.reg "%i5") (lit (-9187201950435737472))] from rfl]
  rw [denoteCode_cons_of _ _ _ _ h1]
  rw [denoteCode_cons_of _ _ _ _ h2]
  rw [denoteCode_cons_of _ _ _ _ h3]
  rw [denoteCode_cons_of _ _ _ _ h4]
  rw [denoteCode_cons_of _ _ _ _ h5]
  rw [denoteCode_cons_of _ _ _ _ h6]
  rfl

theorem lookupName_baselineRun (s : State) (x : BitVec 64) :
    lookupName (baselineRun s x).env "%i6" = some (.int 64 (baseOut x)) := by
  simp [baselineRun, b1, b2, b3, b4, b5, b6, State.bind]

theorem baselineRun_mem (s : State) (x : BitVec 64) : (baselineRun s x).mem = s.mem := rfl

/-- The literals `swar` is written with, in the `c` form clang emits. -/
theorem c_comma : c 3182967604875373612 = 0x2C2C2C2C2C2C2C2C := by decide
theorem c_mask : c 9187201950435737471 = 0x7F7F7F7F7F7F7F7F := by decide
theorem c_lane : c (-9187201950435737472) = 0x8080808080808080 := by decide

/-- The packed mask is the baseline seam. -/
theorem baseOut_eq_swar (x : BitVec 64) : baseOut x = swar x := by
  simp only [baseOut, baseNot, baseOr, baseBiased, baseMasked, baseW, swar, c_comma, c_mask]
  rw [xor_ofInt_neg_one]
  simp only [c_lane]

theorem baseline_step_entry (x : BitVec 64) :
    step baselineFunction (initState baselineFunction [.int 64 x]) =
      .jump { initState baselineFunction [.int 64 x] with pc := "bb1" } := by
  simp only [step, baselineFunction, baselineEntry, baselineBody, Function.findBlock,
    findBlockList, Function.entry?, initState, List.head?, Option.map, Option.getD,
    List.map, List.zip, List.zipWith, denoteCode, execTerm, ite_true, argName]

theorem baseline_step_body (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) (hpc : s.pc = "bb1") :
    step baselineFunction s = .ret (some (.int 64 (swar x))) (baselineRun s x) := by
  have hfind : baselineFunction.findBlock s.pc = some baselineBody := by
    simp [hpc, baselineFunction, baselineEntry, baselineBody, Function.findBlock, findBlockList]
  simp only [step, hfind, baselineBody]
  rw [baseline_block s x h0]
  simp [execTerm, evalOperand, lookupName_baselineRun, baseOut_eq_swar]

theorem lookupName_initState_baseline (x : BitVec 64) :
    lookupName (initState baselineFunction [.int 64 x]).env "%arg" = some (.int 64 x) := by
  simp only [initState, baselineFunction, List.map, List.zip, List.zipWith, lookupName,
    ite_true, argName]

theorem baseline_initState_mem (x : BitVec 64) :
    (initState baselineFunction [.int 64 x]).mem = [] := rfl

theorem baseline_runFuel_body (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) (hpc : s.pc = "bb1")
    (hm : s.mem = []) :
    ∀ n, runFuel (n + 1) baselineFunction s =
      some (.ret (some (.int 64 (swar x))) []) := by
  intro n
  cases n with
  | zero =>
      simp only [runFuel, baseline_step_body s x h0 hpc, baselineRun_mem, hm]
  | succ k =>
      simp only [runFuel, baseline_step_body s x h0 hpc, baselineRun_mem, hm]

theorem baseline_runFuel (x : BitVec 64) :
    ∀ n, runFuel (n + 2) baselineFunction (initState baselineFunction [.int 64 x]) =
      some (.ret (some (.int 64 (swar x))) []) := by
  intro n
  have h0 : lookupName { initState baselineFunction [.int 64 x] with pc := "bb1" }.env
      "%arg" = some (.int 64 x) := lookupName_initState_baseline x
  have hm : ({ initState baselineFunction [.int 64 x] with pc := "bb1" } : State).mem = [] :=
    baseline_initState_mem x
  cases n with
  | zero =>
      simp only [runFuel, baseline_step_entry]
      exact baseline_runFuel_body _ x h0 rfl hm 0
  | succ k =>
      simp only [runFuel, baseline_step_entry]
      exact baseline_runFuel_body _ x h0 rfl hm (k + 1)

theorem baseline_runFuel_none_or (x : BitVec 64) :
    ∀ n, runFuel n baselineFunction (initState baselineFunction [.int 64 x]) = none ∨
      runFuel n baselineFunction (initState baselineFunction [.int 64 x]) =
        some (.ret (some (.int 64 (swar x))) []) := by
  intro n
  cases n with
  | zero => exact Or.inl rfl
  | succ k =>
    cases k with
    | zero =>
        refine Or.inl ?_
        simp only [runFuel, baseline_step_entry]
    | succ j => exact Or.inr (baseline_runFuel x j)

/-! ### The candidate body, stage by stage -/

theorem ite_int (p : Prop) [Decidable p] (a b : BitVec 64) :
    (if p then (.int 64 a : Value) else .int 64 b) = .int 64 (if p then a else b) := by
  by_cases h : p <;> simp [h]

def d1 (s : State) (x : BitVec 64) : State := s.bind "%i" (.int 64 (candW x))
def d2 (s : State) (x : BitVec 64) : State := (d1 s x).bind "%i1" (.int 64 (candW x >>> sh 0))
def d3 (s : State) (x : BitVec 64) : State := (d2 s x).bind "%i2" (.int 64 (candByte x 0))
def d4 (s : State) (x : BitVec 64) : State := (d3 s x).bind "%i3" (.int 1 (candTest x 0))
def d5 (s : State) (x : BitVec 64) : State := (d4 s x).bind "%i4" (.int 64 (c 0 ||| c 128))
def d6 (s : State) (x : BitVec 64) : State := (d5 s x).bind "%i5" (.int 64 (candA0 x))
def d7 (s : State) (x : BitVec 64) : State := (d6 s x).bind "%i6" (.int 64 (candW x >>> sh 8))
def d8 (s : State) (x : BitVec 64) : State := (d7 s x).bind "%i7" (.int 64 (candByte x 8))
def d9 (s : State) (x : BitVec 64) : State := (d8 s x).bind "%i8" (.int 1 (candTest x 8))
def d10 (s : State) (x : BitVec 64) : State := (d9 s x).bind "%i9" (.int 64 (candA0 x ||| c 32768))
def d11 (s : State) (x : BitVec 64) : State := (d10 s x).bind "%i10" (.int 64 (candA1 x))
def d12 (s : State) (x : BitVec 64) : State := (d11 s x).bind "%i11" (.int 64 (candW x >>> sh 16))
def d13 (s : State) (x : BitVec 64) : State := (d12 s x).bind "%i12" (.int 64 (candByte x 16))
def d14 (s : State) (x : BitVec 64) : State := (d13 s x).bind "%i13" (.int 1 (candTest x 16))
def d15 (s : State) (x : BitVec 64) : State := (d14 s x).bind "%i14" (.int 64 (candA1 x ||| c 8388608))
def d16 (s : State) (x : BitVec 64) : State := (d15 s x).bind "%i15" (.int 64 (candA2 x))
def d17 (s : State) (x : BitVec 64) : State := (d16 s x).bind "%i16" (.int 64 (candW x >>> sh 24))
def d18 (s : State) (x : BitVec 64) : State := (d17 s x).bind "%i17" (.int 64 (candByte x 24))
def d19 (s : State) (x : BitVec 64) : State := (d18 s x).bind "%i18" (.int 1 (candTest x 24))
def d20 (s : State) (x : BitVec 64) : State := (d19 s x).bind "%i19" (.int 64 (candA2 x ||| c 2147483648))
def d21 (s : State) (x : BitVec 64) : State := (d20 s x).bind "%i20" (.int 64 (candA3 x))
def d22 (s : State) (x : BitVec 64) : State := (d21 s x).bind "%i21" (.int 64 (candW x >>> sh 32))
def d23 (s : State) (x : BitVec 64) : State := (d22 s x).bind "%i22" (.int 64 (candByte x 32))
def d24 (s : State) (x : BitVec 64) : State := (d23 s x).bind "%i23" (.int 1 (candTest x 32))
def d25 (s : State) (x : BitVec 64) : State := (d24 s x).bind "%i24" (.int 64 (candA3 x ||| c 549755813888))
def d26 (s : State) (x : BitVec 64) : State := (d25 s x).bind "%i25" (.int 64 (candA4 x))
def d27 (s : State) (x : BitVec 64) : State := (d26 s x).bind "%i26" (.int 64 (candW x >>> sh 40))
def d28 (s : State) (x : BitVec 64) : State := (d27 s x).bind "%i27" (.int 64 (candByte x 40))
def d29 (s : State) (x : BitVec 64) : State := (d28 s x).bind "%i28" (.int 1 (candTest x 40))
def d30 (s : State) (x : BitVec 64) : State := (d29 s x).bind "%i29" (.int 64 (candA4 x ||| c 140737488355328))
def d31 (s : State) (x : BitVec 64) : State := (d30 s x).bind "%i30" (.int 64 (candA5 x))
def d32 (s : State) (x : BitVec 64) : State := (d31 s x).bind "%i31" (.int 64 (candW x >>> sh 48))
def d33 (s : State) (x : BitVec 64) : State := (d32 s x).bind "%i32" (.int 64 (candByte x 48))
def d34 (s : State) (x : BitVec 64) : State := (d33 s x).bind "%i33" (.int 1 (candTest x 48))
def d35 (s : State) (x : BitVec 64) : State := (d34 s x).bind "%i34" (.int 64 (candA5 x ||| c 36028797018963968))
def d36 (s : State) (x : BitVec 64) : State := (d35 s x).bind "%i35" (.int 64 (candA6 x))
def d37 (s : State) (x : BitVec 64) : State := (d36 s x).bind "%i36" (.int 64 (candW x >>> sh 56))
def d38 (s : State) (x : BitVec 64) : State := (d37 s x).bind "%i37" (.int 64 (candByte x 56))
def d39 (s : State) (x : BitVec 64) : State := (d38 s x).bind "%i38" (.int 1 (candTest x 56))
def d40 (s : State) (x : BitVec 64) : State := (d39 s x).bind "%i39" (.int 64 (candA6 x ||| c (-9223372036854775808)))
def d41 (s : State) (x : BitVec 64) : State := (d40 s x).bind "%i40" (.int 64 (candA7 x))

/-- The state the body reaches from `s`, register by register. -/
def candidateRun (s : State) (x : BitVec 64) : State := d41 s x

theorem candStep1 (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) :
    evalInstr s (.binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612)) = some (d1 s x) := by
  simp [d1, evalInstr_xor_imm, State.bind, candW, argName, h0]

theorem candStep2 (s : State) (x : BitVec 64) :
    evalInstr (d1 s x) (.binop "%i1" .lshr 64 (.reg "%i") (lit 0)) = some (d2 s x) := by
  simp [d1, d2, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep3 (s : State) (x : BitVec 64) :
    evalInstr (d2 s x) (.binop "%i2" .and 64 (.reg "%i1") (lit 255)) = some (d3 s x) := by
  simp [d1, d2, d3, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep4 (s : State) (x : BitVec 64) :
    evalInstr (d3 s x) (.icmp "%i3" .eq 64 (.reg "%i2") (lit 0)) = some (d4 s x) := by
  simp [d1, d2, d3, d4, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep5 (s : State) (x : BitVec 64) :
    evalInstr (d4 s x) (.binop "%i4" .or 64 (lit 0) (lit 128)) = some (d5 s x) := by
  simp [d1, d2, d3, d4, d5, evalInstr_or_imm_imm, State.bind]

theorem candStep6 (s : State) (x : BitVec 64) :
    evalInstr (d5 s x) (.select "%i5" (.int 64) (.reg "%i3") (.reg "%i4") (lit 0)) = some (d6 s x) := by
  simp [d1, d2, d3, d4, d5, d6, evalInstr_select_reg_imm, State.bind, ite_int, candA0, candLane, lookupName]

theorem candStep7 (s : State) (x : BitVec 64) :
    evalInstr (d6 s x) (.binop "%i6" .lshr 64 (.reg "%i") (lit 8)) = some (d7 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep8 (s : State) (x : BitVec 64) :
    evalInstr (d7 s x) (.binop "%i7" .and 64 (.reg "%i6") (lit 255)) = some (d8 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep9 (s : State) (x : BitVec 64) :
    evalInstr (d8 s x) (.icmp "%i8" .eq 64 (.reg "%i7") (lit 0)) = some (d9 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep10 (s : State) (x : BitVec 64) :
    evalInstr (d9 s x) (.binop "%i9" .or 64 (.reg "%i5") (lit 32768)) = some (d10 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, evalInstr_or_imm, State.bind, lookupName]

theorem candStep11 (s : State) (x : BitVec 64) :
    evalInstr (d10 s x) (.select "%i10" (.int 64) (.reg "%i8") (.reg "%i9") (.reg "%i5")) = some (d11 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, evalInstr_select_reg, State.bind, ite_int, candA1, candA0, candLane, lookupName]

theorem candStep12 (s : State) (x : BitVec 64) :
    evalInstr (d11 s x) (.binop "%i11" .lshr 64 (.reg "%i") (lit 16)) = some (d12 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep13 (s : State) (x : BitVec 64) :
    evalInstr (d12 s x) (.binop "%i12" .and 64 (.reg "%i11") (lit 255)) = some (d13 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep14 (s : State) (x : BitVec 64) :
    evalInstr (d13 s x) (.icmp "%i13" .eq 64 (.reg "%i12") (lit 0)) = some (d14 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep15 (s : State) (x : BitVec 64) :
    evalInstr (d14 s x) (.binop "%i14" .or 64 (.reg "%i10") (lit 8388608)) = some (d15 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, evalInstr_or_imm, State.bind, lookupName]

theorem candStep16 (s : State) (x : BitVec 64) :
    evalInstr (d15 s x) (.select "%i15" (.int 64) (.reg "%i13") (.reg "%i14") (.reg "%i10")) = some (d16 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, evalInstr_select_reg, State.bind, ite_int, candA2, candA1, candLane, lookupName]

theorem candStep17 (s : State) (x : BitVec 64) :
    evalInstr (d16 s x) (.binop "%i16" .lshr 64 (.reg "%i") (lit 24)) = some (d17 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep18 (s : State) (x : BitVec 64) :
    evalInstr (d17 s x) (.binop "%i17" .and 64 (.reg "%i16") (lit 255)) = some (d18 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep19 (s : State) (x : BitVec 64) :
    evalInstr (d18 s x) (.icmp "%i18" .eq 64 (.reg "%i17") (lit 0)) = some (d19 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep20 (s : State) (x : BitVec 64) :
    evalInstr (d19 s x) (.binop "%i19" .or 64 (.reg "%i15") (lit 2147483648)) = some (d20 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, evalInstr_or_imm, State.bind, lookupName]

theorem candStep21 (s : State) (x : BitVec 64) :
    evalInstr (d20 s x) (.select "%i20" (.int 64) (.reg "%i18") (.reg "%i19") (.reg "%i15")) = some (d21 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, evalInstr_select_reg, State.bind, ite_int, candA3, candA2, candLane, lookupName]

theorem candStep22 (s : State) (x : BitVec 64) :
    evalInstr (d21 s x) (.binop "%i21" .lshr 64 (.reg "%i") (lit 32)) = some (d22 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep23 (s : State) (x : BitVec 64) :
    evalInstr (d22 s x) (.binop "%i22" .and 64 (.reg "%i21") (lit 255)) = some (d23 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep24 (s : State) (x : BitVec 64) :
    evalInstr (d23 s x) (.icmp "%i23" .eq 64 (.reg "%i22") (lit 0)) = some (d24 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep25 (s : State) (x : BitVec 64) :
    evalInstr (d24 s x) (.binop "%i24" .or 64 (.reg "%i20") (lit 549755813888)) = some (d25 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, evalInstr_or_imm, State.bind, lookupName]

theorem candStep26 (s : State) (x : BitVec 64) :
    evalInstr (d25 s x) (.select "%i25" (.int 64) (.reg "%i23") (.reg "%i24") (.reg "%i20")) = some (d26 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, evalInstr_select_reg, State.bind, ite_int, candA4, candA3, candLane, lookupName]

theorem candStep27 (s : State) (x : BitVec 64) :
    evalInstr (d26 s x) (.binop "%i26" .lshr 64 (.reg "%i") (lit 40)) = some (d27 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep28 (s : State) (x : BitVec 64) :
    evalInstr (d27 s x) (.binop "%i27" .and 64 (.reg "%i26") (lit 255)) = some (d28 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep29 (s : State) (x : BitVec 64) :
    evalInstr (d28 s x) (.icmp "%i28" .eq 64 (.reg "%i27") (lit 0)) = some (d29 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep30 (s : State) (x : BitVec 64) :
    evalInstr (d29 s x) (.binop "%i29" .or 64 (.reg "%i25") (lit 140737488355328)) = some (d30 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, evalInstr_or_imm, State.bind, lookupName]

theorem candStep31 (s : State) (x : BitVec 64) :
    evalInstr (d30 s x) (.select "%i30" (.int 64) (.reg "%i28") (.reg "%i29") (.reg "%i25")) = some (d31 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, evalInstr_select_reg, State.bind, ite_int, candA5, candA4, candLane, lookupName]

theorem candStep32 (s : State) (x : BitVec 64) :
    evalInstr (d31 s x) (.binop "%i31" .lshr 64 (.reg "%i") (lit 48)) = some (d32 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep33 (s : State) (x : BitVec 64) :
    evalInstr (d32 s x) (.binop "%i32" .and 64 (.reg "%i31") (lit 255)) = some (d33 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep34 (s : State) (x : BitVec 64) :
    evalInstr (d33 s x) (.icmp "%i33" .eq 64 (.reg "%i32") (lit 0)) = some (d34 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep35 (s : State) (x : BitVec 64) :
    evalInstr (d34 s x) (.binop "%i34" .or 64 (.reg "%i30") (lit 36028797018963968)) = some (d35 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, evalInstr_or_imm, State.bind, lookupName]

theorem candStep36 (s : State) (x : BitVec 64) :
    evalInstr (d35 s x) (.select "%i35" (.int 64) (.reg "%i33") (.reg "%i34") (.reg "%i30")) = some (d36 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, evalInstr_select_reg, State.bind, ite_int, candA6, candA5, candLane, lookupName]

theorem candStep37 (s : State) (x : BitVec 64) :
    evalInstr (d36 s x) (.binop "%i36" .lshr 64 (.reg "%i") (lit 56)) = some (d37 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, evalInstr_lshr_imm, State.bind, candW, sh, lookupName]

theorem candStep38 (s : State) (x : BitVec 64) :
    evalInstr (d37 s x) (.binop "%i37" .and 64 (.reg "%i36") (lit 255)) = some (d38 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, evalInstr_and_imm, State.bind, candW, sh, candByte, lookupName]

theorem candStep39 (s : State) (x : BitVec 64) :
    evalInstr (d38 s x) (.icmp "%i38" .eq 64 (.reg "%i37") (lit 0)) = some (d39 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, evalInstr_icmp_eq_imm, State.bind, candW, sh, candByte, candTest, lookupName] <;> congr 1

theorem candStep40 (s : State) (x : BitVec 64) :
    evalInstr (d39 s x) (.binop "%i39" .or 64 (.reg "%i35") (lit (-9223372036854775808))) = some (d40 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, evalInstr_or_imm, State.bind, lookupName]

theorem candStep41 (s : State) (x : BitVec 64) :
    evalInstr (d40 s x) (.select "%i40" (.int 64) (.reg "%i38") (.reg "%i39") (.reg "%i35")) = some (d41 s x) := by
  simp [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, evalInstr_select_reg, State.bind, ite_int, candA7, candA6, candLane, lookupName]

theorem candidate_block (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) :
    denoteCode candidateInstrs s = some (candidateRun s x) := by
  have h1 := candStep1 s x h0
  have h2 := candStep2 s x
  have h3 := candStep3 s x
  have h4 := candStep4 s x
  have h5 := candStep5 s x
  have h6 := candStep6 s x
  have h7 := candStep7 s x
  have h8 := candStep8 s x
  have h9 := candStep9 s x
  have h10 := candStep10 s x
  have h11 := candStep11 s x
  have h12 := candStep12 s x
  have h13 := candStep13 s x
  have h14 := candStep14 s x
  have h15 := candStep15 s x
  have h16 := candStep16 s x
  have h17 := candStep17 s x
  have h18 := candStep18 s x
  have h19 := candStep19 s x
  have h20 := candStep20 s x
  have h21 := candStep21 s x
  have h22 := candStep22 s x
  have h23 := candStep23 s x
  have h24 := candStep24 s x
  have h25 := candStep25 s x
  have h26 := candStep26 s x
  have h27 := candStep27 s x
  have h28 := candStep28 s x
  have h29 := candStep29 s x
  have h30 := candStep30 s x
  have h31 := candStep31 s x
  have h32 := candStep32 s x
  have h33 := candStep33 s x
  have h34 := candStep34 s x
  have h35 := candStep35 s x
  have h36 := candStep36 s x
  have h37 := candStep37 s x
  have h38 := candStep38 s x
  have h39 := candStep39 s x
  have h40 := candStep40 s x
  have h41 := candStep41 s x
  rw [show candidateInstrs =
      [(.binop "%i" .xor 64 (.reg argName) (lit 3182967604875373612)),
       (.binop "%i1" .lshr 64 (.reg "%i") (lit 0)),
       (.binop "%i2" .and 64 (.reg "%i1") (lit 255)),
       (.icmp "%i3" .eq 64 (.reg "%i2") (lit 0)),
       (.binop "%i4" .or 64 (lit 0) (lit 128)),
       (.select "%i5" (.int 64) (.reg "%i3") (.reg "%i4") (lit 0)),
       (.binop "%i6" .lshr 64 (.reg "%i") (lit 8)),
       (.binop "%i7" .and 64 (.reg "%i6") (lit 255)),
       (.icmp "%i8" .eq 64 (.reg "%i7") (lit 0)),
       (.binop "%i9" .or 64 (.reg "%i5") (lit 32768)),
       (.select "%i10" (.int 64) (.reg "%i8") (.reg "%i9") (.reg "%i5")),
       (.binop "%i11" .lshr 64 (.reg "%i") (lit 16)),
       (.binop "%i12" .and 64 (.reg "%i11") (lit 255)),
       (.icmp "%i13" .eq 64 (.reg "%i12") (lit 0)),
       (.binop "%i14" .or 64 (.reg "%i10") (lit 8388608)),
       (.select "%i15" (.int 64) (.reg "%i13") (.reg "%i14") (.reg "%i10")),
       (.binop "%i16" .lshr 64 (.reg "%i") (lit 24)),
       (.binop "%i17" .and 64 (.reg "%i16") (lit 255)),
       (.icmp "%i18" .eq 64 (.reg "%i17") (lit 0)),
       (.binop "%i19" .or 64 (.reg "%i15") (lit 2147483648)),
       (.select "%i20" (.int 64) (.reg "%i18") (.reg "%i19") (.reg "%i15")),
       (.binop "%i21" .lshr 64 (.reg "%i") (lit 32)),
       (.binop "%i22" .and 64 (.reg "%i21") (lit 255)),
       (.icmp "%i23" .eq 64 (.reg "%i22") (lit 0)),
       (.binop "%i24" .or 64 (.reg "%i20") (lit 549755813888)),
       (.select "%i25" (.int 64) (.reg "%i23") (.reg "%i24") (.reg "%i20")),
       (.binop "%i26" .lshr 64 (.reg "%i") (lit 40)),
       (.binop "%i27" .and 64 (.reg "%i26") (lit 255)),
       (.icmp "%i28" .eq 64 (.reg "%i27") (lit 0)),
       (.binop "%i29" .or 64 (.reg "%i25") (lit 140737488355328)),
       (.select "%i30" (.int 64) (.reg "%i28") (.reg "%i29") (.reg "%i25")),
       (.binop "%i31" .lshr 64 (.reg "%i") (lit 48)),
       (.binop "%i32" .and 64 (.reg "%i31") (lit 255)),
       (.icmp "%i33" .eq 64 (.reg "%i32") (lit 0)),
       (.binop "%i34" .or 64 (.reg "%i30") (lit 36028797018963968)),
       (.select "%i35" (.int 64) (.reg "%i33") (.reg "%i34") (.reg "%i30")),
       (.binop "%i36" .lshr 64 (.reg "%i") (lit 56)),
       (.binop "%i37" .and 64 (.reg "%i36") (lit 255)),
       (.icmp "%i38" .eq 64 (.reg "%i37") (lit 0)),
       (.binop "%i39" .or 64 (.reg "%i35") (lit (-9223372036854775808))),
       (.select "%i40" (.int 64) (.reg "%i38") (.reg "%i39") (.reg "%i35"))] from rfl]
  rw [denoteCode_cons_of _ _ _ _ h1]
  rw [denoteCode_cons_of _ _ _ _ h2]
  rw [denoteCode_cons_of _ _ _ _ h3]
  rw [denoteCode_cons_of _ _ _ _ h4]
  rw [denoteCode_cons_of _ _ _ _ h5]
  rw [denoteCode_cons_of _ _ _ _ h6]
  rw [denoteCode_cons_of _ _ _ _ h7]
  rw [denoteCode_cons_of _ _ _ _ h8]
  rw [denoteCode_cons_of _ _ _ _ h9]
  rw [denoteCode_cons_of _ _ _ _ h10]
  rw [denoteCode_cons_of _ _ _ _ h11]
  rw [denoteCode_cons_of _ _ _ _ h12]
  rw [denoteCode_cons_of _ _ _ _ h13]
  rw [denoteCode_cons_of _ _ _ _ h14]
  rw [denoteCode_cons_of _ _ _ _ h15]
  rw [denoteCode_cons_of _ _ _ _ h16]
  rw [denoteCode_cons_of _ _ _ _ h17]
  rw [denoteCode_cons_of _ _ _ _ h18]
  rw [denoteCode_cons_of _ _ _ _ h19]
  rw [denoteCode_cons_of _ _ _ _ h20]
  rw [denoteCode_cons_of _ _ _ _ h21]
  rw [denoteCode_cons_of _ _ _ _ h22]
  rw [denoteCode_cons_of _ _ _ _ h23]
  rw [denoteCode_cons_of _ _ _ _ h24]
  rw [denoteCode_cons_of _ _ _ _ h25]
  rw [denoteCode_cons_of _ _ _ _ h26]
  rw [denoteCode_cons_of _ _ _ _ h27]
  rw [denoteCode_cons_of _ _ _ _ h28]
  rw [denoteCode_cons_of _ _ _ _ h29]
  rw [denoteCode_cons_of _ _ _ _ h30]
  rw [denoteCode_cons_of _ _ _ _ h31]
  rw [denoteCode_cons_of _ _ _ _ h32]
  rw [denoteCode_cons_of _ _ _ _ h33]
  rw [denoteCode_cons_of _ _ _ _ h34]
  rw [denoteCode_cons_of _ _ _ _ h35]
  rw [denoteCode_cons_of _ _ _ _ h36]
  rw [denoteCode_cons_of _ _ _ _ h37]
  rw [denoteCode_cons_of _ _ _ _ h38]
  rw [denoteCode_cons_of _ _ _ _ h39]
  rw [denoteCode_cons_of _ _ _ _ h40]
  rw [denoteCode_cons_of _ _ _ _ h41]
  rfl

theorem lookupName_candidateRun (s : State) (x : BitVec 64) :
    lookupName (candidateRun s x).env "%i40" = some (.int 64 (candA7 x)) := by
  simp [candidateRun, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30,
    d31, d32, d33, d34, d35, d36, d37, d38, d39, d40, d41, State.bind]

theorem candidateRun_mem (s : State) (x : BitVec 64) : (candidateRun s x).mem = s.mem := rfl

/-- The candidate's eight lanes are the fold in `CommaMask.byteLoop`.  Each lane
contributes the same byte test and the same bit; `sh` is `8 * k` at the literals
clang emitted, and the lane constants are the emitted numerals. -/
theorem candOut_eq_byteLoop (x : BitVec 64) : candOut x = byteLoop x := by
  have h0 : sh 0 = 8 * 0 := by decide
  have h8 : sh 8 = 8 * 1 := by decide
  have h16 : sh 16 = 8 * 2 := by decide
  have h24 : sh 24 = 8 * 3 := by decide
  have h32 : sh 32 = 8 * 4 := by decide
  have h40 : sh 40 = 8 * 5 := by decide
  have h48 : sh 48 = 8 * 6 := by decide
  have h56 : sh 56 = 8 * 7 := by decide
  have b0 : c 128 = (0x80 : BitVec 64) <<< (8 * 0) := by decide
  have b1 : c 32768 = (0x80 : BitVec 64) <<< (8 * 1) := by decide
  have b2 : c 8388608 = (0x80 : BitVec 64) <<< (8 * 2) := by decide
  have b3 : c 2147483648 = (0x80 : BitVec 64) <<< (8 * 3) := by decide
  have b4 : c 549755813888 = (0x80 : BitVec 64) <<< (8 * 4) := by decide
  have b5 : c 140737488355328 = (0x80 : BitVec 64) <<< (8 * 5) := by decide
  have b6 : c 36028797018963968 = (0x80 : BitVec 64) <<< (8 * 6) := by decide
  have b7 : c (-9223372036854775808) = (0x80 : BitVec 64) <<< (8 * 7) := by decide
  have z : c 0 = (0 : BitVec 64) := by decide
  have m255 : c 255 = (0xFF : BitVec 64) := by decide
  simp only [candOut, candA7, candA6, candA5, candA4, candA3, candA2, candA1, candA0,
    candLane, candTest, candByte, candW, byteLoop, List.foldl_cons, List.foldl_nil,
    ofBool_eq_one, h0, h8, h16, h24, h32, h40, h48, h56,
    b0, b1, b2, b3, b4, b5, b6, b7, z, m255, c_comma] <;> rfl

theorem candA7_eq_byteLoop (x : BitVec 64) : candA7 x = byteLoop x := candOut_eq_byteLoop x

theorem candidate_step_body (s : State) (x : BitVec 64)
    (h0 : lookupName s.env "%arg" = some (.int 64 x)) (hpc : s.pc = "bb") :
    step candidateFunction s = .ret (some (.int 64 (byteLoop x))) (candidateRun s x) := by
  have hfind : candidateFunction.findBlock s.pc = some candidateBody := by
    simp [hpc, candidateFunction, candidateBody, Function.findBlock, findBlockList]
  simp only [step, hfind, candidateBody]
  rw [candidate_block s x h0]
  simp [execTerm, evalOperand, lookupName_candidateRun, candA7_eq_byteLoop]

theorem lookupName_initState_candidate (x : BitVec 64) :
    lookupName (initState candidateFunction [.int 64 x]).env "%arg" = some (.int 64 x) := by
  simp only [initState, candidateFunction, List.map, List.zip, List.zipWith, lookupName,
    ite_true, argName]

theorem candidate_initState_mem (x : BitVec 64) :
    (initState candidateFunction [.int 64 x]).mem = [] := rfl

theorem candidate_runFuel (x : BitVec 64) :
    ∀ n, runFuel (n + 1) candidateFunction (initState candidateFunction [.int 64 x]) =
      some (.ret (some (.int 64 (byteLoop x))) []) := by
  intro n
  cases n with
  | zero =>
      simp only [runFuel, candidate_step_body _ x (lookupName_initState_candidate x) rfl,
        candidateRun_mem, candidate_initState_mem]
  | succ k =>
      simp only [runFuel, candidate_step_body _ x (lookupName_initState_candidate x) rfl,
        candidateRun_mem, candidate_initState_mem]

theorem candidate_runFuel_none_or (x : BitVec 64) :
    ∀ n, runFuel n candidateFunction (initState candidateFunction [.int 64 x]) = none ∨
      runFuel n candidateFunction (initState candidateFunction [.int 64 x]) =
        some (.ret (some (.int 64 (byteLoop x))) []) := by
  intro n
  cases n with
  | zero => exact Or.inl rfl
  | succ k => exact Or.inr (candidate_runFuel x k)

/-! ### The two functions agree on every argument list -/

theorem initState_cons_baseline (a : Value) (rest : List Value) :
    initState baselineFunction (a :: rest) = initState baselineFunction [a] := rfl

theorem initState_cons_candidate (a : Value) (rest : List Value) :
    initState candidateFunction (a :: rest) = initState candidateFunction [a] := rfl

/-- On an `i64` argument the baseline returns `swar` and nothing else. -/
theorem baseline_beh_int (x : BitVec 64) (rest : List Value) (o : Outcome) :
    Beh baselineFunction (.int 64 x :: rest) o ↔
      o = .ret (some (.int 64 (swar x))) [] := by
  constructor
  · intro h
    rw [Beh, initState_cons_baseline] at h
    rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
    · rcases baseline_runFuel_none_or x n with h' | h' <;> rw [h'] at hn <;> simp at hn
    · rcases baseline_runFuel_none_or x n with h' | h' <;> rw [h'] at hn
      · simp at hn
      · exact (Option.some.inj hn).symm
  · intro h
    subst h
    exact Or.inr ⟨2, baseline_runFuel x 0⟩

/-- On an `i64` argument the candidate returns `byteLoop` and nothing else. -/
theorem candidate_beh_int (x : BitVec 64) (rest : List Value) (o : Outcome) :
    Beh candidateFunction (.int 64 x :: rest) o ↔
      o = .ret (some (.int 64 (byteLoop x))) [] := by
  constructor
  · intro h
    rw [Beh, initState_cons_candidate] at h
    rcases h with ⟨n, hn⟩ | ⟨n, hn⟩
    · rcases candidate_runFuel_none_or x n with h' | h' <;> rw [h'] at hn <;> simp at hn
    · rcases candidate_runFuel_none_or x n with h' | h' <;> rw [h'] at hn
      · simp at hn
      · exact (Option.some.inj hn).symm
  · intro h
    subst h
    exact Or.inr ⟨1, candidate_runFuel x 0⟩

/-- The baseline refuses any other argument list by reaching `ub` at its first
instruction. -/
theorem baseline_beh_other (a : Value) (rest : List Value)
    (hne : ∀ x, a ≠ .int 64 x) (o : Outcome) :
    Beh baselineFunction (a :: rest) o := by
  obtain ⟨w, v⟩ | ⟨p⟩ := a
  · have hw : w ≠ 64 := by
      intro hw
      subst hw
      exact hne v rfl
    refine Or.inl ⟨2, ?_⟩
    simp [runFuel, step, baselineFunction, baselineEntry, baselineBody,
      Function.findBlock, findBlockList, Function.entry?, initState, List.head?, Option.map,
      Option.getD, List.map, List.zip, List.zipWith, denoteCode, baselineInstrs, execTerm,
      evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c, argName, hw]
  · refine Or.inl ⟨2, ?_⟩
    simp [runFuel, step, baselineFunction, baselineEntry, baselineBody,
      Function.findBlock, findBlockList, Function.entry?, initState, List.head?, Option.map,
      Option.getD, List.map, List.zip, List.zipWith, denoteCode, baselineInstrs, execTerm,
      evalInstr, evalOperand, Const.toValue, Value.intToNat, lit, c, argName]

/-- The candidate refuses any other argument list in the same way. -/
theorem candidate_beh_other (a : Value) (rest : List Value)
    (hne : ∀ x, a ≠ .int 64 x) (o : Outcome) :
    Beh candidateFunction (a :: rest) o := by
  obtain ⟨w, v⟩ | ⟨p⟩ := a
  · have hw : w ≠ 64 := by
      intro hw
      subst hw
      exact hne v rfl
    refine Or.inl ⟨1, ?_⟩
    simp [runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, initState, List.head?, Option.map, Option.getD,
      List.map, List.zip, List.zipWith, denoteCode, candidateInstrs, evalInstr,
      evalOperand, Const.toValue, Value.intToNat, lit, c, argName, hw]
  · refine Or.inl ⟨1, ?_⟩
    simp [runFuel, step, candidateFunction, candidateBody, Function.findBlock,
      findBlockList, Function.entry?, initState, List.head?, Option.map, Option.getD,
      List.map, List.zip, List.zipWith, denoteCode, candidateInstrs, evalInstr,
      evalOperand, Const.toValue, Value.intToNat, lit, c, argName]

/-- With no argument the parameter is unbound, so the first instruction is
undefined. -/
theorem baseline_beh_nil (o : Outcome) : Beh baselineFunction [] o := by
  refine Or.inl ⟨2, ?_⟩
  simp [runFuel, step, baselineFunction, baselineEntry, baselineBody,
    Function.findBlock, findBlockList, Function.entry?, initState, List.head?, Option.map,
    Option.getD, List.zip, denoteCode, baselineInstrs, execTerm,
    evalInstr, evalOperand, Const.toValue, lit, c, argName, lookupName]

theorem candidate_beh_nil (o : Outcome) : Beh candidateFunction [] o := by
  refine Or.inl ⟨1, ?_⟩
  simp [runFuel, step, candidateFunction, candidateBody, Function.findBlock,
    findBlockList, Function.entry?, initState, List.head?, Option.map, Option.getD,
    List.zip, denoteCode, candidateInstrs, evalInstr,
    evalOperand, Const.toValue, lit, c, argName]

/-- The emitted candidate refines the emitted baseline: on an `i64` argument both
return the specification, and on every other argument list both reach `ub`,
which admits every outcome. -/
theorem IR_refines : LeanLLVM.Refines candidateFunction baselineFunction := by
  intro args o h
  match args with
  | [] => exact baseline_beh_nil o
  | a :: rest =>
    match a with
    | .int w v =>
      by_cases hw : w = 64
      · subst hw
        have hc := (candidate_beh_int v rest o).1 h
        have heq : byteLoop v = swar v := (byteLoop_eq_spec v).trans (swar_eq_spec v).symm
        rw [hc, heq]
        exact (baseline_beh_int v rest _).2 rfl
      · have hne : ∀ y, (Value.int w v : Value) ≠ .int 64 y := by
          intro y hy
          injection hy with hw' _
          exact hw hw'
        exact baseline_beh_other _ _ hne o
    | .ptr p =>
      have hne : ∀ y, (Value.ptr p : Value) ≠ .int 64 y := by
        intro y hy
        cases hy
      exact baseline_beh_other _ _ hne o

end LeanLLVM.Vellum.CommaMaskIR
