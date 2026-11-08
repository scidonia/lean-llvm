/-
The step corpus of the entry unit's emitted bodies.

`JsonEntryIR` holds the fixture, its AST pin, the call environment
`entryCalls`, the address-free table and the specification vocabulary the
theorem is stated in.  This module holds the execution: one step lemma per
instruction shape the two bodies use, the block-level compositions, and the
vocabulary the headline theorem `entry_pos8_refines` and its companions are
stated in.

## The shape of a step

A step is stated at an **opaque environment** — `withEnv env s`, with the
operands it reads as *hypotheses* — and its conclusion adds one cell to that
environment.  No goal therefore contains a nested `State.bind`, so a lookup is a
head test plus a bounded skip, never a walk down a state chain.  This is the
shape `JsonS1MasksSteps` measured as linear in instruction count and independent
of depth, and it is adopted here rather than rediscovered.

The block compositions resolve each step's operand lookups with `ent_lk`: peel
the cells bound after the register, then take the cell, or the caller's
environment for a parameter.  The values are *not* named in the compositions —
they are inferred from the step lemma's hypothesis by unification, which is what
keeps a hundred-instruction chain readable.

## What the headline theorem's clauses are

`entry_pos8_refines` states three things about one call of the pinned POS8 body:
the returned cursor is the starting cursor plus the stream's population count;
the `k' - k` words at `[k, k')` are the model's positions; and no byte outside
`[o, o + 4 * (k' + 8))` moved.  The last clause's bound is the body's own: POS8
stores a whole eight-lane table row per group *unconditionally*, so its final
group writes lane `k' + 7` even when the trailing byte is zero, and the first
lane it never writes is `k' + 8` — the sentinel lane the route reads.
-/
import LeanLLVM.Vellum.JsonEntryIR
import LeanLLVM.Vellum.JsonS1MasksIR

namespace LeanLLVM.Vellum.JsonEntrySteps

open LeanLLVM
open LeanLLVM.Vellum.JsonEntryIR
open LeanLLVM.Vellum.JsonScanSpec
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.JsonS1MasksIR
  (lookupName_bind_ne lookupName_bind_self evalInstr_load evalInstr_binop
   evalInstr_binopVec evalInstr_icmp evalInstr_zext evalInstr_store evalInstr_call
   evalOperands_cons evalInstr_extractelement vecLanes_self)

/-! ### The step vocabulary -/

/-- Straight-line composition: an instruction that resolves to a state leaves the
rest of the list to be run from it. -/
theorem denoteCode_cons_of (calls : Calls) (i : Instr) (is : List Instr) (s s' : State)
    (h : evalInstr calls s i = some s') :
    denoteCode calls (i :: is) s = denoteCode calls is s' := by
  simp [denoteCode, h]

/-- A straight-line sequence splits anywhere. -/
theorem denoteCode_append (calls : Calls) (a b : List Instr) (s : State) :
    denoteCode calls (a ++ b) s = (denoteCode calls a s).bind (denoteCode calls b) := by
  induction a generalizing s with
  | nil => rfl
  | cons i is ih =>
      simp only [List.cons_append, denoteCode]
      cases h : evalInstr calls s i with
      | none => rfl
      | some s' => exact ih s'

/-- A state seen as its environment: the composition's subject.  Everything a step
does not touch — memory, the allocator cursor, the block, the predecessor — is
carried through unchanged. -/
def withEnv (env : Env) (s : State) : State := { s with env := env }

/-- The environment of a run is not observed by `State.mem`. -/
theorem withEnv_mem (env : Env) (s : State) : (withEnv env s).mem = s.mem := rfl

/-- Resolve a register in the run's environment: peel the cells bound after it,
then take the cell it is, or the caller's environment when it is a parameter. -/
macro "ent_lk " h:term : tactic =>
  `(tactic| ((repeat rw [lookupName_cons_ne _ _ (by decide)]); (first
      | exact lookupName_cons_self _ _ _
      | exact $h)))

/-- The value a register reads, as the hypothesis a step consumes. -/
theorem evalOperand_reg_of (env : Env) (s : State) (n : String) (v : Value)
    (h : lookupName env n = some v) : evalOperand (withEnv env s) (.reg n) = some v := by
  simp only [withEnv, evalOperand, h]

/-- The eight-lane vector `x` broadcast: the shape `insertelement` + `shufflevector`
produces for a group's block base. -/
def splatVec (x : BitVec 32) : List (BitVec 32) := x :: List.replicate 7 0

/-- The eight zero lanes the emission's `zeroinitializer` names. -/
def zeroVec : List (BitVec 32) := List.replicate 8 0

/-- A literal operand reads to its integer constant. -/
theorem evalOperand_lit_of (s : State) (w : Nat) (c : BitVec w) :
    evalOperand s (.imm (.int w c)) = some (.int w c) := rfl

/-- `BitVec.ofNat` of an overflowing sum is the sum. -/
theorem ofNat_toNat_add {w : Nat} (x y : BitVec w) :
    BitVec.ofNat w ((x.toNat + y.toNat) % 2 ^ w) = x + y := by
  rw [← BitVec.toNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `BitVec.ofNat` of a shifted word is the shifted word. -/
theorem ofNat_toNat_shl {w : Nat} (x : BitVec w) (n : Nat) :
    BitVec.ofNat w (x.toNat <<< n % 2 ^ w) = x <<< n := by
  rw [← BitVec.toNat_shiftLeft, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `BitVec.ofNat` of a logical shift is the logical shift. -/
theorem ofNat_toNat_lshr {w : Nat} (x : BitVec w) (n : Nat) :
    BitVec.ofNat w (x.toNat >>> n) = x >>> n := by
  rw [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The eight bytes of a 64-bit word are `2 ^ 64`. -/
theorem pow256_eight : (256 : Nat) ^ 8 = 2 ^ 64 := by decide

/-! #### The scalar steps -/

/-- `%d = trunc i64 %src to i32` and the sibling widths. -/
theorem step_trunc (env : Env) (s : State) (d src : String) (wIn wOut : Nat)
    (x : BitVec wIn) (h : lookupName env src = some (.int wIn x)) :
    evalInstr entryCalls (withEnv env s) (.trunc d wIn wOut (.reg src)) =
      some (withEnv ((d, .int wOut (BitVec.ofNat wOut (x.toNat % 2 ^ wOut))) :: env) s) := by
  have hx := evalOperand_reg_of env s src (.int wIn x) h
  simp only [evalInstr, hx, State.bind]
  rfl

/-- `%d = zext i32 %src to i64`. -/
theorem step_zext (env : Env) (s : State) (d src : String) (wIn wOut : Nat)
    (x : BitVec wIn) (h : lookupName env src = some (.int wIn x)) :
    evalInstr entryCalls (withEnv env s) (.zext d wIn wOut (.reg src)) =
      some (withEnv ((d, .int wOut (BitVec.ofNat wOut x.toNat)) :: env) s) := by
  rw [evalInstr_zext (hv := evalOperand_reg_of env s src (.int wIn x) h)]
  simp [withEnv, State.bind]

/-- Every scalar binop step shares the `BitVec.ofNat` boundary. -/
theorem evalInstr_binop_of (env : Env) (s : State) (d src : String) (op : BinOp) (w : Nat)
    (x c : BitVec w) (r : Nat)
    (h : lookupName env src = some (.int w x))
    (hr : evalBinopNat op w x.toNat c.toNat = some r) :
    evalInstr entryCalls (withEnv env s) (.binop d op w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (BitVec.ofNat w r)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c) (hr := hr)]
  simp [withEnv, State.bind]

/-- `%d = and i32 %src, <c>`. -/
theorem step_and_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.binop d .and w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x &&& c)) :: env) s) := by
  rw [evalInstr_binop_of env s d src .and w x c _ h (by rfl)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = or i32 %src, <c>`. -/
theorem step_or_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.binop d .or w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x ||| c)) :: env) s) := by
  rw [evalInstr_binop_of env s d src .or w x c _ h (by rfl)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = add i64 %a, %b`. -/
theorem step_add_reg (env : Env) (s : State) (d a b : String) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr entryCalls (withEnv env s) (.binop d .add w (.reg a) (.reg b)) =
      some (withEnv ((d, .int w (x + y)) :: env) s) := by
  rw [evalInstr_binop (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb) (hr := by rfl)]
  simp only [withEnv, State.bind, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = add i64 %src, <c>`. -/
theorem step_add_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.binop d .add w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x + c)) :: env) s) := by
  rw [evalInstr_binop_of env s d src .add w x c _ h (by rfl)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = shl i32 %src, <c>`. -/
theorem step_shl_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.binop d .shl w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x <<< c.toNat)) :: env) s) := by
  rw [evalInstr_binop_of env s d src .shl w x c _ h (by rfl)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `%d = lshr i64 %src, <c>`. -/
theorem step_lshr_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.binop d .lshr w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int w (x >>> c.toNat)) :: env) s) := by
  rw [evalInstr_binop_of env s d src .lshr w x c _ h (by rfl)]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-- `%d = icmp eq i64 %src, <c>`. -/
theorem step_icmp_eq_imm (env : Env) (s : State) (d src : String) (w : Nat)
    (x c : BitVec w) (h : lookupName env src = some (.int w x)) :
    evalInstr entryCalls (withEnv env s) (.icmp d .eq w (.reg src) (.imm (.int w c))) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x = c))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s src (.int w x) h)
    (hb := evalOperand_lit_of _ w c)]
  simp [withEnv, State.bind, evalICmp]

/-- `%d = icmp eq i64 %a, %b`. -/
theorem step_icmp_eq_reg (env : Env) (s : State) (d a b : String) (w : Nat)
    (x y : BitVec w) (ha : lookupName env a = some (.int w x))
    (hb : lookupName env b = some (.int w y)) :
    evalInstr entryCalls (withEnv env s) (.icmp d .eq w (.reg a) (.reg b)) =
      some (withEnv ((d, .int 1 (BitVec.ofBool (x = y))) :: env) s) := by
  rw [evalInstr_icmp (ha := evalOperand_reg_of env s a (.int w x) ha)
    (hb := evalOperand_reg_of env s b (.int w y) hb)]
  simp [withEnv, State.bind, evalICmp]

/-! #### The pointer steps -/

/-- `%d = getelementptr <elem>, ptr %base, i64 %off`, at an index below `2 ^ 63`. -/
theorem step_gep64 (env : Env) (s : State) (d base off : String) (elem : Ty)
    (a : Nat) (idx : BitVec 64)
    (hb : lookupName env base = some (.ptr a))
    (ho : lookupName env off = some (.int 64 idx))
    (hpos : idx.toNat < 2 ^ 63) :
    evalInstr entryCalls (withEnv env s) (.gep d elem (.reg base) (.reg off)) =
      some (withEnv ((d, .ptr (a + idx.toNat * elem.sizeBytes)) :: env) s) := by
  rw [evalInstr_gep (hb := evalOperand_reg_of env s base (.ptr a) hb)
    (ho := evalOperand_reg_of env s off (.int 64 idx) ho)
    (hpos := by simpa using hpos)]
  simp only [withEnv, State.bind, BitVec.signExtend_eq]

/-- A 64-bit load at a readable word. -/
theorem loadValue_i64 (m : Mem) (addr : Nat) (v : BitVec 64)
    (h : readBytes m addr 8 = some (natToBytes v.toNat 8)) :
    loadValue m (.int 64) addr = some (.int 64 v) := by
  simp only [loadValue, show (64 + 7) / 8 = 8 from rfl]
  simp only [show (64 = 0) = False from by decide, ite_false]
  rw [h]
  simp only [natToBytes_toNat, pow256_eight, Nat.mod_eq_of_lt v.isLt,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A row load at the thirty-two bytes the table row occupies. -/
theorem loadValue_row (m : Mem) (addr : Nat) (lanes : List (BitVec 32)) (bs : List UInt8)
    (hb : bs.length = 32) (hr : readBytes m addr 32 = some bs)
    (hl : unpackLanes 32 8 (bytesToNat bs) = lanes) :
    loadValue m v8i32 addr = some (.vec 8 32 lanes) := by
  rw [loadValue_vec_int (by decide) (by decide) (by simpa using hr), hl]

/-- `%d = load i64, ptr %p`, at the eight bytes a 64-bit word occupies. -/
theorem step_load64 (env : Env) (s : State) (d p : String) (a : Nat) (v : BitVec 64)
    (hp : lookupName env p = some (.ptr a))
    (hv : readBytes s.mem a 8 = some (natToBytes v.toNat 8)) :
    evalInstr entryCalls (withEnv env s) (.load d (.int 64) (.reg p)) =
      some (withEnv ((d, .int 64 v) :: env) s) := by
  rw [evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by
      rw [show (withEnv env s).mem = s.mem from rfl]
      exact loadValue_i64 s.mem a v hv)]
  simp [withEnv, State.bind]

/-- `%d = load <8 x i32>, ptr %p`, at the thirty-two bytes a row occupies. -/
theorem step_load_vec (env : Env) (s : State) (d p : String) (a : Nat)
    (lanes : List (BitVec 32)) (bs : List UInt8)
    (hp : lookupName env p = some (.ptr a))
    (hb : bs.length = 32) (hr : readBytes s.mem a 32 = some bs)
    (hl : unpackLanes 32 8 (bytesToNat bs) = lanes) :
    evalInstr entryCalls (withEnv env s) (.load d v8i32 (.reg p)) =
      some (withEnv ((d, .vec 8 32 lanes) :: env) s) := by
  rw [evalInstr_load (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hv := by
      rw [show (withEnv env s).mem = s.mem from rfl]
      exact loadValue_row s.mem a lanes bs hb hr hl)]
  simp [withEnv, State.bind]

/-- `store <8 x i32> %v, ptr %p`: lane `k` at bits `[32k, 32k + 32)`. -/
theorem step_store_vec (env : Env) (s : State) (v p : String) (a : Nat)
    (lanes : List (BitVec 32))
    (hv : lookupName env v = some (.vec 8 32 lanes))
    (hp : lookupName env p = some (.ptr a))
    (hlen : lanes.length = 8) :
    evalInstr entryCalls (withEnv env s) (.store v8i32 (.reg v) (.reg p)) =
      some (withEnv env { s with
        mem := writeBytes s.mem a (natToBytes (packLanes lanes) 32) }) := by
  rw [evalInstr_store (hv := evalOperand_reg_of env s v (.vec 8 32 lanes) hv)
    (hp := evalOperand_reg_of env s p (.ptr a) hp)
    (hs := by
      have hb : 8 * 32 % 8 = 0 := by decide
      simp [storeValue, hlen, hb]
      rfl)]
  simp [withEnv, State.bind]

/-! #### The lane steps -/

/-- `BitVec.ofNat` of a word's own width is the word. -/
theorem ofNat_toNat_32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `%d = insertelement <8 x i32> undef, i32 %src, i64 0`: lane 0 is the value
and the rest are the `zeroinitializer` the emission names. -/
theorem step_insertelement (env : Env) (s : State) (d src : String) (base : Operand)
    (x : BitVec 32) (h : lookupName env src = some (.int 32 x))
    (hbase : evalOperand (withEnv env s) base = some (.vec 8 32 zeroVec)) :
    evalInstr entryCalls (withEnv env s)
        (.insertelement d 8 32 base (.reg src) (.imm (.int 64 (BitVec.ofInt 64 0)))) =
      some (withEnv ((d, .vec 8 32 (splatVec x)) :: env) s) := by
  have hidx : evalOperand (withEnv env s) (.imm (.int 64 (BitVec.ofInt 64 0))) =
      some (.int 64 (BitVec.ofInt 64 0)) := rfl
  rw [evalInstr_insertelement (hv := hbase)
    (hl := vecLanes_self (by decide))
    (he := evalOperand_reg_of env s src (.int 32 x) h)
    (hx := rfl)
    (hi := hidx)
    (hk := by decide)]
  simp only [withEnv, State.bind, zeroVec, ofNat_toNat_32]
  rfl

/-- A broadcast vector has eight lanes. -/
theorem splatVec_length (x : BitVec 32) : (splatVec x).length = 8 := by simp [splatVec]

/-- The zero vector has eight lanes. -/
theorem zeroVec_length : zeroVec.length = 8 := by simp [zeroVec]

/-- A lane-wise add against a broadcast: the first operand's lanes, each offset. -/
theorem zip_replicate_mapM_add (l : List (BitVec 32)) (x : BitVec 32) :
    (l.zip (List.replicate l.length x)).mapM (fun p => evalBinop .add p.1 p.2) =
      some (l.map (fun v => v + x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, List.mapM_cons,
        List.map_cons]
      rw [ih]
      rfl

/-! #### The vector steps -/

/-- `%d = shufflevector <8 x i32> %a, <8 x i32> zeroinitializer, <8 x i32> zeroinitializer`:
every mask entry selects lane 0 of the first operand, so the result is lane 0
broadcast. -/
theorem step_shuffle_splat (env : Env) (s : State) (d a : String) (b : Operand)
    (x : BitVec 32)
    (ha : lookupName env a = some (.vec 8 32 (splatVec x)))
    (hb : evalOperand (withEnv env s) b = some (.vec 8 32 zeroVec)) :
    evalInstr entryCalls (withEnv env s)
        (.shuffleVec d 8 32 (.reg a) b [0, 0, 0, 0, 0, 0, 0, 0]) =
      some (withEnv ((d, .vec 8 32 (List.replicate 8 x)) :: env) s) := by
  have hA : Value.vecLanes 8 32 (.vec 8 32 (splatVec x)) = some (splatVec x) :=
    vecLanes_self (splatVec_length x)
  have hB : Value.vecLanes 8 32 (.vec 8 32 zeroVec) = some zeroVec :=
    vecLanes_self (by simp [zeroVec])
  have hm : ([0, 0, 0, 0, 0, 0, 0, 0] : List Nat).mapM
      (fun k => if k < 8 then (splatVec x)[k]? else zeroVec[k - 8]?)
      = some (List.replicate 8 x) := by
    simp [splatVec]
  have hoa := evalOperand_reg_of env s a (.vec 8 32 (splatVec x)) ha
  simp only [evalInstr, hoa, hb]
  simp only [hA, hB, hm]
  simp [withEnv, State.bind]

/-- `%d = add <8 x i32> %a, %b` at a broadcast second operand: the lane-wise sum
is the first operand's lanes offset by the broadcast value. -/
theorem step_addVec_splat (env : Env) (s : State) (d a b : String)
    (lanes : List (BitVec 32)) (x : BitVec 32)
    (ha : lookupName env a = some (.vec 8 32 lanes))
    (hb : lookupName env b = some (.vec 8 32 (List.replicate 8 x)))
    (hlen : lanes.length = 8) :
    evalInstr entryCalls (withEnv env s) (.binopVec d .add 8 32 (.reg a) (.reg b)) =
      some (withEnv ((d, .vec 8 32 (lanes.map (fun v => v + x))) :: env) s) := by
  have h2 : (List.replicate 8 x).length = 8 := by simp
  have hm : (lanes.zip (List.replicate 8 x)).mapM (fun p => evalBinop .add p.1 p.2)
      = some (lanes.map (fun v => v + x)) := by
    rw [← hlen, zip_replicate_mapM_add]
  rw [evalInstr_binopVec (h1 := hlen) (h2 := h2)
    (ha := evalOperand_reg_of env s a (.vec 8 32 lanes) ha)
    (hb := evalOperand_reg_of env s b (.vec 8 32 (List.replicate 8 x)) hb) (hm := hm)]
  simp [withEnv, State.bind]

/-- The 32-bit population count a group's byte is counted with. -/
theorem step_call_ctpop32 (env : Env) (s : State) (d src : String) (x : BitVec 32)
    (h : lookupName env src = some (.int 32 x)) :
    evalInstr entryCalls (withEnv env s)
        (.call d (.int 32) "llvm.ctpop.i32" [((.int 32), (.reg src))]) =
      some (withEnv ((d, .int 32 (BitVec.ofNat 32 (BitLanes.ctpop x))) :: env) s) := by
  have ha : evalOperands (withEnv env s) [((.int 32), (.reg src))] =
      some [.int 32 x] := by
    rw [evalOperands_cons (by exact evalOperand_reg_of env s src (.int 32 x) h) rfl]
  rw [evalInstr_call ha (entryCalls_ctpop32 x s.mem s.next)]
  simp [withEnv, State.bind]

/-- The 64-bit population count the block's word is counted with. -/
theorem step_call_ctpop64 (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr entryCalls (withEnv env s)
        (.call d (.int 64) "llvm.ctpop.i64" [((.int 64), (.reg src))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (BitLanes.ctpop x))) :: env) s) := by
  have ha : evalOperands (withEnv env s) [((.int 64), (.reg src))] =
      some [.int 64 x] := by
    rw [evalOperands_cons (by exact evalOperand_reg_of env s src (.int 64 x) h) rfl]
  rw [evalInstr_call ha (entryCalls_ctpop64 x s.mem s.next)]
  simp [withEnv, State.bind]


def groupLane (base j : Nat) : BitVec 32 := BitVec.ofNat 32 (base + 8 * j)
def groupPop (w : BitVec 64) (j : Nat) : Nat :=
  (setLanes (BitVec.ofNat 8 (byteOf w j))).length
def groupCursor (w : BitVec 64) (k j : Nat) : Nat :=
  k + ((List.range j).map (groupPop w)).sum

/-- The eight lanes group `j` stores: the table row for the byte, each lane
offset by the group's place in the block. -/
def groupVec (w : BitVec 64) (base j : Nat) : List (BitVec 32) :=
  (pos8Row (byteOf w j)).map (fun v => v + groupLane base j)

/-- The block's memory: group `j`'s row written at group `j`'s cursor, in
group order. -/
def blockMem (o : Nat) (w : BitVec 64) (base k : Nat) : Nat → Mem → Mem
  | 0, mem => mem
  | j + 1, mem =>
      writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
        (natToBytes (packLanes (groupVec w base j)) 32)

theorem groupCursor_succ (w : BitVec 64) (k j : Nat) :
    groupCursor w k (j + 1) = groupCursor w k j + groupPop w j := by
  unfold groupCursor
  rw [List.range_succ, List.map_append, List.sum_append]
  simp
  omega

theorem groupCursor_eight (w : BitVec 64) (k : Nat) :
    groupCursor w k 8 = k + ctpop w := by
  unfold groupCursor
  rw [ctpop_eq_setLanes_length, setLanes_eq_bytes, List.length_flatten]
  congr 1
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  simp [groupPop, Function.comp_def, List.length_map]


/-- Dropping past one list's length leaves the other's tail. -/
theorem drop_append_length {α : Type} (A b : List α) (k : Nat) :
    (A ++ b).drop (A.length + k) = b.drop k := by
  induction A with
  | nil => simp
  | cons a t ih =>
      rw [List.cons_append, List.length_cons]
      rw [show (t.length + 1) + k = (t.length + k) + 1 from by omega]
      rw [List.drop_succ_cons]
      exact ih

theorem flatMap_range_drop (f : Nat → List UInt8) (hlen : ∀ i, (f i).length = 32) :
    ∀ (n i : Nat), i < n →
      ((List.range n).flatMap f).drop (i * 32) =
        f i ++ ((List.range n).flatMap f).drop ((i + 1) * 32) := by
  intro n
  induction n with
  | zero => intro i h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
      intro i h
      rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil]
      have hA : ((List.range n).flatMap f).length = n * 32 := by
        rw [List.length_flatMap]
        rw [show (List.map (fun a => (f a).length) (List.range n)).sum = n * 32 from by
          rw [show (List.map (fun a => (f a).length) (List.range n)) =
            List.map (fun _ => 32) (List.range n) from by
            apply List.map_congr_left
            intro a _
            exact hlen a]
          rw [List.map_const', List.length_range, sum_replicate]]
      by_cases hi : i < n
      · rw [List.drop_append_of_le_length (by omega)]
        rw [ih i hi]
        rw [List.append_assoc]
        congr 1
        rw [List.drop_append_of_le_length (by omega)]
      · have hi' : i = n := by omega
        subst i
        have hnext : (n + 1) * 32 = ((List.range n).flatMap f).length + 32 := by
          rw [hA]; omega
        rw [show n * 32 = ((List.range n).flatMap f).length from hA.symm, List.drop_left]
        rw [hnext, drop_append_length]
        rw [show (32 : Nat) = (f n).length from (hlen n).symm, List.drop_length,
          List.append_nil]

/-! ### The row's bytes -/

theorem pos8Table_drop_take (m : Nat) (hm : m < 256) :
    (pos8Table.drop (m * 32)).take 32 = pos8RowBytes m := by
  unfold pos8Table
  rw [flatMap_range_drop pos8RowBytes (fun i => pos8RowBytes_length i) 256 m hm]
  rw [show (32 : Nat) = (pos8RowBytes m).length from (pos8RowBytes_length m).symm,
    List.take_left]

theorem pos8Table_row_read (mem : Mem) (tab : Nat)
    (htab : readBytes mem tab 8192 = some pos8Table) (m : Nat) (hm : m < 256) :
    readBytes mem (tab + m * 32) 32 = some (pos8RowBytes m) := by
  obtain ⟨_, htail⟩ := readBytes_split mem tab (m * 32) (8192 - m * 32) (by
    rw [show m * 32 + (8192 - m * 32) = 8192 from by omega]; exact htab)
  obtain ⟨hrow, _⟩ := readBytes_split mem (tab + m * 32) 32 (8192 - m * 32 - 32) (by
    rw [show 32 + (8192 - m * 32 - 32) = 8192 - m * 32 from by omega]; exact htail)
  rw [hrow, pos8Table_drop_take m hm]

theorem bytesToNat_flatMap32 (lanes : List (BitVec 32)) :
    bytesToNat (lanes.flatMap (fun v => natToBytes v.toNat 4)) = packLanes lanes := by
  induction lanes with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons, bytesToNat_append,
        show (natToBytes x.toNat 4).length = 4 from natToBytes_length _ _,
        show bytesToNat (natToBytes x.toNat 4) = x.toNat from by
          rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide,
            Nat.mod_eq_of_lt x.isLt],
        ih]
      rfl

theorem unpackLanes_row (m : Nat) :
    unpackLanes 32 8 (bytesToNat (pos8RowBytes m)) = pos8Row m := by
  rw [show pos8RowBytes m = (pos8Row m).flatMap (fun v => natToBytes v.toNat 4) from rfl,
    bytesToNat_flatMap32,
    show (8 : Nat) = (pos8Row m).length from (pos8Row_length m).symm,
    unpackLanes_packLanes]

theorem natToBytes_append_pow (a b k m : Nat) (ha : a < 256 ^ k) :
    natToBytes (a + 256 ^ k * b) (k + m) = natToBytes a k ++ natToBytes b m := by
  induction k generalizing a with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      subst ha0
      simp
      rfl
  | succ k ih =>
      have hpow : (256 : Nat) ^ (k + 1) = 256 * 256 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm]
      have harg : a + 256 ^ (k + 1) * b = a + (256 ^ k * b) * 256 := by
        rw [hpow, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ k * b)]
      have hmod : (a + (256 ^ k * b) * 256) % 256 = a % 256 :=
        Nat.add_mul_mod_self_right _ _ _
      have hdiv : (a + (256 ^ k * b) * 256) / 256 = a / 256 + 256 ^ k * b :=
        Nat.add_mul_div_right _ _ (by decide : 0 < 256)
      rw [show k + 1 + m = (k + m) + 1 from by omega]
      rw [show natToBytes (a + 256 ^ (k + 1) * b) ((k + m) + 1) =
        UInt8.ofNat ((a + 256 ^ (k + 1) * b) % 256) ::
          natToBytes ((a + 256 ^ (k + 1) * b) / 256) (k + m) from rfl]
      rw [harg, hmod, hdiv]
      rw [ih (a / 256)]
      · rw [show natToBytes a (k + 1) =
          UInt8.ofNat (a % 256) :: natToBytes (a / 256) k from rfl]
        rfl
      · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
        rw [Nat.mul_comm (256 ^ k) 256, ← hpow]
        exact ha

theorem natToBytes_packLanes (lanes : List (BitVec 32)) :
    natToBytes (packLanes lanes) (4 * lanes.length) =
      lanes.flatMap (fun v => natToBytes v.toNat 4) := by
  induction lanes with
  | nil => rfl
  | cons x xs ih =>
      show natToBytes (x.toNat + 2 ^ 32 * packLanes xs) (4 * (xs.length + 1)) = _
      rw [show 2 ^ 32 = 256 ^ 4 from by decide]
      rw [show 4 * (xs.length + 1) = 4 + 4 * xs.length from by omega]
      rw [natToBytes_append_pow x.toNat (packLanes xs) 4 (4 * xs.length) (by
        rw [show (256 : Nat) ^ 4 = 2 ^ 32 from by decide]; exact x.isLt)]
      rw [ih, List.flatMap_cons]

/-- Taking `4 * n` of a concatenation of four-byte blocks takes `n` blocks. -/
theorem take_flatMap_four {α : Type} (l : List α) (f : α → List UInt8)
    (hlen : ∀ a ∈ l, (f a).length = 4) (n : Nat) :
    (l.flatMap f).take (4 * n) = (l.take n).flatMap f := by
  induction l generalizing n with
  | nil => simp
  | cons a t ih =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons]
          rw [show 4 * (n + 1) = (f a).length + 4 * n from by
            rw [hlen a (by simp)]; omega]
          rw [List.take_append]
          rw [List.take_of_length_le (by omega)]
          rw [show (f a).length + 4 * n - (f a).length = 4 * n from by omega]
          rw [ih (fun b hb => hlen b (by simp [hb]))]



theorem readBytes_append (m : Mem) :
    ∀ (n1 : Nat) (a : Nat) (b1 : List UInt8) (n2 : Nat) (b2 : List UInt8),
      readBytes m a n1 = some b1 → readBytes m (a + n1) n2 = some b2 →
      readBytes m a (n1 + n2) = some (b1 ++ b2)
  | 0, a, b1, n2, b2, h1, h2 => by
      simp only [readBytes, Option.some.injEq] at h1
      subst h1
      simpa using h2
  | n1 + 1, a, b1, n2, b2, h1, h2 => by
      simp only [readBytes] at h1
      cases hb : readByte m a with
      | none => rw [hb] at h1; cases h1
      | some b0 =>
          rw [hb] at h1
          cases h1' : readBytes m (a + 1) n1 with
          | none => rw [h1'] at h1; cases h1
          | some b1' =>
              rw [h1'] at h1
              simp only [Option.some.injEq] at h1
              subst h1
              have h2' : readBytes m (a + 1 + n1) n2 = some b2 := by
                rw [show a + 1 + n1 = a + (n1 + 1) from by omega]; exact h2
              have ih := readBytes_append m n1 (a + 1) b1' n2 b2 h1' h2'
              rw [show n1 + 1 + n2 = (n1 + n2) + 1 from by omega]
              simp only [readBytes, hb]
              rw [ih]
              rfl

theorem readBytes_writeBytes_above (m : Mem) (bs : List UInt8) :
    ∀ (n addr start : Nat), start + bs.length ≤ addr →
      readBytes (writeBytes m start bs) addr n = readBytes m addr n
  | 0, _, _, _ => rfl
  | n + 1, addr, start, h => by
      simp only [readBytes]
      rw [readByte_writeBytes_above m bs (by omega)]
      cases hr : readByte m addr with
      | none => rfl
      | some b =>
          rw [readBytes_writeBytes_above m bs n (addr + 1) start (by omega)]

theorem getD_cons_drop (bs : List UInt8) (k n : Nat) (hk : k < bs.length) :
    bs.getD k 0 :: (bs.drop (k + 1)).take n = (bs.drop k).take (n + 1) := by
  induction bs generalizing k n with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons b bs ih =>
      cases k with
      | zero => simp
      | succ k =>
          simp only [List.drop_succ_cons, List.getD_cons_succ]
          exact ih k n (by simpa using hk)

theorem readBytes_writeBytes_seg (m : Mem) (bs : List UInt8) :
    ∀ (start addr n : Nat), start ≤ addr → addr + n ≤ start + bs.length →
      readBytes (writeBytes m start bs) addr n = some ((bs.drop (addr - start)).take n)
  | start, addr, 0, _, _ => rfl
  | start, addr, n + 1, h1, h2 => by
      simp only [readBytes]
      have hread : readByte (writeBytes m start bs) addr = some (bs.getD (addr - start) 0) := by
        have h := readByte_writeBytes_at m bs start (addr - start) (by omega)
        rwa [show start + (addr - start) = addr from by omega] at h
      rw [hread]
      rw [readBytes_writeBytes_seg m bs start (addr + 1) n (by omega) (by omega)]
      simp only [Option.bind_some, Option.map_some]
      congr 1
      rw [show addr + 1 - start = (addr - start) + 1 from by omega]
      exact getD_cons_drop bs (addr - start) n (by omega)

theorem take_natToBytes_append (x n : Nat) (rest : List UInt8) :
    (natToBytes x n ++ rest).take n = natToBytes x n := by
  simpa [natToBytes_length] using (List.take_left (l₁ := natToBytes x n) (l₂ := rest))

theorem drop_natToBytes_append (x n : Nat) (rest : List UInt8) :
    (natToBytes x n ++ rest).drop n = rest := by
  simpa [natToBytes_length] using (List.drop_left (l₁ := natToBytes x n) (l₂ := rest))

theorem readLanes32_flatMap (m : Mem) (addr : Nat) (lanes : List (BitVec 32))
    (hr : readBytes m addr (4 * lanes.length) = some (lanes.flatMap (fun v => natToBytes v.toNat 4))) :
    readLanes32 m addr lanes.length = some (lanes.map (fun v => v.toNat)) := by
  induction lanes generalizing addr with
  | nil => rfl
  | cons x xs ih =>
      rw [List.flatMap_cons] at hr
      simp only [List.length_cons] at hr
      rw [show 4 * (xs.length + 1) = 4 + 4 * xs.length from by omega] at hr
      obtain ⟨h1, h2⟩ := readBytes_split m addr 4 (4 * xs.length) hr
      rw [take_natToBytes_append x.toNat 4 (xs.flatMap (fun v => natToBytes v.toNat 4))] at h1
      rw [drop_natToBytes_append x.toNat 4 (xs.flatMap (fun v => natToBytes v.toNat 4))] at h2
      show readLanes32 m addr (xs.length + 1) = some ((x :: xs).map (fun v => v.toNat))
      simp only [readLanes32]
      rw [h1]
      simp only [Option.bind_some]
      rw [ih (addr + 4) h2]
      simp only [Option.map_some, List.map_cons]
      congr 1
      rw [natToBytes_toNat, show (256 : Nat) ^ 4 = 2 ^ 32 from by decide,
        Nat.mod_eq_of_lt x.isLt]

theorem readLanes32_add (m : Mem) :
    ∀ (n1 : Nat) (addr : Nat) (l1 : List Nat) (n2 : Nat) (l2 : List Nat),
      readLanes32 m addr n1 = some l1 → readLanes32 m (addr + 4 * n1) n2 = some l2 →
      readLanes32 m addr (n1 + n2) = some (l1 ++ l2)
  | 0, addr, l1, n2, l2, h1, h2 => by
      simp only [readLanes32, Option.some.injEq] at h1
      subst h1
      simpa using h2
  | n1 + 1, addr, l1, n2, l2, h1, h2 => by
      simp only [readLanes32] at h1
      cases hb : readBytes m addr 4 with
      | none => rw [hb] at h1; cases h1
      | some bs =>
          rw [hb] at h1
          cases h1' : readLanes32 m (addr + 4) n1 with
          | none => rw [h1'] at h1; cases h1
          | some l1' =>
              simp only [h1', Option.map_some, Option.bind_some, Option.some.injEq] at h1
              subst h1
              have h2' : readLanes32 m (addr + 4 + 4 * n1) n2 = some l2 := by
                rw [show addr + 4 + 4 * n1 = addr + 4 * (n1 + 1) from by omega]; exact h2
              have ih := readLanes32_add m n1 (addr + 4) l1' n2 l2 h1' h2'
              rw [show n1 + 1 + n2 = (n1 + n2) + 1 from by omega]
              simp only [readLanes32, hb]
              rw [ih]
              rfl



theorem groupVec_length (w : BitVec 64) (base j : Nat) : (groupVec w base j).length = 8 := by
  simp [groupVec, pos8Row_length]

theorem groupPop_le (w : BitVec 64) (j : Nat) : groupPop w j ≤ 8 := by
  unfold groupPop
  exact setLanes_length_le _

theorem natToBytes_packLanes_eight (lanes : List (BitVec 32)) (h : lanes.length = 8) :
    natToBytes (packLanes lanes) 32 = lanes.flatMap (fun v => natToBytes v.toNat 4) := by
  have := natToBytes_packLanes lanes
  rw [h] at this
  simpa using this

theorem groupBytes_eq (w : BitVec 64) (base j : Nat) :
    natToBytes (packLanes (groupVec w base j)) 32 =
      (groupVec w base j).flatMap (fun v => natToBytes v.toNat 4) :=
  natToBytes_packLanes_eight _ (groupVec_length w base j)

/-- The bytes group `j` contributes to the position stream: the table row's set
lanes, offset by the group's place, each a four-byte word. -/
def groupPosBytes (w : BitVec 64) (base j : Nat) : List UInt8 :=
  ((pos8Row (byteOf w j)).take (groupPop w j)).flatMap
    (fun v => natToBytes (v + groupLane base j).toNat 4)

/-- The lanes group `j` contributes to the position stream. -/
def groupLanes (w : BitVec 64) (base j : Nat) : List (BitVec 32) :=
  ((pos8Row (byteOf w j)).take (groupPop w j)).map (fun v => v + groupLane base j)

/-- The block's positions as lanes, group order preserved. -/
def blockLanes (w : BitVec 64) (base j : Nat) : List (BitVec 32) :=
  ((List.range j).map (fun t => groupLanes w base t)).flatten

/-- The block's positions, as the values the words hold. -/
def blockPositions (w : BitVec 64) (base j : Nat) : List Nat :=
  (blockLanes w base j).map (fun v => v.toNat)

/-- The block's position bytes, group order preserved. -/
def blockPosBytes (w : BitVec 64) (base j : Nat) : List UInt8 :=
  ((List.range j).map (fun t => groupPosBytes w base t)).flatten

theorem groupVec_eq_map (w : BitVec 64) (base j : Nat) :
    groupVec w base j = (pos8Row (byteOf w j)).map (fun v => v + groupLane base j) := rfl

theorem groupPosBytes_eq (w : BitVec 64) (base j : Nat) :
    groupPosBytes w base j =
      List.flatMap (fun v : BitVec 32 => natToBytes v.toNat 4)
        ((groupVec w base j).take (groupPop w j)) := by
  unfold groupPosBytes
  rw [groupVec_eq_map]
  rw [← List.map_take (f := fun v : BitVec 32 => v + groupLane base j)
    (l := pos8Row (byteOf w j)) (i := groupPop w j)]
  exact (List.flatMap_map (fun v : BitVec 32 => v + groupLane base j)
    (fun v => natToBytes v.toNat 4) (List.take (groupPop w j) (pos8Row (byteOf w j)))).symm

theorem flatten_flatMap {α β : Type} (L : List (List α)) (f : α → List β) :
    L.flatten.flatMap f = (L.map (fun x => x.flatMap f)).flatten := by
  induction L with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatten_cons, List.flatMap_append, ih, List.map_cons, List.flatten_cons]

theorem blockPosBytes_eq (w : BitVec 64) (base j : Nat) :
    blockPosBytes w base j = (blockLanes w base j).flatMap (fun v => natToBytes v.toNat 4) := by
  unfold blockPosBytes blockLanes groupPosBytes groupLanes
  rw [flatten_flatMap, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  rw [List.flatMap_map]

theorem blockMem_group_read (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    readBytes (blockMem o w base k (j + 1) mem) (o + 4 * groupCursor w k j)
        (4 * groupPop w j) = some (groupPosBytes w base j) := by
  show readBytes (writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
      (natToBytes (packLanes (groupVec w base j)) 32))
      (o + 4 * groupCursor w k j) (4 * groupPop w j) = some (groupPosBytes w base j)
  rw [readBytes_writeBytes_seg]
  · rw [Nat.sub_self, List.drop_zero]
    rw [groupBytes_eq]
    rw [take_flatMap_four (groupVec w base j) (fun v : BitVec 32 => natToBytes v.toNat 4)
      (fun a _ => natToBytes_length a.toNat 4) (groupPop w j)]
    rw [groupPosBytes_eq]
  · omega
  · rw [natToBytes_length]
    have := groupPop_le w j
    omega



theorem groupCursor_ge (w : BitVec 64) (k j : Nat) : k ≤ groupCursor w k j := by
  unfold groupCursor; omega

theorem blockMem_read (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) :
    ∀ j, readBytes (blockMem o w base k j mem) (o + 4 * k)
        (4 * (groupCursor w k j - k)) = some (blockPosBytes w base j) := by
  intro j
  induction j with
  | zero =>
      rw [show groupCursor w k 0 - k = 0 from by unfold groupCursor; simp,
        show blockPosBytes w base 0 = [] from rfl]
      rfl
  | succ j ih =>
      have hge : k ≤ groupCursor w k j := groupCursor_ge w k j
      have hc : groupCursor w k (j + 1) = groupCursor w k j + groupPop w j :=
        groupCursor_succ w k j
      have hsplit : 4 * (groupCursor w k (j + 1) - k)
          = 4 * (groupCursor w k j - k) + 4 * groupPop w j := by
        rw [hc]; omega
      rw [hsplit]
      show readBytes (writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
          (natToBytes (packLanes (groupVec w base j)) 32))
          (o + 4 * k) (4 * (groupCursor w k j - k) + 4 * groupPop w j)
        = some (blockPosBytes w base (j + 1))
      have hbelow : readBytes (writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
          (natToBytes (packLanes (groupVec w base j)) 32)) (o + 4 * k)
          (4 * (groupCursor w k j - k)) = some (blockPosBytes w base j) := by
        rw [readBytes_writeBytes_below _ _ _ _ _ (by omega)]
        exact ih
      have hgroup : readBytes (writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
          (natToBytes (packLanes (groupVec w base j)) 32))
          (o + 4 * k + 4 * (groupCursor w k j - k)) (4 * groupPop w j)
          = some (groupPosBytes w base j) := by
        rw [show o + 4 * k + 4 * (groupCursor w k j - k) = o + 4 * groupCursor w k j from by
          omega]
        exact blockMem_group_read o w base k j mem
      rw [readBytes_append _ _ _ _ _ _ hbelow hgroup]
      show some (((List.range j).map (fun t => groupPosBytes w base t)).flatten
          ++ groupPosBytes w base j)
        = some (blockPosBytes w base (j + 1))
      rw [blockPosBytes, show j + 1 = Nat.succ j from rfl, List.range_succ, List.map_append,
        List.flatten_append]
      simp

theorem blockLanes_length (w : BitVec 64) (base j : Nat) :
    (blockLanes w base j).length = ((List.range j).map (groupPop w)).sum := by
  unfold blockLanes groupLanes
  rw [List.length_flatten, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, List.length_map, List.length_take, pos8Row_length]
  rw [Nat.min_eq_left (groupPop_le w t)]

theorem blockLanes_eight_length (w : BitVec 64) (base k : Nat) :
    (blockLanes w base 8).length = ctpop w := by
  rw [blockLanes_length]
  have h := groupCursor_eight w k
  unfold groupCursor at h
  omega

theorem blockMem_readLanes (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) :
    readLanes32 (blockMem o w base k 8 mem) (o + 4 * k) (ctpop w)
      = some (blockPositions w base 8) := by
  have hread := blockMem_read o w base k mem 8
  have hcur := groupCursor_eight w k
  have hlen : 4 * (groupCursor w k 8 - k) = 4 * ctpop w := by omega
  rw [hlen] at hread
  rw [blockPosBytes_eq] at hread
  have hflat := readLanes32_flatMap (blockMem o w base k 8 mem) (o + 4 * k)
    (blockLanes w base 8) (by rw [blockLanes_eight_length w base k]; exact hread)
  rw [blockLanes_eight_length w base k] at hflat
  exact hflat

theorem groupPop_eq_ctpop (w : BitVec 64) (j : Nat) :
    groupPop w j = ctpop (BitVec.ofNat 8 (byteOf w j)) := by
  unfold groupPop
  rw [ctpop_eq_setLanes_length]

theorem groupLane_toNat (x : BitVec 32) (base j : Nat)
    (hb : x.toNat + (base + 8 * j) < 2 ^ 32) :
    (x + groupLane base j).toNat = x.toNat + base + 8 * j := by
  rw [BitVec.toNat_add]
  rw [show (groupLane base j).toNat = base + 8 * j from by
    unfold groupLane
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem groupLanes_map_toNat (w : BitVec 64) (base j : Nat) (hbase : base + 64 < 2 ^ 32)
    (hj : j < 8) :
    (groupLanes w base j).map (fun v => v.toNat)
      = ((pos8Row (byteOf w j)).take (groupPop w j)).map
          (fun v => base + 8 * j + v.toNat) := by
  unfold groupLanes
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  have hv' : v ∈ (pos8Row (byteOf w j)).take (ctpop (BitVec.ofNat 8 (byteOf w j))) := by
    simpa [groupPop_eq_ctpop] using hv
  rw [pos8Row_take] at hv'
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hv'
  have hk8 : k < 8 := (mem_setLanes.mp hk).1
  simp only [Function.comp_apply]
  have hk64 : k + 8 * j < 64 := by omega
  have hbnd : (BitVec.ofNat 32 k).toNat + (base + 8 * j) < 2 ^ 32 := by
    rw [show (BitVec.ofNat 32 k).toNat = k from by rw [BitVec.toNat_ofNat]; omega]
    omega
  rw [groupLane_toNat _ base j hbnd]
  rw [show (BitVec.ofNat 32 k).toNat = k from by rw [BitVec.toNat_ofNat]; omega]
  omega

theorem blockPositions_eight (w : BitVec 64) (base : Nat) (hbase : base + 64 < 2 ^ 32) :
    blockPositions w base 8 = positionsOf w base := by
  unfold blockPositions blockLanes
  rw [List.map_flatten]
  rw [show (List.map (List.map (fun v => v.toNat))
      (List.map (fun t => groupLanes w base t) (List.range 8)))
      = List.map ((List.map (fun v => v.toNat)) ∘ (fun t => groupLanes w base t)) (List.range 8)
      from List.map_map]
  rw [positionsOf_eq_bytes]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j hj
  have hj8 : j < 8 := List.mem_range.mp hj
  simp only [Function.comp_apply]
  rw [groupLanes_map_toNat w base j hbase hj8, groupPop_eq_ctpop]



/-! ### The block's units: the head, the seven groups, and the tail

The block is simulated one unit at a time.  Each unit's step lemmas are the
intrinsic-free shape above; the group units are one group sequence each, so
no goal ever holds more than one unit's instructions. -/

theorem and255_eq (x : Nat) : x &&& 255 = x % 256 := by
  have := Nat.and_two_pow_sub_one_eq_mod x 8
  simpa using this

/-- A filter of a range stops where its predicate is false. -/
theorem filter_range_eq_of (p q : Nat → Bool) {n m : Nat} (hn : n ≤ m)
    (hagree : ∀ i, i < n → p i = q i)
    (hzero : ∀ i, n ≤ i → i < m → p i = false) :
    (List.range m).filter p = (List.range n).filter q := by
  have key : ∀ d, n + d ≤ m → (List.range (n + d)).filter p = (List.range n).filter p := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        rw [Nat.add_succ, List.range_succ, List.filter_append, ih (by omega)]
        simp [hzero (n + d) (by omega) (by omega)]
  rw [← Nat.add_sub_cancel' hn]
  rw [key (m - n) (by omega)]
  exact List.filter_congr (fun i hi => hagree i (List.mem_range.mp hi))

theorem setLanes_ofNat32_ofNat8 (b : Nat) (hb : b < 256) :
    setLanes (BitVec.ofNat 32 b) = setLanes (BitVec.ofNat 8 b) := by
  unfold setLanes
  apply filter_range_eq_of _ _ (show 8 ≤ 32 from by decide)
  · intro i hi
    rw [BitVec.getLsbD_ofNat, BitVec.getLsbD_ofNat,
      show decide (i < 32) = true from decide_eq_true (by omega),
      show decide (i < 8) = true from decide_eq_true hi]
  · intro i hi hi2
    have hb8 : b < 2 ^ 8 := by
      rw [show ((2 : Nat) ^ 8) = 256 from by decide]; exact hb
    have hpow : (2 : Nat) ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_of_le (by decide) hi
    rw [BitVec.getLsbD_ofNat, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb8 hpow)]
    simp [show decide (i < 32) = true from decide_eq_true hi2]

theorem ctpop_eq_groupPop32 (w : BitVec 64) (j : Nat) :
    ctpop (BitVec.ofNat 32 (byteOf w j)) = groupPop w j := by
  rw [ctpop_eq_setLanes_length, groupPop_eq_ctpop, ctpop_eq_setLanes_length,
    setLanes_ofNat32_ofNat8 _ (byteOf_lt w j)]

/-- The trunc-and-mask of a shifted word is that byte, at 32 bits. -/
theorem and255_trunc (w : BitVec 64) (j : Nat) :
    ((BitVec.ofNat 32 ((w >>> (8 * j)).toNat % 2 ^ 32)) &&& BitVec.ofInt 32 255)
      = BitVec.ofNat 32 (byteOf w j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h255 : (BitVec.ofInt 32 255).toNat = 255 := by decide
  rw [h255, and255_eq]
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_mod]
  unfold byteOf
  rw [Nat.mod_eq_of_lt (by omega : w.toNat / 2 ^ (8 * j) % 256 < 2 ^ 32)]
  exact Nat.mod_mod_of_dvd _ (show (256 : Nat) ∣ 2 ^ 32 from ⟨2 ^ 24, by decide⟩)

/-- The mask's byte index, at 64 bits. -/
theorem and255_shift64 (w : BitVec 64) (j : Nat) :
    ((w >>> (8 * j)) &&& BitVec.ofInt 64 255) = BitVec.ofNat 64 (byteOf w j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat]
  have h255 : (BitVec.ofInt 64 255).toNat = 255 := by decide
  rw [h255, and255_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold byteOf
  rw [Nat.mod_eq_of_lt (by omega : w.toNat / 2 ^ (8 * j) % 256 < 2 ^ 64)]

theorem or_ofNat_shift (base : Nat) (j : Nat) (hb : base % 64 = 0) (hj : j < 8)
    (hcap : base + 64 ≤ 2 ^ 32) :
    (BitVec.ofNat 32 base ||| BitVec.ofNat 32 (8 * j)) = BitVec.ofNat 32 (base + 8 * j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hb64 : base = (base / 64) <<< 6 := by
    rw [Nat.shiftLeft_eq, show ((2 : Nat) ^ 6) = 64 from by decide]
    exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hb)).symm
  have h8 : 8 * j < 2 ^ 6 := by omega
  have h1 : base ||| 8 * j = base + 8 * j := by
    have h := (Nat.shiftLeft_add_eq_or_of_lt (i := 6) h8 (base / 64)).symm
    rw [← hb64] at h
    exact h
  rw [h1]

/-- The block base, as `%conv` computes it. -/
theorem pos8_conv (i blk0 : Nat) (h : 64 * (blk0 + i) + 64 ≤ 2 ^ 32) :
    BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
      = BitVec.ofNat 32 (64 * (blk0 + i)) := by
  have hsum : (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat = i + blk0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : blk0 < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hsum]
  rw [show BitVec.ofNat 32 ((i + blk0) % 2 ^ 32) = BitVec.ofNat 32 (i + blk0) from by
    rw [Nat.mod_eq_of_lt (by omega)]]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### The block's arithmetic -/

theorem toNat_ofNat64 (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toNat_ofNat32 (n : Nat) (h : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem gc_zero (w : BitVec 64) (k : Nat) : groupCursor w k 0 = k := by simp [groupCursor]

theorem gc_one (w : BitVec 64) (k : Nat) : groupCursor w k 1 = k + groupPop w 0 := by
  have h := groupCursor_succ w k 0
  rw [gc_zero] at h
  exact h

theorem gc_succ' (w : BitVec 64) (k j : Nat) :
    groupCursor w k (j + 1) = groupCursor w k j + groupPop w j := groupCursor_succ w k j

theorem ctpop_le {w : Nat} (x : BitVec w) : ctpop x ≤ w := by
  rw [ctpop_eq_setLanes_length]
  exact setLanes_length_le x

def posBase (blk0 i : Nat) : Nat := 64 * (blk0 + i)

theorem posBase_eq (blk0 i : Nat) : posBase blk0 i = 64 * (blk0 + i) := rfl

theorem posBase_mod (blk0 i : Nat) : posBase blk0 i % 64 = 0 := by
  unfold posBase
  exact Nat.mul_mod_right 64 (blk0 + i)

theorem groupVec_at (w : BitVec 64) (base j : Nat) :
    groupVec w base j = (pos8Row (byteOf w j)).map (fun v => v + BitVec.ofNat 32 (base + 8 * j)) := by
  rw [groupVec_eq_map]
  rfl

theorem blockMem_succ (o : Nat) (w : BitVec 64) (base k j : Nat) (mem : Mem) :
    blockMem o w base k (j + 1) mem =
      writeBytes (blockMem o w base k j mem) (o + 4 * groupCursor w k j)
        (natToBytes (packLanes (groupVec w base j)) 32) := rfl

theorem shr56_toNat (w : BitVec 64) : (w >>> 56).toNat = byteOf w 7 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  unfold byteOf
  rw [Nat.mod_eq_of_lt (by omega : w.toNat / 2 ^ (8 * 7) < 256)]

macro "ent_auto" : tactic =>
  `(tactic| ((repeat rw [lookupName_cons_ne _ _ (by decide)]); (try exact lookupName_cons_self _ _ _); (try assumption)))

macro "ent_step " l:term : tactic =>
  `(tactic| rw [denoteCode_cons_of _ _ _ _ _ $l])


theorem groupLane_zero (base : Nat) : groupLane base 0 = BitVec.ofNat 32 base := by
  unfold groupLane
  rw [Nat.mul_zero, Nat.add_zero]

theorem groupVec_zero (w : BitVec 64) (base : Nat) :
    groupVec w base 0 = (pos8Row (byteOf w 0)).map (fun v => v + BitVec.ofNat 32 base) := by
  rw [groupVec_eq_map, groupLane_zero]

/-- A state's memory is the value the update writes.  Stated with the memory a
variable: at a `blockMem` term the `rfl` would reduce the whole fold. -/
theorem state_mem_update (s : State) (m : Mem) : ({ s with mem := m } : State).mem = m := rfl

theorem blockMem_one (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) :
    blockMem o w base k 1 mem =
      writeBytes mem (o + 4 * k) (natToBytes (packLanes (groupVec w base 0)) 32) := by
  show writeBytes (blockMem o w base k 0 mem) (o + 4 * groupCursor w k 0)
      (natToBytes (packLanes (groupVec w base 0)) 32) = _
  rw [gc_zero]
  rfl

theorem pos8Head_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Head (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * groupCursor w k 1)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr⟩
  case hrun =>
    simp only [pos8Head, reg, lit, zero8, splatLane0]
    ent_step (step_add_reg _ _ "%add" "%i.010" "%blk0" 64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 blk0) (by ent_auto) (by ent_auto))
    ent_step (step_trunc _ _ "%add.tr" "%add" 64 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0) (by ent_auto))
    ent_step (step_shl_imm _ _ "%conv" "%add.tr" 32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32)) (BitVec.ofInt 32 6) (by ent_auto))
    rw [show (BitVec.ofInt 32 6).toNat = 6 from by decide, hconv]
    ent_step (step_gep64 _ _ "%add.ptr" "%out" "%k.addr.011" (.int 32) o (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 k (by omega)]; omega))
    rw [show o + (BitVec.ofNat 64 k).toNat * (Ty.int 32).sizeBytes = o + 4 * k from by
      rw [toNat_ofNat64 k (by omega), show (Ty.int 32).sizeBytes = 4 from rfl]; omega]
    ent_step (step_trunc _ _ "%1" "%0" 64 32 w (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.i" "%1" 32 (BitVec.ofNat 32 (w.toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [show (BitVec.ofNat 32 (w.toNat % 2 ^ 32) &&& BitVec.ofInt 32 255) = BitVec.ofNat 32 (byteOf w 0) from by simpa using and255_trunc w 0]
    ent_step (step_and_imm _ _ "%idxprom.i" "%0" 64 w (BitVec.ofInt 64 255) (by ent_auto))
    rw [show (w &&& BitVec.ofInt 64 255) = BitVec.ofNat 64 (byteOf w 0) from by simpa using and255_shift64 w 0]
    ent_step (step_gep64 _ _ "%arrayidx.i" "%tab" "%idxprom.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 0)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 0; rw [toNat_ofNat64 (byteOf w 0) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 0)).toNat * v8i32.sizeBytes = tab + byteOf w 0 * 32 from by rw [toNat_ofNat64 (byteOf w 0) (by have := byteOf_lt w 0; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%2" "%arrayidx.i" (tab + byteOf w 0 * 32) (pos8Row (byteOf w 0)) (pos8RowBytes (byteOf w 0)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 0)) (by exact unpackLanes_row _))
    ent_step (step_insertelement _ _ "%vecinit.i.i" "%conv" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.i" "%vecinit.i.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.i" "%2" "%vecinit7.i.i" (pos8Row (byteOf w 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [← groupVec_zero w (posBase blk0 i)]
    ent_step (step_store_vec _ _ "%add.i.i" "%add.ptr" (o + 4 * k) (groupVec w (posBase blk0 i) 0) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%3" "%conv.i" (BitVec.ofNat 32 (byteOf w 0)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.i" "%3" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 0)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 0)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 0)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 0)); omega)]]
    rw [ctpop_eq_groupPop32 w 0]
    ent_step (step_gep64 _ _ "%add.ptr.i" "%add.ptr" "%conv4.i" (.int 32) (o + 4 * k) (BitVec.ofNat 64 (groupPop w 0)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 0; rw [toNat_ofNat64 (groupPop w 0) (by omega)]; omega))
    rw [show o + 4 * k + (BitVec.ofNat 64 (groupPop w 0)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 1 from by
      rw [toNat_ofNat64 (groupPop w 0) (by have := groupPop_le w 0; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_one w k]
      omega]
    simp only [denoteCode, Option.bind]
    rw [blockMem_one]
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr => ent_auto


/-- Groups `1` … `6`: shift the mask word down to byte `j`, select that byte's
table row, broadcast it offset by the group's place in the block, store it at
the running cursor, and advance the cursor by the byte's population count. -/

theorem pos8Group1_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 1 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.i" = some (.ptr (o + 4 * groupCursor w k 1)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group1 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 2 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.1.i" = some (.ptr (o + 4 * groupCursor w k 2)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group1, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.1.i" "%0" 64 w (BitVec.ofInt 64 8) (by ent_auto))
    rw [show (BitVec.ofInt 64 8).toNat = 8 * 1 from by decide]
    ent_step (step_trunc _ _ "%4" "%shr.1.i" 64 32 (w >>> (8 * 1)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.1.i" "%4" 32 (BitVec.ofNat 32 ((w >>> (8 * 1)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 1]
    ent_step (step_and_imm _ _ "%idxprom.1.i" "%shr.1.i" 64 (w >>> (8 * 1)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 1]
    ent_step (step_gep64 _ _ "%arrayidx.1.i" "%tab" "%idxprom.1.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 1)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 1; rw [toNat_ofNat64 (byteOf w 1) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 1)).toNat * v8i32.sizeBytes = tab + byteOf w 1 * 32 from by
      rw [toNat_ofNat64 (byteOf w 1) (by have := byteOf_lt w 1; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%5" "%arrayidx.1.i" (tab + byteOf w 1 * 32) (pos8Row (byteOf w 1)) (pos8RowBytes (byteOf w 1)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 1)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.1.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 8) (by ent_auto))
    rw [show BitVec.ofInt 32 8 = BitVec.ofNat 32 (8 * 1) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 1 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.1.i" "%add.1.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.1.i" "%vecinit.i.1.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.1.i" "%5" "%vecinit7.i.1.i" (pos8Row (byteOf w 1)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 1)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) = groupVec w (posBase blk0 i) 1 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.1.i" "%add.ptr.i" (o + 4 * groupCursor w k 1) (groupVec w (posBase blk0 i) 1) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%6" "%conv.1.i" (BitVec.ofNat 32 (byteOf w 1)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.1.i" "%6" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 1)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 1)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 1)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 1)); omega)]]
    rw [ctpop_eq_groupPop32 w 1]
    ent_step (step_gep64 _ _ "%add.ptr.1.i" "%add.ptr.i" "%conv4.1.i" (.int 32) (o + 4 * groupCursor w k 1) (BitVec.ofNat 64 (groupPop w 1)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 1; rw [toNat_ofNat64 (groupPop w 1) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 1 + (BitVec.ofNat 64 (groupPop w 1)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 2 from by
      rw [toNat_ofNat64 (groupPop w 1) (by have := groupPop_le w 1; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 1]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem pos8Group2_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 2 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.1.i" = some (.ptr (o + 4 * groupCursor w k 2)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group2 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 3 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.2.i" = some (.ptr (o + 4 * groupCursor w k 3)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group2, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.2.i" "%0" 64 w (BitVec.ofInt 64 16) (by ent_auto))
    rw [show (BitVec.ofInt 64 16).toNat = 8 * 2 from by decide]
    ent_step (step_trunc _ _ "%7" "%shr.2.i" 64 32 (w >>> (8 * 2)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.2.i" "%7" 32 (BitVec.ofNat 32 ((w >>> (8 * 2)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 2]
    ent_step (step_and_imm _ _ "%idxprom.2.i" "%shr.2.i" 64 (w >>> (8 * 2)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 2]
    ent_step (step_gep64 _ _ "%arrayidx.2.i" "%tab" "%idxprom.2.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 2)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 2; rw [toNat_ofNat64 (byteOf w 2) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 2)).toNat * v8i32.sizeBytes = tab + byteOf w 2 * 32 from by
      rw [toNat_ofNat64 (byteOf w 2) (by have := byteOf_lt w 2; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%8" "%arrayidx.2.i" (tab + byteOf w 2 * 32) (pos8Row (byteOf w 2)) (pos8RowBytes (byteOf w 2)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 2)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.2.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 16) (by ent_auto))
    rw [show BitVec.ofInt 32 16 = BitVec.ofNat 32 (8 * 2) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 2 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.2.i" "%add.2.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.2.i" "%vecinit.i.2.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.2.i" "%8" "%vecinit7.i.2.i" (pos8Row (byteOf w 2)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 2)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) = groupVec w (posBase blk0 i) 2 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.2.i" "%add.ptr.1.i" (o + 4 * groupCursor w k 2) (groupVec w (posBase blk0 i) 2) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%9" "%conv.2.i" (BitVec.ofNat 32 (byteOf w 2)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.2.i" "%9" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 2)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 2)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 2)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 2)); omega)]]
    rw [ctpop_eq_groupPop32 w 2]
    ent_step (step_gep64 _ _ "%add.ptr.2.i" "%add.ptr.1.i" "%conv4.2.i" (.int 32) (o + 4 * groupCursor w k 2) (BitVec.ofNat 64 (groupPop w 2)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 2; rw [toNat_ofNat64 (groupPop w 2) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 2 + (BitVec.ofNat 64 (groupPop w 2)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 3 from by
      rw [toNat_ofNat64 (groupPop w 2) (by have := groupPop_le w 2; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 2]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem pos8Group3_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 3 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.2.i" = some (.ptr (o + 4 * groupCursor w k 3)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group3 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 4 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.3.i" = some (.ptr (o + 4 * groupCursor w k 4)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group3, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.3.i" "%0" 64 w (BitVec.ofInt 64 24) (by ent_auto))
    rw [show (BitVec.ofInt 64 24).toNat = 8 * 3 from by decide]
    ent_step (step_trunc _ _ "%10" "%shr.3.i" 64 32 (w >>> (8 * 3)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.3.i" "%10" 32 (BitVec.ofNat 32 ((w >>> (8 * 3)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 3]
    ent_step (step_and_imm _ _ "%idxprom.3.i" "%shr.3.i" 64 (w >>> (8 * 3)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 3]
    ent_step (step_gep64 _ _ "%arrayidx.3.i" "%tab" "%idxprom.3.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 3)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 3; rw [toNat_ofNat64 (byteOf w 3) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 3)).toNat * v8i32.sizeBytes = tab + byteOf w 3 * 32 from by
      rw [toNat_ofNat64 (byteOf w 3) (by have := byteOf_lt w 3; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%11" "%arrayidx.3.i" (tab + byteOf w 3 * 32) (pos8Row (byteOf w 3)) (pos8RowBytes (byteOf w 3)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 3)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.3.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 24) (by ent_auto))
    rw [show BitVec.ofInt 32 24 = BitVec.ofNat 32 (8 * 3) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 3 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.3.i" "%add.3.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.3.i" "%vecinit.i.3.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.3.i" "%11" "%vecinit7.i.3.i" (pos8Row (byteOf w 3)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 3)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) = groupVec w (posBase blk0 i) 3 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.3.i" "%add.ptr.2.i" (o + 4 * groupCursor w k 3) (groupVec w (posBase blk0 i) 3) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%12" "%conv.3.i" (BitVec.ofNat 32 (byteOf w 3)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.3.i" "%12" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 3)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 3)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 3)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 3)); omega)]]
    rw [ctpop_eq_groupPop32 w 3]
    ent_step (step_gep64 _ _ "%add.ptr.3.i" "%add.ptr.2.i" "%conv4.3.i" (.int 32) (o + 4 * groupCursor w k 3) (BitVec.ofNat 64 (groupPop w 3)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 3; rw [toNat_ofNat64 (groupPop w 3) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 3 + (BitVec.ofNat 64 (groupPop w 3)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 4 from by
      rw [toNat_ofNat64 (groupPop w 3) (by have := groupPop_le w 3; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 3]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem pos8Group4_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 4 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.3.i" = some (.ptr (o + 4 * groupCursor w k 4)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group4 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 5 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.4.i" = some (.ptr (o + 4 * groupCursor w k 5)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group4, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.4.i" "%0" 64 w (BitVec.ofInt 64 32) (by ent_auto))
    rw [show (BitVec.ofInt 64 32).toNat = 8 * 4 from by decide]
    ent_step (step_trunc _ _ "%13" "%shr.4.i" 64 32 (w >>> (8 * 4)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.4.i" "%13" 32 (BitVec.ofNat 32 ((w >>> (8 * 4)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 4]
    ent_step (step_and_imm _ _ "%idxprom.4.i" "%shr.4.i" 64 (w >>> (8 * 4)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 4]
    ent_step (step_gep64 _ _ "%arrayidx.4.i" "%tab" "%idxprom.4.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 4)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 4; rw [toNat_ofNat64 (byteOf w 4) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 4)).toNat * v8i32.sizeBytes = tab + byteOf w 4 * 32 from by
      rw [toNat_ofNat64 (byteOf w 4) (by have := byteOf_lt w 4; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%14" "%arrayidx.4.i" (tab + byteOf w 4 * 32) (pos8Row (byteOf w 4)) (pos8RowBytes (byteOf w 4)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 4)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.4.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 32) (by ent_auto))
    rw [show BitVec.ofInt 32 32 = BitVec.ofNat 32 (8 * 4) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 4 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.4.i" "%add.4.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.4.i" "%vecinit.i.4.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.4.i" "%14" "%vecinit7.i.4.i" (pos8Row (byteOf w 4)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 4)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) = groupVec w (posBase blk0 i) 4 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.4.i" "%add.ptr.3.i" (o + 4 * groupCursor w k 4) (groupVec w (posBase blk0 i) 4) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%15" "%conv.4.i" (BitVec.ofNat 32 (byteOf w 4)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.4.i" "%15" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 4)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 4)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 4)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 4)); omega)]]
    rw [ctpop_eq_groupPop32 w 4]
    ent_step (step_gep64 _ _ "%add.ptr.4.i" "%add.ptr.3.i" "%conv4.4.i" (.int 32) (o + 4 * groupCursor w k 4) (BitVec.ofNat 64 (groupPop w 4)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 4; rw [toNat_ofNat64 (groupPop w 4) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 4 + (BitVec.ofNat 64 (groupPop w 4)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 5 from by
      rw [toNat_ofNat64 (groupPop w 4) (by have := groupPop_le w 4; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 4]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem pos8Group5_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 5 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.4.i" = some (.ptr (o + 4 * groupCursor w k 5)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group5 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 6 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.5.i" = some (.ptr (o + 4 * groupCursor w k 6)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group5, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.5.i" "%0" 64 w (BitVec.ofInt 64 40) (by ent_auto))
    rw [show (BitVec.ofInt 64 40).toNat = 8 * 5 from by decide]
    ent_step (step_trunc _ _ "%16" "%shr.5.i" 64 32 (w >>> (8 * 5)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.5.i" "%16" 32 (BitVec.ofNat 32 ((w >>> (8 * 5)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 5]
    ent_step (step_and_imm _ _ "%idxprom.5.i" "%shr.5.i" 64 (w >>> (8 * 5)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 5]
    ent_step (step_gep64 _ _ "%arrayidx.5.i" "%tab" "%idxprom.5.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 5)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 5; rw [toNat_ofNat64 (byteOf w 5) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 5)).toNat * v8i32.sizeBytes = tab + byteOf w 5 * 32 from by
      rw [toNat_ofNat64 (byteOf w 5) (by have := byteOf_lt w 5; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%17" "%arrayidx.5.i" (tab + byteOf w 5 * 32) (pos8Row (byteOf w 5)) (pos8RowBytes (byteOf w 5)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 5)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.5.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 40) (by ent_auto))
    rw [show BitVec.ofInt 32 40 = BitVec.ofNat 32 (8 * 5) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 5 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.5.i" "%add.5.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.5.i" "%vecinit.i.5.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.5.i" "%17" "%vecinit7.i.5.i" (pos8Row (byteOf w 5)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 5)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) = groupVec w (posBase blk0 i) 5 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.5.i" "%add.ptr.4.i" (o + 4 * groupCursor w k 5) (groupVec w (posBase blk0 i) 5) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%18" "%conv.5.i" (BitVec.ofNat 32 (byteOf w 5)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.5.i" "%18" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 5)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 5)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 5)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 5)); omega)]]
    rw [ctpop_eq_groupPop32 w 5]
    ent_step (step_gep64 _ _ "%add.ptr.5.i" "%add.ptr.4.i" "%conv4.5.i" (.int 32) (o + 4 * groupCursor w k 5) (BitVec.ofNat 64 (groupPop w 5)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 5; rw [toNat_ofNat64 (groupPop w 5) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 5 + (BitVec.ofNat 64 (groupPop w 5)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 6 from by
      rw [toNat_ofNat64 (groupPop w 5) (by have := groupPop_le w 5; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 5]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem pos8Group6_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 6 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.5.i" = some (.ptr (o + 4 * groupCursor w k 6)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group6 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 7 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.6.i" = some (.ptr (o + 4 * groupCursor w k 7)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group6, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.6.i" "%0" 64 w (BitVec.ofInt 64 48) (by ent_auto))
    rw [show (BitVec.ofInt 64 48).toNat = 8 * 6 from by decide]
    ent_step (step_trunc _ _ "%19" "%shr.6.i" 64 32 (w >>> (8 * 6)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.6.i" "%19" 32 (BitVec.ofNat 32 ((w >>> (8 * 6)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 6]
    ent_step (step_and_imm _ _ "%idxprom.6.i" "%shr.6.i" 64 (w >>> (8 * 6)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 6]
    ent_step (step_gep64 _ _ "%arrayidx.6.i" "%tab" "%idxprom.6.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 6)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 6; rw [toNat_ofNat64 (byteOf w 6) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 6)).toNat * v8i32.sizeBytes = tab + byteOf w 6 * 32 from by
      rw [toNat_ofNat64 (byteOf w 6) (by have := byteOf_lt w 6; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%20" "%arrayidx.6.i" (tab + byteOf w 6 * 32) (pos8Row (byteOf w 6)) (pos8RowBytes (byteOf w 6)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read s.mem tab htabread _ (byteOf_lt w 6)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.6.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 48) (by ent_auto))
    rw [show BitVec.ofInt 32 48 = BitVec.ofNat 32 (8 * 6) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 6 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.6.i" "%add.6.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.6.i" "%vecinit.i.6.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.6.i" "%20" "%vecinit7.i.6.i" (pos8Row (byteOf w 6)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 6)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) = groupVec w (posBase blk0 i) 6 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.6.i" "%add.ptr.5.i" (o + 4 * groupCursor w k 6) (groupVec w (posBase blk0 i) 6) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%21" "%conv.6.i" (BitVec.ofNat 32 (byteOf w 6)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.6.i" "%21" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 6)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 6)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 6)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 6)); omega)]]
    rw [ctpop_eq_groupPop32 w 6]
    ent_step (step_gep64 _ _ "%add.ptr.6.i" "%add.ptr.5.i" "%conv4.6.i" (.int 32) (o + 4 * groupCursor w k 6) (BitVec.ofNat 64 (groupPop w 6)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 6; rw [toNat_ofNat64 (groupPop w 6) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 6 + (BitVec.ofNat 64 (groupPop w 6)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 7 from by
      rw [toNat_ofNat64 (groupPop w 6) (by have := groupPop_le w 6; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 6]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto

theorem sum_map_groupPop_le (w : BitVec 64) (j : Nat) (hj : j ≤ 8) :
    ((List.range j).map (groupPop w)).sum ≤ 8 * j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.append_nil]
      have h1 := groupPop_le w j
      have h2 := ih (by omega)
      omega

theorem groupCursor_le (w : BitVec 64) (k j : Nat) (hj : j ≤ 8) :
    groupCursor w k j ≤ k + 8 * j := by
  unfold groupCursor
  have := sum_map_groupPop_le w j hj
  omega

/-- A read outside a write's span is unaffected by it. -/
theorem readBytes_writeBytes_frame (m : Mem) (bs : List UInt8) (start p n : Nat)
    (h : p + n ≤ start ∨ start + bs.length ≤ p) :
    readBytes (writeBytes m start bs) p n = readBytes m p n := by
  rcases h with h | h
  · exact readBytes_writeBytes_below m bs n p start h
  · exact readBytes_writeBytes_above m bs n p start h

theorem pos8Group7_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 7 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.6.i" = some (.ptr (o + 4 * groupCursor w k 7)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (htabread : readBytes s.mem tab 8192 = some pos8Table) :
    ∃ env', denoteCode entryCalls pos8Group7 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 8 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk'⟩
  case hrun =>
    simp only [pos8Group7, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.7.i" "%0" 64 w (BitVec.ofInt 64 56) (by ent_auto))
    rw [show (BitVec.ofInt 64 56).toNat = 8 * 7 from by decide]
    ent_step (step_gep64 _ _ "%arrayidx.7.i" "%tab" "%shr.7.i" v8i32 tab (w >>> 56) (by ent_auto) (by ent_auto) (by rw [shr56_toNat w]; have := byteOf_lt w 7; omega))
    rw [show tab + (w >>> 56).toNat * v8i32.sizeBytes = tab + byteOf w 7 * 32 from by
      rw [shr56_toNat w, show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%22" "%arrayidx.7.i" (tab + byteOf w 7 * 32) (pos8Row (byteOf w 7)) (pos8RowBytes (byteOf w 7)) (by ent_auto) (by exact pos8RowBytes_length _) (by exact pos8Table_row_read _ tab htabread _ (byteOf_lt w 7)) (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.7.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 56) (by ent_auto))
    rw [show BitVec.ofInt 32 56 = BitVec.ofNat 32 (8 * 7) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 7 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.7.i" "%add.7.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.7.i" "%vecinit.i.7.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.7.i" "%22" "%vecinit7.i.7.i" (pos8Row (byteOf w 7)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 7)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) = groupVec w (posBase blk0 i) 7 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.7.i" "%add.ptr.6.i" (o + 4 * groupCursor w k 7) (groupVec w (posBase blk0 i) 7) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto

/-- The block's last two instructions: the word's population count and the
advanced cursor. -/
theorem pos8Tail_run (env : Env) (s : State) (w : BitVec 64) (k : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls pos8Tail (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%add1"
        = some (.int 64 (BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k)) := by
  refine ⟨?env', ?hrun, ?hadd1⟩
  case hrun =>
    simp only [pos8Tail, reg, lit, zero8, splatLane0]
    ent_step (step_call_ctpop64 _ _ "%23" "%0" w (by ent_auto))
    ent_step (step_add_reg _ _ "%add1" "%23" "%k.addr.011" 64 (BitVec.ofNat 64 (ctpop w)) (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto))
    simp only [denoteCode, Option.bind]
    simp only [withEnv]
    rfl
  case hadd1 => ent_auto


/-! ### The block, composed from its units -/

theorem pos8GroupsInstrs_split :
    pos8GroupsInstrs =
      pos8Head ++ (pos8Group1 ++ (pos8Group2 ++ (pos8Group3 ++ (pos8Group4 ++
        (pos8Group5 ++ (pos8Group6 ++ (pos8Group7 ++ pos8Tail))))))) := by
  simp only [pos8GroupsInstrs, List.append_assoc]

/-- The table stays readable through every group store, at the frame end the
stores actually have: a block's writes reach `o + 4 * (k + ctpop w + 8)` and no
further, so a table outside that span is untouched by any of the eight rows. -/
theorem groupCursor_le_eight (w : BitVec 64) (k j : Nat) (hj : j ≤ 8) :
    groupCursor w k j ≤ groupCursor w k 8 := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
  rw [hd]
  clear hj hd
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
      have h1 : groupCursor w k (j + d) ≤ groupCursor w k (j + d + 1) := by
        rw [groupCursor_succ]
        omega
      exact Nat.le_trans ih h1

theorem blockMem_frame_tight (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem)
    (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (k + ctpop w + 8) ≤ p) :
    ∀ j, j ≤ 8 → readBytes (blockMem o w base k j mem) p n = readBytes mem p n
  | 0, _ => rfl
  | j + 1, hj => by
      rw [blockMem_succ, readBytes_writeBytes_frame]
      · exact blockMem_frame_tight o w base k mem p n hdisj j (by omega)
      · rcases hdisj with h | h
        · left
          have := groupCursor_ge w k j
          omega
        · right
          have hmono : groupCursor w k j ≤ groupCursor w k 8 := groupCursor_le_eight w k j (by omega)
          rw [groupCursor_eight] at hmono
          rw [natToBytes_length]
          omega

theorem blockMem_read_table (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem)
    (tab : Nat) (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab)
    (htabread : readBytes mem tab 8192 = some pos8Table) :
    ∀ j, j ≤ 8 → readBytes (blockMem o w base k j mem) tab 8192 = some pos8Table
  | j, hj => by
      rw [blockMem_frame_tight o w base k mem tab 8192 (by
        rcases hdisj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h) j hj]
      exact htabread

theorem pos8Groups_run (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (htabread : readBytes s.mem tab 8192 = some pos8Table)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    ∃ env', denoteCode entryCalls pos8GroupsInstrs (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 8 s.mem }) ∧
      lookupName env' "%add1"
        = some (.int 64 (BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k)) := by
  obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
    pos8Head_run env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv htabread
  obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
    pos8Group1_run e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 1 (by omega))
  obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
    pos8Group2_run e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 2 (by omega))
  obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
    pos8Group3_run e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 3 (by omega))
  obtain ⟨e5, h5, h5a, h5b, h5c, h5d, h5e⟩ :=
    pos8Group4_run e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h4a h4b h4e h4c h4d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 4 (by omega))
  obtain ⟨e6, h6, h6a, h6b, h6c, h6d, h6e⟩ :=
    pos8Group5_run e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h5a h5b h5e h5c h5d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 5 (by omega))
  obtain ⟨e7, h7, h7a, h7b, h7c, h7d, h7e⟩ :=
    pos8Group6_run e6 { s with mem := blockMem o w (posBase blk0 i) k 6 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h6a h6b h6e h6c h6d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 6 (by omega))
  obtain ⟨e8, h8, h8a, h8b, h8c, h8d⟩ :=
    pos8Group7_run e7 { s with mem := blockMem o w (posBase blk0 i) k 7 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h7a h7b h7e h7c h7d hblk
      (by rw [state_mem_update]; exact blockMem_read_table o w (posBase blk0 i) k s.mem tab hdisj htabread 7 (by omega))
  obtain ⟨e9, h9, h9a⟩ :=
    pos8Tail_run e8 { s with mem := blockMem o w (posBase blk0 i) k 8 s.mem } w k h8a h8d
  rw [pos8GroupsInstrs_split]
  refine ⟨e9, ?_, h9a⟩
  rw [denoteCode_append, h1]
  simp only [Option.bind_some]
  rw [denoteCode_append, h2]
  simp only [Option.bind_some]
  rw [denoteCode_append, h3]
  simp only [Option.bind_some]
  rw [denoteCode_append, h4]
  simp only [Option.bind_some]
  rw [denoteCode_append, h5]
  simp only [Option.bind_some]
  rw [denoteCode_append, h6]
  simp only [Option.bind_some]
  rw [denoteCode_append, h7]
  simp only [Option.bind_some]
  rw [denoteCode_append, h8]
  simp only [Option.bind_some]
  exact h9

theorem storeValue_env (s s' : State) (ty : Ty) (v : Value) (addr : Nat)
    (h : storeValue s ty v addr = some s') : s'.env = s.env := by
  match ty, v with
  | .int w, .int w' x =>
      simp only [storeValue] at h
      split at h
      · cases h; rfl
      · cases h
  | .int _, .ptr _ => simp [storeValue] at h
  | .int _, .vec _ _ _ => simp [storeValue] at h
  | .ptr, .int _ _ => simp [storeValue] at h
  | .ptr, .ptr _ => simp [storeValue] at h; cases h; rfl
  | .ptr, .vec _ _ _ => simp [storeValue] at h
  | .void, _ => cases v <;> simp [storeValue] at h
  | .vec n (.int w), .int _ _ => simp [storeValue] at h
  | .vec n (.int w), .ptr _ => simp [storeValue] at h
  | .vec n (.int w), .vec n' w' lanes =>
      simp only [storeValue] at h
      split at h
      · cases h; rfl
      · cases h
  | .vec n (.vec _ _), _ => cases v <;> simp [storeValue] at h
  | .vec n .ptr, _ => cases v <;> simp [storeValue] at h
  | .vec n .void, _ => cases v <;> simp [storeValue] at h

theorem evalInstr_env_pre (calls : Calls) (s s' : State) (i : Instr)
    (h : evalInstr calls s i = some s') :
    (i.dst? = none ∧ s'.env = s.env) ∨
      (∃ d v, i.dst? = some d ∧ s'.env = (d, v) :: s.env) := by
  cases i <;> simp only [evalInstr] at h
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · cases h
    exact Or.inr ⟨_, _, rfl, rfl⟩
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inl ⟨rfl, storeValue_env _ _ _ _ _ h⟩
             | exact Or.inr ⟨_, _, rfl, rfl⟩)
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))
  · (try (split at h)) <;> (try (split at h)) <;> (try (split at h)) <;>
      (try (split at h)) <;> (try (split at h)) <;> (try (cases h)) <;>
      (first | exact Or.inr ⟨_, _, rfl, rfl⟩
             | exact Or.inl ⟨rfl, rfl⟩
             | (rw [Option.map_eq_some_iff] at h; rcases h with ⟨r, _, rfl⟩;
                exact Or.inr ⟨_, _, rfl, rfl⟩))

theorem evalInstr_lookupName (calls : Calls) (s s' : State) (i : Instr) (n : String)
    (h : evalInstr calls s i = some s') (hn : i.dst? ≠ some n) :
    lookupName s'.env n = lookupName s.env n := by
  rcases evalInstr_env_pre calls s s' i h with ⟨_, he⟩ | ⟨d, v, hd, he⟩
  · rw [he]
  · rw [he]
    exact lookupName_cons_ne v s.env (fun hdn => hn (hdn ▸ hd))

theorem denoteCode_lookupName (calls : Calls) (instrs : List Instr) (n : String)
    (hn : ∀ i ∈ instrs, i.dst? ≠ some n) :
    ∀ (s s' : State), denoteCode calls instrs s = some s' →
      lookupName s'.env n = lookupName s.env n := by
  induction instrs with
  | nil =>
      intro s s' h
      simp only [denoteCode, Option.some.injEq] at h
      subst h
      rfl
  | cons i is ih =>
      intro s s' h
      simp only [denoteCode] at h
      split at h
      · cases h
      · rename_i s1 h1
        rw [ih (fun j hj => hn j (List.mem_cons_of_mem _ hj)) s1 s' h,
          evalInstr_lookupName calls s s1 i n h1 (hn i (List.mem_cons_self ..))]

/-- The six parameter names the loop carries across a block. -/
def pos8Params : List String := ["%ent", "%blk0", "%nblk", "%out", "%k", "%tab"]

theorem denoteCode_params (instrs : List Instr) (env env' : Env) (s : State)
    (hrun : denoteCode entryCalls instrs (withEnv env s) = some (withEnv env' s))
    (hn : ∀ i ∈ instrs, i.dst? ∉ pos8Params.map some) :
    ∀ n ∈ pos8Params, lookupName env' n = lookupName env n := by
  intro n hmem
  exact denoteCode_lookupName entryCalls instrs n
    (fun i hi hd => hn i hi (hd.symm ▸ List.mem_map_of_mem (f := some) hmem)) (withEnv env s) (withEnv env' s) hrun

/-! ### Numeric helpers -/

theorem ofInt64_zero : (BitVec.ofInt 64 0 : BitVec 64) = 0 := by decide

theorem ofInt64_one : (BitVec.ofInt 64 1 : BitVec 64) = 1 := by decide

theorem ofNat64_add_ofNat (a b : Nat) (h : a + b < 2 ^ 64) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

theorem ofNat64_add_one (n : Nat) (h : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + (1 : BitVec 64) = BitVec.ofNat 64 (n + 1) := by
  have := ofNat64_add_ofNat n 1 (by simpa using h)
  simpa using this

theorem ofBool_eq_one {p : Prop} [Decidable p] (h : p) :
    BitVec.ofBool (decide p) = (1 : BitVec 1) := by
  rw [decide_eq_true h]
  rfl

theorem ofBool_eq_zero {p : Prop} [Decidable p] (h : ¬ p) :
    BitVec.ofBool (decide p) = (0 : BitVec 1) := by
  rw [decide_eq_false h]
  rfl

/-- The zero word has no set lanes.  Proved through `filter_eq_nil_of_all_false`
rather than `simp`, whose `List.filter_eq_nil_iff` carries `Classical.choice`. -/
theorem setLanes_zero {w : Nat} : setLanes (0 : BitVec w) = [] := by
  unfold setLanes
  exact filter_eq_nil_of_all_false (fun _ _ => BitVec.getLsbD_zero)

theorem byteOf_zero (j : Nat) : byteOf (0 : BitVec 64) j = 0 := by
  unfold byteOf
  simp

theorem ctpop_zero64 : ctpop (0 : BitVec 64) = 0 := by
  rw [ctpop_eq_setLanes_length, setLanes_zero]
  rfl

theorem groupLanes_zero (base j : Nat) : groupLanes (0 : BitVec 64) base j = [] := by
  unfold groupLanes groupPop
  rw [byteOf_zero]
  show List.map (fun v => v + groupLane base j)
      (List.take (setLanes (BitVec.ofNat 8 0)).length (pos8Row 0)) = []
  rw [show (BitVec.ofNat 8 0 : BitVec 8) = 0 from rfl, setLanes_zero]
  rfl

theorem blockPositions_zero (base : Nat) : blockPositions (0 : BitVec 64) base 8 = [] := by
  unfold blockPositions blockLanes
  have h : (List.map (fun t => groupLanes (0 : BitVec 64) base t) (List.range 8)).flatten = [] := by
    rw [List.flatten_eq_nil_iff]
    intro l hl
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hl
    exact groupLanes_zero base t
  rw [h]
  rfl

def blockStore (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) : Mem :=
  if w = 0 then mem else blockMem o w base k 8 mem

def pos8MemFold (o : Nat) : Nat → Nat → List (BitVec 64) → Mem → Mem
  | _, _, [], mem => mem
  | base, k, w :: ws, mem =>
      pos8MemFold o (base + 64) (k + ctpop w) ws (blockStore o w base k mem)

def pos8Cursor : List (BitVec 64) → Nat → Nat
  | [], k => k
  | w :: ws, k => pos8Cursor ws (k + ctpop w)

def pos8Stream : List (BitVec 64) → Nat → List Nat
  | [], _ => []
  | w :: ws, base => blockPositions w base 8 ++ pos8Stream ws (base + 64)

theorem blockStore_zero (o : Nat) (base k : Nat) (mem : Mem) :
    blockStore o 0 base k mem = mem := by
  unfold blockStore
  simp

theorem blockStore_of_ne (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (h : w ≠ 0) :
    blockStore o w base k mem = blockMem o w base k 8 mem := by
  unfold blockStore
  split
  · exact absurd ‹w = 0› h
  · rfl

theorem pos8Cursor_eq_sum (ent : List (BitVec 64)) (k : Nat) :
    pos8Cursor ent k = k + (ent.map ctpop).sum := by
  induction ent generalizing k with
  | nil => rfl
  | cons w ws ih =>
      rw [pos8Cursor, ih, List.map_cons, List.sum_cons]
      omega

theorem pos8Cursor_le (ent : List (BitVec 64)) (k : Nat) :
    pos8Cursor ent k ≤ k + 64 * ent.length := by
  rw [pos8Cursor_eq_sum]
  induction ent generalizing k with
  | nil => simp
  | cons w ws ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have h1 : k + (ctpop w + (ws.map ctpop).sum) ≤ k + 64 * (ws.length + 1) := by
        have h2 : ctpop w ≤ 64 := ctpop_le w
        have h3 : k + (ws.map ctpop).sum ≤ k + 64 * ws.length := by
          have := ih k; omega
        omega
      omega

theorem pos8MemFold_append (o base k : Nat) (a b : List (BitVec 64)) (mem : Mem) :
    pos8MemFold o base k (a ++ b) mem =
      pos8MemFold o (base + 64 * a.length) (pos8Cursor a k) b
        (pos8MemFold o base k a mem) := by
  induction a generalizing base k mem with
  | nil =>
      show pos8MemFold o base k b mem =
        pos8MemFold o (base + 64 * ([] : List (BitVec 64)).length) (pos8Cursor [] k) b mem
      rw [pos8Cursor]
      rfl
  | cons w ws ih =>
      show pos8MemFold o (base + 64) (k + ctpop w) (ws ++ b) (blockStore o w base k mem) =
        pos8MemFold o (base + 64 * (ws.length + 1)) (pos8Cursor ws (k + ctpop w)) b
          (pos8MemFold o (base + 64) (k + ctpop w) ws (blockStore o w base k mem))
      rw [ih (base + 64) (k + ctpop w) (blockStore o w base k mem)]
      rw [show base + 64 * (ws.length + 1) = (base + 64) + 64 * ws.length from by omega]

theorem blockStore_frame (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (k + ctpop w + 8) ≤ p) :
    readBytes (blockStore o w base k mem) p n = readBytes mem p n := by
  unfold blockStore
  split
  · rfl
  · exact blockMem_frame_tight o w base k mem p n hdisj 8 (Nat.le_refl 8)

theorem pos8MemFold_frame (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem) (p n : Nat)
    (hdisj : p + n ≤ o + 4 * k ∨ o + 4 * (pos8Cursor ent k + 8) ≤ p) :
    readBytes (pos8MemFold o base k ent mem) p n = readBytes mem p n := by
  induction ent generalizing base k mem with
  | nil => rfl
  | cons w ws ih =>
      have h1 : readBytes (pos8MemFold o (base + 64) (k + ctpop w) ws
          (blockStore o w base k mem)) p n = readBytes (blockStore o w base k mem) p n := by
        refine ih (base + 64) (k + ctpop w) (blockStore o w base k mem) ?_
        rcases hdisj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by show o + 4 * (pos8Cursor ws (k + ctpop w) + 8) ≤ p; exact h)
      show readBytes (pos8MemFold o (base + 64) (k + ctpop w) ws
          (blockStore o w base k mem)) p n = readBytes mem p n
      rw [h1]
      refine blockStore_frame o w base k mem p n ?_
      rcases hdisj with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        have h' : o + 4 * (pos8Cursor ws (k + ctpop w) + 8) ≤ p := h
        have hle : k + ctpop w ≤ pos8Cursor ws (k + ctpop w) := by
          rw [pos8Cursor_eq_sum]
          omega
        have h2 : 4 * (k + ctpop w + 8) ≤ 4 * (pos8Cursor ws (k + ctpop w) + 8) :=
          Nat.mul_le_mul_left 4 (Nat.add_le_add_right hle 8)
        omega

theorem readLanes32_congr (m m' : Mem) (addr : Nat) :
    ∀ n, (∀ j, j < n → readBytes m' (addr + 4 * j) 4 = readBytes m (addr + 4 * j) 4) →
      readLanes32 m' addr n = readLanes32 m addr n
  | 0, _ => rfl
  | n + 1, h => by
      show (readBytes m' addr 4).bind (fun bs =>
          (readLanes32 m' (addr + 4) n).map fun rest => bytesToNat bs :: rest) =
        (readBytes m addr 4).bind (fun bs =>
          (readLanes32 m (addr + 4) n).map fun rest => bytesToNat bs :: rest)
      have h0 : readBytes m' addr 4 = readBytes m addr 4 := by
        have hh := h 0 (by omega)
        rwa [show addr + 4 * 0 = addr from by omega] at hh
      rw [h0]
      have hrec : readLanes32 m' (addr + 4) n = readLanes32 m (addr + 4) n := by
        apply readLanes32_congr m m' (addr + 4) n
        intro j hj
        rw [show addr + 4 + 4 * j = addr + 4 * (j + 1) from by omega]
        exact h (j + 1) (by omega)
      rw [hrec]

theorem pos8MemFold_read (o base k : Nat) (ent : List (BitVec 64)) (mem : Mem) :
    readLanes32 (pos8MemFold o base k ent mem) (o + 4 * k) (pos8Cursor ent k - k)
      = some (pos8Stream ent base) := by
  induction ent generalizing base k mem with
  | nil =>
      show readLanes32 mem (o + 4 * k) (pos8Cursor [] k - k) = some (pos8Stream [] base)
      rw [pos8Cursor, Nat.sub_self]
      rfl
  | cons w ws ih =>
      by_cases hw : w = 0
      · subst hw
        have hstream : pos8Stream ((0 : BitVec 64) :: ws) base = pos8Stream ws (base + 64) := by
          show blockPositions (0 : BitVec 64) base 8 ++ pos8Stream ws (base + 64) = _
          rw [blockPositions_zero]
          rfl
        rw [hstream]
        show readLanes32 (pos8MemFold o (base + 64) (k + ctpop (0 : BitVec 64)) ws
            (blockStore o (0 : BitVec 64) base k mem)) (o + 4 * k) (pos8Cursor ws (k + 0) - k)
          = some (pos8Stream ws (base + 64))
        simp only [ctpop_zero64, blockStore_zero, Nat.add_zero]
        exact ih (base + 64) k mem
      · have hfold : pos8MemFold o base k (w :: ws) mem
            = pos8MemFold o (base + 64) (k + ctpop w) ws (blockMem o w base k 8 mem) := by
          show pos8MemFold o (base + 64) (k + ctpop w) ws (blockStore o w base k mem) = _
          rw [blockStore_of_ne o w base k mem hw]
        rw [hfold]
        have hlen : pos8Cursor (w :: ws) k - k
            = ctpop w + (pos8Cursor ws (k + ctpop w) - (k + ctpop w)) := by
          rw [pos8Cursor_eq_sum, pos8Cursor_eq_sum, List.map_cons, List.sum_cons]
          omega
        rw [hlen]
        have hbelow : readLanes32 (pos8MemFold o (base + 64) (k + ctpop w) ws
              (blockMem o w base k 8 mem)) (o + 4 * k) (ctpop w)
            = some (blockPositions w base 8) := by
          have hcongr := readLanes32_congr
            (blockMem o w base k 8 mem)
            (pos8MemFold o (base + 64) (k + ctpop w) ws (blockMem o w base k 8 mem))
            (o + 4 * k) (ctpop w) (fun j _ => by
              exact pos8MemFold_frame o (base + 64) (k + ctpop w) ws
                (blockMem o w base k 8 mem) (o + 4 * k + 4 * j) 4 (Or.inl (by omega)))
          rw [hcongr]
          exact blockMem_readLanes o w base k mem
        have habove : readLanes32 (pos8MemFold o (base + 64) (k + ctpop w) ws
              (blockMem o w base k 8 mem)) (o + 4 * k + 4 * ctpop w)
              (pos8Cursor ws (k + ctpop w) - (k + ctpop w))
            = some (pos8Stream ws (base + 64)) := by
          have harith : o + 4 * k + 4 * ctpop w = o + 4 * (k + ctpop w) := by omega
          rw [harith]
          exact ih (base + 64) (k + ctpop w) (blockMem o w base k 8 mem)
        have hadd := readLanes32_add
          (pos8MemFold o (base + 64) (k + ctpop w) ws (blockMem o w base k 8 mem))
          (ctpop w) (o + 4 * k) (blockPositions w base 8)
          (pos8Cursor ws (k + ctpop w) - (k + ctpop w))
          (pos8Stream ws (base + 64)) hbelow habove
        rw [hadd]
        rfl

theorem mapIdx_congr {α β : Type} {l : List α} {f g : Nat → α → β}
    (h : ∀ i (a : α), i < l.length → f i a = g i a) : l.mapIdx f = l.mapIdx g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.getElem_mapIdx, List.getElem_mapIdx]
    exact h i _ (by simpa using h1)

theorem pos8Stream_eq_positions (ent : List (BitVec 64)) (base : Nat)
    (hblk : base + 64 * ent.length < 2 ^ 32) :
    pos8Stream ent base = (ent.mapIdx fun i w => positionsOf w (base + 64 * i)).flatten := by
  induction ent generalizing base with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.length_cons] at hblk
      show blockPositions w base 8 ++ pos8Stream ws (base + 64) = _
      rw [blockPositions_eight w base (by omega), ih (base + 64) (by omega),
        List.mapIdx_cons, List.flatten_cons]
      congr 1
      rw [mapIdx_congr (l := ws) (f := fun i a => positionsOf a (base + 64 + 64 * i))
        (g := fun i a => positionsOf a (base + 64 * (i + 1)))
        (fun i a _ => by rw [show base + 64 + 64 * i = base + 64 * (i + 1) from by omega])]

theorem pos8Stream_eq_streamPrefix (ent : List (BitVec 64)) (blk0 : Nat) :
    (ent.mapIdx fun i w => positionsOf w (64 * blk0 + 64 * i)).flatten
      = streamPrefix ent blk0 ent.length := by
  rw [streamPrefix, List.take_length]
  congr 1
  rw [mapIdx_congr (l := ent) (f := fun i a => positionsOf a (64 * blk0 + 64 * i))
    (g := fun i a => positionsOf a (64 * (blk0 + i)))
    (fun i a _ => by rw [Nat.mul_add])]

theorem wordsOf_cons (w : BitVec 64) (ws : List (BitVec 64)) :
    wordsOf (w :: ws) = natToBytes w.toNat 8 ++ wordsOf ws := by
  simp [wordsOf]

theorem wordsOf_length (ent : List (BitVec 64)) : (wordsOf ent).length = 8 * ent.length := by
  induction ent with
  | nil => rfl
  | cons w ws ih =>
      rw [wordsOf_cons, List.length_append, natToBytes_length, ih, List.length_cons]
      omega

theorem readBytes_wordsOf (m : Mem) (e : Nat) (ent : List (BitVec 64))
    (h : readBytes m e (8 * ent.length) = some (wordsOf ent)) :
    ∀ (i : Nat) (hi : i < ent.length),
      readBytes m (e + 8 * i) 8 = some (natToBytes (ent[i]).toNat 8) := by
  induction ent generalizing e with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons w ws ih =>
      intro i hi
      rw [show (w :: ws).length = ws.length + 1 from rfl] at h
      rw [show 8 * (ws.length + 1) = 8 + 8 * ws.length from by omega,
        wordsOf_cons] at h
      obtain ⟨h1, h2⟩ := readBytes_split m e 8 (8 * ws.length) h
      rw [take_natToBytes_append w.toNat 8 (wordsOf ws)] at h1
      rw [drop_natToBytes_append w.toNat 8 (wordsOf ws)] at h2
      cases i with
      | zero =>
          rw [show e + 8 * 0 = e from by omega]
          simpa using h1
      | succ i =>
          have hi' : i < ws.length := by simpa using hi
          rw [show e + 8 * (i + 1) = e + 8 + 8 * i from by omega]
          rw [show (w :: ws)[i + 1] = ws[i] from List.getElem_cons_succ w ws i hi]
          exact ih (e + 8) h2 i hi'





/-! ### The tight frames, from the statement's disjointness

`hdisj` is stated against the run's own span, `o + 4 * (k + 64 * ent.length + 8)`,
and a block's stores reach only `o + 4 * (kᵢ + popcount wᵢ + 8)` with
`kᵢ + popcount wᵢ ≤ k + 64 * ent.length`.  These two lemmas are that step, one per
buffer: the table frame `pos8Groups_run` consumes, and the mask-word frame the
loop's read consumes.  Stated on their own so the derivation is checkable where
the hypothesis is supplied rather than buried in an induction. -/

/-- The cursor bound `pos8Groups_run` takes, from the statement's own: a block's
largest output index is `k + 63`, so `k + 64 ≤ 2 ^ 63` follows from `hk63` once a
block exists.  The side condition is real — at `nblk = 0` the statement gives only
`k + 9 < 2 ^ 63` — and it is harmless because no block runs then: the loop's
zero-block arm returns `k` with the incoming memory and never reaches a group
store. -/
theorem groups_hk63_of_hk63 (k nblk : Nat) (hpos : 1 ≤ nblk)
    (h : k + 64 * nblk + 9 < 2 ^ 63) : k + 64 ≤ 2 ^ 63 := by
  have hmul : 64 ≤ 64 * nblk := Nat.mul_le_mul_left 64 hpos
  omega

/-- A block's table frame, from the statement's disjointness. -/
theorem table_disj_of_hdisj (o tab k k0 nblk b : Nat)
    (hk : k + b ≤ k0 + 64 * nblk)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ tab) :
    tab + 8192 ≤ o ∨ o + 4 * (k + b + 8) ≤ tab := by
  rcases hdisj with h | h
  · exact Or.inl h
  · refine Or.inr ?_
    have h4 : 4 * (k + b + 8) ≤ 4 * (k0 + 64 * nblk + 8) :=
      Nat.mul_le_mul_left 4 (by omega)
    omega

/-- The mask word's frame, from the statement's disjointness: the read happens at
the cursor the first `i` blocks leave, and the fold's stores stay inside `k`'s own
span. -/
theorem mask_disj_of_hdisj (o e k0 nblk i k : Nat)
    (hi : i < nblk)
    (hk : k ≤ k0 + 64 * i)
    (hdisj : e + 8 * nblk ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ e) :
    e + 8 * i + 8 ≤ o + 4 * k ∨ o + 4 * (k + 8) ≤ e + 8 * i := by
  rcases hdisj with h | h
  · left
    omega
  · right
    have h4 : 4 * (k + 8) ≤ 4 * (k0 + 64 * nblk + 8) :=
      Nat.mul_le_mul_left 4 (by omega)
    omega

/-! ### Block lookup and the terminators -/

theorem findBlock_pos8Entry :
    entryPos8Function.findBlock "entry" = some pos8Entry := by
  simp [entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups, pos8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_pos8Body :
    entryPos8Function.findBlock "for.body" = some pos8Body := by
  simp [entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups, pos8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_pos8Groups :
    entryPos8Function.findBlock "if.end" = some pos8Groups := by
  simp [entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups, pos8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_pos8Advance :
    entryPos8Function.findBlock "cleanup" = some pos8Advance := by
  simp [entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups, pos8Advance,
    Function.findBlock, findBlockList]

theorem findBlock_pos8Exit :
    entryPos8Function.findBlock "for.cond.cleanup" = some pos8LoopExit := by
  simp [entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups, pos8Advance,
    Function.findBlock, findBlockList]

theorem execTerm_condbr_true {s : State} {c : Operand} {bit : BitVec 1} {t f : String}
    (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 1) :
    execTerm s (.condbr c t f) = .jump { s with pc := t, pre := some s.pc } := by
  simp [execTerm, h, hb]

theorem execTerm_condbr_false {s : State} {c : Operand} {bit : BitVec 1} {t f : String}
    (h : evalOperand s c = some (.int 1 bit)) (hb : bit = 0) :
    execTerm s (.condbr c t f) = .jump { s with pc := f, pre := some s.pc } := by
  simp [execTerm, h, hb]

theorem execTerm_br (s : State) (d : String) :
    execTerm s (.br d) = .jump { s with pc := d, pre := some s.pc } := rfl

theorem execTerm_ret_reg (s : State) (d : String) (v : Value)
    (h : evalOperand s (.reg d) = some v) :
    execTerm s (.ret (.int 64) (some (.reg d))) = .ret (some v) s := by
  simp [execTerm, h]

theorem step_of (s : State) (name : String) (b : Block) (s' : State)
    (hpc : s.pc = name) (hfind : entryPos8Function.findBlock name = some b)
    (hbody : denoteCode entryCalls b.instrs s = some s') :
    step entryCalls entryPos8Function s = execTerm s' b.term := by
  simp [step, hpc, hfind, hbody]

theorem runFuel_jump {s s' : State} {n : Nat}
    (h : step entryCalls entryPos8Function s = .jump s') :
    runFuel entryCalls (n + 1) entryPos8Function s = runFuel entryCalls n entryPos8Function s' := by
  simp [runFuel, h]

theorem runFuel_ret {s s' : State} {v : Option Value} {n : Nat}
    (h : step entryCalls entryPos8Function s = .ret v s') :
    runFuel entryCalls (n + 1) entryPos8Function s = some (.ret v s'.mem) := by
  simp [runFuel, h]

theorem runFuel_ub {s : State} {n : Nat}
    (h : step entryCalls entryPos8Function s = .ub) :
    runFuel entryCalls (n + 1) entryPos8Function s = some .ub := by
  simp [runFuel, h]

theorem withEnv_withEnv (env env' : Env) (s : State) :
    withEnv env' (withEnv env s) = withEnv env' s := rfl

theorem withEnv_pc (env : Env) (s : State) : (withEnv env s).pc = s.pc := rfl

theorem phi_step (env : Env) (s : State) (d : String) (ty : Ty)
    (inc : List (String × Operand)) (p : String) (op : Operand) (v : Value)
    (hpre : s.pre = some p) (hinc : phiIncoming p inc = some op)
    (hop : evalOperand (withEnv env s) op = some v) :
    evalInstr entryCalls (withEnv env s) (.phi d ty inc) = some (withEnv ((d, v) :: env) s) := by
  rw [evalInstr_phi (s := withEnv env s) hpre hinc hop]
  rfl

/-! ### The incoming lists -/

def pos8IncomingK : List (String × Operand) :=
  [("cleanup", reg "%k.addr.1"), ("entry", reg "%k")]

def pos8IncomingI : List (String × Operand) :=
  [("cleanup", reg "%inc"), ("entry", lit 64 0)]

def pos8IncomingCl : List (String × Operand) :=
  [("if.end", reg "%add1"), ("for.body", reg "%k.addr.011")]

def pos8IncomingE : List (String × Operand) :=
  [("entry", reg "%k"), ("cleanup", reg "%k.addr.1")]

/-! ### `entry` -/

theorem pos8Entry_body (env : Env) (s : State) (nblk : Nat)
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk))) :
    ∃ env', denoteCode entryCalls pos8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%cmp9.not" = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) := by
  refine ⟨?env', ?hrun, ?hnot⟩
  case hrun =>
    simp only [pos8Entry, reg, lit]
    ent_step (step_icmp_eq_imm env s "%cmp9.not" "%nblk" 64 (BitVec.ofNat 64 nblk)
      (BitVec.ofInt 64 0) (by ent_auto))
    rw [ofInt64_zero]
    simp only [denoteCode, Option.bind]
    rfl
  case hnot => ent_auto

/-! ### `for.body` -/

theorem pos8Body_body (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63) :
    ∃ env', denoteCode entryCalls pos8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 (BitVec.ofBool (w = 0))) := by
  refine ⟨?env', ?hrun, ?hi, ?hk, ?h0, ?hb⟩
  case hrun =>
    simp only [pos8Body, reg, lit, pos8IncomingK, pos8IncomingI]
    have hopk' : phiIncoming p
        [("cleanup", Operand.reg "%k.addr.1"), ("entry", Operand.reg "%k")] = some opk := hopk
    have hopi' : phiIncoming p
        [("cleanup", Operand.reg "%inc"),
         ("entry", Operand.imm (Const.int 64 (BitVec.ofInt 64 0)))] = some opi := hopi
    ent_step (phi_step env s "%k.addr.011" (.int 64) _ p opk _ hpre hopk' hvk)
    ent_step (phi_step (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s
      "%i.010" (.int 64) _ p opi _ hpre hopi' hvi)
    ent_step (step_gep64 _ _ "%arrayidx" "%ent" "%i.010" (.int 64) e (BitVec.ofNat 64 i)
      (by ent_auto) (by ent_auto)
      (by rw [toNat_ofNat64 i (by omega)]; omega))
    rw [show e + (BitVec.ofNat 64 i).toNat * (Ty.int 64).sizeBytes = e + 8 * i from by
      rw [toNat_ofNat64 i (by omega), show (Ty.int 64).sizeBytes = 8 from rfl]
      omega]
    ent_step (step_load64 _ _ "%0" "%arrayidx" (e + 8 * i) w (by ent_auto) hread)
    ent_step (step_icmp_eq_imm _ _ "%tobool.not" "%0" 64 w (BitVec.ofInt 64 0) (by ent_auto))
    rw [ofInt64_zero]
    simp only [denoteCode, Option.bind]
    rfl
  case hi => ent_auto
  case hk => ent_auto
  case h0 => ent_auto
  case hb => ent_auto

/-! ### `cleanup` -/

theorem pos8Cleanup_body (env : Env) (s : State) (i k nblk : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64) :
    ∃ env', denoteCode entryCalls pos8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not"
        = some (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) := by
  refine ⟨?env', ?hrun, ?hk, ?hinc, ?hx⟩
  case hrun =>
    simp only [pos8Advance, reg, lit, pos8IncomingCl]
    have hopk' : phiIncoming p
        [("if.end", Operand.reg "%add1"), ("for.body", Operand.reg "%k.addr.011")] = some opk := hopk
    ent_step (phi_step env s "%k.addr.1" (.int 64) _ p opk _ hpre hopk' hvk)
    ent_step (step_add_imm _ _ "%inc" "%i.010" 64 (BitVec.ofNat 64 i) (BitVec.ofInt 64 1)
      (by ent_auto))
    rw [ofInt64_one, ofNat64_add_one i hi64]
    ent_step (step_icmp_eq_reg _ _ "%exitcond.not" "%inc" "%nblk" 64
      (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 nblk) (by ent_auto) (by ent_auto))
    simp only [denoteCode, Option.bind]
    rfl
  case hk => ent_auto
  case hinc => ent_auto
  case hx => ent_auto

/-! ### `for.cond.cleanup` -/

theorem pos8Exit_body (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', denoteCode entryCalls pos8LoopExit.instrs (withEnv env s) = some (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) := by
  refine ⟨?env', ?hrun, ?hk⟩
  case hrun =>
    simp only [pos8LoopExit, reg, lit, pos8IncomingE]
    have hopk' : phiIncoming p
        [("entry", Operand.reg "%k"), ("cleanup", Operand.reg "%k.addr.1")] = some opk := hopk
    ent_step (phi_step env s "%k.addr.0.lcssa" (.int 64) _ p opk _ hpre hopk' hvk)
    simp only [denoteCode, Option.bind]
    rfl
  case hk => ent_auto




theorem pos8Params_body : ∀ i ∈ pos8Body.instrs, i.dst? ∉ pos8Params.map some := by decide
theorem pos8Params_groups : ∀ i ∈ pos8GroupsInstrs, i.dst? ∉ pos8Params.map some := by decide
theorem pos8Params_cleanup : ∀ i ∈ pos8Advance.instrs, i.dst? ∉ pos8Params.map some := by decide
theorem pos8Params_exit : ∀ i ∈ pos8LoopExit.instrs, i.dst? ∉ pos8Params.map some := by decide

theorem denoteCode_param' (instrs : List Instr) (env env' : Env) (s s' : State)
    (hrun : denoteCode entryCalls instrs s = some s')
    (henv : s.env = env) (henv' : s'.env = env')
    (hn : ∀ i ∈ instrs, i.dst? ∉ pos8Params.map some) :
    ∀ n ∈ pos8Params, lookupName env' n = lookupName env n := by
  intro n hmem
  have h := denoteCode_lookupName entryCalls instrs n
    (fun i hi hd => hn i hi (hd.symm ▸ List.mem_map_of_mem (f := some) hmem)) s s' hrun
  rw [henv', henv] at h
  exact h

theorem pos8_i010_groups : ∀ i ∈ pos8GroupsInstrs, i.dst? ≠ some "%i.010" := by decide
theorem pos8_i010_cleanup : ∀ i ∈ pos8Advance.instrs, i.dst? ≠ some "%i.010" := by decide

/-! ### `entry` -/

theorem pos8Entry_step_zero (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (h0 : nblk = 0) :
    ∃ env', denoteCode entryCalls pos8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, hnot⟩ := pos8Entry_body env s nblk hnblk
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (1 : BitVec 1) := by
    subst h0
    rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [step_of (withEnv env s) "entry" pos8Entry (withEnv env' s) hpc findBlock_pos8Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "entry" })
    have hop := evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_true (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

theorem pos8Entry_step_pos (env : Env) (s : State) (nblk : Nat)
    (hpc : s.pc = "entry")
    (hnblk : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hnblk64 : nblk < 2 ^ 64)
    (h0 : nblk ≠ 0) :
    ∃ env', denoteCode entryCalls pos8Entry.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" }) ∧
      lookupName env' "%cmp9.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, hnot⟩ := pos8Entry_body env s nblk hnblk
  have hne : ¬ (BitVec.ofNat 64 nblk = 0) := by
    intro h
    have h1 : (BitVec.ofNat 64 nblk).toNat = nblk := toNat_ofNat64 nblk hnblk64
    rw [h] at h1
    simp at h1
    omega
  have hb : BitVec.ofBool (BitVec.ofNat 64 nblk = 0) = (0 : BitVec 1) := by
    have hd : decide (BitVec.ofNat 64 nblk = 0) = false := decide_eq_false hne
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, ?_⟩
  · rw [step_of (withEnv env s) "entry" pos8Entry (withEnv env' s) hpc findBlock_pos8Entry hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%cmp9.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "entry" })
    have hop := evalOperand_reg_of env' s "%cmp9.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 nblk = 0))) hnot
    rw [execTerm_condbr_false (c := .reg "%cmp9.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "entry" from hpc]
    rfl
  · rwa [hb] at hnot

/-! ### `for.body` -/

theorem pos8Body_step_zero (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w = 0) :
    ∃ env', denoteCode entryCalls pos8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    pos8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (1 : BitVec 1) := by
    have hd : decide (w = 0) = true := decide_eq_true hw
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [step_of (withEnv env s) "for.body" pos8Body (withEnv env' s) hpc findBlock_pos8Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "cleanup", pre := some "for.body" })
    have hop := evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4
    rw [execTerm_condbr_true (c := .reg "%tobool.not") (t := "cleanup")
      (f := "if.end") hop hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

theorem pos8Body_step_pos (env : Env) (s : State) (w : BitVec 64) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8))
    (hi63 : i < 2 ^ 63)
    (hw : w ≠ 0) :
    ∃ env', denoteCode entryCalls pos8Body.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" }) ∧
      lookupName env' "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%tobool.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, h1, h2, h3, h4⟩ :=
    pos8Body_body env s w i k e p opk opi hpre hopk hopi hvk hvi hent hread hi63
  have hb : BitVec.ofBool (w = 0) = (0 : BitVec 1) := by
    have hd : decide (w = 0) = false := decide_eq_false hw
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, h1, h2, h3, ?_⟩
  · rw [step_of (withEnv env s) "for.body" pos8Body (withEnv env' s) hpc findBlock_pos8Body hbody]
    show execTerm (withEnv env' s) (.condbr (.reg "%tobool.not") "cleanup" "if.end")
      = .jump (withEnv env' { s with pc := "if.end", pre := some "for.body" })
    have hop := evalOperand_reg_of env' s "%tobool.not" (.int 1 (BitVec.ofBool (w = 0))) h4
    rw [execTerm_condbr_false (c := .reg "%tobool.not") (t := "cleanup")
      (f := "if.end") hop hb]
    rw [show (withEnv env' s).pc = "for.body" from hpc]
    rfl
  · rwa [hb] at h4

/-! ### `if.end` -/

theorem pos8Groups_step (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (M : Mem)
    (hpc : s.pc = "if.end")
    (hM : M = blockMem o w (posBase blk0 i) k 8 s.mem)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (htabread : readBytes s.mem tab 8192 = some pos8Table)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    ∃ env', denoteCode entryCalls pos8GroupsInstrs (withEnv env s) = some (withEnv env' { s with mem := M }) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with mem := M, pc := "cleanup", pre := some "if.end" }) ∧
      (∀ n ∈ pos8Params, lookupName env' n = lookupName env n) ∧
      lookupName env' "%i.010" = lookupName env "%i.010" ∧
      lookupName env' "%add1"
        = some (.int 64 (BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k)) := by
  obtain ⟨env', hbody, h1⟩ := pos8Groups_run env s w i blk0 k o tab hi hbk hout hk h0 htab
    hk63 hblk hconv htabread hdisj
  have hbody' : denoteCode entryCalls pos8GroupsInstrs (withEnv env s)
      = some (withEnv env' { s with mem := M }) := by
    rw [← hM] at hbody; exact hbody
  have hparam : ∀ n ∈ pos8Params, lookupName env' n = lookupName env n := by
    intro n hn
    exact denoteCode_lookupName entryCalls pos8GroupsInstrs n
      (fun j hj hd => pos8Params_groups j hj (hd.symm ▸ List.mem_map_of_mem (f := some) hn))
      (withEnv env s) (withEnv env' { s with mem := M }) hbody'
  have hi010 : lookupName env' "%i.010" = lookupName env "%i.010" :=
    denoteCode_lookupName entryCalls pos8GroupsInstrs "%i.010"
      (fun j hj hd => pos8_i010_groups j hj hd)
      (withEnv env s) (withEnv env' { s with mem := M }) hbody'
  refine ⟨env', hbody', ?_, hparam, hi010, h1⟩
  rw [step_of (withEnv env s) "if.end" pos8Groups (withEnv env' { s with mem := M }) hpc
    findBlock_pos8Groups hbody']
  show execTerm (withEnv env' { s with mem := M }) (.br "cleanup")
    = .jump (withEnv env' { s with mem := M, pc := "cleanup", pre := some "if.end" })
  rw [execTerm_br]
  rw [show (withEnv env' { s with mem := M }).pc = "if.end" from hpc]
  rfl

/-! ### `cleanup` -/

theorem pos8Cleanup_step_last (env : Env) (s : State) (i k nblk : Nat) (p : String) (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls pos8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 1) := by
  obtain ⟨env', hbody, h1, h2, h3⟩ :=
    pos8Cleanup_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hb : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (1 : BitVec 1) := by
    have hd : decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = true := decide_eq_true hx
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, h1, h2, ?_⟩
  · rw [step_of (withEnv env s) "cleanup" pos8Advance (withEnv env' s) hpc
      findBlock_pos8Advance hbody]
    show execTerm (withEnv env' s)
        (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.cond.cleanup", pre := some "cleanup" })
    have hop := evalOperand_reg_of env' s "%exitcond.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) h3
    rw [execTerm_condbr_true (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hb] at h3

theorem pos8Cleanup_step_more (env : Env) (s : State) (i k nblk : Nat) (p : String) (opk : Operand)
    (hpc : s.pc = "cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingCl = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hnb : lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)))
    (hi64 : i + 1 < 2 ^ 64)
    (hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) :
    ∃ env', denoteCode entryCalls pos8Advance.instrs (withEnv env s) = some (withEnv env' s) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" }) ∧
      lookupName env' "%k.addr.1" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%inc" = some (.int 64 (BitVec.ofNat 64 (i + 1))) ∧
      lookupName env' "%exitcond.not" = some (.int 1 0) := by
  obtain ⟨env', hbody, h1, h2, h3⟩ :=
    pos8Cleanup_body env s i k nblk p opk hpre hopk hvk hi hnb hi64
  have hb : BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = (0 : BitVec 1) := by
    have hd : decide (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk) = false := decide_eq_false hx
    rw [hd]; rfl
  refine ⟨env', hbody, ?_, h1, h2, ?_⟩
  · rw [step_of (withEnv env s) "cleanup" pos8Advance (withEnv env' s) hpc
      findBlock_pos8Advance hbody]
    show execTerm (withEnv env' s)
        (.condbr (.reg "%exitcond.not") "for.cond.cleanup" "for.body")
      = .jump (withEnv env' { s with pc := "for.body", pre := some "cleanup" })
    have hop := evalOperand_reg_of env' s "%exitcond.not"
      (.int 1 (BitVec.ofBool (BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk))) h3
    rw [execTerm_condbr_false (c := .reg "%exitcond.not") (t := "for.cond.cleanup")
      (f := "for.body") hop hb]
    rw [show (withEnv env' s).pc = "cleanup" from hpc]
    rfl
  · rwa [hb] at h3

/-! ### `for.cond.cleanup` -/

theorem pos8Exit_step (env : Env) (s : State) (k : Nat) (p : String) (opk : Operand)
    (hpc : s.pc = "for.cond.cleanup")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingE = some opk)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k))) :
    ∃ env', step entryCalls entryPos8Function (withEnv env s)
        = .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s) ∧
      lookupName env' "%k.addr.0.lcssa" = some (.int 64 (BitVec.ofNat 64 k)) := by
  obtain ⟨env', hbody, hk⟩ := pos8Exit_body env s k p opk hpre hopk hvk
  refine ⟨env', ?_, hk⟩
  rw [step_of (withEnv env s) "for.cond.cleanup" pos8LoopExit (withEnv env' s) hpc
    findBlock_pos8Exit hbody]
  show execTerm (withEnv env' s) (.ret (.int 64) (some (.reg "%k.addr.0.lcssa"))) =
    .ret (some (.int 64 (BitVec.ofNat 64 k))) (withEnv env' s)
  rw [execTerm_ret_reg (withEnv env' s) "%k.addr.0.lcssa" (.int 64 (BitVec.ofNat 64 k))
    (evalOperand_reg_of env' s "%k.addr.0.lcssa" _ hk)]

/-! ### The loop -/

theorem pos8_take_length (ent : List (BitVec 64)) (i : Nat) (h : i ≤ ent.length) :
    (ent.take i).length = i := by
  rw [List.length_take, Nat.min_eq_left h]

theorem pos8_take_succ (ent : List (BitVec 64)) (i : Nat) (hi : i < ent.length) :
    ent.take (i + 1) = ent.take i ++ [ent[i]] := by
  have h := List.take_add_one (l := ent) (i := i)
  rwa [List.getElem?_eq_getElem hi] at h

theorem pos8Cursor_append (a b : List (BitVec 64)) (k : Nat) :
    pos8Cursor (a ++ b) k = pos8Cursor b (pos8Cursor a k) := by
  induction a generalizing k with
  | nil => rfl
  | cons w ws ih => exact ih (k + ctpop w)

theorem pos8Cursor_take_succ (ent : List (BitVec 64)) (k0 i : Nat) (hi : i < ent.length) :
    pos8Cursor (ent.take (i + 1)) k0 = pos8Cursor (ent.take i) k0 + ctpop (ent[i]) := by
  rw [pos8_take_succ ent i hi, pos8Cursor_append]
  rfl

theorem pos8Cursor_drop_succ (ent : List (BitVec 64)) (k i : Nat) (hi : i < ent.length) :
    pos8Cursor (ent.drop i) k = pos8Cursor (ent.drop (i + 1)) (k + ctpop (ent[i])) := by
  rw [List.drop_eq_getElem_cons hi]
  rfl

theorem pos8MemFold_succ (ent : List (BitVec 64)) (blk0 k0 o i : Nat) (mem0 : Mem)
    (hi : i < ent.length) :
    pos8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0
      = blockStore o (ent[i]) (posBase blk0 i) (pos8Cursor (ent.take i) k0)
          (pos8MemFold o (64 * blk0) k0 (ent.take i) mem0) := by
  rw [pos8_take_succ ent i hi, pos8MemFold_append]
  rw [pos8_take_length ent i (by omega)]
  rw [show 64 * blk0 + 64 * i = posBase blk0 i from by rw [posBase]; omega]
  rfl

/-- The mask word a block's iteration reads. -/
theorem pos8_read_word (ent : List (BitVec 64)) (blk0 k0 o e i : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hdisj : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hi : i < ent.length) :
    readBytes (pos8MemFold o (64 * blk0) k0 (ent.take i) mem0) (e + 8 * i) 8
      = some (natToBytes (ent[i]).toNat 8) := by
  have h0 := readBytes_wordsOf mem0 e ent hwords i hi
  have hfr := pos8MemFold_frame o (64 * blk0) k0 (ent.take i) mem0 (e + 8 * i) 8 (by
    rcases hdisj with h | h
    · left; omega
    · right
      have hc : pos8Cursor (ent.take i) k0 ≤ k0 + 64 * i := by
        have h1 := pos8Cursor_le (ent.take i) k0
        rwa [pos8_take_length ent i (by omega)] at h1
      omega)
  rw [hfr]; exact h0

/-- The table the block's group stores read. -/
theorem pos8_read_table (ent : List (BitVec 64)) (blk0 k0 o tab i : Nat) (mem0 : Mem)
    (hrows : readBytes mem0 tab 8192 = some pos8Table)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ tab)
    (hi : i < ent.length) :
    readBytes (pos8MemFold o (64 * blk0) k0 (ent.take i) mem0) tab 8192 = some pos8Table := by
  have hfr := pos8MemFold_frame o (64 * blk0) k0 (ent.take i) mem0 tab 8192 (by
    rcases hdisj with h | h
    · left; omega
    · right
      have hc : pos8Cursor (ent.take i) k0 ≤ k0 + 64 * i := by
        have h1 := pos8Cursor_le (ent.take i) k0
        rwa [pos8_take_length ent i (by omega)] at h1
      omega)
  rw [hfr]; exact hrows


theorem ofNat64_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b := by
  have h' := congrArg BitVec.toNat h
  rwa [toNat_ofNat64 a ha, toNat_ofNat64 b hb] at h'

theorem pos8_loop_run (ent : List (BitVec 64)) (blk0 nblk k0 o tab e : Nat) (mem0 : Mem)
    (hwords : readBytes mem0 e (8 * ent.length) = some (wordsOf ent))
    (hrows : readBytes mem0 tab 8192 = some pos8Table)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * ent.length + 9 < 2 ^ 63)
    (hdisjE : e + 8 * ent.length ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ e)
    (hdisjT : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * ent.length + 8) ≤ tab)
    (hnblk : nblk = ent.length) :
    ∀ (r i k : Nat) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = nblk → s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName env "%ent" = some (.ptr e) →
      lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) →
      lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) →
      lookupName env "%out" = some (.ptr o) →
      lookupName env "%tab" = some (.ptr tab) →
      k = pos8Cursor (ent.take i) k0 →
      s.mem = pos8MemFold o (64 * blk0) k0 (ent.take i) mem0 →
      ∃ (env' : Env) (mem' : Mem),
        runFuel entryCalls (3 * r + 1) entryPos8Function (withEnv env s)
          = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor (ent.drop i) k)))) mem') ∧
        mem' = pos8MemFold o (64 * blk0) k0 ent mem0 := by
  intro r
  induction r with
  | zero => intro i k env s p opk opi hr _; exact absurd hr (by simp)
  | succ r' ih =>
    intro i k env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hent hbk hNb hout htab hk hmem
    have hilen : i < ent.length := by omega
    have hkle : k ≤ k0 + 64 * i := by
      rw [hk]
      have hc := pos8Cursor_le (ent.take i) k0
      rwa [pos8_take_length ent i (by omega)] at hc
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hnblkpos : 1 ≤ nblk := by omega
    have hword : readBytes s.mem (e + 8 * i) 8 = some (natToBytes (ent[i]).toNat 8) := by
      rw [hmem]; exact pos8_read_word ent blk0 k0 o e i mem0 hwords hdisjE hilen
    have htabread : readBytes s.mem tab 8192 = some pos8Table := by
      rw [hmem]; exact pos8_read_table ent blk0 k0 o tab i mem0 hrows hdisjT hilen
    have hframe := fun (e1 : Env) (h : denoteCode entryCalls pos8Body.instrs (withEnv env s)
        = some (withEnv e1 s)) (n : String) (hn : n ∈ pos8Params) =>
      (denoteCode_params pos8Body.instrs env e1 s h pos8Params_body n hn)
    have hfuel : 3 * (r' + 1) + 1 = (((3 * r' + 1) + 1) + 1) + 1 := by omega
    have hxeq : BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk ↔ i + 1 = nblk :=
      ⟨fun h => ofNat64_inj (by omega) (by omega) h, fun h => by rw [h]⟩
    have hent_eq : ∀ _ : i + 1 = nblk, ent = ent.take (i + 1) := fun hlast => by
      have h1 : ent.take (i + 1) = ent.take nblk := by rw [hlast]
      rw [h1, hnblk, List.take_length]
    by_cases hw : ent[i] = 0
    · -- the word is zero: the body takes the `continue` edge
      obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
        pos8Body_step_zero env s (ent[i]) i k e p opk opi hpc hpre hopk hopi hvk hvi hent
          hword hi63 hw
      have hNb1 : lookupName e1 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
        (hframe e1 hrun1 "%nblk" (by decide)).trans hNb
      by_cases hlast : i + 1 = nblk
      · -- the loop is done: `for.cond.cleanup` returns the cursor
        obtain ⟨e2, hrun2, hstep2, hk2, hinc2, hx2⟩ :=
          pos8Cleanup_step_last e1 { s with pc := "cleanup", pre := some "for.body" } i k nblk
            "for.body" (.reg "%k.addr.011") rfl rfl rfl
            (evalOperand_reg_of e1 _ _ _ hk1) hi1 hNb1 hi64 (hxeq.mpr hlast)
        obtain ⟨e3, hstep3, hk3⟩ :=
          pos8Exit_step e2 { s with pc := "for.cond.cleanup", pre := some "cleanup" } k
            "cleanup" (.reg "%k.addr.1") rfl rfl rfl (evalOperand_reg_of e2 _ _ _ hk2)
        refine ⟨e3, s.mem, ?_, ?_⟩
        · rw [pos8Cursor_drop_succ ent k i hilen, hw, ctpop_zero64]
          have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
          rw [hdrop]
          rw [hfuel]
          rw [runFuel_jump hstep1, runFuel_jump hstep2, runFuel_ret hstep3]
          rfl
        · have hmem' : s.mem = pos8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
            rw [hmem, pos8MemFold_succ ent blk0 k0 o i mem0 hilen, hw, blockStore_zero]
          rw [hent_eq hlast, hmem']
      · -- the loop continues at the next block
        obtain ⟨e2, hrun2, hstep2, hk2, hinc2, hx2⟩ :=
          pos8Cleanup_step_more e1 { s with pc := "cleanup", pre := some "for.body" } i k nblk
            "for.body" (.reg "%k.addr.011") rfl rfl rfl
            (evalOperand_reg_of e1 _ _ _ hk1) hi1 hNb1 hi64 (fun hcon => hlast (hxeq.mp hcon))
        have hfr2 := fun (n : String) (hn : n ∈ pos8Params) =>
          (denoteCode_params pos8Advance.instrs e1 e2
            { s with pc := "cleanup", pre := some "for.body" } hrun2 pos8Params_cleanup n hn)
        have hkNext : k + ctpop (ent[i]) = pos8Cursor (ent.take (i + 1)) k0 := by
          rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm
        have hmemNext : s.mem = pos8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
          rw [hmem, pos8MemFold_succ ent blk0 k0 o i mem0 hilen, hw, blockStore_zero]
        obtain ⟨e3, mem3, hrun3, hmem3⟩ :=
          ih (i + 1) (k + ctpop (ent[i])) e2
            { s with pc := "for.body", pre := some "cleanup" } "cleanup"
            (.reg "%k.addr.1") (.reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl
            (by rw [hw, ctpop_zero64]; exact evalOperand_reg_of e2 _ _ _ hk2)
            (by
              rw [hw, ctpop_zero64]
              exact evalOperand_reg_of
                (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: e2) _ "%inc" _
                ((lookupName_cons_ne _ _ (by decide)).trans hinc2))
            ((hfr2 "%ent" (by decide)).trans ((hframe e1 hrun1 "%ent" (by decide)).trans hent))
            ((hfr2 "%blk0" (by decide)).trans ((hframe e1 hrun1 "%blk0" (by decide)).trans hbk))
            ((hfr2 "%nblk" (by decide)).trans ((hframe e1 hrun1 "%nblk" (by decide)).trans hNb))
            ((hfr2 "%out" (by decide)).trans ((hframe e1 hrun1 "%out" (by decide)).trans hout))
            ((hfr2 "%tab" (by decide)).trans ((hframe e1 hrun1 "%tab" (by decide)).trans htab))
            hkNext hmemNext
        refine ⟨e3, mem3, ?_, hmem3⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        rw [hfuel]
        rw [runFuel_jump hstep1, runFuel_jump hstep2]
        exact runFuel_mono_le (show 3 * r' + 1 ≤ (3 * r' + 1) + 1 from Nat.le_succ _) hrun3
    · -- the word is not zero: the group stores run, then `cleanup`
      have hwne : ent[i] ≠ 0 := hw
      have hk63'' : k0 + 64 * nblk + 9 < 2 ^ 63 := by rw [hnblk]; exact hk63
      have hk63' : k + 64 ≤ 2 ^ 63 := by
        have h64 := groups_hk63_of_hk63 k0 nblk hnblkpos hk63''
        omega
      have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
        have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
          have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
          calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
            _ ≤ 64 * (blk0 + nblk) := by omega
        rw [posBase_eq]
        omega
      have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
          = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
      have hdisjT'' : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ tab := by
        rw [hnblk]; exact hdisjT
      have hdisjT' : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop (ent[i]) + 8) ≤ tab :=
        table_disj_of_hdisj o tab k k0 nblk (ctpop (ent[i]))
          (by have := ctpop_le (ent[i]); omega) hdisjT''
      obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
        pos8Body_step_pos env s (ent[i]) i k e p opk opi hpc hpre hopk hopi hvk hvi hent
          hword hi63 hwne
      have hfr1 := fun (n : String) (hn : n ∈ pos8Params) =>
        (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body n hn)
      obtain ⟨e2, hrun2, hstep2, hpar2, hi010, hadd1⟩ :=
        pos8Groups_step e1 { s with pc := "if.end", pre := some "for.body" } (ent[i]) i blk0 k o tab
          (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem) rfl rfl
          hi1 ((hfr1 "%blk0" (by decide)).trans hbk) ((hfr1 "%out" (by decide)).trans hout)
          hk1 h01 ((hfr1 "%tab" (by decide)).trans htab) hk63' hblk' hconv htabread hdisjT'
      have hfr2 := fun (n : String) (hn : n ∈ pos8Params) => hpar2 n hn
      have hc64 : ctpop (ent[i]) + k < 2 ^ 64 := by
        have h1 := ctpop_le (ent[i])
        omega
      have hsum : BitVec.ofNat 64 (ctpop (ent[i])) + BitVec.ofNat 64 k
          = BitVec.ofNat 64 (k + ctpop (ent[i])) := by
        rw [ofNat64_add_ofNat (ctpop (ent[i])) k hc64, Nat.add_comm]
      have hi1' : lookupName e2 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
        hi010.trans hi1
      have hNb2 : lookupName e2 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
        (hpar2 "%nblk" (by decide)).trans ((hfr1 "%nblk" (by decide)).trans hNb)
      by_cases hlast : i + 1 = nblk
      · obtain ⟨e3, hrun3, hstep3, hk3, hinc3, hx3⟩ :=
          pos8Cleanup_step_last e2
            { s with mem := (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" }
            i (k + ctpop (ent[i])) nblk "if.end" (.reg "%add1") rfl rfl rfl
            (by rw [← hsum]; exact evalOperand_reg_of e2 _ _ _ hadd1) hi1' hNb2 hi64
            (hxeq.mpr hlast)
        obtain ⟨e4, hstep4, hk4⟩ :=
          pos8Exit_step e3
            { s with mem := (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem), pc := "for.cond.cleanup", pre := some "cleanup" }
            (k + ctpop (ent[i])) "cleanup" (.reg "%k.addr.1") rfl rfl rfl
            (evalOperand_reg_of e3 _ _ _ hk3)
        refine ⟨e4, blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem, ?_, ?_⟩
        · rw [pos8Cursor_drop_succ ent k i hilen]
          have hdrop : ent.drop (i + 1) = [] := by rw [hlast, hnblk, List.drop_length]
          rw [hdrop]
          rw [hfuel]
          rw [runFuel_jump hstep1, runFuel_jump hstep2, runFuel_jump hstep3, runFuel_ret hstep4]
          simp only [withEnv]
          rfl
        · have hmem' : blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem
              = pos8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 := by
            rw [hmem, pos8MemFold_succ ent blk0 k0 o i mem0 hilen, hk,
              blockStore_of_ne o (ent[i]) (posBase blk0 i) (pos8Cursor (ent.take i) k0) _ hwne]
          have hE : pos8MemFold o (64 * blk0) k0 ent mem0
              = pos8MemFold o (64 * blk0) k0 (ent.take (i + 1)) mem0 :=
            congrArg (fun l => pos8MemFold o (64 * blk0) k0 l mem0) (hent_eq hlast)
          rw [hE, hmem']
      · obtain ⟨e3, hrun3, hstep3, hk3, hinc3, hx3⟩ :=
          pos8Cleanup_step_more e2
            { s with mem := (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" }
            i (k + ctpop (ent[i])) nblk "if.end" (.reg "%add1") rfl rfl rfl
            (by rw [← hsum]; exact evalOperand_reg_of e2 _ _ _ hadd1) hi1' hNb2 hi64
            (fun hcon => hlast (hxeq.mp hcon))
        have hfr3 := fun (n : String) (hn : n ∈ pos8Params) =>
          (denoteCode_params pos8Advance.instrs e2 e3
            { s with mem := (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" } hrun3 pos8Params_cleanup n hn)
        obtain ⟨e4, mem4, hrun4, hmem4⟩ :=
          ih (i + 1) (k + ctpop (ent[i])) e3
            { s with mem := (blockMem o (ent[i]) (posBase blk0 i) k 8 s.mem), pc := "for.body", pre := some "cleanup" } "cleanup"
            (.reg "%k.addr.1") (.reg "%inc")
            (by omega) (by omega) rfl rfl rfl rfl
            (evalOperand_reg_of e3 _ _ _ hk3)
            (evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop (ent[i])))) :: e3)
              _ "%inc" _ ((lookupName_cons_ne _ _ (by decide)).trans hinc3))
            ((hfr3 "%ent" (by decide)).trans ((hfr2 "%ent" (by decide)).trans
              ((hfr1 "%ent" (by decide)).trans hent)))
            ((hfr3 "%blk0" (by decide)).trans ((hfr2 "%blk0" (by decide)).trans
              ((hfr1 "%blk0" (by decide)).trans hbk)))
            ((hfr3 "%nblk" (by decide)).trans ((hfr2 "%nblk" (by decide)).trans
              ((hfr1 "%nblk" (by decide)).trans hNb)))
            ((hfr3 "%out" (by decide)).trans ((hfr2 "%out" (by decide)).trans
              ((hfr1 "%out" (by decide)).trans hout)))
            ((hfr3 "%tab" (by decide)).trans ((hfr2 "%tab" (by decide)).trans
              ((hfr1 "%tab" (by decide)).trans htab)))
            (by rw [hk]; exact (pos8Cursor_take_succ ent k0 i hilen).symm)
            (by rw [hmem, pos8MemFold_succ ent blk0 k0 o i mem0 hilen, hk,
              blockStore_of_ne o (ent[i]) (posBase blk0 i) (pos8Cursor (ent.take i) k0) _ hwne])
        refine ⟨e4, mem4, ?_, hmem4⟩
        rw [pos8Cursor_drop_succ ent k i hilen]
        rw [hfuel]
        rw [runFuel_jump hstep1, runFuel_jump hstep2, runFuel_jump hstep3]
        simpa only [withEnv] using hrun4

/-! ### The headline theorem -/

/-- `ret` carries the memory and nothing else, so two runs that agree on the
returned cursor can be compared at the memory. -/
theorem pos8_init_env :
    (initState entryPos8Function [.ptr (0:Nat), .int 64 0, .int 64 0, .ptr 0,
      .int 64 0, .ptr 0]).env =
      [("%ent", .ptr (0:Nat)), ("%blk0", .int 64 (0 : BitVec 64)),
       ("%nblk", .int 64 (0 : BitVec 64)), ("%out", .ptr (0:Nat)),
       ("%k", .int 64 (0 : BitVec 64)), ("%tab", .ptr (0:Nat))] := rfl

/-- The initial state's five parameter cells and its block. -/
theorem pos8_init (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab : Nat) :
    let S0 : State := { (initState entryPos8Function
      [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
    S0.pc = "entry" ∧
      lookupName S0.env "%ent" = some (.ptr e) ∧
      lookupName S0.env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) ∧
      lookupName S0.env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) ∧
      lookupName S0.env "%out" = some (.ptr o) ∧
      lookupName S0.env "%k" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName S0.env "%tab" = some (.ptr tab) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [initState, entryPos8Function, pos8Entry, pos8LoopExit, pos8Body, pos8Groups,
      pos8Advance, List.zip, List.map, lookupName]

theorem readBytes_one (m : Mem) (a : Nat) :
    readBytes m a 1 = (readByte m a).map (fun b => [b]) := by
  unfold readBytes
  cases readByte m a with
  | none => rfl
  | some b => rfl

theorem readByte_congr_of_readBytes_one (m m' : Mem) (a : Nat)
    (h : readBytes m' a 1 = readBytes m a 1) : readByte m' a = readByte m a := by
  rw [readBytes_one, readBytes_one] at h
  cases hb : readByte m' a with
  | none =>
      cases hb2 : readByte m a with
      | none => rfl
      | some c => rw [hb, hb2] at h; simp at h
  | some b =>
      cases hb2 : readByte m a with
      | none => rw [hb, hb2] at h; simp at h
      | some c => rw [hb, hb2] at h; simpa using h

theorem entry_pos8_refines (ent : List (BitVec 64)) (blk0 nblk k : Nat) (mem : Mem)
    (e o tab outCap : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hent : readBytes mem e (8 * ent.length) = some (wordsOf ent))
    (htab : readBytes mem tab 8192 = some pos8Table)
    (hdisj : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
             (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hcap : k + 64 * ent.length + 9 ≤ outCap)
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    ∃ (k' : Nat) (mem' : Mem),
      runFuel entryCalls (3 * nblk + 3) entryPos8Function
        { (initState entryPos8Function
            [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
          = some (.ret (some (.int 64 (BitVec.ofNat 64 k'))) mem') ∧
      k' = k + (ent.map ctpop).sum ∧
      readLanes32 mem' (o + 4 * k) (k' - k) = streamPrefix ent blk0 nblk ∧
      (∀ a, a < o ∨ o + 4 * (k' + 8) ≤ a → readByte mem' a = readByte mem a) := by
  let S0 : State := { (initState entryPos8Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0, htab0⟩ := pos8_init ent blk0 nblk k mem e o tab
  by_cases hz : nblk = 0
  · -- no block runs: the entry test branches straight to `for.cond.cleanup`
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      pos8Entry_step_zero S0.env S0 nblk hpc0 hNb hz
    have hk1 : lookupName e1 "%k" = some (.int 64 (BitVec.ofNat 64 k)) :=
      (denoteCode_params pos8Entry.instrs S0.env e1 S0 hrun1 (by decide)
        "%k" (by decide)).trans hk0
    obtain ⟨e2, hstep2, hk2⟩ :=
      pos8Exit_step e1 { S0 with pc := "for.cond.cleanup", pre := some "entry" } k
        "entry" (.reg "%k") rfl rfl rfl (evalOperand_reg_of e1 _ _ _ hk1)
    refine ⟨k, mem, ?_, ?_, ?_, ?_⟩
    · show runFuel entryCalls (3 * nblk + 2 + 1) entryPos8Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 k))) mem)
      rw [runFuel_jump hstep1, runFuel_ret hstep2]
      rfl
    · subst hz
      have he : ent = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst he
      simp
    · subst hz
      have he : ent = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst he
      simp [streamPrefix, List.take, readLanes32]
    · intro a ha
      rfl
  · -- the loop runs: `entry` falls into `for.body` with the parameter cells
    have hpos : 1 ≤ nblk := by omega
    obtain ⟨e1, hrun1, hstep1, hnot⟩ :=
      pos8Entry_step_pos S0.env S0 nblk hpc0 hNb (by omega) hz
    have hfr := fun (n : String) (hn : n ∈ pos8Params) =>
      (denoteCode_params pos8Entry.instrs S0.env e1 S0 hrun1 (by decide) n hn)
    obtain ⟨e2, mem2, hrun2, hmem2⟩ :=
      pos8_loop_run ent blk0 nblk k o tab e mem hent htab hblk hk63 hdisj.1 hdisj.2 hnblk
        nblk 0 k e1 { S0 with pc := "for.body", pre := some "entry" }
        "entry" (.reg "%k") (lit 64 0)
        hpos (by omega) rfl rfl rfl rfl
        (evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
        (by
          show evalOperand _ (.imm (.int 64 (BitVec.ofInt 64 0))) = some (.int 64 (BitVec.ofNat 64 0))
          rw [ofInt64_zero]
          rfl)
        ((hfr "%ent" (by decide)).trans hent0)
        ((hfr "%blk0" (by decide)).trans hblk0)
        ((hfr "%nblk" (by decide)).trans hNb)
        ((hfr "%out" (by decide)).trans hout0)
        ((hfr "%tab" (by decide)).trans htab0)
        rfl
        rfl
    refine ⟨pos8Cursor ent k, mem2, ?_, ?_, ?_, ?_⟩
    · -- the run: one entry step, then the loop at `3 * nblk + 2`
      show runFuel entryCalls (3 * nblk + 2 + 1) entryPos8Function (withEnv S0.env S0)
        = some (.ret (some (.int 64 (BitVec.ofNat 64 (pos8Cursor ent k)))) mem2)
      rw [runFuel_jump hstep1]
      exact runFuel_mono_le (show 3 * nblk + 1 ≤ 3 * nblk + 2 from by omega) hrun2
    · -- the count
      rw [pos8Cursor_eq_sum]
    · -- the words
      rw [hmem2, pos8MemFold_read]
      rw [pos8Stream_eq_positions ent (64 * blk0) (by omega)]
      rw [pos8Stream_eq_streamPrefix, hnblk]
    · -- the frame
      intro a ha
      rw [hmem2]
      exact readByte_congr_of_readBytes_one _ _ a
        (pos8MemFold_frame (o := o) (base := 64 * blk0) (k := k) (ent := ent)
          (mem := mem) a 1 (by
            rcases ha with h | h
            · left; omega
            · right; exact h))

theorem denoteCode_cons_none (calls : Calls) (i : Instr) (is : List Instr) (s : State)
    (h : evalInstr calls s i = none) : denoteCode calls (i :: is) s = none := by
  simp only [denoteCode, h]

theorem loadValue_i64_none {m : Mem} {a : Nat} (h : readBytes m a 8 = none) :
    loadValue m (.int 64) a = none := by
  simp [loadValue, h]

theorem evalInstr_load_none {calls : Calls} {s : State} {d : String} {ty : Ty} {p : Operand}
    {a : Nat} (hp : evalOperand s p = some (.ptr a)) (hv : loadValue s.mem ty a = none) :
    evalInstr calls s (.load d ty p) = none := by
  simp [evalInstr, hp, hv]

theorem runFuel_of_step_ub {f : Function} {s : State} {n : Nat}
    (h : step entryCalls f s = .ub) : runFuel entryCalls (n + 1) f s = some .ub := by
  simp [runFuel, h]

/-- The body's run is `ub` when its mask word is unreadable: the two `phi`s and
the address run, and the load is the instruction that fails. -/
theorem pos8Body_denote_none (env : Env) (s : State) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hi63 : i < 2 ^ 63)
    (hno : readBytes s.mem (e + 8 * i) 8 = none) :
    denoteCode entryCalls pos8Body.instrs (withEnv env s) = none := by
  simp only [pos8Body, reg, lit, pos8IncomingK, pos8IncomingI]
  have hopk' : phiIncoming p
      [("cleanup", Operand.reg "%k.addr.1"), ("entry", Operand.reg "%k")] = some opk := hopk
  have hopi' : phiIncoming p
      [("cleanup", Operand.reg "%inc"),
       ("entry", Operand.imm (Const.int 64 (BitVec.ofInt 64 0)))] = some opi := hopi
  ent_step (phi_step env s "%k.addr.011" (.int 64) _ p opk _ hpre hopk' hvk)
  ent_step (phi_step (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s
    "%i.010" (.int 64) _ p opi _ hpre hopi' hvi)
  ent_step (step_gep64 _ _ "%arrayidx" "%ent" "%i.010" (.int 64) e (BitVec.ofNat 64 i)
    (by ent_auto) (by ent_auto)
    (by rw [toNat_ofNat64 i (by omega)]; omega))
  rw [show e + (BitVec.ofNat 64 i).toNat * (Ty.int 64).sizeBytes = e + 8 * i from by
    rw [toNat_ofNat64 i (by omega), show (Ty.int 64).sizeBytes = 8 from rfl]
    omega]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx") (hp := by ent_auto) (hv := loadValue_i64_none hno))

theorem step_ub_pos8 (s : State) (name : String) (b : Block)
    (hpc : s.pc = name) (hfind : entryPos8Function.findBlock name = some b)
    (hbody : denoteCode entryCalls b.instrs s = none) :
    step entryCalls entryPos8Function s = .ub := by
  simp [step, hpc, hfind, hbody]

/-- The body is `ub`: one step of the loop's body, at the fuel a single block
costs. -/
theorem pos8Body_ub_of_no_read (env : Env) (s : State) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hi63 : i < 2 ^ 63)
    (hno : readBytes s.mem (e + 8 * i) 8 = none) :
    runFuel entryCalls 2 entryPos8Function (withEnv env s) = some .ub := by
  have hden := pos8Body_denote_none env s i k e p opk opi hpre hopk hopi hvk hvi hent hi63 hno
  exact runFuel_of_step_ub (n := 1) (step_ub_pos8 (withEnv env s) "for.body" pos8Body hpc
    findBlock_pos8Body hden)

/-! ### The same for B8 -/

theorem findBlock_b8Body :
    entryB8Function.findBlock "for.body" = some b8Body := by
  simp [entryB8Function, b8Entry, b8LoopExit, b8Body, b8Kernel, b8TailGuard, b8TailPreheader,
    b8TailUnrolled, b8TailLoop, b8TailRemainderGuard, b8TailRemainder, b8Join, b8Advance,
    Function.findBlock, findBlockList]

theorem step_ub_b8 (s : State) (name : String) (b : Block)
    (hpc : s.pc = name) (hfind : entryB8Function.findBlock name = some b)
    (hbody : denoteCode entryCalls b.instrs s = none) :
    step entryCalls entryB8Function s = .ub := by
  simp [step, hpc, hfind, hbody]

/-- B8's body block is the entry body's text, so the same failing load is the
same `ub`; only the function the step is taken in differs. -/
theorem b8Body_ub_of_no_read (env : Env) (s : State) (i k e : Nat) (p : String)
    (opk opi : Operand)
    (hpc : s.pc = "for.body")
    (hpre : s.pre = some p)
    (hopk : phiIncoming p pos8IncomingK = some opk)
    (hopi : phiIncoming p pos8IncomingI = some opi)
    (hvk : evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)))
    (hvi : evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
            = some (.int 64 (BitVec.ofNat 64 i)))
    (hent : lookupName env "%ent" = some (.ptr e))
    (hi63 : i < 2 ^ 63)
    (hno : readBytes s.mem (e + 8 * i) 8 = none) :
    runFuel entryCalls 2 entryB8Function (withEnv env s) = some .ub := by
  have hden := pos8Body_denote_none env s i k e p opk opi hpre hopk hopi hvk hvi hent hi63 hno
  exact runFuel_of_step_ub (n := 1) (step_ub_b8 (withEnv env s) "for.body" b8Body hpc
    findBlock_b8Body hden)

/-! ### The read's own bytes -/

/-- A byte list of a word's width is the encoding of the value it denotes. -/
theorem natToBytes_bytesToNat (bs : List UInt8) :
    natToBytes (bytesToNat bs) bs.length = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih =>
      show UInt8.ofNat ((b.toNat + 256 * bytesToNat rest) % 256) ::
        natToBytes ((b.toNat + 256 * bytesToNat rest) / 256) rest.length = b :: rest
      have hlt : b.toNat < 256 := by simpa using UInt8.toNat_lt b
      have hmod : (b.toNat + 256 * bytesToNat rest) % 256 = b.toNat := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      have hdiv : (b.toNat + 256 * bytesToNat rest) / 256 = bytesToNat rest := by
        rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt hlt, Nat.zero_add]
      rw [hmod, hdiv, ih, UInt8.ofNat_toNat]

/-- A successful read returns as many bytes as it asks for. -/
theorem readBytes_length (m : Mem) (a : Nat) : ∀ (n : Nat) {bs : List UInt8},
    readBytes m a n = some bs → bs.length = n
  | 0, bs, h => by
      rw [show readBytes m a 0 = some [] from rfl] at h
      rw [Option.some.injEq] at h
      subst h
      rfl
  | n + 1, bs, h => by
      unfold readBytes at h
      cases hb : readByte m a with
      | none => rw [hb] at h; cases h
      | some b =>
          rw [hb] at h
          cases hr : readBytes m (a + 1) n with
          | none => rw [hr] at h; cases h
          | some bs' =>
              rw [hr] at h
              rw [Option.some.injEq] at h
              subst h
              rw [List.length_cons, readBytes_length m (a + 1) n hr]

/-- The memory a state update sets, read back.  Stated with the fields as
variables so that applying it never unfolds the value: the value is a `blockMem`
fold, and reducing that is work the elaboration order should not do. -/
theorem state_mem_update_pc (s : State) (m : Mem) (pc : String) (pre : Option String) :
    ({ s with mem := m, pc := pc, pre := pre } : State).mem = m := rfl

/-- A successful eight-byte read names the word it read. -/
theorem natToBytes_of_readBytes_eight (m : Mem) (a : Nat) (bs : List UInt8)
    (h : readBytes m a 8 = some bs) :
    natToBytes (BitVec.ofNat 64 (bytesToNat bs)).toNat 8 = bs := by
  have hlen : bs.length = 8 := readBytes_length m a 8 h
  have hlt : bytesToNat bs < 2 ^ 64 := by
    have h1 := bytesToNat_lt bs
    rw [hlen] at h1
    rw [show (256 : Nat) ^ 8 = 2 ^ 64 from by decide] at h1
    exact h1
  rw [toNat_ofNat64 _ hlt, ← hlen]
  exact natToBytes_bytesToNat bs

/-! ### The loop, when a word is unreadable -/

/-- From a loop state with `r` blocks left before the failing one, if the memory's
mask word at block `jj` is unreadable the run is `ub`: each earlier block's body
steps and the successor state is handed on, and the frame carries the unreadable
word and the table's readability past every store, because a block's writes stay
inside the output span. -/
theorem pos8_loop_run_ub (blk0 nblk k0 o tab e : Nat) (jj : Nat)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * nblk + 9 < 2 ^ 63)
    (hdisjE : e + 8 * nblk ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ e)
    (hdisjT : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ tab)
    (hj : jj < nblk) :
    ∀ (r i k : Nat) (mem : Mem) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = jj + 1 →
      s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName env "%ent" = some (.ptr e) →
      lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) →
      lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) →
      lookupName env "%out" = some (.ptr o) →
      lookupName env "%tab" = some (.ptr tab) →
      s.mem = mem →
      k ≤ k0 + 64 * i →
      readBytes mem (e + 8 * jj) 8 = none →
      readBytes mem tab 8192 = some pos8Table →
      runFuel entryCalls (3 * r + 1) entryPos8Function (withEnv env s) = some .ub := by
  intro r
  induction r with
  | zero => intro i k mem env s p opk opi hr; exact absurd hr (by omega)
  | succ r' ih =>
    intro i k mem env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hent hbk hNb hout htab hsm hkb hfailS htabS
    have hinl : i < nblk := by omega
    have hn63 : nblk < 2 ^ 63 := by
      have h1 : 64 * nblk < 2 ^ 63 := by omega
      have h2 : 64 * nblk < 64 * 2 ^ 57 := by
        rw [show 64 * 2 ^ 57 = 2 ^ 63 from by decide]
        exact h1
      have h3 : nblk < 2 ^ 57 := Nat.lt_of_mul_lt_mul_left h2
      omega
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hnb64 : nblk < 2 ^ 64 := by omega
    have hfuel : 3 * (r' + 1) + 1 = (((3 * r' + 1) + 1) + 1) + 1 := by omega
    by_cases hnow : i = jj
    · -- the failing block is this one
      have hno : readBytes s.mem (e + 8 * i) 8 = none := by
        rw [hsm, hnow]
        exact hfailS
      exact runFuel_mono_le (show 2 ≤ 3 * (r' + 1) + 1 from by omega)
        (pos8Body_ub_of_no_read env s i k e p opk opi hpc hpre hopk hopi hvk hvi hent hi63 hno)
    · have hlt : i < jj := by omega
      have hr2 : 1 ≤ r' := by omega
      have hne : i + 1 ≠ nblk := by omega
      have hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk := fun hcon =>
        hne (ofNat64_inj (by omega) hnb64 hcon)
      cases hrd : readBytes s.mem (e + 8 * i) 8 with
      | none =>
          exact runFuel_mono_le (show 2 ≤ 3 * (r' + 1) + 1 from by omega)
            (pos8Body_ub_of_no_read env s i k e p opk opi hpc hpre hopk hopi hvk hvi hent hi63 hrd)
      | some bs =>
          obtain ⟨w, hwdef⟩ : ∃ w : BitVec 64, natToBytes w.toNat 8 = bs :=
            ⟨BitVec.ofNat 64 (bytesToNat bs), natToBytes_of_readBytes_eight s.mem (e + 8 * i) bs hrd⟩
          have hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8) := by
            rw [hwdef]; exact hrd
          by_cases hw : w = 0
          · -- the block emits nothing: `cleanup` and the next block
            obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
              pos8Body_step_zero env s w i k e p opk opi hpc hpre
                hopk hopi hvk hvi hent hread hi63 hw
            have hNb1 : lookupName e1 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%nblk"
                (by decide)).trans hNb
            obtain ⟨e2, hrun2, hstep2, hk2, hinc2, hx2⟩ :=
              pos8Cleanup_step_more e1 { s with pc := "cleanup", pre := some "for.body" } i k nblk
                "for.body" (.reg "%k.addr.011") rfl rfl rfl
                (evalOperand_reg_of e1 _ _ _ hk1) hi1 hNb1 hi64 hx
            have hfr2 := fun (n : String) (hn : n ∈ pos8Params) =>
              (denoteCode_params pos8Advance.instrs e1 e2
                { s with pc := "cleanup", pre := some "for.body" } hrun2 pos8Params_cleanup n hn)
            have hb1' : lookupName e1 "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%blk0"
                (by decide)).trans hbk
            have hout1 : lookupName e1 "%out" = some (.ptr o) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%out"
                (by decide)).trans hout
            have htab1 : lookupName e1 "%tab" = some (.ptr tab) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%tab"
                (by decide)).trans htab
            have hent1 : lookupName e1 "%ent" = some (.ptr e) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%ent"
                (by decide)).trans hent
            obtain hrec :=
              ih (i + 1) k mem e2 { s with pc := "for.body", pre := some "cleanup" } "cleanup"
                (.reg "%k.addr.1") (.reg "%inc") hr2 (by omega) rfl rfl rfl rfl
                (evalOperand_reg_of e2 _ _ _ hk2)
                (evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: e2) _ "%inc" _
                  ((lookupName_cons_ne _ _ (by decide)).trans hinc2))
                ((hfr2 "%ent" (by decide)).trans hent1)
                ((hfr2 "%blk0" (by decide)).trans hb1')
                ((hfr2 "%nblk" (by decide)).trans hNb1)
                ((hfr2 "%out" (by decide)).trans hout1)
                ((hfr2 "%tab" (by decide)).trans htab1)
                hsm (by omega) hfailS htabS
            rw [hfuel]
            rw [runFuel_jump hstep1]
            rw [runFuel_jump hstep2]
            exact runFuel_mono_le (show 3 * r' + 1 ≤ (3 * r' + 1) + 1 from Nat.le_succ _) hrec
          · -- the block emits: the group stores, then `cleanup`
            have hwne : w ≠ 0 := hw
            have hk63' : k + 64 ≤ 2 ^ 63 := by
              have := ctpop_le w
              omega
            have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
              have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
                have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
                calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
                  _ ≤ 64 * (blk0 + nblk) := by omega
              rw [posBase_eq]
              omega
            have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
                = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
            have hdisjT' : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab :=
              table_disj_of_hdisj o tab k k0 nblk (ctpop w)
                (by have := ctpop_le w; omega) hdisjT
            have htabS' : readBytes s.mem tab 8192 = some pos8Table := by
              rw [hsm]; exact htabS
            obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
              pos8Body_step_pos env s w i k e p opk opi hpc hpre
                hopk hopi hvk hvi hent hread hi63 hwne
            have hfr1 := fun (n : String) (hn : n ∈ pos8Params) =>
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body n hn)
            obtain ⟨e2, hrun2, hstep2, hpar2, hi010, hadd1⟩ :=
              pos8Groups_step e1 { s with pc := "if.end", pre := some "for.body" } w i blk0 k o tab
                (blockMem o w (posBase blk0 i) k 8 s.mem) rfl rfl
                hi1 ((hfr1 "%blk0" (by decide)).trans hbk) ((hfr1 "%out" (by decide)).trans hout)
                hk1 h01 ((hfr1 "%tab" (by decide)).trans htab) hk63' hblk' hconv htabS' hdisjT'
            have hfr2 := fun (n : String) (hn : n ∈ pos8Params) => hpar2 n hn
            have hc64 : ctpop w + k < 2 ^ 64 := by
              have := ctpop_le w
              omega
            have hsum : BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k
                = BitVec.ofNat 64 (k + ctpop w) := by
              rw [ofNat64_add_ofNat _ _ hc64, Nat.add_comm]
            have hi1' : lookupName e2 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
              hi010.trans hi1
            have hNb2 : lookupName e2 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
              (hpar2 "%nblk" (by decide)).trans ((hfr1 "%nblk" (by decide)).trans hNb)
            obtain ⟨e3, hrun3, hstep3, hk3, hinc3, hx3⟩ :=
              pos8Cleanup_step_more e2 { s with mem := (blockMem o w (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" }
                i (k + ctpop w) nblk "if.end" (.reg "%add1") rfl rfl rfl
                (by rw [← hsum]; exact evalOperand_reg_of e2 _ _ _ hadd1) hi1' hNb2 hi64 hx
            have hfr3 := fun (n : String) (hn : n ∈ pos8Params) =>
              (denoteCode_params pos8Advance.instrs e2 e3
                { s with mem := (blockMem o w (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" } hrun3 pos8Params_cleanup n hn)
            have hcanon : blockMem o w (posBase blk0 i) k 8 s.mem
                = blockStore o w (posBase blk0 i) k s.mem :=
              (blockStore_of_ne o w (posBase blk0 i) k s.mem hwne).symm
            have hfailNext : readBytes (blockMem o w (posBase blk0 i) k 8 s.mem)
                (e + 8 * jj) 8 = none := by
              rw [hcanon, blockStore_frame o w (posBase blk0 i) k s.mem (e + 8 * jj) 8 ?_]
              rw [hsm]
              exact hfailS
              rcases hdisjE with h | h
              · left; omega
              · right
                have := ctpop_le w
                omega
            have htabNext : readBytes (blockMem o w (posBase blk0 i) k 8 s.mem) tab 8192
                = some pos8Table := by
              rw [hcanon, blockStore_frame o w (posBase blk0 i) k s.mem tab 8192 ?_]
              exact htabS'
              rcases hdisjT with h | h
              · left; omega
              · right
                have := ctpop_le w
                omega
            have hs2 := state_mem_update_pc s (blockMem o w (posBase blk0 i) k 8 s.mem)
              "for.body" (some "cleanup")
            have hkb2 : k + ctpop w ≤ k0 + 64 * (i + 1) := by
              have := ctpop_le w
              omega
            obtain hrec :=
              ih (i + 1) (k + ctpop w) (blockMem o w (posBase blk0 i) k 8 s.mem) e3
                { s with mem := (blockMem o w (posBase blk0 i) k 8 s.mem), pc := "for.body", pre := some "cleanup" } "cleanup"
                (.reg "%k.addr.1") (.reg "%inc") hr2 (by omega) rfl rfl rfl rfl
                (evalOperand_reg_of e3 _ _ _ hk3)
                (evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop w))) :: e3)
                  _ "%inc" _ ((lookupName_cons_ne _ _ (by decide)).trans hinc3))
                ((hfr3 "%ent" (by decide)).trans ((hfr2 "%ent" (by decide)).trans
                  ((hfr1 "%ent" (by decide)).trans hent)))
                ((hfr3 "%blk0" (by decide)).trans ((hfr2 "%blk0" (by decide)).trans
                  ((hfr1 "%blk0" (by decide)).trans hbk)))
                ((hfr3 "%nblk" (by decide)).trans ((hfr2 "%nblk" (by decide)).trans
                  ((hfr1 "%nblk" (by decide)).trans hNb)))
                ((hfr3 "%out" (by decide)).trans ((hfr2 "%out" (by decide)).trans
                  ((hfr1 "%out" (by decide)).trans hout)))
                ((hfr3 "%tab" (by decide)).trans ((hfr2 "%tab" (by decide)).trans
                  ((hfr1 "%tab" (by decide)).trans htab)))
                hs2 hkb2 hfailNext htabNext
            rw [hfuel]
            rw [runFuel_jump hstep1]
            rw [runFuel_jump hstep2]
            rw [runFuel_jump hstep3]
            simpa only [withEnv] using hrec

/-! ### The companion -/

/-- An unreadable mask word makes the whole run `ub`: block `j`'s load is the
instruction that fails, and the failure survives the earlier blocks' stores
because the output span is disjoint from the word's address.

The table is required readable, which the group stores already take as their
hypothesis; a block whose row is unreadable is not covered here — see
`entry_pos8_undefined_of_no_row` for that class. -/
theorem entry_pos8_undefined_of_no_read (ent : List (BitVec 64)) (blk0 nblk k : Nat)
    (mem : Mem) (e o tab j : Nat)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hj : j < nblk)
    (hno : readBytes (pos8MemFold o (64 * blk0) k (ent.take j) mem) (e + 8 * j) 8 = none)
    (hrows : readBytes mem tab 8192 = some pos8Table)
    (hdisj : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
             (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    runFuel entryCalls (3 * nblk + 3) entryPos8Function
      { (initState entryPos8Function
          [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
        = some .ub := by
  let S0 : State := { (initState entryPos8Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0, htab0⟩ := pos8_init ent blk0 nblk k mem e o tab
  have hz : nblk ≠ 0 := by omega
  have hnb64 : nblk < 2 ^ 64 := by omega
  have hfrFold : readBytes (pos8MemFold o (64 * blk0) k (ent.take j) mem) (e + 8 * j) 8
      = readBytes mem (e + 8 * j) 8 :=
    pos8MemFold_frame (o := o) (base := 64 * blk0) (k := k) (ent := ent.take j) (mem := mem)
      (e + 8 * j) 8 (by
        rcases hdisj.1 with h | h
        · left; omega
        · right
          have hc : pos8Cursor (ent.take j) k ≤ k + 64 * j := by
            have h1 := pos8Cursor_le (ent.take j) k
            rwa [pos8_take_length ent j (by omega)] at h1
          omega)
  have hfail0 : readBytes mem (e + 8 * j) 8 = none := by rw [← hfrFold]; exact hno
  obtain ⟨e1, hrun1, hstep1, _⟩ := pos8Entry_step_pos S0.env S0 nblk hpc0 hNb hnb64 hz
  have hfr := fun (n : String) (hn : n ∈ pos8Params) =>
    (denoteCode_params pos8Entry.instrs S0.env e1 S0 hrun1 (by decide) n hn)
  obtain hrun :=
    pos8_loop_run_ub blk0 nblk k o tab e j hblk (by rw [hnblk]; exact hk63)
      (by rw [hnblk]; exact hdisj.1) (by rw [hnblk]; exact hdisj.2) hj
      (j + 1) 0 k mem e1 { S0 with pc := "for.body", pre := some "entry" } "entry" (.reg "%k") (lit 64 0)
      (by omega) (by omega) rfl rfl rfl rfl
      (evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
      (by
        show evalOperand _ (.imm (.int 64 (BitVec.ofInt 64 0)))
          = some (.int 64 (BitVec.ofNat 64 0))
        rw [ofInt64_zero]
        rfl)
      ((hfr "%ent" (by decide)).trans hent0)
      ((hfr "%blk0" (by decide)).trans hblk0)
      ((hfr "%nblk" (by decide)).trans hNb)
      ((hfr "%out" (by decide)).trans hout0)
      ((hfr "%tab" (by decide)).trans htab0)
      rfl (by omega) hfail0 hrows
  show runFuel entryCalls (3 * nblk + 2 + 1) entryPos8Function (withEnv S0.env S0) = some .ub
  rw [runFuel_jump hstep1]
  exact runFuel_mono_le (show 3 * (j + 1) + 1 ≤ 3 * nblk + 2 from by omega) hrun

/-! ### The row half: a group whose row is unreadable

The runners above take the whole table's readability (`readBytes s.mem tab 8192 =
some pos8Table`) and derive each row load from it — `pos8Table_row_read` is that
derivation.  A block whose *row* is unreadable cannot be described that way, so
the eight runners are restated against the load's own premise: the `_row`
variants differ from their originals in that single hypothesis, and the
`_none_row` variants are the same instruction prefix stopped where that load
fails.  `blockMem_read_row` carries a row past the block's group stores,
`pos8Groups_run_row` and `pos8Groups_ub_of_row` compose the variants,
`pos8_loop_run_row_ub` walks the loop to the unreadable row, and
`entry_pos8_undefined_of_no_row` is the companion's table-row half — the mirror
of `entry_pos8_undefined_of_no_read`, which carries the table readable where this
one carries it readable in every row but the failing one.
-/

/-- A table row lies outside the block's writes: a read of it is the same after
any number of group stores, at the frame end the stores have. -/
theorem blockMem_read_row (o : Nat) (w : BitVec 64) (base k : Nat) (mem : Mem)
    (tab m : Nat) (hm : m < 256)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    ∀ j, j ≤ 8 →
      readBytes (blockMem o w base k j mem) (tab + m * 32) 32
        = readBytes mem (tab + m * 32) 32
  | j, hj => by
      rw [blockMem_frame_tight o w base k mem (tab + m * 32) 32 (by
        rcases hdisj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)) j hj]

/-- The head group at its own row: `pos8Head_run` with the whole table's
readability replaced by the one row this group loads.  The seven group lemmas
below are that same substitution — one premise, and nothing else, differs from
their originals. -/
theorem pos8Head_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hrowread : readBytes s.mem (tab + byteOf w 0 * 32) 32 = some (pos8RowBytes (byteOf w 0))) :
    ∃ env', denoteCode entryCalls pos8Head (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.i" = some (.ptr (o + 4 * groupCursor w k 1)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr⟩
  case hrun =>
    simp only [pos8Head, reg, lit, zero8, splatLane0]
    ent_step (step_add_reg _ _ "%add" "%i.010" "%blk0" 64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 blk0) (by ent_auto) (by ent_auto))
    ent_step (step_trunc _ _ "%add.tr" "%add" 64 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0) (by ent_auto))
    ent_step (step_shl_imm _ _ "%conv" "%add.tr" 32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32)) (BitVec.ofInt 32 6) (by ent_auto))
    rw [show (BitVec.ofInt 32 6).toNat = 6 from by decide, hconv]
    ent_step (step_gep64 _ _ "%add.ptr" "%out" "%k.addr.011" (.int 32) o (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 k (by omega)]; omega))
    rw [show o + (BitVec.ofNat 64 k).toNat * (Ty.int 32).sizeBytes = o + 4 * k from by
      rw [toNat_ofNat64 k (by omega), show (Ty.int 32).sizeBytes = 4 from rfl]; omega]
    ent_step (step_trunc _ _ "%1" "%0" 64 32 w (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.i" "%1" 32 (BitVec.ofNat 32 (w.toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [show (BitVec.ofNat 32 (w.toNat % 2 ^ 32) &&& BitVec.ofInt 32 255) = BitVec.ofNat 32 (byteOf w 0) from by simpa using and255_trunc w 0]
    ent_step (step_and_imm _ _ "%idxprom.i" "%0" 64 w (BitVec.ofInt 64 255) (by ent_auto))
    rw [show (w &&& BitVec.ofInt 64 255) = BitVec.ofNat 64 (byteOf w 0) from by simpa using and255_shift64 w 0]
    ent_step (step_gep64 _ _ "%arrayidx.i" "%tab" "%idxprom.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 0)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 0; rw [toNat_ofNat64 (byteOf w 0) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 0)).toNat * v8i32.sizeBytes = tab + byteOf w 0 * 32 from by rw [toNat_ofNat64 (byteOf w 0) (by have := byteOf_lt w 0; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%2" "%arrayidx.i" (tab + byteOf w 0 * 32) (pos8Row (byteOf w 0)) (pos8RowBytes (byteOf w 0)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_insertelement _ _ "%vecinit.i.i" "%conv" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.i" "%vecinit.i.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.i" "%2" "%vecinit7.i.i" (pos8Row (byteOf w 0)) (BitVec.ofNat 32 (posBase blk0 i)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [← groupVec_zero w (posBase blk0 i)]
    ent_step (step_store_vec _ _ "%add.i.i" "%add.ptr" (o + 4 * k) (groupVec w (posBase blk0 i) 0) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%3" "%conv.i" (BitVec.ofNat 32 (byteOf w 0)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.i" "%3" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 0)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 0)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 0)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 0)); omega)]]
    rw [ctpop_eq_groupPop32 w 0]
    ent_step (step_gep64 _ _ "%add.ptr.i" "%add.ptr" "%conv4.i" (.int 32) (o + 4 * k) (BitVec.ofNat 64 (groupPop w 0)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 0; rw [toNat_ofNat64 (groupPop w 0) (by omega)]; omega))
    rw [show o + 4 * k + (BitVec.ofNat 64 (groupPop w 0)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 1 from by
      rw [toNat_ofNat64 (groupPop w 0) (by have := groupPop_le w 0; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_one w k]
      omega]
    simp only [denoteCode, Option.bind]
    rw [blockMem_one]
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr => ent_auto



theorem pos8Group1_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 1 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.i" = some (.ptr (o + 4 * groupCursor w k 1)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 1 * 32) 32 = some (pos8RowBytes (byteOf w 1))) :
    ∃ env', denoteCode entryCalls pos8Group1 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 2 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.1.i" = some (.ptr (o + 4 * groupCursor w k 2)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group1, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.1.i" "%0" 64 w (BitVec.ofInt 64 8) (by ent_auto))
    rw [show (BitVec.ofInt 64 8).toNat = 8 * 1 from by decide]
    ent_step (step_trunc _ _ "%4" "%shr.1.i" 64 32 (w >>> (8 * 1)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.1.i" "%4" 32 (BitVec.ofNat 32 ((w >>> (8 * 1)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 1]
    ent_step (step_and_imm _ _ "%idxprom.1.i" "%shr.1.i" 64 (w >>> (8 * 1)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 1]
    ent_step (step_gep64 _ _ "%arrayidx.1.i" "%tab" "%idxprom.1.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 1)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 1; rw [toNat_ofNat64 (byteOf w 1) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 1)).toNat * v8i32.sizeBytes = tab + byteOf w 1 * 32 from by
      rw [toNat_ofNat64 (byteOf w 1) (by have := byteOf_lt w 1; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%5" "%arrayidx.1.i" (tab + byteOf w 1 * 32) (pos8Row (byteOf w 1)) (pos8RowBytes (byteOf w 1)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.1.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 8) (by ent_auto))
    rw [show BitVec.ofInt 32 8 = BitVec.ofNat 32 (8 * 1) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 1 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.1.i" "%add.1.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.1.i" "%vecinit.i.1.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.1.i" "%5" "%vecinit7.i.1.i" (pos8Row (byteOf w 1)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 1)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 1)) = groupVec w (posBase blk0 i) 1 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.1.i" "%add.ptr.i" (o + 4 * groupCursor w k 1) (groupVec w (posBase blk0 i) 1) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%6" "%conv.1.i" (BitVec.ofNat 32 (byteOf w 1)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.1.i" "%6" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 1)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 1)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 1)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 1)); omega)]]
    rw [ctpop_eq_groupPop32 w 1]
    ent_step (step_gep64 _ _ "%add.ptr.1.i" "%add.ptr.i" "%conv4.1.i" (.int 32) (o + 4 * groupCursor w k 1) (BitVec.ofNat 64 (groupPop w 1)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 1; rw [toNat_ofNat64 (groupPop w 1) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 1 + (BitVec.ofNat 64 (groupPop w 1)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 2 from by
      rw [toNat_ofNat64 (groupPop w 1) (by have := groupPop_le w 1; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 1]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group2_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 2 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.1.i" = some (.ptr (o + 4 * groupCursor w k 2)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 2 * 32) 32 = some (pos8RowBytes (byteOf w 2))) :
    ∃ env', denoteCode entryCalls pos8Group2 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 3 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.2.i" = some (.ptr (o + 4 * groupCursor w k 3)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group2, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.2.i" "%0" 64 w (BitVec.ofInt 64 16) (by ent_auto))
    rw [show (BitVec.ofInt 64 16).toNat = 8 * 2 from by decide]
    ent_step (step_trunc _ _ "%7" "%shr.2.i" 64 32 (w >>> (8 * 2)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.2.i" "%7" 32 (BitVec.ofNat 32 ((w >>> (8 * 2)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 2]
    ent_step (step_and_imm _ _ "%idxprom.2.i" "%shr.2.i" 64 (w >>> (8 * 2)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 2]
    ent_step (step_gep64 _ _ "%arrayidx.2.i" "%tab" "%idxprom.2.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 2)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 2; rw [toNat_ofNat64 (byteOf w 2) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 2)).toNat * v8i32.sizeBytes = tab + byteOf w 2 * 32 from by
      rw [toNat_ofNat64 (byteOf w 2) (by have := byteOf_lt w 2; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%8" "%arrayidx.2.i" (tab + byteOf w 2 * 32) (pos8Row (byteOf w 2)) (pos8RowBytes (byteOf w 2)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.2.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 16) (by ent_auto))
    rw [show BitVec.ofInt 32 16 = BitVec.ofNat 32 (8 * 2) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 2 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.2.i" "%add.2.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.2.i" "%vecinit.i.2.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.2.i" "%8" "%vecinit7.i.2.i" (pos8Row (byteOf w 2)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 2)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 2)) = groupVec w (posBase blk0 i) 2 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.2.i" "%add.ptr.1.i" (o + 4 * groupCursor w k 2) (groupVec w (posBase blk0 i) 2) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%9" "%conv.2.i" (BitVec.ofNat 32 (byteOf w 2)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.2.i" "%9" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 2)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 2)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 2)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 2)); omega)]]
    rw [ctpop_eq_groupPop32 w 2]
    ent_step (step_gep64 _ _ "%add.ptr.2.i" "%add.ptr.1.i" "%conv4.2.i" (.int 32) (o + 4 * groupCursor w k 2) (BitVec.ofNat 64 (groupPop w 2)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 2; rw [toNat_ofNat64 (groupPop w 2) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 2 + (BitVec.ofNat 64 (groupPop w 2)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 3 from by
      rw [toNat_ofNat64 (groupPop w 2) (by have := groupPop_le w 2; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 2]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group3_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 3 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.2.i" = some (.ptr (o + 4 * groupCursor w k 3)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 3 * 32) 32 = some (pos8RowBytes (byteOf w 3))) :
    ∃ env', denoteCode entryCalls pos8Group3 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 4 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.3.i" = some (.ptr (o + 4 * groupCursor w k 4)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group3, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.3.i" "%0" 64 w (BitVec.ofInt 64 24) (by ent_auto))
    rw [show (BitVec.ofInt 64 24).toNat = 8 * 3 from by decide]
    ent_step (step_trunc _ _ "%10" "%shr.3.i" 64 32 (w >>> (8 * 3)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.3.i" "%10" 32 (BitVec.ofNat 32 ((w >>> (8 * 3)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 3]
    ent_step (step_and_imm _ _ "%idxprom.3.i" "%shr.3.i" 64 (w >>> (8 * 3)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 3]
    ent_step (step_gep64 _ _ "%arrayidx.3.i" "%tab" "%idxprom.3.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 3)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 3; rw [toNat_ofNat64 (byteOf w 3) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 3)).toNat * v8i32.sizeBytes = tab + byteOf w 3 * 32 from by
      rw [toNat_ofNat64 (byteOf w 3) (by have := byteOf_lt w 3; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%11" "%arrayidx.3.i" (tab + byteOf w 3 * 32) (pos8Row (byteOf w 3)) (pos8RowBytes (byteOf w 3)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.3.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 24) (by ent_auto))
    rw [show BitVec.ofInt 32 24 = BitVec.ofNat 32 (8 * 3) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 3 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.3.i" "%add.3.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.3.i" "%vecinit.i.3.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.3.i" "%11" "%vecinit7.i.3.i" (pos8Row (byteOf w 3)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 3)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 3)) = groupVec w (posBase blk0 i) 3 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.3.i" "%add.ptr.2.i" (o + 4 * groupCursor w k 3) (groupVec w (posBase blk0 i) 3) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%12" "%conv.3.i" (BitVec.ofNat 32 (byteOf w 3)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.3.i" "%12" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 3)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 3)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 3)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 3)); omega)]]
    rw [ctpop_eq_groupPop32 w 3]
    ent_step (step_gep64 _ _ "%add.ptr.3.i" "%add.ptr.2.i" "%conv4.3.i" (.int 32) (o + 4 * groupCursor w k 3) (BitVec.ofNat 64 (groupPop w 3)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 3; rw [toNat_ofNat64 (groupPop w 3) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 3 + (BitVec.ofNat 64 (groupPop w 3)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 4 from by
      rw [toNat_ofNat64 (groupPop w 3) (by have := groupPop_le w 3; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 3]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group4_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 4 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.3.i" = some (.ptr (o + 4 * groupCursor w k 4)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 4 * 32) 32 = some (pos8RowBytes (byteOf w 4))) :
    ∃ env', denoteCode entryCalls pos8Group4 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 5 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.4.i" = some (.ptr (o + 4 * groupCursor w k 5)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group4, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.4.i" "%0" 64 w (BitVec.ofInt 64 32) (by ent_auto))
    rw [show (BitVec.ofInt 64 32).toNat = 8 * 4 from by decide]
    ent_step (step_trunc _ _ "%13" "%shr.4.i" 64 32 (w >>> (8 * 4)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.4.i" "%13" 32 (BitVec.ofNat 32 ((w >>> (8 * 4)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 4]
    ent_step (step_and_imm _ _ "%idxprom.4.i" "%shr.4.i" 64 (w >>> (8 * 4)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 4]
    ent_step (step_gep64 _ _ "%arrayidx.4.i" "%tab" "%idxprom.4.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 4)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 4; rw [toNat_ofNat64 (byteOf w 4) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 4)).toNat * v8i32.sizeBytes = tab + byteOf w 4 * 32 from by
      rw [toNat_ofNat64 (byteOf w 4) (by have := byteOf_lt w 4; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%14" "%arrayidx.4.i" (tab + byteOf w 4 * 32) (pos8Row (byteOf w 4)) (pos8RowBytes (byteOf w 4)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.4.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 32) (by ent_auto))
    rw [show BitVec.ofInt 32 32 = BitVec.ofNat 32 (8 * 4) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 4 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.4.i" "%add.4.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.4.i" "%vecinit.i.4.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.4.i" "%14" "%vecinit7.i.4.i" (pos8Row (byteOf w 4)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 4)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 4)) = groupVec w (posBase blk0 i) 4 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.4.i" "%add.ptr.3.i" (o + 4 * groupCursor w k 4) (groupVec w (posBase blk0 i) 4) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%15" "%conv.4.i" (BitVec.ofNat 32 (byteOf w 4)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.4.i" "%15" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 4)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 4)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 4)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 4)); omega)]]
    rw [ctpop_eq_groupPop32 w 4]
    ent_step (step_gep64 _ _ "%add.ptr.4.i" "%add.ptr.3.i" "%conv4.4.i" (.int 32) (o + 4 * groupCursor w k 4) (BitVec.ofNat 64 (groupPop w 4)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 4; rw [toNat_ofNat64 (groupPop w 4) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 4 + (BitVec.ofNat 64 (groupPop w 4)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 5 from by
      rw [toNat_ofNat64 (groupPop w 4) (by have := groupPop_le w 4; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 4]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group5_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 5 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.4.i" = some (.ptr (o + 4 * groupCursor w k 5)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 5 * 32) 32 = some (pos8RowBytes (byteOf w 5))) :
    ∃ env', denoteCode entryCalls pos8Group5 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 6 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.5.i" = some (.ptr (o + 4 * groupCursor w k 6)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group5, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.5.i" "%0" 64 w (BitVec.ofInt 64 40) (by ent_auto))
    rw [show (BitVec.ofInt 64 40).toNat = 8 * 5 from by decide]
    ent_step (step_trunc _ _ "%16" "%shr.5.i" 64 32 (w >>> (8 * 5)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.5.i" "%16" 32 (BitVec.ofNat 32 ((w >>> (8 * 5)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 5]
    ent_step (step_and_imm _ _ "%idxprom.5.i" "%shr.5.i" 64 (w >>> (8 * 5)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 5]
    ent_step (step_gep64 _ _ "%arrayidx.5.i" "%tab" "%idxprom.5.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 5)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 5; rw [toNat_ofNat64 (byteOf w 5) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 5)).toNat * v8i32.sizeBytes = tab + byteOf w 5 * 32 from by
      rw [toNat_ofNat64 (byteOf w 5) (by have := byteOf_lt w 5; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%17" "%arrayidx.5.i" (tab + byteOf w 5 * 32) (pos8Row (byteOf w 5)) (pos8RowBytes (byteOf w 5)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.5.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 40) (by ent_auto))
    rw [show BitVec.ofInt 32 40 = BitVec.ofNat 32 (8 * 5) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 5 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.5.i" "%add.5.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.5.i" "%vecinit.i.5.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.5.i" "%17" "%vecinit7.i.5.i" (pos8Row (byteOf w 5)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 5)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 5)) = groupVec w (posBase blk0 i) 5 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.5.i" "%add.ptr.4.i" (o + 4 * groupCursor w k 5) (groupVec w (posBase blk0 i) 5) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%18" "%conv.5.i" (BitVec.ofNat 32 (byteOf w 5)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.5.i" "%18" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 5)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 5)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 5)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 5)); omega)]]
    rw [ctpop_eq_groupPop32 w 5]
    ent_step (step_gep64 _ _ "%add.ptr.5.i" "%add.ptr.4.i" "%conv4.5.i" (.int 32) (o + 4 * groupCursor w k 5) (BitVec.ofNat 64 (groupPop w 5)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 5; rw [toNat_ofNat64 (groupPop w 5) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 5 + (BitVec.ofNat 64 (groupPop w 5)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 6 from by
      rw [toNat_ofNat64 (groupPop w 5) (by have := groupPop_le w 5; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 5]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group6_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 6 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.5.i" = some (.ptr (o + 4 * groupCursor w k 6)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 6 * 32) 32 = some (pos8RowBytes (byteOf w 6))) :
    ∃ env', denoteCode entryCalls pos8Group6 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 7 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) ∧
      lookupName env' "%add.ptr.6.i" = some (.ptr (o + 4 * groupCursor w k 7)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk', ?hptr'⟩
  case hrun =>
    simp only [pos8Group6, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.6.i" "%0" 64 w (BitVec.ofInt 64 48) (by ent_auto))
    rw [show (BitVec.ofInt 64 48).toNat = 8 * 6 from by decide]
    ent_step (step_trunc _ _ "%19" "%shr.6.i" 64 32 (w >>> (8 * 6)) (by ent_auto))
    ent_step (step_and_imm _ _ "%conv.6.i" "%19" 32 (BitVec.ofNat 32 ((w >>> (8 * 6)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
    rw [and255_trunc w 6]
    ent_step (step_and_imm _ _ "%idxprom.6.i" "%shr.6.i" 64 (w >>> (8 * 6)) (BitVec.ofInt 64 255) (by ent_auto))
    rw [and255_shift64 w 6]
    ent_step (step_gep64 _ _ "%arrayidx.6.i" "%tab" "%idxprom.6.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 6)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 6; rw [toNat_ofNat64 (byteOf w 6) (by omega)]; omega))
    rw [show tab + (BitVec.ofNat 64 (byteOf w 6)).toNat * v8i32.sizeBytes = tab + byteOf w 6 * 32 from by
      rw [toNat_ofNat64 (byteOf w 6) (by have := byteOf_lt w 6; omega), show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%20" "%arrayidx.6.i" (tab + byteOf w 6 * 32) (pos8Row (byteOf w 6)) (pos8RowBytes (byteOf w 6)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.6.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 48) (by ent_auto))
    rw [show BitVec.ofInt 32 48 = BitVec.ofNat 32 (8 * 6) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 6 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.6.i" "%add.6.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.6.i" "%vecinit.i.6.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.6.i" "%20" "%vecinit7.i.6.i" (pos8Row (byteOf w 6)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 6)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 6)) = groupVec w (posBase blk0 i) 6 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.6.i" "%add.ptr.5.i" (o + 4 * groupCursor w k 6) (groupVec w (posBase blk0 i) 6) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    ent_step (step_call_ctpop32 _ _ "%21" "%conv.6.i" (BitVec.ofNat 32 (byteOf w 6)) (by ent_auto))
    ent_step (step_zext _ _ "%conv4.6.i" "%21" 32 64 (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 6)))) (by ent_auto))
    rw [show (BitVec.ofNat 32 (ctpop (BitVec.ofNat 32 (byteOf w 6)))).toNat = ctpop (BitVec.ofNat 32 (byteOf w 6)) from by
      rw [toNat_ofNat32 _ (by have := ctpop_le (BitVec.ofNat 32 (byteOf w 6)); omega)]]
    rw [ctpop_eq_groupPop32 w 6]
    ent_step (step_gep64 _ _ "%add.ptr.6.i" "%add.ptr.5.i" "%conv4.6.i" (.int 32) (o + 4 * groupCursor w k 6) (BitVec.ofNat 64 (groupPop w 6)) (by ent_auto) (by ent_auto) (by have h := groupPop_le w 6; rw [toNat_ofNat64 (groupPop w 6) (by omega)]; omega))
    rw [show o + 4 * groupCursor w k 6 + (BitVec.ofNat 64 (groupPop w 6)).toNat * (Ty.int 32).sizeBytes = o + 4 * groupCursor w k 7 from by
      rw [toNat_ofNat64 (groupPop w 6) (by have := groupPop_le w 6; omega), show (Ty.int 32).sizeBytes = 4 from rfl, gc_succ' w k 6]
      omega]
    simp only [denoteCode, Option.bind]
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto
  case hptr' => ent_auto


theorem pos8Group7_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (mem : Mem)
    (hs : s.mem = blockMem o w (posBase blk0 i) k 7 mem)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (hconv : lookupName env "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))))
    (hptr : lookupName env "%add.ptr.6.i" = some (.ptr (o + 4 * groupCursor w k 7)))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hrowread : readBytes s.mem (tab + byteOf w 7 * 32) 32 = some (pos8RowBytes (byteOf w 7))) :
    ∃ env', denoteCode entryCalls pos8Group7 (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 8 mem }) ∧
      lookupName env' "%0" = some (.int 64 w) ∧
      lookupName env' "%conv" = some (.int 32 (BitVec.ofNat 32 (posBase blk0 i))) ∧
      lookupName env' "%tab" = some (.ptr tab) ∧
      lookupName env' "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)) := by
  refine ⟨?env', ?hrun, ?h0', ?hconv', ?htab', ?hk'⟩
  case hrun =>
    simp only [pos8Group7, reg, lit, zero8, splatLane0]
    ent_step (step_lshr_imm _ _ "%shr.7.i" "%0" 64 w (BitVec.ofInt 64 56) (by ent_auto))
    rw [show (BitVec.ofInt 64 56).toNat = 8 * 7 from by decide]
    ent_step (step_gep64 _ _ "%arrayidx.7.i" "%tab" "%shr.7.i" v8i32 tab (w >>> 56) (by ent_auto) (by ent_auto) (by rw [shr56_toNat w]; have := byteOf_lt w 7; omega))
    rw [show tab + (w >>> 56).toNat * v8i32.sizeBytes = tab + byteOf w 7 * 32 from by
      rw [shr56_toNat w, show v8i32.sizeBytes = 32 from rfl]]
    ent_step (step_load_vec _ _ "%22" "%arrayidx.7.i" (tab + byteOf w 7 * 32) (pos8Row (byteOf w 7)) (pos8RowBytes (byteOf w 7)) (by ent_auto) (by exact pos8RowBytes_length _) hrowread (by exact unpackLanes_row _))
    ent_step (step_or_imm _ _ "%add.7.i" "%conv" 32 (BitVec.ofNat 32 (posBase blk0 i)) (BitVec.ofInt 32 56) (by ent_auto))
    rw [show BitVec.ofInt 32 56 = BitVec.ofNat 32 (8 * 7) from by simp]
    rw [or_ofNat_shift (posBase blk0 i) 7 (posBase_mod blk0 i) (by omega) hblk]
    ent_step (step_insertelement _ _ "%vecinit.i.7.i" "%add.7.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by rfl))
    ent_step (step_shuffle_splat _ _ "%vecinit7.i.7.i" "%vecinit.i.7.i" (.imm (.splat 8 32 0)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by rfl))
    ent_step (step_addVec_splat _ _ "%add.i.7.i" "%22" "%vecinit7.i.7.i" (pos8Row (byteOf w 7)) (BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) (by ent_auto) (by ent_auto) (by exact pos8Row_length _))
    rw [show (pos8Row (byteOf w 7)).map (fun v => v + BitVec.ofNat 32 (posBase blk0 i + 8 * 7)) = groupVec w (posBase blk0 i) 7 from by
      rw [groupVec_at]]
    ent_step (step_store_vec _ _ "%add.i.7.i" "%add.ptr.6.i" (o + 4 * groupCursor w k 7) (groupVec w (posBase blk0 i) 7) (by ent_auto) (by ent_auto) (by exact groupVec_length _ _ _))
    simp only [hs, withEnv]
    rfl
  case h0' => ent_auto
  case hconv' => ent_auto
  case htab' => ent_auto
  case hk' => ent_auto


/-- The head group's load is the instruction that fails: the same instruction
prefix `pos8Head_run` steps, stopped where the row read returns nothing.  The
seven group lemmas below are this one per group, and each names only what its
prefix reads. -/
theorem pos8Head_run_none_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hrowread : readBytes s.mem (tab + byteOf w 0 * 32) 32 = none) :
    denoteCode entryCalls pos8Head (withEnv env s) = none := by
  simp only [pos8Head, reg, lit, zero8, splatLane0]
  ent_step (step_add_reg _ _ "%add" "%i.010" "%blk0" 64 (BitVec.ofNat 64 i) (BitVec.ofNat 64 blk0) (by ent_auto) (by ent_auto))
  ent_step (step_trunc _ _ "%add.tr" "%add" 64 32 (BitVec.ofNat 64 i + BitVec.ofNat 64 blk0) (by ent_auto))
  ent_step (step_shl_imm _ _ "%conv" "%add.tr" 32 (BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32)) (BitVec.ofInt 32 6) (by ent_auto))
  rw [show (BitVec.ofInt 32 6).toNat = 6 from by decide, hconv]
  ent_step (step_gep64 _ _ "%add.ptr" "%out" "%k.addr.011" (.int 32) o (BitVec.ofNat 64 k) (by ent_auto) (by ent_auto) (by rw [toNat_ofNat64 k (by omega)]; omega))
  rw [show o + (BitVec.ofNat 64 k).toNat * (Ty.int 32).sizeBytes = o + 4 * k from by
    rw [toNat_ofNat64 k (by omega), show (Ty.int 32).sizeBytes = 4 from rfl]; omega]
  ent_step (step_trunc _ _ "%1" "%0" 64 32 w (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.i" "%1" 32 (BitVec.ofNat 32 (w.toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [show (BitVec.ofNat 32 (w.toNat % 2 ^ 32) &&& BitVec.ofInt 32 255) = BitVec.ofNat 32 (byteOf w 0) from by simpa using and255_trunc w 0]
  ent_step (step_and_imm _ _ "%idxprom.i" "%0" 64 w (BitVec.ofInt 64 255) (by ent_auto))
  rw [show (w &&& BitVec.ofInt 64 255) = BitVec.ofNat 64 (byteOf w 0) from by simpa using and255_shift64 w 0]
  ent_step (step_gep64 _ _ "%arrayidx.i" "%tab" "%idxprom.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 0)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 0; rw [toNat_ofNat64 (byteOf w 0) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 0)).toNat * v8i32.sizeBytes = tab + byteOf w 0 * 32 from by rw [toNat_ofNat64 (byteOf w 0) (by have := byteOf_lt w 0; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group1_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 1 * 32) 32 = none) :
    denoteCode entryCalls pos8Group1 (withEnv env s) = none := by
  simp only [pos8Group1, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.1.i" "%0" 64 w (BitVec.ofInt 64 8) (by ent_auto))
  rw [show (BitVec.ofInt 64 8).toNat = 8 * 1 from by decide]
  ent_step (step_trunc _ _ "%4" "%shr.1.i" 64 32 (w >>> (8 * 1)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.1.i" "%4" 32 (BitVec.ofNat 32 ((w >>> (8 * 1)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 1]
  ent_step (step_and_imm _ _ "%idxprom.1.i" "%shr.1.i" 64 (w >>> (8 * 1)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 1]
  ent_step (step_gep64 _ _ "%arrayidx.1.i" "%tab" "%idxprom.1.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 1)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 1; rw [toNat_ofNat64 (byteOf w 1) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 1)).toNat * v8i32.sizeBytes = tab + byteOf w 1 * 32 from by
    rw [toNat_ofNat64 (byteOf w 1) (by have := byteOf_lt w 1; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.1.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group2_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 2 * 32) 32 = none) :
    denoteCode entryCalls pos8Group2 (withEnv env s) = none := by
  simp only [pos8Group2, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.2.i" "%0" 64 w (BitVec.ofInt 64 16) (by ent_auto))
  rw [show (BitVec.ofInt 64 16).toNat = 8 * 2 from by decide]
  ent_step (step_trunc _ _ "%7" "%shr.2.i" 64 32 (w >>> (8 * 2)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.2.i" "%7" 32 (BitVec.ofNat 32 ((w >>> (8 * 2)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 2]
  ent_step (step_and_imm _ _ "%idxprom.2.i" "%shr.2.i" 64 (w >>> (8 * 2)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 2]
  ent_step (step_gep64 _ _ "%arrayidx.2.i" "%tab" "%idxprom.2.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 2)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 2; rw [toNat_ofNat64 (byteOf w 2) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 2)).toNat * v8i32.sizeBytes = tab + byteOf w 2 * 32 from by
    rw [toNat_ofNat64 (byteOf w 2) (by have := byteOf_lt w 2; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.2.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group3_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 3 * 32) 32 = none) :
    denoteCode entryCalls pos8Group3 (withEnv env s) = none := by
  simp only [pos8Group3, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.3.i" "%0" 64 w (BitVec.ofInt 64 24) (by ent_auto))
  rw [show (BitVec.ofInt 64 24).toNat = 8 * 3 from by decide]
  ent_step (step_trunc _ _ "%10" "%shr.3.i" 64 32 (w >>> (8 * 3)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.3.i" "%10" 32 (BitVec.ofNat 32 ((w >>> (8 * 3)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 3]
  ent_step (step_and_imm _ _ "%idxprom.3.i" "%shr.3.i" 64 (w >>> (8 * 3)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 3]
  ent_step (step_gep64 _ _ "%arrayidx.3.i" "%tab" "%idxprom.3.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 3)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 3; rw [toNat_ofNat64 (byteOf w 3) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 3)).toNat * v8i32.sizeBytes = tab + byteOf w 3 * 32 from by
    rw [toNat_ofNat64 (byteOf w 3) (by have := byteOf_lt w 3; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.3.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group4_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 4 * 32) 32 = none) :
    denoteCode entryCalls pos8Group4 (withEnv env s) = none := by
  simp only [pos8Group4, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.4.i" "%0" 64 w (BitVec.ofInt 64 32) (by ent_auto))
  rw [show (BitVec.ofInt 64 32).toNat = 8 * 4 from by decide]
  ent_step (step_trunc _ _ "%13" "%shr.4.i" 64 32 (w >>> (8 * 4)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.4.i" "%13" 32 (BitVec.ofNat 32 ((w >>> (8 * 4)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 4]
  ent_step (step_and_imm _ _ "%idxprom.4.i" "%shr.4.i" 64 (w >>> (8 * 4)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 4]
  ent_step (step_gep64 _ _ "%arrayidx.4.i" "%tab" "%idxprom.4.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 4)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 4; rw [toNat_ofNat64 (byteOf w 4) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 4)).toNat * v8i32.sizeBytes = tab + byteOf w 4 * 32 from by
    rw [toNat_ofNat64 (byteOf w 4) (by have := byteOf_lt w 4; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.4.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group5_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 5 * 32) 32 = none) :
    denoteCode entryCalls pos8Group5 (withEnv env s) = none := by
  simp only [pos8Group5, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.5.i" "%0" 64 w (BitVec.ofInt 64 40) (by ent_auto))
  rw [show (BitVec.ofInt 64 40).toNat = 8 * 5 from by decide]
  ent_step (step_trunc _ _ "%16" "%shr.5.i" 64 32 (w >>> (8 * 5)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.5.i" "%16" 32 (BitVec.ofNat 32 ((w >>> (8 * 5)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 5]
  ent_step (step_and_imm _ _ "%idxprom.5.i" "%shr.5.i" 64 (w >>> (8 * 5)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 5]
  ent_step (step_gep64 _ _ "%arrayidx.5.i" "%tab" "%idxprom.5.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 5)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 5; rw [toNat_ofNat64 (byteOf w 5) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 5)).toNat * v8i32.sizeBytes = tab + byteOf w 5 * 32 from by
    rw [toNat_ofNat64 (byteOf w 5) (by have := byteOf_lt w 5; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.5.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group6_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 6 * 32) 32 = none) :
    denoteCode entryCalls pos8Group6 (withEnv env s) = none := by
  simp only [pos8Group6, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.6.i" "%0" 64 w (BitVec.ofInt 64 48) (by ent_auto))
  rw [show (BitVec.ofInt 64 48).toNat = 8 * 6 from by decide]
  ent_step (step_trunc _ _ "%19" "%shr.6.i" 64 32 (w >>> (8 * 6)) (by ent_auto))
  ent_step (step_and_imm _ _ "%conv.6.i" "%19" 32 (BitVec.ofNat 32 ((w >>> (8 * 6)).toNat % 2 ^ 32)) (BitVec.ofInt 32 255) (by ent_auto))
  rw [and255_trunc w 6]
  ent_step (step_and_imm _ _ "%idxprom.6.i" "%shr.6.i" 64 (w >>> (8 * 6)) (BitVec.ofInt 64 255) (by ent_auto))
  rw [and255_shift64 w 6]
  ent_step (step_gep64 _ _ "%arrayidx.6.i" "%tab" "%idxprom.6.i" v8i32 tab (BitVec.ofNat 64 (byteOf w 6)) (by ent_auto) (by ent_auto) (by have h := byteOf_lt w 6; rw [toNat_ofNat64 (byteOf w 6) (by omega)]; omega))
  rw [show tab + (BitVec.ofNat 64 (byteOf w 6)).toNat * v8i32.sizeBytes = tab + byteOf w 6 * 32 from by
    rw [toNat_ofNat64 (byteOf w 6) (by have := byteOf_lt w 6; omega), show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.6.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

theorem pos8Group7_run_none_row (env : Env) (s : State) (w : BitVec 64) (tab : Nat)
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hrowread : readBytes s.mem (tab + byteOf w 7 * 32) 32 = none) :
    denoteCode entryCalls pos8Group7 (withEnv env s) = none := by
  simp only [pos8Group7, reg, lit, zero8, splatLane0]
  ent_step (step_lshr_imm _ _ "%shr.7.i" "%0" 64 w (BitVec.ofInt 64 56) (by ent_auto))
  rw [show (BitVec.ofInt 64 56).toNat = 8 * 7 from by decide]
  ent_step (step_gep64 _ _ "%arrayidx.7.i" "%tab" "%shr.7.i" v8i32 tab (w >>> 56) (by ent_auto) (by ent_auto) (by rw [shr56_toNat w]; have := byteOf_lt w 7; omega))
  rw [show tab + (w >>> 56).toNat * v8i32.sizeBytes = tab + byteOf w 7 * 32 from by
    rw [shr56_toNat w, show v8i32.sizeBytes = 32 from rfl]]
  exact denoteCode_cons_none _ _ _ _
    (evalInstr_load_none (p := .reg "%arrayidx.7.i") (hp := by ent_auto)
      (hv := loadValue_vec_int_of_readBytes_none (by decide) (by decide) hrowread))

/-- The groups block completes when each of the eight rows it reads is readable at
its own address: the row variants in block order, with the row facts carried past
the stores by `blockMem_read_row`. -/
theorem pos8Groups_run_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hrows : ∀ j', j' < 8 →
      readBytes s.mem (tab + byteOf w j' * 32) 32 = some (pos8RowBytes (byteOf w j')))
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    ∃ env', denoteCode entryCalls pos8GroupsInstrs (withEnv env s) =
        some (withEnv env' { s with mem := blockMem o w (posBase blk0 i) k 8 s.mem }) ∧
      lookupName env' "%add1"
        = some (.int 64 (BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k)) := by
  have hrowAt : ∀ (j' : Nat), j' < 8 →
      readBytes (blockMem o w (posBase blk0 i) k j' s.mem) (tab + byteOf w j' * 32) 32
        = some (pos8RowBytes (byteOf w j')) := fun j' hj' =>
    (blockMem_read_row o w (posBase blk0 i) k s.mem tab (byteOf w j') (byteOf_lt w j') hdisj
      j' (by omega)).trans (hrows j' hj')
  obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
    pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
      (hrowAt 0 (by omega))
  obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
    pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
      (by rw [state_mem_update]; exact hrowAt 1 (by omega))
  obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
    pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
      (by rw [state_mem_update]; exact hrowAt 2 (by omega))
  obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
    pos8Group3_run_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
      (by rw [state_mem_update]; exact hrowAt 3 (by omega))
  obtain ⟨e5, h5, h5a, h5b, h5c, h5d, h5e⟩ :=
    pos8Group4_run_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h4a h4b h4e h4c h4d hblk
      (by rw [state_mem_update]; exact hrowAt 4 (by omega))
  obtain ⟨e6, h6, h6a, h6b, h6c, h6d, h6e⟩ :=
    pos8Group5_run_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h5a h5b h5e h5c h5d hblk
      (by rw [state_mem_update]; exact hrowAt 5 (by omega))
  obtain ⟨e7, h7, h7a, h7b, h7c, h7d, h7e⟩ :=
    pos8Group6_run_row e6 { s with mem := blockMem o w (posBase blk0 i) k 6 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h6a h6b h6e h6c h6d hblk
      (by rw [state_mem_update]; exact hrowAt 6 (by omega))
  obtain ⟨e8, h8, h8a, h8b, h8c, h8d⟩ :=
    pos8Group7_run_row e7 { s with mem := blockMem o w (posBase blk0 i) k 7 s.mem } w i blk0 k o tab
      s.mem (state_mem_update _ _) h7a h7b h7e h7c h7d hblk
      (by rw [state_mem_update]; exact hrowAt 7 (by omega))
  obtain ⟨e9, h9, h9a⟩ :=
    pos8Tail_run e8 { s with mem := blockMem o w (posBase blk0 i) k 8 s.mem } w k h8a h8d
  rw [pos8GroupsInstrs_split]
  refine ⟨e9, ?_, h9a⟩
  rw [denoteCode_append, h1]
  simp only [Option.bind_some]
  rw [denoteCode_append, h2]
  simp only [Option.bind_some]
  rw [denoteCode_append, h3]
  simp only [Option.bind_some]
  rw [denoteCode_append, h4]
  simp only [Option.bind_some]
  rw [denoteCode_append, h5]
  simp only [Option.bind_some]
  rw [denoteCode_append, h6]
  simp only [Option.bind_some]
  rw [denoteCode_append, h7]
  simp only [Option.bind_some]
  rw [denoteCode_append, h8]
  simp only [Option.bind_some]
  exact h9

/-- The groups block is `none` when group `g`'s row is unreadable and every other
row is readable: the groups before it step to their own rows, and a group whose
byte *is* the failing row fails there instead — either way the block has no
result, which is what makes the block's step `ub`.

One branch per group, because the block is a fixed nesting of eight appends and
no earlier group's result can be named without its own row's readability: the
step before the failing group is a different lemma in each case. -/
theorem pos8Groups_ub_of_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab g : Nat)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hrowsOk : ∀ m, m < 256 → m ≠ byteOf w g →
      readBytes s.mem (tab + m * 32) 32 = some (pos8RowBytes m))
    (hrow : readBytes s.mem (tab + byteOf w g * 32) 32 = none)
    (hg : g < 8)
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    denoteCode entryCalls pos8GroupsInstrs (withEnv env s) = none := by
  have hpre : ∀ (j' : Nat), j' < 8 → byteOf w j' ≠ byteOf w g →
      readBytes (blockMem o w (posBase blk0 i) k j' s.mem) (tab + byteOf w j' * 32) 32
        = some (pos8RowBytes (byteOf w j')) := fun j' hj' hne =>
    (blockMem_read_row o w (posBase blk0 i) k s.mem tab (byteOf w j') (byteOf_lt w j') hdisj
      j' (by omega)).trans (hrowsOk (byteOf w j') (byteOf_lt w j') hne)
  have hfail : ∀ (j' : Nat), j' < 8 → byteOf w j' = byteOf w g →
      readBytes (blockMem o w (posBase blk0 i) k j' s.mem) (tab + byteOf w j' * 32) 32 = none :=
    fun j' _ heq => by
      rw [heq]
      exact (blockMem_read_row o w (posBase blk0 i) k s.mem tab (byteOf w g) (byteOf_lt w g) hdisj
        j' (by omega)).trans hrow
  match g with
  | 0 =>
      rw [pos8GroupsInstrs_split]
      rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
        hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) rfl)]
      rfl
  | 1 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 1
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
          w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) rfl)]
        rfl
  | 2 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 2
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 2
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
            w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) rfl)]
          rfl
  | 3 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 3
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 3
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          by_cases hb2 : byteOf w 2 = byteOf w 3
          ·
            rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
              w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) hb2)]
            rfl
          ·
            obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
              pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
                w i blk0 k o tab s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
                (by rw [state_mem_update]; exact hpre 2 (by omega) hb2)
            rw [denoteCode_append, h3]
            simp only [Option.bind_some]
            rw [denoteCode_append, pos8Group3_run_none_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
              w tab h3a h3c (by rw [state_mem_update]; exact hfail 3 (by omega) rfl)]
            rfl
  | 4 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 4
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 4
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          by_cases hb2 : byteOf w 2 = byteOf w 4
          ·
            rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
              w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) hb2)]
            rfl
          ·
            obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
              pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
                w i blk0 k o tab s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
                (by rw [state_mem_update]; exact hpre 2 (by omega) hb2)
            rw [denoteCode_append, h3]
            simp only [Option.bind_some]
            by_cases hb3 : byteOf w 3 = byteOf w 4
            ·
              rw [denoteCode_append, pos8Group3_run_none_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                w tab h3a h3c (by rw [state_mem_update]; exact hfail 3 (by omega) hb3)]
              rfl
            ·
              obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
                pos8Group3_run_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                  w i blk0 k o tab s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
                  (by rw [state_mem_update]; exact hpre 3 (by omega) hb3)
              rw [denoteCode_append, h4]
              simp only [Option.bind_some]
              rw [denoteCode_append, pos8Group4_run_none_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                w tab h4a h4c (by rw [state_mem_update]; exact hfail 4 (by omega) rfl)]
              rfl
  | 5 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 5
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 5
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          by_cases hb2 : byteOf w 2 = byteOf w 5
          ·
            rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
              w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) hb2)]
            rfl
          ·
            obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
              pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
                w i blk0 k o tab s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
                (by rw [state_mem_update]; exact hpre 2 (by omega) hb2)
            rw [denoteCode_append, h3]
            simp only [Option.bind_some]
            by_cases hb3 : byteOf w 3 = byteOf w 5
            ·
              rw [denoteCode_append, pos8Group3_run_none_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                w tab h3a h3c (by rw [state_mem_update]; exact hfail 3 (by omega) hb3)]
              rfl
            ·
              obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
                pos8Group3_run_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                  w i blk0 k o tab s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
                  (by rw [state_mem_update]; exact hpre 3 (by omega) hb3)
              rw [denoteCode_append, h4]
              simp only [Option.bind_some]
              by_cases hb4 : byteOf w 4 = byteOf w 5
              ·
                rw [denoteCode_append, pos8Group4_run_none_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                  w tab h4a h4c (by rw [state_mem_update]; exact hfail 4 (by omega) hb4)]
                rfl
              ·
                obtain ⟨e5, h5, h5a, h5b, h5c, h5d, h5e⟩ :=
                  pos8Group4_run_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                    w i blk0 k o tab s.mem (state_mem_update _ _) h4a h4b h4e h4c h4d hblk
                    (by rw [state_mem_update]; exact hpre 4 (by omega) hb4)
                rw [denoteCode_append, h5]
                simp only [Option.bind_some]
                rw [denoteCode_append, pos8Group5_run_none_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem }
                  w tab h5a h5c (by rw [state_mem_update]; exact hfail 5 (by omega) rfl)]
                rfl
  | 6 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 6
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 6
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          by_cases hb2 : byteOf w 2 = byteOf w 6
          ·
            rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
              w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) hb2)]
            rfl
          ·
            obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
              pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
                w i blk0 k o tab s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
                (by rw [state_mem_update]; exact hpre 2 (by omega) hb2)
            rw [denoteCode_append, h3]
            simp only [Option.bind_some]
            by_cases hb3 : byteOf w 3 = byteOf w 6
            ·
              rw [denoteCode_append, pos8Group3_run_none_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                w tab h3a h3c (by rw [state_mem_update]; exact hfail 3 (by omega) hb3)]
              rfl
            ·
              obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
                pos8Group3_run_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                  w i blk0 k o tab s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
                  (by rw [state_mem_update]; exact hpre 3 (by omega) hb3)
              rw [denoteCode_append, h4]
              simp only [Option.bind_some]
              by_cases hb4 : byteOf w 4 = byteOf w 6
              ·
                rw [denoteCode_append, pos8Group4_run_none_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                  w tab h4a h4c (by rw [state_mem_update]; exact hfail 4 (by omega) hb4)]
                rfl
              ·
                obtain ⟨e5, h5, h5a, h5b, h5c, h5d, h5e⟩ :=
                  pos8Group4_run_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                    w i blk0 k o tab s.mem (state_mem_update _ _) h4a h4b h4e h4c h4d hblk
                    (by rw [state_mem_update]; exact hpre 4 (by omega) hb4)
                rw [denoteCode_append, h5]
                simp only [Option.bind_some]
                by_cases hb5 : byteOf w 5 = byteOf w 6
                ·
                  rw [denoteCode_append, pos8Group5_run_none_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem }
                    w tab h5a h5c (by rw [state_mem_update]; exact hfail 5 (by omega) hb5)]
                  rfl
                ·
                  obtain ⟨e6, h6, h6a, h6b, h6c, h6d, h6e⟩ :=
                    pos8Group5_run_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem }
                      w i blk0 k o tab s.mem (state_mem_update _ _) h5a h5b h5e h5c h5d hblk
                      (by rw [state_mem_update]; exact hpre 5 (by omega) hb5)
                  rw [denoteCode_append, h6]
                  simp only [Option.bind_some]
                  rw [denoteCode_append, pos8Group6_run_none_row e6 { s with mem := blockMem o w (posBase blk0 i) k 6 s.mem }
                    w tab h6a h6c (by rw [state_mem_update]; exact hfail 6 (by omega) rfl)]
                  rfl
  | 7 =>
      rw [pos8GroupsInstrs_split]
      by_cases hb0 : byteOf w 0 = byteOf w 7
      ·
        rw [denoteCode_append, pos8Head_run_none_row env s w i blk0 k o tab
          hi hbk hout hk h0 htab hconv hk63 (hfail 0 (by omega) hb0)]
        rfl
      ·
        obtain ⟨e1, h1, h1a, h1b, h1c, h1d, h1e⟩ :=
          pos8Head_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab hk63 hblk hconv
            (hpre 0 (by omega) hb0)
        rw [denoteCode_append, h1]
        simp only [Option.bind_some]
        by_cases hb1 : byteOf w 1 = byteOf w 7
        ·
          rw [denoteCode_append, pos8Group1_run_none_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
            w tab h1a h1c (by rw [state_mem_update]; exact hfail 1 (by omega) hb1)]
          rfl
        ·
          obtain ⟨e2, h2, h2a, h2b, h2c, h2d, h2e⟩ :=
            pos8Group1_run_row e1 { s with mem := blockMem o w (posBase blk0 i) k 1 s.mem }
              w i blk0 k o tab s.mem (state_mem_update _ _) h1a h1b h1e h1c h1d hblk
              (by rw [state_mem_update]; exact hpre 1 (by omega) hb1)
          rw [denoteCode_append, h2]
          simp only [Option.bind_some]
          by_cases hb2 : byteOf w 2 = byteOf w 7
          ·
            rw [denoteCode_append, pos8Group2_run_none_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
              w tab h2a h2c (by rw [state_mem_update]; exact hfail 2 (by omega) hb2)]
            rfl
          ·
            obtain ⟨e3, h3, h3a, h3b, h3c, h3d, h3e⟩ :=
              pos8Group2_run_row e2 { s with mem := blockMem o w (posBase blk0 i) k 2 s.mem }
                w i blk0 k o tab s.mem (state_mem_update _ _) h2a h2b h2e h2c h2d hblk
                (by rw [state_mem_update]; exact hpre 2 (by omega) hb2)
            rw [denoteCode_append, h3]
            simp only [Option.bind_some]
            by_cases hb3 : byteOf w 3 = byteOf w 7
            ·
              rw [denoteCode_append, pos8Group3_run_none_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                w tab h3a h3c (by rw [state_mem_update]; exact hfail 3 (by omega) hb3)]
              rfl
            ·
              obtain ⟨e4, h4, h4a, h4b, h4c, h4d, h4e⟩ :=
                pos8Group3_run_row e3 { s with mem := blockMem o w (posBase blk0 i) k 3 s.mem }
                  w i blk0 k o tab s.mem (state_mem_update _ _) h3a h3b h3e h3c h3d hblk
                  (by rw [state_mem_update]; exact hpre 3 (by omega) hb3)
              rw [denoteCode_append, h4]
              simp only [Option.bind_some]
              by_cases hb4 : byteOf w 4 = byteOf w 7
              ·
                rw [denoteCode_append, pos8Group4_run_none_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                  w tab h4a h4c (by rw [state_mem_update]; exact hfail 4 (by omega) hb4)]
                rfl
              ·
                obtain ⟨e5, h5, h5a, h5b, h5c, h5d, h5e⟩ :=
                  pos8Group4_run_row e4 { s with mem := blockMem o w (posBase blk0 i) k 4 s.mem }
                    w i blk0 k o tab s.mem (state_mem_update _ _) h4a h4b h4e h4c h4d hblk
                    (by rw [state_mem_update]; exact hpre 4 (by omega) hb4)
                rw [denoteCode_append, h5]
                simp only [Option.bind_some]
                by_cases hb5 : byteOf w 5 = byteOf w 7
                ·
                  rw [denoteCode_append, pos8Group5_run_none_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem }
                    w tab h5a h5c (by rw [state_mem_update]; exact hfail 5 (by omega) hb5)]
                  rfl
                ·
                  obtain ⟨e6, h6, h6a, h6b, h6c, h6d, h6e⟩ :=
                    pos8Group5_run_row e5 { s with mem := blockMem o w (posBase blk0 i) k 5 s.mem }
                      w i blk0 k o tab s.mem (state_mem_update _ _) h5a h5b h5e h5c h5d hblk
                      (by rw [state_mem_update]; exact hpre 5 (by omega) hb5)
                  rw [denoteCode_append, h6]
                  simp only [Option.bind_some]
                  by_cases hb6 : byteOf w 6 = byteOf w 7
                  ·
                    rw [denoteCode_append, pos8Group6_run_none_row e6 { s with mem := blockMem o w (posBase blk0 i) k 6 s.mem }
                      w tab h6a h6c (by rw [state_mem_update]; exact hfail 6 (by omega) hb6)]
                    rfl
                  ·
                    obtain ⟨e7, h7, h7a, h7b, h7c, h7d, h7e⟩ :=
                      pos8Group6_run_row e6 { s with mem := blockMem o w (posBase blk0 i) k 6 s.mem }
                        w i blk0 k o tab s.mem (state_mem_update _ _) h6a h6b h6e h6c h6d hblk
                        (by rw [state_mem_update]; exact hpre 6 (by omega) hb6)
                    rw [denoteCode_append, h7]
                    simp only [Option.bind_some]
                    rw [denoteCode_append, pos8Group7_run_none_row e7 { s with mem := blockMem o w (posBase blk0 i) k 7 s.mem }
                      w tab h7a h7c (by rw [state_mem_update]; exact hfail 7 (by omega) rfl)]
                    rfl
  | n + 8 =>
      exact False.elim (by omega)
/-- `if.end` steps when every row the block reads is readable: the groups block
completes, the branch to `cleanup` is taken, and the loop's parameters survive —
`pos8Groups_step` with the whole-table premise replaced by the eight rows. -/
theorem pos8Groups_step_row (env : Env) (s : State) (w : BitVec 64) (i blk0 k o tab : Nat)
    (M : Mem)
    (hpc : s.pc = "if.end")
    (hM : M = blockMem o w (posBase blk0 i) k 8 s.mem)
    (hi : lookupName env "%i.010" = some (.int 64 (BitVec.ofNat 64 i)))
    (hbk : lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)))
    (hout : lookupName env "%out" = some (.ptr o))
    (hk : lookupName env "%k.addr.011" = some (.int 64 (BitVec.ofNat 64 k)))
    (h0 : lookupName env "%0" = some (.int 64 w))
    (htab : lookupName env "%tab" = some (.ptr tab))
    (hk63 : k + 64 ≤ 2 ^ 63)
    (hblk : posBase blk0 i + 64 ≤ 2 ^ 32)
    (hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
              = BitVec.ofNat 32 (posBase blk0 i))
    (hrows : ∀ j', j' < 8 →
      readBytes s.mem (tab + byteOf w j' * 32) 32 = some (pos8RowBytes (byteOf w j')))
    (hdisj : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab) :
    ∃ env', denoteCode entryCalls pos8GroupsInstrs (withEnv env s) = some (withEnv env' { s with mem := M }) ∧
      step entryCalls entryPos8Function (withEnv env s)
        = .jump (withEnv env' { s with mem := M, pc := "cleanup", pre := some "if.end" }) ∧
      (∀ n ∈ pos8Params, lookupName env' n = lookupName env n) ∧
      lookupName env' "%i.010" = lookupName env "%i.010" ∧
      lookupName env' "%add1"
        = some (.int 64 (BitVec.ofNat 64 (ctpop w) + BitVec.ofNat 64 k)) := by
  obtain ⟨env', hbody, h1⟩ := pos8Groups_run_row env s w i blk0 k o tab hi hbk hout hk h0 htab
    hk63 hblk hconv hrows hdisj
  have hbody' : denoteCode entryCalls pos8GroupsInstrs (withEnv env s)
      = some (withEnv env' { s with mem := M }) := by
    rw [← hM] at hbody; exact hbody
  have hparam : ∀ n ∈ pos8Params, lookupName env' n = lookupName env n := by
    intro n hn
    exact denoteCode_lookupName entryCalls pos8GroupsInstrs n
      (fun j hj hd => pos8Params_groups j hj (hd.symm ▸ List.mem_map_of_mem (f := some) hn))
      (withEnv env s) (withEnv env' { s with mem := M }) hbody'
  have hi010 : lookupName env' "%i.010" = lookupName env "%i.010" :=
    denoteCode_lookupName entryCalls pos8GroupsInstrs "%i.010"
      (fun j hj hd => pos8_i010_groups j hj hd)
      (withEnv env s) (withEnv env' { s with mem := M }) hbody'
  refine ⟨env', hbody', ?_, hparam, hi010, h1⟩
  rw [step_of (withEnv env s) "if.end" pos8Groups (withEnv env' { s with mem := M }) hpc
    findBlock_pos8Groups hbody']
  show execTerm (withEnv env' { s with mem := M }) (.br "cleanup")
    = .jump (withEnv env' { s with mem := M, pc := "cleanup", pre := some "if.end" })
  rw [execTerm_br]
  rw [show (withEnv env' { s with mem := M }).pc = "if.end" from hpc]
  rfl

/-- From a loop state with `r` blocks left before the failing one, if the memory
holds the word `w` at block `jj`, `w` is non-zero, every table row is readable
except `w`'s group `g` row, and that row is not, the run is `ub`: each earlier
block steps and hands the successor state on — a block whose word contains the
failing byte is `ub` at that group, otherwise all eight of its rows are readable
and it completes — and the frame carries the word, the readable rows and the
unreadable row past every store, because a block's writes stay inside the output
span. -/
theorem pos8_loop_run_row_ub (blk0 nblk k0 o tab e : Nat) (jj g : Nat) (w : BitVec 64)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hk63 : k0 + 64 * nblk + 9 < 2 ^ 63)
    (hdisjE : e + 8 * nblk ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ e)
    (hdisjT : tab + 8192 ≤ o ∨ o + 4 * (k0 + 64 * nblk + 8) ≤ tab)
    (hj : jj < nblk)
    (hg : g < 8)
    (hw : w ≠ 0) :
    ∀ (r i k : Nat) (mem : Mem) (env : Env) (s : State) (p : String) (opk opi : Operand),
      1 ≤ r → i + r = jj + 1 →
      s.pc = "for.body" → s.pre = some p →
      phiIncoming p pos8IncomingK = some opk → phiIncoming p pos8IncomingI = some opi →
      evalOperand (withEnv env s) opk = some (.int 64 (BitVec.ofNat 64 k)) →
      evalOperand (withEnv (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: env) s) opi
        = some (.int 64 (BitVec.ofNat 64 i)) →
      lookupName env "%ent" = some (.ptr e) →
      lookupName env "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) →
      lookupName env "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) →
      lookupName env "%out" = some (.ptr o) →
      lookupName env "%tab" = some (.ptr tab) →
      s.mem = mem →
      k ≤ k0 + 64 * i →
      readBytes mem (e + 8 * jj) 8 = some (natToBytes w.toNat 8) →
      (∀ m, m < 256 → m ≠ byteOf w g →
        readBytes mem (tab + m * 32) 32 = some (pos8RowBytes m)) →
      readBytes mem (tab + byteOf w g * 32) 32 = none →
      runFuel entryCalls (3 * r + 1) entryPos8Function (withEnv env s) = some .ub := by
  intro r
  induction r with
  | zero => intro i k mem env s p opk opi hr; exact absurd hr (by omega)
  | succ r' ih =>
    intro i k mem env s p opk opi hr hi hpc hpre hopk hopi hvk hvi hent hbk hNb hout htab hsm hkb
      hwordS hrowsOkS hrowS
    have hinl : i < nblk := by omega
    have hn63 : nblk < 2 ^ 63 := by
      have h1 : 64 * nblk < 2 ^ 63 := by omega
      have h2 : 64 * nblk < 64 * 2 ^ 57 := by
        rw [show 64 * 2 ^ 57 = 2 ^ 63 from by decide]
        exact h1
      have h3 : nblk < 2 ^ 57 := Nat.lt_of_mul_lt_mul_left h2
      omega
    have hi63 : i < 2 ^ 63 := by omega
    have hi64 : i + 1 < 2 ^ 64 := by omega
    have hnb64 : nblk < 2 ^ 64 := by omega
    have hfuel : 3 * (r' + 1) + 1 = (((3 * r' + 1) + 1) + 1) + 1 := by omega
    have hblk' : posBase blk0 i + 64 ≤ 2 ^ 32 := by
      have h1 : 64 * (blk0 + i) + 64 ≤ 64 * (blk0 + nblk) := by
        have h2 : blk0 + i + 1 ≤ blk0 + nblk := by omega
        calc 64 * (blk0 + i) + 64 = 64 * (blk0 + i + 1) := by omega
          _ ≤ 64 * (blk0 + nblk) := by omega
      rw [posBase_eq]
      omega
    have hk63' : k + 64 ≤ 2 ^ 63 := by omega
    have hconv : BitVec.ofNat 32 ((BitVec.ofNat 64 i + BitVec.ofNat 64 blk0).toNat % 2 ^ 32) <<< 6
        = BitVec.ofNat 32 (posBase blk0 i) := pos8_conv i blk0 (by omega)
    by_cases hnow : i = jj
    · -- the failing row is this block's: the body steps to `if.end` and the
      -- groups block has no result
      have hword : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w.toNat 8) := by
        rw [hsm, hnow]; exact hwordS
      have hrowsOk' : ∀ m, m < 256 → m ≠ byteOf w g →
          readBytes s.mem (tab + m * 32) 32 = some (pos8RowBytes m) := by
        intro m hm hne; rw [hsm]; exact hrowsOkS m hm hne
      have hrow' : readBytes s.mem (tab + byteOf w g * 32) 32 = none := by
        rw [hsm]; exact hrowS
      have hdisjT' : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w + 8) ≤ tab :=
        table_disj_of_hdisj o tab k k0 nblk (ctpop w) (by have := ctpop_le w; omega) hdisjT
      obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, htob1⟩ :=
        pos8Body_step_pos env s w i k e p opk opi hpc hpre hopk hopi hvk hvi hent hword hi63 hw
      have hfr1 := fun (n : String) (hn : n ∈ pos8Params) =>
        (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body n hn)
      have hden : denoteCode entryCalls pos8GroupsInstrs
          (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) = none :=
        pos8Groups_ub_of_row e1 { s with pc := "if.end", pre := some "for.body" } w i blk0 k o tab g
          hi1 ((hfr1 "%blk0" (by decide)).trans hbk) ((hfr1 "%out" (by decide)).trans hout)
          hk1 h01 ((hfr1 "%tab" (by decide)).trans htab) hk63' hblk' hconv hrowsOk' hrow' hg hdisjT'
      have hstepub : step entryCalls entryPos8Function
          (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) = .ub :=
        step_ub_pos8 (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) "if.end"
          pos8Groups rfl findBlock_pos8Groups hden
      rw [hfuel]
      rw [runFuel_jump hstep1]
      exact runFuel_mono_le (show 2 ≤ ((3 * r' + 1) + 1) + 1 from by omega)
        (runFuel_of_step_ub (n := 1) hstepub)
    · have hlt : i < jj := by omega
      have hr2 : 1 ≤ r' := by omega
      have hne : i + 1 ≠ nblk := by omega
      have hx : ¬ BitVec.ofNat 64 (i + 1) = BitVec.ofNat 64 nblk := fun hcon =>
        hne (ofNat64_inj (by omega) hnb64 hcon)
      cases hrd : readBytes s.mem (e + 8 * i) 8 with
      | none =>
          exact runFuel_mono_le (show 2 ≤ 3 * (r' + 1) + 1 from by omega)
            (pos8Body_ub_of_no_read env s i k e p opk opi hpc hpre hopk hopi hvk hvi hent hi63 hrd)
      | some bs =>
          obtain ⟨w', hwdef⟩ : ∃ w' : BitVec 64, natToBytes w'.toNat 8 = bs :=
            ⟨BitVec.ofNat 64 (bytesToNat bs), natToBytes_of_readBytes_eight s.mem (e + 8 * i) bs hrd⟩
          have hread : readBytes s.mem (e + 8 * i) 8 = some (natToBytes w'.toNat 8) := by
            rw [hwdef]; exact hrd
          by_cases hw' : w' = 0
          · -- the block emits nothing: `cleanup` and the next block
            obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
              pos8Body_step_zero env s w' i k e p opk opi hpc hpre
                hopk hopi hvk hvi hent hread hi63 hw'
            have hNb1 : lookupName e1 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%nblk"
                (by decide)).trans hNb
            obtain ⟨e2, hrun2, hstep2, hk2, hinc2, hx2⟩ :=
              pos8Cleanup_step_more e1 { s with pc := "cleanup", pre := some "for.body" } i k nblk
                "for.body" (.reg "%k.addr.011") rfl rfl rfl
                (evalOperand_reg_of e1 _ _ _ hk1) hi1 hNb1 hi64 hx
            have hfr2 := fun (n : String) (hn : n ∈ pos8Params) =>
              (denoteCode_params pos8Advance.instrs e1 e2
                { s with pc := "cleanup", pre := some "for.body" } hrun2 pos8Params_cleanup n hn)
            have hb1' : lookupName e1 "%blk0" = some (.int 64 (BitVec.ofNat 64 blk0)) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%blk0"
                (by decide)).trans hbk
            have hout1 : lookupName e1 "%out" = some (.ptr o) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%out"
                (by decide)).trans hout
            have htab1 : lookupName e1 "%tab" = some (.ptr tab) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%tab"
                (by decide)).trans htab
            have hent1 : lookupName e1 "%ent" = some (.ptr e) :=
              (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body "%ent"
                (by decide)).trans hent
            obtain hrec :=
              ih (i + 1) k mem e2 { s with pc := "for.body", pre := some "cleanup" } "cleanup"
                (.reg "%k.addr.1") (.reg "%inc") hr2 (by omega) rfl rfl rfl rfl
                (evalOperand_reg_of e2 _ _ _ hk2)
                (evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 k)) :: e2) _ "%inc" _
                  ((lookupName_cons_ne _ _ (by decide)).trans hinc2))
                ((hfr2 "%ent" (by decide)).trans hent1)
                ((hfr2 "%blk0" (by decide)).trans hb1')
                ((hfr2 "%nblk" (by decide)).trans hNb1)
                ((hfr2 "%out" (by decide)).trans hout1)
                ((hfr2 "%tab" (by decide)).trans htab1)
                hsm (by omega) hwordS hrowsOkS hrowS
            rw [hfuel]
            rw [runFuel_jump hstep1]
            rw [runFuel_jump hstep2]
            exact runFuel_mono_le (show 3 * r' + 1 ≤ (3 * r' + 1) + 1 from Nat.le_succ _) hrec
          · by_cases hocc : ∃ j', j' < 8 ∧ byteOf w' j' = byteOf w g
            · -- this block's word holds the failing byte: it is `ub` at that group
              obtain ⟨j', hj'8, heqj⟩ := hocc
              have hdisjT' : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w' + 8) ≤ tab :=
                table_disj_of_hdisj o tab k k0 nblk (ctpop w') (by have := ctpop_le w'; omega) hdisjT
              obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, htob1⟩ :=
                pos8Body_step_pos env s w' i k e p opk opi hpc hpre hopk hopi hvk hvi hent hread hi63 hw'
              have hfr1 := fun (n : String) (hn : n ∈ pos8Params) =>
                (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body n hn)
              have hden : denoteCode entryCalls pos8GroupsInstrs
                  (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) = none :=
                pos8Groups_ub_of_row e1 { s with pc := "if.end", pre := some "for.body" } w' i blk0 k o tab j'
                  hi1 ((hfr1 "%blk0" (by decide)).trans hbk) ((hfr1 "%out" (by decide)).trans hout)
                  hk1 h01 ((hfr1 "%tab" (by decide)).trans htab) hk63' hblk' hconv
                  (fun m hm hne => by
                    show readBytes s.mem (tab + m * 32) 32 = some (pos8RowBytes m)
                    rw [hsm]
                    exact hrowsOkS m hm (fun hc => hne (hc.trans heqj.symm)))
                  (by
                    show readBytes s.mem (tab + byteOf w' j' * 32) 32 = none
                    rw [heqj, hsm]
                    exact hrowS)
                  hj'8 hdisjT'
              have hstepub : step entryCalls entryPos8Function
                  (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) = .ub :=
                step_ub_pos8 (withEnv e1 { s with pc := "if.end", pre := some "for.body" }) "if.end"
                  pos8Groups rfl findBlock_pos8Groups hden
              rw [hfuel]
              rw [runFuel_jump hstep1]
              exact runFuel_mono_le (show 2 ≤ ((3 * r' + 1) + 1) + 1 from by omega)
                (runFuel_of_step_ub (n := 1) hstepub)
            · -- every row this block reads is readable: the groups complete
              have hrowsNow : ∀ (j' : Nat), j' < 8 →
                  readBytes s.mem (tab + byteOf w' j' * 32) 32 = some (pos8RowBytes (byteOf w' j')) :=
                fun j' hj' => by
                  rw [hsm]
                  exact hrowsOkS (byteOf w' j') (byteOf_lt w' j') (fun hc => hocc ⟨j', hj', hc⟩)
              have hdisjT' : tab + 8192 ≤ o ∨ o + 4 * (k + ctpop w' + 8) ≤ tab :=
                table_disj_of_hdisj o tab k k0 nblk (ctpop w') (by have := ctpop_le w'; omega) hdisjT
              obtain ⟨e1, hrun1, hstep1, hi1, hk1, h01, hb1⟩ :=
                pos8Body_step_pos env s w' i k e p opk opi hpc hpre hopk hopi hvk hvi hent hread hi63 hw'
              have hfr1 := fun (n : String) (hn : n ∈ pos8Params) =>
                (denoteCode_params pos8Body.instrs env e1 s hrun1 pos8Params_body n hn)
              obtain ⟨e2, hrun2, hstep2, hpar2, hi010, hadd1⟩ :=
                pos8Groups_step_row e1 { s with pc := "if.end", pre := some "for.body" } w' i blk0 k o tab
                  (blockMem o w' (posBase blk0 i) k 8 s.mem) rfl rfl
                  hi1 ((hfr1 "%blk0" (by decide)).trans hbk) ((hfr1 "%out" (by decide)).trans hout)
                  hk1 h01 ((hfr1 "%tab" (by decide)).trans htab) hk63' hblk' hconv hrowsNow hdisjT'
              have hfr2 := fun (n : String) (hn : n ∈ pos8Params) => hpar2 n hn
              have hc64 : ctpop w' + k < 2 ^ 64 := by
                have := ctpop_le w'
                omega
              have hsum : BitVec.ofNat 64 (ctpop w') + BitVec.ofNat 64 k
                  = BitVec.ofNat 64 (k + ctpop w') := by
                rw [ofNat64_add_ofNat _ _ hc64, Nat.add_comm]
              have hi1' : lookupName e2 "%i.010" = some (.int 64 (BitVec.ofNat 64 i)) :=
                hi010.trans hi1
              have hNb2 : lookupName e2 "%nblk" = some (.int 64 (BitVec.ofNat 64 nblk)) :=
                (hpar2 "%nblk" (by decide)).trans ((hfr1 "%nblk" (by decide)).trans hNb)
              obtain ⟨e3, hrun3, hstep3, hk3, hinc3, hx3⟩ :=
                pos8Cleanup_step_more e2 { s with mem := (blockMem o w' (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" }
                  i (k + ctpop w') nblk "if.end" (.reg "%add1") rfl rfl rfl
                  (by rw [← hsum]; exact evalOperand_reg_of e2 _ _ _ hadd1) hi1' hNb2 hi64 hx
              have hfr3 := fun (n : String) (hn : n ∈ pos8Params) =>
                (denoteCode_params pos8Advance.instrs e2 e3
                  { s with mem := (blockMem o w' (posBase blk0 i) k 8 s.mem), pc := "cleanup", pre := some "if.end" } hrun3 pos8Params_cleanup n hn)
              have hwordNext : readBytes (blockMem o w' (posBase blk0 i) k 8 s.mem) (e + 8 * jj) 8
                  = some (natToBytes w.toNat 8) := by
                rw [blockMem_frame_tight o w' (posBase blk0 i) k s.mem (e + 8 * jj) 8 (by
                  rcases hdisjE with h | h
                  · exact Or.inl (by omega)
                  · refine Or.inr ?_
                    have hc := ctpop_le w'
                    omega) 8 (by omega)]
                rw [hsm]
                exact hwordS
              have hrowsNext : ∀ m, m < 256 → m ≠ byteOf w g →
                  readBytes (blockMem o w' (posBase blk0 i) k 8 s.mem) (tab + m * 32) 32
                    = some (pos8RowBytes m) := fun m hm hne =>
                (blockMem_read_row o w' (posBase blk0 i) k s.mem tab m hm hdisjT' 8 (by omega)).trans
                  (by rw [hsm]; exact hrowsOkS m hm hne)
              have hrowNext : readBytes (blockMem o w' (posBase blk0 i) k 8 s.mem)
                  (tab + byteOf w g * 32) 32 = none :=
                (blockMem_read_row o w' (posBase blk0 i) k s.mem tab (byteOf w g) (byteOf_lt w g)
                  hdisjT' 8 (by omega)).trans (by rw [hsm]; exact hrowS)
              have hs2 := state_mem_update_pc s (blockMem o w' (posBase blk0 i) k 8 s.mem)
                "for.body" (some "cleanup")
              have hkb2 : k + ctpop w' ≤ k0 + 64 * (i + 1) := by
                have := ctpop_le w'
                omega
              obtain hrec :=
                ih (i + 1) (k + ctpop w') (blockMem o w' (posBase blk0 i) k 8 s.mem) e3
                  { s with mem := (blockMem o w' (posBase blk0 i) k 8 s.mem), pc := "for.body", pre := some "cleanup" } "cleanup"
                  (.reg "%k.addr.1") (.reg "%inc") hr2 (by omega) rfl rfl rfl rfl
                  (evalOperand_reg_of e3 _ _ _ hk3)
                  (evalOperand_reg_of (("%k.addr.011", .int 64 (BitVec.ofNat 64 (k + ctpop w'))) :: e3)
                    _ "%inc" _ ((lookupName_cons_ne _ _ (by decide)).trans hinc3))
                  ((hfr3 "%ent" (by decide)).trans ((hfr2 "%ent" (by decide)).trans
                    ((hfr1 "%ent" (by decide)).trans hent)))
                  ((hfr3 "%blk0" (by decide)).trans ((hfr2 "%blk0" (by decide)).trans
                    ((hfr1 "%blk0" (by decide)).trans hbk)))
                  ((hfr3 "%nblk" (by decide)).trans ((hfr2 "%nblk" (by decide)).trans
                    ((hfr1 "%nblk" (by decide)).trans hNb)))
                  ((hfr3 "%out" (by decide)).trans ((hfr2 "%out" (by decide)).trans
                    ((hfr1 "%out" (by decide)).trans hout)))
                  ((hfr3 "%tab" (by decide)).trans ((hfr2 "%tab" (by decide)).trans
                    ((hfr1 "%tab" (by decide)).trans htab)))
                  hs2 hkb2 hwordNext hrowsNext hrowNext
              rw [hfuel]
              rw [runFuel_jump hstep1]
              rw [runFuel_jump hstep2]
              rw [runFuel_jump hstep3]
              simpa only [withEnv] using hrec

/-- An unreadable table row makes the whole run `ub`: block `j`'s mask word is
readable and non-zero, the row its group `g` selects is not, and every other row
of the table is — so the group's load is the instruction that fails, and the
failure survives the earlier blocks' stores because the output span is disjoint
from the table.

The witness is the block and the group, in the mask-word companion's form.  Its
`htab` premise (the whole table readable) becomes `hrowsOk`: every row but the
failing one.  That is not a weakening for convenience — a whole table readable
contradicts the unreadable row — and it is what makes the prefix complete, since
a block before `j` whose word holds the failing byte is `ub` at that group and
one whose word does not has all eight of its rows readable.  `hw` is the whole
condition on the word: `s1f_ke_pos8` guards only `if (!m)` and then reads a row
for every byte, including row `0` for a zero byte, so a zero word reads none.
The mask words here are `natToBytes w.toNat 8`, the same eight-byte encoding
`wordsOf` gives an element, so the companion's two halves describe one layout. -/
theorem entry_pos8_undefined_of_no_row (ent : List (BitVec 64)) (blk0 nblk k : Nat)
    (mem : Mem) (e o tab j g : Nat) (w : BitVec 64)
    (hnblk : nblk = ent.length)
    (hblk : 64 * (blk0 + nblk) + 63 < 2 ^ 32)
    (hj : j < nblk)
    (hg : g < 8)
    (hw : w ≠ 0)
    (hword : readBytes mem (e + 8 * j) 8 = some (natToBytes w.toNat 8))
    (hrowsOk : ∀ m, m < 256 → m ≠ byteOf w g →
      readBytes mem (tab + m * 32) 32 = some (pos8RowBytes m))
    (hrow : readBytes mem (tab + byteOf w g * 32) 32 = none)
    (hdisj : (e + 8 * ent.length ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ e) ∧
             (tab + 8192 ≤ o ∨ o + 4 * (k + 64 * ent.length + 8) ≤ tab))
    (hk63 : k + 64 * ent.length + 9 < 2 ^ 63) :
    runFuel entryCalls (3 * nblk + 3) entryPos8Function
      { (initState entryPos8Function
          [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
        = some .ub := by
  let S0 : State := { (initState entryPos8Function
    [.ptr e, .int 64 blk0, .int 64 nblk, .ptr o, .int 64 k, .ptr tab]) with mem := mem }
  obtain ⟨hpc0, hent0, hblk0, hNb, hout0, hk0, htab0⟩ := pos8_init ent blk0 nblk k mem e o tab
  have hz : nblk ≠ 0 := by omega
  have hnb64 : nblk < 2 ^ 64 := by omega
  obtain ⟨e1, hrun1, hstep1, _⟩ := pos8Entry_step_pos S0.env S0 nblk hpc0 hNb hnb64 hz
  have hfr := fun (n : String) (hn : n ∈ pos8Params) =>
    (denoteCode_params pos8Entry.instrs S0.env e1 S0 hrun1 (by decide) n hn)
  obtain hrun :=
    pos8_loop_run_row_ub blk0 nblk k o tab e j g w hblk (by rw [hnblk]; exact hk63)
      (by rw [hnblk]; exact hdisj.1) (by rw [hnblk]; exact hdisj.2) hj hg hw
      (j + 1) 0 k mem e1 { S0 with pc := "for.body", pre := some "entry" } "entry" (.reg "%k") (lit 64 0)
      (by omega) (by omega) rfl rfl rfl rfl
      (evalOperand_reg_of e1 _ _ _ ((hfr "%k" (by decide)).trans hk0))
      (by
        show evalOperand _ (.imm (.int 64 (BitVec.ofInt 64 0)))
          = some (.int 64 (BitVec.ofNat 64 0))
        rw [ofInt64_zero]
        rfl)
      ((hfr "%ent" (by decide)).trans hent0)
      ((hfr "%blk0" (by decide)).trans hblk0)
      ((hfr "%nblk" (by decide)).trans hNb)
      ((hfr "%out" (by decide)).trans hout0)
      ((hfr "%tab" (by decide)).trans htab0)
      rfl (by omega) hword hrowsOk hrow
  show runFuel entryCalls (3 * nblk + 2 + 1) entryPos8Function (withEnv S0.env S0) = some .ub
  rw [runFuel_jump hstep1]
  exact runFuel_mono_le (show 3 * (j + 1) + 1 ≤ 3 * nblk + 2 from by omega) hrun
end LeanLLVM.Vellum.JsonEntrySteps
