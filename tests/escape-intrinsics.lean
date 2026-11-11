/-
The sufficiency demonstration for the escape unit's intrinsic vocabulary.

`JsonEscapeIntrinsics` binds the five intrinsic spellings
`probes/install/ir/json-escape.inventory` names, and the census below checks that
set against the fixture's instrument.  What the census cannot show is that a step
of the escape body evaluates through those bindings, which is what the unit's
refinement needs: an environment that resolves a symbol is no use if reading one
call through it does not land on the model the statement is written in.  This file
takes that step for each distinct call form in the emission — the head of each step
of the escape body — so the statement's proof can be measured against them without
any part of that proof existing yet.

The step shape is `JsonEntrySteps`' and `JsonUtf8Steps`': the instruction is stated
at an **opaque environment** (`withEnv env s`) with the operands it reads as
hypotheses, and the conclusion adds one cell to that environment.  The argument
order and the result shapes are the emission's, and the second operand of each
multiply-add is left as an arbitrary operand whose value is given, because the
emission passes a literal there.

The two spellings the entry kernels already model (`ctpop.i64`, `cttz.i64`) get
their step here as well: the environment these steps are read at is
`escapeCalls`, and a step stated at `entryCalls` cannot be used at it.

Elaborated by `nix develop -c lake env lean tests/escape-intrinsics.lean`.  A
`#guard` or a failed proof stops elaboration with a nonzero exit status; no
compiler, service, clock or network is reached.
-/
import LeanLLVM.Refinement.JsonEscapeIntrinsics
import LeanLLVM.Refinement.JsonS1MasksIR

namespace EscapeIntrinsics

open LeanLLVM
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.JsonEscapeIntrinsics
open LeanLLVM.Refinement.JsonS1MasksIR (evalInstr_call evalOperands_cons)

/-! ### The staging form and the operand readers -/

/-- A state seen as its environment, as the step modules stage a body's read. -/
def withEnv (env : Env) (s : State) : State := { s with env := env }

/-- A register reads the value its name is bound to. -/
theorem evalOperand_reg_of (env : Env) (s : State) (n : String) (v : Value)
    (h : lookupName env n = some v) : evalOperand (withEnv env s) (.reg n) = some v := by
  simp only [withEnv, evalOperand, h]

/-- A two-operand argument list reads to the two values its operands do.  Every
call in this unit's emission takes two operands. -/
theorem evalOperands_pair {s : State} {t₁ t₂ : Ty} {o₁ o₂ : Operand} {v₁ v₂ : Value}
    (h₁ : evalOperand s o₁ = some v₁) (h₂ : evalOperand s o₂ = some v₂) :
    evalOperands s [(t₁, o₁), (t₂, o₂)] = some [v₁, v₂] := by
  simp [evalOperands, h₁, h₂]

/-- A vector literal reads to the lane list it spells, with the list's own length
as the lane count. -/
theorem evalOperand_vector_lit (s : State) (w : Nat) (l : List (BitVec w)) :
    evalOperand s (.imm (.vector w l)) = some (.vec l.length w l) := rfl

/-! ### The scalar steps: `ctpop.i64`, `cttz.i64`, `umin.i32` -/

/-- `%d = call i64 @llvm.ctpop.i64(i64 %src)`. -/
theorem escape_step_call_ctpop64 (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 64) "llvm.ctpop.i64" [((.int 64), (.reg src))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (ctpop x))) :: env) s) := by
  have ha : evalOperands (withEnv env s) [((.int 64), (.reg src))]
      = some [.int 64 x] :=
    evalOperands_cons (evalOperand_reg_of env s src (.int 64 x) h) rfl
  rw [evalInstr_call ha (escapeCalls_ctpop64 x s.mem s.next)]
  simp only [withEnv]

/-- `%d = call i64 @llvm.cttz.i64(i64 %src, i1 <flag>)`.  The flag is the
emission's `i1 true`, and the value is the model's at either flag. -/
theorem escape_step_call_cttz (env : Env) (s : State) (d src : String) (x : BitVec 64)
    (flag : BitVec 1) (h : lookupName env src = some (.int 64 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 64) "llvm.cttz.i64"
          [((.int 64), (.reg src)), ((.int 1), (.imm (.int 1 flag)))]) =
      some (withEnv ((d, .int 64 (BitVec.ofNat 64 (cttz x))) :: env) s) := by
  have ha : evalOperands (withEnv env s)
      [((.int 64), (.reg src)), ((.int 1), (.imm (.int 1 flag)))]
      = some [.int 64 x, .int 1 flag] :=
    evalOperands_cons (evalOperand_reg_of env s src (.int 64 x) h)
      (evalOperands_cons (by rfl) rfl)
  rw [evalInstr_call ha (escapeCalls_cttz x flag s.mem s.next)]
  simp only [withEnv]

/-- `%d = call i32 @llvm.umin.i32(i32 %a, i32 %b)`, with the **second** operand
left as an arbitrary operand: the emission passes `i32 8` there, and the model is
read at the call's own order rather than reversed. -/
theorem escape_step_call_umin32 (env : Env) (s : State) (d a : String) (b : Operand)
    (x y : BitVec 32) (ha : lookupName env a = some (.int 32 x))
    (hb : evalOperand (withEnv env s) b = some (.int 32 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 32) "llvm.umin.i32" [((.int 32), (.reg a)), ((.int 32), b)]) =
      some (withEnv ((d, .int 32 (umin x y)) :: env) s) := by
  rw [evalInstr_call
    (evalOperands_pair (evalOperand_reg_of env s a (.int 32 x) ha) hb)
    (escapeCalls_umin32 x y s.mem s.next)]
  simp only [withEnv]

/-- The emitted line: `%cond = tail call i32 @llvm.umin.i32(i32 %cast36, i32 8)`. -/
theorem escape_step_call_umin32_literal (env : Env) (s : State) (d a : String)
    (x c : BitVec 32) (ha : lookupName env a = some (.int 32 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d (.int 32) "llvm.umin.i32"
          [((.int 32), (.reg a)), ((.int 32), (.imm (.int 32 c)))]) =
      some (withEnv ((d, .int 32 (umin x c)) :: env) s) :=
  escape_step_call_umin32 env s d a (.imm (.int 32 c)) x c ha (by rfl)

/-! ### The two multiply-adds

Both are stated with a register first operand and an arbitrary second operand,
because that is how the emission spells them: `%19` against a literal
`<i8 16, i8 1, …>`, then `%20` against a literal `<i16 256, i16 1, 0, …>`.  The
lane counts are the call's — `<16 x i8>` into `<8 x i16>`, then `<8 x i16>` into
`<4 x i32>` — and each result is the model at the lane pair. -/

/-- `%d = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)`. -/
theorem escape_step_call_pmaddUbSw (env : Env) (s : State) (d a : String) (b : Operand)
    (x y : List (BitVec 8)) (ha : lookupName env a = some (.vec 16 8 x))
    (hb : evalOperand (withEnv env s) b = some (.vec 16 8 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d v8i16 "llvm.x86.ssse3.pmadd.ub.sw.128" [(v16i8, (.reg a)), (v16i8, b)]) =
      some (withEnv ((d, .vec 8 16 (pmaddUbSw x y)) :: env) s) := by
  rw [evalInstr_call
    (evalOperands_pair (evalOperand_reg_of env s a (.vec 16 8 x) ha) hb)
    (escapeCalls_pmaddUbSw x y s.mem s.next)]
  simp only [withEnv]

/-- The emitted line: the second operand is the literal `<i8 16, i8 1, …>` — sixteen
lanes, as the `.vector` literal's length is its lane count. -/
theorem escape_step_call_pmaddUbSw_literal (env : Env) (s : State) (d a : String)
    (x tab : List (BitVec 8)) (hlen : tab.length = 16)
    (ha : lookupName env a = some (.vec 16 8 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d v8i16 "llvm.x86.ssse3.pmadd.ub.sw.128"
          [(v16i8, (.reg a)), (v16i8, (.imm (.vector 8 tab)))]) =
      some (withEnv ((d, .vec 8 16 (pmaddUbSw x tab)) :: env) s) := by
  have hb : evalOperand (withEnv env s) (.imm (.vector 8 tab)) = some (.vec 16 8 tab) := by
    rw [evalOperand_vector_lit, hlen]
  exact escape_step_call_pmaddUbSw env s d a (.imm (.vector 8 tab)) x tab ha hb

/-- `%d = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)`. -/
theorem escape_step_call_pmaddWd (env : Env) (s : State) (d a : String) (b : Operand)
    (x y : List (BitVec 16)) (ha : lookupName env a = some (.vec 8 16 x))
    (hb : evalOperand (withEnv env s) b = some (.vec 8 16 y)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d v4i32 "llvm.x86.sse2.pmadd.wd" [(v8i16, (.reg a)), (v8i16, b)]) =
      some (withEnv ((d, .vec 4 32 (pmaddWd x y)) :: env) s) := by
  rw [evalInstr_call
    (evalOperands_pair (evalOperand_reg_of env s a (.vec 8 16 x) ha) hb)
    (escapeCalls_pmaddWd x y s.mem s.next)]
  simp only [withEnv]

/-- The emitted line: the second operand is the literal `<i16 256, i16 1, 0, …>` at
eight lanes. -/
theorem escape_step_call_pmaddWd_literal (env : Env) (s : State) (d a : String)
    (x tab : List (BitVec 16)) (hlen : tab.length = 8)
    (ha : lookupName env a = some (.vec 8 16 x)) :
    evalInstr escapeCalls (withEnv env s)
        (.call d v4i32 "llvm.x86.sse2.pmadd.wd"
          [(v8i16, (.reg a)), (v8i16, (.imm (.vector 16 tab)))]) =
      some (withEnv ((d, .vec 4 32 (pmaddWd x tab)) :: env) s) := by
  have hb : evalOperand (withEnv env s) (.imm (.vector 16 tab)) = some (.vec 8 16 tab) := by
    rw [evalOperand_vector_lit, hlen]
  exact escape_step_call_pmaddWd env s d a (.imm (.vector 16 tab)) x tab ha hb

/-! ### What the steps do not touch

Each step binds one register and leaves the memory, the allocator cursor, the block
and the predecessor where they were.  The frame clause of any statement over this
body reads its memory through that, and the environment's own statement of it —
`escapeCalls_mem_next`, that every arm returns the caller's memory and cursor — is
in the vocabulary module rather than restated here per spelling.
-/

/-! ### The census

This file is the census: the escape unit's call set, enumerated by instrument
rather than recalled, against the spellings `escapeCalls` binds.  The inventory is
the fixture's instrument and not a list written here — it is generated by
`probes/install/ir/capture-escape.sh` and committed — so the spellings compared are
the emission's own.  It also lists the fixture's own definitions' calls
(`@us_dec_x`, `@xl_batch`), which no call environment resolves (a call to a defined
function is the linker's, not an intrinsic's), so the comparison is over the
`llvm.*` targets, which are exactly the spellings a `Calls` environment has to
supply.

The comparison is here and not in the vocabulary module because this file is
compiled from source on every run: a `#guard` in a compiled module reads its
`include_str` when that module is elaborated, so an inventory regenerated afterwards
would be compared only when something else forced a rebuild.

`escapeBindings` is the bound set as pairs of a spelling and an argument list it
must resolve — the pairs are what makes the list checkable, since each is sent
through `escapeCalls` — and `unmodelled` is the failure set.  Both sides are
asserted non-empty before the comparison is read (an instrument that finds nothing
agrees with an environment that binds nothing), and the controls show the detector
reporting a call it should find and rejecting a spelling it should not serve. -/

/-- The committed inventory this unit's capture wrote. -/
def escapeInventory : String := include_str "../probes/install/ir/json-escape.inventory"

/-- The target of one inventory line, without its `@`, when the line is a call
line.  The inventory writes one space between `call` and the target. -/
def callTarget? (line : String) : Option String :=
  match line.splitOn " " with
  | ["call", target] =>
      if target.startsWith "@" then some (String.ofList (target.toList.drop 1)) else none
  | _ => none

/-- Every call target an inventory text names. -/
def inventoryCallTargets (text : String) : List String :=
  (text.splitOn "\n").filterMap callTarget?

/-- The intrinsic call set: the `llvm.*` targets, which are the spellings a call
environment resolves. -/
def inventoryIntrinsics (text : String) : List String :=
  (inventoryCallTargets text).filter (fun s => s.startsWith "llvm.")

/-- The bound set, as each spelling together with an argument list of the shape the
environment matches for it. -/
def escapeBindings : List (String × List Value) :=
  [("llvm.ctpop.i64", [.int 64 0]),
   ("llvm.cttz.i64", [.int 64 0, .int 1 0]),
   ("llvm.umin.i32", [.int 32 0, .int 32 0]),
   ("llvm.x86.sse2.pmadd.wd", [.vec 8 16 (List.replicate 8 0), .vec 8 16 (List.replicate 8 0)]),
   ("llvm.x86.ssse3.pmadd.ub.sw.128",
     [.vec 16 8 (List.replicate 16 0), .vec 16 8 (List.replicate 16 0)])]

/-- The spellings the environment binds. -/
def escapeModelled : List String := escapeBindings.map (·.1)

/-- Whether one spelling at one argument list resolves.  A binding named in
`escapeBindings` that does not is a spelling the census claims and `escapeCalls`
does not serve. -/
def escapeCallsBinds (sym : String) (args : List Value) : Bool :=
  (escapeCalls sym args [] 0).isSome

/-- The spellings a text's call set names and the environment does not bind: the
census's failure set, empty exactly when the emission's calls are all modelled. -/
def unmodelled (text : String) : List String :=
  (inventoryIntrinsics text).filter (fun s => !escapeModelled.contains s)

-- the inventory names calls at all
#guard 0 < (inventoryIntrinsics escapeInventory).length

-- the environment claims to bind spellings at all
#guard 0 < escapeModelled.length

-- every spelling the vocabulary says is bound resolves at the shape it names
#guard escapeBindings.all (fun (s, a) => escapeCallsBinds s a)

-- the emission calls nothing the environment does not bind
#guard (unmodelled escapeInventory).isEmpty

-- the detector finds a call when one is written
#guard inventoryIntrinsics "call @llvm.memcpy.p0.p0.i64\n" = ["llvm.memcpy.p0.p0.i64"]

-- the detector reports an unmodelled spelling as one; `llvm.memcpy` is not a
-- spelling the escape emission has, which is the point of the control: the
-- comparison above is about the inventory, and this shows it would catch the
-- first such spelling to enter it
#guard (unmodelled "call @llvm.memcpy.p0.p0.i64\n").isEmpty = false

-- a near-miss spelling is refused rather than served by a same-named model at
-- another width: `umin` is bound at `i32` only, as the emission spells it
#guard escapeCallsBinds "llvm.umin.i64" [.int 64 0, .int 64 0] = false

/-! ### Axiom footprints -/

/-- info: 'EscapeIntrinsics.escape_step_call_ctpop64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_step_call_ctpop64

/-- info: 'EscapeIntrinsics.escape_step_call_cttz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_step_call_cttz

/-- info: 'EscapeIntrinsics.escape_step_call_umin32' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_step_call_umin32

/-- info: 'EscapeIntrinsics.escape_step_call_pmaddUbSw' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_step_call_pmaddUbSw

/-- info: 'EscapeIntrinsics.escape_step_call_pmaddWd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escape_step_call_pmaddWd

end EscapeIntrinsics
