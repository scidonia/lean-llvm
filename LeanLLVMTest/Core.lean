/-
Checks for the public interface, written from outside the library module.

Behavioural checks are `#guard`s over the parser, the printer and the
executable semantics; the semantic checks are the certified passes applied to a
concrete program; the kernel checks pin that the soundness theorems rest on the
standard axioms only.
-/
import LeanLLVM

open LeanLLVM

def sample : String :=
"define i32 @main(i32 %x) {
entry:
  %a = add i32 %x, 1
  %t = add i32 1, 2
  %c = icmp eq i32 %t, 3
  br i1 %c, label %yes, label %no
yes:
  ret i32 %a
no:
  ret i32 %x
}
"

def sampleModule : Module :=
  match parseModule sample with
  | .ok m => m
  | .error _ => ⟨[], []⟩

def sampleFunction : Function :=
  match sampleModule.functions with
  | f :: _ => f
  | [] => ⟨"", .void, [], []⟩

-- The parser accepts the modelled subset.
#guard
  match parseModule sample with
  | .ok _ => true
  | .error _ => false

-- The printer emits canonical textual IR that parses back to the same AST.
#guard
  match parseModule (Module.render sampleModule) with
  | .ok m => m = sampleModule
  | .error _ => false

-- A function definition's header is checked for attributes the semantics does
-- not model.  `sample` above is the control: an attribute-free header parses.
-- An attribute that constrains the returned value, or one that changes what the
-- function promises its caller, is refused with a diagnostic naming it rather
-- than parsed past and printed back without it.
def returnAttrSample : String :=
"define range(i64 0, 1) i64 @f(i64 %x) {
entry:
  ret i64 %x
}
"

def functionAttrSample : String :=
"define i64 @f(i64 %x) noreturn {
entry:
  ret i64 %x
}
"

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

#guard
  match parseModule returnAttrSample with
  | .error e => mentions e "unsupported" && mentions e "range"
  | .ok _ => false

#guard
  match parseModule functionAttrSample with
  | .error e => mentions e "unsupported" && mentions e "noreturn"
  | .ok _ => false

-- A call is modelled end to end: it round-trips through the printer, the
-- environment supplies its result, and an unresolved call is `ub`.
def callSample : String :=
"declare i64 @f(i64)

define i64 @caller(i64 %arg) {
entry:
  %r = call i64 @f(i64 %arg)
  ret i64 %r
}
"

#guard
  match parseModule callSample with
  | .ok m => m.render = callSample
  | .error _ => false

/-- An environment in which `f` returns its argument plus one and leaves the
caller's memory and allocator exactly as it found them. -/
def plusOneEnv : Calls := fun callee args mem next =>
  if callee = "f" then
    match args with
    | [.int 64 x] => some { ret := .int 64 (x + 1), mem := mem, next := next }
    | _ => none
  else none

#guard
  match parseModule callSample with
  | .ok m =>
      match m.functions with
      | [f] => run plusOneEnv f [.int 64 41] =
          some (.ret (some (.int 64 42)) []) ∧
          run noCalls f [.int 64 41] = some .ub
      | _ => false
  | .error _ => false

-- A 64-bit store is read back by a 64-bit load at the same address, including
-- when a later store overwrites it.
def memory64Sample : String :=
"define i64 @mem64() {
entry:
  %p = alloca i64, align 8
  store i64 1234567890123456789, ptr %p
  %v = load i64, ptr %p
  ret i64 %v
}
"

#guard
  match parseModule memory64Sample with
  | .ok m =>
      match m.functions with
      | [f] =>
          match run noCalls f [] with
          | some (.ret (some v) _) => v == .int 64 (BitVec.ofInt 64 1234567890123456789)
          | _ => false
      | _ => false
  | .error _ => false

def memory64Overwrite : String :=
"define i64 @mem64b() {
entry:
  %p = alloca i64, align 8
  store i64 1, ptr %p
  store i64 2, ptr %p
  %v = load i64, ptr %p
  ret i64 %v
}
"

#guard
  match parseModule memory64Overwrite with
  | .ok m =>
      match m.functions with
      | [f] =>
          match run noCalls f [] with
          | some (.ret (some v) _) => v == .int 64 2
          | _ => false
      | _ => false
  | .error _ => false

-- The semantics computes the taken branch (`%a` is 3).
#guard run noCalls sampleFunction [.int 32 (BitVec.ofInt 32 2)] =
  some (.ret (some (.int 32 (BitVec.ofInt 32 3))) [])

-- The semantics computes the other input.
#guard run noCalls sampleFunction [.int 32 (BitVec.ofInt 32 7)] =
  some (.ret (some (.int 32 (BitVec.ofInt 32 8))) [])

-- Constant propagation makes the comparison's operands literal and the branch
-- condition folds; the conditional edge disappears.
#guard
  match (optimizeFunction sampleFunction).blocks with
  | b :: _ => b.term = .br "yes"
  | [] => false

-- The pipeline leaves observable behaviour unchanged on this program.
#guard run noCalls sampleFunction [.int 32 (BitVec.ofInt 32 2)] =
  run noCalls (optimizeFunction sampleFunction) [.int 32 (BitVec.ofInt 32 2)]

#guard run noCalls sampleFunction [.int 32 (BitVec.ofInt 32 7)] =
  run noCalls (optimizeFunction sampleFunction) [.int 32 (BitVec.ofInt 32 7)]

-- Refinement is what the pipeline theorem provides.
example : ∀ calls, Refines calls (optimizeFunction sampleFunction) sampleFunction :=
  fun calls => optimisationPipeline_sound calls sampleFunction

/-- info: 'LeanLLVM.constantPropagation_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.constantPropagation_sound

/-- info: 'LeanLLVM.optimisationPipeline_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.optimisationPipeline_sound

/-- Memory: `alloca`, `store`, `load` and arithmetic round-trip through the
byte-addressed memory model. -/
def memorySample : String :=
"define i32 @mem() {
entry:
  %p = alloca i32, align 4
  store i32 41, ptr %p
  %v = load i32, ptr %p
  %r = add i32 %v, 1
  ret i32 %r
}
"

def memoryFunction : Function :=
  match parseModule memorySample with
  | .ok ⟨_, f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

def returnsValue (o : Option Outcome) (v : Value) : Bool :=
  match o with
  | some (.ret (some w) _) => w = v
  | _ => false

#guard returnsValue (run noCalls memoryFunction []) (.int 32 (BitVec.ofInt 32 42))

/-- Signed division truncates toward zero and `srem` follows the dividend's
sign, as LLVM specifies; `-5 / 2 = -2`, `-5 % 2 = -1`. -/
def signedSample : String :=
"define i32 @signed() {
entry:
  %d = sdiv i32 -5, 2
  %r = srem i32 -5, 2
  %s = mul i32 %d, 10
  %t = add i32 %s, %r
  ret i32 %t
}
"

def signedFunction : Function :=
  match parseModule signedSample with
  | .ok ⟨_, f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

#guard returnsValue (run noCalls signedFunction []) (.int 32 (BitVec.ofInt 32 (-21)))

-- The pipeline preserves the signed-division program's behaviour.
#guard run noCalls signedFunction [] = run noCalls (optimizeFunction signedFunction) []

-- The printer keeps the type on register operands where the grammar requires
-- it (`store`'s value, `select`'s arms), and omits `, align 0` from an
-- align-less `alloca`.  Both forms are common LLVM syntax and both used to
-- print to IR that `llvm-as` rejects.
def roundTripSample : String :=
"define i32 @roundtrip(i32 %x, ptr %p) {
entry:
  %a = alloca i32
  store i32 %x, ptr %p
  %c = icmp eq i32 %x, 0
  %s = select i1 %c, i32 %x, i32 5
  ret i32 %s
}
"

#guard
  match parseModule roundTripSample with
  | .ok m =>
      match parseModule (Module.render m) with
      | .ok m' => m' = m
      | .error _ => false
  | .error _ => false

-- The vector sample: the load of `<32 x i8>`, the lane-wise comparison and
-- operation, the mask `bitcast` and the `splat` operand the emitted classifier
-- uses.  The text must parse to these exact constructors, and the printed form
-- must parse back to the same module, so a wrong `<n x iw>` type, a `splat`
-- without its element type, or a `bitcast` without its result width fails here
-- rather than only in the emitted classifier.
def vectorRoundTripSample : String :=
"define i32 @vector_roundtrip(ptr %p) {
entry:
  %v = load <32 x i8>, ptr %p
  %c = icmp eq <32 x i8> %v, splat (i8 34)
  %d = icmp ult <32 x i8> %v, splat (i8 2)
  %o = or <32 x i1> %c, %d
  %a = add <32 x i8> %v, splat (i8 -9)
  %m = bitcast <32 x i1> %o to i32
  ret i32 %m
}
"

#guard
  match parseModule vectorRoundTripSample with
  | .ok ⟨_, f :: _⟩ =>
      match f.blocks with
      | [b] =>
          b.instrs =
            [ .load "%v" (.vec 32 (.int 8)) (.reg "%p"),
              .icmpVec "%c" .eq 32 8 (.reg "%v") (.imm (.splat 32 8 34)),
              .icmpVec "%d" .ult 32 8 (.reg "%v") (.imm (.splat 32 8 2)),
              .binopVec "%o" .or 32 1 (.reg "%c") (.reg "%d"),
              .binopVec "%a" .add 32 8 (.reg "%v") (.imm (.splat 32 8 (BitVec.ofInt 8 (-9)))),
              .bitcastMask "%m" 32 (.reg "%o") ]
      | _ => false
  | _ => false

#guard
  match parseModule vectorRoundTripSample with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

-- Strength reduction fires on `mul i32 %x, 2` and preserves behaviour.
def strengthSample : String :=
"define i32 @twice(i32 %x) {
entry:
  %y = mul i32 %x, 2
  ret i32 %y
}
"

def strengthFunction : Function :=
  match parseModule strengthSample with
  | .ok ⟨_, f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

#guard
  match (strengthReduction.run strengthFunction).blocks with
  | b :: _ =>
      match b.instrs with
      | [i] => i = .binop "%y" .shl 32 (.reg "%x") (.imm (.int 32 (BitVec.ofNat 32 1)))
      | _ => false
  | [] => false

#guard run noCalls strengthFunction [.int 32 (BitVec.ofInt 32 21)] =
  run noCalls (strengthReduction.run strengthFunction) [.int 32 (BitVec.ofInt 32 21)]

/-- info: 'LeanLLVM.strengthReduction_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.strengthReduction_sound

/-- The byte-offset `getelementptr`: a pointer and a byte count, printed in the
canonical form the parser accepts back. -/
def gepSample : String :=
"define ptr @gep(ptr %p, i64 %k) {
entry:
  %q = getelementptr inbounds i8, ptr %p, i64 %k
  ret ptr %q
}
"

#guard
  match parseModule gepSample with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

/-- `getelementptr` where a byte-walking body uses it: the address of one byte
inside a word, read back through the memory model.  The offset is a parameter,
so the check below reads every offset of the word rather than only the first,
and the negative one is the undefined offset the model refuses. -/
def gepByteProgram (off : String) : String :=
"define i32 @gep_byte(ptr %p) {
entry:
  store i32 16909060, ptr %p
  %q = getelementptr inbounds i8, ptr %p, i64 " ++ off ++ "
  %v = load i8, ptr %q
  %w = zext i8 %v to i32
  ret i32 %w
}
"

def gepByteRun (off : String) : Option Outcome :=
  match parseModule (gepByteProgram off) with
  | .ok ⟨_, f :: _⟩ => run noCalls f [.ptr 1]
  | _ => none

-- `16909060` is `0x01020304`, which the byte-addressed memory holds as
-- `04 03 02 01`, so the byte at offset `k` of the word is `4 - k`.
#guard returnsValue (gepByteRun "0") (.int 32 (BitVec.ofNat 32 4))
#guard returnsValue (gepByteRun "1") (.int 32 (BitVec.ofNat 32 3))
#guard returnsValue (gepByteRun "2") (.int 32 (BitVec.ofNat 32 2))
#guard returnsValue (gepByteRun "3") (.int 32 (BitVec.ofNat 32 1))

-- Past the word the byte was never written, and a negative offset is undefined
-- rather than a read of an address below the base: both are `ub`.
#guard gepByteRun "4" = some .ub
#guard gepByteRun "-1" = some .ub

-- The step's facts, restated from `LeanLLVM.Semantics`: the accepting case with
-- the element-type scaling, the `i8` case where the scaling is the byte count
-- the earlier model computed, the refusal the negative index is, the refusal of
-- each other operand shape, and the memory it leaves alone.  A `#guard` above
-- observes the step on values this file chose; these are the statements a later
-- proof composes with, and each is pinned below to the standard axioms.
example {calls : Calls} {s : State} {d : String} {elemTy : Ty} {base off : Operand}
    {a w : Nat} {n : BitVec w} (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d elemTy base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat * elemTy.sizeBytes))) :=
  evalInstr_gep hb ho hpos

example {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a w : Nat} {n : BitVec w} (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d (.int 8) base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat))) :=
  evalInstr_gep_i8 hb ho hpos

example {calls : Calls} {s : State} {d : String} {elemTy : Ty} {base off : Operand}
    {a w : Nat} {n : BitVec w} (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hneg : ¬ (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d elemTy base off) = none :=
  evalInstr_gep_negative hb ho hneg

example {calls : Calls} {s : State} {d : String} {elemTy : Ty} {base off : Operand}
    {v : Value} (hb : evalOperand s base = some v) (hv : ∀ a, v ≠ .ptr a) :
    evalInstr calls s (.gep d elemTy base off) = none :=
  evalInstr_gep_none_of_base hb hv

example {calls : Calls} {s : State} {d : String} {elemTy : Ty} {base off : Operand}
    {a : Nat} (hb : evalOperand s base = some (.ptr a)) {v : Value}
    (ho : evalOperand s off = some v) (hv : ∀ w n, v ≠ .int w n) :
    evalInstr calls s (.gep d elemTy base off) = none :=
  evalInstr_gep_none_of_off hb ho hv

example {calls : Calls} {s : State} {d : String} {elemTy : Ty} {base off : Operand}
    (h : evalOperand s base = none ∨ evalOperand s off = none) :
    evalInstr calls s (.gep d elemTy base off) = none :=
  evalInstr_gep_none_of_unbound h

example {calls : Calls} {s s' : State} {d : String} {elemTy : Ty} {base off : Operand}
    (h : evalInstr calls s (.gep d elemTy base off) = some s') : s'.mem = s.mem :=
  evalInstr_gep_mem h

/-- info: 'LeanLLVM.evalInstr_gep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep

/-- info: 'LeanLLVM.evalInstr_gep_i8' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_i8

/-- info: 'LeanLLVM.evalInstr_gep_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_negative

/-- info: 'LeanLLVM.evalInstr_gep_none_of_base' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_none_of_base

/-- info: 'LeanLLVM.evalInstr_gep_none_of_off' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_none_of_off

/-- info: 'LeanLLVM.evalInstr_gep_none_of_unbound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_none_of_unbound

/-- info: 'LeanLLVM.evalInstr_gep_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep_mem

-- The readback lemma the byte walk rests on, restated: a range the body read
-- supplies each of its bytes at the offset the body asks for.
example {m : Mem} {addr n : Nat} {bs : List UInt8}
    (h : readBytes m addr n = some bs) {k : Nat} (hk : k < n) :
    readByte m (addr + k) = some (bs.getD k 0) :=
  readByte_of_readBytes h hk

/-- info: 'LeanLLVM.readByte_of_readBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.readByte_of_readBytes

/-! ### `phi`

The instruction's text, its selection, and the non-interference theorem that
says adding it changes no existing run.  The pins are the load-bearing ones: a
`phi`-free program's outcome is the same whatever predecessor its starting state
carries.  The round trip is the parser/printer half.
-/

/-- A loop whose `phi` takes a different value on entry than on the back-edge,
printed in the canonical form. -/
def phiSample : String :=
"define i32 @loop() {
entry:
  br label %head
head:
  %i = phi i32 [ 0, %entry ], [ %j, %body ]
  %c = icmp ult i32 %i, 3
  br i1 %c, label %body, label %exit
body:
  %j = add i32 %i, 1
  br label %head
exit:
  ret i32 %i
}
"

#guard
  match parseModule phiSample with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

-- The instruction reaches the AST with its type and its two labelled entries in
-- order, so a printer or parser that dropped either would fail here.
#guard
  match parseModule phiSample with
  | .ok ⟨_, f :: _⟩ =>
      match f.findBlock "head" with
      | some b =>
          b.instrs.head? = some (.phi "%i" (.int 32)
            [("entry", .imm (.int 32 0)), ("body", .reg "%j")])
      | none => false
  | _ => false

-- Running it returns 3, which is the answer only edge timing produces: the
-- entry value is 0 and the loop needs three back-edges.
#guard
  match parseModule phiSample with
  | .ok ⟨_, f :: _⟩ => run noCalls f [] = some (.ret (some (.int 32 3)) [])
  | _ => false

/-- Non-interference, restated: a `phi`-free function's run is the same from a
state and from that state with any predecessor whatever.  The statement is
spelled out here so a narrowing of the theorem fails this file. -/
example (f : Function) (hf : f.phiFree = true) (n : Nat) (s : State)
    (q : Option String) :
    runFuel noCalls n f (s.setPre q) = runFuel noCalls n f s :=
  runFuel_setPre hf n s q

/-- The same fact between two states that agree on every field but the
predecessor. -/
example (f : Function) (hf : f.phiFree = true) {s t : State}
    (h : s.SameExceptPre t) (n : Nat) :
    runFuel noCalls n f s = runFuel noCalls n f t :=
  runFuel_sameExceptPre hf h n

/-- And at the initial state, which is the claim that existing runs — the ones
recorded before `phi` existed — are unchanged. -/
example (f : Function) (hf : f.phiFree = true) (n : Nat) (args : List Value)
    (q : Option String) :
    runFuel noCalls n f ((initState f args).setPre q) =
      runFuel noCalls n f (initState f args) :=
  runFuel_init_setPre hf n args q

/-- info: 'LeanLLVM.runFuel_setPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.runFuel_setPre

/-- info: 'LeanLLVM.runFuel_sameExceptPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.runFuel_sameExceptPre

/-- info: 'LeanLLVM.runFuel_init_setPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.runFuel_init_setPre

/-- info: 'LeanLLVM.evalInstr_phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi

/-- info: 'LeanLLVM.evalInstr_phi_missing' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi_missing

/-- info: 'LeanLLVM.evalInstr_phi_no_pred' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi_no_pred

/-- info: 'LeanLLVM.step_setPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.step_setPre

/-! The rest of the chain, pinned.

`runFuel_init_setPre` is the claim; these are the lemmas it is built from, and
`AGENTS.md` asks for a footprint pin on every theorem that carries a soundness
claim.  The helpers the chain uses (`evalOperand_setPre`, `evalOperands_setPre`,
`storeValue_setPre`) and the `phi` facts the proof layers consume are here too, so
a widening — a `Classical.choice` arriving through a rewrite, or a statement
narrowed to a special case — changes this file rather than passing unnoticed.
-/

/-- info: 'LeanLLVM.evalInstr_setPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_setPre

/-- info: 'LeanLLVM.denoteCode_setPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.denoteCode_setPre

/-- info: 'LeanLLVM.execTerm_setPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.execTerm_setPre

/-- info: 'LeanLLVM.step_sameExceptPre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.step_sameExceptPre

/-- info: 'LeanLLVM.evalInstr_pre_of_not_phi' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_pre_of_not_phi

/-- info: 'LeanLLVM.evalOperand_setPre' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.evalOperand_setPre

/-- info: 'LeanLLVM.evalOperands_setPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.evalOperands_setPre

/-- info: 'LeanLLVM.storeValue_setPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.storeValue_setPre

/-- info: 'LeanLLVM.evalInstr_phi_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi_mem

/-- info: 'LeanLLVM.evalInstr_phi_env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi_env

/-- info: 'LeanLLVM.phiIncoming_map' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.phiIncoming_map

/-! The chain's statements, spelled out.

Each `example` restates a member of the non-interference chain in full and
discharges it by the theorem, so a narrowed statement — an extra hypothesis, a
special case in place of the general one — fails here rather than at a consumer.
-/

example {calls : Calls} (i : Instr) (hi : i.isPhi = false) (s : State)
    (p : Option String) :
    evalInstr calls (s.setPre p) i = (evalInstr calls s i).map (·.setPre p) :=
  evalInstr_setPre i hi s p

example (calls : Calls) (is : List Instr) (h : ∀ i ∈ is, i.isPhi = false)
    (s : State) (p : Option String) :
    denoteCode calls is (s.setPre p) = (denoteCode calls is s).map (·.setPre p) :=
  denoteCode_setPre calls is h s p

example (s : State) (p : Option String) (t : Term) :
    execTerm (s.setPre p) t = (execTerm s t).setPre p :=
  execTerm_setPre s p t

example {calls : Calls} {f : Function} (hf : f.phiFree = true) (s : State)
    (p : Option String) :
    step calls f (s.setPre p) = (step calls f s).setPre p :=
  step_setPre hf s p

example {calls : Calls} {f : Function} (hf : f.phiFree = true) {s t : State}
    (h : s.SameExceptPre t) :
    Ctrl.SameExceptPre (step calls f s) (step calls f t) :=
  step_sameExceptPre hf h

/-! The supporting lemmas, pinned.  Each is a step the chain or the parser's
checks rest on; none is left unpinned, including the `rfl` conveniences, so a
proof that starts to depend on a choice axiom shows up here. -/

/-- info: 'LeanLLVM.Function.phiFree_block' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.Function.phiFree_block

/-- info: 'LeanLLVM.findBlockList_mem' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.findBlockList_mem

/-- info: 'LeanLLVM.Ctrl.sameExceptPre_setPre' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanLLVM.Ctrl.sameExceptPre_setPre

/-- info: 'LeanLLVM.State.setPre_eq_of_sameExceptPre' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_eq_of_sameExceptPre

/-- info: 'LeanLLVM.State.sameExceptPre_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.sameExceptPre_refl

/-- info: 'LeanLLVM.State.bind_setPre' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.bind_setPre

/-- info: 'LeanLLVM.evalInstr_phi_subst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_phi_subst

/-- info: 'LeanLLVM.State.setPre_pc' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_pc

/-- info: 'LeanLLVM.State.setPre_env' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_env

/-- info: 'LeanLLVM.State.setPre_mem' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_mem

/-- info: 'LeanLLVM.State.setPre_next' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_next

/-- info: 'LeanLLVM.State.setPre_self' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.State.setPre_self

/-! ### Surfaces the parser accepts and drops

Four pieces of LLVM's text that the model does not represent: the `tail` marker on
a call, a definition's linkage and calling convention, the `samesign` flag on an
integer comparison, and a call written without a destination register.  Each is
checked the same way — the construct parses to the AST the same program without it
parses to, and the program runs to the same answer.  The first half fails a parser
that dropped something else or kept the token in a field; the second fails a
semantics that gave the construct a meaning.  The reason each is droppable is with
the parser, at the point of the decision.
-/

/-- The function a module defines, when it parses and defines exactly one.  A
failed parse or another arity is `none`, and every check below makes `none` fail:
a `Function` placeholder would let two failed parses compare equal and prove
nothing. -/
def onlyFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok ⟨_, [f]⟩ => some f
  | _ => none

/-- Whether two texts parse to one function each and to the same function.  A
failed parse on either side is `false`, never an equality of placeholders. -/
def sameFunction (a b : String) : Bool :=
  match onlyFunction a, onlyFunction b with
  | some f, some g => f = g
  | _, _ => false

/-- Whether `src` is refused with a message naming every token. -/
def refusedWith (src : String) (tokens : List String) : Bool :=
  match parseModule src with
  | .error e => tokens.all (mentions e)
  | .ok _ => false

/-- The integer a run returns, or `none` for `ub` and for an unfinished run. -/
def intOut (o : Option Outcome) : Option Nat :=
  match o with
  | some (.ret (some (.int _ v)) _) => some v.toNat
  | _ => none

/-- The outcome of a run, when `src` parses to one function: a failed parse is
`none` and an outcome is `some o`, so a check cannot mistake one for the other. -/
def runOf (calls : Calls) (src : String) (args : List Value) : Option (Option Outcome) :=
  (onlyFunction src).map fun f => run calls f args

/-- The integer a run returns, at the same two levels: `some (some n)` is the
answer, `some none` is `ub` or an unfinished run, and `none` is a failed parse. -/
def intOf (calls : Calls) (src : String) (args : List Value) : Option (Option Nat) :=
  (runOf calls src args).map intOut

/-- A call with and without the `tail` marker. -/
def tailSrc (marker : String) : String :=
"define i32 @tailer(i32 %x) {
entry:
  %y = " ++ marker ++ "call i32 @g(i32 %x)
  ret i32 %y
}
"

/-- `@g` adds one and leaves the caller's memory and allocator alone. -/
def plusOneCalls : Calls := fun callee args mem next =>
  if callee = "g" then
    match args with
    | [.int 32 v] => some { ret := .int 32 (v + 1), mem := mem, next := next }
    | _ => none
  else none

-- The marker is dropped: both texts parse to one function.
#guard sameFunction (tailSrc "tail ") (tailSrc "")

-- And the call still does what it did: the environment answers, and the answer is
-- the one the plain call gives (the ASTs are equal above, so one run decides both).
#guard runOf plusOneCalls (tailSrc "tail ") [.int 32 (BitVec.ofNat 32 41)] =
  some (some (.ret (some (.int 32 (BitVec.ofNat 32 42))) []))

/-- A definition with and without header surface in front of its return type. -/
def headerSrc (surface : String) : String :=
"define " ++ surface ++ "i32 @header(i32 %x) {
entry:
  %y = add i32 %x, 1
  ret i32 %y
}
"

-- Linkage, a calling convention, a preemption or visibility specifier and a
-- numbered calling convention are dropped, alone and together.
#guard sameFunction (headerSrc "internal ") (headerSrc "")
#guard sameFunction (headerSrc "internal fastcc ") (headerSrc "")
#guard sameFunction (headerSrc "dso_local hidden cc 10 ") (headerSrc "")
#guard sameFunction (headerSrc "private dso_preemptable dllimport coldcc ") (headerSrc "")

-- The target-specific calling conventions are the same kind of token as `fastcc`:
-- each is a calling convention, and none is modelled, so each is dropped rather
-- than reported as a property of the returned value.
#guard sameFunction (headerSrc "x86_stdcallcc ") (headerSrc "")
#guard sameFunction (headerSrc "win64cc ") (headerSrc "")
#guard sameFunction (headerSrc "x86_fastcallcc ") (headerSrc "")
#guard sameFunction (headerSrc "aarch64_vector_pcs ") (headerSrc "")
#guard sameFunction (headerSrc "aarch64_sve_vector_pcs ") (headerSrc "")
#guard sameFunction (headerSrc "arm_aapcs_vfpcc ") (headerSrc "")
#guard sameFunction (headerSrc "cxx_fast_tlscc ") (headerSrc "")
#guard sameFunction (headerSrc "amdgpu_kernel ") (headerSrc "")
-- And in the position clang writes them, mixed with linkage and visibility.
#guard sameFunction (headerSrc "internal win64cc dso_local hidden ") (headerSrc "")

-- The body is the body: the run is the same answer.
#guard runOf noCalls (headerSrc "internal fastcc ") [.int 32 (BitVec.ofNat 32 1)] =
  some (some (.ret (some (.int 32 (BitVec.ofNat 32 2))) []))

-- The boundary is where the attributes start: a token in the same position that
-- is not linkage or a calling convention is still a return attribute, and it is
-- refused as one.
#guard refusedWith (headerSrc "zeroext ") ["zeroext", "return attribute"]

/-- An integer comparison with and without the `samesign` flag. -/
def samesignSrc (flag : String) : String :=
"define i32 @cmp(i32 %x) {
entry:
  %c = icmp " ++ flag ++ "ugt i32 %x, 5
  br i1 %c, label %big, label %small
big:
  ret i32 1
small:
  ret i32 0
}
"

-- Dropped: the flag leaves no field behind, so both texts parse to one function.
#guard sameFunction (samesignSrc "samesign ") (samesignSrc "")

-- The comparison still decides, both ways: `6 > 5` and `3 > 5`.
#guard runOf noCalls (samesignSrc "samesign ") [.int 32 (BitVec.ofNat 32 6)] =
  some (some (.ret (some (.int 32 (BitVec.ofNat 32 1))) []))
#guard runOf noCalls (samesignSrc "samesign ") [.int 32 (BitVec.ofNat 32 3)] =
  some (some (.ret (some (.int 32 (BitVec.ofNat 32 0))) []))

/-! ### Pointer comparison

A pointer is compared by its address.  The two programs below make the failure
mode a naive reading would have: comparing integer *values* rather than
addresses, or a signed 64-bit order rather than an unsigned one. -/

/-- Two different objects at the same offset: `%pa` and `%pb` both add zero to
the address of a distinct `i32`, so only their addresses distinguish them. -/
def ptrCmpSrc (pred : String) : String :=
"define i1 @pcmp() {
entry:
  %a = alloca i32
  %b = alloca i32
  %pa = getelementptr inbounds i32, ptr %a, i64 0
  %pb = getelementptr inbounds i32, ptr %b, i64 0
  %c = icmp " ++ pred ++ " ptr %pa, %pb
  ret i1 %c
}
"

-- Different objects compare unequal even at equal offsets, and equality says
-- they are not equal.
#guard intOf noCalls (ptrCmpSrc "ne") [] = some (some 1)
#guard intOf noCalls (ptrCmpSrc "eq") [] = some (some 0)

-- The printer emits the pointer form and the parser reads it back: one function,
-- so no field of the written address comparison is lost.
#guard
  match onlyFunction (ptrCmpSrc "eq") with
  | some f => parseModule (Module.render ⟨[], [f]⟩) = .ok ⟨[], [f]⟩
  | none => false

-- The control: one pointer compares equal to itself.
def ptrSelfSrc (pred : String) : String :=
"define i1 @pself() {
entry:
  %a = alloca i32
  %c = icmp " ++ pred ++ " ptr %a, %a
  ret i1 %c
}
"

#guard intOf noCalls (ptrSelfSrc "eq") [] = some (some 1)
#guard intOf noCalls (ptrSelfSrc "ne") [] = some (some 0)

/-- `%hi` is `0x8000000000000004`: `%a` is the first `i32`, at address 1 (address
0 is `null`), `%b` is the second, at 5, and the index is the largest one the
`getelementptr` step admits. -/
def highPtrCmpSrc (pred : String) : String :=
"define i1 @hcmp() {
entry:
  %a = alloca i32
  %b = alloca i32
  %hi = getelementptr inbounds i8, ptr %b, i64 0x7FFFFFFFFFFFFFFF
  %c = icmp " ++ pred ++ " ptr %hi, %a
  ret i1 %c
}
"

-- An address at or above `2 ^ 63` is *above* a low one unsigned, and a signed
-- 64-bit order would put it below: `ugt` and `uge` are true, `ult` and `ule` are
-- false.  A signed reading of the same bit pattern would answer the other way.
#guard intOf noCalls (highPtrCmpSrc "ugt") [] = some (some 1)
#guard intOf noCalls (highPtrCmpSrc "uge") [] = some (some 1)
#guard intOf noCalls (highPtrCmpSrc "ult") [] = some (some 0)
#guard intOf noCalls (highPtrCmpSrc "ule") [] = some (some 0)

-- The ordered pair the other way round, so the answers above are the order and
-- not a constant.
def highPtrCmpRevSrc (pred : String) : String :=
"define i1 @hrev() {
entry:
  %a = alloca i32
  %b = alloca i32
  %hi = getelementptr inbounds i8, ptr %b, i64 0x7FFFFFFFFFFFFFFF
  %c = icmp " ++ pred ++ " ptr %a, %hi
  ret i1 %c
}
"

#guard intOf noCalls (highPtrCmpRevSrc "ugt") [] = some (some 0)
#guard intOf noCalls (highPtrCmpRevSrc "ult") [] = some (some 1)

-- A signed predicate over pointers is not LLVM-valid and is refused by name.
#guard refusedWith (ptrCmpSrc "slt") ["slt", "pointer", "signed order"]
#guard refusedWith (ptrCmpSrc "sge") ["sge", "pointer", "signed order"]

/-- A pointer comparison with one operand bound at an integer type, in the left
position and in the right.  The text parses as `icmp <pred> ptr ...`, so the
instruction's type is a pointer and the register's type disagrees with it. -/
def mixedPtrSrc (l r : String) : String :=
"define i1 @mixed(i32 %i) {
entry:
  %a = alloca i32
  %c = icmp eq ptr " ++ l ++ ", " ++ r ++ "
  ret i1 %c
}
"

#guard refusedWith (mixedPtrSrc "%i" "%a") ["left operand", "%i", "i32", "not comparable"]
#guard refusedWith (mixedPtrSrc "%a" "%i") ["right operand", "%i", "i32", "not comparable"]

-- The semantics' answer for a hand-built AST, where no register table exists:
-- an operand that is not a pointer is `none`, which `step` reads as `ub`.
def handBuiltMixedCmp : Function :=
  ⟨"hand", .int 1, [],
   [⟨"entry",
     [ .binop "%i" .add 32 (.imm (.int 32 1)) (.imm (.int 32 2)),
       .icmpPtr "%c" .eq (.reg "%i") (.reg "%i") ],
     .ret (.int 1) (some (.reg "%c"))⟩]⟩

#guard run noCalls handBuiltMixedCmp [] = some .ub

-- And a hand-built signed predicate over two real pointers is `ub` too: the
-- parser refuses the text, and `evalICmpPtr` refuses the predicate.
def handBuiltSignedCmp : Function :=
  ⟨"hand", .int 1, [],
   [⟨"entry",
     [ .alloca "%a" (.int 32) 0, .alloca "%b" (.int 32) 0,
       .icmpPtr "%c" .slt (.reg "%a") (.reg "%b") ],
     .ret (.int 1) (some (.reg "%c"))⟩]⟩

#guard run noCalls handBuiltSignedCmp [] = some .ub
#guard evalICmpPtr .slt 0 0 = none

/-- The unsigned order over addresses, restated: an address at or above `2 ^ 63`
is greater than a low one. -/
example : evalICmpPtr .ugt (2 ^ 63) 0 = some (1 : BitVec 1) :=
  evalICmpPtr_high_address_unsigned.1

/-- info: 'LeanLLVM.evalICmpPtr_high_address_unsigned' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.evalICmpPtr_high_address_unsigned

/-- A signed predicate over addresses is refused, restated. -/
example : evalICmpPtr .slt 5 7 = none :=
  evalICmpPtr_signed_none .slt (Or.inl rfl) 5 7

/-- info: 'LeanLLVM.evalICmpPtr_signed_none' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanLLVM.evalICmpPtr_signed_none

/-- The accepting case of the instruction, restated: two pointer operands bind
the predicate's result on their addresses. -/
example {calls : Calls} {s : State} {d : String} {pr : IPred} {a b : Operand}
    {x y : Nat} {r : BitVec 1}
    (ha : evalOperand s a = some (.ptr x)) (hb : evalOperand s b = some (.ptr y))
    (hr : evalICmpPtr pr x y = some r) :
    evalInstr calls s (.icmpPtr d pr a b) = some (s.bind d (.int 1 r)) :=
  evalInstr_icmpPtr ha hb hr

/-- info: 'LeanLLVM.evalInstr_icmpPtr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_icmpPtr

/-- A pointer comparison writes no memory, restated. -/
example {calls : Calls} {s s' : State} {d : String} {pr : IPred} {a b : Operand}
    (h : evalInstr calls s (.icmpPtr d pr a b) = some s') : s'.mem = s.mem :=
  evalInstr_icmpPtr_mem h

/-- info: 'LeanLLVM.evalInstr_icmpPtr_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_icmpPtr_mem

/-- A pointer comparison binds exactly its destination, restated. -/
example {calls : Calls} {s s' : State} {d : String} {pr : IPred} {a b : Operand}
    (h : evalInstr calls s (.icmpPtr d pr a b) = some s') :
    ∃ v, s'.env = (d, v) :: s.env :=
  evalInstr_icmpPtr_env h

/-- info: 'LeanLLVM.evalInstr_icmpPtr_env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_icmpPtr_env

/-- Two void calls in one function, the second written with `tail`.  Both bind
nothing, so the function defines no register at all. -/
def twoVoidSrc : String :=
"define void @two(i32 %x) {
entry:
  call void @sink(i32 %x)
  tail call void @sink(i32 %x)
  ret void
}
"

#guard
  match onlyFunction twoVoidSrc with
  | some f =>
      match f.blocks with
      | [b] => b.instrs =
          [ .callVoid "sink" [(.int 32, .reg "%x")],
            .callVoid "sink" [(.int 32, .reg "%x")] ]
      | _ => false
  | none => false

-- The two-call case is the one a destination sentinel would have refused as a
-- repeated definition: a void call has no destination, so `definedNames` is empty
-- however many of them the function makes.
#guard
  match onlyFunction twoVoidSrc with
  | some f => f.definedNames = []
  | none => false

#guard
  match onlyFunction twoVoidSrc with
  | some f => parseModule (Module.render ⟨[], [f]⟩) = .ok ⟨[], [f]⟩
  | none => false

/-- The callee of the state test: it writes `77` through the pointer it is given,
writes `111` at the caller's allocator cursor and `555` four bytes further on, and
hands the caller a cursor four bytes on — so it writes and it allocates. -/
def fittingCalls : Calls := fun callee args mem next =>
  if callee = "fit" then
    match args with
    | [.ptr a] =>
        some { ret := .int 32 0,
               mem := writeBytes (writeBytes (writeBytes mem a (natToBytes 77 4))
                 next (natToBytes 111 4)) (next + 4) (natToBytes 555 4),
               next := next + 4 }
    | _ => none
  else none

/-- A void call whose effect the caller then observes: through the pointer it
passed, and through the allocator cursor it resumes from. -/
def fitSrc : String :=
"define i32 @fitter(i32 %x) {
entry:
  %p = alloca i32
  store i32 %x, ptr %p
  call void @fit(ptr %p)
  %q = alloca i32
  %a = load i32, ptr %p
  %b = load i32, ptr %q
  %r = add i32 %a, %b
  ret i32 %r
}
"

-- 632 = 77 + 555 is the answer only when the call's memory *and* its allocator
-- cursor are adopted: a model that kept its own cursor would land the second
-- `alloca` on 111 and answer 188, and one that kept its own memory would leave
-- `%q` unreadable and the run `ub`.
#guard intOf fittingCalls fitSrc [.int 32 (BitVec.ofNat 32 0)] = some (some 632)

/-- The control: a callee that leaves the state alone. -/
def idleCalls : Calls := fun callee _ mem next =>
  if callee = "fit" then some { ret := .int 32 0, mem := mem, next := next } else none

-- With nothing written, the caller's second `alloca` lands on a byte no
-- instruction wrote, so the 632 above is the callee's state and not the caller's.
-- `some (some .ub)` also pins that the program parsed: a failed parse is `none`.
#guard runOf idleCalls fitSrc [.int 32 (BitVec.ofNat 32 0)] = some (some .ub)

/-- One body line in a function that returns `i32`. -/
def withLine (line : String) : String :=
"define i32 @line(i32 %x) {
entry:
  " ++ line ++ "
  ret i32 %x
}
"

-- A `void` call binds nothing, so a destination register is refused by name; a
-- call with no destination whose result is not `void` is refused too.
#guard refusedWith (withLine "%d = call void @sink()") ["void", "%d"]
#guard refusedWith (withLine "call i32 @g()") ["no destination", "i32"]

-- Their control: the void call with no destination parses.
#guard (onlyFunction (withLine "call void @sink()")).isSome

/-- A call with a written callee function type in front of its symbol. -/
def typedCallSrc (sig : String) : String :=
"define i32 @typed(i32 %x) {
entry:
  %r = call i32 " ++ sig ++ "@g(i32 %x)
  ret i32 %r
}
"

-- The written type leaves no field behind: the text with it parses to the same
-- function as the text without it, for a scalar and for a variadic signature.
#guard sameFunction (typedCallSrc "(i32) ") (typedCallSrc "")
#guard
  sameFunction
    (withLine "call void (ptr, i64, ptr, ...) @printf(ptr null, i64 0, ptr null)")
    (withLine "call void @printf(ptr null, i64 0, ptr null)")

-- And the call still runs: the environment answers by symbol, and the written
-- type changed none of the values it receives.
#guard intOf plusOneCalls (typedCallSrc "(i32) ") [.int 32 (BitVec.ofNat 32 41)] =
  some (some 42)

-- The printer has no field for the written type, so the canonical text omits it
-- and re-parses to the same instruction.
#guard
  match onlyFunction (typedCallSrc "(i32) ") with
  | some f => parseModule (Module.render ⟨[], [f]⟩) = .ok ⟨[], [f]⟩
  | none => false

-- The check is not vacuous: a written type that disagrees with the arguments is
-- refused, by argument position and with both types named.
#guard refusedWith (withLine "%d = call i32 (i64) @g(i32 1)")
  ["argument 1", "i64", "i32"]
-- The written return type is the type the destination is bound at, so the
-- function-level table already sees it.  The `phi` check reads that table: a
-- call at `i64` feeding a `phi i32` is refused by the same check that refuses
-- any other incoming-type disagreement.
def typedCallPhiSrc (ty : String) : String :=
"define " ++ ty ++ " @pcf() {
entry:
  %r = call " ++ ty ++ " (i32) @g(i32 1)
  br label %b
b:
  %p = phi " ++ ty ++ " [ %r, %entry ]
  ret " ++ ty ++ " %p
}
"

#guard (onlyFunction (typedCallPhiSrc "i32")).isSome

def typedCallPhiMismatch : String :=
"define i32 @pcf() {
entry:
  %r = call i64 (i32) @g(i32 1)
  br label %b
b:
  %p = phi i32 [ %r, %entry ]
  ret i32 %p
}
"

#guard refusedWith typedCallPhiMismatch ["phi %p", "i32", "i64"]

-- A variadic signature still constrains its fixed prefix.
#guard refusedWith (withLine "call void (ptr, ...) @printf()")
  ["writes 1 parameter", "passes 0 argument"]
#guard refusedWith (withLine "call void (ptr, ...) @printf(i32 1)")
  ["argument 1", "ptr", "i32"]
-- A `...` is only a suffix.
#guard refusedWith (withLine "call void (..., ptr) @printf(ptr null)")
  ["variadic", "last"]

/-- A void call whose argument list is written by the parameter. -/
def argsSrc (args : String) : String :=
"define i32 @argscanner(i32 %x) {
entry:
  call void @takesargs(" ++ args ++ ")
  ret i32 %x
}
"

-- The scanner reads to the `)` that closes the list and not the first `)`, and a
-- comma inside a nested group does not separate arguments: this is one call with
-- two arguments, the second a `splat`.
#guard
  match onlyFunction (argsSrc "i32 1, <4 x i32> splat (i32 7)") with
  | some f =>
      match f.blocks with
      | [b] => b.instrs = [ .callVoid "takesargs"
          [(.int 32, .imm (.int 32 1)), (.vec 4 (.int 32), .imm (.splat 4 32 7))] ]
      | _ => false
  | none => false

-- A `poison` argument is read, and the model gives it no value: the call is `ub`,
-- which is the conservative reading of a poison operand rather than a narrowing.
-- The same holds at a vector type, where the literal is not a lane list.
#guard runOf noCalls (argsSrc "i32 poison") [.int 32 (BitVec.ofNat 32 0)] = some (some .ub)
#guard runOf noCalls (argsSrc "<4 x i32> poison") [.int 32 (BitVec.ofNat 32 0)] =
  some (some .ub)

-- The two shapes the operand grammar still has no value for are refused by name,
-- with the argument's position: a literal vector, and an argument attribute.
#guard refusedWith (argsSrc "i32 1, <4 x i32> <i32 1, i32 2, i32 3, i32 4>")
  ["argument 2", "vector literal"]
#guard refusedWith (argsSrc "i32 1, i32 range(i32 0, 65) %x")
  ["argument 2", "range", "not modelled"]

/-- info: 'LeanLLVM.evalInstr_callVoid_env' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_callVoid_env
