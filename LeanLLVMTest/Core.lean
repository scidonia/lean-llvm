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

-- The step's facts, restated from `LeanLLVM.Semantics`: the accepting case, the
-- refusal the negative index is, the refusal of each other operand shape, and
-- the memory it leaves alone.  A `#guard` above observes the step on values this
-- file chose; these are the statements a later proof composes with, and each is
-- pinned below to the standard axioms.
example {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a w : Nat} {n : BitVec w} (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hpos : (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d base off) =
      some (s.bind d (.ptr (a + (n.signExtend 64).toNat))) :=
  evalInstr_gep hb ho hpos

example {calls : Calls} {s : State} {d : String} {base off : Operand}
    {a w : Nat} {n : BitVec w} (hb : evalOperand s base = some (.ptr a))
    (ho : evalOperand s off = some (.int w n)) (hneg : ¬ (n.signExtend 64).toNat < 2 ^ 63) :
    evalInstr calls s (.gep d base off) = none :=
  evalInstr_gep_negative hb ho hneg

example {calls : Calls} {s : State} {d : String} {base off : Operand} {v : Value}
    (hb : evalOperand s base = some v) (hv : ∀ a, v ≠ .ptr a) :
    evalInstr calls s (.gep d base off) = none :=
  evalInstr_gep_none_of_base hb hv

example {calls : Calls} {s : State} {d : String} {base off : Operand} {a : Nat}
    (hb : evalOperand s base = some (.ptr a)) {v : Value}
    (ho : evalOperand s off = some v) (hv : ∀ w n, v ≠ .int w n) :
    evalInstr calls s (.gep d base off) = none :=
  evalInstr_gep_none_of_off hb ho hv

example {calls : Calls} {s : State} {d : String} {base off : Operand}
    (h : evalOperand s base = none ∨ evalOperand s off = none) :
    evalInstr calls s (.gep d base off) = none :=
  evalInstr_gep_none_of_unbound h

example {calls : Calls} {s s' : State} {d : String} {base off : Operand}
    (h : evalInstr calls s (.gep d base off) = some s') : s'.mem = s.mem :=
  evalInstr_gep_mem h

/-- info: 'LeanLLVM.evalInstr_gep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.evalInstr_gep

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
