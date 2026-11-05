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
