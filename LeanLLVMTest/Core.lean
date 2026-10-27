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
  | .error _ => ⟨[]⟩

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

-- The semantics computes the taken branch (`%a` is 3).
#guard run sampleFunction [.int 32 (BitVec.ofInt 32 2)] =
  some (.ret (some (.int 32 (BitVec.ofInt 32 3))) [])

-- The semantics computes the other input.
#guard run sampleFunction [.int 32 (BitVec.ofInt 32 7)] =
  some (.ret (some (.int 32 (BitVec.ofInt 32 8))) [])

-- Constant propagation makes the comparison's operands literal and the branch
-- condition folds; the conditional edge disappears.
#guard
  match (optimizeFunction sampleFunction).blocks with
  | b :: _ => b.term = .br "yes"
  | [] => false

-- The pipeline leaves observable behaviour unchanged on this program.
#guard run sampleFunction [.int 32 (BitVec.ofInt 32 2)] =
  run (optimizeFunction sampleFunction) [.int 32 (BitVec.ofInt 32 2)]

#guard run sampleFunction [.int 32 (BitVec.ofInt 32 7)] =
  run (optimizeFunction sampleFunction) [.int 32 (BitVec.ofInt 32 7)]

-- Refinement is what the pipeline theorem provides.
example : Refines (optimizeFunction sampleFunction) sampleFunction :=
  optimisationPipeline_sound sampleFunction

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
  | .ok ⟨f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

def returnsValue (o : Option Outcome) (v : Value) : Bool :=
  match o with
  | some (.ret (some w) _) => w = v
  | _ => false

#guard returnsValue (run memoryFunction []) (.int 32 (BitVec.ofInt 32 42))

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
  | .ok ⟨f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

#guard returnsValue (run signedFunction []) (.int 32 (BitVec.ofInt 32 (-21)))

-- The pipeline preserves the signed-division program's behaviour.
#guard run signedFunction [] = run (optimizeFunction signedFunction) []

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
  | .ok ⟨f :: _⟩ => f
  | _ => ⟨"", .void, [], []⟩

#guard
  match (strengthReduction.run strengthFunction).blocks with
  | b :: _ =>
      match b.instrs with
      | [i] => i = .binop "%y" .shl 32 (.reg "%x") (.imm (.int 32 (BitVec.ofNat 32 1)))
      | _ => false
  | [] => false

#guard run strengthFunction [.int 32 (BitVec.ofInt 32 21)] =
  run (strengthReduction.run strengthFunction) [.int 32 (BitVec.ofInt 32 21)]

/-- info: 'LeanLLVM.strengthReduction_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanLLVM.strengthReduction_sound
