/-
The core extension's acceptance scenario: the address conversions, the global
symbol operand, the binary64 forms and the aggregate layouts, in one program.

Three surfaces meet here because one emitted body needs all of them.
`probes/install/ir/stage2.helper.s2_string_body.ll` stores the message word
`@.str.14` through a `ptrtoint`, and `num_fast_el1`'s emission computes in
binary64 over `[23 x double]` tables; each construct below is pinned to the text
it reads, the AST it becomes, the form it prints, the value it computes and the
neighbour it refuses.

**Addresses and integers.** `%d = ptrtoint ptr %v to i64` is the model's one
pointer-to-integer conversion, at the width `Ty.sizeBytes .ptr` already fixes.
An address is an unbounded `Nat` and an `i64` is 64 bits, so the step is
defined exactly below `2 ^ 64`: an address at or above it is `ub`, not a
truncation. `%d = inttoptr i64 %v to ptr` is the inverse reading, and the pair's
exactness is `Value.toAddr_ofAddr`. Another written width, another source type,
and a `bitcast` between a pointer and an integer are refused by name.

**Global symbols.** `@sym` is an operand whose value is the address the loader
assigned; the text names the symbol and the run supplies the address, so it is
not a `Const`. A symbol is read at `ptr` and nowhere else, its environment key is
its own `@`-spelling (a register's is its `%`-spelling, so the two cannot
collide), and a symbol the staging does not bind is `ub` — the reading an
unresolved call gets.

**Binary64.** `double` is carried as its 64-bit pattern, so `+0` and `-0` are
distinct values and a NaN keeps its payload; `bitcast` is the identity in both
directions. The arithmetic is one `roundMag` call on each operation's exact
value in ticks, so the answers below are IEEE 754 binary64's, and the ones that
differ from a decimal reading (the two integer widenings that round) are pinned
by their bits.

**Aggregates.** `[N x T]` occupies `N * sizeof(T)`; `%struct.<name>` occupies the
byte extent the target datalayout gives it, which the parser takes from a
declared layout rather than recomputing from fields. A `getelementptr` over an
array with a literal `0` leading index reduces to the one-index step at the
element type — the same instruction the source could have written directly.

The parser compares string tokens and does not reduce in the kernel, so every
check here is a `#guard` rather than a `decide`d proposition.

Elaborated by `nix develop -c lake env lean tests/core-extension.lean`. A
`#guard` that does not hold stops elaboration with a nonzero exit status;
nothing outside the elaborated program is written.
-/
import LeanLLVM

namespace CoreExtension

open LeanLLVM
set_option autoImplicit false

/-! ### Helpers -/

def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

def parses (src : String) : Bool :=
  match parseModule src with
  | .ok _ => true
  | .error _ => false

def refusal (src : String) : Option String :=
  match parseModule src with
  | .error e => some e
  | .ok _ => none

def wrap (body : String) : String :=
"define i64 @f(ptr %p, i64 %q) {
entry:
" ++ body ++ "
}
"

/-! ### Address conversions -/

def castSample : String :=
"define i64 @cast(ptr %p, i64 %q) {
entry:
  %a = ptrtoint ptr %p to i64
  %b = inttoptr i64 %q to ptr
  %c = ptrtoint ptr null to i64
  ret i64 %a
}
"

-- The text parses to exactly these constructors: no width field, source `ptr`,
-- result `i64`, and the `null` literal read as the pointer it is.
#guard
  match parseModule castSample with
  | .ok ⟨_, f :: _⟩ =>
      match f.blocks with
      | [b] =>
          decide (b.instrs =
            [ .ptrtoint "%a" (.reg "%p"),
              .inttoptr "%b" (.reg "%q"),
              .ptrtoint "%c" (.imm .null) ])
      | _ => false
  | _ => false

-- The printed form parses back to the same module.
#guard
  match parseModule castSample with
  | .ok m =>
      match parseModule (Module.render m) with
      | .ok m' => decide (m' = m)
      | .error _ => false
  | .error _ => false

def runSample : String :=
"define i64 @cast_run(ptr %p) {
entry:
  %a = ptrtoint ptr %p to i64
  %b = sub i64 %a, 8
  ret i64 %b
}
"

def runBody : Option Function :=
  match parseModule runSample with
  | .ok ⟨_, f :: _⟩ => some f
  | _ => none

-- The conversion's value, carried through the model's own subtraction, is the
-- address minus eight.
#guard
  match runBody with
  | some f => decide (run noCalls f [.ptr 40] = some (.ret (some (.int 64 32)) []))
  | none => false

-- An address at or above `2 ^ 64` has no value at the modelled width.
#guard
  match runBody with
  | some f => decide (run noCalls f [.ptr (2 ^ 64)] = some .ub)
  | none => false

-- Neighbouring integer widths are refused by name.
#guard refusal (wrap "  %a = ptrtoint ptr %p to i32
  ret i64 0") =
  some "in block 'entry': ptrtoint to i32 is not modelled: the model's pointer is 64 bits, so an address converts exactly at i64 only"

#guard refusal (wrap "  %a = ptrtoint ptr %p to i128
  ret i64 0") =
  some "in block 'entry': ptrtoint to i128 is not modelled: the model's pointer is 64 bits, so an address converts exactly at i64 only"

-- A non-pointer source.
#guard refusal (wrap "  %a = ptrtoint i64 %q to i64
  ret i64 %a") =
  some "in block 'entry': ptrtoint's source must be ptr, got i64: only an address converts to an integer"

#guard refusal (wrap "  %a = inttoptr i32 %q to ptr
  ret i64 0") =
  some "in block 'entry': inttoptr from i32 is not modelled: the model's pointer is 64 bits, so the conversion is modelled at i64 only"

#guard refusal (wrap "  %a = inttoptr i64 %q to i64
  ret i64 %a") =
  some "in block 'entry': inttoptr's result must be ptr, got i64: only an integer converts to an address"

-- A source bound at the wrong type is refused once the function is known.
#guard refusal (wrap "  %a = ptrtoint ptr %q to i64
  ret i64 %a") =
  some "ptrtoint %a converts %q, which has type i64: only a pointer converts to an integer"

#guard refusal (wrap "  %r = inttoptr i64 %p to ptr
  ret i64 0") =
  some "inttoptr %r converts %p, which has type ptr: only an i64 converts to an address"

-- `bitcast` between a pointer and an integer stays refused: the modelled
-- conversion is the instruction above, and LLVM rejects this cast anyway.
#guard refusal (wrap "  %a = bitcast ptr %p to i64
  ret i64 %a") =
  some "in block 'entry': bitcast from ptr to i64 is not modelled"

-- The pair's exactness and the four step lemmas.
example (a : Nat) (ha : a < 2 ^ 64) : Value.toAddr (.ofAddr a) = some a :=
  Value.toAddr_ofAddr a ha

example (s : State) (d : String) (v : Operand) (a : Nat)
    (hv : evalOperand s v = some (.ptr a)) (ha : a < 2 ^ 64) :
    evalInstr noCalls s (.ptrtoint d v) = some (s.bind d (.ofAddr a)) :=
  evalInstr_ptrtoint hv ha

example (s : State) (d : String) (v : Operand) (a : Nat)
    (hv : evalOperand s v = some (.ptr a)) (ha : 2 ^ 64 ≤ a) :
    evalInstr noCalls s (.ptrtoint d v) = none :=
  evalInstr_ptrtoint_out_of_range hv ha

example (s : State) (d : String) (v : Operand) (x : BitVec 64)
    (hv : evalOperand s v = some (.int 64 x)) :
    evalInstr noCalls s (.inttoptr d v) = some (s.bind d (.ptr x.toNat)) :=
  evalInstr_inttoptr hv

example (s : State) (d e : String) (v : Operand) (a : Nat)
    (hv : evalOperand s v = some (.ptr a)) (ha : a < 2 ^ 64) :
    evalInstr noCalls (s.bind d (.ofAddr a)) (.inttoptr e (.reg d)) =
      some ((s.bind d (.ofAddr a)).bind e (.ptr a)) :=
  evalInstr_inttoptr_ptrtoint hv ha

/-! ### The global symbol operand -/

-- The operand's environment key is the text's own spelling: a register's begins
-- `%` and a symbol's `@`, so the two namespaces cannot collide.
#guard Operand.regs (.global "@g") = ["@g"]
#guard Operand.regs (.reg "%g") = ["%g"]
#guard ("@demo.g" == "%demo.g") = false

-- The read set carries the symbol, which is what `State.AgreeOn` transports on.
#guard decide ("@demo.g" ∈ Instr.uses (.store .ptr (.global "@demo.g") (.reg "%p")))

/-- Run a function with the loader's assignment bound: the staging step a body
that names a global symbol needs. -/
def runStaged (calls : Calls) (f : Function) (args : List Value) (g : Globals)
    (fuel : Nat) : Option Outcome :=
  runFuel calls fuel f ((initState f args).withGlobals g)

def testCalls : Calls := fun name _ mem next =>
  if name = "llvm.lifetime.start.p0" || name = "llvm.lifetime.end.p0" then
    some { ret := .int 64 0, mem := mem, next := next }
  else if name = "leanllvm_json_escape_expand" then
    some { ret := .int 64 (BitVec.ofInt 64 (-1)), mem := mem, next := next }
  else none

-- Every position the operand grammar admits a pointer in, and the round trip.
def gSample : String :=
"define i32 @f(ptr %p, ptr %q) {
entry:
  store ptr @demo.g, ptr %q
  %a = load ptr, ptr @demo.g
  %c = icmp eq ptr @demo.g, %a
  %d = getelementptr i8, ptr @demo.g, i64 4
  call void @use(ptr @demo.g)
  ret i32 0
}
"

#guard
  match parseModule gSample with
  | .ok ⟨_, f :: _⟩ =>
      decide (f.blocks.flatMap (·.instrs) =
        [ .store .ptr (.global "@demo.g") (.reg "%q"),
          .load "%a" .ptr (.global "@demo.g"),
          .icmpPtr "%c" .eq (.global "@demo.g") (.reg "%a"),
          .gep "%d" (.int 8) (.global "@demo.g") (.imm (.int 64 4)),
          .callVoid "use" [(.ptr, .global "@demo.g")] ])
  | _ => false

#guard
  match parseModule gSample with
  | .ok m =>
      match parseModule (Module.render m) with
      | .ok m' => decide (m' = m) && hasSubstr (Module.render m) "@demo.g"
      | .error _ => false
  | .error _ => false

-- The value: the loader's address, stored, read back and converted.
def addrSample : String :=
"define i64 @addr(ptr %out) {
entry:
  store ptr @demo.g, ptr %out
  %a = load ptr, ptr %out
  %b = ptrtoint ptr %a to i64
  ret i64 %b
}
"

def addrBody : Option Function :=
  match parseModule addrSample with
  | .ok ⟨_, f :: _⟩ => some f
  | _ => none

#guard
  match addrBody with
  | some f =>
      decide (runStaged testCalls f [.ptr 64] [("@demo.g", 4096)] 400 =
        some (.ret (some (.int 64 4096)) (writeBytes [] 64 (natToBytes 4096 8))))
  | none => false

-- The same program with no assignment for the symbol is `ub`: a global the run
-- does not resolve behaves as a call the environment does not resolve.
#guard
  match addrBody with
  | some f =>
      decide (runStaged testCalls f [.ptr 64] [] 400 = some .ub)
  | none => false

-- A global is not a `Const`, so no substitution folds it.
example : (constOperand (fun _ => some (.int 64 7)) (.global "@g")).isNone := rfl
example : substOperand (fun _ => some (.int 64 7)) (.global "@g") = .global "@g" := rfl

-- Refusals by name.
#guard refusal (wrap "  store i64 @g, ptr %p
  ret i64 0") =
  some "in block 'entry': a global symbol's value is an address, so it has type \
ptr: '@g' is written here at type i64"

#guard refusal (wrap "  %a = getelementptr i8, ptr %p, i64 @g
  ret i64 0") =
  some "in block 'entry': a global symbol's value is an address, so it has type \
ptr: '@g' is written here at type i64"

#guard refusal (wrap "  store ptr @, ptr %p
  ret i64 0") =
  some "in block 'entry': a global symbol needs a name after '@'"

#guard refusal ("@g = global i8 0\n" ++ wrap "  store ptr @g, ptr %p
  ret i64 0") =
  some "expected 'define' or 'declare', got '@g = global i8 0'"

#guard refusal (wrap "  store ptr @g, ptr %p
  ret i64 0") = none

#guard refusal (wrap "  %a = icmp ult i64 @g, %q
  ret i64 0") =
  some "in block 'entry': a global symbol's value is an address, so it has type \
ptr: '@g' is written here at type i64"

-- The transport the read set already carries.
example {s t : State} (h : State.AgreeOn (Operand.regs (.global "@g")) s t) :
    evalOperand s (.global "@g") = evalOperand t (.global "@g") :=
  evalOperand_agree (op := .global "@g") (fun n hn => h.2.2.2 n hn)

example {calls : Calls} {s t s' : State} {p : Operand}
    (h : State.AgreeOn (Instr.uses (.store .ptr (.global "@g") p)) s t)
    (hs : evalInstr calls s (.store .ptr (.global "@g") p) = some s') :
    ∃ t', evalInstr calls t (.store .ptr (.global "@g") p) = some t' ∧
      State.AgreeOn (Instr.uses (.store .ptr (.global "@g") p)) s' t' :=
  evalInstr_agree calls h (fun _ hn => hn) hs

/-! ### The binary64 forms -/

def stF (a b : BitVec 64) : State :=
  { env := [("%a", .float a), ("%b", .float b)], mem := [], next := 1,
    pc := "entry", pre := none }

def stI (x : Nat) : State :=
  { env := [("%x", .int 64 (BitVec.ofNat 64 x))], mem := [], next := 1,
    pc := "entry", pre := none }

def stX (b : BitVec 64) : State :=
  { env := [("%x", .float b)], mem := [], next := 1, pc := "entry", pre := none }

def outVal (i : Instr) (s : State) (n : String) : Option Value :=
  (evalInstr noCalls s i).bind fun s' => lookupName s'.env n

def outBits (i : Instr) (s : State) (n : String) : Option (BitVec 64) :=
  (outVal i s n).bind fun v => match v with
    | .float b => some b
    | _ => none

def outOne (i : Instr) (s : State) (n : String) : Option (BitVec 1) :=
  (outVal i s n).bind fun v => match v with
    | .int 1 b => some b
    | _ => none

#guard Ty.sizeBytes .double = 8
#guard Ty.gepElemAdmitted .double = true
#guard Const.toValue (.float 0x3FF0000000000000) = some (.float 0x3FF0000000000000)
#guard (.float 0x0000000000000000 : Value) ≠ .float 0x8000000000000000
#guard Ty.render .double = "double"
#guard Const.render (.float 0x0000000000000000) = "0x0000000000000000"
#guard Const.render (.float 0x8000000000000000) = "0x8000000000000000"
#guard Const.render (.float 0x7FF8000000000001) = "0x7ff8000000000001"

-- `uitofp i64 … to double`, against C's `(double)x`; the seventh and eighth
-- round, which is the only place the widening is not exact.
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 0) "%r" = some 0x0000000000000000
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 1) "%r" = some 0x3ff0000000000000
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 9) "%r" = some 0x4022000000000000
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 123456789012345) "%r" = some 0x42dc12218377de40
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 4503599627370497) "%r" = some 0x4330000000000001
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 9007199254740993) "%r" = some 0x4340000000000000
#guard outBits (.uitofp "%r" 64 (.reg "%x")) (stI 18446744073709551615) "%r" = some 0x43f0000000000000

-- `fmul` and `fdiv`, against C's `a * b` and `a / b`.
#guard outBits (.fmul "%r" (.reg "%a") (.reg "%b")) (stF 0x3ff0000000000000 0x4024000000000000) "%r" = some 0x4024000000000000
#guard outBits (.fmul "%r" (.reg "%a") (.reg "%b")) (stF 0x4022000000000000 0x4024000000000000) "%r" = some 0x4056800000000000
#guard outBits (.fmul "%r" (.reg "%a") (.reg "%b")) (stF 0x430c6bf52633fff8 0x4480f0cf064dd592) "%r" = some 0x479e17b843576913
#guard outBits (.fdiv "%r" (.reg "%a") (.reg "%b")) (stF 0x3ff0000000000000 0x4008000000000000) "%r" = some 0x3fd5555555555555
#guard outBits (.fdiv "%r" (.reg "%a") (.reg "%b")) (stF 0x430c6bf52633fff8 0x430c6bf526340000) "%r" = some 0x3feffffffffffff7
#guard outBits (.fdiv "%r" (.reg "%a") (.reg "%b")) (stF 0x4345ee2a2eb5a5c4 0x4480f0cf064dd592) "%r" = some 0x3eb4b66dc01ec6fb

-- `fneg` is the sign bit's inversion, payload and all.
#guard outBits (.fneg "%r" (.reg "%a")) (stF 0x0000000000000000 0x0) "%r" = some 0x8000000000000000
#guard outBits (.fneg "%r" (.reg "%a")) (stF 0x7ff0000000000000 0x0) "%r" = some 0xfff0000000000000
#guard outBits (.fneg "%r" (.reg "%a")) (stF 0x7ff8000000000001 0x0) "%r" = some 0xfff8000000000001

-- `fcmp oeq`: the zeros are equal, a NaN is never equal, infinities compare.
#guard outOne (.fcmp "%r" .oeq (.reg "%a") (.reg "%b")) (stF 0x0000000000000000 0x8000000000000000) "%r" = some 1
#guard outOne (.fcmp "%r" .oeq (.reg "%a") (.reg "%b")) (stF 0x7ff8000000000000 0x7ff8000000000000) "%r" = some 0
#guard outOne (.fcmp "%r" .oeq (.reg "%a") (.reg "%b")) (stF 0x7ff0000000000000 0x7ff0000000000000) "%r" = some 1
#guard outOne (.fcmp "%r" .oeq (.reg "%a") (.reg "%b")) (stF 0x7ff0000000000000 0xfff0000000000000) "%r" = some 0

-- `bitcast` both ways is the pattern, unchanged.
#guard outBits (.bitcastToDouble "%r" (.reg "%x")) (stI 0x400921FB54442D18) "%r"
  = some 0x400921FB54442D18
#guard (outVal (.bitcastToInt "%r" (.reg "%x")) (stX 0x400921FB54442D18) "%r")
  = some (.int 64 0x400921FB54442D18)

-- Shape refusals at run time: a hand-built AST that reads an operand of another
-- value shape steps nowhere.
#guard (evalInstr noCalls (stI 5) (.fmul "%r" (.reg "%x") (.reg "%x"))) = none
#guard (evalInstr noCalls (stI 5) (.uitofp "%r" 32 (.reg "%x"))) = none
#guard (evalInstr noCalls (stF 0x3FF0000000000000 0x0)
          (.bitcastToDouble "%r" (.reg "%a"))) = none
#guard (evalInstr noCalls (stI 5) (.fneg "%r" (.reg "%x"))) = none

-- The memory, `select` and `phi` forms at `double`.
def memRun : Option State := do
  let s0 : State := { env := [], mem := [], next := 1, pc := "entry", pre := none }
  let s1 ← evalInstr noCalls s0 (Instr.alloca "%s" .double 8)
  let s2 ← evalInstr noCalls s1
    (Instr.store .double (.imm (.float 0x400921FB54442D18)) (.reg "%s"))
  let s3 ← evalInstr noCalls s2 (Instr.load "%v" .double (.reg "%s"))
  let s4 ← evalInstr noCalls s3
    (Instr.select "%r" .double (.imm (.int 1 1)) (.reg "%v")
      (.imm (.float 0x0000000000000000)))
  let s5 ← evalInstr noCalls s4
    (Instr.fcmp "%e" .oeq (.reg "%r") (.reg "%v"))
  pure s5

#guard (evalInstr noCalls { env := [], mem := [], next := 1, pc := "e", pre := none }
          (Instr.alloca "%s" .double 8)).map (·.next) = some 9
#guard (memRun.bind fun s => lookupName s.env "%v") = some (.float 0x400921FB54442D18)
#guard (memRun.bind fun s => readBytes s.mem 1 8)
  = some (natToBytes 0x400921FB54442D18 8)
#guard (memRun.bind fun s => lookupName s.env "%r") = some (.float 0x400921FB54442D18)
#guard (memRun.bind fun s => lookupName s.env "%e") = some (.int 1 1)
#guard ((evalInstr noCalls
          { env := [("%a", .float 0x3FF0000000000000)], mem := [], next := 1,
            pc := "j", pre := some "t" }
          (Instr.phi "%r" .double
            [("t", .reg "%a"), ("f", .imm (.float 0x0000000000000000))])).bind
        fun s => lookupName s.env "%r") = some (.float 0x3FF0000000000000)
#guard Instr.render (Instr.phi "%r" .double [("t", .reg "%a")])
  = "  %r = phi double [ %a, %t ]"

-- The printed forms.
#guard Instr.render (.uitofp "%c" 64 (.reg "%m")) = "  %c = uitofp i64 %m to double"
#guard Instr.render (.fmul "%m" (.reg "%c") (.reg "%p")) = "  %m = fmul double %c, %p"
#guard Instr.render (.fdiv "%q" (.reg "%m") (.reg "%p")) = "  %q = fdiv double %m, %p"
#guard Instr.render (.fneg "%n" (.reg "%q")) = "  %n = fneg double %q"
#guard Instr.render (.fcmp "%e" .oeq (.reg "%q") (.reg "%q")) = "  %e = fcmp oeq double %q, %q"
#guard Instr.render (.bitcastToInt "%i" (.reg "%q")) = "  %i = bitcast double %q to i64"
#guard Instr.render (.bitcastToDouble "%j" (.reg "%i")) = "  %j = bitcast i64 %i to double"

-- The body's tier-1 computation for one operand pair, and its printed text.
def tier1Block : Block :=
  { name := "entry"
    instrs := [ Instr.uitofp "%c" 64 (.reg "%mant"),
                Instr.fmul "%m" (.reg "%c") (.reg "%pw"),
                Instr.fdiv "%q" (.reg "%m") (.reg "%pw"),
                Instr.bitcastToInt "%i" (.reg "%q"),
                Instr.bitcastToDouble "%j" (.reg "%i"),
                Instr.fneg "%nf" (.reg "%j"),
                Instr.fneg "%r" (.reg "%nf") ]
    term := Term.ret .double (some (.reg "%r")) }

def tier1Fn : Function :=
  { name := "tier1", retTy := .double,
    params := [("%mant", .int 64), ("%pw", .double)],
    blocks := [tier1Block] }

#guard Function.regType tier1Fn "%q" = some .double
#guard Function.regType tier1Fn "%i" = some (.int 64)
#guard run noCalls tier1Fn [.int 64 123456789012345, .float 0x3ff0000000000000] =
  some (.ret (some (.float 0x42dc12218377de40)) [])
#guard run noCalls tier1Fn [.int 64 999999999999999, .float 0x4480f0cf064dd592] =
  some (.ret (some (.float 0x430c6bf52633fff8)) [])
#guard run noCalls tier1Fn [.int 64 4503599627370497, .float 0x430c6bf526340000] =
  some (.ret (some (.float 0x4330000000000001)) [])

/-! ### The aggregate layouts -/

#guard Ty.sizeBytes (.array 768 (.int 8)) = 768
#guard Ty.sizeBytes (.array 96 (.int 64)) = 768
#guard Ty.sizeBytes (.array 23 .double) = 184
#guard Ty.sizeBytes (.struct "Stk" 1568) = 1568
#guard Ty.render (.array 96 (.int 64)) = "[96 x i64]"
#guard Ty.render (.struct "Stk" 1568) = "%struct.Stk"

def aggSample : String :=
"define i64 @agg() {
entry:
  %a = alloca [768 x i8], align 16
  %b = getelementptr [768 x i8], ptr %a, i64 0, i64 767
  %c = getelementptr [768 x i8], ptr %a, i64 0, i64 %k
  ret i64 0
}
"

-- The alloca's size is its element count times the element's, and the reduced
-- GEP is the one-index step at the element type.
#guard
  match parseModule aggSample with
  | .ok ⟨_, f :: _⟩ =>
      match f.blocks with
      | [b] =>
          decide (b.instrs =
            [ .alloca "%a" (.array 768 (.int 8)) 16,
              .gep "%b" (.int 8) (.reg "%a") (.imm (.int 64 767)),
              .gep "%c" (.int 8) (.reg "%a") (.reg "%k") ])
      | _ => false
  | _ => false

-- Printed and re-parsed, the array alloca is the same module.
#guard
  match parseModule aggSample with
  | .ok m =>
      match parseModule (Module.render m) with
      | .ok m' => decide (m' = m)
      | .error _ => false
  | .error _ => false

-- The cursor moves by the array's size: the allocation is 768 bytes from 1.
#guard
  (evalInstr noCalls { env := [], mem := [], next := 1, pc := "e", pre := none }
    (Instr.alloca "%a" (.array 768 (.int 8)) 16)).map (·.next) = some 769

-- A named struct takes its extent from the declared layout, and is refused
-- without one.
def structSample : String :=
"define i64 @st() {
entry:
  %v = alloca %struct.Stk, align 8
  ret i64 0
}
"

#guard
  match parseModuleWith [("Stk", 1568)] structSample with
  | .ok ⟨_, f :: _⟩ =>
      match f.blocks with
      | [b] => decide (b.instrs = [.alloca "%v" (.struct "Stk" 1568) 8])
      | _ => false
  | _ => false

#guard refusal structSample =
  some "in block 'entry': named struct '%struct.Stk' has no declared layout: the model takes a struct's byte extent from the target datalayout (a `Layout` argument) and does not recompute it from fields"

-- The refusals that keep the layout honest.
#guard refusal (wrap "  %a = alloca [0 x i8]
  ret i64 0") = some "in block 'entry': an array needs at least one element"

#guard refusal (wrap "  %a = alloca [4 x i24]
  ret i64 0") =
  some "in block 'entry': array element type 'i24' is not admitted: an array's allocated size is its element count times the element's allocated size, so its element must be a type whose allocated and stored sizes agree — the set `Ty.gepElemAdmitted` pins (the integer widths i1, i7, i8, i16, i32, i64 and i128, and whole-byte vectors whose packed size is a power of two)"

#guard refusal (wrap "  %a = alloca [[2 x i8] x 3]
  ret i64 0") = some "in block 'entry': a nested array type is not modelled"

#guard refusal (wrap "  %a = alloca <8 x i8>
  ret i64 0") = some "in block 'entry': alloca of a vector type is not modelled"

-- A nonzero or register leading index has a whole-array stride the reduced
-- instruction cannot express.
#guard refusal (wrap "  %a = getelementptr [4 x i8], ptr %p, i64 1, i64 %k
  ret i64 0") =
  some "in block 'entry': getelementptr over '[4 x i8]' is modelled only with a literal 0 leading index, got 1: the model's step has one index and no term for a whole-array stride"

#guard refusal (wrap "  %a = getelementptr [4 x i8], ptr %p, i64 %j, i64 %k
  ret i64 0") =
  some "in block 'entry': getelementptr over '[4 x i8]' is modelled only with a literal 0 leading index: the model's step has one index and no term for a whole-array stride"

#guard refusal (wrap "  %a = getelementptr [4 x i8], ptr %p, i64 0, i64 %k, i64 %j
  ret i64 0") =
  some "in block 'entry': getelementptr with more than two indices is not modelled"

-- An aggregate is not a load, store, parameter or `icmp` type: the type reader
-- refuses it where `alloca` is not the reader.
#guard refusal (wrap "  %a = load [4 x i8], ptr %p
  ret i64 0") = some "in block 'entry': unsupported type '['"

/-! ### The body the surface exists for -/

def s2Src : String :=
  include_str "../probes/install/ir/stage2.helper.s2_string_body.ll"

def s2InitSrc : String :=
  include_str "../probes/install/ir/stage2.helper.s2_init.ll"

-- The captured body is a program of the fragment: its `ptrtoint` pair and its
-- global-symbol operand are both modelled, and its sibling carries neither.
#guard parses s2Src = true
#guard hasSubstr s2Src "@.str.14" = true
#guard hasSubstr s2Src "ptrtoint ptr" = true
#guard hasSubstr s2InitSrc "@.str.14" = false
#guard parses s2InitSrc = true

def s2Body : Option Function :=
  match parseModule s2Src with
  | .ok ⟨_, f :: _⟩ => some f
  | _ => none

/-- The body's global use, read off the parsed AST: one `store` of the symbol's
address into `%msg2.i.i`.  The symbol is not loaded, GEP'd through, compared or
passed: the body needs the address and nothing else. -/
def storesGlobalAt (f : Function) (reg sym : String) : Bool :=
  (f.blocks.flatMap (·.instrs)).any fun i =>
    match i with
    | .store .ptr (.global g) (.reg r) => r == reg && g == sym
    | _ => false

#guard s2Body.any (fun f => storesGlobalAt f "%msg2.i.i" "@.str.14")

-- It is the only global operand in the body, and no instruction loads through
-- one: the fixture declares no contents and the body reads none.
#guard
  match s2Body with
  | some f =>
      decide ((f.blocks.flatMap (·.instrs)).filterMap (fun i =>
        match i with
        | .store .ptr (.global g) _ => some g
        | _ => none) = ["@.str.14"]) &&
      decide ((f.blocks.flatMap (·.instrs)).any (fun i =>
        match i with
        | .load _ _ (.global _) => true
        | _ => false) = false)
  | none => false

-- The body's two address conversions, in the emitted order.
#guard
  match s2Body with
  | some f =>
      match f.blocks with
      | b :: _ =>
          decide (b.instrs.filterMap (fun i => match i with
            | .ptrtoint d v => some (d, v)
            | _ => none) =
            [("%sub.ptr.lhs.cast", .reg "%p"),
             ("%sub.ptr.rhs.cast", .reg "%0")])
      | _ => false
  | none => false

-- Printing and re-parsing the captured body is the identity.
#guard
  match parseModule s2Src with
  | .ok m =>
      match parseModule (Module.render m) with
      | .ok m' => decide (m' = m)
      | .error _ => false
  | .error _ => false

-- The run: the refusal path's message word is the loader's address.  Staging
-- follows the emitted call's eight arguments, the body's own base word at `%c`,
-- the cursor list `[8, 24]`, the context's pointer word at `%c + 1112` and the
-- escape routine's `-1` answer.
def C : Nat := 16
def P : Nat := 40
def XP : Nat := 100
def XJ : Nat := 108
def CBASE : Nat := 1128
def E : Nat := 5000
def G : Nat := 4096

def s2Args : List Value :=
  [.ptr C, .ptr P, .int 64 2, .ptr 2000, .ptr 3000, .ptr XP, .ptr XJ, .int 64 2]

def s2Mem : Mem :=
  writeBytes (writeBytes (writeBytes (writeBytes (writeBytes []
    C (natToBytes C 8))
    XP (natToBytes 8 4))
    (XP + 4) (natToBytes 24 4))
    XJ (natToBytes 0 8))
    CBASE (natToBytes E 8)

def s2Staged (f : Function) (g : Globals) : State :=
  ({ initState f s2Args with mem := s2Mem } : State).withGlobals g

#guard
  match s2Body with
  | some f =>
      match runFuel testCalls 400 f (s2Staged f [("@.str.14", G)]) with
      | some (.ret (some (.int 32 0)) mem) => readBytes mem (E + 16) 8 = some (natToBytes G 8)
      | _ => false
  | none => false

-- The same staging with the symbol unassigned is undefined behaviour at the
-- store that reads it.
#guard
  match s2Body with
  | some f =>
      decide (runFuel testCalls 400 f (s2Staged f []) = some .ub)
  | none => false

-- A different loader assignment puts a different word there: the run is a
-- function of the staging, not of the text.
#guard
  match s2Body with
  | some f =>
      match runFuel testCalls 400 f (s2Staged f [("@.str.14", 9000)]) with
      | some (.ret (some (.int 32 0)) mem) =>
          readBytes mem (E + 16) 8 = some (natToBytes 9000 8)
      | _ => false
  | none => false

-- The rest of the record is the body's own arithmetic: the flag word is zero and
-- the offset word is `0 + (p - base)`.
#guard
  match s2Body with
  | some f =>
      match runFuel testCalls 400 f (s2Staged f [("@.str.14", G)]) with
      | some (.ret _ mem) =>
          readBytes mem E 4 = some (natToBytes 0 4) &&
          readBytes mem (E + 8) 8 = some (natToBytes 24 8)
      | _ => false
  | none => false

end CoreExtension
