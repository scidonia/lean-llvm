/-
The stage-1 fragment closure: the forms the fragment gained for the emitted
classifier body's text — and the one direction admitted with them that body does
not emit — each accepted, printed and re-parsed, evaluated as its Lean
definition, and each nearest neighbour that is not modelled refused by a name
that says what was refused.

The forms, one text each:

* `shufflevector` with a defined mask: a two-source static permutation whose
  result has the mask's lane count;
* a mask `store`: `<n x i1>` whose total width is a whole number of bytes;
* a non-mask vector `bitcast` at equal total width, changing element size;
* `lshr` on an integer vector, the shift the emitted body writes, and `shl` with
  it, the same operation in the other direction; no tracked `.ll` emits a vector
  `shl`, so that direction is this file's accepted control;
* the five intrinsic spellings the kernel calls — the two-argument
  `@llvm.x86.avx2.pshuf.b`, `@llvm.x86.pclmulqdq` at `i8 0`,
  `@llvm.x86.bmi.pext.64`, `@llvm.x86.bmi.pdep.64`, and `@llvm.ctlz.i64` with
  the flag `i1 false`.

The refusals, one text each: a `shufflevector` mask entry at `2n`; the same with
`undef` in the mask; a mask store whose width is not a whole number of bytes; a
vector store that is not a mask; a `bitcast` whose total widths disagree; a
`bitcast` to a vector of non-integer elements; a vector `ashr`; `umin` and
`umax`; and, for each intrinsic, the neighbouring spelling the fragment does
not model — `pshuf.b` with three arguments or at another vector type,
`pclmulqdq` at an immediate other than 0 or with a register there, `pext.32`,
`pdep.32`, and `ctlz` with the flag `i1 true`.

Two special facts are asserted where they arise rather than described:

* `shufflevector` selects from two operands, `k < n` from the first and
  `n ≤ k < 2n` from the second; an entry at or past `2n` is `ub` in the
  semantics (the parser refuses the text, so the AST here is hand-built).
* `pshuf.b` is the **per-128-bit-lane** table lookup: control bits 4 through 6
  are ignored, bit 7 zeroes the result byte, and the table address is within the
  control byte's own 16-byte lane.  The lane-17 case below is the one a linear
  32-entry reading gets wrong.

Elaborated by `nix develop -c lake env lean tests/vector-s1.lean`.  A `#guard`
that does not hold stops elaboration with a nonzero exit status; no compiler,
proof checker, service, clock or network is reached.
-/
import LeanLLVM

namespace VectorS1

open LeanLLVM
open LeanLLVM.Vellum.BitLanes
open LeanLLVM.Vellum.Pclmul

/-! ### Reading one answer -/

/-- One function whose body is the given instruction lines, so a single
instruction can be parsed, printed and run without a whole program. -/
def moduleOf (body : String) : String :=
  "define i64 @f(ptr %p, i64 %k) {\nentry:\n" ++ body ++ "\n  ret i64 0\n}\n"

/-- Parse a module holding the given instruction lines. -/
def parseWith (body : String) : Except String Module :=
  parseModule (moduleOf body)

/-- The instruction a one-line body parses to, when it parses. -/
def instrsOf (body : String) : Option (List Instr) :=
  match parseWith body with
  | .ok ⟨_, [f]⟩ => f.blocks.map (·.instrs) |>.head?
  | _ => none

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The body parses, and every token names part of the refusal of the printed
text. -/
def refusedWith (body : String) (tokens : List String) : Bool :=
  match parseWith body with
  | .error e => tokens.all (mentions e)
  | .ok _ => false

/-- The body parses. -/
def accepted (body : String) : Bool :=
  match parseWith body with
  | .ok _ => true
  | .error _ => false

/-- Whether a printed instruction parses back to itself, as the only
instruction of a one-line function body. -/
def rendersTo (i : Instr) : Bool :=
  match parseWith (Instr.render i) with
  | .ok ⟨_, [f]⟩ => (f.blocks.map (·.instrs)).head? = some [i]
  | _ => false

/-- Whether the printed form of a one-line body's instruction parses back to
that instruction. -/
def reparses (body : String) : Bool :=
  match instrsOf body with
  | some [i] => rendersTo i
  | _ => false

/-! ### Running one instruction -/

/-- A state with the given registers and memory, at the entry block. -/
def stateOf (env : Env) (mem : Mem := []) : State :=
  { env := env, mem := mem, next := 0, pc := "entry", pre := none }

/-- Run the one instruction of a body under `calls` and read back the register
`%r`.  `none` is a parse or shape failure; `some none` is undefined behaviour;
`some (some v)` is the value bound to `%r`. -/
def runOne (calls : Calls) (env : Env) (body : String) : Option (Option Value) :=
  match instrsOf body with
  | some [i] =>
      match evalInstr calls (stateOf env) i with
      | some s => some (lookupName s.env "%r")
      | none => none
  | _ => none

/-- The memory a one-instruction body leaves, when it runs. -/
def memOf (env : Env) (body : String) : Option Mem :=
  match instrsOf body with
  | some [i] => (evalInstr noCalls (stateOf env) i).map (·.mem)
  | _ => none

/-! ### The three vector-byte tables the checks read

A 32-lane table whose lane `k` is `k`, and a control that exercises each rule of
the lane-local lookup: a low-nibble selection within the first lane, bit 7 set,
both nibbles of the second lane, and the high bits of a control byte. -/

def table32 : List (BitVec 8) := (List.range 32).map fun i => BitVec.ofNat 8 i

def control32 : List (BitVec 8) :=
  (List.range 32).map fun i =>
    match i with
    | 0 => 0x11    -- 17: low nibble 1, so table lane 1
    | 5 => 0x85    -- bit 7 set, so zero
    | 17 => 0x01   -- lane base 16: table lane 17, not 1
    | 21 => 0x7F   -- bits 4-6 set but bit 7 clear: table lane 16 + 15
    | _ => 0x00    -- table lane 0 of the byte's own 16-byte half

/-- The intrinsic environment the checks run under: the five modelled symbols,
each evaluated by the Lean definition it is named after.  It is local to this
check so the forms can be exercised without the pinned fixture; the library's
environment for the same five symbols lives with that fixture in
`LeanLLVM/Vellum/JsonS1MasksIR.lean`, built from the same definitions, and the
two can differ only in a symbol name. -/
def fragmentCalls : Calls
  | "llvm.x86.avx2.pshuf.b", [.vec 32 8 table, .vec 32 8 control], mem, next =>
      some { ret := .vec 32 8 (pshufbLanes table control), mem := mem, next := next }
  | "llvm.x86.pclmulqdq", [.vec 2 64 a, .vec 2 64 b, .int 8 _], mem, next =>
      match a, b with
      | [a0, _], [b0, _] =>
          some { ret := .vec 2 64 [clmul a0 b0, 0], mem := mem, next := next }
      | _, _ => none
  | "llvm.x86.bmi.pext.64", [.int 64 a, .int 64 m], mem, next =>
      some { ret := .int 64 (pext a m), mem := mem, next := next }
  | "llvm.x86.bmi.pdep.64", [.int 64 a, .int 64 m], mem, next =>
      some { ret := .int 64 (pdep a m), mem := mem, next := next }
  | "llvm.ctlz.i64", [.int 64 a, .int 1 _], mem, next =>
      some { ret := .int 64 (BitVec.ofNat 64 (ctlz a)), mem := mem, next := next }
  | _, _, _, _ => none

/-! ### `shufflevector` -/

def shuffleBody : String :=
  "  %r = shufflevector <2 x i8> %a, <2 x i8> %b, <4 x i32> <i32 0, i32 1, i32 3, i32 2>"

#guard accepted shuffleBody
#guard reparses shuffleBody

-- Entry `k < n` reads the first operand and `n ≤ k < 2n` the second.
#guard runOne noCalls [("%a", .vec 2 8 [10, 20]), ("%b", .vec 2 8 [30, 40])]
    shuffleBody = some (some (.vec 4 8 [10, 20, 40, 30]))

-- An entry at `2n` is `ub`.  The parser refuses the text, so this AST is
-- hand-built: it is the semantics' bound, not the parser's.
#guard (evalInstr noCalls
    (stateOf [("%a", .vec 2 8 [10, 20]), ("%b", .vec 2 8 [30, 40])])
    (.shuffleVec "%r" 2 8 (.reg "%a") (.reg "%b") [0, 4])).isNone

-- A mask entry at `2n` is refused by name.
#guard refusedWith
  "  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 2, i32 3, i32 8, i32 5, i32 6, i32 7>"
  ["shufflevector"]

-- An `undef` entry is refused by name: the mask field is a list of naturals.
#guard refusedWith
  "  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 undef, i32 3, i32 4, i32 5, i32 6, i32 7>"
  ["shufflevector"]

-- So is a `poison` entry.
#guard refusedWith
  "  %r = shufflevector <4 x i64> %a, <4 x i64> %a, <8 x i32> <i32 0, i32 1, i32 poison, i32 3, i32 4, i32 5, i32 6, i32 7>"
  ["shufflevector"]

/-! ### A mask store -/

def maskStoreBody : String :=
  "  store <8 x i1> %m, ptr %p"

#guard accepted maskStoreBody
#guard reparses maskStoreBody

-- Lane `k` is bit `k` of the packed word, little-endian: 1 + 4 + 8 + 64 = 77.
#guard memOf [("%m", .vec 8 1 [1, 0, 1, 1, 0, 0, 1, 0]), ("%p", .ptr 0)] maskStoreBody
  = some [(0, (0x4D : UInt8))]

-- A mask whose total width is not whole bytes has no byte layout.
#guard refusedWith "  store <5 x i1> %m, ptr %p" ["store"]

-- A vector store that is not a mask is refused: `<32 x i8>` has no packing rule
-- here even though its total width is whole.
#guard refusedWith "  store <32 x i8> %v, ptr %p" ["store"]

/-! ### A non-mask vector `bitcast` -/

def bitcastBody : String :=
  "  %r = bitcast <4 x i16> %v to <8 x i8>"

#guard accepted bitcastBody
#guard reparses bitcastBody

-- The reinterpretation is little-endian and lane-ordered.
#guard runOne noCalls [("%v", .vec 4 16 [0x1234, 0x5678, 0x9ABC, 0xDEF0])]
    bitcastBody = some (some (.vec 8 8 [0x34, 0x12, 0x78, 0x56, 0xBC, 0x9A, 0xF0, 0xDE]))

-- The observed widening, `<4 x i64>` to `<32 x i8>`, is the same rule.
#guard accepted "  %r = bitcast <4 x i64> %v to <32 x i8>"
#guard reparses "  %r = bitcast <4 x i64> %v to <32 x i8>"

-- The width disagreement is refused by name.
#guard refusedWith "  %r = bitcast <4 x i64> %v to <16 x i8>" ["bitcast"]

-- A vector of non-integer elements is refused by the type grammar, before the
-- bitcast rule reads it; the refusal names the element type.
#guard refusedWith "  %r = bitcast <4 x i64> %v to <8 x ptr>" ["ptr"]

-- A different total width, or a scalar destination, keeps the mask pack's
-- neighbour refused as before.
#guard refusedWith "  %r = bitcast <32 x i8> %v to i32" ["bitcast"]

/-! ### Vector shifts -/

def lshrBody : String :=
  "  %r = lshr <4 x i16> %a, splat (i16 4)"

def shlBody : String :=
  "  %r = shl <4 x i16> %a, splat (i16 4)"

#guard accepted lshrBody
#guard reparses lshrBody
#guard accepted shlBody
#guard reparses shlBody

#guard runOne noCalls [("%a", .vec 4 16 [0x00F0, 0x1234, 0xFFFF, 0x8000])] lshrBody
  = some (some (.vec 4 16 [0x000F, 0x0123, 0x0FFF, 0x0800]))

#guard runOne noCalls [("%a", .vec 4 16 [0x00F0, 0x1234, 0xFFFF, 0x8000])] shlBody
  = some (some (.vec 4 16 [0x0F00, 0x2340, 0xFFF0, 0x0000]))

-- The signed shift stays refused, by name.
#guard refusedWith "  %r = ashr <4 x i16> %a, splat (i16 4)" ["ashr"]

/-! ### The five intrinsic spellings -/

def pshufbBody : String :=
  "  %r = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %a, <32 x i8> %c)"

def pclmulBody : String :=
  "  %r = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %a, <2 x i64> %b, i8 0)"

def pextBody : String :=
  "  %r = call i64 @llvm.x86.bmi.pext.64(i64 %a, i64 %m)"

def pdepBody : String :=
  "  %r = call i64 @llvm.x86.bmi.pdep.64(i64 %a, i64 %m)"

def ctlzBody : String :=
  "  %r = call i64 @llvm.ctlz.i64(i64 %a, i1 false)"

#guard accepted pshufbBody
#guard reparses pshufbBody
#guard accepted pclmulBody
#guard reparses pclmulBody
#guard accepted pextBody
#guard reparses pextBody
#guard accepted pdepBody
#guard reparses pdepBody
#guard accepted ctlzBody
#guard reparses ctlzBody

/-! #### `pshuf.b` is lane-local -/

-- Lane 0 selects table lane 1.
#guard (pshufbLanes table32 control32)[0]? = some (1 : BitVec 8)
-- Bit 7 of the control byte zeroes the result byte.
#guard (pshufbLanes table32 control32)[5]? = some (0 : BitVec 8)
-- Lane 17 addresses table lane 16 + 1, not lane 1: the linear reading gives 1.
#guard (pshufbLanes table32 control32)[17]? = some (17 : BitVec 8)
-- Bits 4 through 6 are ignored: with bit 7 clear the low nibble selects 15.
#guard (pshufbLanes table32 control32)[21]? = some (31 : BitVec 8)
-- The result has one lane per control lane.
#guard (pshufbLanes table32 control32).length = 32

-- The parsed call evaluates to exactly the definition on the same operands.
#guard runOne fragmentCalls
    [("%a", .vec 32 8 table32), ("%c", .vec 32 8 control32)] pshufbBody
  = some (some (.vec 32 8 (pshufbLanes table32 control32)))

/-! #### The other four intrinsics -/

-- Immediate 0 takes both operands' low lanes; lane 1 of the result is zero.
-- `clmul 3 5 = 15` (the polynomial product `(x + 1)(x² + 1)`).
#guard runOne fragmentCalls [("%a", .vec 2 64 [3, 9]), ("%b", .vec 2 64 [5, 7])]
    pclmulBody = some (some (.vec 2 64 [15, 0]))

-- `pext 0b1011 0b1010 = 0b11`: the selected lanes compacted to the low positions.
#guard runOne fragmentCalls [("%a", .int 64 11), ("%m", .int 64 10)] pextBody
  = some (some (.int 64 3))

-- `pdep 0b11 0b1010 = 0b1010`: the low lanes scattered into the mask's lanes.
#guard runOne fragmentCalls [("%a", .int 64 3), ("%m", .int 64 10)] pdepBody
  = some (some (.int 64 10))

-- `ctlz 1 = 63` at 64 bits; the zero word would give 64.
#guard runOne fragmentCalls [("%a", .int 64 1)] ctlzBody
  = some (some (.int 64 63))

/-! #### The neighbouring intrinsic spellings are refused by name -/

-- `pshuf.b` with three arguments.
#guard refusedWith
  "  %r = call <32 x i8> @llvm.x86.avx2.pshuf.b(<32 x i8> %a, <32 x i8> %a, <32 x i8> %a)"
  ["pshuf.b"]

-- `pshuf.b` at another vector type.
#guard refusedWith
  "  %r = call <16 x i8> @llvm.x86.avx2.pshuf.b(<16 x i8> %a, <16 x i8> %a)"
  ["pshuf.b"]

-- `pclmulqdq` at an immediate other than 0.
#guard refusedWith
  "  %r = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %a, <2 x i64> %b, i8 1)"
  ["pclmulqdq"]

-- `pclmulqdq` with a register where the immediate belongs.
#guard refusedWith
  "  %r = call <2 x i64> @llvm.x86.pclmulqdq(<2 x i64> %a, <2 x i64> %b, i8 %k)"
  ["pclmulqdq"]

-- `pext.32` and `pdep.32`: the width is part of the intrinsic's name.
#guard refusedWith "  %r = call i32 @llvm.x86.bmi.pext.32(i32 %a, i32 %a)" ["pext"]
#guard refusedWith "  %r = call i32 @llvm.x86.bmi.pdep.32(i32 %a, i32 %a)" ["pdep"]

-- `pext.64` at another operand type.
#guard refusedWith "  %r = call i64 @llvm.x86.bmi.pext.64(i32 %a, i32 %a)" ["pext"]

-- `ctlz` with the poison flag.
#guard refusedWith "  %r = call i64 @llvm.ctlz.i64(i64 %a, i1 true)" ["ctlz"]

-- The unmodelled vector operations the emission does not contain.
#guard refusedWith "  %r = umin <32 x i8> %a, %a" ["umin"]
#guard refusedWith "  %r = umax <32 x i8> %a, %a" ["umax"]

end VectorS1
