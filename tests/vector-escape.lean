/-
The lane-wise `select` the escape emission carries: the form the fragment gains
for `select <16 x i1> %c, <16 x i8> %a, <16 x i8> %b`, its lane-by-lane
meaning, its printed round trip, and the three neighbouring shapes the parser
refuses by name.

LLVM's `select` on a vector condition is vectorised: lane `j` of the result is
lane `j` of the first operand where the condition's lane `j` is set, and lane
`j` of the second where it is clear.  There is no reading in which the mask is
tested as a whole, so the checks below are written at conditions that differ
per lane — a uniform condition cannot tell the two readings apart.

The form is the emitted one, taken from `probes/install/ir/json-escape.candidate.ll`
(`us_hex4_pshufb`'s `_mm_and_si128(isa, _mm_set1_epi8(9))`):

* `select <16 x i1> %cmp, <16 x i8> <i8 9, …>, <16 x i8> <i8 0, …>`

The refusals, one text each: a scalar `i1` condition with vector operands; a
vector condition whose element type is not `i1`; operands whose lane counts
disagree (the condition's lane count against the operands', and the two
operands' against each other); operands of one lane count but a different lane
width; a vector condition with scalar operands; and a scalar condition that is
not `i1`.

`evalInstr_select_lanes` is the step lemma: the instruction evaluates to the
lane-wise definition `selectLanes`, on the shapes the instruction fixes.  Its
axiom footprint is pinned below.

The escape unit's three intrinsic call spellings are checked the same way, in
the same run: `llvm.umin.i32` at `i32 (i32, i32)`,
`llvm.x86.sse2.pmadd.wd` at `<4 x i32> (<8 x i16>, <8 x i16>)` and
`llvm.x86.ssse3.pmadd.ub.sw.128` at `<8 x i16> (<16 x i8>, <16 x i8>)`, each
accepted at the emitted shape, printed back to itself, and refused by name at
another width, arity, operand type or result type — including the neighbouring
symbols `llvm.umin.i64`, `llvm.x86.ssse3.pmadd.ub.sw` and
`llvm.x86.sse2.pmadd.ub.sw.128`.

Elaborated by `nix develop -c lake env lean tests/vector-escape.lean`.  A
`#guard` that does not hold stops elaboration with a nonzero exit status; no
compiler, proof checker, service, clock or network is reached.
-/
import LeanLLVM

namespace VectorEscape

open LeanLLVM

/-! ### Reading a single instruction line -/

/-- One function whose body is the given instruction lines, so a parse of one
instruction is observable without a whole program. -/
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

/-- The body parses, and every token names part of the refusal of the text. -/
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

/-! ### The emitted spelling -/

/-- The `select` line the escape emission writes in `us_hex4_pshufb`: a
`<16 x i1>` condition and two `<16 x i8>` lane lists, the first four lanes of
the first operand set and the rest zero. -/
def emittedSelectBody : String :=
  "  %r = select <16 x i1> %cmp, <16 x i8> <i8 9, i8 9, i8 9, i8 9, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>, <16 x i8> <i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0, i8 0>"

#guard accepted emittedSelectBody
#guard reparses emittedSelectBody

-- The instruction's type is the operands': `<16 x i8>`, not the condition's
-- `<16 x i1>`.  The condition's type is not a field; the printer recovers it
-- from this one.
#guard match instrsOf emittedSelectBody with
  | some [i] => i.resultTy = some (.vec 16 (.int 8))
  | _ => false

-- The emitted line evaluates to its lane-wise definition: the first four lanes
-- come from the first operand's `9` and the remaining twelve from the second
-- operand's `0`.  An all-lanes reading would answer `9` at every lane, and a
-- uniform test would answer one operand's whole vector.
#guard runOne noCalls
    [("%cmp", .vec 16 1 (List.replicate 4 1 ++ List.replicate 12 0))] emittedSelectBody
  = some (some (.vec 16 8
      (List.replicate 4 (BitVec.ofNat 8 9) ++ List.replicate 12 0)))

-- The same rule at four lanes, with the condition written per lane, so the
-- lane-wise reading and a uniform "any lane set" reading give different
-- answers: lanes 0 and 2 take the first operand, lanes 1 and 3 the second.
def fourLaneBody : String :=
  "  %r = select <4 x i1> %cmp, <4 x i8> %a, <4 x i8> %b"

#guard accepted fourLaneBody
#guard reparses fourLaneBody

#guard runOne noCalls
    [("%cmp", .vec 4 1 [1, 0, 1, 0]), ("%a", .vec 4 8 [10, 11, 12, 13]),
      ("%b", .vec 4 8 [20, 21, 22, 23])] fourLaneBody
  = some (some (.vec 4 8 [10, 21, 12, 23]))

-- One set lane and three clear ones: only lane 0 comes from `%a`.  A reading
-- that tested the condition as a whole would take all of `%a` or all of `%b`.
#guard runOne noCalls
    [("%cmp", .vec 4 1 [1, 0, 0, 0]), ("%a", .vec 4 8 [10, 11, 12, 13]),
      ("%b", .vec 4 8 [20, 21, 22, 23])] fourLaneBody
  = some (some (.vec 4 8 [10, 21, 22, 23]))

-- All clear: every lane comes from `%b`.
#guard runOne noCalls
    [("%cmp", .vec 4 1 [0, 0, 0, 0]), ("%a", .vec 4 8 [10, 11, 12, 13]),
      ("%b", .vec 4 8 [20, 21, 22, 23])] fourLaneBody
  = some (some (.vec 4 8 [20, 21, 22, 23]))

-- All set: every lane comes from `%a`.
#guard runOne noCalls
    [("%cmp", .vec 4 1 [1, 1, 1, 1]), ("%a", .vec 4 8 [10, 11, 12, 13]),
      ("%b", .vec 4 8 [20, 21, 22, 23])] fourLaneBody
  = some (some (.vec 4 8 [10, 11, 12, 13]))

-- The operands may themselves be masks: `<4 x i1>` is the same rule at lane
-- width one.
def maskSelectBody : String :=
  "  %r = select <4 x i1> %cmp, <4 x i1> %a, <4 x i1> %b"

#guard accepted maskSelectBody
#guard reparses maskSelectBody
#guard runOne noCalls
    [("%cmp", .vec 4 1 [1, 0, 1, 0]), ("%a", .vec 4 1 [1, 1, 0, 0]),
      ("%b", .vec 4 1 [0, 0, 1, 1])] maskSelectBody
  = some (some (.vec 4 1 [1, 0, 0, 1]))

-- A condition value of the wrong shape is `ub`, not a whole-value read.  The
-- parser refuses this text; the AST is hand-built, so this is the semantics'
-- shape check.
#guard (evalInstr noCalls
    (stateOf [("%cmp", .vec 4 8 [1, 1, 1, 1]), ("%a", .vec 4 8 [10, 11, 12, 13]),
      ("%b", .vec 4 8 [20, 21, 22, 23])])
    (.select "%r" (.vec 4 (.int 8)) (.reg "%cmp") (.reg "%a") (.reg "%b"))).isNone

/-! ### The three refusals -/

-- A scalar `i1` condition with vector operands: a vector result needs a
-- `<n x i1>` condition, and a whole-value test does not read lanes.
#guard refusedWith
  "  %r = select i1 %c, <4 x i8> %a, <4 x i8> %b"
  ["scalar i1", "vector"]

-- A vector condition whose element type is not `i1`.
#guard refusedWith
  "  %r = select <4 x i8> %c, <4 x i8> %a, <4 x i8> %b"
  ["<n x i1>", "element type"]

-- The condition's lane count against the operands'.
#guard refusedWith
  "  %r = select <4 x i1> %c, <8 x i8> %a, <8 x i8> %b"
  ["lane count"]

-- The two operands' lane counts against each other.
#guard refusedWith
  "  %r = select <4 x i1> %c, <4 x i8> %a, <8 x i8> %b"
  ["lane count"]

-- One lane count but two lane widths: the operands are not equally typed.
#guard refusedWith
  "  %r = select <4 x i1> %c, <4 x i8> %a, <4 x i16> %b"
  ["same type"]

-- A vector condition with scalar operands: the lane count has nothing to
-- agree with.
#guard refusedWith
  "  %r = select <4 x i1> %c, i8 %a, i8 %b"
  ["vector operands"]

-- A scalar condition that is not `i1`, the form's nearest scalar neighbour.
#guard refusedWith
  "  %r = select i8 %c, i8 %a, i8 %b"
  ["i1"]

/-! ### The step lemma -/

/-- The lane-wise select evaluates as its definition: on a `<n x i1>` condition
and two `<n x iw>` operands, lane `j` of the result is `a[j]` where the
condition's lane is set and `b[j]` where it is clear.  The hypotheses are the
operand values and the lane-list lengths the three shape checks establish. -/
theorem evalInstr_select_lanes {calls : Calls} {s : State} {d : String}
    {n w : Nat} {c a b : Operand} {cs : List (BitVec 1)}
    {la lb : List (BitVec w)}
    (hc : evalOperand s c = some (.vec n 1 cs))
    (ha : evalOperand s a = some (.vec n w la)) (hla : la.length = n)
    (hb : evalOperand s b = some (.vec n w lb)) (hlb : lb.length = n) :
    evalInstr calls s (.select d (.vec n (.int w)) c a b) =
      some (s.bind d (.vec n w (selectLanes cs la lb))) := by
  simp [evalInstr, hc, ha, hb, hla, hlb, Value.vecLanes, selectLanes]

/--
info: 'VectorEscape.evalInstr_select_lanes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms evalInstr_select_lanes

-- `selectLanes` is the definition the step lemma names; this reads it directly
-- so the lane order is checked against a literal list as well.
#guard selectLanes ([1, 0, 1, 0] : List (BitVec 1))
    ([10, 11, 12, 13] : List (BitVec 8)) ([20, 21, 22, 23] : List (BitVec 8))
  = ([10, 21, 12, 23] : List (BitVec 8))

/-! ### The three intrinsic spellings the escape unit calls -/

/-- `%r = call i32 @llvm.umin.i32(i32 %a, i32 %b)`. -/
def uminBody : String :=
  "  %r = call i32 @llvm.umin.i32(i32 %a, i32 %b)"

/-- `%r = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)`. -/
def pmaddWdBody : String :=
  "  %r = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)"

/-- `%r = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)`. -/
def pmaddUbSwBody : String :=
  "  %r = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)"

-- The emitted shape parses, prints back to itself, and carries the result type
-- the shape rule pins.
#guard accepted uminBody
#guard reparses uminBody
#guard match instrsOf uminBody with
  | some [i] => i.resultTy = some (.int 32)
  | _ => false

#guard accepted pmaddWdBody
#guard reparses pmaddWdBody
#guard match instrsOf pmaddWdBody with
  | some [i] => i.resultTy = some (.vec 4 (.int 32))
  | _ => false

#guard accepted pmaddUbSwBody
#guard reparses pmaddUbSwBody
#guard match instrsOf pmaddUbSwBody with
  | some [i] => i.resultTy = some (.vec 8 (.int 16))
  | _ => false

/-! #### Every neighbouring spelling is refused by name -/

-- `umin` at another width: the rule covers `i32`, and the width is part of the
-- intrinsic's name.
#guard refusedWith "  %r = call i64 @llvm.umin.i64(i64 %a, i64 %b)"
  ["llvm.umin.i64"]

-- `umin.i32` at another arity.
#guard refusedWith "  %r = call i32 @llvm.umin.i32(i32 %a)"
  ["llvm.umin.i32", "exactly 2"]

-- `umin.i32` at another operand type.
#guard refusedWith "  %r = call i32 @llvm.umin.i32(i64 %a, i64 %b)"
  ["llvm.umin.i32", "operand types"]

-- `umin.i32` at another result type.
#guard refusedWith "  %r = call i64 @llvm.umin.i32(i32 %a, i32 %b)"
  ["llvm.umin.i32", "result type"]

-- `pmadd.wd` with three arguments.
#guard refusedWith
  "  %r = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b, <8 x i16> %c)"
  ["llvm.x86.sse2.pmadd.wd", "exactly 2"]

-- `pmadd.wd` at another element type.
#guard refusedWith
  "  %r = call <4 x i32> @llvm.x86.sse2.pmadd.wd(<4 x i16> %a, <4 x i16> %b)"
  ["llvm.x86.sse2.pmadd.wd", "operand types"]

-- `pmadd.wd` at another result type.
#guard refusedWith
  "  %r = call <8 x i16> @llvm.x86.sse2.pmadd.wd(<8 x i16> %a, <8 x i16> %b)"
  ["llvm.x86.sse2.pmadd.wd", "result type"]

-- `pmadd.ub.sw.128` with three arguments.
#guard refusedWith
  "  %r = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b, <16 x i8> %c)"
  ["llvm.x86.ssse3.pmadd.ub.sw.128", "exactly 2"]

-- `pmadd.ub.sw.128` at another element type.
#guard refusedWith
  "  %r = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw.128(<8 x i8> %a, <8 x i8> %b)"
  ["llvm.x86.ssse3.pmadd.ub.sw.128", "operand types"]

-- The neighbouring symbols, not just wrong shapes of the modelled ones:
-- `pmadd.ub.sw` without `.128`, and the unsigned-byte form under the signed
-- prefix.
#guard refusedWith
  "  %r = call <8 x i16> @llvm.x86.ssse3.pmadd.ub.sw(<16 x i8> %a, <16 x i8> %b)"
  ["llvm.x86.ssse3.pmadd.ub.sw"]
#guard refusedWith
  "  %r = call <4 x i32> @llvm.x86.sse2.pmadd.ub.sw.128(<16 x i8> %a, <16 x i8> %b)"
  ["llvm.x86.sse2.pmadd.ub.sw.128"]

end VectorEscape
