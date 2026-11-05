/-
The `getelementptr` scenario: the shapes the model reads, the canonical text
they print, the shapes it refuses, and the address the step computes.

`getelementptr [inbounds] <elemTy>, ptr %base, iN %off` offsets a pointer by
`%off` **elements** of type `<elemTy>`: the step is `base + off * sizeof(elemTy)`.
The admitted element widths are the ones the model pins as having the same
**allocated** size on the modelled datalayout as the stored size it scales by —
`i1`, `i7`, `i8`, `i16`, `i32`, `i64` and `i128`; the list is an allowlist, so a
width outside it is refused even where its two sizes would agree.  `Ty.sizeBytes` is a store size, so a width such
as `i24` (stores 3, allocated 4) or `i48` (stores 6, allocated 8) would give this
model one address and LLVM another; the parser refuses those by name instead of
approximating them.

So `getelementptr i32, ptr %p, i64 1` from `%p = 100` reads 104 — the byte-offset
reading, which would add one, is a different answer.  `i8` is the element type
whose size is one, so every `getelementptr i8` computes exactly the byte count
the earlier model computed, and the `i8` assertions below are the control for
that.

The index is sign-extended to 64 bits and a negative offset is undefined.  That
refusal is load-bearing at a typed element: a negative index would mean
`base - k * sizeof(elemTy)`, so admitting it would change what the instruction
computes rather than merely widen the model, and pointers here are bare
addresses with no object to walk backwards inside.  The bound is on the index,
not on the address: with an `i128` element type an index below `2 ^ 63` scales to
an address at or above `2 ^ 64`, where the `inbounds` the printer always emits
would poison the pointer in LLVM — a behaviour this model does not represent.

A base that is not a `ptr`, a second index, an index type that is not an integer
no wider than 64 bits, an integer element width outside the admitted set, a
non-integer element type, and the `inrange`/`nuw`/`nusw` modifiers are each
refused by a message naming what was refused.  `inbounds` is accepted and dropped, and the printer emits it again, so
the round trip is stable.

Several refusals are produced by the type parser rather than the `getelementptr`
branch, because the element token is read as a type first: an aggregate such as
`[8 x i8]`, a named struct such as `%struct.P` and a vector such as `<4 x i32>`
fail there with `unsupported type`, naming the first token it read (`[`,
`%struct.P`, `<`).  A scalar type that parses but cannot size a step — `ptr`,
`void` — and an integer width outside the admitted set fail in the
`getelementptr` branch, with that branch's wording.  The checks below assert
which wording each shape gets, and that the other branch's wording is absent, so
the routing is checked rather than assumed.

The parser compares string tokens and does not reduce in the kernel, so every
check here is a `#guard` rather than a `decide`d proposition.

Elaborated by `nix develop -c lake env lean tests/getelementptr.lean`.  A
`#guard` that does not hold stops elaboration with a nonzero exit status;
nothing outside the elaborated program is written.
-/
import LeanLLVM

namespace GetElementPtr

open LeanLLVM

/-! ### Reading a single instruction line -/

/-- One function whose body is the given instruction line, so the parse of a
single `getelementptr` is observable without a whole program. -/
def moduleOf (line : String) : String :=
  "define ptr @f(ptr %p, i32 %k) {\nentry:\n" ++ line ++ "\n  ret ptr %q\n}\n"

/-- Parse a module holding one `getelementptr` line. -/
def parseWith (line : String) : Except String Module :=
  parseModule (moduleOf line)

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- Whether an instruction's printed form parses back to that instruction, as the
only instruction of a one-line function body. -/
def reparses (i : Instr) : Bool :=
  match parseModule (moduleOf (Instr.render i)) with
  | .ok ⟨_, f :: _⟩ => (f.blocks.map (·.instrs)).head? = some [i]
  | _ => false

/-- Whether the run returned the given integer value. -/
def returnsInt (o : Option Outcome) (w : Nat) (v : Nat) : Bool :=
  match o with
  | some (.ret (some (.int w' x)) _) => w' = w && x = BitVec.ofNat w' v
  | _ => false

/-- The instruction the one-line module parsed to, when it parsed. -/
def instrsOf (line : String) : Option (List Instr) :=
  match parseWith line with
  | .ok ⟨_, [f]⟩ => f.blocks.map (·.instrs) |>.head?
  | _ => none

/-- The refusal of a line, when the parser refuses it and the message names each
of `tokens`.  `false` when the line parses, or when the message names something
else. -/
def refusedWith (line : String) (tokens : List String) : Bool :=
  match parseWith line with
  | .error e => tokens.all (mentions e)
  | .ok _ => false

/-- The refusal of a line, when the parser refuses it, the message names each of
`tokens`, and it names none of `absent`.  The absent half is what distinguishes
the branch that produced the refusal from one that would have produced another
message for the same input. -/
def refusedWithOut (line : String) (tokens absent : List String) : Bool :=
  match parseWith line with
  | .error e => tokens.all (mentions e) && absent.all (fun t => !mentions e t)
  | .ok _ => false

/-! ### The accepted shapes -/

/-- The plain form, which an emitted body writes. -/
def gepRegister : String := "  %q = getelementptr i8, ptr %p, i64 %k"

/-- The same instruction with the `inbounds` modifier, the form clang emits for
pointer arithmetic. -/
def gepInbounds : String := "  %q = getelementptr inbounds i8, ptr %p, i64 %k"

/-- The same instruction with a narrower register index. -/
def gepNarrow : String := "  %q = getelementptr i8, ptr %p, i32 %k"

/-- The same instruction with a literal index. -/
def gepLiteral : String := "  %q = getelementptr i8, ptr %p, i32 7"

/-- A scaled element type, with a register index.  The element type is a field,
so this is a different instruction from `gepRegister`, not the same one written
another way. -/
def gepWide : String := "  %q = getelementptr i32, ptr %p, i64 %k"

/-- A scaled element type written with `inbounds` and a literal index, the form
clang emits when it walks an array of words. -/
def gepWideLiteral : String := "  %q = getelementptr inbounds i64, ptr %p, i32 2"

-- The affirmative controls: these lines parse, and to exactly one instruction
-- of the expected shape.  A parser that refused every `getelementptr` would
-- fail here, so the refusals below cannot pass by refusing everything.
#guard instrsOf gepRegister = some [.gep "%q" (.int 8) (.reg "%p") (.reg "%k")]

#guard instrsOf gepLiteral =
  some [.gep "%q" (.int 8) (.reg "%p") (.imm (.int 32 (BitVec.ofNat 32 7)))]

-- The element type is kept: an `i32` element type parses to an instruction
-- whose field is `i32`, and whose step will therefore be scaled by four.
#guard instrsOf gepWide = some [.gep "%q" (.int 32) (.reg "%p") (.reg "%k")]

#guard instrsOf gepWideLiteral =
  some [.gep "%q" (.int 64) (.reg "%p") (.imm (.int 32 (BitVec.ofNat 32 2)))]

-- Every admitted width parses, and the width it parsed is the width it keeps:
-- dropping one from `Ty.gepElemAdmitted`, or admitting a width it does not name,
-- fails here.
#guard [1, 7, 8, 16, 32, 64, 128].all fun w =>
  instrsOf s!"  %q = getelementptr i{w}, ptr %p, i64 %k" =
    some [.gep "%q" (.int w) (.reg "%p") (.reg "%k")]

-- The admitted set is exactly those seven: a width it does not name is refused,
-- whether or not its two sizes would agree, because the model establishes the
-- match for the seven and computes no allocated size.
#guard [2, 3, 24, 33, 48, 96].all fun w =>
  (instrsOf s!"  %q = getelementptr i{w}, ptr %p, i64 %k").isNone

-- `inbounds` is accepted and discarded: it is not a field of the instruction,
-- so the two texts parse to the same AST.  A narrower index type is discarded
-- for the same reason: the instruction carries the index's value, not its
-- width, and the semantics sign-extends whatever it is given.
#guard instrsOf gepInbounds = instrsOf gepRegister

#guard instrsOf gepNarrow = instrsOf gepRegister

/-! ### The canonical text -/

-- A register index prints as `i64`, the width the semantics sign-extends to,
-- and a literal keeps its own width.  Both forms parse back to the same
-- instruction, which is what makes the emitter's round-trip check a check.
#guard Instr.render (.gep "%q" (.int 8) (.reg "%p") (.reg "%k")) =
  "  %q = getelementptr inbounds i8, ptr %p, i64 %k"

#guard Instr.render (.gep "%q" (.int 8) (.reg "%p") (.imm (.int 32 7))) =
  "  %q = getelementptr inbounds i8, ptr %p, i32 7"

-- The element type is printed as it was parsed, not as `i8`: the canonical form
-- of a scaled offset keeps the scale, which is what makes the printed text mean
-- the same instruction.
#guard Instr.render (.gep "%q" (.int 32) (.reg "%p") (.reg "%k")) =
  "  %q = getelementptr inbounds i32, ptr %p, i64 %k"

#guard Instr.render (.gep "%q" (.int 64) (.reg "%p") (.imm (.int 32 2))) =
  "  %q = getelementptr inbounds i64, ptr %p, i32 2"

-- The printed module parses back to the module it came from, for the byte form
-- and for the scaled one.
#guard
  match parseWith gepInbounds with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

#guard
  match parseWith gepWide with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

-- The narrower text prints in the canonical form and re-parses to the same
-- instruction: the dropped width is recovered as `i64`, not as `i32`.
#guard
  match parseWith gepNarrow with
  | .ok m =>
      parseModule (Module.render m) = .ok m ∧
        mentions (Module.render m) "getelementptr inbounds i8, ptr %p, i64 %k"
  | .error _ => false

-- The printed form of a typed offset parses and prints to the same text, which
-- is where a type dropped on the way out would surface as a different
-- instruction (`i8` scale) rather than as a refusal.
#guard
  match instrsOf gepWide with
  | some [i] => reparses i
  | _ => false

/-! ### The refused shapes -/

-- The detector the refusals are read with, on the message a refusal really
-- produces: `mentions` finds the modifier the message names, and does not find
-- a token the message does not carry.  Without this, a `mentions` that matched
-- nothing would make every refusal below vacuous.
#guard
  match parseWith "  %q = getelementptr nuw i8, ptr %p, i64 %k" with
  | .error e => mentions e "nuw" ∧ !mentions e "inbounds"
  | .ok _ => false

-- The detector's other side: an accepted line is not reported as a refusal, so
-- `refusedWith` is not a predicate that answers `true` to everything.
#guard refusedWith gepRegister ["getelementptr"] = false

-- An integer width whose allocated size differs from the stored size the step
-- scales by: `i24` stores three bytes in four, `i33` stores five in eight and
-- `i48` stores six in eight on the modelled datalayout.  The `getelementptr`
-- branch refuses each by name, with that reason, so a step scaled by the stored
-- size cannot silently give an address LLVM does not.
#guard refusedWith "  %q = getelementptr i24, ptr %p, i64 %k"
  ["element width i24", "stored size", "allocated and stored size",
   "i1, i7, i8, i16, i32, i64 and i128"]
#guard refusedWith "  %q = getelementptr i33, ptr %p, i64 %k"
  ["element width i33", "where the two differ"]
#guard refusedWith "  %q = getelementptr i48, ptr %p, i64 %k"
  ["element width i48", "one address here and another by LLVM"]

-- `i2` is allocated 1 byte for a stored 1 — the two sizes agree — and is still
-- refused, because the model pins only the seven and computes no allocated size.
-- The refusal is the list's, and the message says so rather than claiming a
-- divergence `i2` does not have.
#guard refusedWith "  %q = getelementptr i2, ptr %p, i64 %k"
  ["element width i2", "only i1, i7, i8, i16, i32, i64 and i128 are admitted"]

-- A scalar element type that parses but has no integer size: the
-- `getelementptr` branch refuses it, naming the token and the scaling reason.
#guard refusedWithOut "  %q = getelementptr ptr, ptr %p, i64 %k"
  ["getelementptr element type 'ptr'", "pointer or void"] ["unsupported type"]

#guard refusedWith "  %q = getelementptr void, ptr %p, i64 %k"
  ["getelementptr element type 'void'", "pointer or void"]

-- A vector element type is refused by the type parser, which names the `<` it
-- read; that is a different branch's wording, so it is asserted as such.
#guard refusedWithOut "  %q = getelementptr <4 x i32>, ptr %p, i64 %k"
  ["unsupported type '<'"] ["getelementptr element type"]

-- An aggregate element type is refused by the type parser, which is where the
-- element token is read as a type.  The assertion names that branch's wording
-- and the token it read, and rules out the `getelementptr` branch's wording —
-- so a change that rerouted this refusal is visible here.
#guard refusedWithOut "  %q = getelementptr [8 x i8], ptr %p, i64 %k"
  ["unsupported type '['"] ["getelementptr element type"]

-- A named struct element type, likewise refused by the type parser.
#guard refusedWithOut "  %q = getelementptr %struct.P, ptr %p, i64 %k"
  ["unsupported type '%struct.P'"] ["getelementptr element type"]

-- A base that is not a `ptr`.
#guard refusedWith "  %q = getelementptr i8, i32 %p, i64 %k" ["base type", "i32"]

-- A second index is refused, rather than dropped or read as part of the first.
#guard refusedWithOut "  %q = getelementptr i8, ptr %p, i64 %k, i64 1"
  ["more than one index"] ["unsupported type"]

-- An index type that is not an integer type.
#guard refusedWith "  %q = getelementptr i8, ptr %p, ptr %k" ["index type", "ptr"]

-- An index wider than 64 bits is refused rather than truncated: the truncation
-- would silently change the address the body computes.
#guard refusedWithOut "  %q = getelementptr i8, ptr %p, i128 %k"
  ["index width i128", "truncated"] ["unsupported type"]

-- The same width refusal at a scaled element type: the scaling is no reason to
-- accept an index the step would truncate.
#guard refusedWith "  %q = getelementptr i32, ptr %p, i128 %k" ["index width i128", "truncated"]

-- The modifiers that constrain the offset, each refused by name: the instruction
-- has no field for them, and dropping one would accept a narrower promise than
-- the text carries.
#guard refusedWith "  %q = getelementptr inrange(0, 4) i8, ptr %p, i64 %k" ["inrange"]
#guard refusedWith "  %q = getelementptr nuw i8, ptr %p, i64 %k" ["nuw"]
#guard refusedWith "  %q = getelementptr nusw i8, ptr %p, i64 %k" ["nusw"]
#guard refusedWith "  %q = getelementptr inbounds nuw i8, ptr %p, i64 %k" ["nuw"]

/-! ### The address the step computes -/

/-- The address the step computes for `%q = getelementptr <elemTy>, ptr %p, <w>-bit
<off>` starting from `%p = 100`, or `none` when the step refuses the offset. -/
def gepAddress? (elemTy : Ty) (w : Nat) (off : Int) : Option Nat :=
  match evalInstr noCalls
      { env := [("%p", .ptr 100)], mem := [], next := 0, pc := "entry", pre := none }
      (.gep "%q" elemTy (.reg "%p") (.imm (.int w (BitVec.ofInt w off)))) with
  | some s =>
      match lookupName s.env "%q" with
      | some (.ptr a) => some a
      | _ => none
  | none => none

-- One address per admitted width family, so a change to `Ty.sizeBytes` is caught
-- here rather than in a proof: `i1`, `i7` and `i8` are one byte, `i16` is two,
-- `i32` four, `i64` eight and `i128` sixteen.
#guard gepAddress? (.int 1) 64 1 = some 101
#guard gepAddress? (.int 7) 64 1 = some 101
#guard gepAddress? (.int 8) 64 1 = some 101
#guard gepAddress? (.int 16) 64 1 = some 102

-- The discriminating case: an `i32` element type at index 1 adds four bytes, so
-- the address is 104.  The byte-offset reading of the same instruction would
-- answer 101, which is exactly the value the `i8` control above gives — so the
-- two assertions differ, and a step that ignored the element type would fail
-- the `i32` one.
#guard gepAddress? (.int 32) 64 1 = some 104
#guard gepAddress? (.int 64) 64 1 = some 108
#guard gepAddress? (.int 128) 64 1 = some 116

-- Index 2 of an `i64` element type is sixteen bytes.
#guard gepAddress? (.int 64) 64 2 = some 116

-- The byte element type keeps the address the earlier model computed at every
-- index, which is the control that the scaling did not change the byte form.
#guard gepAddress? (.int 8) 64 0 = some 100
#guard gepAddress? (.int 8) 64 3 = some 103

-- The sign-extension at each width the parser accepts, with an offset whose top
-- bit is clear: `127`, `2^31 - 1` and `2^63 - 1` are each scaled by the byte
-- element type's size of one and added to the base.
#guard gepAddress? (.int 8) 8 127 = some 227
#guard gepAddress? (.int 8) 32 2147483647 = some 2147483747
#guard gepAddress? (.int 8) 64 9223372036854775807 = some 9223372036854775907

-- The negative sign of each width is undefined behaviour: `i8 0x80`,
-- `i32 0x80000000` and `i64 -1` are refused, and so is `i64 2^63`.  The three
-- accepted offsets above are this check's control: the step refuses these and
-- not everything.  At a typed element a negative index would subtract
-- `k * sizeof(elemTy)`, so this is the only sound answer short of modelling
-- pointer arithmetic backwards.
#guard gepAddress? (.int 8) 8 (-128) = none
#guard gepAddress? (.int 32) 32 (-2147483648) = none
#guard gepAddress? (.int 64) 64 (-1) = none
#guard gepAddress? (.int 64) 64 9223372036854775808 = none

-- The negative offset in the textual form the refusals use: the parser accepts
-- it as a literal, and the step refuses it.  Both halves are checked, so the
-- restriction is the semantics' and not the parser's by accident.
#guard
  match parseWith "  %q = getelementptr i8, ptr %p, i64 -1" with
  | .ok _ => gepAddress? (.int 8) 64 (-1) = none
  | .error _ => false

-- A base that is not a pointer, and an index that is not an integer, are
-- undefined rather than coerced.
#guard
  (evalInstr noCalls
    { env := [("%p", .int 64 1), ("%k", .int 64 1)], mem := [], next := 0, pc := "entry",
      pre := none }
    (.gep "%q" (.int 32) (.reg "%p") (.reg "%k"))).isSome = false

#guard
  (evalInstr noCalls
    { env := [("%p", .ptr 8), ("%k", .ptr 8)], mem := [], next := 0, pc := "entry",
      pre := none }
    (.gep "%q" (.int 32) (.reg "%p") (.reg "%k"))).isSome = false

/-! ### The scaled offset through a whole program -/

/-- A body that writes distinct bytes one and four bytes past `%p` and reads the
byte the typed offset names.  The byte offsets are written with `i8` offsets, so
the only scaled instruction is the one under test. -/
def gepStrideProgram (elemTy : String) : String :=
"define i32 @gep_stride(ptr %p) {
entry:
  %b1 = getelementptr inbounds i8, ptr %p, i64 1
  store i8 9, ptr %b1
  %b4 = getelementptr inbounds i8, ptr %p, i64 4
  store i8 7, ptr %b4
  %q = getelementptr inbounds " ++ elemTy ++ ", ptr %p, i64 1
  %v = load i8, ptr %q
  %w = zext i8 %v to i32
  ret i32 %w
}
"

def gepStrideRun (elemTy : String) : Option Outcome :=
  match parseModule (gepStrideProgram elemTy) with
  | .ok ⟨_, f :: _⟩ => run noCalls f [.ptr 100]
  | _ => none

-- Through the parser, the semantics and the memory model: `i32` at index 1 names
-- the byte at 104, which this body wrote as 7.  A byte-offset reading would name
-- 101, which it wrote as 9, so the two readings differ in the answer here too.
#guard returnsInt (gepStrideRun "i32") 32 7

-- The control: the `i8` form names the byte at 101 and answers 9.
#guard returnsInt (gepStrideRun "i8") 32 9

/-! ### The instruction's projections -/

-- The offset is a pure value instruction that defines its destination and reads
-- both operands, so a pass that walks registers or a pure set sees it.
#guard Instr.dst? (.gep "%q" (.int 32) (.reg "%p") (.reg "%k")) = some "%q"
#guard Instr.uses (.gep "%q" (.int 32) (.reg "%p") (.imm (.int 64 4))) = ["%p"]
#guard Instr.isPure (.gep "%q" (.int 32) (.reg "%p") (.reg "%k")) = true

end GetElementPtr
