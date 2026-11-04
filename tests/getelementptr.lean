/-
The byte-offset `getelementptr` scenario: the one shape the model reads, the
canonical text it prints, and the shapes it refuses.

`getelementptr [inbounds] i8, ptr %base, iN %off` offsets a pointer by a byte
count.  The index is sign-extended to 64 bits and a negative offset is
undefined; an element type other than `i8`, a base that is not a `ptr`, a second
index, an index type that is not an integer no wider than 64 bits, and the
`inrange`/`nuw`/`nusw` modifiers are each refused by a message naming what was
refused.  `inbounds` is accepted and dropped, and the printer emits it again, so
the round trip is stable.

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

/-! ### The accepted shape -/

/-- The plain form, which an emitted body writes. -/
def gepRegister : String := "  %q = getelementptr i8, ptr %p, i64 %k"

/-- The same instruction with the `inbounds` modifier, the form clang emits for
pointer arithmetic. -/
def gepInbounds : String := "  %q = getelementptr inbounds i8, ptr %p, i64 %k"

/-- The same instruction with a narrower register index. -/
def gepNarrow : String := "  %q = getelementptr i8, ptr %p, i32 %k"

/-- The same instruction with a literal index. -/
def gepLiteral : String := "  %q = getelementptr i8, ptr %p, i32 7"

-- The affirmative controls: these lines parse, and to exactly one instruction
-- of the expected shape.  A parser that refused every `getelementptr` would
-- fail here, so the refusals below cannot pass by refusing everything.
#guard instrsOf gepRegister = some [.gep "%q" (.reg "%p") (.reg "%k")]

#guard instrsOf gepLiteral =
  some [.gep "%q" (.reg "%p") (.imm (.int 32 (BitVec.ofNat 32 7)))]

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
#guard Instr.render (.gep "%q" (.reg "%p") (.reg "%k")) =
  "  %q = getelementptr inbounds i8, ptr %p, i64 %k"

#guard Instr.render (.gep "%q" (.reg "%p") (.imm (.int 32 7))) =
  "  %q = getelementptr inbounds i8, ptr %p, i32 7"

-- The printed module parses back to the module it came from.
#guard
  match parseWith gepInbounds with
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

-- An element type other than `i8` is refused by name: the index is a byte
-- count, so an element type of another size would change the address.
#guard refusedWith "  %q = getelementptr i32, ptr %p, i64 %k" ["element type", "i32"]

-- A base that is not a `ptr`.
#guard refusedWith "  %q = getelementptr i8, i32 %p, i64 %k" ["base type", "i32"]

-- A second index is refused, rather than dropped or read as part of the first.
#guard refusedWith "  %q = getelementptr i8, ptr %p, i64 %k, i64 1" ["more than one index"]

-- An index type that is not an integer type.
#guard refusedWith "  %q = getelementptr i8, ptr %p, ptr %k" ["index type", "ptr"]

-- An index wider than 64 bits is refused rather than truncated: the truncation
-- would silently change the address the body computes.
#guard refusedWith "  %q = getelementptr i8, ptr %p, i128 %k" ["index width i128", "truncated"]

-- The modifiers that constrain the offset, each refused by name: the instruction
-- has no field for them, and dropping one would accept a narrower promise than
-- the text carries.
#guard refusedWith "  %q = getelementptr inrange(0, 4) i8, ptr %p, i64 %k" ["inrange"]
#guard refusedWith "  %q = getelementptr nuw i8, ptr %p, i64 %k" ["nuw"]
#guard refusedWith "  %q = getelementptr nusw i8, ptr %p, i64 %k" ["nusw"]
#guard refusedWith "  %q = getelementptr inbounds nuw i8, ptr %p, i64 %k" ["nuw"]

/-! ### The offset's semantics -/

/-- The address the step computes for `%q = gep %p, <w>-bit <off>` starting from
`%p = 100`, or `none` when the step refuses the offset. -/
def gepAddress? (w : Nat) (off : Int) : Option Nat :=
  match evalInstr noCalls
      { env := [("%p", .ptr 100)], mem := [], next := 0, pc := "entry" }
      (.gep "%q" (.reg "%p") (.imm (.int w (BitVec.ofInt w off)))) with
  | some s =>
      match lookupName s.env "%q" with
      | some (.ptr a) => some a
      | _ => none
  | none => none

-- The sign-extension at each width the parser accepts, with an offset whose top
-- bit is clear: `127`, `2^31 - 1` and `2^63 - 1` are each added to the base.
#guard gepAddress? 8 127 = some 227
#guard gepAddress? 32 2147483647 = some 2147483747
#guard gepAddress? 64 9223372036854775807 = some 9223372036854775907

-- The negative sign of each width is undefined behaviour: `i8 0x80`,
-- `i32 0x80000000` and `i64 -1` are refused, and so is `i64 2^63`.  The three
-- accepted offsets above are this check's control: the step refuses these and
-- not everything.
#guard gepAddress? 8 (-128) = none
#guard gepAddress? 32 (-2147483648) = none
#guard gepAddress? 64 (-1) = none
#guard gepAddress? 64 9223372036854775808 = none

-- The negative offset in the textual form the refusals use: the parser accepts
-- it as a literal, and the step refuses it.  Both halves are checked, so the
-- restriction is the semantics' and not the parser's by accident.
#guard
  match parseWith "  %q = getelementptr i8, ptr %p, i64 -1" with
  | .ok _ => gepAddress? 64 (-1) = none
  | .error _ => false

-- A base that is not a pointer, and an index that is not an integer, are
-- undefined rather than coerced.
#guard
  (evalInstr noCalls
    { env := [("%p", .int 64 1), ("%k", .int 64 1)], mem := [], next := 0, pc := "entry" }
    (.gep "%q" (.reg "%p") (.reg "%k"))).isSome = false

#guard
  (evalInstr noCalls
    { env := [("%p", .ptr 8), ("%k", .ptr 8)], mem := [], next := 0, pc := "entry" }
    (.gep "%q" (.reg "%p") (.reg "%k"))).isSome = false

/-! ### The instruction's projections -/

-- The offset is a pure value instruction that defines its destination and reads
-- both operands, so a pass that walks registers or a pure set sees it.
#guard Instr.dst? (.gep "%q" (.reg "%p") (.reg "%k")) = some "%q"
#guard Instr.uses (.gep "%q" (.reg "%p") (.imm (.int 64 4))) = ["%p"]
#guard Instr.isPure (.gep "%q" (.reg "%p") (.reg "%k")) = true

end GetElementPtr
