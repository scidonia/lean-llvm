/-
The vector lane scenario: literal vector operands, `extractelement`,
`insertelement`, and the rule an out-of-range index gets.

A literal vector operand writes its lanes one by one — `<i64 11, i64 22>` — and
the operand's `<n x iw>` type supplies the lane count and the element width, so
a list of another length or at another width is refused by name.  `extractelement`
reads one lane and `insertelement` writes one; each instruction carries the
vector's shape because that is what the read or write checks the value against,
and each reads its index as an unsigned count whose written width is checked and
dropped.

An index at or past the lane count is **poison** in LLVM and **`ub`** here.  The
model has no poison, and this is the same reading `Const.toValue` gives a
`poison` literal: the program is undefined at that read rather than given a lane
the compiler may choose.  The assertions below are written as a pair for exactly
that reason — the same program returns lane `k` at a valid index and `ub` at
`k ≥ n`, so an implementation that returned some lane for either would fail one
of them.
The values are chosen so that the lanes differ from each other and from zero: a
read that always answered lane 0, one that answered the last lane, or one that
answered `zeroinitializer`'s zero fails the pairs below.

`zeroinitializer` at a vector type is the all-zero vector — the splat of zero
exactly — so the two spellings parse to the same instruction and run to the same
answer; the same-AST half of that pair is in `LeanLLVMTest/Core.lean`.

The parser compares string tokens and does not reduce in the kernel, so every
check here is a `#guard` rather than a `decide`d proposition.

Elaborated by `nix develop -c lake env lean tests/vector-lanes.lean`.  A `#guard`
that does not hold stops elaboration with a nonzero exit status; nothing outside
the elaborated program is written.
-/
import LeanLLVM

namespace VectorLanes

open LeanLLVM

/-! ### Reading a single instruction line -/

/-- One function whose body is the given instruction lines, so a parse of one
instruction is observable without a whole program. -/
def moduleOf (body : String) : String :=
  "define i64 @f(ptr %p, i64 %k) {\nentry:\n" ++ body ++ "\n  ret i64 0\n}\n"

/-- Parse a module holding the given instruction lines. -/
def parseWith (body : String) : Except String Module :=
  parseModule (moduleOf body)

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The refusal of a body, when the parser refuses it and the message names each
of `tokens` and none of `absent`. -/
def refusedWithOut (body : String) (tokens absent : List String) : Bool :=
  match parseWith body with
  | .error e => tokens.all (mentions e) && absent.all (fun t => !mentions e t)
  | .ok _ => false

/-- The refusal of a body whose message names each of `tokens`. -/
def refusedWith (body : String) (tokens : List String) : Bool :=
  refusedWithOut body tokens []

/-- The instruction a one-line body parses to, when it parses. -/
def instrsOf (body : String) : Option (List Instr) :=
  match parseWith body with
  | .ok ⟨_, [f]⟩ => f.blocks.map (·.instrs) |>.head?
  | _ => none

/-- Whether a printed instruction parses back to itself, as the only instruction
of a one-line function body. -/
def rendersTo (i : Instr) : Bool :=
  match parseWith (Instr.render i) with
  | .ok ⟨_, [f]⟩ => (f.blocks.map (·.instrs)).head? = some [i]
  | _ => false

/-- Whether the printed form of a one-line body's instruction parses back to that
instruction. -/
def reparses (body : String) : Bool :=
  match instrsOf body with
  | some [i] => rendersTo i
  | _ => false

/-- The one function of a module source, when it parses. -/
def onlyFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok ⟨_, f :: _⟩ => some f
  | _ => none

/-- Run the one function of a module source with the given arguments. -/
def runSource (src : String) (args : List Value) : Option Outcome :=
  match onlyFunction src with
  | some f => run noCalls f args
  | none => none

/-- Whether the run returned the given integer value. -/
def returnsInt (o : Option Outcome) (w v : Nat) : Bool :=
  match o with
  | some (.ret (some (.int w' x)) _) => w' = w && x = BitVec.ofNat w' v
  | _ => false

/-- Whether the run reached undefined behaviour. -/
def isUb (o : Option Outcome) : Bool :=
  match o with
  | some .ub => true
  | _ => false

/-! ### Literal vector operands -/

-- A literal vector operand parses to the lanes it writes, in order, at the
-- operand type's element width.  The literal is on the right of an `icmp` and the
-- read is at `<4 x i32>`, so a list read at the wrong width or reordered fails
-- here.
#guard
  match instrsOf "  %q = icmp eq <4 x i32> %p, <i32 1, i32 2, i32 3, i32 4>" with
  | some [i] =>
      i = .icmpVec "%q" .eq 4 32 (.reg "%p") (.imm (.vector 32 [1, 2, 3, 4]))
  | _ => false

-- The same list on the left, and negative lanes, so the constructor is not read
-- through one operand position only.
#guard
  match instrsOf "  %q = icmp eq <4 x i32> <i32 -1, i32 0, i32 0, i32 0>, %p" with
  | some [i] =>
      i = .icmpVec "%q" .eq 4 32
            (.imm (.vector 32 [BitVec.ofInt 32 (-1), 0, 0, 0])) (.reg "%p")
  | _ => false

-- A literal vector argument of a call is read at the type its position writes.
#guard
  match instrsOf "  %q = call <2 x i64> @pclmul(<2 x i64> %p, <2 x i64> <i64 -1, i64 0>, i8 0)" with
  | some [i] =>
      i = .call "%q" (.vec 2 (.int 64)) "pclmul"
            [ (.vec 2 (.int 64), .reg "%p"),
              (.vec 2 (.int 64), .imm (.vector 64 [BitVec.ofInt 64 (-1), 0])),
              (.int 8, .imm (.int 8 0)) ]
  | _ => false

-- A lane list whose length disagrees with the operand type is refused by name,
-- and the message carries both counts.
#guard refusedWithOut "  %q = icmp eq <4 x i32> %p, <i32 1, i32 2>"
  ["vector literal", "2 lane(s)", "<4 x i32>", "has 4"] ["integer literal"]

-- A lane written at another width names both widths.
#guard refusedWithOut "  %q = icmp eq <4 x i32> %p, <i32 1, i64 2>"
  ["vector literal lane", "i64", "element width is i32"] ["lane(s)"]

-- A lane that is not an integer literal is refused rather than given a lane
-- value: the model has no `undef` lane.
#guard refusedWith "  %q = icmp eq <4 x i32> %p, <i32 1, i32 undef>"
  ["vector literal lane", "integer literal", "undef"]

-- A lane list at a scalar operand type is refused by name, before the lane
-- reader runs, so the message names the position rather than a lane.
#guard refusedWithOut "  %q = icmp eq i32 %p, <i32 1>"
  ["vector literal operand", "integer-lane vector operand type", "i32"]
  ["lane(s)"]

-- The detector the refusals are read with: it finds a token the message carries
-- and does not find one it does not.  Without this a `mentions` that matched
-- nothing would make every refusal above vacuous.
#guard
  match parseWith "  %q = icmp eq <4 x i32> %p, <i32 1, i32 2>" with
  | .error e => mentions e "vector literal" ∧ !mentions e "not modelled"
  | .ok _ => false

-- The detector's other side: an accepted body is not reported as a refusal.
#guard refusedWith "  %q = icmp eq <4 x i32> %p, <i32 1, i32 2, i32 3, i32 4>" ["x"] = false

/-! ### The lane instructions parse and print -/

#guard
  match instrsOf "  %q = extractelement <2 x i64> %p, i32 1" with
  | some [i] => i = .extractelement "%q" 2 64 (.reg "%p") (.imm (.int 32 1))
  | _ => false

#guard
  match instrsOf "  %q = insertelement <2 x i64> %p, i64 %k, i32 0" with
  | some [i] => i = .insertelement "%q" 2 64 (.reg "%p") (.reg "%k") (.imm (.int 32 0))
  | _ => false

-- The index's own width is not a field of the instruction: `i64 1` and `i32 1`
-- parse to instructions whose vector shape and index lane are the same, and the
-- index literal keeps only the width it was written at, as every literal does.
#guard
  match instrsOf "  %q = extractelement <2 x i64> %p, i64 1" with
  | some [i] => i = .extractelement "%q" 2 64 (.reg "%p") (.imm (.int 64 1))
  | _ => false
#guard
  match instrsOf "  %q = extractelement <2 x i64> %p, i32 1" with
  | some [i] => i = .extractelement "%q" 2 64 (.reg "%p") (.imm (.int 32 1))
  | _ => false

-- The printed form re-parses to the same instruction, including the register
-- index whose width the instruction does not carry.
#guard reparses "  %q = extractelement <2 x i64> %p, i32 1"
#guard reparses "  %q = insertelement <2 x i64> %p, i64 %k, i32 0"
#guard reparses "  %q = extractelement <2 x i64> %p, i32 %k"

-- A register index's written width is not part of the instruction, so the
-- printer writes the canonical `i32` and that form re-parses to the same
-- instruction.  The literal form keeps its width in the literal, and prints it.
#guard
  match instrsOf "  %q = extractelement <2 x i64> %p, i64 %k" with
  | some [i] => rendersTo i ∧ mentions (Instr.render i) ", i32 %k"
  | _ => false
#guard reparses "  %q = insertelement <2 x i64> <i64 1, i64 2>, i64 -3, i32 1"

-- A lane access on a non-vector operand type is refused by name, and the message
-- names the type it saw.
#guard refusedWithOut "  %q = extractelement i64 %p, i32 0"
  ["extractelement", "integer-lane vector operand type", "i64"] ["lane(s)"]
#guard refusedWith "  %q = insertelement i64 %p, i64 %k, i32 0"
  ["insertelement", "integer-lane vector operand type"]

-- The element operand of an `insertelement` is written with the vector's element
-- type; another width names both.
#guard refusedWithOut "  %q = insertelement <2 x i64> %p, i32 %k, i32 0"
  ["element operand is written i32", "element type is i64"] ["lane(s)"]

-- An index that is not an integer type is refused by name.
#guard refusedWith "  %q = extractelement <2 x i64> %p, ptr %k"
  ["extractelement index type 'ptr'", "integer type"]
#guard refusedWith "  %q = insertelement <2 x i64> %p, i64 %k, ptr %p"
  ["insertelement index type 'ptr'", "integer type"]

-- A `phi` may carry a literal-vector incoming value: its commas are inside the
-- literal, so the entry is split at the comma that separates the value from the
-- label.  The printed form of the same phi re-parses to the same instruction, and
-- the selected value is the lane the read asks for.
def phiVectorSrc : String :=
"define i64 @pv(i64 %x) {
entry:
  br label %b
b:
  %v = phi <2 x i64> [ <i64 1, i64 2>, %entry ]
  %e = extractelement <2 x i64> %v, i32 1
  ret i64 %e
}
"

#guard
  match onlyFunction phiVectorSrc with
  | some f =>
      match f.blocks with
      | [_, b] => b.instrs =
          [ .phi "%v" (.vec 2 (.int 64)) [("entry", .imm (.vector 64 [1, 2]))],
            .extractelement "%e" 2 64 (.reg "%v") (.imm (.int 32 1)) ]
      | _ => false
  | none => false

#guard
  match parseModule phiVectorSrc with
  | .ok m => parseModule (Module.render m) = .ok m
  | .error _ => false

-- Through the whole pipeline: selection takes the one incoming entry (the entry
-- block's only predecessor is `entry`), and the read takes lane 1 of it.
#guard returnsInt (runSource phiVectorSrc [.int 64 0]) 64 2

/-! ### The lane a read returns, and the lane a write replaces -/

/-- A body that reads the lane its index names out of the literal vector
`<i64 11, i64 22>`.  The two lanes differ from each other and from zero, so a read
that answered another lane or zero is not the same answer. -/
def readProgram (idx : String) : String :=
"define i64 @lane_read() {
entry:
  %x = extractelement <2 x i64> <i64 11, i64 22>, " ++ idx ++ "
  ret i64 %x
}
"

-- In range: lane 0 and lane 1 each return their own value.  These two are the
-- control for the refusals below: the instruction does read a lane.
#guard returnsInt (runSource (readProgram "i32 0") []) 64 11
#guard returnsInt (runSource (readProgram "i32 1") []) 64 22

-- Out of range: an index at or past the lane count is undefined behaviour, not a
-- lane and not zero.  `isUb` distinguishes it from the two values above.
#guard isUb (runSource (readProgram "i32 2") [])
#guard isUb (runSource (readProgram "i32 18446744073709551615") [])

-- The out-of-range rule is the index's, not the width it was written at: an
-- `i64` index past the lane count is `ub` too, and an `i64` index inside it reads
-- the lane.
#guard isUb (runSource (readProgram "i64 2") [])
#guard returnsInt (runSource (readProgram "i64 1") []) 64 22

/-- A body that writes `%x` into lane 0 of `<i64 11, i64 22>` and returns the two
lanes packed as `lane0 | lane1 << 8`.  The write is visible in lane 0 and the
other lane is untouched, so an implementation that wrote no lane, the last lane,
or every lane gives a different number. -/
def writeProgram (idx : String) : String :=
"define i64 @lane_write(i64 %x) {
entry:
  %v = insertelement <2 x i64> <i64 11, i64 22>, i64 %x, " ++ idx ++ "
  %a = extractelement <2 x i64> %v, i32 0
  %b = extractelement <2 x i64> %v, i32 1
  %s = shl i64 %b, 8
  %t = or i64 %a, %s
  ret i64 %t
}
"

-- Lane 0 becomes 7 and lane 1 is still 22: 7 + 22 * 256 = 5639.  Writing lane 1
-- instead would give 22 + 7 * 256 = 1814, writing nothing 11 + 22 * 256 = 5643,
-- and writing both lanes 7 + 7 * 256 = 1799 — each a different answer.
#guard returnsInt (runSource (writeProgram "i32 0") [.int 64 7]) 64 (7 + 22 * 256)

-- Out of range, the write is undefined behaviour, exactly as the read is.
#guard isUb (runSource (writeProgram "i32 2") [.int 64 7])

-- A `zeroinitializer` vector operand is the all-zero vector: reading lane 0 of
-- it returns 0, and writing it does not make the write disappear — the two are
-- separate assertions because a value that were not a vector would fail both.
def zeroProgram : String :=
"define i64 @zero_lane() {
entry:
  %z = extractelement <2 x i64> zeroinitializer, i32 0
  %w = insertelement <2 x i64> zeroinitializer, i64 5, i32 1
  %e = extractelement <2 x i64> %w, i32 1
  %s = shl i64 %e, 8
  %t = or i64 %z, %s
  ret i64 %t
}
"

-- Lane 0 of the zero vector is 0, and the written lane 1 is 5: 0 + 5 * 256.
#guard returnsInt (runSource zeroProgram []) 64 (5 * 256)

-- The same program with `splat (i64 0)` in place of the first `zeroinitializer`
-- runs to the same answer, so the spelling is the only difference.
#guard runSource (zeroProgram.replace "zeroinitializer" "splat (i64 0)") []
  = runSource zeroProgram []

/-! ### The chain the stage-1 kernel writes

The kernel `@ci2` reads a literal vector operand, inserts a lane into a zero
vector, extracts a lane, and offsets a pointer by it.  These two bodies are that
chain without the surrounding classification, so a change that breaks any link
stops here rather than at the kernel's text.
-/

/-- Literal vector operand, lane write, lane read, typed offset — the shape of
`@ci2`'s `%qac2`/`%pxc2`/`%cp` lines. -/
def chainSource : String :=
"define i64 @chain(ptr %cmask) {
entry:
  %c = icmp eq <2 x i64> <i64 7, i64 9>, <i64 7, i64 9>
  %k = insertelement <2 x i64> zeroinitializer, i64 5, i32 1
  %e = extractelement <2 x i64> %k, i32 1
  %g = getelementptr inbounds i64, ptr %cmask, i64 %e
  %v = load i64, ptr %g
  ret i64 %v
}
"

-- The body parses, and every instruction of the chain is the one the text
-- writes: the literal vector's lanes, the zero vector, the written lane, the read
-- lane and the scaled offset.
#guard
  match onlyFunction chainSource with
  | some f =>
      match f.blocks with
      | [b] =>
          b.instrs =
            [ .icmpVec "%c" .eq 2 64 (.imm (.vector 64 [7, 9])) (.imm (.vector 64 [7, 9])),
              .insertelement "%k" 2 64 (.imm (.splat 2 64 0)) (.imm (.int 64 5)) (.imm (.int 32 1)),
              .extractelement "%e" 2 64 (.reg "%k") (.imm (.int 32 1)),
              .gep "%g" (.int 64) (.reg "%cmask") (.reg "%e"),
              .load "%v" (.int 64) (.reg "%g") ]
      | _ => false
  | none => false

/-- The same chain, run: the inserted lane 1 is 5, so the offset names the fifth
`i64` past the base. -/
def chainRunSource : String :=
"define i64 @chain_run() {
entry:
  %k = insertelement <2 x i64> zeroinitializer, i64 5, i32 1
  %e = extractelement <2 x i64> %k, i32 1
  ret i64 %e
}
"

#guard returnsInt (runSource chainRunSource []) 64 5

end VectorLanes
