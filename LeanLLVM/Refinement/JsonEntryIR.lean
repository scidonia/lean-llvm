/-
An emitted-IR bridge for the entry positions unit.

`probes/install/ir/json-entry.candidate.ll` is the emission of
`kernel/json/entry.c` at the measured compiler line, reduced to the two
functions the unit's wrappers call: `@s1f_k_pos8`, which turns a block's mask
word into positions through the byte table, and `@s1f_k_b8`, which does it with
eight fixed count-trailing-zeros slots and a scalar tail.  Both are `noinline`
in the source, so the fixture holds one function per kernel rather than an
inlined copy of each.

`probes/install/ir/capture-entry.sh` records the invocation and derives, by
diffing its own clang emission against what it emits, every item the
normalisation took out (`json-entry.strip.tsv`, by class), every place it
rewrote text (`json-entry.rewrites.tsv`, with the reason), the table read
(`json-entry.table.tsv`), and the fixture's own construct inventory
(`json-entry.inventory`, opcodes and call targets).

This module parses the file and pins the parsed ASTs against the literals below.
The pin is a `#guard` rather than a `rfl` proposition because the parser runs on
`String` primitives, which the kernel does not reduce, so a proposition about a
`parseModule` result cannot be closed by reflexivity.  What the pin buys is that
the hand-written ASTs and the committed text are the same object: a change to
either that the other does not carry fails elaboration, and no theorem below can
be stated about a body the text does not contain.  It is checked when this module
is elaborated, and that is the moment `include_str` reads the fixture: the text
is fixed in the module from then on, and a change to the fixture alone does not
make lake rebuild it, so such a change reaches the pin only when this module is
elaborated again.

The registers the emission names are its own (`%k.addr.011`, `%idxprom.1.i`,
`%vecinit7.i.3.i`): the capture compiles with `-fno-discard-value-names`, which
names values and labels the entry block and changes no instruction, and checks
that claim by emitting the source with and without the flag.  The five
parameters are the ABI's own (`%ent`, `%blk0`, `%nblk`, `%out`, `%k`), so the
capture renames none of them.

## The table read, and why the fixture is not the emission text

The fragment has no module-level globals, so `kernel/json/entry.c`'s table and
the eight GEPs that name it cannot be represented.  Each

    getelementptr inbounds nuw [256 x [8 x i32]], ptr @xl_pos8, i64 0, i64 %idx

is rewritten to

    getelementptr inbounds <8 x i32>, ptr %tab, i64 %idx

and `%tab` is appended to the parameter list.  Three operand differences and one
equation: the base becomes the caller's; the element type becomes the packed
`<8 x i32>`, which is 32 bytes, the stride the emitted aggregate computes; the
two indices become one, the aggregate row that the base absorbs.  The emitted
form addresses `@xl_pos8 + 0 * (256 * 32) + idx * 32` and the rewritten form
`%tab + idx * 32`, so the byte offset from the base is `32 * idx` on both sides
for every index, and only the base differs — which is exactly what the
theorem's table hypothesis supplies.  The emitted GEP carries `nuw` and the
rewritten one does not: `nuw` is class 4's removal and is gone before the
rewrite, so it is in the strip inventory and not in the table inventory.

So this module's `define` is not a function `entry.c` declares: its parameter
list has one more parameter, and the eight reads differ from the emission by a
base, an element type and an index arity.  The capture computes that difference
and refuses any other — a differing line that is neither one of those GEPs nor
the parameter list stops it with exit `3` — and `json-entry.table.tsv` is the
per-site record.

## What is here, and what the statement adds

The fixture, the two ASTs and the pin.  The call environment the two bodies'
count calls resolve through, the address-free table the theorem reads at `%tab`,
the output stream the cursor names, and the theorems themselves belong to the
statement that will be made over these bodies, not to the bodies: a definition with no
consumer exercises nothing.  The specification vocabulary the statement is
written in is `JsonScanSpec`'s — the masks, `pos8Row`, `positionsOf`, `limMask`
— which is why this module imports it.
-/
import LeanLLVM.Memory
import LeanLLVM.Parser
import LeanLLVM.Refinement.JsonEntSpec
import LeanLLVM.Refinement.CallsFootprint

namespace LeanLLVM.Refinement.JsonEntryIR

open LeanLLVM

/-! ### The fixture -/

/-- The entry unit as emitted and committed. -/
def jsonEntrySrc : String :=
  include_str "../../probes/install/ir/json-entry.candidate.ll"

/-- Parse a fixture and take its first function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-! ### The pinned ASTs

The two bodies, block by block, in the order the fixture holds them.  The
helpers below only spell an operand the way `parseConst`/`parseOperand` read
one; they decide nothing. -/

/-- A register operand. -/
def reg (n : String) : Operand := .reg n

/-- An integer literal of width `w`. -/
def lit (w : Nat) (v : Int) : Operand := .imm (.int w (BitVec.ofInt w v))

/-- `<8 x i32>`: a table row, which is also the type of the vector the emitter
adds the block base to and stores. -/
abbrev v8i32 : Ty := .vec 8 (.int 32)

/-- `<8 x i32> zeroinitializer`: the vector `insertelement` writes its one lane
into, and the second `shufflevector` operand, whose lanes no mask entry selects.
The emission spells both `poison`; the capture substitutes a defined value,
which is class 6 of its normalisation, because nothing reads the lane. -/
def zero8 : Operand := .imm (.splat 8 32 0)

/-- The `shufflevector` mask: eight entries, every one selecting lane 0 of the
first operand, so the result is that lane broadcast across the vector.  The
emission writes it as `<8 x i32> zeroinitializer`; the capture writes the lane
list the parser reads, because a mask is a static permutation and a splat
constant is not one. -/
def splatLane0 : List Nat := [0, 0, 0, 0, 0, 0, 0, 0]

/-! #### `@s1f_k_pos8` — the block loop, and one group store per mask byte -/

def pos8Entry : Block :=
  { name := "entry",
    instrs := [
      .icmp "%cmp9.not" .eq 64 (reg "%nblk") (lit 64 0)],
    term := .condbr (reg "%cmp9.not") "for.cond.cleanup" "for.body" }

def pos8LoopExit : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%k.addr.0.lcssa" (.int 64) [("entry", (reg "%k")), ("cleanup", (reg "%k.addr.1"))]],
    term := .ret (.int 64) (some (reg "%k.addr.0.lcssa")) }

def pos8Body : Block :=
  { name := "for.body",
    instrs := [
      .phi "%k.addr.011" (.int 64) [("cleanup", (reg "%k.addr.1")), ("entry", (reg "%k"))],
      .phi "%i.010" (.int 64) [("cleanup", (reg "%inc")), ("entry", (lit 64 0))],
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.010"),
      .load "%0" (.int 64) (reg "%arrayidx"),
      .icmp "%tobool.not" .eq 64 (reg "%0") (lit 64 0)],
    term := .condbr (reg "%tobool.not") "cleanup" "if.end" }

/-! The `if.end` block is written as its units — a head, the seven group
sequences that follow the first, and a tail — so `pos8Groups.instrs` is their
concatenation by definition.  Simulation then takes one unit at a time, and no
goal ever holds more than one unit's instructions. -/

/-- The block's first sixteen instructions: the block base `%conv`, the output
pointer `%add.ptr`, and the whole of the first eight-lane group. -/
def pos8Head : List Instr := [
      .binop "%add" .add 64 (reg "%i.010") (reg "%blk0"),
      .trunc "%add.tr" 64 32 (reg "%add"),
      .binop "%conv" .shl 32 (reg "%add.tr") (lit 32 6),
      .gep "%add.ptr" (.int 32) (reg "%out") (reg "%k.addr.011"),
      -- The block's eight mask bytes.  Each byte selects its table row, the row is
      -- broadcast across eight lanes and offset by the byte's position in the block,
      -- and the result is stored at the running cursor, which then advances by the
      -- byte's population count.  The stores are unconditional: a byte with no set
      -- lane still stores eight lanes, which is why the last written lane of a block
      -- is `k' + 7`.
      .trunc "%1" 64 32 (reg "%0"),
      .binop "%conv.i" .and 32 (reg "%1") (lit 32 255),
      .binop "%idxprom.i" .and 64 (reg "%0") (lit 64 255),
      .gep "%arrayidx.i" v8i32 (reg "%tab") (reg "%idxprom.i"),
      .load "%2" v8i32 (reg "%arrayidx.i"),
      .insertelement "%vecinit.i.i" 8 32 zero8 (reg "%conv") (lit 64 0),
      .shuffleVec "%vecinit7.i.i" 8 32 (reg "%vecinit.i.i") zero8 splatLane0,
      .binopVec "%add.i.i" .add 8 32 (reg "%2") (reg "%vecinit7.i.i"),
      .store v8i32 (reg "%add.i.i") (reg "%add.ptr"),
      .call "%3" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.i"))],
      .zext "%conv4.i" 32 64 (reg "%3"),
      .gep "%add.ptr.i" (.int 32) (reg "%add.ptr") (reg "%conv4.i")
  ]

/-- Group `j`'s sequence: shift the mask word down to byte `j`, select that
byte's table row, broadcast the row offset by the group's place in the block,
store it at the running cursor, and advance the cursor by the byte's
population count.  Group 1 begins the sequence. -/
def pos8Group1 : List Instr := [
      .binop "%shr.1.i" .lshr 64 (reg "%0") (lit 64 8),
      .trunc "%4" 64 32 (reg "%shr.1.i"),
      .binop "%conv.1.i" .and 32 (reg "%4") (lit 32 255),
      .binop "%idxprom.1.i" .and 64 (reg "%shr.1.i") (lit 64 255),
      .gep "%arrayidx.1.i" v8i32 (reg "%tab") (reg "%idxprom.1.i"),
      .load "%5" v8i32 (reg "%arrayidx.1.i"),
      .binop "%add.1.i" .or 32 (reg "%conv") (lit 32 8),
      .insertelement "%vecinit.i.1.i" 8 32 zero8 (reg "%add.1.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.1.i" 8 32 (reg "%vecinit.i.1.i") zero8 splatLane0,
      .binopVec "%add.i.1.i" .add 8 32 (reg "%5") (reg "%vecinit7.i.1.i"),
      .store v8i32 (reg "%add.i.1.i") (reg "%add.ptr.i"),
      .call "%6" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.1.i"))],
      .zext "%conv4.1.i" 32 64 (reg "%6"),
      .gep "%add.ptr.1.i" (.int 32) (reg "%add.ptr.i") (reg "%conv4.1.i")
  ]

def pos8Group2 : List Instr := [
      .binop "%shr.2.i" .lshr 64 (reg "%0") (lit 64 16),
      .trunc "%7" 64 32 (reg "%shr.2.i"),
      .binop "%conv.2.i" .and 32 (reg "%7") (lit 32 255),
      .binop "%idxprom.2.i" .and 64 (reg "%shr.2.i") (lit 64 255),
      .gep "%arrayidx.2.i" v8i32 (reg "%tab") (reg "%idxprom.2.i"),
      .load "%8" v8i32 (reg "%arrayidx.2.i"),
      .binop "%add.2.i" .or 32 (reg "%conv") (lit 32 16),
      .insertelement "%vecinit.i.2.i" 8 32 zero8 (reg "%add.2.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.2.i" 8 32 (reg "%vecinit.i.2.i") zero8 splatLane0,
      .binopVec "%add.i.2.i" .add 8 32 (reg "%8") (reg "%vecinit7.i.2.i"),
      .store v8i32 (reg "%add.i.2.i") (reg "%add.ptr.1.i"),
      .call "%9" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.2.i"))],
      .zext "%conv4.2.i" 32 64 (reg "%9"),
      .gep "%add.ptr.2.i" (.int 32) (reg "%add.ptr.1.i") (reg "%conv4.2.i")
  ]

def pos8Group3 : List Instr := [
      .binop "%shr.3.i" .lshr 64 (reg "%0") (lit 64 24),
      .trunc "%10" 64 32 (reg "%shr.3.i"),
      .binop "%conv.3.i" .and 32 (reg "%10") (lit 32 255),
      .binop "%idxprom.3.i" .and 64 (reg "%shr.3.i") (lit 64 255),
      .gep "%arrayidx.3.i" v8i32 (reg "%tab") (reg "%idxprom.3.i"),
      .load "%11" v8i32 (reg "%arrayidx.3.i"),
      .binop "%add.3.i" .or 32 (reg "%conv") (lit 32 24),
      .insertelement "%vecinit.i.3.i" 8 32 zero8 (reg "%add.3.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.3.i" 8 32 (reg "%vecinit.i.3.i") zero8 splatLane0,
      .binopVec "%add.i.3.i" .add 8 32 (reg "%11") (reg "%vecinit7.i.3.i"),
      .store v8i32 (reg "%add.i.3.i") (reg "%add.ptr.2.i"),
      .call "%12" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.3.i"))],
      .zext "%conv4.3.i" 32 64 (reg "%12"),
      .gep "%add.ptr.3.i" (.int 32) (reg "%add.ptr.2.i") (reg "%conv4.3.i")
  ]

def pos8Group4 : List Instr := [
      .binop "%shr.4.i" .lshr 64 (reg "%0") (lit 64 32),
      .trunc "%13" 64 32 (reg "%shr.4.i"),
      .binop "%conv.4.i" .and 32 (reg "%13") (lit 32 255),
      .binop "%idxprom.4.i" .and 64 (reg "%shr.4.i") (lit 64 255),
      .gep "%arrayidx.4.i" v8i32 (reg "%tab") (reg "%idxprom.4.i"),
      .load "%14" v8i32 (reg "%arrayidx.4.i"),
      .binop "%add.4.i" .or 32 (reg "%conv") (lit 32 32),
      .insertelement "%vecinit.i.4.i" 8 32 zero8 (reg "%add.4.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.4.i" 8 32 (reg "%vecinit.i.4.i") zero8 splatLane0,
      .binopVec "%add.i.4.i" .add 8 32 (reg "%14") (reg "%vecinit7.i.4.i"),
      .store v8i32 (reg "%add.i.4.i") (reg "%add.ptr.3.i"),
      .call "%15" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.4.i"))],
      .zext "%conv4.4.i" 32 64 (reg "%15"),
      .gep "%add.ptr.4.i" (.int 32) (reg "%add.ptr.3.i") (reg "%conv4.4.i")
  ]

def pos8Group5 : List Instr := [
      .binop "%shr.5.i" .lshr 64 (reg "%0") (lit 64 40),
      .trunc "%16" 64 32 (reg "%shr.5.i"),
      .binop "%conv.5.i" .and 32 (reg "%16") (lit 32 255),
      .binop "%idxprom.5.i" .and 64 (reg "%shr.5.i") (lit 64 255),
      .gep "%arrayidx.5.i" v8i32 (reg "%tab") (reg "%idxprom.5.i"),
      .load "%17" v8i32 (reg "%arrayidx.5.i"),
      .binop "%add.5.i" .or 32 (reg "%conv") (lit 32 40),
      .insertelement "%vecinit.i.5.i" 8 32 zero8 (reg "%add.5.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.5.i" 8 32 (reg "%vecinit.i.5.i") zero8 splatLane0,
      .binopVec "%add.i.5.i" .add 8 32 (reg "%17") (reg "%vecinit7.i.5.i"),
      .store v8i32 (reg "%add.i.5.i") (reg "%add.ptr.4.i"),
      .call "%18" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.5.i"))],
      .zext "%conv4.5.i" 32 64 (reg "%18"),
      .gep "%add.ptr.5.i" (.int 32) (reg "%add.ptr.4.i") (reg "%conv4.5.i")
  ]

def pos8Group6 : List Instr := [
      .binop "%shr.6.i" .lshr 64 (reg "%0") (lit 64 48),
      .trunc "%19" 64 32 (reg "%shr.6.i"),
      .binop "%conv.6.i" .and 32 (reg "%19") (lit 32 255),
      .binop "%idxprom.6.i" .and 64 (reg "%shr.6.i") (lit 64 255),
      .gep "%arrayidx.6.i" v8i32 (reg "%tab") (reg "%idxprom.6.i"),
      .load "%20" v8i32 (reg "%arrayidx.6.i"),
      .binop "%add.6.i" .or 32 (reg "%conv") (lit 32 48),
      .insertelement "%vecinit.i.6.i" 8 32 zero8 (reg "%add.6.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.6.i" 8 32 (reg "%vecinit.i.6.i") zero8 splatLane0,
      .binopVec "%add.i.6.i" .add 8 32 (reg "%20") (reg "%vecinit7.i.6.i"),
      .store v8i32 (reg "%add.i.6.i") (reg "%add.ptr.5.i"),
      .call "%21" (.int 32) "llvm.ctpop.i32" [((.int 32), (reg "%conv.6.i"))],
      .zext "%conv4.6.i" 32 64 (reg "%21"),
      .gep "%add.ptr.6.i" (.int 32) (reg "%add.ptr.5.i") (reg "%conv4.6.i")
  ]

/-- The top group's sequence.  The emission keeps the top byte's index at full
width, so there is no `trunc` and no `idxprom` step, and the group is the last
store: the cursor does not advance past it. -/
def pos8Group7 : List Instr := [
      .binop "%shr.7.i" .lshr 64 (reg "%0") (lit 64 56),
      .gep "%arrayidx.7.i" v8i32 (reg "%tab") (reg "%shr.7.i"),
      .load "%22" v8i32 (reg "%arrayidx.7.i"),
      .binop "%add.7.i" .or 32 (reg "%conv") (lit 32 56),
      .insertelement "%vecinit.i.7.i" 8 32 zero8 (reg "%add.7.i") (lit 64 0),
      .shuffleVec "%vecinit7.i.7.i" 8 32 (reg "%vecinit.i.7.i") zero8 splatLane0,
      .binopVec "%add.i.7.i" .add 8 32 (reg "%22") (reg "%vecinit7.i.7.i"),
      .store v8i32 (reg "%add.i.7.i") (reg "%add.ptr.6.i")
  ]

/-- The block's last two instructions: the mask word's population count and the
cursor advanced by it. -/
def pos8Tail : List Instr := [
      .call "%23" (.int 64) "llvm.ctpop.i64" [((.int 64), (reg "%0"))],
      .binop "%add1" .add 64 (reg "%23") (reg "%k.addr.011")
  ]

/-- The block's instructions as its units, in order. -/
def pos8GroupsInstrs : List Instr :=
  pos8Head ++ pos8Group1 ++ pos8Group2 ++ pos8Group3 ++ pos8Group4 ++
    pos8Group5 ++ pos8Group6 ++ pos8Group7 ++ pos8Tail

def pos8Groups : Block :=
  { name := "if.end",
    instrs := pos8GroupsInstrs,
    term := .br "cleanup" }

def pos8Advance : Block :=
  { name := "cleanup",
    instrs := [
      .phi "%k.addr.1" (.int 64) [("if.end", (reg "%add1")), ("for.body", (reg "%k.addr.011"))],
      .binop "%inc" .add 64 (reg "%i.010") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%nblk")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-- The POS8 kernel: the block loop, and one eight-lane group store per mask
byte through the byte table. -/
def entryPos8Function : Function :=
  { name := "s1f_k_pos8",
    retTy := .int 64,
    params := [("%ent", .ptr), ("%blk0", .int 64), ("%nblk", .int 64), ("%out", .ptr), ("%k", .int 64), ("%tab", .ptr)],
    blocks :=
      [pos8Entry,
       pos8LoopExit,
       pos8Body,
       pos8Groups,
       pos8Advance] }

/-! #### `@s1f_k_b8` — the block loop, eight fixed slots, then a scalar tail -/

def b8Entry : Block :=
  { name := "entry",
    instrs := [
      .icmp "%cmp9.not" .eq 64 (reg "%nblk") (lit 64 0)],
    term := .condbr (reg "%cmp9.not") "for.cond.cleanup" "for.body" }

def b8LoopExit : Block :=
  { name := "for.cond.cleanup",
    instrs := [
      .phi "%k.addr.0.lcssa" (.int 64) [("entry", (reg "%k")), ("cleanup", (reg "%k.addr.1"))]],
    term := .ret (.int 64) (some (reg "%k.addr.0.lcssa")) }

def b8Body : Block :=
  { name := "for.body",
    instrs := [
      .phi "%k.addr.011" (.int 64) [("cleanup", (reg "%k.addr.1")), ("entry", (reg "%k"))],
      .phi "%i.010" (.int 64) [("cleanup", (reg "%inc")), ("entry", (lit 64 0))],
      .gep "%arrayidx" (.int 64) (reg "%ent") (reg "%i.010"),
      .load "%0" (.int 64) (reg "%arrayidx"),
      .icmp "%tobool.not" .eq 64 (reg "%0") (lit 64 0)],
    term := .condbr (reg "%tobool.not") "cleanup" "if.end" }

def b8Kernel : Block :=
  { name := "if.end",
    instrs := [
      .binop "%add" .add 64 (reg "%i.010") (reg "%blk0"),
      .trunc "%add.tr" 64 32 (reg "%add"),
      .binop "%conv" .shl 32 (reg "%add.tr") (lit 32 6),
      .gep "%add.ptr" (.int 32) (reg "%out") (reg "%k.addr.011"),
      .call "%1" (.int 64) "llvm.ctpop.i64" [((.int 64), (reg "%0"))],
      .call "%2" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%0")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast1.i" 64 32 (reg "%2"),
      -- Eight fixed slots: after the first, each clears the lane it just wrote before
      -- reading the next, so a mask with fewer than eight set lanes leaves the tail
      -- of the eight slots reading a cleared word.
      .binop "%add.i" .or 32 (reg "%conv") (reg "%cast1.i"),
      .store (.int 32) (reg "%add.i") (reg "%add.ptr"),
      .binop "%sub.i" .add 64 (reg "%0") (lit 64 (-1)),
      .binop "%and.i" .and 64 (reg "%sub.i") (reg "%0"),
      .call "%3" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast2.i" 64 32 (reg "%3"),
      .binop "%add3.i" .or 32 (reg "%conv") (reg "%cast2.i"),
      .gep "%arrayidx4.i" (.int 8) (reg "%add.ptr") (lit 64 4),
      .store (.int 32) (reg "%add3.i") (reg "%arrayidx4.i"),
      .binop "%sub5.i" .add 64 (reg "%and.i") (lit 64 (-1)),
      .binop "%and6.i" .and 64 (reg "%sub5.i") (reg "%and.i"),
      .call "%4" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and6.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast7.i" 64 32 (reg "%4"),
      .binop "%add8.i" .or 32 (reg "%conv") (reg "%cast7.i"),
      .gep "%arrayidx9.i" (.int 8) (reg "%add.ptr") (lit 64 8),
      .store (.int 32) (reg "%add8.i") (reg "%arrayidx9.i"),
      .binop "%sub10.i" .add 64 (reg "%and6.i") (lit 64 (-1)),
      .binop "%and11.i" .and 64 (reg "%sub10.i") (reg "%and6.i"),
      .call "%5" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and11.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast12.i" 64 32 (reg "%5"),
      .binop "%add13.i" .or 32 (reg "%conv") (reg "%cast12.i"),
      .gep "%arrayidx14.i" (.int 8) (reg "%add.ptr") (lit 64 12),
      .store (.int 32) (reg "%add13.i") (reg "%arrayidx14.i"),
      .binop "%sub15.i" .add 64 (reg "%and11.i") (lit 64 (-1)),
      .binop "%and16.i" .and 64 (reg "%sub15.i") (reg "%and11.i"),
      .call "%6" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and16.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast17.i" 64 32 (reg "%6"),
      .binop "%add18.i" .or 32 (reg "%conv") (reg "%cast17.i"),
      .gep "%arrayidx19.i" (.int 8) (reg "%add.ptr") (lit 64 16),
      .store (.int 32) (reg "%add18.i") (reg "%arrayidx19.i"),
      .binop "%sub20.i" .add 64 (reg "%and16.i") (lit 64 (-1)),
      .binop "%and21.i" .and 64 (reg "%sub20.i") (reg "%and16.i"),
      .call "%7" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and21.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast22.i" 64 32 (reg "%7"),
      .binop "%add23.i" .or 32 (reg "%conv") (reg "%cast22.i"),
      .gep "%arrayidx24.i" (.int 8) (reg "%add.ptr") (lit 64 20),
      .store (.int 32) (reg "%add23.i") (reg "%arrayidx24.i"),
      .binop "%sub25.i" .add 64 (reg "%and21.i") (lit 64 (-1)),
      .binop "%and26.i" .and 64 (reg "%sub25.i") (reg "%and21.i"),
      .call "%8" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and26.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast27.i" 64 32 (reg "%8"),
      .binop "%add28.i" .or 32 (reg "%conv") (reg "%cast27.i"),
      .gep "%arrayidx29.i" (.int 8) (reg "%add.ptr") (lit 64 24),
      .store (.int 32) (reg "%add28.i") (reg "%arrayidx29.i"),
      .binop "%sub30.i" .add 64 (reg "%and26.i") (lit 64 (-1)),
      .binop "%and31.i" .and 64 (reg "%sub30.i") (reg "%and26.i"),
      .call "%9" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and31.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast32.i" 64 32 (reg "%9"),
      .binop "%add33.i" .or 32 (reg "%conv") (reg "%cast32.i"),
      .gep "%arrayidx34.i" (.int 8) (reg "%add.ptr") (lit 64 28),
      .store (.int 32) (reg "%add33.i") (reg "%arrayidx34.i"),
      .icmp "%cmp.i" .ult 64 (reg "%1") (lit 64 9)],
    term := .condbr (reg "%cmp.i") "s1f_ke_b8.exit" "if.end39.i" }

def b8TailGuard : Block :=
  { name := "if.end39.i",
    instrs := [
      .binop "%sub35.i" .add 64 (reg "%and31.i") (lit 64 (-1)),
      .binop "%and36.i" .and 64 (reg "%sub35.i") (reg "%and31.i"),
      .call "%10" (.int 64) "llvm.ctpop.i64" [((.int 64), (reg "%and36.i"))],
      .binop "%11" .add 64 (reg "%10") (lit 64 8),
      .icmp "%12" .eq 64 (reg "%and36.i") (lit 64 0)],
    term := .condbr (reg "%12") "s1f_ke_b8.exit" "while.body.preheader.i" }

def b8TailPreheader : Block :=
  { name := "while.body.preheader.i",
    instrs := [
      .gep "%add.ptr.i" (.int 8) (reg "%add.ptr") (lit 64 32),
      .binop "%xtraiter" .and 64 (reg "%10") (lit 64 7),
      .icmp "%13" .ult 64 (reg "%10") (lit 64 8)],
    term := .condbr (reg "%13") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.preheader.i.new" }

def b8TailUnrolled : Block :=
  { name := "while.body.preheader.i.new",
    instrs := [
      .binop "%unroll_iter" .and 64 (reg "%10") (lit 64 56)],
    term := .br "while.body.i" }

def b8TailLoop : Block :=
  { name := "while.body.i",
    instrs := [
      .phi "%c.096.i" (.int 64) [("while.body.preheader.i.new", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
      .phi "%o.addr.095.i" .ptr [("while.body.preheader.i.new", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
      .phi "%niter" (.int 64) [("while.body.preheader.i.new", (lit 64 0)), ("while.body.i", (reg "%niter.next.7"))],
      .call "%14" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%c.096.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i" 64 32 (reg "%14"),
      .binop "%add42.i" .or 32 (reg "%conv") (reg "%cast41.i"),
      .gep "%incdec.ptr.i" (.int 8) (reg "%o.addr.095.i") (lit 64 4),
      .store (.int 32) (reg "%add42.i") (reg "%o.addr.095.i"),
      .binop "%sub43.i" .add 64 (reg "%c.096.i") (lit 64 (-1)),
      .binop "%and44.i" .and 64 (reg "%sub43.i") (reg "%c.096.i"),
      .call "%15" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.1" 64 32 (reg "%15"),
      .binop "%add42.i.1" .or 32 (reg "%conv") (reg "%cast41.i.1"),
      .gep "%incdec.ptr.i.1" (.int 8) (reg "%o.addr.095.i") (lit 64 8),
      .store (.int 32) (reg "%add42.i.1") (reg "%incdec.ptr.i"),
      .binop "%sub43.i.1" .add 64 (reg "%and44.i") (lit 64 (-1)),
      .binop "%and44.i.1" .and 64 (reg "%sub43.i.1") (reg "%and44.i"),
      .call "%16" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.1")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.2" 64 32 (reg "%16"),
      .binop "%add42.i.2" .or 32 (reg "%conv") (reg "%cast41.i.2"),
      .gep "%incdec.ptr.i.2" (.int 8) (reg "%o.addr.095.i") (lit 64 12),
      .store (.int 32) (reg "%add42.i.2") (reg "%incdec.ptr.i.1"),
      .binop "%sub43.i.2" .add 64 (reg "%and44.i.1") (lit 64 (-1)),
      .binop "%and44.i.2" .and 64 (reg "%sub43.i.2") (reg "%and44.i.1"),
      .call "%17" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.2")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.3" 64 32 (reg "%17"),
      .binop "%add42.i.3" .or 32 (reg "%conv") (reg "%cast41.i.3"),
      .gep "%incdec.ptr.i.3" (.int 8) (reg "%o.addr.095.i") (lit 64 16),
      .store (.int 32) (reg "%add42.i.3") (reg "%incdec.ptr.i.2"),
      .binop "%sub43.i.3" .add 64 (reg "%and44.i.2") (lit 64 (-1)),
      .binop "%and44.i.3" .and 64 (reg "%sub43.i.3") (reg "%and44.i.2"),
      .call "%18" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.3")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.4" 64 32 (reg "%18"),
      .binop "%add42.i.4" .or 32 (reg "%conv") (reg "%cast41.i.4"),
      .gep "%incdec.ptr.i.4" (.int 8) (reg "%o.addr.095.i") (lit 64 20),
      .store (.int 32) (reg "%add42.i.4") (reg "%incdec.ptr.i.3"),
      .binop "%sub43.i.4" .add 64 (reg "%and44.i.3") (lit 64 (-1)),
      .binop "%and44.i.4" .and 64 (reg "%sub43.i.4") (reg "%and44.i.3"),
      .call "%19" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.4")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.5" 64 32 (reg "%19"),
      .binop "%add42.i.5" .or 32 (reg "%conv") (reg "%cast41.i.5"),
      .gep "%incdec.ptr.i.5" (.int 8) (reg "%o.addr.095.i") (lit 64 24),
      .store (.int 32) (reg "%add42.i.5") (reg "%incdec.ptr.i.4"),
      .binop "%sub43.i.5" .add 64 (reg "%and44.i.4") (lit 64 (-1)),
      .binop "%and44.i.5" .and 64 (reg "%sub43.i.5") (reg "%and44.i.4"),
      .call "%20" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.5")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.6" 64 32 (reg "%20"),
      .binop "%add42.i.6" .or 32 (reg "%conv") (reg "%cast41.i.6"),
      .gep "%incdec.ptr.i.6" (.int 8) (reg "%o.addr.095.i") (lit 64 28),
      .store (.int 32) (reg "%add42.i.6") (reg "%incdec.ptr.i.5"),
      .binop "%sub43.i.6" .add 64 (reg "%and44.i.5") (lit 64 (-1)),
      .binop "%and44.i.6" .and 64 (reg "%sub43.i.6") (reg "%and44.i.5"),
      .call "%21" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%and44.i.6")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.7" 64 32 (reg "%21"),
      .binop "%add42.i.7" .or 32 (reg "%conv") (reg "%cast41.i.7"),
      .gep "%incdec.ptr.i.7" (.int 8) (reg "%o.addr.095.i") (lit 64 32),
      .store (.int 32) (reg "%add42.i.7") (reg "%incdec.ptr.i.6"),
      .binop "%sub43.i.7" .add 64 (reg "%and44.i.6") (lit 64 (-1)),
      .binop "%and44.i.7" .and 64 (reg "%sub43.i.7") (reg "%and44.i.6"),
      .binop "%niter.next.7" .add 64 (reg "%niter") (lit 64 8),
      .icmp "%niter.ncmp.7" .eq 64 (reg "%niter.next.7") (reg "%unroll_iter")],
    term := .condbr (reg "%niter.ncmp.7") "s1f_ke_b8.exit.loopexit.unr-lcssa" "while.body.i" }

def b8TailRemainderGuard : Block :=
  { name := "s1f_ke_b8.exit.loopexit.unr-lcssa",
    instrs := [
      .phi "%c.096.i.unr" (.int 64) [("while.body.preheader.i", (reg "%and36.i")), ("while.body.i", (reg "%and44.i.7"))],
      .phi "%o.addr.095.i.unr" .ptr [("while.body.preheader.i", (reg "%add.ptr.i")), ("while.body.i", (reg "%incdec.ptr.i.7"))],
      .icmp "%lcmp.mod.not" .eq 64 (reg "%xtraiter") (lit 64 0)],
    term := .condbr (reg "%lcmp.mod.not") "s1f_ke_b8.exit" "while.body.i.epil" }

def b8TailRemainder : Block :=
  { name := "while.body.i.epil",
    instrs := [
      .phi "%c.096.i.epil" (.int 64) [("while.body.i.epil", (reg "%and44.i.epil")), ("s1f_ke_b8.exit.loopexit.unr-lcssa", (reg "%c.096.i.unr"))],
      .phi "%o.addr.095.i.epil" .ptr [("while.body.i.epil", (reg "%incdec.ptr.i.epil")), ("s1f_ke_b8.exit.loopexit.unr-lcssa", (reg "%o.addr.095.i.unr"))],
      .phi "%epil.iter" (.int 64) [("while.body.i.epil", (reg "%epil.iter.next")), ("s1f_ke_b8.exit.loopexit.unr-lcssa", (lit 64 0))],
      .call "%22" (.int 64) "llvm.cttz.i64" [((.int 64), (reg "%c.096.i.epil")), ((.int 1), (lit 1 (-1)))],
      .trunc "%cast41.i.epil" 64 32 (reg "%22"),
      .binop "%add42.i.epil" .or 32 (reg "%conv") (reg "%cast41.i.epil"),
      .gep "%incdec.ptr.i.epil" (.int 8) (reg "%o.addr.095.i.epil") (lit 64 4),
      .store (.int 32) (reg "%add42.i.epil") (reg "%o.addr.095.i.epil"),
      .binop "%sub43.i.epil" .add 64 (reg "%c.096.i.epil") (lit 64 (-1)),
      .binop "%and44.i.epil" .and 64 (reg "%sub43.i.epil") (reg "%c.096.i.epil"),
      .binop "%epil.iter.next" .add 64 (reg "%epil.iter") (lit 64 1),
      .icmp "%epil.iter.cmp.not" .eq 64 (reg "%epil.iter.next") (reg "%xtraiter")],
    term := .condbr (reg "%epil.iter.cmp.not") "s1f_ke_b8.exit" "while.body.i.epil" }

def b8Join : Block :=
  { name := "s1f_ke_b8.exit",
    instrs := [
      .phi "%retval.0.i" (.int 64) [("if.end", (reg "%1")), ("if.end39.i", (lit 64 8)), ("while.body.i.epil", (reg "%11")), ("s1f_ke_b8.exit.loopexit.unr-lcssa", (reg "%11"))],
      .binop "%add1" .add 64 (reg "%retval.0.i") (reg "%k.addr.011")],
    term := .br "cleanup" }

def b8Advance : Block :=
  { name := "cleanup",
    instrs := [
      .phi "%k.addr.1" (.int 64) [("s1f_ke_b8.exit", (reg "%add1")), ("for.body", (reg "%k.addr.011"))],
      .binop "%inc" .add 64 (reg "%i.010") (lit 64 1),
      .icmp "%exitcond.not" .eq 64 (reg "%inc") (reg "%nblk")],
    term := .condbr (reg "%exitcond.not") "for.cond.cleanup" "for.body" }

/-- The B8 kernel: the block loop, eight fixed slots per mask word, and a scalar
loop for the lanes past the eighth. -/
def entryB8Function : Function :=
  { name := "s1f_k_b8",
    retTy := .int 64,
    params := [("%ent", .ptr), ("%blk0", .int 64), ("%nblk", .int 64), ("%out", .ptr), ("%k", .int 64)],
    blocks :=
      [b8Entry,
       b8LoopExit,
       b8Body,
       b8Kernel,
       b8TailGuard,
       b8TailPreheader,
       b8TailUnrolled,
       b8TailLoop,
       b8TailRemainderGuard,
       b8TailRemainder,
       b8Join,
       b8Advance] }


/-! ### The pin -/

-- The committed text parses to the POS8 body above.
#guard decide (firstFunction jsonEntrySrc = some entryPos8Function)

-- And to the B8 body, in the emission's order, so the one text is the subject of
-- both kernels rather than two texts that could drift apart.
#guard
  match parseModule jsonEntrySrc with
  | .ok m => m.functions = [entryPos8Function, entryB8Function]
  | .error _ => false

-- The POS8 fixture's ABI: the measured five parameters in their order, then the
-- table base the rewrite appends.
#guard
  match firstFunction jsonEntrySrc with
  | some f =>
      f.name = "s1f_k_pos8" ∧ f.retTy = Ty.int 64 ∧
      f.params = [("%ent", Ty.ptr), ("%blk0", Ty.int 64), ("%nblk", Ty.int 64),
                  ("%out", Ty.ptr), ("%k", Ty.int 64), ("%tab", Ty.ptr)]
  | none => false

-- The B8 fixture's ABI: the measured five, and no table — the kernel reads
-- none, which is why its parameter list is the emission's own.
#guard
  match parseModule jsonEntrySrc with
  | .ok m =>
      match m.functions.drop 1 with
      | [f] =>
          f.name = "s1f_k_b8" ∧ f.retTy = Ty.int 64 ∧
          f.params = [("%ent", Ty.ptr), ("%blk0", Ty.int 64), ("%nblk", Ty.int 64),
                      ("%out", Ty.ptr), ("%k", Ty.int 64)]
      | _ => false
  | .error _ => false

open LeanLLVM.Refinement.JsonScanSpec

/-! ### The call environment

`evalInstr`'s `.call` case consults a `Calls` environment, and `noCalls` answers
`none`, which `step` reads as `ub`; a statement over `noCalls` would therefore
say nothing about either body.  The environment below resolves the three
intrinsics the entry emission calls — `llvm.ctpop.i32`, `llvm.ctpop.i64` and
`llvm.cttz.i64` — to the lane vocabulary in `BitLanes`, and nothing else: an
unresolved symbol stays `ub`.

`ctpop` is exact at every word, so its two widths need no side condition.
`cttz`'s `i1` flag is admitted at both values: at `false` the model's `cttz` is
exactly LLVM's (the least set lane, and the width at the zero word), and at
`true` LLVM makes the zero word poison while this model gives it the width.  The
`true` flag is admissible **only under the bound the kernels' clauses state**: a
value produced at a cleared word reaches lanes at or past the emitted count,
which no clause of `entry_pos8_refines` (or of the B8 statement) reads — the
words clause stops at `k'` and the frame clause permits writes only up to
`k'+7`.  `ctlz … i1 true` is not admitted, because neither body reads it and no
clause would bound where its poison lands; the asymmetry is stated at
`checkIntrinsicShape`, which refuses it. -/

/-- The unit's reference call environment: the three entry intrinsics. -/
def entryCalls : Calls :=
  fun callee args mem next =>
    match callee, args with
    | "llvm.ctpop.i32", [.int 32 x] =>
        some { ret := .int 32 (BitVec.ofNat 32 (BitLanes.ctpop x)),
               mem := mem, next := next }
    | "llvm.ctpop.i64", [.int 64 x] =>
        some { ret := .int 64 (BitVec.ofNat 64 (BitLanes.ctpop x)),
               mem := mem, next := next }
    | "llvm.cttz.i64", [.int 64 x, .int 1 _flag] =>
        some { ret := .int 64 (BitVec.ofNat 64 (BitLanes.cttz x)),
               mem := mem, next := next }
    | _, _ => none

/-- **The entry unit's caller-visible footprint is empty.**  The three count
intrinsics are register operations, so every arm returns the caller's memory and
no caller address moves. -/
def entryCallsFootprint : CallsFootprint entryCalls :=
  CallsFootprint.pure entryCalls (by
    intro sym args mem next r h
    simp only [entryCalls] at h
    repeat' split at h
    all_goals (cases h <;> rfl))

/-- The 32-bit population count. -/
theorem entryCalls_ctpop32 (x : BitVec 32) (mem : Mem) (next : Nat) :
    entryCalls "llvm.ctpop.i32" [.int 32 x] mem next =
      some { ret := .int 32 (BitVec.ofNat 32 (BitLanes.ctpop x)),
             mem := mem, next := next } :=
  rfl

/-- The 64-bit population count. -/
theorem entryCalls_ctpop64 (x : BitVec 64) (mem : Mem) (next : Nat) :
    entryCalls "llvm.ctpop.i64" [.int 64 x] mem next =
      some { ret := .int 64 (BitVec.ofNat 64 (BitLanes.ctpop x)),
             mem := mem, next := next } :=
  rfl

/-- The trailing count, at either flag: the flag does not change the value the
model gives.  The flagged spelling is admissible because the model's value is
exact wherever LLVM's poison would land — a poison-carrying count is accepted
only where it agrees with the model, so the body's choice of flag cannot move
the result it writes. -/
theorem entryCalls_cttz (x : BitVec 64) (flag : BitVec 1) (mem : Mem) (next : Nat) :
    entryCalls "llvm.cttz.i64" [.int 64 x, .int 1 flag] mem next =
      some { ret := .int 64 (BitVec.ofNat 64 (BitLanes.cttz x)),
             mem := mem, next := next } :=
  rfl

/-! ### The stream the statement names

The mask stream is `nblk` little-endian `i64` words; the table is the 256 rows
`pos8Row` gives, each four little-endian bytes per lane; and the output is read
back as `k' - k` little-endian `i32` words.  All three are stated address-free:
the theory's hypotheses place them at `%ent` and `%tab`, and the buffer at
`%out`, so no address is a parameter of a definition here. -/

/-- A list of 64-bit masks as the bytes the stream occupies. -/
def wordsOf (ent : List (BitVec 64)) : List UInt8 :=
  (ent.map fun m => natToBytes m.toNat 8).flatten

/-- `n` little-endian `i32` words at `addr`, or `none` when a byte is absent.
Stated recursively so a proofs about a concatenation peel one word at a time. -/
def readLanes32 (m : Mem) (addr : Nat) : Nat → Option (List Nat)
  | 0 => some []
  | n + 1 =>
      (readBytes m addr 4).bind fun bs =>
        (readLanes32 m (addr + 4) n).map fun rest => bytesToNat bs :: rest

/-- The output cursor's contents after `j` blocks, as the stream the model
names: every block's positions, block order preserved. -/
def streamPrefix (ent : List (BitVec 64)) (blk0 j : Nat) : List Nat :=
  ((ent.take j).mapIdx fun i m => positionsOf m (64 * (blk0 + i))).flatten

/-- One table row as the 32 bytes the body's vector load reads. -/
def pos8RowBytes (m : Nat) : List UInt8 :=
  ((pos8Row m).map fun v => natToBytes v.toNat 4).flatten

/-- The table's 8 KiB, address-free: `pos8Row` at each of the 256 indices.  The
theorem reads it at `%tab`, so the hypothesis is
`readBytes mem tab 8192 = some pos8Table`; the rows hold no addresses, and an
address argument could not change a byte. -/
def pos8Table : List UInt8 :=
  (List.range 256).flatMap pos8RowBytes

/-- A list of `n` copies of `a` sums to `n * a`. -/
theorem sum_replicate (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]; omega

/-- A row has eight lanes. -/
theorem pos8Row_length (m : Nat) : (pos8Row m).length = 8 := by
  simp [pos8Row, BitLanes.setLanes_length_le]


/-- A row's bytes are `4 * 8`. -/
theorem pos8RowBytes_length (m : Nat) : (pos8RowBytes m).length = 32 := by
  rw [pos8RowBytes, List.length_flatten]
  simp only [List.map_map, Function.comp_def, natToBytes_length]
  rw [List.map_const', pos8Row_length, sum_replicate]

/-- The table's 256 rows are 8 KiB. -/
theorem pos8Table_length : pos8Table.length = 8192 := by
  rw [pos8Table, List.length_flatMap]
  simp only [pos8RowBytes_length]
  rw [List.map_const', List.length_range, sum_replicate]

/-! ### The tail mask

`limMask lim` is `(1 <<< lim) - 1` below the block's width and all-ones at it, so
its low `lim` lanes are set and every higher lane is clear.  `entry_tail_eq` reads
that as the statement the tail exists for: masking a block with `limMask (n - b)`
leaves exactly the positions below the document's end `n`. -/

/-- Below the width, the mask's lanes are exactly those below `lim`. -/
theorem limMask_getLsbD (lim k : Nat) (hlim : lim ≤ 64) (hk : k < 64) :
    (limMask lim).getLsbD k = decide (k < lim) := by
  by_cases h : lim < 64
  · have hpow : 2 ^ lim < 2 ^ 64 := by
      have hle : 2 ^ lim ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have h63 : 2 ^ 63 < 2 ^ 64 := by decide
      omega
    have hpos : 0 < 2 ^ lim := Nat.two_pow_pos lim
    have htoNat : (((1 : BitVec 64) <<< lim) - 1).toNat = 2 ^ lim - 1 := by
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
      rw [show (1 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
      rw [Nat.mod_eq_of_lt hpow]
      rw [show 2 ^ 64 - 1 + 2 ^ lim = (2 ^ lim - 1) + 2 ^ 64 from by omega]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [limMask, if_pos h]
    show (((1 : BitVec 64) <<< lim) - 1).getLsbD k = _
    rw [BitVec.getLsbD, htoNat]
    exact BitLanes.testBit_two_pow_sub_one lim k
  · have h64 : lim = 64 := by omega
    subst h64
    rw [limMask, if_neg h]
    have hall : BitVec.ofInt 64 (-1) = BitVec.allOnes 64 := by decide
    rw [hall, BitLanes.allOnes_getLsbD_of_lt hk]
    exact (decide_eq_true hk).symm

/-- Masking with `limMask` clears exactly the lanes at or above `lim`. -/
theorem getLsbD_and_limMask (m : BitVec 64) (lim k : Nat) (hlim : lim ≤ 64) :
    (m &&& limMask lim).getLsbD k = (m.getLsbD k && decide (k < lim)) := by
  rw [BitVec.getLsbD_and]
  by_cases hk : k < 64
  · rw [limMask_getLsbD lim k hlim hk]
  · have h1 : m.getLsbD k = false := BitVec.getLsbD_of_ge m k (by omega)
    have h2 : (limMask lim).getLsbD k = false := BitVec.getLsbD_of_ge _ k (by omega)
    rw [h1, h2]
    simp

/-- Masking with `limMask` leaves exactly the low lanes of the mask. -/
theorem setLanes_and_limMask (m : BitVec 64) (lim : Nat) (hlim : lim ≤ 64) :
    BitLanes.setLanes (m &&& limMask lim) = (BitLanes.setLanes m).filter (· < lim) := by
  unfold BitLanes.setLanes
  rw [List.filter_filter]
  congr 1
  funext k
  rw [getLsbD_and_limMask m lim k hlim, Bool.and_comm]

/-- A mask's positions, filtered at the document's end, are the tail mask's
positions. -/
theorem positionsOf_filter (m : BitVec 64) (base n : Nat) (h : base ≤ n) :
    (positionsOf m base).filter (· < n) =
      ((BitLanes.setLanes m).filter (· < n - base)).map (fun k => base + k) := by
  unfold positionsOf
  induction (BitLanes.setLanes m) with
  | nil => rfl
  | cons k ks ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases hk : base + k < n
      · have hk' : k < n - base := by omega
        simp [hk, hk', ih]
      · have hk' : ¬ k < n - base := by omega
        simp [hk, hk', ih]

/-- **The tail mask keeps exactly the positions below the document's end.**
For a block base `b` and a document end `n` with `b ≤ n ≤ b + 64`, the tail
mask's positions are the block's positions filtered at `n`; the `take` spells the
population count, which is the whole list. -/
theorem entry_tail_eq (mask : BitVec 64) (b n : Nat) (hb : b ≤ n)
    (hn : n ≤ b + 64) :
    (positionsOf (mask &&& limMask (n - b)) b).take
        (BitLanes.ctpop (mask &&& limMask (n - b))) =
      (positionsOf mask b).filter (· < n) := by
  have hpos : positionsOf (mask &&& limMask (n - b)) b
      = ((BitLanes.setLanes mask).filter (· < n - b)).map (fun k => b + k) := by
    unfold positionsOf
    rw [setLanes_and_limMask mask (n - b) (by omega)]
  rw [hpos, BitLanes.ctpop_eq_setLanes_length]
  rw [show (BitLanes.setLanes (mask &&& limMask (n - b))).length
      = (((BitLanes.setLanes mask).filter (· < n - b)).map (fun k => b + k)).length from by
    simp [setLanes_and_limMask mask (n - b) (by omega)]]
  rw [List.take_length]
  exact (positionsOf_filter mask b n hb).symm

/-! ### The block's eight bytes

The table the POS8 body indexes is one row per **mask byte**, so the positions a
block's mask names are the block's set lanes read eight at a time.  The facts
below are that reading: `byteOf` is a mask word's `j`-th byte, its bit `t` is the
word's bit `8 * j + t`, and the word's set lanes are the concatenation of its
eight bytes' set lanes, each shifted by the byte's index. -/

/-- The `j`-th byte of a mask word, as a number below 256. -/
def byteOf (m : BitVec 64) (j : Nat) : Nat := (m.toNat / 2 ^ (8 * j)) % 256

/-- A byte is below 256. -/
theorem byteOf_lt (m : BitVec 64) (j : Nat) : byteOf m j < 256 :=
  Nat.mod_lt _ (by decide)

/-- A byte's bit `t` is the word's bit `8 * j + t`. -/
theorem byteOf_testBit (m : BitVec 64) (j t : Nat) (ht : t < 8) :
    (byteOf m j).testBit t = m.toNat.testBit (8 * j + t) := by
  unfold byteOf
  rw [show (256 : Nat) = 2 ^ 8 from rfl, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  rw [show decide (t < 8) = true from decide_eq_true ht]
  simp [Nat.add_comm]

/-- The byte as a `BitVec 8` reads the same bit. -/
theorem getLsbD_byteOf (m : BitVec 64) (j t : Nat) (ht : t < 8) :
    (BitVec.ofNat 8 (byteOf m j)).getLsbD t = m.getLsbD (8 * j + t) := by
  rw [BitVec.getLsbD_ofNat, BitVec.getLsbD, byteOf_testBit m j t ht]
  simp [ht]

/-- The eight byte blocks tile the word's lanes. -/
theorem range_flatMap_bytes :
    (List.range 8).flatMap (fun j => (List.range 8).map (fun t => 8 * j + t)) =
      List.range 64 := by
  decide

/-- Filtering a `flatMap` is filtering each block. -/
theorem filter_flatMap (l : List Nat) (f : Nat → List Nat) (p : Nat → Bool) :
    (l.flatMap f).filter p = l.flatMap (fun a => (f a).filter p) := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.flatMap_cons, List.filter_append, List.flatMap_cons, ih]

/-- `flatMap` respects a pointwise equality. -/
theorem flatMap_congr {l : List Nat} {f g : Nat → List Nat}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
        ih (fun b hb => h b (by simp [hb]))]

/-- **A word's set lanes are its eight bytes' set lanes, shifted by the byte's
index.** -/
theorem setLanes_eq_bytes (m : BitVec 64) :
    BitLanes.setLanes m =
      ((List.range 8).map (fun j =>
        (BitLanes.setLanes (BitVec.ofNat 8 (byteOf m j))).map
          (fun t => 8 * j + t))).flatten := by
  unfold BitLanes.setLanes
  rw [show List.range 64 =
      (List.range 8).flatMap (fun j => (List.range 8).map (fun t => 8 * j + t)) from
    range_flatMap_bytes.symm]
  rw [filter_flatMap]
  apply flatMap_congr
  intro j _
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro t ht
  exact (getLsbD_byteOf m j t (List.mem_range.mp ht)).symm

/-- A row's first `popcount` lanes are its set lanes, as 32-bit values. -/
theorem pos8Row_take (b : Nat) :
    (pos8Row b).take (BitLanes.ctpop (BitVec.ofNat 8 b)) =
      (BitLanes.setLanes (BitVec.ofNat 8 b)).map (fun k => BitVec.ofNat 32 k) := by
  unfold pos8Row
  rw [BitLanes.ctpop_eq_setLanes_length, ← List.length_map]
  exact List.take_left

/-- A row's set lanes, read at a block's base, are the block's positions in that
byte's group. -/
theorem pos8Row_take_map (b base j : Nat) :
    ((pos8Row b).take (BitLanes.ctpop (BitVec.ofNat 8 b))).map
        (fun v => base + 8 * j + v.toNat) =
      (BitLanes.setLanes (BitVec.ofNat 8 b)).map (fun t => base + 8 * j + t) := by
  rw [pos8Row_take, List.map_map]
  apply List.map_congr_left
  intro t ht
  have ht8 : t < 8 := (BitLanes.mem_setLanes.mp ht).1
  simp only [Function.comp_apply, BitVec.toNat_ofNat]
  rw [show t % 2 ^ 32 = t from Nat.mod_eq_of_lt (by omega)]

/-- **A block's positions, split at its eight mask bytes.**  This is what makes
the table read a positions read: group `j`'s positions are the set lanes of byte
`j`, offset by the byte's place in the block. -/
theorem positionsOf_eq_bytes (m : BitVec 64) (base : Nat) :
    positionsOf m base =
      ((List.range 8).map (fun j =>
        ((pos8Row (byteOf m j)).take (BitLanes.ctpop (BitVec.ofNat 8 (byteOf m j)))).map
          (fun v => base + 8 * j + v.toNat))).flatten := by
  unfold positionsOf
  rw [setLanes_eq_bytes]
  have hRHS :
      (List.map (fun j => List.map (fun v => base + 8 * j + v.toNat)
          ((pos8Row (byteOf m j)).take (BitLanes.ctpop (BitVec.ofNat 8 (byteOf m j)))))
        (List.range 8)) =
      (List.map (fun j => List.map (fun t => base + 8 * j + t)
          (BitLanes.setLanes (BitVec.ofNat 8 (byteOf m j)))) (List.range 8)) := by
    apply List.map_congr_left
    intro j _
    exact pos8Row_take_map (byteOf m j) base j
  rw [hRHS, List.map_flatten, List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply]
  rw [List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply]
  omega

end LeanLLVM.Refinement.JsonEntryIR
