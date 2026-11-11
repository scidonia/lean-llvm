/-
The escape unit's emitted bodies, pinned.

`probes/install/ir/json-escape.candidate.ll` is the escape unit at the measured
compiler line, reduced to the four definitions its two entry points reach: the
escape-position list `@leanllvm_json_escape_list`, the expander's entry point
`@leanllvm_json_escape_expand`, the decoder `@us_dec_x` it calls, and the
out-of-line batch `@xl_batch` the list calls.  This module parses the fixture and
pins the parsed AST against the literal below, the way `JsonEntryIR`,
`JsonS1MasksIR` and `JsonUtf8IR` pin theirs: the pin is a `#guard`, because the
parser runs on `String` primitives, which the kernel does not reduce, so an AST
proposition cannot be closed by reflexivity.

The pin compares **every** function the fixture defines rather than only the two
entry points.  A body reached through a call is part of the claim about the body
the run starts at — `@xl_batch` is called by the list on every block with more
than eight escape lanes, and `@us_dec_x` is the body the expander's thunk calls —
so a pin that stopped at the entry points would leave the callees unobserved
while the theorems read through them.

The counts beside the copies are the enumeration's own: the block list and the
instruction line of each block, so a fixture that changed shape fails the pin at
the count as well as at the literal.

Both closure parameters the emission adds are visible here and are the reason the
literal is not the source text: the fragment has no module-level globals, so the
escape table the decoder reads is passed as the appended `%tab` parameter, and the
sixteen-lane `select` the hex reader carries is modelled lane-wise by `Syntax`.
The fixture's own header records both rewrites.
-/
import LeanLLVM.Parser
import LeanLLVM.Refinement.JsonEscapeIntrinsics
import LeanLLVM.Refinement.Refinement

namespace LeanLLVM.Refinement.JsonEscapeIR

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonEscapeIntrinsics

/-! ### The fixture -/

/-- The unit as emitted and committed. -/
def escapeSrc : String :=
  include_str "../../probes/install/ir/json-escape.candidate.ll"

/-- Parse a fixture and take its first function. -/
def firstFunction (src : String) : Option Function :=
  match parseModule src with
  | .ok m => m.functions.head?
  | .error _ => none

/-! ### The pinned AST

The four definitions in the fixture's order, instruction by instruction.  The
literal is the parse written out; the `#guard`s below are what tie it to the
committed bytes. -/

/-- `@leanllvm_json_escape_list` — the mask-driven position emitter.

Seven parameters: the classifier's three words, the position base as a block
index, the output stream and its count, and the two-word carry.  The body forms
the run-start word from `bs` by doubling it through the `and7` word to a fixed
point, folds `ctl` and `im` into the escape word, stores the eight-entry first
batch at `xp + 4 * *xn`, and hands the remaining set bits to `@xl_batch` eight at
a time. -/
def escapeListFunction : Function :=
{ name := "leanllvm_json_escape_list",
  retTy := .void,
  params := [("%bs", .int 64), ("%ctl", .int 64), ("%im", .int 64), ("%blk0", .int 64), ("%xp", .ptr), ("%xn", .ptr), ("%carry", .ptr)],
  blocks := [
  { name := "entry",
    instrs := [
      .gep "%arrayidx1" (.int 8) (.reg "%carry") (.imm (.int 64 (BitVec.ofInt 64 (8)))),
      .load "%0" (.int 64) (.reg "%carry"),
      .binop "%shl.i" .shl 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .binop "%or.i" .or 64 (.reg "%0") (.reg "%shl.i"),
      .binop "%not.i" .xor 64 (.reg "%or.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.i" .and 64 (.reg "%bs") (.reg "%not.i"),
      .binop "%and1.i" .and 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .binop "%and2.i" .and 64 (.reg "%and1.i") (.reg "%0"),
      .icmp "%tobool.not.i" .eq 64 (.reg "%and2.i") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
    ],
    term := .condbr (.reg "%tobool.not.i") "if.end.i" "if.then.i" },
  { name := "if.then.i",
    instrs := [
      .load "%1" (.int 64) (.reg "%arrayidx1"),
      .icmp "%tobool3.not.i" .eq 64 (.reg "%1") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
      .binop "%and4.i" .and 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .select "%cond.i" (.int 64) (.reg "%tobool3.not.i") (.imm (.int 64 (BitVec.ofInt 64 (1)))) (.reg "%and4.i"),
      .binop "%or5.i" .or 64 (.reg "%cond.i") (.reg "%and.i"),
    ],
    term := .br "if.end.i" },
  { name := "if.end.i",
    instrs := [
      .phi "%e.0.i" (.int 64) [("if.then.i", .reg "%or5.i"), ("entry", .reg "%and.i")],
      .binop "%and7.i" .and 64 (.reg "%shl.i") (.reg "%bs"),
      .binop "%shl8.i" .shl 64 (.reg "%e.0.i") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .binop "%and9.i" .and 64 (.reg "%shl8.i") (.reg "%and7.i"),
      .binop "%or10.i" .or 64 (.reg "%and9.i") (.reg "%e.0.i"),
      .binop "%shl11.i" .shl 64 (.reg "%or10.i") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .binop "%and12.i" .and 64 (.reg "%shl11.i") (.reg "%and7.i"),
      .binop "%or13.i" .or 64 (.reg "%and12.i") (.reg "%or10.i"),
      .binop "%shl14.i" .shl 64 (.reg "%or13.i") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .binop "%not16.i" .xor 64 (.reg "%or13.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%2" .and 64 (.reg "%shl14.i") (.reg "%not16.i"),
      .binop "%and17.i" .and 64 (.reg "%2") (.reg "%and7.i"),
      .icmp "%cmp.not.i" .eq 64 (.reg "%and17.i") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
    ],
    term := .condbr (.reg "%cmp.not.i") "xl_lanes.exit" "do.body.i" },
  { name := "do.body.i",
    instrs := [
      .phi "%e.1.i" (.int 64) [("do.body.i", .reg "%or23.i"), ("if.end.i", .reg "%or13.i")],
      .binop "%shl21.i" .shl 64 (.reg "%e.1.i") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .binop "%and22.i" .and 64 (.reg "%shl21.i") (.reg "%and7.i"),
      .binop "%or23.i" .or 64 (.reg "%and22.i") (.reg "%e.1.i"),
      .icmp "%cmp24.not.i" .eq 64 (.reg "%or23.i") (.reg "%e.1.i"),
    ],
    term := .condbr (.reg "%cmp24.not.i") "xl_lanes.exit" "do.body.i" },
  { name := "xl_lanes.exit",
    instrs := [
      .phi "%e.2.i" (.int 64) [("if.end.i", .reg "%or13.i"), ("do.body.i", .reg "%e.1.i")],
      .binop "%shr.i" .lshr 64 (.reg "%bs") (.imm (.int 64 (BitVec.ofInt 64 (63)))),
      .store (.int 64) (.reg "%shr.i") (.reg "%carry"),
      .binop "%shr2757.i" .and 64 (.reg "%e.2.i") (.reg "%bs"),
      .binop "%and29.i" .lshr 64 (.reg "%shr2757.i") (.imm (.int 64 (BitVec.ofInt 64 (63)))),
      .store (.int 64) (.reg "%and29.i") (.reg "%arrayidx1"),
      .binop "%or30.i" .or 64 (.reg "%e.2.i") (.reg "%ctl"),
      .binop "%and31.i" .and 64 (.reg "%or30.i") (.reg "%im"),
      .trunc "%blk0.tr" 64 32 (.reg "%blk0"),
      .binop "%conv" .shl 32 (.reg "%blk0.tr") (.imm (.int 32 (BitVec.ofInt 32 (6)))),
      .icmp "%tobool.not.i3" .eq 64 (.reg "%and31.i") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
    ],
    term := .condbr (.reg "%tobool.not.i3") "xl_emit.exit" "if.end.i4" },
  { name := "if.end.i4",
    instrs := [
      .load "%3" (.int 64) (.reg "%xn"),
      .gep "%add.ptr.i.i" (.int 32) (.reg "%xp") (.reg "%3"),
      .binop "%or.i.i.i" .or 64 (.reg "%and31.i") (.imm (.int 64 (BitVec.ofInt 64 (-9223372036854775808)))),
      .call "%4" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%or.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast.i.i.i" 64 32 (.reg "%4"),
      .binop "%add.i.i.i" .or 32 (.reg "%conv") (.reg "%cast.i.i.i"),
      .store (.int 32) (.reg "%add.i.i.i") (.reg "%add.ptr.i.i"),
      .binop "%sub.i.i.i" .add 64 (.reg "%or.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.i.i.i" .and 64 (.reg "%sub.i.i.i") (.reg "%or.i.i.i"),
      .call "%5" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast1.i.i.i" 64 32 (.reg "%5"),
      .binop "%add2.i.i.i" .or 32 (.reg "%conv") (.reg "%cast1.i.i.i"),
      .gep "%arrayidx3.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (4)))),
      .store (.int 32) (.reg "%add2.i.i.i") (.reg "%arrayidx3.i.i.i"),
      .binop "%sub4.i.i.i" .add 64 (.reg "%and.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and5.i.i.i" .and 64 (.reg "%sub4.i.i.i") (.reg "%and.i.i.i"),
      .call "%6" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and5.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast6.i.i.i" 64 32 (.reg "%6"),
      .binop "%add7.i.i.i" .or 32 (.reg "%conv") (.reg "%cast6.i.i.i"),
      .gep "%arrayidx8.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (8)))),
      .store (.int 32) (.reg "%add7.i.i.i") (.reg "%arrayidx8.i.i.i"),
      .binop "%sub9.i.i.i" .add 64 (.reg "%and5.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and10.i.i.i" .and 64 (.reg "%sub9.i.i.i") (.reg "%and5.i.i.i"),
      .call "%7" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and10.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast11.i.i.i" 64 32 (.reg "%7"),
      .binop "%add12.i.i.i" .or 32 (.reg "%conv") (.reg "%cast11.i.i.i"),
      .gep "%arrayidx13.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (12)))),
      .store (.int 32) (.reg "%add12.i.i.i") (.reg "%arrayidx13.i.i.i"),
      .binop "%sub14.i.i.i" .add 64 (.reg "%and10.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and15.i.i.i" .and 64 (.reg "%sub14.i.i.i") (.reg "%and10.i.i.i"),
      .call "%8" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and15.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast16.i.i.i" 64 32 (.reg "%8"),
      .binop "%add17.i.i.i" .or 32 (.reg "%conv") (.reg "%cast16.i.i.i"),
      .gep "%arrayidx18.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (16)))),
      .store (.int 32) (.reg "%add17.i.i.i") (.reg "%arrayidx18.i.i.i"),
      .binop "%sub19.i.i.i" .add 64 (.reg "%and15.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and20.i.i.i" .and 64 (.reg "%sub19.i.i.i") (.reg "%and15.i.i.i"),
      .call "%9" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and20.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast21.i.i.i" 64 32 (.reg "%9"),
      .binop "%add22.i.i.i" .or 32 (.reg "%conv") (.reg "%cast21.i.i.i"),
      .gep "%arrayidx23.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (20)))),
      .store (.int 32) (.reg "%add22.i.i.i") (.reg "%arrayidx23.i.i.i"),
      .binop "%sub24.i.i.i" .add 64 (.reg "%and20.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and25.i.i.i" .and 64 (.reg "%sub24.i.i.i") (.reg "%and20.i.i.i"),
      .call "%10" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and25.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast26.i.i.i" 64 32 (.reg "%10"),
      .binop "%add27.i.i.i" .or 32 (.reg "%conv") (.reg "%cast26.i.i.i"),
      .gep "%arrayidx28.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (24)))),
      .store (.int 32) (.reg "%add27.i.i.i") (.reg "%arrayidx28.i.i.i"),
      .binop "%sub29.i.i.i" .add 64 (.reg "%and25.i.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and30.i.i.i" .and 64 (.reg "%sub29.i.i.i") (.reg "%and25.i.i.i"),
      .call "%11" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and30.i.i.i"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast31.i.i.i" 64 32 (.reg "%11"),
      .binop "%add32.i.i.i" .or 32 (.reg "%conv") (.reg "%cast31.i.i.i"),
      .gep "%arrayidx33.i.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (28)))),
      .store (.int 32) (.reg "%add32.i.i.i") (.reg "%arrayidx33.i.i.i"),
      .call "%12" (.int 64) "llvm.ctpop.i64" [(.int 64, .reg "%and31.i")],
      .trunc "%cast36.i.i.i" 64 32 (.reg "%12"),
      .call "%cond.i.i.i" (.int 32) "llvm.umin.i32" [(.int 32, .reg "%cast36.i.i.i"), (.int 32, .imm (.int 32 (BitVec.ofInt 32 (8))))],
      .zext "%conv.i.i" 32 64 (.reg "%cond.i.i.i"),
      .binop "%add.i.i" .add 64 (.reg "%3") (.reg "%conv.i.i"),
      .store (.int 64) (.reg "%add.i.i") (.reg "%xn"),
      .icmp "%cmp.i.i" .ugt 64 (.reg "%12") (.imm (.int 64 (BitVec.ofInt 64 (8)))),
    ],
    term := .condbr (.reg "%cmp.i.i") "for.body.preheader.i.i" "xl_emit.exit" },
  { name := "for.body.preheader.i.i",
    instrs := [
      .binop "%sub.i.i" .add 64 (.reg "%and31.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.i.i" .and 64 (.reg "%sub.i.i") (.reg "%and31.i"),
      .binop "%sub.1.i.i" .add 64 (.reg "%and.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.1.i.i" .and 64 (.reg "%sub.1.i.i") (.reg "%and.i.i"),
      .binop "%sub.2.i.i" .add 64 (.reg "%and.1.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.2.i.i" .and 64 (.reg "%sub.2.i.i") (.reg "%and.1.i.i"),
      .binop "%sub.3.i.i" .add 64 (.reg "%and.2.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.3.i.i" .and 64 (.reg "%sub.3.i.i") (.reg "%and.2.i.i"),
      .binop "%sub.4.i.i" .add 64 (.reg "%and.3.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.4.i.i" .and 64 (.reg "%sub.4.i.i") (.reg "%and.3.i.i"),
      .binop "%sub.5.i.i" .add 64 (.reg "%and.4.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.5.i.i" .and 64 (.reg "%sub.5.i.i") (.reg "%and.4.i.i"),
      .binop "%sub.6.i.i" .add 64 (.reg "%and.5.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.6.i.i" .and 64 (.reg "%sub.6.i.i") (.reg "%and.5.i.i"),
      .binop "%sub.7.i.i" .add 64 (.reg "%and.6.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and.7.i.i" .and 64 (.reg "%sub.7.i.i") (.reg "%and.6.i.i"),
      .icmp "%tobool6.not42.i.i" .eq 64 (.reg "%and.7.i.i") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
    ],
    term := .condbr (.reg "%tobool6.not42.i.i") "xl_emit.exit" "while.body.preheader.i.i" },
  { name := "while.body.preheader.i.i",
    instrs := [
      .gep "%add.ptr5.i.i" (.int 8) (.reg "%add.ptr.i.i") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
    ],
    term := .br "while.body.i.i" },
  { name := "while.body.i.i",
    instrs := [
      .phi "%o.044.i.i" (.ptr) [("while.body.i.i", .reg "%add.ptr8.i.i"), ("while.body.preheader.i.i", .reg "%add.ptr5.i.i")],
      .phi "%c.143.i.i" (.int 64) [("while.body.i.i", .reg "%and18.7.i.i"), ("while.body.preheader.i.i", .reg "%and.7.i.i")],
      .call "%call7.i.i" (.int 32) "xl_batch" [(.int 64, .reg "%c.143.i.i"), (.int 32, .reg "%conv"), (.ptr, .reg "%o.044.i.i")],
      .zext "%idx.ext.i.i" 32 64 (.reg "%call7.i.i"),
      .load "%13" (.int 64) (.reg "%xn"),
      .binop "%add10.i.i" .add 64 (.reg "%13") (.reg "%idx.ext.i.i"),
      .store (.int 64) (.reg "%add10.i.i") (.reg "%xn"),
      .binop "%sub17.i.i" .add 64 (.reg "%c.143.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.i.i" .and 64 (.reg "%sub17.i.i") (.reg "%c.143.i.i"),
      .binop "%sub17.1.i.i" .add 64 (.reg "%and18.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.1.i.i" .and 64 (.reg "%sub17.1.i.i") (.reg "%and18.i.i"),
      .binop "%sub17.2.i.i" .add 64 (.reg "%and18.1.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.2.i.i" .and 64 (.reg "%sub17.2.i.i") (.reg "%and18.1.i.i"),
      .binop "%sub17.3.i.i" .add 64 (.reg "%and18.2.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.3.i.i" .and 64 (.reg "%sub17.3.i.i") (.reg "%and18.2.i.i"),
      .binop "%sub17.4.i.i" .add 64 (.reg "%and18.3.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.4.i.i" .and 64 (.reg "%sub17.4.i.i") (.reg "%and18.3.i.i"),
      .binop "%sub17.5.i.i" .add 64 (.reg "%and18.4.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.5.i.i" .and 64 (.reg "%sub17.5.i.i") (.reg "%and18.4.i.i"),
      .binop "%sub17.6.i.i" .add 64 (.reg "%and18.5.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.6.i.i" .and 64 (.reg "%sub17.6.i.i") (.reg "%and18.5.i.i"),
      .binop "%sub17.7.i.i" .add 64 (.reg "%and18.6.i.i") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and18.7.i.i" .and 64 (.reg "%sub17.7.i.i") (.reg "%and18.6.i.i"),
      .gep "%add.ptr8.i.i" (.int 32) (.reg "%o.044.i.i") (.reg "%idx.ext.i.i"),
      .icmp "%tobool6.not.i.i" .eq 64 (.reg "%and18.7.i.i") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
    ],
    term := .condbr (.reg "%tobool6.not.i.i") "xl_emit.exit" "while.body.i.i" },
  { name := "xl_emit.exit",
    instrs := [

    ],
    term := .ret (.void) none }] }

/-- `@leanllvm_json_escape_expand` — the expander's entry point.

One instruction: the call to `@us_dec_x`, whose nine parameters are the eight the
ABI names and the escape table the rewrite appends. -/
def escapeExpandFunction : Function :=
{ name := "leanllvm_json_escape_expand",
  retTy := .int 64,
  params := [("%b", .ptr), ("%n", .int 64), ("%dst", .ptr), ("%err", .ptr), ("%xp", .ptr), ("%xj", .ptr), ("%nxp", .int 64), ("%pos0", .int 64), ("%tab", .ptr)],
  blocks := [
  { name := "entry",
    instrs := [
      .call "%call" (.int 64) "us_dec_x" [(.ptr, .reg "%b"), (.int 64, .reg "%n"), (.ptr, .reg "%dst"), (.ptr, .reg "%err"), (.ptr, .reg "%xp"), (.ptr, .reg "%xj"), (.int 64, .reg "%nxp"), (.int 64, .reg "%pos0"), (.ptr, .reg "%tab")],
    ],
    term := .ret (.int 64) (some (.reg "%call")) }] }

/-- `@us_dec_x` — the decoder the expander calls.

Twenty-nine blocks and both copy shapes: the position-driven walk (skip to the
first position at or past `pos0`, copy to it, read the escape byte, decode `\u`
through the two multiply-adds, or refuse) and the two `us_run` copies that move
the rest of the body in whole vectors.  The ninth parameter is the rewritten table
base. -/
def usDecFunction : Function :=
{ name := "us_dec_x",
  retTy := .int 64,
  params := [("%p", .ptr), ("%n", .int 64), ("%dst", .ptr), ("%err", .ptr), ("%xp", .ptr), ("%xj", .ptr), ("%nxp", .int 64), ("%pos0", .int 64), ("%tab", .ptr)],
  blocks := [
  { name := "entry",
    instrs := [
      .load "%0" (.int 64) (.reg "%xj"),
      .binop "%add" .add 64 (.reg "%pos0") (.reg "%n"),
      .icmp "%cmp286" .ult 64 (.reg "%0") (.reg "%nxp"),
    ],
    term := .condbr (.reg "%cmp286") "land.rhs" "while.end" },
  { name := "land.rhs",
    instrs := [
      .phi "%k.0287" (.int 64) [("while.body", .reg "%inc"), ("entry", .reg "%0")],
      .gep "%arrayidx" (.int 32) (.reg "%xp") (.reg "%k.0287"),
      .load "%1" (.int 32) (.reg "%arrayidx"),
      .zext "%conv" 32 64 (.reg "%1"),
      .icmp "%cmp1" .ugt 64 (.reg "%pos0") (.reg "%conv"),
    ],
    term := .condbr (.reg "%cmp1") "while.body" "while.end" },
  { name := "while.body",
    instrs := [
      .binop "%inc" .add 64 (.reg "%k.0287") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .icmp "%exitcond.not" .eq 64 (.reg "%inc") (.reg "%nxp"),
    ],
    term := .condbr (.reg "%exitcond.not") "while.end35" "land.rhs" },
  { name := "while.end",
    instrs := [
      .phi "%k.0.lcssa" (.int 64) [("entry", .reg "%0"), ("land.rhs", .reg "%k.0287")],
      .icmp "%cmp4293" .ult 64 (.reg "%k.0.lcssa") (.reg "%nxp"),
    ],
    term := .condbr (.reg "%cmp4293") "while.body6" "while.end35" },
  { name := "while.body6",
    instrs := [
      .phi "%k.1296" (.int 64) [("cleanup32", .reg "%add28"), ("while.end", .reg "%k.0.lcssa")],
      .phi "%i.0295" (.int 64) [("cleanup32", .reg "%add24"), ("while.end", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .phi "%j.0294" (.int 64) [("cleanup32", .reg "%j.3"), ("while.end", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .gep "%arrayidx7" (.int 32) (.reg "%xp") (.reg "%k.1296"),
      .load "%2" (.int 32) (.reg "%arrayidx7"),
      .zext "%conv8" 32 64 (.reg "%2"),
      .icmp "%cmp9.not" .ugt 64 (.reg "%add") (.reg "%conv8"),
    ],
    term := .condbr (.reg "%cmp9.not") "if.end" "while.end35" },
  { name := "if.end",
    instrs := [
      .binop "%inc11" .add 64 (.reg "%k.1296") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .binop "%sub" .sub 64 (.reg "%conv8") (.reg "%pos0"),
      .gep "%add.ptr" (.int 8) (.reg "%p") (.reg "%i.0295"),
      .gep "%add.ptr12" (.int 8) (.reg "%dst") (.reg "%j.0294"),
      .binop "%sub13" .sub 64 (.reg "%sub") (.reg "%i.0295"),
      .icmp "%cmp.i88289" .ugt 64 (.reg "%sub13") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
    ],
    term := .condbr (.reg "%cmp.i88289") "while.body.i91" "us_run_long.exit99" },
  { name := "while.body.i91",
    instrs := [
      .phi "%k.0.i86290" (.int 64) [("while.body.i91", .reg "%add.i98"), ("if.end", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .gep "%add.ptr.i92" (.int 8) (.reg "%add.ptr12") (.reg "%k.0.i86290"),
      .gep "%add.ptr1.i93" (.int 8) (.reg "%add.ptr") (.reg "%k.0.i86290"),
      .load "%3" (.vec 4 (.int 64)) (.reg "%add.ptr1.i93"),
      .store (.vec 4 (.int 64)) (.reg "%3") (.reg "%add.ptr.i92"),
      .gep "%add.ptr3.i95" (.int 8) (.reg "%add.ptr.i92") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .gep "%add.ptr5.i96" (.int 8) (.reg "%add.ptr1.i93") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .load "%4" (.vec 4 (.int 64)) (.reg "%add.ptr5.i96"),
      .store (.vec 4 (.int 64)) (.reg "%4") (.reg "%add.ptr3.i95"),
      .binop "%add.i98" .add 64 (.reg "%k.0.i86290") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
      .binop "%sub.i87" .sub 64 (.reg "%sub13") (.reg "%add.i98"),
      .icmp "%cmp.i88" .ugt 64 (.reg "%sub.i87") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
    ],
    term := .condbr (.reg "%cmp.i88") "while.body.i91" "us_run_long.exit99" },
  { name := "us_run_long.exit99",
    instrs := [
      .phi "%k.0.i86.lcssa" (.int 64) [("if.end", .imm (.int 64 (BitVec.ofInt 64 (0)))), ("while.body.i91", .reg "%add.i98")],
      .phi "%sub.i87.lcssa" (.int 64) [("if.end", .reg "%sub13"), ("while.body.i91", .reg "%sub.i87")],
      .gep "%add.ptr7.i89" (.int 8) (.reg "%add.ptr") (.reg "%k.0.i86.lcssa"),
      .gep "%add.ptr8.i90" (.int 8) (.reg "%add.ptr12") (.reg "%k.0.i86.lcssa"),
      .load "%5" (.vec 4 (.int 64)) (.reg "%add.ptr7.i89"),
      .store (.vec 4 (.int 64)) (.reg "%5") (.reg "%add.ptr8.i90"),
      .icmp "%cmp.i102" .ugt 64 (.reg "%sub.i87.lcssa") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
    ],
    term := .condbr (.reg "%cmp.i102") "if.then.i104" "us_run.exit" },
  { name := "if.then.i104",
    instrs := [
      .gep "%add.ptr.i105" (.int 8) (.reg "%add.ptr8.i90") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .gep "%add.ptr1.i106" (.int 8) (.reg "%add.ptr7.i89") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .load "%6" (.vec 4 (.int 64)) (.reg "%add.ptr1.i106"),
      .store (.vec 4 (.int 64)) (.reg "%6") (.reg "%add.ptr.i105"),
    ],
    term := .br "us_run.exit" },
  { name := "us_run.exit",
    instrs := [
      .binop "%add15" .add 64 (.reg "%sub13") (.reg "%j.0294"),
      .gep "%arrayidx16" (.int 8) (.reg "%p") (.reg "%sub"),
      .load "%7" (.int 8) (.reg "%arrayidx16"),
      .icmp "%cmp18" .ult 8 (.reg "%7") (.imm (.int 8 (BitVec.ofInt 8 (32)))),
    ],
    term := .condbr (.reg "%cmp18") "if.then20" "if.end21" },
  { name := "if.then20",
    instrs := [
      .store (.int 64) (.reg "%sub") (.reg "%err"),
      .store (.int 64) (.reg "%inc11") (.reg "%xj"),
    ],
    term := .br "cleanup41" },
  { name := "if.end21",
    instrs := [
      .binop "%add.i100" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .icmp "%cmp.not.i" .ult 64 (.reg "%add.i100") (.reg "%n"),
    ],
    term := .condbr (.reg "%cmp.not.i") "if.end.i" "if.then22" },
  { name := "if.end.i",
    instrs := [
      .gep "%arrayidx.i" (.int 8) (.reg "%p") (.reg "%add.i100"),
      .load "%8" (.int 8) (.reg "%arrayidx.i"),
      .zext "%idxprom.i" 8 64 (.reg "%8"),
      .gep "%arrayidx2.i" (.int 8) (.reg "%tab") (.reg "%idxprom.i"),
      .load "%9" (.int 8) (.reg "%arrayidx2.i"),
      .icmp "%cmp4.i" .sgt 8 (.reg "%9") (.imm (.int 8 (BitVec.ofInt 8 (-1)))),
    ],
    term := .condbr (.reg "%cmp4.i") "if.then6.i" "if.end9.i" },
  { name := "if.then6.i",
    instrs := [
      .gep "%arrayidx7.i" (.int 8) (.reg "%dst") (.reg "%add15"),
      .store (.int 8) (.reg "%9") (.reg "%arrayidx7.i"),
      .binop "%add8.i" .add 64 (.reg "%add15") (.imm (.int 64 (BitVec.ofInt 64 (1)))),
    ],
    term := .br "cleanup32" },
  { name := "if.end9.i",
    instrs := [
      .icmp "%cmp10.not.i" .ne 8 (.reg "%8") (.imm (.int 8 (BitVec.ofInt 8 (117)))),
      .binop "%add.i113" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 (6)))),
      .icmp "%cmp.i114" .ugt 64 (.reg "%add.i113") (.reg "%n"),
      .binop "%or.cond335" .or 1 (.reg "%cmp10.not.i") (.reg "%cmp.i114"),
    ],
    term := .condbr (.reg "%or.cond335") "if.then22" "if.end.i115" },
  { name := "if.end.i115",
    instrs := [
      .gep "%add.ptr1.i117" (.int 8) (.reg "%arrayidx16") (.imm (.int 64 (BitVec.ofInt 64 (2)))),
      .load "%10" (.vec 2 (.int 64)) (.reg "%add.ptr1.i117"),
      .vecBitcast "%11" 2 64 16 8 (.reg "%10"),
      .binopVec "%sub.i169" .add 16 8 (.reg "%11") (.imm (.splat 16 8 (BitVec.ofInt 8 (-48)))),
      .binopVec "%12" .or 16 8 (.reg "%11") (.imm (.splat 16 8 (BitVec.ofInt 8 (32)))),
      .binopVec "%sub.i168" .add 16 8 (.reg "%12") (.imm (.splat 16 8 (BitVec.ofInt 8 (-97)))),
      .icmpVec "%cmp.i192" .ult 16 8 (.reg "%sub.i169") (.imm (.splat 16 8 (BitVec.ofInt 8 (10)))),
      .icmpVec "%cmp.i190" .ult 16 8 (.reg "%sub.i168") (.imm (.splat 16 8 (BitVec.ofInt 8 (6)))),
      .binopVec "%or.i185258259" .or 16 1 (.reg "%cmp.i192") (.reg "%cmp.i190"),
      .bitcastMask "%13" 16 (.reg "%or.i185258259"),
      .binop "%14" .and 16 (.reg "%13") (.imm (.int 16 (BitVec.ofInt 16 (15)))),
      .icmp "%cmp.not.i128" .eq 16 (.reg "%14") (.imm (.int 16 (BitVec.ofInt 16 (15)))),
    ],
    term := .condbr (.reg "%cmp.not.i128") "if.end3.i" "if.then22" },
  { name := "if.end3.i",
    instrs := [
      .vecBitcast "%bc318" 2 64 16 8 (.reg "%10"),
      .extractelement "%15" 16 8 (.reg "%bc318") (.imm (.int 64 (BitVec.ofInt 64 (5)))),
      .vecBitcast "%bc" 2 64 16 8 (.reg "%10"),
      .extractelement "%16" 16 8 (.reg "%bc") (.imm (.int 64 (BitVec.ofInt 64 (4)))),
      .binopVec "%17" .and 16 8 (.reg "%11") (.imm (.vector 8 [(BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])),
      .select "%18" (.vec 16 (.int 8)) (.reg "%cmp.i190") (.imm (.vector 8 [(BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])) (.imm (.vector 8 [(BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])),
      .binopVec "%add.i202" .add 16 8 (.reg "%18") (.reg "%17"),
      .call "%19" (.vec 8 (.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128" [(.vec 16 (.int 8), .reg "%add.i202"), (.vec 16 (.int 8), .imm (.vector 8 [(BitVec.ofInt 8 (16)), (BitVec.ofInt 8 (1)), (BitVec.ofInt 8 (16)), (BitVec.ofInt 8 (1)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))]))],
      .call "%20" (.vec 4 (.int 32)) "llvm.x86.sse2.pmadd.wd" [(.vec 8 (.int 16), .reg "%19"), (.vec 8 (.int 16), .imm (.vector 16 [(BitVec.ofInt 16 (256)), (BitVec.ofInt 16 (1)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0))]))],
      .extractelement "%vecext.i207" 4 32 (.reg "%20") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
      .binop "%and27.i" .and 32 (.reg "%vecext.i207") (.imm (.int 32 (BitVec.ofInt 32 (65535)))),
      .binop "%21" .and 32 (.reg "%vecext.i207") (.imm (.int 32 (BitVec.ofInt 32 (64512)))),
      .icmp "%cmp4.i118" .eq 32 (.reg "%21") (.imm (.int 32 (BitVec.ofInt 32 (55296)))),
      .binop "%add5.i" .add 64 (.reg "%sub") (.imm (.int 64 (BitVec.ofInt 64 (12)))),
      .icmp "%cmp6.not.i" .ule 64 (.reg "%add5.i") (.reg "%n"),
      .binop "%or.cond.i.not336" .and 1 (.reg "%cmp6.not.i") (.reg "%cmp4.i118"),
      .icmp "%cmp9.i" .eq 8 (.reg "%16") (.imm (.int 8 (BitVec.ofInt 8 (92)))),
      .binop "%or.cond" .and 1 (.reg "%or.cond.i.not336") (.reg "%cmp9.i"),
      .icmp "%cmp15.i" .eq 8 (.reg "%15") (.imm (.int 8 (BitVec.ofInt 8 (117)))),
      .binop "%or.cond334" .and 1 (.reg "%or.cond") (.reg "%cmp15.i"),
    ],
    term := .condbr (.reg "%or.cond334") "if.then17.i" "if.end32.i" },
  { name := "if.then17.i",
    instrs := [
      .gep "%add.ptr19.i" (.int 8) (.reg "%arrayidx16") (.imm (.int 64 (BitVec.ofInt 64 (8)))),
      .load "%22" (.vec 16 (.int 8)) (.reg "%add.ptr19.i"),
      .binopVec "%sub.i167" .add 16 8 (.reg "%22") (.imm (.splat 16 8 (BitVec.ofInt 8 (-48)))),
      .binopVec "%23" .or 16 8 (.reg "%22") (.imm (.splat 16 8 (BitVec.ofInt 8 (32)))),
      .binopVec "%sub.i166" .add 16 8 (.reg "%23") (.imm (.splat 16 8 (BitVec.ofInt 8 (-97)))),
      .icmpVec "%cmp.i188" .ult 16 8 (.reg "%sub.i167") (.imm (.splat 16 8 (BitVec.ofInt 8 (10)))),
      .icmpVec "%cmp.i187" .ult 16 8 (.reg "%sub.i166") (.imm (.splat 16 8 (BitVec.ofInt 8 (6)))),
      .binopVec "%or.i260261" .or 16 1 (.reg "%cmp.i188") (.reg "%cmp.i187"),
      .bitcastMask "%24" 16 (.reg "%or.i260261"),
      .binop "%25" .and 16 (.reg "%24") (.imm (.int 16 (BitVec.ofInt 16 (15)))),
      .icmp "%cmp.not.i150" .eq 16 (.reg "%25") (.imm (.int 16 (BitVec.ofInt 16 (15)))),
    ],
    term := .condbr (.reg "%cmp.not.i150") "land.lhs.true22.i" "if.end32.i" },
  { name := "land.lhs.true22.i",
    instrs := [
      .binopVec "%26" .and 16 8 (.reg "%22") (.imm (.vector 8 [(BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (15)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])),
      .select "%27" (.vec 16 (.int 8)) (.reg "%cmp.i187") (.imm (.vector 8 [(BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (9)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])) (.imm (.vector 8 [(BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))])),
      .binopVec "%add.i201" .add 16 8 (.reg "%27") (.reg "%26"),
      .call "%28" (.vec 8 (.int 16)) "llvm.x86.ssse3.pmadd.ub.sw.128" [(.vec 16 (.int 8), .reg "%add.i201"), (.vec 16 (.int 8), .imm (.vector 8 [(BitVec.ofInt 8 (16)), (BitVec.ofInt 8 (1)), (BitVec.ofInt 8 (16)), (BitVec.ofInt 8 (1)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0)), (BitVec.ofInt 8 (0))]))],
      .call "%29" (.vec 4 (.int 32)) "llvm.x86.sse2.pmadd.wd" [(.vec 8 (.int 16), .reg "%28"), (.vec 8 (.int 16), .imm (.vector 16 [(BitVec.ofInt 16 (256)), (BitVec.ofInt 16 (1)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0)), (BitVec.ofInt 16 (0))]))],
      .extractelement "%vecext.i" 4 32 (.reg "%29") (.imm (.int 64 (BitVec.ofInt 64 (0)))),
      .binop "%and27.i164" .and 32 (.reg "%vecext.i") (.imm (.int 32 (BitVec.ofInt 32 (65535)))),
      .binop "%sub23.i" .add 32 (.reg "%and27.i164") (.imm (.int 32 (BitVec.ofInt 32 (-56320)))),
      .icmp "%cmp24.i" .ult 32 (.reg "%sub23.i") (.imm (.int 32 (BitVec.ofInt 32 (1024)))),
    ],
    term := .condbr (.reg "%cmp24.i") "if.then26.i" "if.end32.i" },
  { name := "if.then26.i",
    instrs := [
      .binop "%sub27.i" .shl 32 (.reg "%and27.i") (.imm (.int 32 (BitVec.ofInt 32 (10)))),
      .binop "%add28.i" .add 32 (.reg "%sub27.i") (.imm (.int 32 (BitVec.ofInt 32 (-56557568)))),
      .binop "%add30.i" .or 32 (.reg "%sub23.i") (.reg "%add28.i"),
    ],
    term := .br "if.end32.i" },
  { name := "if.end32.i",
    instrs := [
      .phi "%cp.i.3" (.int 32) [("if.end3.i", .reg "%and27.i"), ("if.then26.i", .reg "%add30.i"), ("land.lhs.true22.i", .reg "%and27.i"), ("if.then17.i", .reg "%and27.i")],
      .phi "%adv.1.i" (.int 64) [("if.end3.i", .imm (.int 64 (BitVec.ofInt 64 (6)))), ("if.then26.i", .imm (.int 64 (BitVec.ofInt 64 (12)))), ("land.lhs.true22.i", .imm (.int 64 (BitVec.ofInt 64 (6)))), ("if.then17.i", .imm (.int 64 (BitVec.ofInt 64 (6))))],
      .binop "%shr.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (6)))),
      .binop "%and.i208" .and 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (63)))),
      .binop "%or1.i" .or 32 (.reg "%and.i208") (.imm (.int 32 (BitVec.ofInt 32 (128)))),
      .binop "%shl.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
      .binop "%or.i209" .or 32 (.reg "%shr.i") (.reg "%shl.i"),
      .binop "%or2.i" .or 32 (.reg "%or.i209") (.imm (.int 32 (BitVec.ofInt 32 (192)))),
      .binop "%shr3.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (12)))),
      .binop "%and6.i" .and 32 (.reg "%shr.i") (.imm (.int 32 (BitVec.ofInt 32 (63)))),
      .binop "%or7.i" .or 32 (.reg "%and6.i") (.imm (.int 32 (BitVec.ofInt 32 (128)))),
      .binop "%shl8.i" .shl 32 (.reg "%or7.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
      .binop "%shl12.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (16)))),
      .binop "%30" .or 32 (.reg "%shl8.i") (.reg "%shl12.i"),
      .binop "%or9.i" .or 32 (.reg "%shr3.i") (.reg "%30"),
      .binop "%or13.i" .or 32 (.reg "%or9.i") (.imm (.int 32 (BitVec.ofInt 32 (224)))),
      .binop "%shr14.i" .lshr 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (18)))),
      .binop "%and17.i" .shl 32 (.reg "%shr3.i") (.imm (.int 32 (BitVec.ofInt 32 (8)))),
      .binop "%or18.i" .and 32 (.reg "%and17.i") (.imm (.int 32 (BitVec.ofInt 32 (16128)))),
      .binop "%shl19.i" .or 32 (.reg "%shr14.i") (.reg "%or18.i"),
      .binop "%shl24.i" .shl 32 (.reg "%or7.i") (.imm (.int 32 (BitVec.ofInt 32 (16)))),
      .binop "%or20.i" .or 32 (.reg "%shl19.i") (.reg "%shl24.i"),
      .binop "%shl28.i" .shl 32 (.reg "%or1.i") (.imm (.int 32 (BitVec.ofInt 32 (24)))),
      .binop "%or25.i" .or 32 (.reg "%or20.i") (.reg "%shl28.i"),
      .binop "%or29.i" .or 32 (.reg "%or25.i") (.imm (.int 32 (BitVec.ofInt 32 (33008)))),
      .icmp "%cmp.i210" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (127)))),
      .icmp "%cmp30.i" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (2047)))),
      .zext "%conv31.i" 1 64 (.reg "%cmp30.i"),
      .icmp "%cmp32.i" .ugt 32 (.reg "%cp.i.3") (.imm (.int 32 (BitVec.ofInt 32 (65535)))),
      .zext "%conv33.i" 1 64 (.reg "%cmp32.i"),
      .select "%cond.i" (.int 32) (.reg "%cmp.i210") (.reg "%or2.i") (.reg "%cp.i.3"),
      .select "%cond38.i" (.int 32) (.reg "%cmp30.i") (.reg "%or13.i") (.reg "%cond.i"),
      .select "%cond43.i" (.int 32) (.reg "%cmp32.i") (.reg "%or29.i") (.reg "%cond38.i"),
      .select "%add.i211" (.int 64) (.reg "%cmp.i210") (.imm (.int 64 (BitVec.ofInt 64 (2)))) (.imm (.int 64 (BitVec.ofInt 64 (1)))),
      .gep "%add.ptr.i124" (.int 8) (.reg "%dst") (.reg "%add15"),
      .store (.int 32) (.reg "%cond43.i") (.reg "%add.ptr.i124"),
      .binop "%add44.i" .add 64 (.reg "%add15") (.reg "%conv31.i"),
      .binop "%add45.i" .add 64 (.reg "%add44.i") (.reg "%add.i211"),
      .binop "%add.i125" .add 64 (.reg "%add45.i") (.reg "%conv33.i"),
    ],
    term := .br "cleanup32" },
  { name := "if.then22",
    instrs := [
      .store (.int 64) (.reg "%sub") (.reg "%err"),
      .store (.int 64) (.reg "%inc11") (.reg "%xj"),
    ],
    term := .br "cleanup41" },
  { name := "cleanup32",
    instrs := [
      .phi "%j.3" (.int 64) [("if.then6.i", .reg "%add8.i"), ("if.end32.i", .reg "%add.i125")],
      .phi "%adv.2" (.int 64) [("if.then6.i", .imm (.int 64 (BitVec.ofInt 64 (2)))), ("if.end32.i", .reg "%adv.1.i")],
      .binop "%add24" .add 64 (.reg "%adv.2") (.reg "%sub"),
      .icmp "%cmp25" .eq 64 (.reg "%adv.2") (.imm (.int 64 (BitVec.ofInt 64 (12)))),
      .zext "%conv27" 1 64 (.reg "%cmp25"),
      .binop "%add28" .add 64 (.reg "%inc11") (.reg "%conv27"),
      .icmp "%cmp4" .ult 64 (.reg "%add28") (.reg "%nxp"),
    ],
    term := .condbr (.reg "%cmp4") "while.body6" "while.end35" },
  { name := "while.end35",
    instrs := [
      .phi "%j.0.lcssa" (.int 64) [("while.end", .imm (.int 64 (BitVec.ofInt 64 (0)))), ("while.body6", .reg "%j.0294"), ("cleanup32", .reg "%j.3"), ("while.body", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .phi "%i.0.lcssa" (.int 64) [("while.end", .imm (.int 64 (BitVec.ofInt 64 (0)))), ("while.body6", .reg "%i.0295"), ("cleanup32", .reg "%add24"), ("while.body", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .phi "%k.1.lcssa" (.int 64) [("while.end", .reg "%k.0.lcssa"), ("while.body6", .reg "%k.1296"), ("cleanup32", .reg "%add28"), ("while.body", .reg "%nxp")],
      .gep "%add.ptr36" (.int 8) (.reg "%p") (.reg "%i.0.lcssa"),
      .gep "%add.ptr37" (.int 8) (.reg "%dst") (.reg "%j.0.lcssa"),
      .binop "%sub38" .sub 64 (.reg "%n") (.reg "%i.0.lcssa"),
      .icmp "%cmp.i303" .ugt 64 (.reg "%sub38") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
    ],
    term := .condbr (.reg "%cmp.i303") "while.body.i" "us_run_long.exit" },
  { name := "while.body.i",
    instrs := [
      .phi "%k.0.i304" (.int 64) [("while.body.i", .reg "%add.i"), ("while.end35", .imm (.int 64 (BitVec.ofInt 64 (0))))],
      .gep "%add.ptr.i" (.int 8) (.reg "%add.ptr37") (.reg "%k.0.i304"),
      .gep "%add.ptr1.i" (.int 8) (.reg "%add.ptr36") (.reg "%k.0.i304"),
      .load "%31" (.vec 4 (.int 64)) (.reg "%add.ptr1.i"),
      .store (.vec 4 (.int 64)) (.reg "%31") (.reg "%add.ptr.i"),
      .gep "%add.ptr3.i" (.int 8) (.reg "%add.ptr.i") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .gep "%add.ptr5.i" (.int 8) (.reg "%add.ptr1.i") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .load "%32" (.vec 4 (.int 64)) (.reg "%add.ptr5.i"),
      .store (.vec 4 (.int 64)) (.reg "%32") (.reg "%add.ptr3.i"),
      .binop "%add.i" .add 64 (.reg "%k.0.i304") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
      .binop "%sub.i" .sub 64 (.reg "%sub38") (.reg "%add.i"),
      .icmp "%cmp.i" .ugt 64 (.reg "%sub.i") (.imm (.int 64 (BitVec.ofInt 64 (64)))),
    ],
    term := .condbr (.reg "%cmp.i") "while.body.i" "us_run_long.exit" },
  { name := "us_run_long.exit",
    instrs := [
      .phi "%k.0.i.lcssa" (.int 64) [("while.end35", .imm (.int 64 (BitVec.ofInt 64 (0)))), ("while.body.i", .reg "%add.i")],
      .phi "%sub.i.lcssa" (.int 64) [("while.end35", .reg "%sub38"), ("while.body.i", .reg "%sub.i")],
      .gep "%add.ptr7.i" (.int 8) (.reg "%add.ptr36") (.reg "%k.0.i.lcssa"),
      .gep "%add.ptr8.i" (.int 8) (.reg "%add.ptr37") (.reg "%k.0.i.lcssa"),
      .load "%33" (.vec 4 (.int 64)) (.reg "%add.ptr7.i"),
      .store (.vec 4 (.int 64)) (.reg "%33") (.reg "%add.ptr8.i"),
      .icmp "%cmp.i107" .ugt 64 (.reg "%sub.i.lcssa") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
    ],
    term := .condbr (.reg "%cmp.i107") "if.then.i109" "us_run.exit112" },
  { name := "if.then.i109",
    instrs := [
      .gep "%add.ptr.i110" (.int 8) (.reg "%add.ptr8.i") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .gep "%add.ptr1.i111" (.int 8) (.reg "%add.ptr7.i") (.imm (.int 64 (BitVec.ofInt 64 (32)))),
      .load "%34" (.vec 4 (.int 64)) (.reg "%add.ptr1.i111"),
      .store (.vec 4 (.int 64)) (.reg "%34") (.reg "%add.ptr.i110"),
    ],
    term := .br "us_run.exit112" },
  { name := "us_run.exit112",
    instrs := [
      .store (.int 64) (.reg "%k.1.lcssa") (.reg "%xj"),
      .binop "%add40" .add 64 (.reg "%sub38") (.reg "%j.0.lcssa"),
    ],
    term := .br "cleanup41" },
  { name := "cleanup41",
    instrs := [
      .phi "%retval.4" (.int 64) [("us_run.exit112", .reg "%add40"), ("if.then20", .imm (.int 64 (BitVec.ofInt 64 (-1)))), ("if.then22", .imm (.int 64 (BitVec.ofInt 64 (-1))))],
    ],
    term := .ret (.int 64) (some (.reg "%retval.4")) }] }

/-- `@xl_batch` — the out-of-line batch the list hands its remaining set bits to.

One block: eight `cttz`-and-clear steps from the low lane, each storing
`base + lane` and advancing four bytes, and `min (ctpop esc) 8` as the count. -/
def xlBatchFunction : Function :=
{ name := "xl_batch",
  retTy := .int 32,
  params := [("%esc", .int 64), ("%base", .int 32), ("%o", .ptr)],
  blocks := [
  { name := "entry",
    instrs := [
      .binop "%or" .or 64 (.reg "%esc") (.imm (.int 64 (BitVec.ofInt 64 (-9223372036854775808)))),
      .call "%0" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%or"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast" 64 32 (.reg "%0"),
      .binop "%add" .add 32 (.reg "%base") (.reg "%cast"),
      .store (.int 32) (.reg "%add") (.reg "%o"),
      .binop "%sub" .add 64 (.reg "%or") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and" .and 64 (.reg "%sub") (.reg "%or"),
      .call "%1" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast1" 64 32 (.reg "%1"),
      .binop "%add2" .add 32 (.reg "%base") (.reg "%cast1"),
      .gep "%arrayidx3" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (4)))),
      .store (.int 32) (.reg "%add2") (.reg "%arrayidx3"),
      .binop "%sub4" .add 64 (.reg "%and") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and5" .and 64 (.reg "%sub4") (.reg "%and"),
      .call "%2" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and5"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast6" 64 32 (.reg "%2"),
      .binop "%add7" .add 32 (.reg "%base") (.reg "%cast6"),
      .gep "%arrayidx8" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (8)))),
      .store (.int 32) (.reg "%add7") (.reg "%arrayidx8"),
      .binop "%sub9" .add 64 (.reg "%and5") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and10" .and 64 (.reg "%sub9") (.reg "%and5"),
      .call "%3" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and10"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast11" 64 32 (.reg "%3"),
      .binop "%add12" .add 32 (.reg "%base") (.reg "%cast11"),
      .gep "%arrayidx13" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (12)))),
      .store (.int 32) (.reg "%add12") (.reg "%arrayidx13"),
      .binop "%sub14" .add 64 (.reg "%and10") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and15" .and 64 (.reg "%sub14") (.reg "%and10"),
      .call "%4" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and15"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast16" 64 32 (.reg "%4"),
      .binop "%add17" .add 32 (.reg "%base") (.reg "%cast16"),
      .gep "%arrayidx18" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (16)))),
      .store (.int 32) (.reg "%add17") (.reg "%arrayidx18"),
      .binop "%sub19" .add 64 (.reg "%and15") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and20" .and 64 (.reg "%sub19") (.reg "%and15"),
      .call "%5" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and20"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast21" 64 32 (.reg "%5"),
      .binop "%add22" .add 32 (.reg "%base") (.reg "%cast21"),
      .gep "%arrayidx23" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (20)))),
      .store (.int 32) (.reg "%add22") (.reg "%arrayidx23"),
      .binop "%sub24" .add 64 (.reg "%and20") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and25" .and 64 (.reg "%sub24") (.reg "%and20"),
      .call "%6" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and25"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast26" 64 32 (.reg "%6"),
      .binop "%add27" .add 32 (.reg "%base") (.reg "%cast26"),
      .gep "%arrayidx28" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (24)))),
      .store (.int 32) (.reg "%add27") (.reg "%arrayidx28"),
      .binop "%sub29" .add 64 (.reg "%and25") (.imm (.int 64 (BitVec.ofInt 64 (-1)))),
      .binop "%and30" .and 64 (.reg "%sub29") (.reg "%and25"),
      .call "%7" (.int 64) "llvm.cttz.i64" [(.int 64, .reg "%and30"), (.int 1, .imm (.int 1 (BitVec.ofInt 1 (-1))))],
      .trunc "%cast31" 64 32 (.reg "%7"),
      .binop "%add32" .add 32 (.reg "%base") (.reg "%cast31"),
      .gep "%arrayidx33" (.int 8) (.reg "%o") (.imm (.int 64 (BitVec.ofInt 64 (28)))),
      .store (.int 32) (.reg "%add32") (.reg "%arrayidx33"),
      .call "%8" (.int 64) "llvm.ctpop.i64" [(.int 64, .reg "%esc")],
      .trunc "%cast36" 64 32 (.reg "%8"),
      .call "%cond" (.int 32) "llvm.umin.i32" [(.int 32, .reg "%cast36"), (.int 32, .imm (.int 32 (BitVec.ofInt 32 (8))))],
    ],
    term := .ret (.int 32) (some (.reg "%cond")) }] }

/-! ### The pin -/

-- The fixture's four definitions, whole and in its order.  Every token the
-- parser models is compared: the pin is an equality of parsed functions, not of
-- a rendering.
#guard decide ((parseModule escapeSrc).toOption.map (fun m => m.functions) =
  some [escapeListFunction, escapeExpandFunction, usDecFunction, xlBatchFunction])

-- The entry-point lookup the list theorem runs at finds the pinned body.
#guard decide (firstFunction escapeSrc = some escapeListFunction)

-- The three ABIs.  The list's parameters are its record's argument names; the
-- expander's and the decoder's carry the rewritten table base as a ninth, which
-- is the one parameter the fragment's lack of module-level globals adds.
#guard
  match (parseModule escapeSrc).toOption with
  | some m =>
      m.functions.any (fun f => f.name = "leanllvm_json_escape_list" &&
        f.params.map (fun p => p.1) = ["%bs", "%ctl", "%im", "%blk0", "%xp", "%xn", "%carry"] &&
        f.retTy = Ty.void) &&
      m.functions.any (fun f => f.name = "leanllvm_json_escape_expand" &&
        f.params.map (fun p => p.1) = ["%b", "%n", "%dst", "%err", "%xp", "%xj", "%nxp",
          "%pos0", "%tab"] &&
        f.retTy = Ty.int 64) &&
      m.functions.any (fun f => f.name = "us_dec_x" &&
        f.params.map (fun p => p.1) = ["%p", "%n", "%dst", "%err", "%xp", "%xj", "%nxp",
          "%pos0", "%tab"] &&
        f.retTy = Ty.int 64) &&
      m.functions.any (fun f => f.name = "xl_batch" &&
        f.params.map (fun p => p.1) = ["%esc", "%base", "%o"] &&
        f.retTy = Ty.int 32)
  | none => false

-- The list: ten blocks, and the instruction line of each —
-- 9 + 5 + 13 + 5 + 11 + 63 + 17 + 1 + 25 + 0 = 149.
#guard escapeListFunction.blocks.length = 10
#guard escapeListFunction.blocks.map (fun b => b.instrs.length) =
  [9, 5, 13, 5, 11, 63, 17, 1, 25, 0]
#guard (escapeListFunction.blocks.map (fun b => b.instrs.length)).sum = 149

-- The expander's entry point: one block, one call.
#guard escapeExpandFunction.blocks.length = 1
#guard escapeExpandFunction.blocks.map (fun b => b.instrs.length) = [1]

-- The decoder: twenty-nine blocks, and the enumeration beside the sum —
-- 3 + 5 + 2 + 2 + 7 + 6 + 12 + 7 + 4 + 4 + 2 + 2 + 6 + 3 + 4 + 12 + 20 + 11 +
-- 9 + 3 + 39 + 2 + 7 + 7 + 12 + 7 + 4 + 2 + 1 = 205.
#guard usDecFunction.blocks.length = 29
#guard usDecFunction.blocks.map (fun b => b.instrs.length) =
  [3, 5, 2, 2, 7, 6, 12, 7, 4, 4, 2, 2, 6, 3, 4, 12, 20, 11, 9, 3, 39, 2, 7, 7, 12,
   7, 4, 2, 1]
#guard (usDecFunction.blocks.map (fun b => b.instrs.length)).sum = 205

-- The batch: one block, fifty-seven lines.
#guard xlBatchFunction.blocks.length = 1
#guard xlBatchFunction.blocks.map (fun b => b.instrs.length) = [57]

-- The four bodies together: 10 + 1 + 29 + 1 = 41 blocks and
-- 149 + 1 + 205 + 57 = 412 instruction lines.
#guard (escapeListFunction.blocks.length + escapeExpandFunction.blocks.length +
  usDecFunction.blocks.length + xlBatchFunction.blocks.length) = 41
#guard ((escapeListFunction.blocks.map (fun b => b.instrs.length)).sum +
  (escapeExpandFunction.blocks.map (fun b => b.instrs.length)).sum +
  (usDecFunction.blocks.map (fun b => b.instrs.length)).sum +
  (xlBatchFunction.blocks.map (fun b => b.instrs.length)).sum) = 412

/-! ### The environments the unit's own calls resolve in

`escapeCalls` binds the five intrinsic spellings and nothing else, so a call to a
**defined** body is `ub` at it — and the unit's two bodies each make one: the list
calls `@xl_batch` on every block with more than eight escape lanes, and the
expander's entry point calls `@us_dec_x`.  Each defined callee is resolved at its
own record, at `envForUnit`, which runs the body from the caller's memory and
allocator at that record's own budget; a fuel nested inside the call would make a
caller's budget depend on an inner one.

Each environment is a merge: the unit's intrinsics first, then the defined callee's
arm, and nothing else.  The two records are parameters, because a record and the
theorem that establishes it are one artefact and this module states neither.
-/

/-- The list's call environment: the unit's intrinsics, and `@xl_batch` at its own
record. -/
def escapeListCalls (Γ_batch : MemContract) : Calls :=
  fun callee args mem next =>
    match escapeCalls callee args mem next with
    | some r => some r
    | none =>
        envForUnit "xl_batch" Γ_batch escapeCalls xlBatchFunction callee args mem next

/-- The expander's call environment: the unit's intrinsics, and `@us_dec_x` at the
expander's own record.

The decoder's own run and the entry point's call to it read the same environment.
The decoder calls no defined body, so the second arm is unreachable from its run —
it is the arm the entry point's one instruction lands on. -/
def escapeExpandCalls (Γ_expand : MemContract) : Calls :=
  fun callee args mem next =>
    match escapeCalls callee args mem next with
    | some r => some r
    | none =>
        envForUnit "us_dec_x" Γ_expand escapeCalls usDecFunction callee args mem next

/-- The intrinsic environment resolves no defined symbol: `@xl_batch` is not one of
the five spellings, so the merge's second arm is the one a call to it lands on. -/
theorem escapeCalls_xlBatch (args : List Value) (mem : Mem) (next : Nat) :
    escapeCalls "xl_batch" args mem next = none := rfl

/-- The same for the decoder's symbol. -/
theorem escapeCalls_usDec_x (args : List Value) (mem : Mem) (next : Nat) :
    escapeCalls "us_dec_x" args mem next = none := rfl

/-- At an intrinsic spelling the list's environment is the intrinsic environment. -/
theorem escapeListCalls_intrinsic {Γ_batch : MemContract} {callee : String}
    {args : List Value} {mem : Mem} {next : Nat} {r : CallOutcome}
    (h : escapeCalls callee args mem next = some r) :
    escapeListCalls Γ_batch callee args mem next = some r := by
  simp only [escapeListCalls, h]

/-- At `@xl_batch` the list's environment is the batch's own arm. -/
theorem escapeListCalls_xlBatch (Γ_batch : MemContract) (args : List Value)
    (mem : Mem) (next : Nat) :
    escapeListCalls Γ_batch "xl_batch" args mem next =
      envForUnit "xl_batch" Γ_batch escapeCalls xlBatchFunction
        "xl_batch" args mem next := by
  simp only [escapeListCalls, escapeCalls_xlBatch]

/-- At an intrinsic spelling the expander's environment is the intrinsic
environment. -/
theorem escapeExpandCalls_intrinsic {Γ_expand : MemContract} {callee : String}
    {args : List Value} {mem : Mem} {next : Nat} {r : CallOutcome}
    (h : escapeCalls callee args mem next = some r) :
    escapeExpandCalls Γ_expand callee args mem next = some r := by
  simp only [escapeExpandCalls, h]

/-- At `@us_dec_x` the expander's environment is the decoder's own arm. -/
theorem escapeExpandCalls_usDec_x (Γ_expand : MemContract) (args : List Value)
    (mem : Mem) (next : Nat) :
    escapeExpandCalls Γ_expand "us_dec_x" args mem next =
      envForUnit "us_dec_x" Γ_expand escapeCalls usDecFunction
        "us_dec_x" args mem next := by
  simp only [escapeExpandCalls, escapeCalls_usDec_x]

/-! ### Axiom footprints -/

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeCalls_xlBatch' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_xlBatch

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeCalls_usDec_x' depends on axioms: [propext] -/
#guard_msgs in
#print axioms escapeCalls_usDec_x

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeListCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeListCalls

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeExpandCalls' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpandCalls

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeListCalls_intrinsic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeListCalls_intrinsic

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeExpandCalls_intrinsic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpandCalls_intrinsic

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeListCalls_xlBatch' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeListCalls_xlBatch

/-- info: 'LeanLLVM.Refinement.JsonEscapeIR.escapeExpandCalls_usDec_x' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms escapeExpandCalls_usDec_x

end LeanLLVM.Refinement.JsonEscapeIR
