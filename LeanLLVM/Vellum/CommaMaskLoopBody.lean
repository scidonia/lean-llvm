/-
The memory-backed comma-mask loop as an AST.

This module is the one definition of the loop.  `lake exe leanllvm-loop-emit`
renders it with `LeanLLVM.Function.render` into
`probes/install/ir/loop.ll`, and `LeanLLVM/Vellum/CommaMaskLoop.lean` parses
that fixture at build time and pins it back to this AST before proving the
loop's correctness and framed-memory statements.

The definition lives here rather than in the proof module so that the emitter
does not depend on its own output: the proof module reads `loop.ll` through
`include_str`, which the kernel only pins when the module is elaborated, so a
change to the loop would otherwise have to be made by editing the fixture.

Every instruction below is inside the subset `LeanLLVM.Semantics` models, so the
printer emits the function as it stands; nothing is removed or rewritten on the
way to the fixture.
-/
import LeanLLVM.Vellum.CommaMaskIR

namespace LeanLLVM.Vellum.CommaMaskLoop

open LeanLLVM
open LeanLLVM.Vellum.CommaMaskIR

/-- The entry block's instructions: the comma-XOR word, the two locals the
loop keeps in memory, and their zero initialisers. -/
def entryInstrs : List Instr := [
  .binop "%m" .xor 64 (.reg "%arg") (lit 3182967604875373612),
  .alloca "%acc" (.int 64) 8,
  .alloca "%i" (.int 64) 8,
  .store (.int 64) (.imm (.int 64 0)) (.reg "%acc"),
  .store (.int 64) (.imm (.int 64 0)) (.reg "%i")]

/-- The condition block's instructions: load the counter and compare it with
the lane count. -/
def condInstrs : List Instr := [
  .load "%i1" (.int 64) (.reg "%i"),
  .icmp "%c" .ult 64 (.reg "%i1") (.imm (.int 64 8))]

/-- One iteration: the lane offset, the shifted lane byte, the zero test, the
accumulator round trip and the counter increment, both written back. -/
def bodyInstrs : List Instr := [
  .binop "%sh" .mul 64 (.reg "%i1") (.imm (.int 64 8)),
  .binop "%b" .lshr 64 (.reg "%m") (.reg "%sh"),
  .binop "%b2" .and 64 (.reg "%b") (.imm (.int 64 255)),
  .icmp "%z" .eq 64 (.reg "%b2") (.imm (.int 64 0)),
  .load "%a0" (.int 64) (.reg "%acc"),
  .binop "%bit" .shl 64 (.imm (.int 64 128)) (.reg "%sh"),
  .binop "%a1" .or 64 (.reg "%a0") (.reg "%bit"),
  .select "%a2" (.int 64) (.reg "%z") (.reg "%a1") (.reg "%a0"),
  .store (.int 64) (.reg "%a2") (.reg "%acc"),
  .binop "%i2" .add 64 (.reg "%i1") (.imm (.int 64 1)),
  .store (.int 64) (.reg "%i2") (.reg "%i")]

/-- The exit block's instructions: read the accumulator back. -/
def doneInstrs : List Instr := [
  .load "%r" (.int 64) (.reg "%acc")]

/-- The exit block. -/
def doneBlock : Block :=
  { name := "done", instrs := doneInstrs, term := .ret (.int 64) (some (.reg "%r")) }

/-- The body block. -/
def bodyBlock : Block :=
  { name := "body", instrs := bodyInstrs, term := .br "cond" }

/-- The condition block. -/
def condBody : Block :=
  { name := "cond", instrs := condInstrs, term := .condbr (.reg "%c") "body" "done" }

/-- The loop function the printer emits and the proof module parses back. -/
def loopFunction : Function :=
  { name := "leanllvm_comma_mask8", retTy := .int 64, params := [("%arg", .int 64)],
    blocks := [
      { name := "entry", instrs := entryInstrs, term := .br "cond" },
      condBody,
      bodyBlock,
      doneBlock] }

end LeanLLVM.Vellum.CommaMaskLoop
