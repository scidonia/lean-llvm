/-
Emit the memory-backed loop fixture from its Lean AST.

    nix develop -c bash -c 'lake exe leanllvm-loop-emit > probes/install/ir/loop.ll'

`probes/install/ir/capture.sh` runs the same command as part of the documented
fixture route.  The redirect has to be inside the shell the dev shell starts:
`nix develop -c lake exe leanllvm-loop-emit > file` would also capture the dev
shell's own startup banner, which is printed on the way in.

The text is the header comment below followed by `LeanLLVM.Function.render` of
`LeanLLVM.Vellum.CommaMaskLoop.loopFunction`, the AST that
`LeanLLVM/Vellum/CommaMaskLoop.lean` parses the file back to and proves the
correctness and framed-memory statements about.

This is the framework's printer rendering a Lean-defined function; no `lean -c`
C emission and no clang lowering is involved anywhere on this path.  What the
proofs pin is the textual IR: `LeanLLVM/Vellum/CommaMaskLoop.lean` parses this
file and proves its correctness and framed-memory statements about the AST that
results.  Nothing here certifies LLVM's lowering of that text, the object built
from it, or provenance from Lean's native compiler, and none of those is
claimed.

The function is inside the modelled subset, so the printer writes it as it
stands and nothing is removed or rewritten afterwards.  The emitter refuses to
print unless its own output parses back to the same function, so a construct or
attribute the parser does not model cannot reach the fixture silently.
-/
import LeanLLVM
import LeanLLVM.Vellum.CommaMaskLoopBody

open LeanLLVM

/-- The fixture's header: what the file is, how it is regenerated, and what it
is not. -/
def provenance : String :=
"; The comma mask as a memory-backed loop: counter and accumulator live in
; memory, the lane bit and test are computed from the counter, and the select
; folds the accumulator.  The loop is the control-flow-different counterpart of
; the unrolled candidate in candidate.ll.
;
; Emitted from LeanLLVM.Vellum.CommaMaskLoop.loopFunction -- the AST in
; LeanLLVM/Vellum/CommaMaskLoopBody.lean that
; LeanLLVM/Vellum/CommaMaskLoop.lean parses this file back to and proves its
; correctness and framed-memory statements about -- with
;
;   nix develop -c bash -c 'lake exe leanllvm-loop-emit > probes/install/ir/loop.ll'
;
; through LeanLLVM.Function.render, the framework's own printer.
; probes/install/ir/capture.sh runs the same command as part of the fixture
; route, with the redirect inside the shell so the dev shell's startup banner
; is not written here.
;
; This is not the output of Lean's native compiler: no `lean -c` C emission and
; no clang lowering is involved.  Nothing in the text below was removed or
; rewritten after rendering."

/-- Render `f`, refusing unless the text parses back to the same well-formed
function. -/
def emit (f : Function) : Except String String := do
  if !f.wf then
    throw s!"function @{f.name} is not well formed (unique block names, every branch target defined)"
  let text := Function.render f
  match parseModule text with
  | .error e => throw s!"the rendered function does not parse: {e}"
  | .ok m =>
      match m.functions with
      | [g] =>
          if g = f then pure text
          else throw s!"the rendered text parses to a different function than @{f.name}"
      | fs => throw s!"the rendered text parses to {fs.length} functions, not one"

def main : IO UInt32 := do
  match emit LeanLLVM.Vellum.CommaMaskLoop.loopFunction with
  | .error e =>
      IO.eprintln s!"leanllvm-loop-emit: {e}"
      return 1
  | .ok text =>
      IO.print (provenance ++ "\n" ++ text ++ "\n")
      return 0
