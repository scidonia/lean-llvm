/-
Emit the JSON seam's staging-caller fixture from its Lean AST.

    nix develop -c bash -c 'lake exe leanllvm-json-emit > probes/install/ir/json-caller.ll'

The redirect has to be inside the shell the dev shell starts:
`nix develop -c lake exe leanllvm-json-emit > file` would also capture the dev
shell's own startup banner, which is printed on the way in.

The text is the header comment below followed by `LeanLLVM.Module.render` of the
module holding the seam's declaration and `LeanLLVM.Refinement.JsonSeam.scanCaller`.
The module is not just the function: the fixture is checked with
`opt -passes=verify`, and LLVM refuses a call to a symbol the module does not
declare.  `LeanLLVM/Refinement/JsonSeam.lean` parses this file back and pins the
whole module, declaration included, with `#guard`.

This is the framework's printer rendering Lean-defined IR; no `lean -c` C
emission and no clang lowering is involved anywhere on this path.  What the
proofs pin is the textual IR: `JsonSeam.lean` parses this file and proves its
statements about the AST that results.  Nothing here certifies LLVM's lowering of
that text, the object built from it, or provenance from Lean's native compiler,
and none of those is claimed.

The emitter refuses to print unless its own output parses back to the same
module, so a construct or attribute the parser does not model cannot reach the
fixture silently.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonSeam

open LeanLLVM

/-- The fixture's header: what the file is, how it is regenerated, and what it
is not. -/
def provenance : String :=
"; The JSON seam's staging caller: four i64 words are staged into four locals
; from address 1, then the seam is called on the first local's address, and the
; i32 it returns is the caller's result.
;
; Emitted from LeanLLVM.Refinement.JsonSeam.scanCaller with
;
;   nix develop -c bash probes/install/lake-locked.sh exe leanllvm-json-emit > probes/install/ir/json-caller.ll
;
; through LeanLLVM.Module.render, the framework's own printer.  The module holds
; the seam's declaration and the caller's definition, because the fixture is
; checked with `opt -passes=verify` and LLVM refuses a call to an undeclared
; symbol.  LeanLLVM/Refinement/JsonSeam.lean parses this file back and pins the
; whole module, declaration included, with `#guard`.
;
; This is not the output of Lean's native compiler: no `lean -c` C emission and
; no clang lowering is involved.  Nothing in the text below was removed or
; rewritten after rendering."

/-- The seam's declaration: the symbol the caller calls and the linker resolves. -/
def seamDecl : Decl :=
  { name := LeanLLVM.Refinement.JsonSeam.jsonSeamSymbol, retTy := .int 32, params := [.ptr] }

/-- The module the fixture holds: the declaration, then the caller. -/
def callerModule : Module :=
  { decls := [seamDecl], functions := [LeanLLVM.Refinement.JsonSeam.scanCaller] }

/-- Render the module, refusing unless the text parses back to the same one. -/
def emit (m : Module) : Except String String := do
  let text := Module.render m
  match parseModule text with
  | .error e => throw s!"the rendered module does not parse: {e}"
  | .ok m' =>
      if m'.decls = m.decls ∧ m'.functions = m.functions then pure text
      else throw "the rendered text parses to a different module"

def main : IO UInt32 := do
  match emit callerModule with
  | .error e =>
      IO.eprintln s!"leanllvm-json-emit: {e}"
      return 1
  | .ok text =>
      IO.print (provenance ++ "\n" ++ text)
      return 0
