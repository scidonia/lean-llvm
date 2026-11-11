/-
Emit the JSON window scanner's authored body from its Lean AST.

    nix develop -c bash -c 'lake exe leanllvm-json-scan-emit > probes/install/ir/json-scan-body.ll'

The redirect has to be inside the shell the dev shell starts:
`nix develop -c lake exe leanllvm-json-scan-emit > file` would also capture the
dev shell's own startup banner, which is printed on the way in.

The text is the header comment below followed by `LeanLLVM.Function.render` of
`LeanLLVM.Refinement.JsonScanBody.scanWindowBody`, the AST that
`LeanLLVM/Refinement/JsonScanIR.lean` parses the file back to and proves the
refinement statement about.

This is the framework's printer rendering a Lean-defined function; no `lean -c`
C emission and no clang lowering is involved anywhere on this path, and nothing
here certifies LLVM's lowering of the text or the object built from it.  The
captured AVX2 source in `probes/install/json/scan-window.candidate.c` and the
fixture its capture script writes are the algorithm's measured shape, not the
certified bytes: they are what the compiler made of the algorithm, and this is
the body the theorems are about.

The function is inside the modelled subset, so the printer writes it as it
stands and nothing is removed or rewritten afterwards.  The emitter refuses to
print unless its own output parses back to the same function, so a construct or
attribute the parser does not model cannot reach the fixture silently.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonScanBody

open LeanLLVM

/-- The fixture's header: what the file is, how it is regenerated, and what it
is not. -/
def provenance : String :=
"; The JSON window scanner as authored IR: the counter, the carry and the stop
; word live in memory, the per-lane rule is select-based, and the carry crosses
; the window's boundary in a 16-byte state slot.  A full window takes the vector
; path (one load of thirty-two bytes and the quote, backslash and b < 0x20 lane
; masks); a shorter window takes the same lane body with the byte's own
; predicates as its skip bits.
;
; Emitted from LeanLLVM.Refinement.JsonScanBody.scanWindowBody -- the AST in
; LeanLLVM/Refinement/JsonScanBody.lean that LeanLLVM/Refinement/JsonScanIR.lean parses
; this file back to -- with
;
;   nix develop -c bash -c 'lake exe leanllvm-json-scan-emit > probes/install/ir/json-scan-body.ll'
;
; through LeanLLVM.Function.render, the framework's own printer.
;
; The refinement statement about this text is not yet proved: LeanLLVM/Refinement/
; JsonScanIR.lean pins the text to the AST and proves the prefix facts the
; statement rests on, and its own header records what is outstanding.  Until
; that theorem exists, nothing here is certified, and the manifest must not
; name this fixture.
;
; This is not the output of Lean's native compiler and not the output of clang:
; no `lean -c` C emission and no clang lowering is involved, and nothing in the
; text below was removed or rewritten after rendering.  The AVX2 body in
; probes/install/json/scan-window.candidate.c, and the fixture its capture
; script writes, are the algorithm's source and its measured inventory; they are
; not this body and they are not certified."

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
  match emit LeanLLVM.Refinement.JsonScanBody.scanWindowBody with
  | .error e =>
      IO.eprintln s!"leanllvm-json-scan-emit: {e}"
      return 1
  | .ok text =>
      IO.print (provenance ++ "\n" ++ text ++ "\n")
      return 0
