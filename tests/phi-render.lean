/-
The printer's output for the two differential fixtures, on stdout, for
`tests/phi-differential.sh` to hand to `llvm-as`.

Each fixture is read from disk, parsed and printed by `Module.render`, so what
`llvm-as` assembles is the printer's text and not the file it came from.  The
two renders are separated by a line `--- phi-render ---` so the caller can split
them; nothing else is printed.

It asserts nothing itself: `llvm-as` is what decides whether the printed text is
assemblable IR.
-/
import LeanLLVM

open LeanLLVM

def render (path : String) : IO String := do
  let src ← IO.FS.readFile path
  match parseModule src with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok m => return Module.render m

def main : IO Unit := do
  let loop ← render "tests/phi/loop.ll"
  let three ← render "tests/phi/three.ll"
  IO.print loop
  IO.println "--- phi-render ---"
  IO.print three

#eval main
