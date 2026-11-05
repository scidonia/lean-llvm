/-
The model-side runner for the differential: it prints the model's answers for
`tests/phi-differential.sh`, which compares them with the answers a compiler
gives for the same files.

It is not a check in its own right and it asserts nothing — it has no `#guard`
and no expectation of its own.  Its only failure mode is a fixture that cannot be
read or parsed, which it reports by name; the comparison, and the verdict, live
in the shell script.

Each fixture is read from disk and parsed, so the text the model runs is the
text the compiler is given.  The output lines are `loop <value>` and
`three <argc=1> <argc=2> <argc=3> <argc=4>`, where a run that ends in `ub` or
without a returned value prints `ub`.  `loop` branches to itself and so re-enters its
`phi` block from a second predecessor; `three` reaches its `phi` from one of three
blocks.  The predecessor field is therefore what selects the incoming value in
both: the differential is about the field, not about a straight line.

Run from the repository root:

    nix develop -c lake env lean tests/phi-model.lean
-/
import LeanLLVM

open LeanLLVM

/-- The integer a run returns, or `ub` for an undefined or unfinished one. -/
def answer (o : Option Outcome) : String :=
  match o with
  | some (.ret (some (.int _ v)) _) => toString v.toNat
  | _ => "ub"

/-- Parse a fixture and run its `main`. -/
def runMain (path : String) (args : List Value) : IO String := do
  let src ← IO.FS.readFile path
  match parseModule src with
  | .error e => return s!"parse error in {path}: {e}"
  | .ok m =>
      match m.functions.find? (·.name = "main") with
      | some f => return answer (run noCalls f args)
      | none => return s!"{path} has no main"

def main : IO Unit := do
  let loop ← runMain "tests/phi/loop.ll" []
  IO.println s!"loop {loop}"
  let mut fields := []
  for argc in [1, 2, 3, 4] do
    let v ← runMain "tests/phi/three.ll"
      [.int 32 (BitVec.ofNat 32 argc), .ptr 0]
    fields := fields ++ [v]
  IO.println s!"three {String.intercalate " " fields}"

#eval main
