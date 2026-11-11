/-
The model-side answers for the leading-`phi` snapshot fixtures.

Each fixture under `tests/counterexamples/` exercises one shape of a block's
leading `phi` run, and all of them must agree with `clang -O0` on the same text:
`phi-cycle.ll` (three-register cycle), `phi-self.ll` (self-carried value),
`phi-backedge.ll` (back edge from a different predecessor block), and the
`phi-perm-a.ll` / `phi-perm-b.ll` permutation pair.

This runner asserts nothing: it prints `model <case> <value>`, where a run that
ends in `ub` or without a returned value prints `ub`.  The driver
`tests/counterexamples/phi-snapshot.sh` is what compares the answers with the
compiler's and the pair with each other.

Run from the repository root:

    nix develop -c probes/install/mem-capped.sh --cap 6G -- lake env lean tests/counterexamples/phi-snapshot.lean
-/
import LeanLLVM

open LeanLLVM

/-- The integer a run returns, or `ub` for an undefined or unfinished one. -/
def answer (o : Option Outcome) : String :=
  match o with
  | some (.ret (some (.int _ v)) _) => toString v.toNat
  | _ => "ub"

/-- The model's answer for the fixture at `path`, read off the same file the
compiler is given. -/
def modelAnswer (path : String) : IO String := do
  let src ← IO.FS.readFile path
  match parseModule src with
  | .error e => return s!"parse-error {e}"
  | .ok m =>
      match m.functions.find? (·.name = "main") with
      | some f => return answer (run noCalls f [])
      | none => return "parse-error no main"

/-- The case name and its fixture, in the order the driver reports them. -/
def cases : List (String × String) :=
  [ ("cycle", "tests/counterexamples/phi-cycle.ll"),
    ("self", "tests/counterexamples/phi-self.ll"),
    ("backedge", "tests/counterexamples/phi-backedge.ll"),
    ("perm-a", "tests/counterexamples/phi-perm-a.ll"),
    ("perm-b", "tests/counterexamples/phi-perm-b.ll") ]

def main : IO Unit := do
  for (name, path) in cases do
    IO.println s!"model {name} {(← modelAnswer path)}"

#eval main
