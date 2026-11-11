/-
The model-side answer for the two-register `phi` swap.

`tests/counterexamples/phi-swap.ll` swaps `%a` and `%b` on the back edge.  Both
incoming operands belong to the edge, so on the second iteration `%b` must read
the `%a` that arrived on that edge — the old `%b`, `2` — and the program returns
`1`.  A semantics that installs `%a`'s new binding before reading `%b`'s operand
returns `2`.

This runner asserts nothing: it prints `model <value>`, where a run that ends in
`ub` or without a returned value prints `ub`.  `tests/counterexamples/phi-swap.sh`
is what compares the answer with the compiler's.

Run from the repository root:

    nix develop -c probes/install/mem-capped.sh --cap 6G -- lake env lean tests/counterexamples/phi-swap.lean
-/
import LeanLLVM

open LeanLLVM

/-- The integer a run returns, or `ub` for an undefined or unfinished one. -/
def answer (o : Option Outcome) : String :=
  match o with
  | some (.ret (some (.int _ v)) _) => toString v.toNat
  | _ => "ub"

def main : IO Unit := do
  let src ← IO.FS.readFile "tests/counterexamples/phi-swap.ll"
  match parseModule src with
  | .error e => IO.println s!"parse-error {e}"
  | .ok m =>
      match m.functions.find? (·.name = "main") with
      | some f => IO.println s!"model {answer (run noCalls f [])}"
      | none => IO.println "parse-error no main"

#eval main
