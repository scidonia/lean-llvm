/-
The parser/printer round trip for the `getelementptr` counterexample.

`tests/counterexamples/gep-roundtrip.ll` walks one byte past an `i8` allocation
and back before dereferencing, and it writes **no** `inbounds`.  This runner
parses it, prints it with `Module.render`, and reports:

* whether the source text and the printed text contain `inbounds` — the same
  detector on both, so the source is the negative control and the printed text
  is the observation;
* the printed text verbatim, between markers;
* the value the model returns, so the observed return is recorded beside the
  text — the return is *not* the criterion here, because LLVM may still return
  the same byte from an undefined program.

`tests/counterexamples/gep-roundtrip.sh` assembles the printed text and decides
the round trip.

Run from the repository root:

    nix develop -c probes/install/mem-capped.sh --cap 6G -- lake env lean tests/counterexamples/gep-roundtrip.lean
-/
import LeanLLVM

open LeanLLVM

/-- Whether `sub` occurs in `s`. -/
def mentions (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- The integer a run returns, or `ub` for an undefined or unfinished one. -/
def answer (o : Option Outcome) : String :=
  match o with
  | some (.ret (some (.int _ v)) _) => toString v.toNat
  | _ => "ub"

def main : IO Unit := do
  let src ← IO.FS.readFile "tests/counterexamples/gep-roundtrip.ll"
  match parseModule src with
  | .error e => IO.println s!"parse-error {e}"
  | .ok m =>
      let printed := Module.render m
      IO.println s!"source-has-inbounds {mentions src "inbounds"}"
      IO.println s!"printed-has-inbounds {mentions printed "inbounds"}"
      IO.println s!"reparse-same {if parseModule printed = .ok m then "true" else "false"}"
      match m.functions.find? (·.name = "roundtrip_gep") with
      | some f => IO.println s!"model {answer (run noCalls f [])}"
      | none => IO.println "parse-error no roundtrip_gep"
      IO.println "--- printed ---"
      IO.print printed
      IO.println "--- end printed ---"

#eval main
