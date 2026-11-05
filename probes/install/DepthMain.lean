/-
`leanllvm-depth-check`: the depth fold's corpus runner.

The installed depth unit's numeric evidence is agreement with the
specification `LeanLLVM.Vellum.DepthCountRefine.depthSpec`, not with another
implementation of the same fold.  This program prints `depthSpec` for each row
of a corpus of index arrays; `probes/install/depth_driver.c` calls the installed
object over the same rows and prints what it returned and stored, and
`tests/depth-count/check.sh` compares the two.

A corpus row is `<name>\t<tokens>\t<indices>`: the token buffer and the index
array, both decimal and comma-separated, empty for the empty list.  An index is
a position inside the token buffer; a row whose index is outside it is refused,
because the kernel's read there is undefined and the driver does not pass such
a row to the unit either.

Exit status: 0 when every row was read and folded, 1 on a malformed row, 2 on a
usage error or an unreadable corpus.
-/
import LeanLLVM.Vellum.DepthCountRefine

open LeanLLVM.Vellum.DepthCountRefine

namespace DepthCheck

def usage : String := "usage: leanllvm-depth-check <corpus.tsv>"

/-- A comma-separated list of natural numbers; the empty string is `[]`. -/
def parseNats (field : String) : Except String (List Nat) := do
  if field.isEmpty then
    pure []
  else
    field.splitOn "," |>.mapM fun part =>
      match part.toNat? with
      | some n => pure n
      | none => throw s!"not a natural number: '{part}'"

/-- The byte values a token field names, each at most 255. -/
def parseBytes (field : String) : Except String (List UInt8) := do
  let ns ← parseNats field
  ns.mapM fun n =>
    if n ≤ 255 then pure (UInt8.ofNat n)
    else throw s!"byte value {n} is above 255"

/-- The token sequence the index list selects.  An index outside the buffer is
refused rather than folded over a stand-in byte. -/
def selectedTokens (tokens : List UInt8) (indices : List Nat) :
    Except String (List UInt8) :=
  indices.mapM fun i =>
    match (tokens.drop i).head? with
    | some b => pure b
    | none => throw s!"index {i} is outside the {tokens.length}-byte token buffer"

/-- One row's specification value: `(final depth, running-depth sum)`. -/
def expectRow (tokens indices : String) : Except String (Int × Int) := do
  let cs ← selectedTokens (← parseBytes tokens) (← parseNats indices)
  pure (depthSpec cs)

/-- Print `<name>\t<depth>\t<sum>` for every row, or report the first
malformation of each row and exit 1. -/
def runCorpus (path : String) : IO UInt32 := do
  let text ←
    try
      IO.FS.readFile path
    catch err =>
      IO.eprintln s!"depth-check: cannot read {path}: {err}"
      return 2
  let mut bad := false
  for line in text.splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then
      continue
    match line.splitOn "\t" with
    | [name, tokens, indices] =>
        match expectRow tokens indices with
        | .ok (sp, sum) => IO.println s!"{name}\t{sp}\t{sum}"
        | .error message =>
            IO.eprintln s!"depth-check: {name}: {message}"
            bad := true
    | _ =>
        IO.eprintln s!"depth-check: malformed row: {line}"
        bad := true
  return if bad then 1 else 0

end DepthCheck

def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => DepthCheck.runCorpus path
  | _ => do
      IO.eprintln DepthCheck.usage
      return 2
