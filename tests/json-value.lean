/-
The value oracle: the reference parser's canonical printed value for each
document in a corpus directory.

For one document the oracle runs `parseBytes Limits.default doc`, decodes the
tape with `decodeTape`, canonicalises the value's number lexemes with
`canonValue`, and prints the lowercase hex of the UTF-8 bytes of
`renderValue`'s rendering (all three from the library: `JSON/Parse.lean`,
`JSON/Tape.lean`, `Refinement/JsonEventValue.lean` and `JSON/Render.lean`).  It
never renders a value itself, so a route comparing its own answer against these
rows compares one rendering, not two.  A document the reference refuses prints
the refusal instead, in the route's value-line vocabulary: the class from
`parseErrorName` and the offset from `parseErrorOffset`, `-` where the refusal
names no byte.

One row per file in the corpus directory, sorted by name, tab-separated, in the
shape `tests/json-value/expected.tsv` pins before its digest column:

    <document>  <accept|refuse>  <hex|->  <class|->  <offset|->

On an acceptance the hex column is the rendering's UTF-8 bytes and the refusal
columns are `-`; on a refusal the hex column is `-`, the class is
`parseErrorName`'s and the offset is `parseErrorOffset`'s or `-`.  The digest
column is the check's to add, because it pins the document's bytes rather than
this program's output.

Elaborated and run by `tests/json-value/check.sh`:

    lake env lean --run tests/json-value.lean tests/json-value/corpus

An unreadable document exits 2 with the path on stderr.  A document the
reference accepts whose value `canonValue` cannot read exits 3: silently leaving
the lexeme in place would compare a source spelling against a canonical payload
and report a value mismatch for a rendering bug.
-/
import LeanLLVM.JSON.Render
import LeanLLVM.Refinement.JsonEventValue
import LeanLLVM.Refinement.JsonPipelineSpec

namespace JsonValueOracle

open LeanLLVM.JSON
open LeanLLVM.Refinement

/-- One byte as two lowercase hex digits.  This is the row's transfer encoding,
not part of the rendering: the value itself comes from `renderValue` above. -/
def hexByte (b : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 b)
  if s.length == 1 then "0" ++ s else s

/-- A string's UTF-8 bytes as lowercase hex, one two-digit byte per byte. -/
def hexUTF8 (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b => hexByte b.toNat)

/-- One corpus document's row, or the status and message it fails with: 2 for a
document that cannot be read, 3 for an accepted document whose value
`canonValue` cannot read. -/
def rowOf (dir name : String) : IO (Except (UInt32 × String) String) := do
  let path := dir ++ "/" ++ name
  let doc ← try
      IO.FS.readBinFile path
    catch e =>
      return .error (2, s!"cannot read '{path}': {e}")
  match parseBytes Limits.default doc with
  | .error e =>
      let offset := match parseErrorOffset e with
        | some p => toString p
        | none => "-"
      return .ok s!"{name}\trefuse\t-\t{parseErrorName e}\t{offset}"
  | .ok t =>
      match (decodeTape t).bind canonValue with
      | some v => return .ok s!"{name}\taccept\t{hexUTF8 (renderValue v)}\t-\t-"
      | none =>
          return .error (3, s!"'{name}': accepted document whose value canonValue \
            cannot read; the oracle has no canonical rendering to pin")

def run (dir : String) : IO UInt32 := do
  let entries ← try
      (dir : System.FilePath).readDir
    catch e =>
      IO.eprintln s!"json-value: cannot read directory '{dir}': {e}"
      return 2
  let names := (entries.map (·.fileName)).qsort fun a b => compare a b == .lt
  let mut status : UInt32 := 0
  for name in names do
    match ← rowOf dir name with
    | .ok row => IO.println row
    | .error (code, msg) =>
        IO.eprintln s!"json-value: {msg}"
        status := code
  return status

end JsonValueOracle

def main (args : List String) : IO UInt32 :=
  match args with
  | [dir] => JsonValueOracle.run dir
  | _ =>
      IO.eprintln "usage: lake env lean --run tests/json-value.lean <corpus-dir>"
      return 2
