/-
`leanllvm-json-utf8`: the UTF-8 stage's specification, printed.

`--tables` prints the three published tables, one line each, as

    <name> <b00> <b01> … <b31>

with each byte two lowercase hexadecimal digits.  `probes/json/u8kl_tables.c`
prints the vendored header's own `kl_t1`, `kl_t2` and `kl_t3` in exactly that
form, and `tests/json-utf8/check.sh` compares the two outputs row for row — so
the specification's tables are shown to be the header's bytes rather than a
transcription that agrees with itself.

Nothing here reads the header, builds a unit, or runs the stage: the mode is the
specification's side of that comparison and nothing else.  The route's corpus
rows belong to the same executable and are not part of this mode.
-/
import LeanLLVM.Vellum.JsonUtf8Spec

open LeanLLVM
open LeanLLVM.Vellum

/-- One byte as two lowercase hexadecimal digits. -/
def hex2 (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b.toNat / 16) '0', digits.getD (b.toNat % 16) '0']

/-- `<name> <b00> … <b31>`: one table's thirty-two bytes, space-separated. -/
def tableRow (name : String) (t : Vector UInt8 32) : String :=
  name ++ " " ++ String.intercalate " " (t.toList.map hex2)

/-- The mode list, printed on a refused argument list. -/
def usage : String :=
  "usage: leanllvm-json-utf8 --tables\n" ++
  "  --tables  print kl_t1, kl_t2 and kl_t3 as the specification's values;\n" ++
  "            tests/json-utf8/check.sh compares them with the vendored header's"

/-- The run: `--tables` and nothing else yet, so an unimplemented mode is a
refusal rather than an empty run. -/
def run (args : List String) : IO UInt32 :=
  match args with
  | ["--tables"] => do
      IO.println (tableRow "kl_t1" JsonUtf8Spec.klT1)
      IO.println (tableRow "kl_t2" JsonUtf8Spec.klT2)
      IO.println (tableRow "kl_t3" JsonUtf8Spec.klT3)
      return 0
  | _ => do
      IO.eprintln usage
      return 2

def main (args : List String) : IO UInt32 := run args
