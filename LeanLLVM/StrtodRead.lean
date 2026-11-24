/-
The emitted scanner's number-lexeme reading, as an executable function.

`kernel/json/stage2.c`'s `num_scan` (`:152`) and `num_fast_el1` (`:379`) read a
number lexeme with three loops: the optional `minus`, `int`'s digit run cut at
the `.`/`e`, the optional `.` and its digit run, and the optional `e`/`E`, its
sign byte and its digit run.  `to_double` (`:647`) reads the same three loops a
second time for the fallback.  `reader` is that reading as a function to
`Decimal`, the decomposition the conversion proofs take as a parameter.

This module holds the executable core of `LeanLLVM.StrtodReader` — the reading
and its field functions — under that module's namespace.  The name and the
namespace differ on purpose: the reading is code, and a consumer of the code must
not inherit the specification's import closure.  `StrtodReader` imports
`StrtodTier1` and `StrtodTier3` for the proofs, and those reach
`ITree.Internal.FloatingPoint`, which imports `Mathlib.Data.FP.Basic`; a program
that only decodes a lexeme would otherwise link the tier modules' initializer
chain.  `StrtodReader` imports this module, keeps the reader's equations and the
tier correspondence, and is where those proofs live.
-/
import LeanLLVM.JSON.Scan
import LeanLLVM.JSON.Strtod

set_option autoImplicit false

namespace LeanLLVM.StrtodReader

open LeanLLVM.JSON
open ByteString

/-- A concrete byte string from a list of byte values. -/
def bytes (cs : List Nat) : Bytes := ByteString.literal (cs.map UInt8.ofNat)

/-- The bytes after an `e`: `[ minus / plus ] 1*DIGIT`, exhausted. -/
def expDigits (sign : Bool) (bs : Bytes) : Option (Bool × Bytes) :=
  let ds := bs.takeWhile IsDigitB
  if ds = empty then none
  else if bs.dropWhile IsDigitB = empty then some (sign, ds) else none

/-- The bytes after the `e`/`E`: an optional sign byte, then `1*DIGIT`. -/
def expPart (bs : Bytes) : Option (Bool × Bytes) :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      if decide (b = 0x2B) then expDigits false (literal rest)
      else if decide (b = 0x2D) then expDigits true (literal rest)
      else expDigits false (b +: literal rest)

/-- `[ exp ]` at the end of a lexeme: nothing, or `e`/`E` and the exponent,
with nothing after. -/
def expTail (bs : Bytes) : Option (Option (Bool × Bytes)) :=
  match bs.data.toList with
  | [] => some none
  | b :: rest =>
      if decide (b = 0x65) || decide (b = 0x45) then (expPart (literal rest)).map some
      else none

/-- The bytes after an `int`: an optional `.` and its `1*DIGIT`, then an
optional exponent, and nothing after. -/
def suffix (neg : Bool) (ip : Bytes) (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => some ⟨neg, ip, none, none⟩
  | b :: rest =>
      if decide (b = 0x2E) then
        let tail : Bytes := literal rest
        let fs := tail.takeWhile IsDigitB
        if fs = empty then none
        else (expTail (tail.dropWhile IsDigitB)).map fun ex => ⟨neg, ip, some fs, ex⟩
      else if decide (b = 0x65) || decide (b = 0x45) then
        (expPart (literal rest)).map fun ex => ⟨neg, ip, none, some ex⟩
      else none

/-- The bytes after the optional `minus`: `int [ frac ] [ exp ]`, exhausted. -/
def body (neg : Bool) (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      let tail : Bytes := literal rest
      if decide (b = 0x30) then suffix neg (0x30 +: empty) tail
      else if 0x31 ≤ b ∧ b ≤ 0x39 then
        suffix neg (b +: tail.takeWhile IsDigitB) (tail.dropWhile IsDigitB)
      else none

/-- `[ minus ] int [ frac ] [ exp ]`, exhausted: the emitted scanner's reading
of a number lexeme, as the decomposition it accumulates.  Each field is the bytes
the emitted loop consumes: `neg` the leading `0x2D`'s presence; `ip` the `int`
bytes, `0` alone or a `1`–`9` lead and its maximal digit run; `fr` the `.`'s
following maximal digit run, `none` when there is no `.`; and `ex` the exponent
marker's optional `+`/`-` (`true` for `-`) and its maximal digit run.  A lexeme
is refused (`none`) when a loop's run is empty where the grammar needs one byte,
or when a byte is left over — the emitted `*err` returns. -/
def reader (bs : Bytes) : Option Decimal :=
  match bs.data.toList with
  | [] => none
  | b :: rest =>
      if decide (b = 0x2D) then body true (literal rest)
      else body false (literal (b :: rest))

end LeanLLVM.StrtodReader
