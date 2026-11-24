/-
The canonical rendering of a reference value's number lexemes.

`bitsLexeme` is the payload's own eight bytes — `strtodSpec`'s bits
little-endian, exactly what an event record carries — and `canonValue` replaces
each number's source lexeme in a `Value` by that rendering.  The reading is
`StrtodReader.reader`, the emitted scanner's own decomposition, the conversion is
`strtodSpec`, and a lexeme the reader refuses has no rendering, so `canonValue`
is `Option`-valued and fails loudly there rather than leaving the lexeme in place
as if it had been canonicalised.

The module exists so the transformation is importable as code: it depends on the
reading (`StrtodRead`) and the JSON value, not on the stage-2 walk's
specification or the strtod tiers.
-/
import LeanLLVM.JSON
import LeanLLVM.StrtodRead
import LeanLLVM.Refinement.JsonEventDecode

set_option autoImplicit false

namespace LeanLLVM.Refinement

open LeanLLVM
open LeanLLVM.JSON

/-- **The canonical rendering of a source lexeme.**  Read the lexeme with the
emitted scanner's reader, convert it to binary64 with `strtodSpec`, and render
that value's payload bytes.  `none` when the reader refuses the lexeme: an
unreadable lexeme has no value, hence no canonical rendering. -/
def canonLexeme (lexeme : Bytes) : Option Bytes :=
  (StrtodReader.reader lexeme).map fun d =>
    ByteString.literal (bitsLexeme (strtodSpec d).toBits)

mutual

/-- **Canonicalise a value's number lexemes.**  Structure, keys, order, strings
and literals are unchanged; each number's lexeme becomes its canonical rendering,
and a lexeme with no rendering makes the whole value `none`. -/
def canonValue : JSON.Value → Option JSON.Value
  | .null => some .null
  | .bool b => some (.bool b)
  | .string cs => some (.string cs)
  | .number lexeme => (canonLexeme lexeme).map .number
  | .array elems => (canonValues elems).map .array
  | .object members => (canonMembers members).map .object

/-- Elementwise canonicalisation, order preserved. -/
def canonValues : List JSON.Value → Option (List JSON.Value)
  | [] => some []
  | v :: vs => canonValue v >>= fun v' => (canonValues vs).map fun vs' => v' :: vs'

/-- Memberwise canonicalisation, keys and order preserved. -/
def canonMembers : List (List Nat × JSON.Value) →
    Option (List (List Nat × JSON.Value))
  | [] => some []
  | (k, v) :: ms =>
      canonValue v >>= fun v' => (canonMembers ms).map fun ms' => (k, v') :: ms'

end

end LeanLLVM.Refinement
