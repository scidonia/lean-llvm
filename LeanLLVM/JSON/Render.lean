/-
A rendering of decoded JSON values, shared by the corpus oracle and the route.

The rendering is test and probe infrastructure, not library semantics: a number
prints `#` and its lexeme's bytes as lowercase hex, a string prints `"` and its
code points as space-separated decimals and `"`, and containers print
recursively.  It is one definition rather than two copies because a route's
value line is compared against the corpus oracle's rows: a second copy could
drift on a whitespace or a hex digit and the comparison would report a value
mismatch instead of a rendering bug.
-/
import LeanLLVM.JSON.Spec

namespace LeanLLVM.JSON

open ByteString

/-- One byte as two lowercase hex digits. -/
def renderHexByte (b : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 b)
  if s.length == 1 then "0" ++ s else s

/-- One code point as its decimal spelling in the rendering's string form. -/
def renderCodePoint (c : Nat) : String := toString c

mutual

/-- A decoded value's rendering. -/
def renderValue : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .number lex => "#" ++ String.join (numHexChars lex)
  | .string cs => "\"" ++ String.intercalate " " (renderCodePoints cs) ++ "\""
  | .array es => "[" ++ String.intercalate "," (renderValues es) ++ "]"
  | .object ms => "{" ++ String.intercalate "," (renderMembers ms) ++ "}"

/-- The lexeme's bytes as lowercase hex, read over the carrier's list view. -/
def numHexChars (bs : Bytes) : List String :=
  bs.toList.map (fun b => renderHexByte b.toNat)

/-- A string's code points, each in its decimal spelling. -/
def renderCodePoints : List Nat → List String
  | [] => []
  | c :: cs => renderCodePoint c :: renderCodePoints cs

/-- An array's elements, rendered and comma-separated. -/
def renderValues : List Value → List String
  | [] => []
  | e :: es => renderValue e :: renderValues es

/-- An object's members, each rendered as `"key":value`, comma-separated. -/
def renderMembers : List (List Nat × Value) → List String
  | [] => []
  | (k, v) :: ms =>
      (renderValue (.string k) ++ ":" ++ renderValue v) :: renderMembers ms

end

end LeanLLVM.JSON
