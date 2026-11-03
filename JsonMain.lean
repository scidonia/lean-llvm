/-
`leanllvm-json`: the scalar reference parser's corpus driver.

It reads `tests/json/manifest.tsv` — four tab-separated columns: the corpus
path relative to the corpus directory, the expected verdict, the expected
rendering (`-` unless the verdict is `accept`), and a limits profile — runs
`parseDocument` on each file under that profile, prints one
`<path>\t<verdict>\t<rendering>` line per row, and exits nonzero with a
`mismatch: ...` line on stderr when any row disagrees.

The rendering is test infrastructure, not library code: a number prints `#` and
its source lexeme as lowercase hex bytes, a string prints `"` and its code points
as space-separated decimals and `"`, and containers print recursively.
-/
import LeanLLVM

open LeanLLVM.JSON

/-- The statically held limits profiles the manifest's fourth column names. -/
def profileLimits : String → Option Limits
  | "default" => some Limits.default
  | "depth2" => some { Limits.default with maxDepth := 2 }
  | "tok4" => some { Limits.default with maxTokens := 4 }
  | "in8" => some { Limits.default with maxInput := 8 }
  | _ => none

/-- A rendering of decoded values, for the corpus oracle. -/
def hexByte (b : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 b)
  if s.length == 1 then "0" ++ s else s

def renderCodePoint (c : Nat) : String := toString c

mutual
def renderValue : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .number lex => "#" ++ String.join (numHexChars lex)
  | .string cs => "\"" ++ String.intercalate " " (renderCodePoints cs) ++ "\""
  | .array es => "[" ++ String.intercalate "," (renderValues es) ++ "]"
  | .object ms => "{" ++ String.intercalate "," (renderMembers ms) ++ "}"

/-- The lexeme's bytes as lowercase hex, read over the carrier's list view. -/
def numHexChars (bs : Bytes) : List String :=
  bs.toList.map (fun b => hexByte b.toNat)

def renderCodePoints : List Nat → List String
  | [] => []
  | c :: cs => renderCodePoint c :: renderCodePoints cs

def renderValues : List Value → List String
  | [] => []
  | e :: es => renderValue e :: renderValues es

def renderMembers : List (List Nat × Value) → List String
  | [] => []
  | (k, v) :: ms =>
      (renderValue (.string k) ++ ":" ++ renderValue v) :: renderMembers ms
end

/-- The verdict column's spelling of the parser's result, and the rendering. -/
def outcome (r : ParseResult) : String × String :=
  match r with
  | .ok t =>
      match decodeTape t with
      | some v => ("accept", renderValue v)
      | none => ("accept", "-")
  | .error (.invalid _) => ("invalid", "-")
  | .error .inputTooLong => ("inputTooLong", "-")
  | .error .depthExceeded => ("depthExceeded", "-")
  | .error .outOfCapacity => ("outOfCapacity", "-")

structure Options where
  corpus : Option String := none
  manifest : Option String := none
  deriving Inhabited

def usage : String :=
  "usage: leanllvm-json --corpus <dir> --manifest <file>"

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      match o.corpus, o.manifest with
      | some _, some _ => .ok o
      | _, none => .error "missing --manifest"
      | none, _ => .error "missing --corpus"
  | "--corpus" :: dir :: rest => parseArgsAux { o with corpus := some dir } rest
  | "--corpus" :: [] => .error "missing directory after --corpus"
  | "--manifest" :: file :: rest => parseArgsAux { o with manifest := some file } rest
  | "--manifest" :: [] => .error "missing file after --manifest"
  | arg :: _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

/-- Split a manifest line into its four columns. -/
def splitLine (line : String) : List String := line.splitOn "\t"

def run (opts : Options) : IO UInt32 := do
  let some corpus := opts.corpus
    | IO.eprintln "leanllvm-json: missing --corpus"; return 1
  let some manifest := opts.manifest
    | IO.eprintln "leanllvm-json: missing --manifest"; return 1
  let text ← try
      IO.FS.readFile manifest
    catch e =>
      IO.eprintln s!"leanllvm-json: cannot read '{manifest}': {e}"
      return 2
  let mut failures : Nat := 0
  for line in text.splitOn "\n" do
    if line.isEmpty then continue
    match splitLine line with
    | [path, verdict, rendering, profile] =>
        let some limits := profileLimits profile
          | IO.eprintln s!"mismatch: {path}: unknown profile '{profile}'"
            failures := failures + 1
            continue
        let bytes ← try
            IO.FS.readBinFile (corpus ++ "/" ++ path)
          catch e =>
            IO.eprintln s!"mismatch: {path}: {e}"
            failures := failures + 1
            continue
        let (gotVerdict, gotRendering) := outcome (parseDocument limits bytes)
        IO.println (path ++ "\t" ++ gotVerdict ++ "\t" ++ gotRendering)
        if gotVerdict != verdict then
          IO.eprintln s!"mismatch: {path}: expected verdict '{verdict}', got '{gotVerdict}'"
          failures := failures + 1
        else if gotRendering != rendering then
          IO.eprintln s!"mismatch: {path}: expected rendering '{rendering}', got '{gotRendering}'"
          failures := failures + 1
    | _ =>
        IO.eprintln s!"mismatch: malformed manifest line '{line}'"
        failures := failures + 1
  if failures == 0 then return 0 else return 1

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .ok opts => run opts
  | .error e =>
      IO.eprintln s!"leanllvm-json: {e}"
      IO.eprintln usage
      return 1
