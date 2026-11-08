/-
`leanllvm-json-utf8`: the UTF-8 stage's specification, printed, and the stage's
body over the route's rows.

Modes:

* `--tables` prints the three published tables, one line each, as

      <name> <b00> <b01> … <b31>

  with each byte two lowercase hexadecimal digits.  `probes/json/u8kl_tables.c`
  prints the vendored header's own `kl_t1`, `kl_t2` and `kl_t3` in exactly that
  form, and `tests/json-utf8/check.sh` compares the two outputs row for row — so
  the specification's tables are shown to be the header's bytes rather than a
  transcription that agrees with itself.

* `[--corpus FILE]... [--arms] --ungated 0|1` runs the stage's body over the
  route's rows and prints one line per row:

      <source> <label> <n> <gate> <path> <word> <skip> <eval> <padded>

  `source` is the corpus argument as given, or `arm:<arm>`; `label` is the
  row's identity inside its source; `n` is the document's length in bytes;
  `gate` and `path` are the gate value the row was run at and the effective
  path the body took, in the same letters, `g` for the gated arm and `u` for
  the ungated one; `word` is the stage's error word, `0` accepted and `1`
  rejected; `padded` is `n % 64 != 0`.

  The kernel is not re-implemented here.  A row stages a window in memory —
  three prefix bytes, the document, and zero padding to the 64-byte boundary
  the block count counts — runs `utf8Function`, the AST
  `LeanLLVM/Vellum/JsonUtf8IR.lean` pins to
  `probes/install/ir/json-utf8.candidate.ll`, through `runFuel` under the
  repository's semantics, and reads the returned word.  The word printed is the
  body's, so a route that compares it with the object's and with the measured
  statements' exercises the body rather than the specification beside it.

  `skip` and `eval` are **derived** from the staged window's bytes by the rule
  `probes/json/utf8_skip.h` states, written here a second time in Lean on
  purpose: the C actors share one derivation and this one is the route's
  independent check of it, so the columns are compared rather than echoed.  The
  gate's two arms agree on every document of the counted matrix, which is what
  makes these counts the gate's only per-document trace.

  The arms are the same list `probes/json/utf8_rows.h` enumerates: the empty
  document, every one- and two-byte document, six three-byte leads against nine
  continuation values squared, seven four-byte leads against those values cubed,
  eight tail suffixes at every length they fit in three layouts, six documents
  under three prefix values, and eight sequences at every block-boundary offset.
  The Lean list and the C list are separate texts, so a row that one side
  enumerates and the other does not is a disagreement rather than a repetition.

  The corpus file is a four-column TSV, no header: `label`, the document's
  bytes as lowercase hex pairs (`-` for the empty document), `n`, and the
  expectation in the stage's units.  A malformed line exits 2; a file that
  cannot be read exits 2 as well, since every row here is an assertion input.
-/
import LeanLLVM.Vellum.JsonUtf8Spec
import LeanLLVM.Vellum.JsonUtf8IR

open LeanLLVM
open LeanLLVM.Vellum

namespace JsonUtf8Main

/-! ### The tables -/

/-- One byte as two lowercase hexadecimal digits. -/
def hex2 (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  String.ofList [digits.getD (b.toNat / 16) '0', digits.getD (b.toNat % 16) '0']

/-- `<name> <b00> … <b31>`: one table's thirty-two bytes, space-separated. -/
def tableRow (name : String) (t : Vector UInt8 32) : String :=
  name ++ " " ++ String.intercalate " " (t.toList.map hex2)

/-! ### Reading the corpus -/

def isDigit (c : Char) : Bool := 48 ≤ c.val.toNat && c.val.toNat ≤ 57

def isHexDigit (c : Char) : Bool :=
  isDigit c || (97 ≤ c.val.toNat && c.val.toNat ≤ 102) ||
    (65 ≤ c.val.toNat && c.val.toNat ≤ 70)

def hexValue (c : Char) : Nat :=
  if isDigit c then c.val.toNat - 48
  else if 97 ≤ c.val.toNat then c.val.toNat - 97 + 10
  else c.val.toNat - 65 + 10

/-- The first run of decimal digits in `s`. -/
def parseDec (s : String) : Option Nat :=
  let ds := (s.toList.dropWhile fun c => !isDigit c).takeWhile isDigit
  if ds.isEmpty then none
  else some (ds.foldl (fun acc c => acc * 10 + (c.val.toNat - 48)) 0)

/-- `hex` as bytes: lowercase or uppercase pairs, or `-` for no bytes. -/
def parseHex (hex : String) : Option (List UInt8) :=
  let cs := hex.toList
  if cs = ['-'] then some []
  else if cs.length % 2 != 0 || !cs.all isHexDigit then none
  else
    let rec go : List Char → Option (List UInt8)
      | [] => some []
      | a :: b :: rest =>
          match go rest with
          | none => none
          | some tail => some (UInt8.ofNat (hexValue a * 16 + hexValue b) :: tail)
      | _ => none
    go cs

/-- One row: what to stage and what it is called. -/
structure Row where
  source : String
  label : String
  pre : List UInt8
  doc : List UInt8
  deriving Inhabited

/-! ### The staged window, the run, and the counts -/

def blocksOf (n : Nat) : Nat := (n + 63) / 64

/-- The window the body reads: `pre` (three bytes), the document, and zeros to
the 64-byte boundary `nb` counts. -/
def windowOf (pre doc : List UInt8) (nb : Nat) : List UInt8 :=
  pre ++ doc ++ List.replicate (64 * nb - doc.length) 0

/-- The window as the memory the body runs from. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- A block is all-ASCII when every byte is below `0x80`. -/
def asciiBlock (blk : List UInt8) : Bool := blk.all fun b => b.toNat < 0x80

/-- The gate's per-document block counts, derived from the window's bytes: a
block the gated arm skips is all-ASCII and its predecessor is too, block 0's
predecessor being the three-byte prefix.  `skip + eval` is the block count. -/
def blockCounts (win : List UInt8) (nb : Nat) (ungated : Bool) : Nat × Nat :=
  let rec go (bi skip eval : Nat) (prevAscii : Bool) : Nat × Nat :=
    if bi < nb then
      let blk := (win.drop (3 + 64 * bi)).take 64
      let ascii := asciiBlock blk
      if !ungated && ascii && prevAscii then go (bi + 1) (skip + 1) eval ascii
      else go (bi + 1) skip (eval + 1) ascii
    else (skip, eval)
  go 0 0 0 true

/-- Run the stage's body over one row and return its error word, or `none`
when the run does not return an `i64` — which would mean the body reached `ub`
or ran out of fuel on a row the theorem covers, and is reported as a setup
fault by the caller rather than printed as a verdict. -/
def runRow (ungated : Bool) (pre doc : List UInt8) : Option Nat :=
  let n := doc.length
  let nb := blocksOf n
  let args : List Value :=
    [.ptr 3, .int 64 n, .int 32 (if ungated then 1 else 0)]
  let win := windowOf pre doc nb
  match runFuel JsonUtf8IR.utf8Calls (JsonUtf8IR.fuelOf nb) JsonUtf8IR.utf8Function
      { (initState JsonUtf8IR.utf8Function args) with mem := bytesAt 0 win } with
  | some (.ret (some (.int 64 e)) _) => some e.toNat
  | _ => none

/-- One row's printed line. -/
def rowLine (ungated : Bool) (r : Row) (word : Nat) : String :=
  let n := r.doc.length
  let nb := blocksOf n
  let win := windowOf r.pre r.doc nb
  let (skip, eval) := blockCounts win nb ungated
  let gate := if ungated then "u" else "g"
  s!"{r.source}\t{r.label}\t{n}\t{gate}\t{gate}\t{word}\t{skip}\t{eval}\t\
     {if n % 64 != 0 then 1 else 0}"

/-! ### The arms -/

def cls9 : List UInt8 := [0x7F, 0x80, 0x8F, 0x90, 0x9F, 0xA0, 0xBF, 0xC0, 0xFF]
def leads3 : List UInt8 := [0xE0, 0xE1, 0xEC, 0xED, 0xEE, 0xEF]
def leads4 : List UInt8 := [0xF0, 0xF1, 0xF3, 0xF4, 0xF5, 0xF7, 0xFF]
def zero3 : List UInt8 := [0, 0, 0]

/-- The eight tail suffixes, their byte strings, and the three layouts. -/
def tailPatterns : List (String × List UInt8) :=
  [("f0", [0xF0]), ("f090", [0xF0, 0x90]), ("f09080", [0xF0, 0x90, 0x80]),
   ("e2", [0xE2]), ("c3", [0xC3]), ("c0", [0xC0]), ("f5", [0xF5]),
   ("80", [0x80])]

def layoutNames : List String := ["raw", "pad", "pre"]

/-- `0x41` before the suffix, in the three layouts: `raw` ends at the suffix at
length `L`; `pad` puts the suffix at position `L` inside a document of the next
64-byte boundary; `pre` prefixes to that boundary with the suffix still last. -/
def tailRow (name : String) (pat : List UInt8) (layout : String) (L : Nat) : Row :=
  let k := pat.length
  let lp := (L + 63) / 64 * 64
  let doc :=
    if layout = "raw" then
      List.replicate (L - k) 0x41 ++ pat
    else if layout = "pad" then
      List.replicate (L - k) 0x41 ++ pat ++ List.replicate (lp - L) 0x41
    else
      List.replicate (lp - k) 0x41 ++ pat
  { source := "arm:tail", label := s!"{name}/{layout}/L{L}", pre := zero3, doc := doc }

def prefixDocs : List (String × List UInt8) :=
  [("80", [0x80]), ("a0", [0xA0]), ("e08080", [0xE0, 0x80, 0x80]),
   ("eda080", [0xED, 0xA0, 0x80]), ("f4908080", [0xF4, 0x90, 0x80, 0x80]),
   ("c0af", [0xC0, 0xAF])]

def prefixPres : List (String × List UInt8) :=
  [("zero", [0x00, 0x00, 0x00]), ("a3", [0x41, 0x41, 0x41]),
   ("f09080", [0xF0, 0x90, 0x80])]

def placeSeqs : List (List UInt8) :=
  [[0xC3, 0xA9], [0xE2, 0x82, 0xAC], [0xF0, 0x9F, 0x98, 0x80],
   [0xF4, 0x90, 0x80, 0x80], [0xE0, 0x80, 0x80], [0xED, 0xA0, 0x80],
   [0xC0, 0xAF], [0x80]]

/-- Every generated arm row, in the order `probes/json/utf8_rows.h` emits. -/
def armRows : List Row :=
  let b1 := (List.range 256).map fun a =>
    { source := "arm:b1", label := hex2 (UInt8.ofNat a), pre := zero3,
      doc := [UInt8.ofNat a] : Row }
  let b2 := (List.range 256).flatMap fun a =>
    (List.range 256).map fun b =>
      { source := "arm:b2", label := hex2 (UInt8.ofNat a) ++ hex2 (UInt8.ofNat b),
        pre := zero3, doc := [UInt8.ofNat a, UInt8.ofNat b] : Row }
  let b3 := leads3.flatMap fun l => cls9.flatMap fun x => cls9.map fun y =>
    { source := "arm:b3", label := hex2 l ++ hex2 x ++ hex2 y, pre := zero3,
      doc := [l, x, y] : Row }
  let b4 := leads4.flatMap fun l => cls9.flatMap fun x => cls9.flatMap fun y =>
    cls9.map fun z =>
      { source := "arm:b4", label := hex2 l ++ hex2 x ++ hex2 y ++ hex2 z,
        pre := zero3, doc := [l, x, y, z] : Row }
  let tail := tailPatterns.flatMap fun (name, pat) =>
    let lengths := (List.range (71 - pat.length)).map fun i => i + pat.length
    lengths.flatMap fun L => layoutNames.map fun layout => tailRow name pat layout L
  let prefixArm := prefixDocs.flatMap fun (dname, db) =>
    prefixPres.map fun (pname, pb) =>
      { source := "arm:prefix", label := s!"{dname}/{pname}", pre := pb,
        doc := db : Row }
  let place := placeSeqs.zipIdx.flatMap fun (seq, si) =>
    (List.range 64).map fun o =>
      let n := 64 + o
      { source := "arm:place", label := s!"seq{si}/off{o}", pre := zero3,
        doc := List.replicate (n - seq.length) 0x41 ++ seq : Row }
  { source := "arm:empty", label := "empty", pre := zero3, doc := [] : Row } ::
    b1 ++ b2 ++ b3 ++ b4 ++ tail ++ prefixArm ++ place

/-! ### Emitting -/

/-- The corpus file's rows, or the first line that does not carry its four
columns. -/
def stripCR (s : String) : String :=
  match s.toList.reverse with
  | '\r' :: rest => String.ofList rest.reverse
  | _ => s

def corpusRows (path text : String) : Except String (List Row) :=
  let lines := (text.splitOn "\n").map stripCR
  let lines := lines.filter (· != "")
  lines.zipIdx.mapM fun (line, i) =>
    match line.splitOn "\t" with
    | [label, hex, nstr, exp] =>
        match parseHex hex, parseDec nstr with
        | some doc, some n =>
            if n != doc.length then
              .error s!"{path}:{i + 1}: {doc.length} byte(s) of hex, n={n}"
            else if exp != "0" && exp != "1" then
              .error s!"{path}:{i + 1}: expectation is not 0 or 1"
            else
              .ok { source := path, label := label, pre := zero3, doc := doc }
        | _, _ => .error s!"{path}:{i + 1}: hex or n does not parse"
    | _ => .error s!"{path}:{i + 1}: not four tab-separated columns"

/-- Print one row, or refuse loudly when the body does not return a word. -/
def emitRows (ungated : Bool) (rows : List Row) : IO UInt32 := do
  for r in rows do
    match runRow ungated r.pre r.doc with
    | some word => IO.println (rowLine ungated r word)
    | none =>
        IO.eprintln s!"leanllvm-json-utf8: {r.source}/{r.label}: the body did \
          not return a word"
        return 1
  return 0

def runRows (corpus : List String) (arms : Bool) (ungated : Bool) : IO UInt32 := do
  let mut rows : List Row := []
  for path in corpus do
    let text ← try
        IO.FS.readFile path
      catch e =>
        IO.eprintln s!"leanllvm-json-utf8: cannot read '{path}': {e}"
        return 2
    match corpusRows path text with
    | .error err => do
        IO.eprintln s!"leanllvm-json-utf8: {err}"
        return 2
    | .ok rs => rows := rows ++ rs
  if arms then rows := rows ++ armRows
  emitRows ungated rows

/-! ### Arguments -/

/-- The mode list, printed on a refused argument list. -/
def usage : String :=
  "usage: leanllvm-json-utf8 --tables\n" ++
  "       leanllvm-json-utf8 [--corpus <path> ...] [--arms] [--ungated 0|1]\n" ++
  "  --tables    print kl_t1, kl_t2 and kl_t3 as the specification's values;\n" ++
  "              tests/json-utf8/check.sh compares them with the vendored header's\n" ++
  "  --corpus F  run the body over a four-column TSV: label, hex, n, expectation\n" ++
  "  --arms      generate the counted arms\n" ++
  "  --ungated N 0 gated, 1 ungated (default 0)"

structure Options where
  corpus : List String := []
  arms : Bool := false
  ungated : Bool := false
  haveUngated : Bool := false
  tables : Bool := false
  deriving Inhabited

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      if o.tables then
        if o.corpus.isEmpty && !o.arms then .ok o
        else .error "--tables takes no corpus and no arms"
      else
        match o.corpus, o.arms with
        | [], false => .error "one of --corpus or --arms is required"
        | _, _ => .ok o
  | "--tables" :: rest => parseArgsAux { o with tables := true } rest
  | "--corpus" :: p :: rest => parseArgsAux { o with corpus := o.corpus ++ [p] } rest
  | "--corpus" :: [] => .error "missing path after --corpus"
  | "--arms" :: rest => parseArgsAux { o with arms := true } rest
  | "--ungated" :: v :: rest =>
      if v = "0" then parseArgsAux { o with ungated := false, haveUngated := true } rest
      else if v = "1" then parseArgsAux { o with ungated := true, haveUngated := true } rest
      else .error s!"--ungated takes 0 or 1, not '{v}'"
  | "--ungated" :: [] => .error "missing value after --ungated"
  | arg :: _ => .error s!"unknown argument '{arg}'"

def run (args : List String) : IO UInt32 :=
  match parseArgsAux {} args with
  | .error err => do
      IO.eprintln s!"leanllvm-json-utf8: {err}"
      IO.eprintln usage
      return 2
  | .ok o => do
      if o.tables then
        IO.println (tableRow "kl_t1" JsonUtf8Spec.klT1)
        IO.println (tableRow "kl_t2" JsonUtf8Spec.klT2)
        IO.println (tableRow "kl_t3" JsonUtf8Spec.klT3)
        return 0
      else
        runRows o.corpus o.arms o.ungated

end JsonUtf8Main

def main (args : List String) : IO UInt32 := JsonUtf8Main.run args
