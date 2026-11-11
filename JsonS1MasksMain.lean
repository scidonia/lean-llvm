/-
`leanllvm-json-s1-masks`: the stage-1 mask body over rows.

The kernel is not re-implemented here.  Each row stages a 64-byte block at
offset 1 of a 96-byte buffer, a 24-byte carry slot and a 48-byte output slot
pre-filled with `0xA5` in memory, and runs `s1MasksFunction` — the AST that
`LeanLLVM/Refinement/JsonS1MasksIR.lean` pins to
`probes/install/ir/json-s1-masks.candidate.ll` — with `runFuel` under the
repository's semantics.  The words printed are read back out of the two slots,
so the route exercises the body rather than the specification beside it.

A row is fifteen tab-separated columns:

    <source> <label> <open> <ppar> <inside> <comma> <quote> <delim>
    <in_string> <ws> <backslash> <ctl> <esc_open> <esc_ppar> <im_carry>

`open`, `ppar`, `inside` and `comma` are `0` or `1`; the nine words are `0x`
and sixteen lowercase hex digits.  `comma` is `1` when any lane of the block is
`0x2C`.  The rows, in order:

1. the mixed 64-byte block, once per carry state, `source` = `mixed`;
2. the corpus files named by `--corpus`, every 64-byte window, offset
   ascending, once per carry state;
3. `arm:byte`: for each state, byte position `0…63` and value `0…255`;
4. `arm:alphabet`: for each state, every 4-byte sequence over the sixteen
   symbols of the class alphabet, at lanes 0–3 of a `0x78` block;
5. `arm:random`: for each state, 4096 blocks from splitmix64 seeded at
   `0x243F6A8885A308D3`.

Modes:

* `--corpus <path>` (repeatable) and `--arms` select the rows; a directory
  contributes the files directly inside it, in name order.
* `--expect <file>` compares each printed row against the same columns written
  in `<file>`, prints `mismatch: <source>\t<label>: expected …, got …` on
  stderr, and exits 1 when any row disagrees — the rows themselves are still
  printed, so the disagreement is the expectation's and not the
  classification's.
* `--emit-block` writes the mixed block's 64 bytes with no trailing newline.

Exit status: `0` when every row was produced (and every expectation held), `1`
on a mismatch or a usage error, `2` when an input cannot be read.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonS1MasksIR

open LeanLLVM
open LeanLLVM.Refinement.JsonS1MasksIR

namespace JsonS1MasksMain

/-! ### Staging one row -/

/-- The 96-byte buffer's base; the block starts at `bufferBase + 1`. -/
def bufferBase : Nat := 8192

/-- The pointer the body is called with: offset 1 of the buffer. -/
def pAddr : Nat := bufferBase + 1

/-- The 24-byte carry slot. -/
def carryAddr : Nat := 9200

/-- The 48-byte output slot. -/
def outAddr : Nat := 9400

/-- The output slot's pre-fill, so a store the body does not make reads back as
a sentinel rather than as a stale word. -/
def slotSentinel : UInt8 := 0xA5

/-- Control steps the body is run for.  A single-block body needs no more. -/
def fuel : Nat := 10000

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- The inbound carry slot's 24 bytes. -/
def carryBytes (opened ppar inside : Bool) : List UInt8 :=
  natToBytes (if opened then 1 else 0) 8 ++
  natToBytes (if ppar then 1 else 0) 8 ++
  natToBytes (if inside then 0xFFFFFFFFFFFFFFFF else 0) 8

/-- The memory a row is run from. -/
def stagingMem (bs : List UInt8) (opened ppar inside : Bool) : Mem :=
  bytesAt pAddr bs ++ bytesAt carryAddr (carryBytes opened ppar inside) ++
    bytesAt outAddr (List.replicate 48 slotSentinel)

/-- The `k`-th little-endian 64-bit word of a byte list. -/
def wordAt (bs : List UInt8) (k : Nat) : Nat :=
  bytesToNat ((bs.drop (8 * k)).take 8)

/-- The nine words a row observes: six masks, then three carry words.  `none`
when the body does not return or leaves a slot unreadable — a defect in the
body, not an expectation about a block. -/
def runRow (block : List UInt8) (state : Nat) : Option (List Nat) :=
  let opened := state / 4 % 2 == 1
  let ppar := state / 2 % 2 == 1
  let inside := state % 2 == 1
  match runFuel s1Calls fuel s1MasksFunction
      { (initState s1MasksFunction [.ptr pAddr, .ptr carryAddr, .ptr outAddr]) with
        mem := stagingMem block opened ppar inside } with
  | some (.ret _ mem) =>
      match readBytes mem outAddr 48, readBytes mem carryAddr 24 with
      | some o, some c =>
          some ((List.range 6).map (fun k => wordAt o k) ++
                (List.range 3).map (fun k => wordAt c k))
      | _, _ => none
  | _ => none

/-! ### Rendering -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- `0x` and sixteen lowercase hex digits. -/
def renderWord (v : Nat) : String :=
  "0x" ++ String.ofList ((List.range 16).map fun i => hexDigit (v / 16 ^ (15 - i) % 16))

/-- Two lowercase hex digits, the byte arm's label. -/
def renderByte (v : Nat) : String :=
  String.ofList [hexDigit (v / 16 % 16), hexDigit (v % 16)]

/-! ### The mixed block -/

/-- The route's mixed 64-byte block: escaped and unescaped quotes, backslash
runs of length one, two and three, all six delimiters, all four whitespace
bytes, control bytes with and without the whitespace class, `0x7F`, and
ordinary content. -/
def mixedBlock : List UInt8 :=
  [ 0x22, 0x6B, 0x5C, 0x22, 0x2C, 0x20, 0x31, 0x5D,
    0x0A, 0x09, 0x0D, 0x5C, 0x5C, 0x22, 0x3A, 0x78,
    0x22, 0x61, 0x22, 0x7B, 0x7D, 0x5B, 0x5D, 0x2C,
    0x20, 0x01, 0x1F, 0x7F, 0x22, 0x5C, 0x74, 0x22,
    0x5C, 0x6E, 0x22, 0x2C, 0x09, 0x5C, 0x22, 0x3A,
    0x64, 0x5B, 0x5D, 0x7B, 0x7D, 0x20, 0x0D, 0x30,
    0x22, 0x5C, 0x5C, 0x5C, 0x22, 0x2C, 0x76, 0x20,
    0x09, 0x0A, 0x22, 0x7A, 0x1F, 0x79, 0x5C, 0x22 ]

/-! ### The generated arms -/

/-- The class alphabet: every byte class the six masks distinguish, one symbol
per class and per position on the class boundaries. -/
def alphabet : List UInt8 :=
  [0x00, 0x09, 0x0A, 0x0D, 0x1F, 0x20, 0x22, 0x2C,
   0x3A, 0x5B, 0x5C, 0x5D, 0x7B, 0x7D, 0x61, 0x80]

/-- Sixteen classes, four lanes. -/
def alphabetCount : Nat := 16 ^ 4

/-- The block a 4-byte sequence is staged in: the sequence at lanes 0–3 and
`0x78` elsewhere. -/
def alphabetBlock (seq : List UInt8) : List UInt8 :=
  seq ++ List.replicate 60 (0x78 : UInt8)

/-- The sequence a sequence index writes. -/
def alphabetSeq (i : Nat) : List UInt8 :=
  [ alphabet.getD (i % 16) 0,
    alphabet.getD (i / 16 % 16) 0,
    alphabet.getD (i / 256 % 16) 0,
    alphabet.getD (i / 4096 % 16) 0 ]

/-- The blocks the random arm runs. -/
def randomCount : Nat := 4096

def splitmixGamma : UInt64 := 0x9E3779B97F4A7C15
def randomSeed : UInt64 := 0x243F6A8885A308D3

/-- One splitmix64 step: the next state and its output. -/
def splitmixNext (x : UInt64) : UInt64 × UInt64 :=
  let x' := x + splitmixGamma
  let z := (x' ^^^ (x' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (x', z ^^^ (z >>> 31))

/-- The eight words block `i` is built from. -/
def randomWords (i : Nat) : List UInt64 :=
  let rec go (x : UInt64) : Nat → List UInt64 → List UInt64
    | 0, acc => acc.reverse
    | n + 1, acc =>
        let (x', w) := splitmixNext x
        go x' n (w :: acc)
  go (randomSeed + UInt64.ofNat i * splitmixGamma) 8 []

/-- The little-endian bytes of a word list. -/
def wordsToBytes (ws : List UInt64) : List UInt8 :=
  ws.flatMap fun w =>
    (List.range 8).map fun k => UInt8.ofNat (w.toNat / 256 ^ k % 256)

/-- The block the random arm runs at index `i`. -/
def randomBlock (i : Nat) : List UInt8 := wordsToBytes (randomWords i)

/-- Whether any lane of the block is `0x2C`, the byte the comma class's table
entry decides. -/
def hasComma (block : List UInt8) : Bool := block.any fun b => b == 0x2C

/-! ### Emitting rows -/

/-- The comparison an `--expect` run makes as it prints. -/
structure Emitter where
  expected : Option (Array String)
  index : IO.Ref Nat
  failures : IO.Ref Nat

def Emitter.emit (e : Emitter) (source label line : String) : IO Unit := do
  IO.println line
  match e.expected with
  | none => pure ()
  | some arr =>
      let i ← e.index.get
      e.index.set (i + 1)
      match arr[i]? with
      | none =>
          IO.eprintln s!"mismatch: {source}\t{label}: no expectation row"
          e.failures.modify (· + 1)
      | some want =>
          if want = line then pure ()
          else
            IO.eprintln s!"mismatch: {source}\t{label}: expected {want}, got {line}"
            e.failures.modify (· + 1)

/-- Print one row: run the body over a block under a carry state. -/
def Emitter.row (e : Emitter) (source label : String) (state : Nat)
    (block : List UInt8) : IO Unit := do
  match runRow block state with
  | some ws =>
      let flag (b : Bool) : String := if b then "1" else "0"
      let line := s!"{source}\t{label}\t{flag (state / 4 % 2 == 1)}\t\
        {flag (state / 2 % 2 == 1)}\t{flag (state % 2 == 1)}\t\
        {flag (hasComma block)}\t\
        {String.intercalate "\t" (ws.map renderWord)}"
      e.emit source label line
  | none =>
      IO.eprintln s!"mismatch: {source}\t{label}: the body did not return and \
        leave both slots"
      e.failures.modify (· + 1)

/-- The regular files a path names: the file itself, or the files directly in
a directory, in name order. -/
def expandPath (p : String) : IO (Except String (List String)) := do
  let isDir ← System.FilePath.isDir p
  if !isDir then return .ok [p]
  let entries ← try
      (p : System.FilePath).readDir
    catch e =>
      return .error s!"cannot read directory '{p}': {e}"
  let names := (entries.map (·.fileName)).qsort fun a b => compare a b == .lt
  let mut files : List String := []
  for name in names do
    let path := p ++ "/" ++ name
    let entryIsDir ← System.FilePath.isDir path
    if !entryIsDir then files := files ++ [path]
  return .ok files

/-- The mixed block's rows. -/
def emitMixed (e : Emitter) : IO Unit := do
  for state in List.range 8 do
    e.row "mixed" (toString state) state mixedBlock

/-- Every 64-byte window of every corpus file, once per carry state. -/
def emitCorpus (e : Emitter) (paths : List String) : IO (Except String Unit) := do
  let mut files : List String := []
  for p in paths do
    match ← expandPath p with
    | .error err => return .error err
    | .ok fs => files := files ++ fs
  for path in files do
    let bytes ← try
        IO.FS.readBinFile path
      catch err =>
        return .error s!"cannot read '{path}': {err}"
    if bytes.size ≥ 64 then
      for offset in List.range (bytes.size - 63) do
        let block := (bytes.extract offset (offset + 64)).toList
        for state in List.range 8 do
          e.row path (toString offset) state block
  return .ok ()

/-- The byte sweep: every value at every lane position, under every state. -/
def emitByteArm (e : Emitter) : IO Unit := do
  for state in List.range 8 do
    for pos in List.range 64 do
      for v in List.range 256 do
        let block := (List.replicate 64 (0x78 : UInt8)).set pos (UInt8.ofNat v)
        e.row "arm:byte" s!"pos{pos}/val{renderByte v}/carry{state}" state block

/-- Every 4-byte sequence over the class alphabet, under every state. -/
def emitAlphabetArm (e : Emitter) : IO Unit := do
  for state in List.range 8 do
    for i in List.range alphabetCount do
      let seq := alphabetSeq i
      e.row "arm:alphabet"
        s!"{String.join (seq.map fun b => renderByte b.toNat)}/carry{state}"
        state (alphabetBlock seq)

/-- The fixed-seed random arm, under every state. -/
def emitRandomArm (e : Emitter) : IO Unit := do
  for state in List.range 8 do
    for i in List.range randomCount do
      e.row "arm:random" s!"idx{i}/carry{state}" state (randomBlock i)

/-- Write the mixed block's bytes, with no trailing newline. -/
def runEmitBlock : IO UInt32 := do
  IO.print (String.ofList (mixedBlock.map fun b => Char.ofNat b.toNat))
  return 0

/-! ### Arguments -/

structure Options where
  corpus : List String := []
  arms : Bool := false
  expect : Option String := none
  emitBlock : Bool := false
  deriving Inhabited

def usage : String :=
  "usage: leanllvm-json-s1-masks [--corpus <path> ...] [--arms] [--expect <file>]\n" ++
  "       leanllvm-json-s1-masks --emit-block"

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      if o.emitBlock then
        match o.corpus, o.arms, o.expect with
        | [], false, none => .ok o
        | _, _, _ => .error "--emit-block cannot be combined with the row options"
      else
        match o.corpus, o.arms with
        | [], false => .error "one of --corpus, --arms or --emit-block is required"
        | _, _ => .ok o
  | "--corpus" :: p :: rest => parseArgsAux { o with corpus := o.corpus ++ [p] } rest
  | "--corpus" :: [] => .error "missing path after --corpus"
  | "--arms" :: rest => parseArgsAux { o with arms := true } rest
  | "--expect" :: f :: rest => parseArgsAux { o with expect := some f } rest
  | "--expect" :: [] => .error "missing file after --expect"
  | "--emit-block" :: rest => parseArgsAux { o with emitBlock := true } rest
  | arg :: _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

/-- Run every selected row, comparing against the expectation when one is
given. -/
def runRows (o : Options) : IO UInt32 := do
  let expected ← match o.expect with
    | none => pure (none : Option (Array String))
    | some file =>
        let text ← try
            IO.FS.readFile file
          catch e =>
            IO.eprintln s!"leanllvm-json-s1-masks: cannot read '{file}': {e}"
            return 2
        pure (some (text.splitOn "\n" |>.toArray))
  let index ← IO.mkRef 0
  let failures ← IO.mkRef 0
  let e : Emitter := { expected := expected, index := index, failures := failures }
  emitMixed e
  match ← emitCorpus e o.corpus with
  | .error err =>
      IO.eprintln s!"leanllvm-json-s1-masks: {err}"
      return 2
  | .ok () => pure ()
  if o.arms then
    emitByteArm e
    emitAlphabetArm e
    emitRandomArm e
  let fails ← failures.get
  -- A short expectation is a disagreement too: rows were printed against no
  -- expectation.
  if fails = 0 then
    match expected, o.expect with
    | some arr, some file =>
        let printed ← index.get
        -- The file's final newline makes one empty trailing element.
        let want := if arr.size > 0 ∧ arr[arr.size - 1]! = "" then arr.size - 1 else arr.size
        if printed = want then
          IO.eprintln s!"ok: {printed} row(s) agree with '{file}'"
          return 0
        else
          IO.eprintln s!"mismatch: {want} row(s) expected, {printed} printed"
          return 1
    | _, _ =>
        IO.eprintln s!"ok: {← index.get} row(s)"
        return 0
  else
    IO.eprintln s!"leanllvm-json-s1-masks: {fails} row(s) disagree"
    return 1

/-- Dispatch one command line.  Named `run` rather than `main`: a `main`
inside this namespace leaves the module without a root-level one, and the
linked `Lean` library's own front end would answer `--emit-block` instead. -/
def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .ok { emitBlock := true, corpus := [], arms := false, expect := none } => runEmitBlock
  | .ok o => runRows o
  | .error e =>
      IO.eprintln s!"leanllvm-json-s1-masks: {e}"
      IO.eprintln usage
      return 1

end JsonS1MasksMain

/-- The executable's entry point. -/
def main (args : List String) : IO UInt32 := JsonS1MasksMain.run args
