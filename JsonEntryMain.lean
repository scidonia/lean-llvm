/-
`leanllvm-json-entry`: the entry positions bodies over rows, and the `ent`
word's specification rows.

The kernel is not re-implemented here.  A position row stages a mask stream,
the 8 KiB byte table and an output buffer in memory, runs `entryPos8Function`
or `entryB8Function` — the ASTs `LeanLLVM/Vellum/JsonEntryIR.lean` pins to
`probes/install/ir/json-entry.candidate.ll` — through `runFuel` under the
repository's semantics, and reads what the body wrote back out of the buffer.
The words printed are the body's, so a route that compares them with the
object's rows exercises the body rather than the specification beside it.

A row is one `(mask stream, blk0, nblk, k)` call under one kernel, printed as

    <source>\t<label>\t<kernel>\t<count>\t<words>\t<multi>\t<sentinel>

`kernel` is `p` for POS8 and `b` for B8; `count` is the returned cursor `k'`;
`words` is the first `k'` `i32` words, `0x` and exactly eight lowercase hex
digits each, comma-separated, or `-` when `k'` is 0; `multi` is 1 when a block
of the stream has more than eight set lanes; and `sentinel` is the word at lane
`k'+8`, the first lane neither kernel writes (POS8's last written lane is
`k'+7`, B8's `k'+6`).  The output buffer is staged with `0xA5`, so a lane the
body does not write reads back as `0xa5a5a5a5`, and a row whose cursor starts
at `k` begins with `k` sentinel words.

Modes:

* `--corpus <path>` (repeatable) and `--arms` select the position rows.  Each
  corpus file carries `"blk0"`, `"k"` and its masks; the arms are the 64
  single-lane masks, the 256 masks that set group 0's byte to each value, 65536
  splitmix64 masks from a fixed seed, the empty and full masks, and the 1025-mask
  long-loop stream built from the corpus masks concatenated in file order and
  repeated.
* `--expect <file>` compares each printed row against the same columns written
  in `<file>`, prints `mismatch: <source>\t<label>: expected …, got …` on
  stderr, and exits 1 when any row disagrees — the rows themselves are still
  printed, so the disagreement is the expectation's and not the body's.
* `--ent` prints the `ent` word's specification rows instead: one line per
  document block, `label qm sm im ws prevS n bi S ent tailed`, with the four
  masks the specification computes at the block and the three words built from
  them.  `label` is `corpus:<file>:blk<bi>`, `class:<name>`, or
  `arm:seed<16 hex>:blk<bi>` — the fixed-seed arm carries its seed in the label,
  so the seed is part of the result.  Inputs are decimal; the three words are
  `0x` and sixteen lowercase hex digits, because a 64-lane word above 2^53 is
  not exact in a decimal reader's arithmetic.  The tail is `lim = n - 64 * bi`
  derived inside the row, not a field: the tail arithmetic is part of the word.

Exit status: `0` when every row was produced (and every expectation held), `1`
on a mismatch or a usage error, `2` when an input cannot be read.
-/
import LeanLLVM
import LeanLLVM.Vellum.JsonEntryIR

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Vellum.JsonEntryIR
open LeanLLVM.Vellum.JsonScanSpec

namespace JsonEntryMain

/-! ### Helpers -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- `width` lowercase hex digits, with no prefix. -/
def renderHexDigits (width v : Nat) : String :=
  String.ofList ((List.range width).reverse.map fun i => hexDigit (v / 16 ^ i % 16))

/-- `0x` and `width` lowercase hex digits. -/
def renderHex (width v : Nat) : String :=
  "0x" ++ renderHexDigits width v

/-- Two lowercase hex digits. -/
def renderByte (v : Nat) : String :=
  String.ofList [hexDigit (v / 16 % 16), hexDigit (v % 16)]

/-- Two decimal digits: the lane arm's label, which names its lane in decimal. -/
def renderDec2 (v : Nat) : String :=
  String.ofList [Char.ofNat (0x30 + v / 10 % 10), Char.ofNat (0x30 + v % 10)]

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

/-- Sixteen hex digits at the front of `s`. -/
def parseHex16 (s : String) : Option Nat :=
  let ds := s.toList.take 16
  if ds.length = 16 && ds.all isHexDigit then
    some (ds.foldl (fun acc c => acc * 16 + hexValue c) 0)
  else none

/-- The quoted string after the first occurrence of `key`. -/
def quotedField (text key : String) : Option String :=
  match (text.splitOn key).drop 1 |>.head? with
  | none => none
  | some rest =>
      match rest.toList.dropWhile (fun c => c != '"') with
      | '"' :: after => some (String.ofList (after.takeWhile fun c => c != '"'))
      | _ => none

/-- The unsigned field after `key` (`"blk0": 3`). -/
def numberField (text key : String) : Option Nat :=
  match (text.splitOn key).drop 1 |>.head? with
  | none => none
  | some rest => parseDec rest

/-! ### The corpus -/

/-- One mask stream and its staging, as a committed corpus file carries them. -/
structure CorpusFile where
  path : String
  blk0 : Nat
  k : Nat
  masks : List Nat
  source : Option String

/-- The masks of a corpus file, in order. -/
def corpusMasks (text : String) : List Nat :=
  ((text.splitOn "\"0x").drop 1).filterMap fun chunk => parseHex16 chunk

def readCorpus (path : String) : IO (Except String CorpusFile) := do
  let text ← try
      IO.FS.readFile path
    catch e =>
      return .error s!"cannot read '{path}': {e}"
  let some blk0 := numberField text "\"blk0\""
    | return .error s!"'{path}' does not carry blk0"
  let some k := numberField text "\"k\""
    | return .error s!"'{path}' does not carry k"
  let masks := corpusMasks text
  if masks.isEmpty then
    return .error s!"'{path}' carries no masks"
  return .ok { path := path, blk0 := blk0, k := k, masks := masks,
               source := quotedField text "\"source\"" }

/-! ### Staging one position row -/

def slotSentinel : UInt8 := 0xA5

def tabSize : Nat := 8192

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- A mask stream as the bytes the body reads. -/
def masksBytes (ms : List Nat) : List UInt8 :=
  ms.flatMap fun m => natToBytes m 8

/-- The population count of a mask word. -/
def popcount (m : Nat) : Nat :=
  LeanLLVM.Vellum.BitLanes.ctpop (BitVec.ofNat 64 m)

/-- The cursor a correct body returns over the stream. -/
def derivedCount (k : Nat) (masks : List Nat) : Nat :=
  masks.foldl (fun acc m => acc + popcount m) k

/-- The block's eight mask bytes, group 0 first. -/
def groupBytes (m : Nat) : List Nat :=
  (List.range 8).map fun b => (m >>> (8 * b)) &&& 0xFF

/-- The table row indices a stream's group bytes select, in first-use order. -/
def firstUseRows (masks : List Nat) : List Nat :=
  let seen := masks.foldl
    (fun seen m => (groupBytes m).foldl
      (fun seen b => if seen.contains b then seen else b :: seen) seen) []
  seen.reverse

/-- One table row as the 32 bytes the body's vector load reads. -/
def pos8RowBytes (m : Nat) : List UInt8 :=
  ((pos8Row m).map fun v => natToBytes v.toNat 4).flatten

/-- The table's rows, each 32 bytes, indexed by the mask byte. -/
def pos8AllRows : List (List UInt8) :=
  (List.range 256).map pos8RowBytes

/-- The output buffer's byte count: the rows' words, the pre-cursor sentinels
and the sentinel at lane `k'+8`, with eight lanes of slack. -/
def outByteCount (k' : Nat) : Nat := 4 * (k' + 16)

/-- The table's base address, past the output buffer. -/
def tabBase (k' : Nat) : Nat := outByteCount k'

/-- The mask stream's base address, past the table. -/
def entBase (k' : Nat) : Nat := tabBase k' + tabSize

/-- The memory a position row is run from: the table rows the stream's group
bytes select, the output buffer filled with the sentinel, the mask stream, and
then the table rows nothing reads.  The cells are the whole table and the whole
buffer either way — every address the body names holds its value — but the list
order decides which cells a load and a store walk past, so the rows a load
finds are first, the buffer whose stores are many is next, and the rows no group
byte selects are last. -/
def stagingMem (k' : Nat) (masks : List Nat)
    (rows : List (List UInt8)) : Mem :=
  let used := firstUseRows masks
  let cellOf (i : Nat) : Mem := bytesAt (tabBase k' + 32 * i) (rows.getD i [])
  (used.flatMap cellOf) ++
    bytesAt 0 (List.replicate (outByteCount k') slotSentinel) ++
    bytesAt (entBase k') (masksBytes masks) ++
    ((List.range 256).filter fun i => !used.contains i).flatMap cellOf

/-- The little-endian `i32` at lane `i` of a byte array. -/
def laneAt (arr : Array UInt8) (i : Nat) : Nat :=
  let byte (j : Nat) : Nat := (arr.getD (4 * i + j) 0).toNat
  byte 0 + 256 * byte 1 + 65536 * byte 2 + 16777216 * byte 3

/-- Run one kernel over one stream.  Returns the returned count, the first `k'`
words and the word at lane `k'+8`, or `none` when the body does not return a
cursor inside the staged buffer. -/
def runRow (b8 : Bool) (masks : List Nat) (blk0 : Nat) (k : Nat)
    (rows : List (List UInt8)) : Option (Nat × List Nat × Nat) :=
  let expected := derivedCount k masks
  let outN := outByteCount expected
  let mem := stagingMem expected masks rows
  let f := if b8 then entryB8Function else entryPos8Function
  let args : List LeanLLVM.Value :=
    if b8 then
      [.ptr (entBase expected), .int 64 blk0, .int 64 masks.length,
       .ptr 0, .int 64 k]
    else
      [.ptr (entBase expected), .int 64 blk0, .int 64 masks.length,
       .ptr 0, .int 64 k, .ptr (tabBase expected)]
  let fuel := 10000 + 2000 * masks.length
  match runFuel entryCalls fuel f { (initState f args) with mem := mem } with
  | some (.ret (some (.int 64 kv)) mem') =>
      let kv := kv.toNat
      if kv + 9 ≤ expected + 16 then
        let arr := mem'.foldl
          (fun (a : Array UInt8) (cell : Nat × UInt8) =>
            if cell.1 < outN then a.set! cell.1 cell.2 else a)
          ((List.replicate outN slotSentinel).toArray)
        some (kv, (List.range kv).map (laneAt arr), laneAt arr (kv + 8))
      else none
  | _ => none

/-! ### Emitting position rows -/

/-- The comparison an `--expect` run makes as it prints. -/
structure Emitter where
  expected : Option (Array String)
  index : IO.Ref Nat
  printed : IO.Ref Nat
  failures : IO.Ref Nat

def Emitter.emit (e : Emitter) (source label line : String) : IO Unit := do
  IO.println line
  e.printed.modify (· + 1)
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

/-- Print both kernels' rows over one stream. -/
def Emitter.row (e : Emitter) (source label : String) (masks : List Nat)
    (blk0 k : Nat) (rows : List (List UInt8)) : IO Unit := do
  for b8 in [false, true] do
    match runRow b8 masks blk0 k rows with
    | some (count, words, sentinel) =>
        let rendered :=
          if count = 0 then "-" else String.intercalate "," (words.map (renderHex 8))
        let multi := if masks.any (fun m => popcount m > 8) then "1" else "0"
        let line := s!"{source}\t{label}\t{if b8 then "b" else "p"}\t{count}\t\
          {rendered}\t{multi}\t{renderHex 8 sentinel}"
        e.emit source label line
    | none =>
        IO.eprintln s!"mismatch: {source}\t{label}: the body did not return a \
          cursor inside the staged buffer"
        e.failures.modify (· + 1)

def emitCorpus (e : Emitter) (files : List CorpusFile)
    (rows : List (List UInt8)) : IO Unit := do
  for cf in files do
    let label := s!"blk0{cf.blk0}/k{cf.k}/masks{cf.masks.length}"
    e.row cf.path label cf.masks cf.blk0 cf.k rows

/-! ### The generated arms -/

def splitmixGamma : UInt64 := 0x9E3779B97F4A7C15
def randomSeed : UInt64 := 0x243F6A8885A308D3

/-- One splitmix64 step: the next state and its output. -/
def splitmixNext (x : UInt64) : UInt64 × UInt64 :=
  let x' := x + splitmixGamma
  let z := (x' ^^^ (x' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (x', z ^^^ (z >>> 31))

/-- The mask `i`: one splitmix64 step from the fixed seed. -/
def randomMask (i : Nat) : Nat :=
  (splitmixNext (randomSeed + UInt64.ofNat i * splitmixGamma)).2.toNat

def emitArms (e : Emitter) (all : List Nat) (rows : List (List UInt8)) : IO Unit := do
  for nn in List.range 64 do
    e.row "arm:lane" s!"lane{renderDec2 nn}" [(1 : Nat) <<< nn] 0 0 rows
  for hh in List.range 256 do
    e.row "arm:byte" s!"val{renderByte hh}" [hh] 0 0 rows
  for i in List.range 65536 do
    let m := randomMask i
    e.row "arm:random" s!"idx{i}/mask{renderHexDigits 16 m}" [m] 0 0 rows
  e.row "arm:empty" "empty" [0] 0 0 rows
  e.row "arm:full" "full" [0xFFFFFFFFFFFFFFFF] 0 0 rows
  if all.isEmpty then
    IO.eprintln "leanllvm-json-entry: the nblk arm has no corpus masks"
    e.failures.modify (· + 1)
  else
    let masks := (List.range 1025).map fun i => all[i % all.length]!
    e.row "arm:nblk" "masks1025" masks 0 0 rows

/-! ### The `ent` word's rows -/

/-- One row of the `ent` word: the block's two halves, the classifier state it
is read in, the previous block's top-lane carry, the document length and the
block's index in it. -/
structure EntRow where
  label : String
  lo : Block32
  hi : Block32
  st : ClassState
  prevS : Bool
  n : Nat
  bi : Nat

/-- A row of bytes as a call's two 32-byte halves, zero-padded at the end. -/
def halves (bs : List UInt8) : Block32 × Block32 :=
  let padded := bs ++ List.replicate 64 0
  ((fun i : Fin 32 => padded.getD i.1 0),
   (fun i : Fin 32 => padded.getD (i.1 + 32) 0))

/-- The rows of a document: one per 64-byte block, from block 0, with the state
and the carry threaded block to block.  `n` is the document's byte length and
`bi` the block's index, so `n - 64 * bi` is the block's own window. -/
def docRows (tag : String) (n : Nat) (bytes : List UInt8) : List EntRow :=
  let count := (bytes.length + 63) / 64
  let rec go (bi : Nat) (st : ClassState) (prevS : Bool) (acc : List EntRow) :
      List EntRow :=
    if bi ≥ count then acc.reverse
    else
      let bs := (bytes.drop (64 * bi)).take 64
      let (lo, hi) := halves bs
      let s := specScalar64 lo hi st
      let row : EntRow :=
        { label := s!"{tag}:blk{bi}", lo := lo, hi := hi, st := st,
          prevS := prevS, n := n, bi := bi }
      let next := (classWindow (List.ofFn hi) ((classWindow (List.ofFn lo) st).carry)).carry
      go (bi + 1) next ((s >>> 63) == 1) (row :: acc)
  go 0 ⟨false, false⟩ false []

/-- The three class blocks: a non-structural byte inside a string, a backslash
outside one, and an escaped quote outside one.  Each is a block in which the
measured rule and the eight-byte structural set disagree. -/
def classBlocks : List (String × List UInt8) :=
  [ ("string-interior",
     [0x22, 0x61, 0x78, 0x22] ++ List.replicate 60 (0x78 : UInt8)),
    ("backslash-outside-string",
     [0x5C, 0x78] ++ List.replicate 62 (0x78 : UInt8)),
    ("escaped-quote-outside-string",
     [0x5C, 0x22, 0x78] ++ List.replicate 61 (0x78 : UInt8)) ]

def classRows : List EntRow :=
  classBlocks.map fun (name, bs) =>
    let (lo, hi) := halves bs
    { label := s!"class:{name}", lo := lo, hi := hi, st := ⟨false, false⟩,
      prevS := false, n := 64, bi := 0 }

/-- The fixed-seed arm: 32 blocks of eight splitmix64 words from the printed
seed, so the states and carries thread over a stream the specification did not
choose. -/
def armSeedLabel : String := "arm:seed243f6a8885a308d3"

def armEntBytes : List UInt8 :=
  (List.range 32).flatMap fun i =>
    (List.range 8).flatMap fun w =>
      let (_, z) := splitmixNext
        (randomSeed + UInt64.ofNat (8 * i + w) * splitmixGamma)
      natToBytes z.toNat 8

def entLine (r : EntRow) : String :=
  let qm := specQuote64 r.lo r.hi r.st
  let sm := specDelimiter64 r.lo r.hi r.st
  let im := specInString64 r.lo r.hi r.st
  let ws := specSpace64 r.lo r.hi r.st
  let s := specScalar64 r.lo r.hi r.st
  let ent := entryMask64 r.lo r.hi r.st r.prevS
  let tailed := ent &&& limMask (r.n - r.bi * 64)
  s!"{r.label} {qm.toNat} {sm.toNat} {im.toNat} {ws.toNat} \
     {if r.prevS then 1 else 0} {r.n} {r.bi} \
     {renderHex 16 s.toNat} {renderHex 16 ent.toNat} {renderHex 16 tailed.toNat}"

def runEnt (files : List CorpusFile) : IO UInt32 := do
  for cf in files do
    match cf.source with
    | none =>
        IO.eprintln s!"leanllvm-json-entry: '{cf.path}' names no source document"
        return 2
    | some src =>
        let bytes ← try
            IO.FS.readFile src
          catch e =>
            IO.eprintln s!"leanllvm-json-entry: cannot read '{src}': {e}"
            return 2
        for r in docRows s!"corpus:{cf.path}" bytes.utf8ByteSize (bytes.toUTF8.toList) do
          IO.println (entLine r)
  for r in classRows do
    IO.println (entLine r)
  for r in docRows armSeedLabel 2048 armEntBytes do
    IO.println (entLine r)
  return 0

/-! ### Arguments -/

structure Options where
  corpus : List String := []
  arms : Bool := false
  expect : Option String := none
  ent : Bool := false
  deriving Inhabited

def usage : String :=
  "usage: leanllvm-json-entry [--corpus <path> ...] [--arms] [--expect <file>]\n" ++
  "       leanllvm-json-entry --ent --corpus <file> ..."

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      if o.ent then
        match o.corpus with
        | [] => .error "--ent needs at least one --corpus file"
        | _ => .ok o
      else
        match o.corpus, o.arms with
        | [], false => .error "one of --corpus or --arms is required"
        | _, _ => .ok o
  | "--corpus" :: p :: rest => parseArgsAux { o with corpus := o.corpus ++ [p] } rest
  | "--corpus" :: [] => .error "missing path after --corpus"
  | "--arms" :: rest => parseArgsAux { o with arms := true } rest
  | "--expect" :: f :: rest => parseArgsAux { o with expect := some f } rest
  | "--expect" :: [] => .error "missing file after --expect"
  | "--ent" :: rest => parseArgsAux { o with ent := true } rest
  | arg :: _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

/-- Read every `--corpus` file. -/
def readCorpora (paths : List String) : IO (Except String (List CorpusFile)) := do
  let mut files : List CorpusFile := []
  for p in paths do
    match ← readCorpus p with
    | .error err => return .error err
    | .ok cf => files := files ++ [cf]
  return .ok files

def runRows (o : Options) (files : List CorpusFile) : IO UInt32 := do
  let expected ← match o.expect with
    | none => pure (none : Option (Array String))
    | some file =>
        let text ← try
            IO.FS.readFile file
          catch e =>
            IO.eprintln s!"leanllvm-json-entry: cannot read '{file}': {e}"
            return 2
        pure (some (text.splitOn "\n" |>.toArray))
  let index ← IO.mkRef 0
  let printed ← IO.mkRef 0
  let failures ← IO.mkRef 0
  let e : Emitter := { expected := expected, index := index, printed := printed,
                       failures := failures }
  let rows := pos8AllRows
  emitCorpus e files rows
  if o.arms then
    let all := files.flatMap (·.masks)
    emitArms e all rows
  let fails ← failures.get
  if fails = 0 then
    match expected, o.expect with
    | some arr, some file =>
        let got ← printed.get
        let want := if arr.size > 0 ∧ arr[arr.size - 1]! = "" then arr.size - 1 else arr.size
        if got = want then
          IO.eprintln s!"ok: {got} row(s) agree with '{file}'"
          return 0
        else
          IO.eprintln s!"mismatch: {want} row(s) expected, {got} printed"
          return 1
    | _, _ =>
        IO.eprintln s!"ok: {← printed.get} row(s)"
        return 0
  else
    IO.eprintln s!"leanllvm-json-entry: {fails} row(s) disagree"
    return 1

def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
      IO.eprintln s!"leanllvm-json-entry: {e}"
      IO.eprintln usage
      return 1
  | .ok o =>
      match ← readCorpora o.corpus with
      | .error err =>
          IO.eprintln s!"leanllvm-json-entry: {err}"
          return 2
      | .ok files =>
          if o.ent then runEnt files else runRows o files

end JsonEntryMain

/-- The executable's entry point. -/
def main (args : List String) : IO UInt32 := JsonEntryMain.run args
