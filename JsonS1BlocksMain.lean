/-
`leanllvm-json-s1-blocks`: the stage-1 block body over documents, both arms.

The kernel is not re-implemented here.  Each row stages a document padded to a
whole number of sixty-four-byte blocks at **offset 1** of a buffer — a
misaligned base — an `ent` array of `8 * blocks` bytes pre-filled with `0xA5`, a
sixty-four-byte `xp` region pre-filled with `0xA5`, an eight-byte `nxp` word
staged at zero (the cursor the first escape-list call reads) and a sixteen-byte
`xcarry` pair staged at zero (the all-false carry), and runs `s1BlocksFunction` —
the AST `LeanLLVM/Refinement/JsonS1BlocksIR.lean` pins to
`probes/install/ir/json-s1-blocks.candidate.ll` — with `runFuel` under the
repository's semantics.  The classifier's two intrinsics are `s1Calls`; the
escape list is the unit's own pinned body, resolved at
`Γ_escape_positions`'s budget through `envForUnit`, so the gate-on arm runs the
escape body rather than a model of it.  The words printed are read back out of
memory, so the route exercises the body rather than the specification beside it.

A row is tab-separated:

    <source> <label> <arm> <blocks> <touched> <ent words…> <nxp> <xp bytes>
    <xcarry lo> <xcarry hi> <ret>

`arm` is `0` (gate off) or `2` (escape list selected); `blocks` is
`(length + 63) / 64` and there are that many `ent` words, one per block, each
`0x` and sixteen lowercase hex digits; `nxp`, the two carry words and the
return word are in the same form; `xp bytes` is the first sixty-four bytes of
the position stream as one hundred and twenty-eight lowercase hex digits.
`touched` is `1` exactly when `xp` is still sixty-four `0xA5` bytes, `nxp` is
still zero and both carry words are still zero — the staged state — so the
gate-off arm's row must read `touched = 1`, and a gate-on row whose block has
an escape position reads `0`.  `ret` is the unit's ASCII probe, read from the
value the body returns: `1` when every document byte is below `0x80`, and `1`
for an empty document.  It is the last column so that the `ent` words stay the
first `0x` fields.  The label carries the document's length as `len<n>` so a
run's row set can be checked against the documents it names.

The rows, in order, each document once per arm, arm ascending:

1. the mixed sixty-four-byte block, `source` = `mixed`, `label` = `len64`;
2. the corpus files named by `--corpus`, each whole file as one document, in
   the order given (a directory contributes the files directly inside it, in
   name order);
3. `arm:byte`: for each byte position `0…63` and value `0…255`, a sixty-four
   byte document of `0x78` with that value at that position;
4. `arm:short`: the first `1…65` bytes of a fixed splitmix64 stream, so the
   peeled tail block is walked at every remainder;
5. `arm:alphabet`: every four-byte sequence over the eight-symbol escape
   alphabet `22 5C 2C 7B 01 20 61 0A` — the unescaped quote, the backslash,
   two structural bytes, a control byte, whitespace, ordinary content and a
   newline;
6. `arm:random`: five hundred and twelve documents from splitmix64 seeded at
   `0x243F6A8885A308D3`, length `1 + (37 * i) mod 128`, so both the full-block
   loop and the tail are exercised at varied lengths.

Modes:

* `--corpus <path>` (repeatable) and `--arms` select the rows; a directory
  contributes the files directly inside it, in name order.
* `--expect <file>` compares each printed row against the same columns written
  in `<file>`, prints `mismatch: <source>\t<label>: expected …, got …` on
  stderr, and exits 1 when any row disagrees — the rows themselves are still
  printed, so the disagreement is the expectation's and not the body's.
* `--emit-block` writes the mixed block's sixty-four bytes with no trailing
  newline.

Exit status: `0` when every row was produced (and every expectation held), `1`
on a mismatch or a usage error, `2` when an input cannot be read.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonS1BlocksIR
import LeanLLVM.Refinement.JsonS1MasksIR
import LeanLLVM.Refinement.JsonEscapeListContract

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls)
open LeanLLVM.Refinement.JsonEscapeIR (escapeListFunction escapeListCalls)

namespace JsonS1BlocksMain

/-! ### The call environment

The block body calls the classifier's two intrinsics and `leanllvm_json_escape_list`.
The first are `s1Calls`; the second is resolved to its own pinned body at the
record's budget, which is the record's fuel function and depends only on the
three masks the call passes. -/

/-- The block unit's call environment: the mask unit's intrinsics, the ASCII
probe's zero test, and the escape list at `Γ_escape_positions`'s budget.

`llvm.x86.avx.ptestz.256` is the parser's `i32 (<4 x i64>, <4 x i64>)` shape,
bound to `BitLanes.ptestz` over the two operands packed little-endian into one
256-bit word, as the UTF-8 stage's environment binds it. -/
def blocksCalls : Calls :=
  fun callee args mem next =>
    if callee = "leanllvm_json_escape_list" then
      envForUnit "leanllvm_json_escape_list"
        (Γ_escape_positions 0 escapePositionsBudget)
        (escapeListCalls Γ_xl_batch) escapeListFunction callee args mem next
    else
      match callee, args with
      | "llvm.x86.avx.ptestz.256", [.vec 4 64 a, .vec 4 64 b] =>
          some { ret := .int 32 (BitLanes.ptestz (BitVec.ofNat 256 (packLanes a))
                (BitVec.ofNat 256 (packLanes b))), mem := mem, next := next }
      | _, _ => s1Calls callee args mem next

/-! ### Staging one row -/

/-- The document's base: offset 1 of the staging buffer. -/
def docAddr : Nat := 8193

/-- The `ent` array's address. -/
def entAddr : Nat := 16384

/-- The position stream's address. -/
def xpAddr : Nat := 32768

/-- The position count's address. -/
def nxpAddr : Nat := 40960

/-- The escape list's carry pair's address. -/
def xcarryAddr : Nat := 41024

/-- The scratch sentinel, so a store the body does not make reads back as a
sentinel rather than as a stale word. -/
def sentinel : UInt8 := 0xA5

/-- Control steps a row is run for.  The documents are at most two blocks. -/
def fuel : Nat := 100000

/-- The blocks a document of length `n` occupies: `(n + 63) >> 6`. -/
def blocksOf (n : Nat) : Nat := (n + 63) / 64

/-- The document padded with zeroes to a whole number of blocks. -/
def padded (bs : List UInt8) : List UInt8 :=
  bs ++ List.replicate (64 * blocksOf bs.length - bs.length) 0

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- The memory a row is run from. -/
def stagingMem (bs : List UInt8) : Mem :=
  bytesAt docAddr (padded bs) ++
    bytesAt entAddr (List.replicate (8 * blocksOf bs.length) sentinel) ++
    bytesAt xpAddr (List.replicate 64 sentinel) ++
    bytesAt nxpAddr (List.replicate 8 0) ++
    bytesAt xcarryAddr (List.replicate 16 0)

/-- One row's observation, read back out of memory and the return value.  `ret`
is the unit's ASCII probe: `1` when every document byte is below `0x80`. -/
structure Obs where
  ent : List Nat
  xp : List UInt8
  nxp : Nat
  carryLo : Nat
  carryHi : Nat
  touched : Bool
  ret : Nat
  deriving Inhabited

/-- The `k`-th little-endian 64-bit word of a byte list. -/
def wordAt (bs : List UInt8) (k : Nat) : Nat :=
  bytesToNat ((bs.drop (8 * k)).take 8)

/-- The staged state: `xp` still sentinel, `nxp` still zero, both carry words
still zero.  A gate-off row that writes either region cannot read `1`. -/
def isStaged (xp : List UInt8) (nxp carryLo carryHi : Nat) : Bool :=
  xp == List.replicate 64 sentinel && nxp == 0 && carryLo == 0 && carryHi == 0

/-- Run one document under one arm.  `none` when the body does not return a
64-bit word or leaves a staged region unreadable — a defect in the body, not an
expectation about a document. -/
def runRow (bs : List UInt8) (arm : Nat) : Option Obs :=
  let bc := blocksOf bs.length
  match runFuel blocksCalls fuel s1BlocksFunction
      { (initState s1BlocksFunction
          [.ptr docAddr, .int 64 bs.length, .ptr entAddr, .ptr xpAddr,
           .ptr nxpAddr, .ptr xcarryAddr, .int 64 arm]) with
        mem := stagingMem bs } with
  | some (.ret (some (.int 64 r)) mem) =>
      match readBytes mem entAddr (8 * bc), readBytes mem xpAddr 64,
            readBytes mem nxpAddr 8, readBytes mem xcarryAddr 16 with
      | some e, some xp, some nx, some xc =>
          let ent := (List.range bc).map (fun k => wordAt e k)
          let nxp := bytesToNat nx
          let lo := bytesToNat (xc.take 8)
          let hi := bytesToNat (xc.drop 8)
          some { ent := ent, xp := xp, nxp := nxp, carryLo := lo, carryHi := hi,
                 touched := isStaged xp nxp lo hi, ret := r.toNat }
      | _, _, _, _ => none
  | _ => none

/-! ### Rendering -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- `0x` and sixteen lowercase hex digits. -/
def renderWord (v : Nat) : String :=
  "0x" ++ String.ofList ((List.range 16).map fun i => hexDigit (v / 16 ^ (15 - i) % 16))

/-- Two lowercase hex digits. -/
def renderByte (v : Nat) : String :=
  String.ofList [hexDigit (v / 16 % 16), hexDigit (v % 16)]

/-- `n` bytes as lowercase hex, no prefix. -/
def renderBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b => renderByte b.toNat)

/-! ### The mixed block -/

/-- The route's mixed sixty-four-byte block: escaped and unescaped quotes,
backslash runs of length one, two and three, all six delimiters, all four
whitespace bytes, control bytes with and without the whitespace class, `0x7F`,
and ordinary content.  It is the mask route's mixed block, byte for byte. -/
def mixedBlock : List UInt8 :=
  [ 0x22, 0x6B, 0x5C, 0x22, 0x2C, 0x20, 0x31, 0x5D,
    0x0A, 0x09, 0x0D, 0x5C, 0x5C, 0x22, 0x3A, 0x78,
    0x22, 0x61, 0x22, 0x7B, 0x7D, 0x5B, 0x5D, 0x2C,
    0x20, 0x01, 0x1F, 0x7F, 0x22, 0x5C, 0x74, 0x22,
    0x5C, 0x6E, 0x22, 0x2C, 0x09, 0x5C, 0x22, 0x3A,
    0x64, 0x5B, 0x5D, 0x7B, 0x7D, 0x20, 0x0D, 0x30,
    0x22, 0x5C, 0x5C, 0x5C, 0x22, 0x2C, 0x76, 0x20,
    0x09, 0x0A, 0x22, 0x7A, 0x1F, 0x79, 0x5C, 0x22 ]

/-! ### The generated documents -/

/-- The escape alphabet: the bytes the escape list's word can select between —
the unescaped quote, the backslash, two structural bytes, a control byte,
whitespace, ordinary content and a newline. -/
def alphabet : List UInt8 :=
  [0x22, 0x5C, 0x2C, 0x7B, 0x01, 0x20, 0x61, 0x0A]

/-- Eight symbols, four lanes. -/
def alphabetCount : Nat := 8 ^ 4

/-- The four-byte document a sequence index writes. -/
def alphabetSeq (i : Nat) : List UInt8 :=
  [ alphabet.getD (i % 8) 0,
    alphabet.getD (i / 8 % 8) 0,
    alphabet.getD (i / 64 % 8) 0,
    alphabet.getD (i / 512 % 8) 0 ]

/-- The documents the random arm runs. -/
def randomCount : Nat := 512

/-- The short arm's longest document: one block and one byte. -/
def shortCount : Nat := 65

def splitmixGamma : UInt64 := 0x9E3779B97F4A7C15
def randomSeed : UInt64 := 0x243F6A8885A308D3
def shortSeed : UInt64 := 0x13198A2E03707344

/-- One splitmix64 step: the next state and its output. -/
def splitmixNext (x : UInt64) : UInt64 × UInt64 :=
  let x' := x + splitmixGamma
  let z := (x' ^^^ (x' >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (x', z ^^^ (z >>> 31))

/-- The first `words` outputs of a splitmix64 stream started at `x`. -/
def splitmixWords (x : UInt64) (words : Nat) : List UInt64 :=
  let rec go (x : UInt64) : Nat → List UInt64 → List UInt64
    | 0, acc => acc.reverse
    | n + 1, acc =>
        let (x', w) := splitmixNext x
        go x' n (w :: acc)
  go x words []

/-- The little-endian bytes of a word list. -/
def wordsToBytes (ws : List UInt64) : List UInt8 :=
  ws.flatMap fun w =>
    (List.range 8).map fun k => UInt8.ofNat (w.toNat / 256 ^ k % 256)

/-- A document of `n` bytes from a splitmix64 stream, at one block's worth of
words per block. -/
def randomDoc (seed : UInt64) (n : Nat) : List UInt8 :=
  (wordsToBytes (splitmixWords seed (8 * blocksOf n))).take n

/-- The short arm's document at length `n`: a fixed stream's first `n` bytes,
so lengths `1…65` walk the peeled tail at every remainder. -/
def shortDoc (n : Nat) : List UInt8 :=
  (wordsToBytes (splitmixWords shortSeed 16)).take n

/-- The random arm's document at index `i` and its length. -/
def randomLen (i : Nat) : Nat := 1 + (37 * i) % 128

def randomDocAt (i : Nat) : List UInt8 :=
  randomDoc (randomSeed + UInt64.ofNat i * splitmixGamma) (randomLen i)

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

/-- The line a row's observation prints.  The ASCII probe is the last column so
that the `ent` words stay the first `0x` fields of the row. -/
def renderRow (source label : String) (arm blocks : Nat) (o : Obs) : String :=
  let flag (b : Bool) : String := if b then "1" else "0"
  s!"{source}\t{label}\t{arm}\t{blocks}\t{flag o.touched}\t\
    {String.intercalate "\t" (o.ent.map renderWord)}\t\
    {renderWord o.nxp}\t{renderBytes o.xp}\t\
    {renderWord o.carryLo}\t{renderWord o.carryHi}\t{renderWord o.ret}"

/-- Print one document's row under one arm. -/
def Emitter.row (e : Emitter) (source label : String) (arm : Nat)
    (bs : List UInt8) : IO Unit := do
  let blocks := blocksOf bs.length
  match runRow bs arm with
  | some o => e.emit source label (renderRow source label arm blocks o)
  | none =>
      IO.eprintln s!"mismatch: {source}\t{label}: the body did not return its \
        valued result and leave every staged region"
      e.failures.modify (· + 1)

/-- Print one document under both arms, gate off then gate on. -/
def Emitter.document (e : Emitter) (source label : String) (bs : List UInt8) : IO Unit := do
  e.row source label 0 bs
  e.row source label 2 bs

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
  e.document "mixed" "len64" mixedBlock

/-- Each corpus file as one document. -/
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
    e.document path s!"len{bytes.size}" bytes.toList
  return .ok ()

/-- The byte sweep: every value at every lane position of a sixty-four-byte
document. -/
def emitByteArm (e : Emitter) : IO Unit := do
  for pos in List.range 64 do
    for v in List.range 256 do
      let block := (List.replicate 64 (0x78 : UInt8)).set pos (UInt8.ofNat v)
      e.document "arm:byte" s!"pos{pos}/val{renderByte v}/len64" block

/-- The short arm: lengths `1…65`, the peeled tail at every remainder. -/
def emitShortArm (e : Emitter) : IO Unit := do
  for n in List.range shortCount do
    let len := n + 1
    e.document "arm:short" s!"len{len}" (shortDoc len)

/-- Every four-byte sequence over the escape alphabet. -/
def emitAlphabetArm (e : Emitter) : IO Unit := do
  for i in List.range alphabetCount do
    let seq := alphabetSeq i
    e.document "arm:alphabet" s!"{renderBytes seq}/len4" seq

/-- The fixed-seed random arm, at varied lengths. -/
def emitRandomArm (e : Emitter) : IO Unit := do
  for i in List.range randomCount do
    e.document "arm:random" s!"idx{i}/len{randomLen i}" (randomDocAt i)

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
  "usage: leanllvm-json-s1-blocks [--corpus <path> ...] [--arms] [--expect <file>]\n" ++
  "       leanllvm-json-s1-blocks --emit-block"

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
            IO.eprintln s!"leanllvm-json-s1-blocks: cannot read '{file}': {e}"
            return 2
        pure (some (text.splitOn "\n" |>.toArray))
  let index ← IO.mkRef 0
  let failures ← IO.mkRef 0
  let e : Emitter := { expected := expected, index := index, failures := failures }
  emitMixed e
  match ← emitCorpus e o.corpus with
  | .error err =>
      IO.eprintln s!"leanllvm-json-s1-blocks: {err}"
      return 2
  | .ok () => pure ()
  if o.arms then
    emitByteArm e
    emitShortArm e
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
    IO.eprintln s!"leanllvm-json-s1-blocks: {fails} row(s) disagree"
    return 1

/-- Dispatch one command line.  Named `run` rather than `main`: a `main`
inside this namespace leaves the module without a root-level one, and the
linked `Lean` library's own front end would answer `--emit-block` instead. -/
def run (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .ok { emitBlock := true, corpus := [], arms := false, expect := none } => runEmitBlock
  | .ok o => runRows o
  | .error e =>
      IO.eprintln s!"leanllvm-json-s1-blocks: {e}"
      IO.eprintln usage
      return 1

end JsonS1BlocksMain

/-- The executable's entry point. -/
def main (args : List String) : IO UInt32 := JsonS1BlocksMain.run args
