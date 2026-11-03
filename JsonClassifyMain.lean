/-
`leanllvm-json-classify`: the JSON block classifier over corpus texts.

The classifier is not re-implemented here.  Each 32-byte window is staged in
memory at `blockBase` and `classify32Function` — the AST that
`LeanLLVM/Vellum/JsonClassifyIR.lean` pins to
`probes/install/ir/json-classify.candidate.ll` and proves equal to the block
layer's mask on every readable block — is run over it with `runFuel` under the
repository's semantics.  The printed mask is that run's `i32` return value, so
the route exercises the certified body rather than the scalar specification
`maskOfList` beside it.

Three modes:

* `--manifest <file>` reads `<path>\t<offset>\t<mask>` rows, classifies the
  window at `offset` in `<path>`, prints one `<path>\t<offset>\t<mask>` line per
  row, and exits nonzero with a `mismatch: ...` line on stderr when any row
  disagrees.  Paths are used as given, relative to the working directory.
  Masks are `0x` followed by exactly eight lowercase hex digits.  Empty lines
  and lines beginning with `#` are ignored.
* `--windows <path>` (repeatable) classifies every 32-byte window of every
  regular file the paths name — a directory contributes its files directly
  inside it, in name order — with offsets ascending, and prints the same
  three-column form.  A file shorter than 32 bytes contributes no window.
* `--emit-block` writes the route's 32-byte mixed block, with no trailing
  newline, so `tests/json-classify/check.sh` can compare the committed
  `tests/json-classify/mixed.block` with it byte for byte.

Exit status: `0` when every window was classified and every expectation held,
`1` on a mismatch, a malformed row, or a usage error, `2` when an input cannot
be read.  A window that runs past the end of its file is a mismatch, not a
skipped row.
-/
import LeanLLVM

open LeanLLVM
open LeanLLVM.Vellum.JsonClassifyIR

/-! ### Running the certified body -/

/-- The address a window is staged at.  Non-zero, because `initState` reserves
address `0` for `null`, and larger than the allocator's first page so a read at
the block is not anchored at the start of memory. -/
def blockBase : Nat := 4096

/-- Memory holding a block's bytes, one cell per byte, in the layout
`readBytes` consumes. -/
def blockMem (block : List UInt8) : Mem :=
  block.zipIdx.map fun (b, i) => (blockBase + i, b)

/-- The mask the emitted classifier body returns for a block.  `none` when the
body does not return an `i32`: an unresolved step is `ub`, and that is a defect
in the body rather than an expectation about the block. -/
def classifyBlock (block : List UInt8) : Option (BitVec 32) :=
  match runFuel noCalls 10000 classify32Function
      { (initState classify32Function [.ptr blockBase]) with mem := blockMem block } with
  | some (.ret (some (.int 32 v)) _) => some v
  | _ => none

/-- The mixed block the route discriminates with: structural bytes, JSON
whitespace and ordinary content interleaved.  Byte 0 is `[` (bit 0 set) and
byte 31 is `q` (bit 31 clear), and bytes 4 and 17 are `,`, so removing the
comma class from the classifier changes this block's mask.  `--emit-block`
writes these bytes, and `tests/json-classify/check.sh` requires the committed
`tests/json-classify/mixed.block` to equal them. -/
def mixedBlockBytes : List UInt8 :=
  [ 0x5B, 0x20, 0x20, 0x31, 0x2C, 0x20, 0x32, 0x5D,
    0x0A, 0x20, 0x22, 0x61, 0x22, 0x20, 0x3A, 0x20,
    0x78, 0x2C, 0x20, 0x79, 0x09, 0x7A, 0x7B, 0x20,
    0x22, 0x5C, 0x6B, 0x22, 0x7D, 0x0D, 0x20, 0x71 ]

/-- Write the mixed block's bytes, with no trailing newline, so the output can
be compared byte for byte with the committed fixture. -/
def runEmitBlock : IO UInt32 := do
  IO.print (String.ofList (mixedBlockBytes.map fun b => Char.ofNat b.toNat))
  return 0

/-! ### Rendering and parsing masks -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (0x30 + n) else Char.ofNat (0x57 + n)

/-- `0x` and eight lowercase hex digits: the form the manifest writes. -/
def renderMask (v : BitVec 32) : String :=
  let n := v.toNat
  "0x" ++ String.ofList ((List.range 8).map fun i => hexDigit (n / 16 ^ (7 - i) % 16))

def hexDigitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 0x30)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 0x61 + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 0x41 + 10)
  else none

/-- A hex mask, with or without a `0x`/`0X` prefix. -/
def parseHexNat (s : String) : Option Nat :=
  let s := if s.startsWith "0x" ∨ s.startsWith "0X" then (s.drop 2).toString else s
  if s.isEmpty then none
  else
    s.toList.foldl
      (fun acc c => acc.bind fun n => (hexDigitVal c).map fun d => n * 16 + d)
      (some 0)

/-- A mask column: a hex number that fits in 32 bits. -/
def parseMask (s : String) : Option (BitVec 32) :=
  match parseHexNat s with
  | some n => if n < 2 ^ 32 then some (BitVec.ofNat 32 n) else none
  | none => none

/-! ### Reading windows -/

/-- The 32 bytes at `offset` in `path`, or the reason they are not there. -/
def readWindow (path : String) (offset : Nat) : IO (Except String (List UInt8)) := do
  let bytes ← try
      IO.FS.readBinFile path
    catch e =>
      return .error s!"cannot read '{path}': {e}"
  if offset + 32 > bytes.size then
    return .error s!"the window {offset}…{offset + 31} is past the end of '{path}' \
      ({(bytes.size : Nat)} bytes)"
  return .ok (bytes.extract offset (offset + 32)).toList

/-! ### The manifest mode -/

/-- One expectation: a window and the mask the classifier must return for it. -/
structure Row where
  path : String
  offset : Nat
  mask : BitVec 32
  deriving Repr

def splitLine (line : String) : List String := line.splitOn "\t"

/-- Parse one manifest row. -/
def parseRow (line : String) : Except String Row :=
  match splitLine line with
  | [path, offsetText, maskText] =>
      match offsetText.toNat?, parseMask maskText with
      | some offset, some mask => .ok { path, offset, mask }
      | none, _ => .error s!"malformed manifest line (offset '{offsetText}' is not a number): '{line}'"
      | _, none => .error s!"malformed manifest line (mask '{maskText}' is not a 32-bit hex number): '{line}'"
  | _ => .error s!"malformed manifest line (want three tab-separated columns): '{line}'"

/-- Classify one window and report it.  Returns `true` when the expectation
held. -/
def checkRow (row : Row) : IO Bool := do
  match ← readWindow row.path row.offset with
  | .error e =>
      IO.eprintln s!"mismatch: {row.path}: offset {row.offset}: {e}"
      return false
  | .ok bytes =>
      match classifyBlock bytes with
      | none =>
          IO.eprintln s!"mismatch: {row.path}: offset {row.offset}: \
            the classifier did not return an i32"
          return false
      | some got =>
          IO.println s!"{row.path}\t{row.offset}\t{renderMask got}"
          if got = row.mask then
            return true
          else
            IO.eprintln s!"mismatch: {row.path}: offset {row.offset}: \
              expected mask {renderMask row.mask}, got {renderMask got}"
            return false

/-- Run every row of a manifest. -/
def runManifest (manifest : String) : IO UInt32 := do
  let text ← try
      IO.FS.readFile manifest
    catch e =>
      IO.eprintln s!"leanllvm-json-classify: cannot read '{manifest}': {e}"
      return 2
  let mut rows : Nat := 0
  let mut failures : Nat := 0
  for line in text.splitOn "\n" do
    if line.isEmpty ∨ line.startsWith "#" then continue
    rows := rows + 1
    match parseRow line with
    | .error e =>
        IO.eprintln s!"mismatch: {e}"
        failures := failures + 1
    | .ok row =>
        let ok ← checkRow row
        if !ok then
          failures := failures + 1
  if failures = 0 then
    IO.eprintln s!"ok: {rows} row(s) agree with the manifest"
    return 0
  else
    IO.eprintln s!"leanllvm-json-classify: {failures} of {rows} row(s) disagree"
    return 1

/-! ### The window enumeration mode -/

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

/-- Classify every 32-byte window of every file the paths name. -/
def runWindows (paths : List String) : IO UInt32 := do
  let mut files : List String := []
  for p in paths do
    match ← expandPath p with
    | .error e =>
        IO.eprintln s!"leanllvm-json-classify: {e}"
        return 2
    | .ok fs => files := files ++ fs
  let mut windows : Nat := 0
  let mut failures : Nat := 0
  for path in files do
    let bytes ← try
        IO.FS.readBinFile path
      catch e =>
        IO.eprintln s!"leanllvm-json-classify: cannot read '{path}': {e}"
        return 2
    for offset in List.range (bytes.size - 31) do
      let block := (bytes.extract offset (offset + 32)).toList
      match classifyBlock block with
      | none =>
          IO.eprintln s!"mismatch: {path}: offset {offset}: \
            the classifier did not return an i32"
          failures := failures + 1
      | some got =>
          IO.println s!"{path}\t{offset}\t{renderMask got}"
          windows := windows + 1
  if failures = 0 then
    IO.eprintln s!"ok: {windows} window(s) classified"
    return 0
  else
    IO.eprintln s!"leanllvm-json-classify: {failures} window(s) unclassified"
    return 1

/-! ### Arguments -/

structure Options where
  manifest : Option String := none
  windows : List String := []
  emitBlock : Bool := false
  deriving Inhabited

def usage : String :=
  "usage: leanllvm-json-classify --manifest <file> | --windows <path> [--windows <path> ...]\n" ++
  "       leanllvm-json-classify --emit-block"

def parseArgsAux (o : Options) : List String → Except String Options
  | [] =>
      if o.emitBlock then
        match o.manifest, o.windows with
        | none, [] => .ok o
        | _, _ => .error "--emit-block cannot be combined with --manifest or --windows"
      else
        match o.manifest, o.windows with
        | some _, [] => .ok o
        | none, _ :: _ => .ok o
        | none, [] => .error "one of --manifest, --windows or --emit-block is required"
        | some _, _ :: _ => .error "--manifest and --windows are exclusive"
  | "--manifest" :: file :: rest => parseArgsAux { o with manifest := some file } rest
  | "--manifest" :: [] => .error "missing file after --manifest"
  | "--windows" :: p :: rest => parseArgsAux { o with windows := o.windows ++ [p] } rest
  | "--windows" :: [] => .error "missing path after --windows"
  | "--emit-block" :: rest => parseArgsAux { o with emitBlock := true } rest
  | arg :: _ => .error s!"unknown argument '{arg}'"

def parseArgs (args : List String) : Except String Options :=
  parseArgsAux {} args

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .ok { manifest := some manifest, windows := [], emitBlock := false } => runManifest manifest
  | .ok { manifest := none, windows := paths, emitBlock := false } => runWindows paths
  | .ok { manifest := none, windows := [], emitBlock := true } => runEmitBlock
  | .ok _ =>
      IO.eprintln "leanllvm-json-classify: one of --manifest, --windows or --emit-block is required"
      IO.eprintln usage
      return 1
  | .error e =>
      IO.eprintln s!"leanllvm-json-classify: {e}"
      IO.eprintln usage
      return 1
