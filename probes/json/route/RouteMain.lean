/-
The JSON pipeline's call route: a standalone Lean program that stages the
document the record demands, calls `leanllvm_json_pipeline` through the C
adapter in `shim.c`, and prints what the caller observes.

The document decision is the library's: `LeanLLVM.JsonKernelDomain.admission`,
imported here rather than transcribed, so the probe's shell and the certified
domain are one predicate.  `admission` admits a document to the native pipeline;
for every document it does not admit, the scalar reference parser answers —
`parseBytes` from the library, with `decodeTape` its value on acceptance — and
the program prints that answer as the fallback's.  There is no second scan and
no pre-filter: a document either takes the fast path or is answered once by the
fallback.

The staging is `LeanLLVM.JsonCallRoute.stagedStore`'s shape, in bytes: the
window is `[0,0,0] ++ doc ++ zero padding ++ 32` readable tail bytes, and the
four growing buffers are sized at the record's capacities.  The POS8 table is
not staged here: the entry unit reads its own static table, and the adapter's
setup fills it (`route_init` in `shim.c`), so this program has no initialiser to
call and no dummy return to consume.

The adapter returns a tagged result for the fast path: the observation's six
words and its two payloads for the two classes where the object ran, and a tag
naming the class otherwise — an unmet staging precondition before the call, an
allocation failure, or a returned cursor past its capacity.  The last three are
reported on stderr with the failed precondition and the expected and observed
numbers, at exit 3, 4 and 5.

The three outcomes are distinct in the output: `verdict=` is the fast path's
observation on an admitted document, `fallback=accepted` is the reference
parser's acceptance of a document outside the pilot's domain, and
`refused: ...` on stderr (exit 2) is the reference's refusal of one.
-/
import LeanLLVM.JsonKernelDomain
import LeanLLVM.JSON.Parse

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement

/-- The adapter: it validates the staging, copies the caller's `ByteArray`s into
the object's ABI, calls `leanllvm_json_pipeline`, and returns the tagged result
`shim.c` defines. -/
@[extern "leanllvm_json_route"]
opaque route (window : ByteArray) (n : UInt64)
  (sc mkSlot entw : ByteArray) (ep : ByteArray) (epcap : UInt64) (nk : ByteArray)
  (xp : ByteArray) (xpcap : UInt64) (nxp xcarry dst : ByteArray)
  (dstcap : UInt64) (ndst : ByteArray) (ev : ByteArray) (evcap : UInt64)
  (nev err : ByteArray) (arm : UInt64) : ByteArray

def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))

def blocks (n : Nat) : Nat := (n + 63) / 64

def usage : String := "usage: leanllvm-json-route --doc <file>"

def hexByte (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def hex (bs : ByteArray) : String :=
  String.join (bs.toList.map hexByte)

def be64 (bs : ByteArray) (i : Nat) : Nat :=
  -- little-endian word at byte offset `i`
  let get (k : Nat) := (bs.toList.getD (i + k) 0).toNat
  get 0 + 256 * get 1 + 65536 * get 2 + 16777216 * get 3 +
    4294967296 * (get 4 + 256 * get 5 + 65536 * get 6 + 16777216 * get 7)

/-! ### The fallback's report

The reference parser's refusal, in the same wording the route has always used
for the character-policy class, so a caller that matched on that text still
matches; the other refusals name their constructor. -/
def rejectText : Reject → String
  | .unexpectedEnd p => s!"unexpected end at {p}"
  | .unexpectedByte p b => s!"unexpected byte 0x{hexByte b} at {p}"
  | .badLiteral p _ => s!"bad literal at {p}"
  | .badNumber p => s!"bad number at {p}"
  | .unterminatedString p => s!"unterminated string at {p}"
  | .badEscape p => s!"bad escape at {p}"
  | .badUTF8 p => s!"bad UTF-8 at {p}"
  | .unpairedSurrogate p =>
      s!"unpairedSurrogate at {p}: the reference parser refuses a surrogate that \
         is not part of a well-formed pair"
  | .noncharacter p =>
      s!"noncharacter at {p}: the reference parser refuses a noncharacter \
         (RFC 7493 §2.1)"
  | .controlCharacter p => s!"control character at {p}"
  | .expectedColon p => s!"expected a colon at {p}"
  | .expectedComma p => s!"expected a comma at {p}"
  | .expectedCloseBracket p => s!"expected a close bracket at {p}"
  | .expectedCloseBrace p => s!"expected a close brace at {p}"
  | .trailingData p => s!"trailing data at {p}"
  | .byteOrderMark => "byte order mark: the reference parser refuses one"

def fallbackText : ParseError → String
  | .invalid r => s!"invalid: {rejectText r}"
  | .inputTooLong => "input too long: the reference parser's bound is exceeded"
  | .depthExceeded =>
      "depthExceeded: the reference parser refuses a document nested deeper than 128"
  | .outOfCapacity =>
      "outOfCapacity: the reference parser's token bound is exceeded"

/-! ### The adapter's tagged result

`shim.c` returns ten header words and then the payloads: `tag detail want got`,
then `verdict nk nxp ndst nev err`.  The tags that name a failure carry the
failed precondition's index and its expected and observed numbers, so the report
says what failed rather than that something did. -/

/-- The header's size: ten words. -/
def headerBytes : Nat := 80

/-- The adapter tagged the object's acceptance. -/
def tagObserved : Nat := 0

/-- The adapter tagged the object's refusal. -/
def tagRefused : Nat := 1

/-- What the adapter's precondition index names, in `shim.c`'s order. -/
def preconditionName : Nat → String
  | 1 => "the window's bytes past its 3-byte base"
  | 2 => "the mask unit's 24-byte carry slot"
  | 3 => "the mask unit's 48-byte output slot"
  | 4 => "the entry word's 8-byte slot"
  | 5 => "the entry stream's buffer at its capacity"
  | 6 => "the entry stream's cursor slot"
  | 7 => "the escape list's buffer at its capacity"
  | 8 => "the escape list's count slot"
  | 9 => "the escape list's 16-byte carry slot"
  | 10 => "the arena at its capacity"
  | 11 => "the arena's cursor slot"
  | 12 => "the event stream at its capacity"
  | 13 => "the event stream's count slot"
  | 14 => "the refusal record's error slot"
  | 15 => "the reserved arm bits"
  | 16 => "the entry stream's cursor"
  | 17 => "the escape list's count"
  | 18 => "the arena's cursor"
  | 19 => "the event stream's count"
  | 20 => "the two payload lengths"
  | _ => "a precondition the adapter did not name"

/-- Report a failure tag and return that class's exit status: 3 for an unmet
staging precondition, 4 for an allocation failure, 5 for an internal contract
violation. -/
def reportAdapterFailure (result : ByteArray) (tag : Nat) : IO UInt32 := do
  let detail := be64 result 8
  let want := be64 result 16
  let got := be64 result 24
  if tag = 2 then
    IO.eprintln s!"route: unsupported domain: {preconditionName detail}: \
      expected {want}, observed {got}"
    return 3
  else if tag = 3 then
    IO.eprintln s!"route: allocation failure: the adapter could not copy a \
      {want}-byte staging buffer"
    return 4
  else
    IO.eprintln s!"route: internal contract violation: {preconditionName detail}: \
      capacity {want}, returned {got}"
    return 5

/-- The fast path: stage the document in the record's shape, call the object
through the adapter, and print the observation and the two payloads. -/
def runFast (doc : ByteArray) (n : Nat) : IO UInt32 := do
  let nb := blocks n
  let epcap := 64 * nb + 9
  let xpcap := 64 * nb + 8
  let dstcap := n + 64
  let evcap := 13 * n + 128
  let window := (zeros 3).append doc |>.append (zeros (64 * nb - n)) |>.append (zeros 32)
  let result := route window (UInt64.ofNat n)
    (zeros 24) (zeros 48) (zeros 8)
    (zeros (4 * epcap)) (UInt64.ofNat epcap) (zeros 8)
    (zeros (4 * xpcap)) (UInt64.ofNat xpcap) (zeros 8) (zeros 16)
    (zeros dstcap) (UInt64.ofNat dstcap) (zeros 8)
    (zeros evcap) (UInt64.ofNat evcap) (zeros 8) (zeros 8) 2
  if result.size < headerBytes then
    IO.eprintln s!"route: internal contract violation: the adapter returned \
      {result.size} bytes, fewer than its {headerBytes}-byte header"
    return 5
  let tag := be64 result 0
  if tag != tagObserved && tag != tagRefused then
    return ← reportAdapterFailure result tag
  let verdict := be64 result 32
  let nk := be64 result 40
  let nxp := be64 result 48
  let ndst := be64 result 56
  let nev := be64 result 64
  let err := be64 result 72
  -- The header names the payload's extent; a result of another length has lost
  -- or gained bytes, and printing it as the observation would hide that.
  if result.size ≠ headerBytes + ndst + nev then
    IO.eprintln s!"route: internal contract violation: the result is \
      {result.size} bytes, and its header names {headerBytes + ndst + nev}"
    return 5
  IO.println s!"verdict={verdict} nk={nk} nxp={nxp} ndst={ndst} nev={nev} err={err}"
  let arena := ByteArray.mk (Array.mk ((result.toList.drop headerBytes).take ndst))
  let events := ByteArray.mk (Array.mk ((result.toList.drop (headerBytes + ndst)).take nev))
  IO.println s!"arena={hex arena}"
  IO.println s!"events={hex events}"
  return 0

/-- The fallback: the reference parser answers the document, once. -/
def runFallback (doc : ByteArray) : IO UInt32 := do
  match parseBytes Limits.default doc with
  | .ok t =>
      let decoded := (decodeTape t).isSome
      IO.println s!"fallback=accepted tokens={t.tokens.length} decoded={decoded}"
      return 0
  | .error e =>
      IO.eprintln s!"refused: {fallbackText e}"
      return 2

def run (path : String) : IO UInt32 := do
  let doc ← try
      IO.FS.readBinFile path
    catch e =>
      IO.eprintln s!"route: cannot read '{path}': {e}"
      return 2
  -- One predicate, the library's: the fast path is taken exactly when the
  -- certified domain admits the document; everything else is the fallback's,
  -- answered by the scalar reference parser and nowhere pre-filtered.
  match admission doc with
  | .ok () => runFast doc doc.size
  | .error _ => runFallback doc

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--doc", path] => run path
  | _ =>
      IO.eprintln usage
      return 1
