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
`shim.c` defines.  It is an `IO` action rather than a pure `let` so that it is
sequenced against the clock reads `--stages` divides its intervals by: a pure
call is free to move. -/
@[extern "leanllvm_json_route"]
opaque route (window : ByteArray) (n : UInt64)
  (sc mkSlot entw : ByteArray) (ep : ByteArray) (epcap : UInt64) (nk : ByteArray)
  (xp : ByteArray) (xpcap : UInt64) (nxp xcarry dst : ByteArray)
  (dstcap : UInt64) (ndst : ByteArray) (ev : ByteArray) (evcap : UInt64)
  (nev err : ByteArray) (arm : UInt64) : IO ByteArray

/-- One stage interval the adapter recorded, in nanoseconds: 0 the copy of the
caller's arrays into the object's ABI, 1 the native call, 2 the copy back.
`UINT64_MAX` means the adapter was built without `ROUTE_TIMING` and filled no
slot, which `--stages` reports rather than printing a zero.  The read is an
`IO` action because the slots are mutable state: a pure extern with a literal
index is folded once and reports the first call's interval for every later one. -/
@[extern "leanllvm_route_stage_ns_at"]
opaque stageNsAt (i : UInt64) : IO Nat

def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n (0 : UInt8))

def blocks (n : Nat) : Nat := (n + 63) / 64

def usage : String :=
  "usage: leanllvm-json-route --doc <file>\n" ++
  "       leanllvm-json-route --stages <file> [reps]"

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

/-- The route's staged input: the window and the four growing buffers at the
record's capacities, each zero-filled, plus the capacities the adapter's
preconditions are stated at. -/
structure Staged where
  n : Nat
  window : ByteArray
  sc : ByteArray
  mkSlot : ByteArray
  entw : ByteArray
  ep : ByteArray
  epcap : Nat
  nk : ByteArray
  xp : ByteArray
  xpcap : Nat
  nxp : ByteArray
  xcarry : ByteArray
  dst : ByteArray
  dstcap : Nat
  ndst : ByteArray
  ev : ByteArray
  evcap : Nat
  nev : ByteArray
  err : ByteArray

/-- Staging: the record's shape in bytes, with every buffer zero-filled and the
window `[0,0,0] ++ doc ++ zero padding ++ 32` readable tail bytes. -/
def stage (doc : ByteArray) (n : Nat) : Staged :=
  let nb := blocks n
  let epcap := 64 * nb + 9
  let xpcap := 64 * nb + 8
  let dstcap := n + 64
  let evcap := 13 * n + 128
  { n := n
    window := (zeros 3).append doc |>.append (zeros (64 * nb - n)) |>.append (zeros 32)
    sc := zeros 24
    mkSlot := zeros 48
    entw := zeros 8
    ep := zeros (4 * epcap)
    epcap := epcap
    nk := zeros 8
    xp := zeros (4 * xpcap)
    xpcap := xpcap
    nxp := zeros 8
    xcarry := zeros 16
    dst := zeros dstcap
    dstcap := dstcap
    ndst := zeros 8
    ev := zeros evcap
    evcap := evcap
    nev := zeros 8
    err := zeros 8 }

/-- The native call through the adapter, over a staged document. -/
def call (s : Staged) : IO ByteArray :=
  route s.window (UInt64.ofNat s.n)
    s.sc s.mkSlot s.entw
    s.ep (UInt64.ofNat s.epcap) s.nk
    s.xp (UInt64.ofNat s.xpcap) s.nxp s.xcarry
    s.dst (UInt64.ofNat s.dstcap) s.ndst
    s.ev (UInt64.ofNat s.evcap) s.nev s.err 2

/-- Outcome handling: decode the adapter's tagged result, and either print the
observation and the two payloads or report the failure class with its failed
precondition and its expected and observed numbers. -/
def interpret (result : ByteArray) : IO UInt32 := do
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

/-- The fast path: stage the document in the record's shape, call the object
through the adapter, and print the observation and the two payloads. -/
def runFast (doc : ByteArray) (n : Nat) : IO UInt32 := do
  let result ← call (stage doc n)
  interpret result

/-- The fallback's acceptance, in the route's wording: the tape's token count,
and whether `decodeTape` gave a value. -/
def reportFallbackAccept (t : Tape) : IO Unit := do
  let decoded := (decodeTape t).isSome
  IO.println s!"fallback=accepted tokens={t.tokens.length} decoded={decoded}"

/-- The fallback's refusal, in the route's wording: the reference parser's own
reason and byte. -/
def reportFallbackReject (e : ParseError) : IO Unit :=
  IO.eprintln s!"refused: {fallbackText e}"

/-- The fallback: the reference parser answers the document, once. -/
def runFallback (doc : ByteArray) : IO UInt32 := do
  match parseBytes Limits.default doc with
  | .ok t => reportFallbackAccept t; return 0
  | .error e => reportFallbackReject e; return 2

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

/-! ### The stage report

`--stages <file> <reps>` runs the route `reps` times on the same document and
prints each stage's median in nanoseconds.  The document is read inside every
repetition and the read is timed apart from the stages, so no stage's input is
hoisted out of its timed region and shared between repetitions: each
repetition's document is a fresh `ByteArray`.  A stage the path does not take is
reported `-`, not 0.

The five stages of the fast path are admission, staging, the adapter's copy-in,
the native call, and the adapter's copy-out; outcome handling is the sixth, and
it is the work between the adapter's return and the printed observation.  The
adapter's three intervals come from the instrumented build's slots, so the
route must be built with `TIMING=1`; a build without it reports that instead of
printing zeros. -/

def median (xs : Array Nat) : Nat :=
  if xs.isEmpty then 0
  else
    let s := xs.qsort (· < ·)
    s[s.size / 2]!

/-- A stage's median, or `-` when the path did not take it. -/
def stageField (xs : Array Nat) : String :=
  if xs.isEmpty then "-" else toString (median xs)

/-- The unfilled slot's value: `UINT64_MAX`. -/
def stageUnfilled : Nat := 18446744073709551615

def runStaged (path : String) (reps : Nat) : IO UInt32 := do
  let mut reads : Array Nat := #[]
  let mut adm : Array Nat := #[]
  let mut staging : Array Nat := #[]
  let mut copyin : Array Nat := #[]
  let mut native : Array Nat := #[]
  let mut copyout : Array Nat := #[]
  let mut awall : Array Nat := #[]
  let mut fallback : Array Nat := #[]
  let mut outcome : Array Nat := #[]
  let mut total : Array Nat := #[]
  let mut summed : Array Nat := #[]
  let mut verdict := 0
  let mut ndst := 0
  let mut nev := 0
  let mut size := 0
  let mut status := 0
  let mut kind := "fast"
  for _ in List.range reps do
    let t0 ← IO.monoNanosNow
    let doc ←
      try
        IO.FS.readBinFile path
      catch e =>
        IO.eprintln s!"route: cannot read '{path}': {e}"
        return 2
    let t1 ← IO.monoNanosNow
    reads := reads.push (t1 - t0)
    size := doc.size
    let a0 ← IO.monoNanosNow
    let decision := admission doc
    let a1 ← IO.monoNanosNow
    adm := adm.push (a1 - a0)
    match decision with
    | .error _ =>
        kind := "fallback"
        let f0 ← IO.monoNanosNow
        let answer := parseBytes Limits.default doc
        let f1 ← IO.monoNanosNow
        fallback := fallback.push (f1 - f0)
        let o0 ← IO.monoNanosNow
        let st ← match answer with
          | .ok t => reportFallbackAccept t; pure 0
          | .error e => reportFallbackReject e; pure 2
        let o1 ← IO.monoNanosNow
        outcome := outcome.push (o1 - o0)
        status := st
        total := total.push (o1 - a0)
        summed := summed.push ((a1 - a0) + (f1 - f0) + (o1 - o0))
    | .ok () =>
        let s0 ← IO.monoNanosNow
        let staged := stage doc doc.size
        let s1 ← IO.monoNanosNow
        let c0 ← IO.monoNanosNow
        let result ← call staged
        let c1 ← IO.monoNanosNow
        let ci ← stageNsAt 0
        let na ← stageNsAt 1
        let co ← stageNsAt 2
        if ci == stageUnfilled || na == stageUnfilled
            || co == stageUnfilled then
          IO.eprintln "route: --stages needs the instrumented adapter: no stage \
            was recorded. Rebuild with TIMING=1, e.g.\n  \
            nix develop -c bash probes/json/route/build.sh"
          return 6
        staging := staging.push (s1 - s0)
        copyin := copyin.push ci
        native := native.push na
        copyout := copyout.push co
        let o0 ← IO.monoNanosNow
        status ← interpret result
        let o1 ← IO.monoNanosNow
        outcome := outcome.push (o1 - o0)
        verdict := be64 result 32
        ndst := be64 result 56
        nev := be64 result 64
        -- The adapter's wall carries the two clock reads the slots are divided
        -- by, and the precondition checks before the first one; the difference
        -- between it and the three slots is that uncovered interval, reported
        -- so a reader can see it rather than infer it from a residual.
        awall := awall.push (c1 - c0)
        total := total.push (o1 - a0)
        summed := summed.push ((a1 - a0) + (s1 - s0) + ci + na + co + (o1 - o0))
  IO.eprintln s!"row doc={(System.FilePath.fileName path).getD path} size={size} \
    path={kind} reps={reps} \
    read_ns={median reads} admission_ns={stageField adm} \
    staging_ns={stageField staging} copyin_ns={stageField copyin} \
    native_ns={stageField native} copyout_ns={stageField copyout} \
    adapter_wall_ns={stageField awall} fallback_ns={stageField fallback} outcome_ns={stageField outcome} \
    total_ns={median total} summed_stage_ns={median summed} \
    verdict={verdict} ndst={ndst} nev={nev} rep_total_ns={total.toList}"
  return status

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--doc", path] => run path
  | ["--stages", path] => runStaged path 11
  | ["--stages", path, reps] => runStaged path reps.toNat!
  | _ =>
      IO.eprintln usage
      return 1
