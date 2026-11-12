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
  "       leanllvm-json-route --stages <file> [reps]\n" ++
  "       leanllvm-json-route --consume <file> [reps]"

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

/-! ### Outcome handling, in the parts the stage report prices

`interpret` is the outcome stage with no clock read in it.  `--stages` calls its
parts with a clock read between them, so the dissection prices the code that
runs — the same `decodeResult`, `payloads`, `observationLine` and `payloadLine`
— rather than a copy written for the instrument.

`decodeResult` is the header decode the route has always done: `be64` materialises
`result.toList` at every byte it reads, so one word costs eight list traversals
of the whole result and the seven words an observation needs cost fifty-six.
`payloads` materialises the result's list once per payload.  Both are priced as
they are rather than changed here; `--consume` below reads the same words
through indexing, and the two numbers together are what those conversions cost.
-/

/-- The observation's six words, decoded from the adapter's header. -/
structure Observation where
  verdict : Nat := 0
  nk : Nat := 0
  nxp : Nat := 0
  ndst : Nat := 0
  nev : Nat := 0
  err : Nat := 0

/-- The header's class: the observation when the object produced one, the
failure's status otherwise.  A failure class is reported here, with its failed
precondition and its expected and observed numbers, so the caller has only a
status to propagate. -/
def decodeResult (result : ByteArray) : IO (Except UInt32 Observation) := do
  if result.size < headerBytes then
    IO.eprintln s!"route: internal contract violation: the adapter returned \
      {result.size} bytes, fewer than its {headerBytes}-byte header"
    return .error 5
  let tag := be64 result 0
  if tag != tagObserved && tag != tagRefused then
    return .error (← reportAdapterFailure result tag)
  let o : Observation :=
    { verdict := be64 result 32
      nk := be64 result 40
      nxp := be64 result 48
      ndst := be64 result 56
      nev := be64 result 64
      err := be64 result 72 }
  -- The header names the payload's extent; a result of another length has lost
  -- or gained bytes, and printing it as the observation would hide that.
  if result.size ≠ headerBytes + o.ndst + o.nev then
    IO.eprintln s!"route: internal contract violation: the result is \
      {result.size} bytes, and its header names {headerBytes + o.ndst + o.nev}"
    return .error 5
  return .ok o

/-- The observation's line, exactly as the route prints it. -/
def observationLine (o : Observation) : String :=
  s!"verdict={o.verdict} nk={o.nk} nxp={o.nxp} ndst={o.ndst} nev={o.nev} err={o.err}"

/-- One payload's line, exactly as the route prints it: the label, then two
lowercase hex digits per byte. -/
def payloadLine (label : String) (bs : ByteArray) : String :=
  label ++ "=" ++ hex bs

/-- The two payloads cut out of the result.  Each cut materialises the result's
`toList` and walks it, so the stage is two list traversals per call. -/
def payloads (result : ByteArray) (ndst nev : Nat) : ByteArray × ByteArray :=
  (ByteArray.mk (Array.mk ((result.toList.drop headerBytes).take ndst)),
   ByteArray.mk (Array.mk ((result.toList.drop (headerBytes + ndst)).take nev)))

/-- Outcome handling: decode the adapter's tagged result, and either print the
observation and the two payloads or report the failure class with its failed
precondition and its expected and observed numbers. -/
def interpret (result : ByteArray) : IO UInt32 := do
  match ← decodeResult result with
  | .error status => return status
  | .ok o =>
    IO.println (observationLine o)
    let (arena, events) := payloads result o.ndst o.nev
    IO.println (payloadLine "arena" arena)
    IO.println (payloadLine "events" events)
    return 0

/-- The outcome stage's intervals, in nanoseconds.  `decode`, `header`, `slice`,
`arena` and `events` are the five parts `interpret` runs, in its order; their
sum is the stage's cost plus the five clock reads that divide it.  `--stages`
reports them, and `arenaBytes`/`eventBytes` carry the payloads so a build-only
probe of the hex conversion can run outside the stage's timed window. -/
structure OutcomeParts where
  decode : Nat := 0
  header : Nat := 0
  slice : Nat := 0
  arena : Nat := 0
  events : Nat := 0
  status : UInt32 := 0
  arenaBytes : ByteArray := ByteArray.empty
  eventBytes : ByteArray := ByteArray.empty

/-- The outcome stage with its parts timed: the same calls `interpret` makes in
the same order, with a clock read between them. -/
def interpretTimed (result : ByteArray) : IO OutcomeParts := do
  let d0 ← IO.monoNanosNow
  let decoded ← decodeResult result
  let d1 ← IO.monoNanosNow
  match decoded with
  | .error status =>
      return { decode := d1 - d0, status := status }
  | .ok o =>
      IO.println (observationLine o)
      let h1 ← IO.monoNanosNow
      let (arena, events) := payloads result o.ndst o.nev
      let s1 ← IO.monoNanosNow
      IO.println (payloadLine "arena" arena)
      let a1 ← IO.monoNanosNow
      IO.println (payloadLine "events" events)
      let e1 ← IO.monoNanosNow
      return { decode := d1 - d0, header := h1 - d1, slice := s1 - h1,
               arena := a1 - s1, events := e1 - a1, status := 0,
               arenaBytes := arena, eventBytes := events }

/-- The hex conversion of both payloads, built and folded into the length it
returned, with no write.  Run after the stage's timed window, it prices the
conversion inside `arena` and `events`; the difference between each and this is
the write. -/
def hexProbe (arena events : ByteArray) : IO (Nat × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let a := payloadLine "arena" arena
  let t1 ← IO.monoNanosNow
  let e := payloadLine "events" events
  let t2 ← IO.monoNanosNow
  -- The lengths are returned so the compiler cannot drop either build.
  return (t1 - t0, t2 - t1, a.length + e.length)

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
  let mut odecode : Array Nat := #[]
  let mut oheader : Array Nat := #[]
  let mut oslice : Array Nat := #[]
  let mut oarena : Array Nat := #[]
  let mut oevents : Array Nat := #[]
  let mut hexArena : Array Nat := #[]
  let mut hexEvents : Array Nat := #[]
  let mut hexLen := 0
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
        let parts ← interpretTimed result
        let o1 ← IO.monoNanosNow
        -- The stage's cost is the sum of its parts, each interval from the
        -- clock read that closed the one before it, so the five reads are in
        -- the stage and nothing else is.
        let ocost := parts.decode + parts.header + parts.slice + parts.arena +
          parts.events
        outcome := outcome.push ocost
        odecode := odecode.push parts.decode
        oheader := oheader.push parts.header
        oslice := oslice.push parts.slice
        oarena := oarena.push parts.arena
        oevents := oevents.push parts.events
        -- Instrument-only, outside the stage's timed window: the same hex
        -- conversion with the write removed, so each printed payload's write is
        -- the difference between its interval and this one.
        let (hexa, hexe, hexl) ← hexProbe parts.arenaBytes parts.eventBytes
        hexArena := hexArena.push hexa
        hexEvents := hexEvents.push hexe
        hexLen := hexl
        status := parts.status
        verdict := be64 result 32
        ndst := be64 result 56
        nev := be64 result 64
        -- The adapter's wall carries the two clock reads the slots are divided
        -- by, and the precondition checks before the first one; the difference
        -- between it and the three slots is that uncovered interval, reported
        -- so a reader can see it rather than infer it from a residual.
        awall := awall.push (c1 - c0)
        total := total.push (o1 - a0)
        summed := summed.push ((a1 - a0) + (s1 - s0) + ci + na + co + ocost)
  IO.eprintln s!"row doc={(System.FilePath.fileName path).getD path} size={size} \
    path={kind} reps={reps} \
    read_ns={median reads} admission_ns={stageField adm} \
    staging_ns={stageField staging} copyin_ns={stageField copyin} \
    native_ns={stageField native} copyout_ns={stageField copyout} \
    adapter_wall_ns={stageField awall} fallback_ns={stageField fallback} outcome_ns={stageField outcome} \
    outcome_decode_ns={stageField odecode} outcome_header_ns={stageField oheader} \
    outcome_slice_ns={stageField oslice} outcome_arena_ns={stageField oarena} \
    outcome_events_ns={stageField oevents} \
    hex_arena_ns={stageField hexArena} hex_events_ns={stageField hexEvents} \
    hexlen={if hexArena.isEmpty then "-" else toString hexLen} \
    total_ns={median total} summed_stage_ns={median summed} \
    verdict={verdict} ndst={ndst} nev={nev} rep_total_ns={total.toList}"
  return status

/-! ### The consumer's read

`--consume <file> <reps>` is the route without its reporting: it runs the fast
path and reads the result the way a consumer that keeps no printed copy would.
The header words come from `ByteArray` indexing rather than `be64`'s list
materialisation, and the event stream is walked record by record at the widths
`kernel/json/stage2.h` documents.  Two readings are priced: a fold that keeps no
per-token object, and one that materialises one `Event` per event — which is what
a consumer that wants values pays, and where a per-token allocation lands.
Nothing is printed per repetition, so neither number contains the route's hex
conversion.

The walk is a summary rather than a second parser: it reads each record's tag,
length and payload, sums the arena's bytes, and stops with `walked=false` at a
record that would run past the stream instead of reading past it.  A consumer
that rebuilt strings from the spans is not measured here; its floor is the arena
read below, and its per-string allocation would sit on top of the token price.
-/

/-- One decoded event record: the tag, the length field a key or string carries
(0 for a tag without one), and the eight-byte payload (a number's IEEE bits, a
key's or string's span, or 0). -/
structure Event where
  tag : UInt8
  len : UInt64
  payload : UInt64
deriving Inhabited

/-- A consumer's summary of one result. -/
structure Consumed where
  tokens : Nat := 0
  events : Nat := 0
  arena : Nat := 0
  sum : UInt64 := 0
  walked : Bool := false
  values : Nat := 0
deriving Inhabited

/-- The record's width, from the encoding `kernel/json/stage2.h` documents: a
key (`T_KEY` = 5) or string (`T_STR` = 6) is a tag, four length bytes and eight
span bytes; a number (`T_NUM` = 7) is a tag and its eight IEEE bytes; every
other tag stands alone. -/
def eventWidth (tag : UInt8) : Nat :=
  if tag == 5 || tag == 6 then 13 else if tag == 7 then 9 else 1

/-- Eight little-endian bytes at `i`, read by index.  The arithmetic is
`UInt64` rather than `Nat`, so a byte read is unboxed and the reading prices the
record walk rather than the accumulator's allocation. -/
def indexWord (bs : ByteArray) (i : Nat) : UInt64 :=
  let g (k : Nat) : UInt64 := (bs.get! (i + k)).toUInt64
  g 0 + 256 * g 1 + 65536 * g 2 + 16777216 * g 3 +
    4294967296 * (g 4 + 256 * g 5 + 65536 * g 6 + 16777216 * g 7)

/-- Four little-endian bytes at `i`, read by index. -/
def indexWord4 (bs : ByteArray) (i : Nat) : UInt64 :=
  let g (k : Nat) : UInt64 := (bs.get! (i + k)).toUInt64
  g 0 + 256 * g 1 + 65536 * g 2 + 16777216 * g 3

/-- The header through indexing: the observation a consumer needs, with neither
`be64`'s per-byte list materialisation nor any printing. -/
def decodeIndexed (result : ByteArray) : Except String Observation :=
  if result.size < headerBytes then
    .error s!"the result is {result.size} bytes, fewer than its \
      {headerBytes}-byte header"
  else
    let tag := indexWord result 0
    if tag != 0 && tag != 1 then
      .error s!"the adapter tagged the result {tag}, not an observation"
    else
      let o : Observation :=
        { verdict := (indexWord result 32).toNat
          nk := (indexWord result 40).toNat
          nxp := (indexWord result 48).toNat
          ndst := (indexWord result 56).toNat
          nev := (indexWord result 64).toNat
          err := (indexWord result 72).toNat }
      if result.size ≠ headerBytes + o.ndst + o.nev then
        .error s!"the result is {result.size} bytes, and its header names \
          {headerBytes + o.ndst + o.nev}"
      else
        .ok o

/-- Read a result as a consumer would.  `build` also materialises one `Event`
per event: with it the walk pays an object and an array growth per event;
without it the same fields are folded and no per-token object exists. -/
partial def consumeResult (result : ByteArray) (o : Observation)
    (build : Bool) : Consumed :=
  let rec arenaSum (k : Nat) (acc : UInt64) : UInt64 :=
    if k < o.ndst then
      arenaSum (k + 1) (acc + (result.get! (headerBytes + k)).toUInt64)
    else acc
  let rec walk (k : Nat) (tokens : Nat) (sum : UInt64) (acc : Array Event) :
      Consumed :=
    if k >= o.nev then
      { tokens := tokens, events := k, arena := o.ndst, sum := sum, walked := true,
        values := acc.size }
    else
      let tag := result.get! (headerBytes + o.ndst + k)
      let w := eventWidth tag
      if k + w > o.nev then
        { tokens := tokens, events := k, arena := o.ndst, sum := sum,
          walked := false, values := acc.size }
      else
        let base := headerBytes + o.ndst + k
        let len := if w == 13 then indexWord4 result (base + 1) else 0
        let payload :=
          if w == 13 then indexWord result (base + 5)
          else if w == 9 then indexWord result (base + 1)
          else 0
        let sum := sum + tag.toUInt64 + len + payload
        let acc :=
          if build then acc.push { tag := tag, len := len, payload := payload }
          else acc
        walk (k + w) (tokens + 1) sum acc
  walk 0 0 (arenaSum 0 0) #[]

/-- `--consume`: the fast path run `reps` times, with the consumer's two
readings timed apart from the route and from each other.  The two readings share
one header decode each, so each price includes it; the fold and the values walk
must agree on the token count and on the checksum, and a disagreement is
reported rather than averaged in. -/
def runConsume (path : String) (reps : Nat) : IO UInt32 := do
  let mut reads : Array Nat := #[]
  let mut adm : Array Nat := #[]
  let mut staging : Array Nat := #[]
  let mut routeNs : Array Nat := #[]
  let mut copyout : Array Nat := #[]
  let mut fold : Array Nat := #[]
  let mut values : Array Nat := #[]
  let mut size := 0
  let mut kind := "fast"
  let mut tokens := 0
  let mut valuesBuilt := 0
  let mut ndst := 0
  let mut nev := 0
  let mut walked := true
  let mut foldSum : UInt64 := 0
  let mut valuesSum : UInt64 := 0
  for rep in List.range reps do
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
    | .ok () =>
      let s0 ← IO.monoNanosNow
      let staged := stage doc doc.size
      let c0 ← IO.monoNanosNow
      let result ← call staged
      let c1 ← IO.monoNanosNow
      staging := staging.push (c0 - s0)
      routeNs := routeNs.push (c1 - c0)
      let co ← stageNsAt 2
      if co != stageUnfilled then copyout := copyout.push co
      -- One reading, with its own header decode.  The two alternate which goes
      -- first, so neither always pays the cold pass over the result.
      let read (build : Bool) : IO (Consumed × Nat) := do
        let t0 ← IO.monoNanosNow
        let c :=
          match decodeIndexed result with
          | .ok o => consumeResult result o build
          | .error _ => ({ walked := false } : Consumed)
        let t1 ← IO.monoNanosNow
        return (c, t1 - t0)
      let first ← read (rep % 2 != 0)
      let second ← read (rep % 2 == 0)
      let (folded, fns) := if rep % 2 == 0 then first else second
      let (built, vns) := if rep % 2 == 0 then second else first
      fold := fold.push fns
      values := values.push vns
      tokens := folded.tokens
      valuesBuilt := built.values
      ndst := folded.arena
      nev := folded.events
      walked := folded.walked && built.walked && folded.tokens == built.tokens
      foldSum := folded.sum
      valuesSum := built.sum
  IO.eprintln s!"row doc={(System.FilePath.fileName path).getD path} size={size} \
    path={kind} reps={reps} read_ns={median reads} \
    admission_ns={stageField adm} staging_ns={stageField staging} \
    route_ns={stageField routeNs} copyout_ns={stageField copyout} \
    consume_fold_ns={stageField fold} consume_values_ns={stageField values} \
    ndst={ndst} nev={nev} tokens={tokens} values={valuesBuilt} \
    walked={if walked then 1 else 0} foldsum={foldSum} valuessum={valuesSum}"
  -- A consumer whose two readings disagree, or whose walk did not land on the
  -- stream's end, is a failure of the reading rather than a number to report.
  if kind == "fast" &&
      !(walked && valuesBuilt == tokens && tokens > 0 && foldSum == valuesSum) then
    IO.eprintln s!"route: --consume: the readings disagree: tokens={tokens} \
      values={valuesBuilt} walked={walked} fold sum={foldSum} \
      values sum={valuesSum}"
    return 5
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--doc", path] => run path
  | ["--stages", path] => runStaged path 11
  | ["--stages", path, reps] => runStaged path reps.toNat!
  | ["--consume", path] => runConsume path 11
  | ["--consume", path, reps] => runConsume path reps.toNat!
  | _ =>
      IO.eprintln usage
      return 1
