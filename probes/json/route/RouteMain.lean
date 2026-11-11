/-
The JSON pipeline's call route: a standalone Lean program that stages the
document the record demands, calls `leanllvm_json_pipeline` through the C
adapter in `shim.c`, and prints what the caller observes.

It is standalone because the kernel is outside Lake: `kernel/json/README.md`
says "`lake` does not build the kernel: it is a C unit of the identity, route
and bench scripts, not of the Lean library."  `build.sh` is the link step, in
the shape `probes/app/build.sh` uses for the comma-mask seam.

The staging is `LeanLLVM.JsonCallRoute.stagedStore`'s shape, in bytes: the
window is `[0,0,0] ++ doc ++ zero padding ++ 32` readable tail bytes, and the
four growing buffers are sized at the record's capacities.  The POS8 table is
not staged here: the entry unit reads its own static table, and the adapter's
setup fills it (`route_init` in `shim.c`), so this program has no initialiser to
call and no dummy return to consume.

The adapter returns a tagged result: the observation's six words and its two
payloads for the two classes where the object ran, and a tag naming the class
otherwise — an unmet staging precondition before the call, an allocation
failure, or a returned cursor past its capacity.  The first two classes print
the object's observation; the last three are reported on stderr with the failed
precondition and the expected and observed numbers, at exit 3, 4 and 5.

The shell refuses the empty document and one over the input bound before any
call, and it refuses the reference parser's character policy after the call: the
object's observation is printed on stdout, and a document the object accepted
that the reference refuses for a lone surrogate or a noncharacter is refused on
stderr with the reference's reason and byte, at exit 2.  The policy scan is
`scanDocument` below; the parser's depth and token exclusions belong to
`LeanLLVM.JsonCallRoute.checkRoute`, which needs the reference parser and so is
checked by `DomainCheck.lean` under `lake env lean`.
-/

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

/-! ### The reference parser's character policy

The pipeline's ABI carries no character-policy slot, so the object accepts
documents the reference parser refuses under RFC 7493 §2.1's restriction on top
of RFC 8259: lone and out-of-range surrogate escapes, and noncharacters, escaped
or raw.  Those are RFC texts, so the object's verdict is the RFC verdict and the
reference's is the stricter one, and the route must be as strict as the
reference it replaces.

The scan below reads the document's string bodies the way the reference's
`scanChars` reads them, and reports the reference's own reason and byte
(`parseKey` reports `opening quote + 1 + body offset`, which is the absolute
index this scan carries).  A body refusal of another class — a bad escape, bad
UTF-8, a control character, or the body running out — stops the scan: the
reference reads no further than its first refusal, so a later body's policy
refusal would not be the reference's verdict.

The scan is consulted only after the object has accepted the document.  That is
the class where the wrapper's verdict can differ from the reference's: a
document the object refused already has a refusal verdict, and its reason is the
object's, not the reference's.  On an accepted document the bytes are RFC JSON,
so the bodies this scan walks are the bodies the reference walks, and the
refusal is the reference's. -/

/-- The reference parser's policy refusals, at the byte it names. -/
inductive PolicyRefusal where
  | unpairedSurrogate (pos : Nat)
  | noncharacter (pos : Nat)
deriving Repr

/-- Unicode noncharacters, as the reference states them: U+FDD0..U+FDEF and every
U+nFFFE / U+nFFFF. -/
def isNoncharacter (n : Nat) : Bool :=
  (decide (0xFDD0 ≤ n) && decide (n ≤ 0xFDEF)) ||
    decide (n % 0x10000 = 0xFFFE) || decide (n % 0x10000 = 0xFFFF)

/-- One hexadecimal digit's value. -/
def hexDigit (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 0x30 ≤ n ∧ n ≤ 0x39 then some (n - 0x30)
  else if 0x41 ≤ n ∧ n ≤ 0x46 then some (n - 0x41 + 10)
  else if 0x61 ≤ n ∧ n ≤ 0x66 then some (n - 0x61 + 10)
  else none

/-- The four hex digits at `i` as one code unit; `none` if any byte is absent or
is not a hex digit. -/
def hex4 (bs : Array UInt8) (i : Nat) : Option Nat :=
  match bs[i]?, bs[i + 1]?, bs[i + 2]?, bs[i + 3]? with
  | some a, some b, some c, some d =>
      (hexDigit a).bind fun x =>
      (hexDigit b).bind fun y =>
      (hexDigit c).bind fun z =>
      (hexDigit d).bind fun w =>
        some (x * 0x1000 + y * 0x100 + z * 0x10 + w)
  | _, _, _, _ => none

/-- A UTF-8 continuation byte in `[lo, hi]`, as the offset from 0x80. -/
def contByte (bs : Array UInt8) (i lo hi : Nat) : Option Nat :=
  match bs[i]? with
  | some c => if lo ≤ c.toNat ∧ c.toNat ≤ hi then some (c.toNat - 0x80) else none
  | none => none

/-- The reference parser's strict UTF-8 decoder: the RFC 3629 ranges it admits,
with the code point and the byte length it reads.  `none` is one of its non-policy
refusals. -/
def decodeUtf8 (bs : Array UInt8) (i : Nat) : Option (Nat × Nat) :=
  match bs[i]? with
  | none => none
  | some b =>
    let n := b.toNat
    if n < 0x80 then some (n, 1)
    else if 0xC2 ≤ n ∧ n ≤ 0xDF then
      (contByte bs (i + 1) 0x80 0xBF).map fun c1 => ((n - 0xC0) * 0x40 + c1, 2)
    else if n = 0xE0 then
      match contByte bs (i + 1) 0xA0 0xBF with
      | some c1 => (contByte bs (i + 2) 0x80 0xBF).map fun c2 => (c1 * 0x40 + c2, 3)
      | none => none
    else if 0xE1 ≤ n ∧ n ≤ 0xEC then
      match contByte bs (i + 1) 0x80 0xBF with
      | some c1 =>
        (contByte bs (i + 2) 0x80 0xBF).map fun c2 =>
          ((n - 0xE0) * 0x1000 + c1 * 0x40 + c2, 3)
      | none => none
    else if n = 0xED then
      match contByte bs (i + 1) 0x80 0x9F with
      | some c1 =>
        (contByte bs (i + 2) 0x80 0xBF).map fun c2 => (0xD000 + c1 * 0x40 + c2, 3)
      | none => none
    else if 0xEE ≤ n ∧ n ≤ 0xEF then
      match contByte bs (i + 1) 0x80 0xBF with
      | some c1 =>
        (contByte bs (i + 2) 0x80 0xBF).map fun c2 =>
          ((n - 0xE0) * 0x1000 + c1 * 0x40 + c2, 3)
      | none => none
    else if n = 0xF0 then
      match contByte bs (i + 1) 0x90 0xBF with
      | some c1 =>
        match contByte bs (i + 2) 0x80 0xBF with
        | some c2 =>
          (contByte bs (i + 3) 0x80 0xBF).map fun c3 =>
            (c1 * 0x1000 + c2 * 0x40 + c3, 4)
        | none => none
      | none => none
    else if 0xF1 ≤ n ∧ n ≤ 0xF3 then
      match contByte bs (i + 1) 0x80 0xBF with
      | some c1 =>
        match contByte bs (i + 2) 0x80 0xBF with
        | some c2 =>
          (contByte bs (i + 3) 0x80 0xBF).map fun c3 =>
            ((n - 0xF0) * 0x40000 + c1 * 0x1000 + c2 * 0x40 + c3, 4)
        | none => none
      | none => none
    else if n = 0xF4 then
      match contByte bs (i + 1) 0x80 0x8F with
      | some c1 =>
        match contByte bs (i + 2) 0x80 0xBF with
        | some c2 =>
          (contByte bs (i + 3) 0x80 0xBF).map fun c3 =>
            (0x100000 + c1 * 0x1000 + c2 * 0x40 + c3, 4)
        | none => none
      | none => none
    else none

/-- One string body's scan's outcome. -/
inductive BodyScan where
  /-- The body closed with no refusal; `next` is the index past the quote. -/
  | clean (next : Nat)
  | unpaired (pos : Nat)
  | noncharacter (pos : Nat)
  /-- A refusal the reference makes for another reason; it reads no further. -/
  | otherRefusal

/-- One string body, read the way the reference's `scanChars` reads it, at
absolute index `i`.  `fuel` bounds the recursion; the scan over a body takes at
most one step per byte. -/
def scanBody (bs : Array UInt8) : Nat → Nat → BodyScan
  | 0, _ => .otherRefusal
  | fuel + 1, i =>
    match bs[i]? with
    | none => .otherRefusal
    | some 0x22 => .clean (i + 1)
    | some 0x5C =>
      match bs[i + 1]? with
      | none => .otherRefusal
      | some e =>
        if e = 0x22 ∨ e = 0x5C ∨ e = 0x2F ∨ e = 0x62 ∨ e = 0x66 ∨ e = 0x6E ∨
            e = 0x72 ∨ e = 0x74 then
          scanBody bs fuel (i + 2)
        else if e = 0x75 then
          match hex4 bs (i + 2) with
          | none => .otherRefusal
          | some c =>
            if 0xD800 ≤ c ∧ c ≤ 0xDBFF then
              match bs[i + 6]?, bs[i + 7]? with
              | some 0x5C, some 0x75 =>
                match bs[i + 8]?, bs[i + 9]?, bs[i + 10]?, bs[i + 11]? with
                | some _, some _, some _, some _ =>
                  match hex4 bs (i + 8) with
                  | none => .otherRefusal
                  | some lo =>
                    if 0xDC00 ≤ lo ∧ lo ≤ 0xDFFF then
                      if isNoncharacter
                          (0x10000 + (c - 0xD800) * 0x400 + (lo - 0xDC00)) then
                        .noncharacter i
                      else scanBody bs fuel (i + 12)
                    else .unpaired i
                | _, _, _, _ => .unpaired i
              | _, _ => .unpaired i
            else if 0xDC00 ≤ c ∧ c ≤ 0xDFFF then .unpaired i
            else if isNoncharacter c then .noncharacter i
            else scanBody bs fuel (i + 6)
        else .otherRefusal
    | some b =>
      let n := b.toNat
      if n < 0x20 then .otherRefusal
      else if n < 0x80 then scanBody bs fuel (i + 1)
      else
        match decodeUtf8 bs i with
        | some (c, len) =>
            if isNoncharacter c then .noncharacter i
            else scanBody bs fuel (i + len)
        | none => .otherRefusal

/-- The document's string bodies in document order: the first refusal the
reference makes under its character policy, or `none`. -/
def scanDocument (bs : Array UInt8) : Nat → Nat → Option PolicyRefusal
  | 0, _ => none
  | fuel + 1, i =>
    match bs[i]? with
    | none => none
    | some 0x22 =>
      match scanBody bs (bs.size - i) (i + 1) with
      | .clean next => scanDocument bs fuel next
      | .unpaired pos => some (.unpairedSurrogate pos)
      | .noncharacter pos => some (.noncharacter pos)
      | .otherRefusal => none
    | some _ => scanDocument bs fuel (i + 1)

/-- The document's policy refusal, if the reference parser would make one. -/
def policyRefusal (doc : ByteArray) : Option PolicyRefusal :=
  scanDocument doc.data doc.size 0

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

/-- The reason the wrapper reports, naming the reference's refusal and byte. -/
def PolicyRefusal.message : PolicyRefusal → String
  | .unpairedSurrogate pos =>
      s!"refused: invalid: unpairedSurrogate at {pos}: the reference parser refuses a \
         surrogate that is not part of a well-formed pair"
  | .noncharacter pos =>
      s!"refused: invalid: noncharacter at {pos}: the reference parser refuses a \
         noncharacter (RFC 7493 §2.1)"

def run (path : String) : IO UInt32 := do
  let doc ← try
      IO.FS.readBinFile path
    catch e =>
      IO.eprintln s!"route: cannot read '{path}': {e}"
      return 2
  let n := doc.size
  if n = 0 then
    IO.eprintln "refused: empty input: the pipeline record's domain requires a non-empty document"
    return 2
  if 1048576 < n then
    IO.eprintln s!"refused: input too long: the record's bound is 1048576 bytes, the document is {n}"
    return 2
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
  -- The reference parser is stricter than RFC 8259 on characters, and the ABI
  -- has no policy slot, so the object accepts texts the reference refuses.  A
  -- document the object accepted is refused here with the reference's reason and
  -- byte; a document the object refused keeps the object's verdict, whose
  -- refusal reason is the object's and not the reference's.
  if verdict = 1 then
    match policyRefusal doc with
    | some r =>
        IO.eprintln r.message
        return 2
    | none => return 0
  else
    return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--doc", path] => run path
  | _ =>
      IO.eprintln usage
      return 1
