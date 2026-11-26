/-
The indexed event reader against the list specification, on hand-built buffers.

`JsonEventBytes.walkRecords` is the executable specification and
`JsonEventCursor.walkRecordsIndexed` its cursor form.  An accepted document's
returned stream is compared on the route (`--indexed-check`); this program
supplies the streams a route never sees: a truncated final record, a span past
the end of either source, an unknown tag, a body that does not decode, and an
empty stream.  Each case is a `(document, event bytes, arena)` triple, so the
comparison is over arbitrary buffers and a malformed stream's `none` is checked
as well as an accepted stream's events.

Each row also carries the expected number of decoded events (or `none`), so the
program fails on a comparison that agreed because both readers failed, and a
valid record whose two readers both returned `none` is a red rather than a
silent pass.

Elaborated and run by `tests/json-indexed-reader.sh`:

    lake env lean --run tests/json-indexed-reader.lean
-/
import LeanLLVM.Refinement.JsonEventCursorInterface

namespace JsonIndexedReader

open LeanLLVM.JSON
open LeanLLVM.Refinement

/-- `n`'s low `k` bytes, little-endian: a record field or a number's payload. -/
def leN (n : Nat) : Nat → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n % 256) :: leN (n / 256) k

/-- A key or string record: the tag, the four length bytes and the eight field
bytes. -/
def strRecord (tag len field : Nat) : List UInt8 :=
  [UInt8.ofNat tag] ++ leN len 4 ++ leN field 8

/-- A number record: `T_NUM` and its eight payload bytes. -/
def numRecord (bits : Nat) : List UInt8 :=
  [7] ++ leN bits 8

/-- A document holding the string `"ab"`, so a plain-form body starts at byte
1 and its closing quote is byte 3. -/
def docAb : List UInt8 := [0x22, 0x61, 0x62, 0x22]

/-- A document holding `"a\nb"`, so the plain form's body carries an escape. -/
def docEscaped : List UInt8 := [0x22, 0x61, 0x5C, 0x6E, 0x62, 0x22]

/-- The arena holding `é` as its two UTF-8 bytes. -/
def arenaEAcute : List UInt8 := [0xC3, 0xA9]

/-- One case: its name, the three buffers, and the expected event count
(`none` for an unreadable stream). -/
structure Case where
  name : String
  doc : List UInt8
  events : List UInt8
  arena : List UInt8
  expected : Option Nat

/-- The cases: every record width, both body sources, the two bounds checks and
the failures each of them can produce. -/
def cases : List Case :=
  let plainKey := strRecord 5 2 (2 ^ 63 + 1)
  let plainStr := strRecord 6 2 (2 ^ 63 + 1)
  let escapedStr := strRecord 6 4 (2 ^ 63 + 1)
  let arenaStr := strRecord 6 2 0
  let obj := [1] ++ plainKey ++ numRecord 5 ++ [2]
  [ { name := "empty", doc := [], events := [], arena := [], expected := some 0 }
  , { name := "tag-obj", doc := [], events := [1], arena := [], expected := some 1 }
  , { name := "tag-obj-end", doc := [], events := [2], arena := [], expected := some 1 }
  , { name := "tag-arr", doc := [], events := [3], arena := [], expected := some 1 }
  , { name := "tag-arr-end", doc := [], events := [4], arena := [], expected := some 1 }
  , { name := "tag-true", doc := [], events := [8], arena := [], expected := some 1 }
  , { name := "tag-false", doc := [], events := [9], arena := [], expected := some 1 }
  , { name := "tag-null", doc := [], events := [10], arena := [], expected := some 1 }
  , { name := "number-one", doc := [], events := numRecord 1, arena := []
    , expected := some 1 }
  , { name := "number-truncated", doc := [], events := [7, 0, 0, 0]
    , arena := [], expected := none }
  , { name := "number-short-by-one", doc := [], events := (numRecord 1).take 8
    , arena := [], expected := none }
  , { name := "plain-string", doc := docAb, events := plainStr, arena := []
    , expected := some 1 }
  , { name := "plain-string-escaped", doc := docEscaped, events := escapedStr
    , arena := [], expected := some 1 }
  , { name := "arena-string", doc := [], events := arenaStr
    , arena := arenaEAcute, expected := some 1 }
  , { name := "object-with-key", doc := docAb, events := obj, arena := []
    , expected := some 4 }
  , { name := "nested-array", doc := docAb
    , events := [1, 3] ++ numRecord 7 ++ [4, 2], arena := [], expected := some 5 }
  , { name := "string-truncated", doc := docAb
    , events := (strRecord 6 2 (2 ^ 63 + 1)).take 11, arena := [], expected := none }
  , { name := "string-truncated-by-one", doc := docAb
    , events := (strRecord 6 2 (2 ^ 63 + 1)).take 12, arena := [], expected := none }
  , { name := "arena-span-past-end", doc := []
    , events := strRecord 6 3 0, arena := arenaEAcute, expected := none }
  , { name := "document-span-past-end", doc := docAb
    , events := strRecord 6 100 (2 ^ 63 + 1), arena := [], expected := none }
  , { name := "document-offset-past-end", doc := docAb
    , events := strRecord 6 1 (2 ^ 63 + 1000), arena := [], expected := none }
  , { name := "document-huge-offset", doc := docAb
    , events := strRecord 6 1 (2 ^ 64 - 1), arena := [], expected := none }
  , { name := "arena-invalid-utf8", doc := []
    , events := strRecord 6 1 0, arena := [0xFF], expected := none }
  , { name := "document-invalid-utf8", doc := [0x22, 0xFF, 0x22]
    , events := strRecord 6 1 (2 ^ 63 + 1), arena := [], expected := none }
  , { name := "unknown-tag-zero", doc := [], events := [0], arena := []
    , expected := none }
  , { name := "unknown-tag-eleven", doc := [], events := [11], arena := []
    , expected := none }
  , { name := "unknown-tag-255", doc := [], events := [255], arena := []
    , expected := none }
  , { name := "record-then-truncated", doc := [], events := [8, 7, 0]
    , arena := [], expected := none }
  , { name := "long-array-of-numbers", doc := []
    , events := (List.range 2000).flatMap numRecord, arena := []
    , expected := some 2000 }
  ]

/-- One case's row, and whether both the comparison and the expectation hold. -/
def runCase (c : Case) : IO Bool := do
  let doc := ByteString.literal c.doc
  let events := ByteString.literal c.events
  let arena := ByteString.literal c.arena
  let indexed := eventsOfBytesIndexed doc events arena
  let listed := eventsOfBytes doc.toList events.toList arena.toList
  let agree := decide (indexed = listed)
  let expectedOK :=
    match c.expected, indexed with
    | none, none => true
    | some n, some ces => ces.length == n
    | _, _ => false
  let eventsField := match indexed with
    | some ces => toString ces.length
    | none => "none"
  if !agree then
    IO.eprintln s!"indexed-reader: {c.name}: the readers disagree \
      (indexed={repr indexed}, listed={repr listed})"
  else if !expectedOK then
    IO.eprintln s!"indexed-reader: {c.name}: expected \
      {repr c.expected}, got {repr indexed}"
  else
    IO.println s!"indexed-reader: {c.name} agree events={eventsField}"
  return agree && expectedOK

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    if !(← runCase c) then
      failures := failures + 1
  if failures != 0 then
    IO.eprintln s!"indexed-reader: {failures} of {cases.length} cases failed"
    return 1
  IO.println s!"indexed-reader: ok — {cases.length} cases, both readers agree"
  return 0

end JsonIndexedReader

/-- `lean --run` looks for an unnamespaced `main`; the cases run from
`JsonIndexedReader.main`. -/
def main : IO UInt32 := JsonIndexedReader.main
