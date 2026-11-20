/-
The contracted block unit's route row: the pinned AST, run under the repository's
semantics, emits the entry words the specification names.

`JsonS1BlocksIR` pins `s1BlocksFunction` to the committed fixture.  This file
runs that body over a handful of documents — a single byte, a sixty-three-byte
prefix, a full mixed block, a block plus one byte, and a stray backslash — with
the gate off, and compares the bytes it leaves in `ent` with
`wordsOf (stage1Words bs)`: the specification's entry words, one per block, with
the classifier carry and the scalar run start carried between blocks and the
final partial block clamped.

The run is the semantics' (`runFuel` over the pinned AST), not a model of it: the
classifier's two intrinsics are the mask unit's own call environment (`s1Calls`),
and a `void` return with no escape list is what the gate-off arm asks for.  Every
observation is a `#guard`, so a failed one stops elaboration with a nonzero exit
status; no compiler, proof checker, service, clock or network is reached.

The object half of the route — the same rows from `kernel/json/s1_blocks.c`
compiled at the measured line, its controls and the corpus — is not this file.
Elaborated by `nix develop -c lake env lean tests/json-s1-blocks.lean`.
-/
import LeanLLVM.Semantics
import LeanLLVM.Refinement.JsonS1MasksIR
import LeanLLVM.Refinement.JsonS1BlocksIR
import LeanLLVM.Refinement.JsonEntSpec

namespace JsonS1BlocksScenario

open LeanLLVM
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR (s1Calls)

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- The document's base: the padded window is staged here. -/
def docAddr : Nat := 16

/-- The `ent` array's address. -/
def entAddr : Nat := 4096

/-- The escape list's cursor slots, staged so a gate-on write would be visible. -/
def xpAddr : Nat := 8192
def nxpAddr : Nat := 8296
def xcarryAddr : Nat := 8384

/-- The sentinel byte the scratch a gate-off run must not touch is filled with. -/
def sentinel : UInt8 := 0xA5

/-- The `ent` array's staged bytes: eight sentinels per block. -/
def entStaging (n : Nat) : List UInt8 :=
  List.replicate (8 * blocksOf n) sentinel

/-- The staging a row is run from: the padded window, the sentinel-filled `ent`
array, and the three escape-list objects. -/
def staging (bs : List UInt8) : Mem :=
  bytesAt docAddr (padded bs) ++ bytesAt entAddr (entStaging bs.length) ++
    bytesAt xpAddr (List.replicate 64 sentinel) ++
    bytesAt nxpAddr (List.replicate 8 sentinel) ++
    bytesAt xcarryAddr (List.replicate 16 sentinel)

/-- The body's run over a document, gate off: the bytes it leaves in `ent`, and
its final memory. -/
def runDoc (bs : List UInt8) : Option (List UInt8 × Mem) :=
  match runFuel s1Calls 100000 s1BlocksFunction
      { (initState s1BlocksFunction
          [.ptr docAddr, .int 64 bs.length, .ptr entAddr, .ptr xpAddr,
           .ptr nxpAddr, .ptr xcarryAddr, .int 64 0]) with
        mem := staging bs } with
  | some (.ret _ mem) =>
      match readBytes mem entAddr (8 * blocksOf bs.length) with
      | some o => some (o, mem)
      | none => none
  | _ => none

/-- The little-endian bytes of the specification's words. -/
def slotBytes (ws : List (BitVec 64)) : List UInt8 :=
  ws.flatMap fun w => natToBytes w.toNat 8

/-- A row: `ent` is the specification's bytes, and the escape list's three
objects were not touched. -/
def rowHolds (bs : List UInt8) : Bool :=
  match runDoc bs with
  | some (o, mem) =>
      o == slotBytes (stage1Words bs) &&
        decide (readBytes mem xpAddr 64 = some (List.replicate 64 sentinel)) &&
        decide (readBytes mem nxpAddr 8 = some (List.replicate 8 sentinel)) &&
        decide (readBytes mem xcarryAddr 16 = some (List.replicate 16 sentinel))
  | none => false

/-- The mixed block the mask unit's scenario stages: unescaped and escaped
quotes, backslash runs of length one, two and three, all six delimiter classes,
all four whitespace bytes, control bytes, `0x7F`, and ordinary content. -/
def mixedBlock : List UInt8 :=
  [ 0x22, 0x6B, 0x5C, 0x22, 0x2C, 0x20, 0x31, 0x5D,
    0x0A, 0x09, 0x0D, 0x5C, 0x5C, 0x22, 0x3A, 0x78,
    0x22, 0x61, 0x22, 0x7B, 0x7D, 0x5B, 0x5D, 0x2C,
    0x20, 0x01, 0x1F, 0x7F, 0x22, 0x5C, 0x74, 0x22,
    0x5C, 0x6E, 0x22, 0x2C, 0x09, 0x5C, 0x22, 0x3A,
    0x64, 0x5B, 0x5D, 0x7B, 0x7D, 0x20, 0x0D, 0x30,
    0x22, 0x5C, 0x5C, 0x5C, 0x22, 0x2C, 0x76, 0x20,
    0x09, 0x0A, 0x22, 0x7A, 0x1F, 0x79, 0x5C, 0x22 ]

-- One byte: the peeled partial block, clamped to one lane.
#guard rowHolds [0x22]
-- One byte that is a backslash: the run carries out of the document.
#guard rowHolds [0x5C]
-- Sixty-three bytes: the peeled block is all but one lane.
#guard rowHolds (mixedBlock.take 63)
-- A full block: the loop's body, no tail.
#guard rowHolds mixedBlock
-- A block plus one byte: one loop iteration and a one-lane tail.
#guard rowHolds (mixedBlock ++ [0x5D])
-- Two blocks: the run start and both classifier carries cross the boundary.
#guard rowHolds (mixedBlock ++ mixedBlock)

-- The row's detector discriminates: a delimiter followed by content starts two
-- runs, the same content without the delimiter starts one, so the two words are
-- not equal and a comparison that matched everything would fail here.
#guard
  match runDoc [0x5D, 0x41] with
  | some (o, _) => o != slotBytes (stage1Words [0x41, 0x41])
  | none => false
-- And the two runs' words are what the difference is: the delimiter's word has
-- lane zero, and the lane after it starts a run.
#guard
  match runDoc [0x5D, 0x41], runDoc [0x41, 0x41] with
  | some (q, _), some (a, _) => q != a
  | _, _ => false

end JsonS1BlocksScenario
