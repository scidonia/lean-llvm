/-
JE2, JE3, the fixture pin, and the four clause witnesses of the entry unit.

The fixture is `probes/install/ir/json-entry.candidate.ll`, read through the
module that pins it: `LeanLLVM/Refinement/JsonEntryIR.lean`.  `firstFunction` of the
committed text is exactly `entryPos8Function`, and the module's two functions
are the POS8 and B8 bodies the theorem is stated over.

JE2 runs the pinned POS8 body through `runFuel` over a mixed three-block mask
stream — an empty block and two blocks with lanes 1 and 4, whose top group byte
is zero — with the output buffer pre-filled with `0xA5`, and asserts the returned count,
the first `k'` words (the two pre-cursor sentinel words then the positions), the
eight words at `[k', k'+8)`, and the sentinel word at `k'+8` — the first lane
neither kernel writes.  JE3 runs both kernels over the same stream and asserts
one stream.

The four clause witnesses follow, each a separate `#guard` over an edited
expectation, so a failure names the clause: the entry word's scalar-run term
(and its carry), the tail mask at the block's end, the table row for a
single-lane mask, and the claim that the overshoot region is zero.

Every observation is a `#guard`, so a failed one stops elaboration with a
nonzero exit status; no compiler, proof checker, service, clock or network is
reached.  Elaborated by
`nix develop -c lake env lean tests/json-entry.lean`.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonEntryIR

namespace JsonEntryScenario

open LeanLLVM
open LeanLLVM.Refinement.JsonEntryIR
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanSpec

/-! ### The fixture is the pinned AST -/

-- The committed fixture parses to the POS8 body the module pins.
#guard decide (firstFunction jsonEntrySrc = some entryPos8Function)

-- And its second function is the B8 body, so the one text is the subject of
-- both kernels rather than two texts that could drift apart.
#guard
  match parseModule jsonEntrySrc with
  | .ok m => m.functions = [entryPos8Function, entryB8Function]
  | .error _ => false

/-! ### One row, staged at the ABI

The row is the measured call's own shape — `(ent, blk0, nblk, out, k)` — with
the fixture's table base appended for the POS8 body (the capture rewrites the
table symbol into a parameter).  The output buffer is pre-filled with `0xA5`,
so a store the body does not make, and the word at `k'+8`, read back as
sentinels rather than as stale values. -/

/-- The mixed mask stream: an empty block (the body's `continue`), then two blocks
with lanes 1 and 4.  Both masks keep their top group byte — the byte at lanes
56–63 — zero, so POS8's last group store lands at the final cursor and writes
through `k'+7`, which is the frame end the overshoot witness is about. -/
def streamMasks : List Nat :=
  [0x0000000000000000, 0x0000000000000012, 0x0000000000000012]

/-- The stream's base block index. -/
def blk0 : Nat := 0

/-- The cursor the row starts at, so the returned count is not the position
total and the absolute positions are what the words hold. -/
def k0 : Nat := 2

/-- The mask stream's address. -/
def entAddr : Nat := 8192

/-- The table's address: past the stream's 24 bytes. -/
def tabAddr : Nat := 8192 + 64

/-- The output slot's address: past the 8 KiB table. -/
def outAddr : Nat := tabAddr + 8192

/-- The byte the output slot is pre-filled with. -/
def slotSentinel : UInt8 := 0xA5

/-- The output slot's size: the `k'+8` sentinel lane and its neighbours. -/
def outBytes : Nat := 4 * 32

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- The mask stream's bytes. -/
def masksBytes (ms : List Nat) : List UInt8 :=
  ms.flatMap fun m => natToBytes m 8

/-- One little-endian `i32` from four bytes. -/
def wordOf : List UInt8 → Option Nat
  | [a, b, c, d] =>
      some (a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat)
  | _ => none

/-- The `n` little-endian `i32` words at `addr`. -/
def wordsAt (mem : Mem) (addr n : Nat) : Option (List Nat) :=
  (List.range n).mapM fun i => (readBytes mem (addr + 4 * i) 4).bind wordOf

/-- The table's 8 KiB as `pos8Table`: the address-free list `pos8Row` builds, one
row per index — the bytes the row rule gives and nothing about where they live.
The theorem's hypothesis reads it at `%tab`, `readBytes mem tab 8192 = some
pos8Table`, which is why the staging below puts these bytes at `tabAddr` and the
value itself carries no address. -/
def tableBytes : List UInt8 :=
  (List.range 256).flatMap fun m =>
    ((pos8Row m).map fun v => natToBytes v.toNat 4).flatten

-- The table the body reads is the row rule's own 8 KiB, and it is `pos8Table`.
#guard tableBytes.length = 8192
#guard decide (tableBytes = pos8Table)

/-- The memory a row is staged in: the mask stream, the table, and the output
slot filled with sentinels. -/
def stagingMem (table : List UInt8) : Mem :=
  bytesAt entAddr (masksBytes streamMasks) ++ bytesAt tabAddr table ++
    bytesAt outAddr (List.replicate outBytes slotSentinel)

/-- The POS8 body's five measured parameters with the fixture's table base
appended. -/
def pos8Args : List LeanLLVM.Value :=
  [.ptr entAddr, .int 64 blk0, .int 64 (streamMasks.length), .ptr outAddr,
   .int 64 k0, .ptr tabAddr]

/-- The B8 body's five measured parameters, which read no table. -/
def b8Args : List LeanLLVM.Value :=
  [.ptr entAddr, .int 64 blk0, .int 64 (streamMasks.length), .ptr outAddr,
   .int 64 k0]

/-- Run a body over a staged row, and return the returned count, the first `k'`
words, the eight words at `[k', k'+8)` and the word at `k'+8` — the first lane
neither kernel writes, so a body that wrote one lane past its bound shows here.
POS8 reaches `k'+7` (its last group stores eight lanes even at a zero byte) and
B8 reaches `k'+6`, which is why the excluded region is eight lanes wide and the
sentinel is the ninth. -/
def runRow (f : Function) (args : List LeanLLVM.Value) (mem : Mem) :
    Option (Nat × List Nat × List Nat × Nat) :=
  match runFuel entryCalls 100000 f { (initState f args) with mem := mem } with
  | some (.ret (some (.int 64 kv)) mem') =>
      let k' := kv.toNat
      match wordsAt mem' outAddr (k' + 9) with
      | some ws => some (k', ws.take k', (ws.drop k').take 8, ws.getD (k' + 8) 0)
      | none => none
  | _ => none

/-- The word at lane `k'+7`: the last of the eight words at `[k', k'+8)`, and the
frame's last lane.  POS8 writes it and B8 does not, so the two kernels are
distinguishable here and nowhere else in the region. -/
def lastLane (r : Nat × List Nat × List Nat × Nat) : Option Nat := r.2.2.1.getLast?

/-! ### JE2 — the POS8 body emits the positions -/

-- The count is the cursor plus the stream's population count: two blocks carry
-- two lanes each, and the empty block contributes nothing.
#guard
  (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map
    (fun r => r.1) = some 6

-- The first `k'` words are the words at indices 0..5: the cursor starts at 2, so
-- the first two are the untouched sentinels, then block 1's lanes 1 and 4 are 65
-- and 68 and block 2's lanes 1 and 4 are 129 and 132.
#guard
  (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map
    (fun r => r.2.1) = some [0xA5A5A5A5, 0xA5A5A5A5, 65, 68, 129, 132]

-- The word at `k'+8` is still the sentinel, so the body stopped inside its
-- bound; the eight words at `[k', k'+8)` are not compared against the positions
-- the masks define (they hold table-row padding), and the frame's last lane is
-- (iv)'s subject.
#guard
  (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map
    (fun r => r.2.2.2) = some 0xA5A5A5A5

/-! ### JE3 — the two kernels write one stream -/

-- B8 reads no table, and returns the same count over the same stream.
#guard
  (runRow entryB8Function b8Args (stagingMem pos8Table)).map (fun r => r.1) =
    (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map (fun r => r.1)

-- The same first `k'` words, at every row.
#guard
  (runRow entryB8Function b8Args (stagingMem pos8Table)).map (fun r => r.2.1) =
    (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map (fun r => r.2.1)

-- And the same sentinel at `k'+8`, the lane neither kernel writes.
#guard
  (runRow entryB8Function b8Args (stagingMem pos8Table)).map (fun r => r.2.2.2) =
    (runRow entryPos8Function pos8Args (stagingMem pos8Table)).map (fun r => r.2.2.2)

/-! ### the four clause witnesses

Each witness is a value the scenario asserts against, so the assertion is what
refuses it: the wrong word a body with that defect would write, compared with
the word the correct body writes. -/

/-! #### (i) `entry_mask_eq`: the entry word's scalar-run term -/

/-- A block whose lane 1 is a comma between scalars, with scalars elsewhere: the
structural term holds the comma at lane 1, and lanes 0 and 2 each start a
scalar run, so the entry word is `0x7` against the structural `0x2`.  (A quote
at lane 0 would not do: the opening quote puts every lane up to the closing one
inside a string, so no lane would be a scalar start.) -/
def delimiterBlock : List UInt8 :=
  [0x78, 0x2C, 0x79] ++ List.replicate 61 0x78

/-- A block whose lane 0 and lane 63 are scalars, every lane a scalar: the
carry's only reach is lane 0, so this is the block shape in which the run-start
bit at lane 0 and the carry disagree. -/
def carryBlock : List UInt8 :=
  [0x61] ++ List.replicate 62 0x78 ++ [0x61]

/-- The low half of a 64-byte block. -/
def lowHalf (bs : List UInt8) : Block32 :=
  fun i => bs.getD i.1 0

/-- The high half of a 64-byte block. -/
def highHalf (bs : List UInt8) : Block32 :=
  fun i => bs.getD (i.1 + 32) 0

/-- The clean classifier state. -/
def cleanState : ClassState := ⟨false, false⟩

-- The witness: the word a body that emitted only the structural term would
-- write is `0x2`, missing the two run starts at lanes 0 and 2, while the clause's
-- word is `0x7`.  The block refuses the clause.
#guard entryMask64 (lowHalf delimiterBlock) (highHalf delimiterBlock) cleanState false ≠
  structuralOnly64 (lowHalf delimiterBlock) (highHalf delimiterBlock) cleanState

-- The same clause at the carry: with the previous block's top lane a scalar the
-- run reaches lane 0, so a body that ignored the carry writes a start there and
-- the correct body does not.
#guard entryMask64 (lowHalf carryBlock) (highHalf carryBlock) cleanState true ≠
  entryMask64 (lowHalf carryBlock) (highHalf carryBlock) cleanState false

/-! #### (ii) `entry_tail_eq`: the tail mask at the block's end -/

/-- A block with a lane at each end, so the top lane is a kept lane whenever the
document reaches the block's end. -/
def tailBlockMask : BitVec 64 := 0x8000000000000001

-- The clause at its witness: the document ends exactly at the block's end
-- (`lim = 64`), so the last kept lane is the block's top lane.
#guard
  (positionsOf (tailBlockMask &&& limMask 64) 0).take
      (LeanLLVM.Refinement.BitLanes.ctpop (tailBlockMask &&& limMask 64)) =
    (positionsOf tailBlockMask 0).filter (· < 64)

-- The witness refuses it: a body whose tail mask stops at `lim = 63` — the
-- wrong side of the `lim < 64` guard — clears the top lane, and the kept
-- positions differ from the document's.
#guard
  (positionsOf (tailBlockMask &&& limMask 63) 0).take
      (LeanLLVM.Refinement.BitLanes.ctpop (tailBlockMask &&& limMask 63)) ≠
    (positionsOf tailBlockMask 0).filter (· < 64)

/-! #### (iii) the positions clause: the table row for a single-lane mask -/

/-- The table with one row's first entry replaced: the table a body whose row
for that mask held a different first entry would read. -/
def tableWithRow (m : Nat) (first : BitVec 32) : List UInt8 :=
  (List.range 256).flatMap fun i =>
    let row := if i = m then first :: (pos8Row i).drop 1 else pos8Row i
    (row.map fun v => natToBytes v.toNat 4).flatten

-- The row the table rule gives a single-lane mask: the lane, then zeros.
#guard pos8Row 0x01 = [0, 0, 0, 0, 0, 0, 0, 0]

-- The witness refuses the clause: a body reading a table whose row for mask
-- `0x01` held `1` instead of `0` writes `1` where the model's position is `0`.
#guard
  (runRow entryPos8Function
      [.ptr entAddr, .int 64 0, .int 64 1, .ptr outAddr, .int 64 0, .ptr tabAddr]
      (bytesAt entAddr (natToBytes 0x01 8) ++ bytesAt tabAddr (tableWithRow 0x01 1) ++
        bytesAt outAddr (List.replicate outBytes slotSentinel))).map (fun r => r.2.1) =
    some [1]
#guard positionsOf 0x0000000000000001 0 = [0]

/-! #### (iv) the overshoot bound: the region `[k', k'+8)` -/

-- The two kernels differ at the frame's last lane, and only there: POS8's group
-- stores run unconditionally, so with the stream's top group byte zero its final
-- store lands at the final cursor and writes lane `k'+7`, while B8's last written
-- lane is `k'+6`.  A region-is-non-zero test cannot see that difference — a body
-- that stopped one lane early still leaves seven written words and the sentinel
-- — so each kernel is asserted at lane `k'+7` on its own, and each failure names
-- its kernel.

-- POS8 writes lane `k'+7`, so it does not hold the sentinel there.
#guard
  match runRow entryPos8Function pos8Args (stagingMem pos8Table) with
  | some r => lastLane r ≠ some 0xA5A5A5A5
  | none => false

-- B8 does not write it, so lane `k'+7` is untouched for that kernel.
#guard
  match runRow entryB8Function b8Args (stagingMem pos8Table) with
  | some r => lastLane r = some 0xA5A5A5A5
  | none => false

-- Neither kernel writes lane `k'+8`: it is the sentinel for POS8 …
#guard
  match runRow entryPos8Function pos8Args (stagingMem pos8Table) with
  | some r => r.2.2.2 = 0xA5A5A5A5
  | none => false

-- … and for B8.
#guard
  match runRow entryB8Function b8Args (stagingMem pos8Table) with
  | some r => r.2.2.2 = 0xA5A5A5A5
  | none => false

end JsonEntryScenario
