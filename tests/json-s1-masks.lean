/-
JS2, JS3, and the fixture pin of JS1 for the stage-1 mask unit.

The fixture is `probes/install/ir/json-s1-masks.candidate.ll`, read through the
module that pins it: `firstFunction` of the committed text is exactly
`s1MasksFunction`, and its name, return type and parameter list are asserted
here.  The parser's own accepted and refused spellings are in
`tests/json-s1-parser.lean`, which imports `LeanLLVM` only; this file neither
imports nor repeats them.

The body's run over a mixed 64-byte block under three carry states is compared
against hand-written words, with three clause witnesses; the block layer's own
mask over the same block is asserted as the union of five hand-written words.
Every observation is a `#guard`, so a failed one stops elaboration with a
nonzero exit status; no compiler, proof checker, service, clock or network is
reached.  Elaborated by
`nix develop -c lake env lean tests/json-s1-masks.lean`.
-/
import LeanLLVM
import LeanLLVM.Refinement.JsonS1MasksIR

namespace JsonS1MasksScenario

open LeanLLVM
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonScanSpec

/-! ### JS1 — the fixture is the pinned AST -/

/-- The single function a parsed text holds. -/
def soleFunction (m : Module) : Option Function :=
  match m.functions with
  | [f] => some f
  | _ => none

-- The committed fixture parses to the AST the module pins.
#guard decide (firstFunction s1MasksSrc = some s1MasksFunction)

-- Its name, return type and parameter list.
#guard
  match parseModule s1MasksSrc with
  | .ok m =>
      match soleFunction m with
      | some f =>
          f.name = "leanllvm_json_s1_masks" ∧
          f.retTy = Ty.void ∧
          f.params = [("%p", Ty.ptr), ("%c", Ty.ptr), ("%o", Ty.ptr)]
      | none => false
  | .error _ => false

/-! ### The mixed block, staged at a misaligned address -/

/-- The route's mixed 64-byte block: unescaped and escaped quotes, backslash
runs of length one, two and three, all six delimiter classes, all four
whitespace bytes, control bytes with and without the whitespace class, `0x7F`,
and ordinary content.  Byte 0 is `"` and byte 63 is `"`, so both ends of the
block carry a string state. -/
def blockBytes : List UInt8 :=
  [ 0x22, 0x6B, 0x5C, 0x22, 0x2C, 0x20, 0x31, 0x5D,
    0x0A, 0x09, 0x0D, 0x5C, 0x5C, 0x22, 0x3A, 0x78,
    0x22, 0x61, 0x22, 0x7B, 0x7D, 0x5B, 0x5D, 0x2C,
    0x20, 0x01, 0x1F, 0x7F, 0x22, 0x5C, 0x74, 0x22,
    0x5C, 0x6E, 0x22, 0x2C, 0x09, 0x5C, 0x22, 0x3A,
    0x64, 0x5B, 0x5D, 0x7B, 0x7D, 0x20, 0x0D, 0x30,
    0x22, 0x5C, 0x5C, 0x5C, 0x22, 0x2C, 0x76, 0x20,
    0x09, 0x0A, 0x22, 0x7A, 0x1F, 0x79, 0x5C, 0x22 ]

/-- The low half of the block. -/
def lo (i : Fin 32) : UInt8 :=
  blockBytes.get ⟨i.1, by
    have h : blockBytes.length = 64 := rfl
    omega⟩

/-- The high half of the block. -/
def hi (i : Fin 32) : UInt8 :=
  blockBytes.get ⟨i.1 + 32, by
    have h : blockBytes.length = 64 := rfl
    omega⟩

/-- The 96-byte buffer's base; the block starts at `blockBase + 1`. -/
def blockBase : Nat := 8192

/-- The pointer the body is called with: offset 1 of the buffer. -/
def pAddr : Nat := blockBase + 1

/-- The 24-byte carry slot. -/
def carryAddr : Nat := 9200

/-- The 48-byte output slot. -/
def outAddr : Nat := 9400

/-- The byte the output slot is pre-filled with, so a store the body does not
make reads back as a sentinel. -/
def slotSentinel : UInt8 := 0xA5

/-- `bs` laid out cell by cell from `addr`. -/
def bytesAt (addr : Nat) (bs : List UInt8) : Mem :=
  bs.zipIdx.map fun (b, i) => (addr + i, b)

/-- The inbound carry slot's 24 bytes: the kernel's `open`, `ppar` and
`im_carry` words, normalised to zero or all-ones.  The binder is `opened`
because `open` is a command keyword. -/
def carryBytes (opened ppar inside : Bool) : List UInt8 :=
  natToBytes (if opened then 1 else 0) 8 ++
  natToBytes (if ppar then 1 else 0) 8 ++
  natToBytes (if inside then 0xFFFFFFFFFFFFFFFF else 0) 8

/-- The memory a row is run from: the block at `pAddr`, the carry at
`carryAddr`, and the output slot filled with sentinels. -/
def stagingMem (bs : List UInt8) (opened ppar inside : Bool) : Mem :=
  bytesAt pAddr bs ++ bytesAt carryAddr (carryBytes opened ppar inside) ++
    bytesAt outAddr (List.replicate 48 slotSentinel)

/-- The little-endian bytes of a list of 64-bit words. -/
def slotBytes (ws : List Nat) : List UInt8 := ws.flatMap fun v => natToBytes v 8

/-- Run a function over a staged row, returning its output slot, its carry slot
and its final memory. -/
def runFunction (f : Function) (bs : List UInt8) (opened ppar inside : Bool) :
    Option (List UInt8 × List UInt8 × Mem) :=
  match runFuel s1Calls 10000 f
      { (initState f [.ptr pAddr, .ptr carryAddr, .ptr outAddr]) with
        mem := stagingMem bs opened ppar inside } with
  | some (.ret _ mem) =>
      match readBytes mem outAddr 48, readBytes mem carryAddr 24 with
      | some o, some c => some (o, c, mem)
      | _, _ => none
  | _ => none

/-- The two words a row observes: the output slot and the carry slot. -/
def masksOf (f : Function) (bs : List UInt8) (opened ppar inside : Bool) :
    Option (List UInt8 × List UInt8) :=
  (runFunction f bs opened ppar inside).map fun t => (t.1, t.2.1)

/-! ### JS2 — the body returns the hand-written six masks and carry under
three carry states -/

/-- Quote, delimiter, in-string, whitespace, backslash, control: the clean
state's six words. -/
def cleanWords : List Nat :=
  [0x0401000490052001, 0x00201E8800F84090, 0xFC00FFFC70031FFF,
   0x0380601001000720, 0x400E002120001804, 0x1300401006000700]

/-- The same six words when the block is entered inside a string: only the
in-string word moves. -/
def insideWords : List Nat :=
  [0x0401000490052001, 0x00201E8800F84090, 0x03FF00038FFCE000,
   0x0380601001000720, 0x400E002120001804, 0x1300401006000700]

/-- The same six words when the block is entered with an odd backslash run
open: the first quote is escaped and the string state enters closed. -/
def oddRunWords : List Nat :=
  [0x0401000490052000, 0x00201E8800F84090, 0x03FF00038FFCE000,
   0x0380601001000720, 0x400E002120001804, 0x1300401006000700]

#guard masksOf s1MasksFunction blockBytes false false false =
  some (slotBytes cleanWords, slotBytes [0, 0, 0xFFFFFFFFFFFFFFFF])

#guard masksOf s1MasksFunction blockBytes false false true =
  some (slotBytes insideWords, slotBytes [0, 0, 0])

#guard masksOf s1MasksFunction blockBytes true true false =
  some (slotBytes oddRunWords, slotBytes [0, 0, 0])

/-- A byte is inside the carry or output slot. -/
def inSlots (a : Nat) : Bool :=
  decide (carryAddr ≤ a ∧ a < carryAddr + 24) ||
    decide (outAddr ≤ a ∧ a < outAddr + 48)

-- No byte outside the two slots moved, under the clean state.
#guard
  match runFunction s1MasksFunction blockBytes false false false with
  | some (_, _, mem') =>
      (List.range 1600).all fun i =>
        let a := blockBase + i
        inSlots a || readByte mem' a = readByte (stagingMem blockBytes false false false) a
  | none => false

/-! #### The three clause witnesses

Each witness is an **edited expectation**, run against the same body: a
scenario whose expectation was edited to match a witness fails that witness's
guard, which is what makes the witnesses falsifiable rather than descriptive. -/

/-- The complement of a 64-bit word, as arithmetic. -/
def notWord (v : Nat) : Nat := 0xFFFFFFFFFFFFFFFF - v

/-- The comma lanes of the mixed block: lanes 4 and 23 in the low half, 35 and
53 in the high half, as a 64-bit mask. -/
def commaLaneMask : Nat := 0x0020000800800010

/-- A 64-bit word with every comma lane cleared — the delimiter word a body
would produce if the comma class's table bit were missing.  For the clean
state's hand-written word this is `0x00001E8000784080`. -/
def clearCommaLanes (v : Nat) : Nat :=
  (BitVec.ofNat 64 v &&& ~~~(BitVec.ofNat 64 commaLaneMask)).toNat

/-- A list of six words with its first word complemented. -/
def complementFirst (ws : List Nat) : List Nat :=
  match ws with
  | q :: rest => notWord q :: rest
  | [] => []

/-- A list of six words with every comma lane cleared from its delimiter word. -/
def clearDelimCommaLanes (ws : List Nat) : List Nat :=
  match ws with
  | q :: d :: rest => q :: clearCommaLanes d :: rest
  | ws => ws

/-- The inbound carry word a state's row is staged with. -/
def carryWord (inside : Bool) : Nat :=
  if inside then 0xFFFFFFFFFFFFFFFF else 0

/-- XOR of a 64-bit word with a carry word that is zero or all-ones. -/
def xorCarry (v c : Nat) : Nat :=
  if c = 0 then v else 0xFFFFFFFFFFFFFFFF - v

/-- A list of six words with the inbound carry XORed into the in-string word a
second time.  With a zero carry that word is unchanged; with an all-ones carry
it is complemented — which is exactly what a body that ignored the carry would
produce in the inside state. -/
def xorCarryIntoInside (ws : List Nat) (carry : Nat) : List Nat :=
  match ws with
  | [q, d, i, w, b, c] => [q, d, xorCarry i carry, w, b, c]
  | ws => ws

-- The quote witness: the first word complemented.  The run differs from it in
-- all three states, so the output clause does not hold for a complemented
-- quote word whichever carry enters.
#guard masksOf s1MasksFunction blockBytes false false false ≠
  some (slotBytes (complementFirst cleanWords), slotBytes [0, 0, 0xFFFFFFFFFFFFFFFF])
#guard masksOf s1MasksFunction blockBytes false false true ≠
  some (slotBytes (complementFirst insideWords), slotBytes [0, 0, 0])
#guard masksOf s1MasksFunction blockBytes true true false ≠
  some (slotBytes (complementFirst oddRunWords), slotBytes [0, 0, 0])

-- The delimiter witness: the block's four commas sit at lanes 4, 23, 35 and
-- 53, so a body whose comma-class table bit is missing would report the clean
-- state's delimiter word with all four of those lanes cleared,
-- `0x00001E8000784080`.  That is the wrong body the witness names, not an
-- arbitrary perturbation.
#guard masksOf s1MasksFunction blockBytes false false false ≠
  some (slotBytes (clearDelimCommaLanes cleanWords),
    slotBytes [0, 0, 0xFFFFFFFFFFFFFFFF])

-- The carry witness, as a pair: with the clean state's zero carry the second
-- XOR changes nothing, so the run equals the witness; with the inside state's
-- all-ones carry the witness is the word a carry-ignoring body would produce,
-- and the run differs from it.  A witness that differed in both states would
-- show only that the word can be perturbed.
#guard masksOf s1MasksFunction blockBytes false false false =
  some (slotBytes (xorCarryIntoInside cleanWords (carryWord false)),
    slotBytes [0, 0, 0xFFFFFFFFFFFFFFFF])

#guard masksOf s1MasksFunction blockBytes false false true ≠
  some (slotBytes (xorCarryIntoInside insideWords (carryWord true)),
    slotBytes [0, 0, 0])

/-! ### JS3 — the block layer's mask is the union of five hand-written words -/

-- The five words the block layer's predicate covers, written out, and their
-- union.
#guard
  (BitVec.ofNat 64 0x0401000490052001 ||| BitVec.ofNat 64 0x8010004000000008 |||
     BitVec.ofNat 64 0x00201E8800F84090 ||| BitVec.ofNat 64 0x400E002120001804 |||
     BitVec.ofNat 64 0x0380601001000720) =
    BitVec.ofNat 64 0xC7BF7EFDB1FD7FBD

-- `maskOfList` over the two halves, joined, is that same union.
#guard
  mask64 (maskOfList (List.ofFn lo)) (maskOfList (List.ofFn hi)) =
    (BitVec.ofNat 64 0x0401000490052001 ||| BitVec.ofNat 64 0x8010004000000008 |||
       BitVec.ofNat 64 0x00201E8800F84090 ||| BitVec.ofNat 64 0x400E002120001804 |||
       BitVec.ofNat 64 0x0380601001000720)

end JsonS1MasksScenario
