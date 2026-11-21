/-
The fused body's per-page words, against the classifier's and the DFA's.

`JsonS1BlocksLoopFacts` names three links the loop's own arithmetic owes and no
module stated: the page store word `%or84` as `entryMask64`, the DFA arm's
`%or.i281` (and the peeled tail's `%or.i`) as `klErrBlk`'s word, and the peel's
`%u8k.3` as the fold one block further than the loop's accumulator.  This module
states and proves them at the registers the emitted body binds.

## The entry word

`JsonS1BlocksIdentities` relates the mask unit's register spellings to the
classifier's words (`blkEscapedW`, `blkAndQuoteW`, `or19W`, the in-string word),
and `JsonS1BlocksSteps.entry_eq_compose` is the composition that consumes them.
What that module does not carry is the transport from the *fused* body's tables
and registers to the mask unit's: its `%or297` quote comparison is over the
joined byte view of the two loaded words, its `%andClass` pair is the fused
emission's `forBodyTableA`/`forBodyTableB`, and its `%or19`, `%or23` and `%or.i`
are computed at `for.body54`'s own names.  The first half of this module is that
transport: the byte views of the two halves are the mask unit's lane lists, the
two fused tables are its `loTabV`/`hiTabV`, and the class word, the delimiter
word, the *neither* word and the in-string word are the classifier's
`specDelimiter64`, `specSpace64` and `specInString64`.

The entry word's statement keeps only the carried state as a hypothesis — the
body's two shift registers are the carry conjunction (`%st.sroa.0 & %st.sroa.9`),
its third is the in-string seed (`%st.sroa.15`), and `%prevS` is the previous
block's top scalar lane — because those are the loop's phis and not words the
page computes.  The peeled block's `%or135` runs the same chain at
`if.then103`'s registers; that statement is the remaining link to
`PeelWordAtModel` and `stage1Word`, and the module states the page's word only.

## The DFA's word

`JsonUtf8Steps` proves what one block's error vector is — `errHalf`/`errBlk`, the
three table lookups, the two saturating subtracts and the high-bit mask, read as
`klErrBlk`'s bytes.  The fused arms run the same expression at their own
register names and their own window slices, so the identities here are that
expression's: `dfaHalf_eq_errRaw` is one half, `ifThen90_xor1_eq`,
`ifThen90_xor2_eq`, `ifThen144_xor448_eq` and `ifThen144_xor460_eq` are the four
halves at their windows, and `ifThen90_or281_eq` / `ifThen144_orI_eq` fold them
with the carried accumulator through `errRawBlk_word_eq`.  With the accumulator's
invariant `packLanes u8k = bytesToNat (klAcc bs i)`, `packLanes_or281_eq` is
`klAcc`'s step at the page's block.

## The peeled accumulator

`%u8k.3 = %or.i = %195 ||| %u8k.1.lcssa` on the peeled tail's arm, so the
packed word is the fold at `shr + 1`; when that is the document's block count,
`klAll_eq_klAcc_succ` reads `klAll` at the gate as `klAcc bs shr ||| klErrBlk`,
and `acc_pack_of_peel` gives the staging's accumulator field at the merge's
word (`packLanes_unpackLanes_klAll` is the word's own round trip).
-/
import LeanLLVM.Refinement.JsonS1BlocksIdentities
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksTail
import LeanLLVM.Refinement.JsonS1BlocksLoop
import LeanLLVM.Refinement.JsonUtf8Fused

namespace LeanLLVM.Refinement.JsonS1BlocksWordIdentities

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.Pclmul (clmul seedVec)
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.JSON
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.JsonUtf8Steps

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Lane-list bridges

The body reads a half as `<4 x i64>`, casts it to `<32 x i8>` and takes nibbles;
the mask unit names the same three lists `loLanes`/`hiLanes`, `nibLanes` and
`hiNibbleLanes`.  These four lemmas are the two spellings' agreement, and the
tables' is one `decide` each. -/

/-- `zipWith` is the `zip`-then-`map` the mask unit's `andLanes` writes. -/
theorem zipWith_eq_zip_map {α β γ : Type} (f : α → β → γ) :
    ∀ (a : List α) (b : List β),
      List.zipWith f a b = (a.zip b).map (fun p : α × β => f p.1 p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
      rw [List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons]
      exact congrArg _ (zipWith_eq_zip_map f xs ys)

/-- The two fused tables are the mask unit's `s1f_lo_tab`/`s1f_hi_tab` lane lists. -/
theorem forBodyTableA_eq_loTabV : forBodyTableA = loTabV := by decide

theorem forBodyTableB_eq_hiTabV : forBodyTableB = hiTabV := by decide

/-- A half's byte view is the mask unit's lane list.  `%111`'s bitcast is the
packed word's bytes, and `loWord` is the same natural. -/
theorem bitcast_bytes_eq (B : List UInt8) (hB : B.length = 32) :
    bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat B)) = byteLanes B := by
  have hlt : bytesToNat B < 2 ^ 256 := by
    have h := bytesToNat_lt B
    rw [hB, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
    exact h
  rw [bitcastVecLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt hlt, byteLanes_eq_unpackLanes hB]

/-- A byte's low nibble, over a half's byte view: the body's `& 0x0F`. -/
theorem byteView_lowNibble (B : List UInt8) (hB : B.length = 32) :
    (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat B))).map
        (fun x => x &&& 0x0f#8) = nibLanes (byteLanes B) := by
  rw [bitcast_bytes_eq B hB]
  rfl

/-- A byte's high nibble, over a half's byte view: the body's `<16 x i16>` shift
and `& 0x0F`. -/
theorem byteView_highNibble (B : List UInt8) (hB : B.length = 32) :
    (bitcastVecLanes 8 32
      ((bitcastVecLanes 16 16 (unpackLanes 64 4 (bytesToNat B))).map
        (fun x : BitVec 16 => x >>> 4))).map (fun x => x &&& 0x0f#8)
      = hiNibbleLanes (bytesToNat B) := by
  have hlt : bytesToNat B < 2 ^ 256 := by
    have h := bytesToNat_lt B
    rw [hB, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
    exact h
  have hV : bitcastVecLanes 16 16 (unpackLanes 64 4 (bytesToNat B))
      = unpackLanes 16 16 (bytesToNat B) := by
    have hp : packLanes (unpackLanes 64 4 (bytesToNat B)) = bytesToNat B := by
      rw [packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
        Nat.mod_eq_of_lt hlt]
    rw [bitcastVecLanes, hp]
  rw [hV]
  have hshr : (unpackLanes 16 16 (bytesToNat B)).map (fun x : BitVec 16 => x >>> 4)
      = shr4Lanes (bytesToNat B) := rfl
  rw [hshr]
  rw [bitcastVecLanes]
  exact nibbleLanes_eq (bytesToNat B)

/-- The byte view of a half is the mask unit's lane list at the mask unit's own
word. -/
theorem bitcast_bytes_eq_loLanes (k : Ctx) :
    bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat (List.ofFn k.lo)))
      = loLanes k := by
  rw [bitcast_bytes_eq _ (by simp), byteLanes_ofFn]
  rfl

theorem bitcast_bytes_eq_hiLanes (k : Ctx) :
    bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat (List.ofFn k.hi)))
      = hiLanes k := by
  rw [bitcast_bytes_eq _ (by simp), byteLanes_ofFn]
  rfl

/-! ### The page's fields, at the block's own names

Each accessor is the `for.body54` binding it names, at the two loaded halves and
the carried state; the proofs are `rfl`, because the values are that block's own
`let` chain.  They keep the identities below at the register spellings the
emission uses, so a reader can match a line of the proof to a line of the body. -/

theorem fb54_byte73 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).byte73
      = bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs73)) := rfl

theorem fb54_byte74 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).byte74
      = bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs74)) := rfl

theorem fb54_joinBytes (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).joinBytes
      = bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
          unpackLanes 64 4 (bytesToNat bs74)) := rfl

theorem fb54_cmp8 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmp8
      = icmpLanes .eq (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
          unpackLanes 64 4 (bytesToNat bs74))) (List.replicate 64 0x22#8) := rfl

theorem fb54_or297 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or297
      = BitVec.ofNat 64 (lanesToNat (icmpLanes .eq
          (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
            unpackLanes 64 4 (bytesToNat bs74))) (List.replicate 64 0x22#8))) := rfl

theorem fb54_cmp39 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmp39
      = icmpLanes .eq (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs73)))
          (List.replicate 32 0x5c#8) := rfl

theorem fb54_mask81 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).mask81
      = BitVec.ofNat 32 (lanesToNat (icmpLanes .eq
          (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs73)))
            (List.replicate 32 0x5c#8))) := rfl

theorem fb54_conv9 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).conv9
      = BitVec.ofNat 64 (fusedValues c bs73 bs74).mask81.toNat := rfl

theorem fb54_cmpii (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmpii
      = icmpLanes .eq (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs74)))
          (List.replicate 32 0x5c#8) := rfl

theorem fb54_mask82 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).mask82
      = BitVec.ofNat 32 (lanesToNat (icmpLanes .eq
          (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs74)))
            (List.replicate 32 0x5c#8))) := rfl

theorem fb54_conv12 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).conv12
      = BitVec.ofNat 64 (fusedValues c bs73 bs74).mask82.toNat := rfl

theorem fb54_shl13 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shl13
      = (fusedValues c bs73 bs74).conv12 <<< (0x0000000000000020#64).toNat := rfl

theorem fb54_or14 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or14
      = (fusedValues c bs73 bs74).shl13 ||| (fusedValues c bs73 bs74).conv9 := rfl

theorem fb54_andII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).andII = c.st0 &&& c.st9 := rfl

theorem fb54_shlII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shlII
      = (fusedValues c bs73 bs74).or14 <<< (0x0000000000000001#64).toNat := rfl

theorem fb54_notII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).notII
      = (fusedValues c bs73 bs74).shlII ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_and1II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and1II
      = (fusedValues c bs73 bs74).or14 &&& (fusedValues c bs73 bs74).notII := rfl

theorem fb54_xorII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).xorII
      = (fusedValues c bs73 bs74).andII ^^^ 0x5555555555555555#64 := rfl

theorem fb54_and2II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and2II
      = (fusedValues c bs73 bs74).and1II &&& (fusedValues c bs73 bs74).xorII := rfl

theorem fb54_xor3II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).xor3II
      = (fusedValues c bs73 bs74).and2II ^^^ (fusedValues c bs73 bs74).and1II := rfl

theorem fb54_not4II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).not4II
      = (fusedValues c bs73 bs74).or14 ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_addII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).addII
      = (fusedValues c bs73 bs74).and2II + (fusedValues c bs73 bs74).or14 := rfl

theorem fb54_add5II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).add5II
      = (fusedValues c bs73 bs74).xor3II + (fusedValues c bs73 bs74).or14 := rfl

theorem fb54_and6II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and6II
      = (fusedValues c bs73 bs74).not4II &&& 0xaaaaaaaaaaaaaaaa#64 := rfl

theorem fb54_and7II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and7II
      = (fusedValues c bs73 bs74).and6II &&& (fusedValues c bs73 bs74).addII := rfl

theorem fb54_and8II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and8II
      = (fusedValues c bs73 bs74).not4II &&& 0x5555555555555555#64 := rfl

theorem fb54_and9II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and9II
      = (fusedValues c bs73 bs74).and8II &&& (fusedValues c bs73 bs74).add5II := rfl

theorem fb54_and11II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and11II
      = (fusedValues c bs73 bs74).andII &&& (fusedValues c bs73 bs74).not4II := rfl

theorem fb54_orII (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).orII
      = (fusedValues c bs73 bs74).and7II ||| (fusedValues c bs73 bs74).and11II := rfl

theorem fb54_or12II (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or12II
      = (fusedValues c bs73 bs74).orII ||| (fusedValues c bs73 bs74).and9II := rfl

theorem fb54_notI (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).notI
      = (fusedValues c bs73 bs74).or12II ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_andI (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).andI
      = (fusedValues c bs73 bs74).or297 &&& (fusedValues c bs73 bs74).notI := rfl

theorem fb54_low85 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low85
      = (fusedValues c bs73 bs74).byte73.map (fun x => x &&& 0x0f#8) := rfl

theorem fb54_shuf86 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shuf86
      = pshufbLanes forBodyTableA (fusedValues c bs73 bs74).low85 := rfl

theorem fb54_half83 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).half83
      = bitcastVecLanes 16 16 (unpackLanes 64 4 (bytesToNat bs73)) := rfl

theorem fb54_shr84 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shr84
      = (fusedValues c bs73 bs74).half83.map (fun x : BitVec 16 => x >>> (0x0004#16).toNat) := rfl

theorem fb54_byte87 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).byte87
      = bitcastVecLanes 8 32 (fusedValues c bs73 bs74).shr84 := rfl

theorem fb54_low88 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low88
      = (fusedValues c bs73 bs74).byte87.map (fun x => x &&& 0x0f#8) := rfl

theorem fb54_shuf89 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shuf89
      = pshufbLanes forBodyTableB (fusedValues c bs73 bs74).low88 := rfl

theorem fb54_andClass1 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).andClass1
      = List.zipWith (fun x y => x &&& y) (fusedValues c bs73 bs74).shuf89
          (fusedValues c bs73 bs74).shuf86 := rfl

theorem fb54_and90 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and90
      = (fusedValues c bs73 bs74).andClass1.map (fun x => x &&& 0x3f#8) := rfl

theorem fb54_cmp21 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmp21
      = icmpLanes .eq (fusedValues c bs73 bs74).and90
          (List.replicate 32 0x00#8) := rfl

theorem fb54_mask91 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).mask91
      = BitVec.ofNat 32 (lanesToNat (fusedValues c bs73 bs74).cmp21) := rfl

theorem fb54_not46 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).not46
      = (fusedValues c bs73 bs74).mask91 ^^^ 0xffffffff#32 := rfl

theorem fb54_half92 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).half92
      = bitcastVecLanes 16 16 (unpackLanes 64 4 (bytesToNat bs74)) := rfl

theorem fb54_shr93 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shr93
      = (fusedValues c bs73 bs74).half92.map (fun x : BitVec 16 => x >>> (0x0004#16).toNat) := rfl

theorem fb54_low94 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low94
      = (fusedValues c bs73 bs74).byte74.map (fun x => x &&& 0x0f#8) := rfl

theorem fb54_shuf95 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shuf95
      = pshufbLanes forBodyTableA (fusedValues c bs73 bs74).low94 := rfl

theorem fb54_byte96 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).byte96
      = bitcastVecLanes 8 32 (fusedValues c bs73 bs74).shr93 := rfl

theorem fb54_low97 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).low97
      = (fusedValues c bs73 bs74).byte96.map (fun x => x &&& 0x0f#8) := rfl

theorem fb54_shuf98 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shuf98
      = pshufbLanes forBodyTableB (fusedValues c bs73 bs74).low97 := rfl

theorem fb54_andClass2 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).andClass2
      = List.zipWith (fun x y => x &&& y) (fusedValues c bs73 bs74).shuf98
          (fusedValues c bs73 bs74).shuf95 := rfl

theorem fb54_and99 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and99
      = (fusedValues c bs73 bs74).andClass2.map (fun x => x &&& 0x3f#8) := rfl

theorem fb54_cmp48 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmp48
      = icmpLanes .eq (fusedValues c bs73 bs74).and99
          (List.replicate 32 0x00#8) := rfl

theorem fb54_mask100 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).mask100
      = BitVec.ofNat 32 (lanesToNat (fusedValues c bs73 bs74).cmp48) := rfl

theorem fb54_not49 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).not49
      = (fusedValues c bs73 bs74).mask100 ^^^ 0xffffffff#32 := rfl

theorem fb54_conv16 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).conv16
      = BitVec.ofNat 64 (fusedValues c bs73 bs74).not46.toNat := rfl

theorem fb54_conv17 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).conv17
      = BitVec.ofNat 64 (fusedValues c bs73 bs74).not49.toNat := rfl

theorem fb54_shl18 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shl18
      = (fusedValues c bs73 bs74).conv17 <<< (0x0000000000000020#64).toNat := rfl

theorem fb54_or19 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or19
      = (fusedValues c bs73 bs74).shl18 ||| (fusedValues c bs73 bs74).conv16 := rfl

theorem fb54_join64 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).join64
      = (fusedValues c bs73 bs74).andClass1 ++ (fusedValues c bs73 bs74).andClass2 := rfl

theorem fb54_cmp30 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).cmp30
      = icmpLanes .eq (fusedValues c bs73 bs74).join64
          (List.replicate 64 0x00#8) := rfl

theorem fb54_or23 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or23
      = BitVec.ofNat 64 (lanesToNat (fusedValues c bs73 bs74).cmp30) := rfl

theorem fb54_vecext (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).vecext
      = clmul (BitVec.ofNat 64 (fusedValues c bs73 bs74).andI.toNat) (BitVec.allOnes 64) := rfl

theorem fb54_xorI (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).xorI
      = (fusedValues c bs73 bs74).vecext ^^^ c.st15 := rfl

theorem fb54_not74 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).not74
      = (fusedValues c bs73 bs74).xorI ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_v104 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).v104
      = (fusedValues c bs73 bs74).andI ||| (fusedValues c bs73 bs74).xorI := rfl

theorem fb54_v105 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).v105
      = (fusedValues c bs73 bs74).v104 ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_and75 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and75
      = (fusedValues c bs73 bs74).or23 &&& (fusedValues c bs73 bs74).v105 := rfl

theorem fb54_and78 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and78
      = (fusedValues c bs73 bs74).or19 &&& (fusedValues c bs73 bs74).not74 := rfl

theorem fb54_shl80 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).shl80
      = (fusedValues c bs73 bs74).and75 <<< (0x0000000000000001#64).toNat := rfl

theorem fb54_or81 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or81
      = (fusedValues c bs73 bs74).shl80 ||| c.prevS := rfl

theorem fb54_not82 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).not82
      = (fusedValues c bs73 bs74).or81 ^^^ 0xffffffffffffffff#64 := rfl

theorem fb54_and83 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).and83
      = (fusedValues c bs73 bs74).and75 &&& (fusedValues c bs73 bs74).not82 := rfl

theorem fb54_v106 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).v106
      = (fusedValues c bs73 bs74).and78 ||| (fusedValues c bs73 bs74).and83 := rfl

theorem fb54_or84 (c : FusedCarry) (bs73 bs74 : List UInt8) :
    (fusedValues c bs73 bs74).or84
      = (fusedValues c bs73 bs74).v106 ||| (fusedValues c bs73 bs74).andI := rfl


/-- The specification's delimiter mask is the carry-free packing's. -/
theorem specDelimiter64_eq_specMask (lo hi : Block32) (st : ClassState) :
    specDelimiter64 lo hi st = specMask64 LeanLLVM.Refinement.JsonScanSpec.IsDelimB lo hi := by
  unfold specDelimiter64 classMask64 specMask64 pack32
  rw [delimiterMask_eq_maskOfListWith _ _ (by simp),
    delimiterMask_eq_maskOfListWith _ _ (by simp)]

/-- The specification's whitespace mask is the carry-free packing's. -/
theorem specSpace64_eq_specMask (lo hi : Block32) (st : ClassState) :
    specSpace64 lo hi st = specMask64 LeanLLVM.JSON.IsSpaceB lo hi := rfl

/-- The same, at the `<16 x i16>` shift's own shift amount: the body's
`x >>> (0x0004#16).toNat` is `x >>> 4`. -/
theorem byteView_highNibble' (B : List UInt8) (hB : B.length = 32) :
    (bitcastVecLanes 8 32
      ((bitcastVecLanes 16 16 (unpackLanes 64 4 (bytesToNat B))).map
        (fun x : BitVec 16 => x >>> (0x0004#16).toNat))).map (fun x => x &&& 0x0f#8)
      = hiNibbleLanes (bytesToNat B) := by
  rw [show (fun x : BitVec 16 => x >>> (0x0004#16).toNat)
      = (fun x : BitVec 16 => x >>> 4) from rfl]
  exact byteView_highNibble B hB

/-! ### The page's loaded words are the mask unit's block -/
/-! ### The page's loaded words are the mask unit's block -/

theorem fb54_joinBytes_eq_blockLanes (k : Ctx) (bs73 bs74 : List UInt8)
    (h73 : bs73 = List.ofFn k.lo) (h74 : bs74 = List.ofFn k.hi) :
    bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
      unpackLanes 64 4 (bytesToNat bs74)) = blockLanes k := by
  rw [h73, h74, bitcastVecLanes]
  exact packLanes_join k

/-- `%or.i.i`'s quote word: the joined byte view compared with `"`. -/
theorem fb54_or297_eq_qrawW {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
      unpackLanes 64 4 (bytesToNat bs74)) = blockLanes k) :
    (fusedValues c bs73 bs74).or297 = qrawW k := by
  rw [fb54_or297, hjb, qrawW, quoteLanes]
  congr 1

theorem fb54_mask81_eq (k : Ctx) (c : FusedCarry) (bs73 bs74 : List UInt8)
    (h73 : bs73 = List.ofFn k.lo) :
    (fusedValues c bs73 bs74).mask81 = BitVec.ofNat 32 (lanesToNat (backLo k)) := by
  have hb : bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs73)) = loLanes k := by
    rw [h73]
    exact bitcast_bytes_eq_loLanes k
  rw [fb54_mask81, hb, backLo,
    show (List.replicate 32 0x5c#8) = List.replicate 32 (BitVec.ofInt 8 92) from by
      decide]

theorem fb54_mask82_eq (k : Ctx) (c : FusedCarry) (bs73 bs74 : List UInt8)
    (h74 : bs74 = List.ofFn k.hi) :
    (fusedValues c bs73 bs74).mask82 = BitVec.ofNat 32 (lanesToNat (backHi k)) := by
  have hb2 : bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs74)) = hiLanes k := by
    rw [h74]
    exact bitcast_bytes_eq_hiLanes k
  rw [fb54_mask82, hb2, backHi,
    show (List.replicate 32 0x5c#8) = List.replicate 32 (BitVec.ofInt 8 92) from by
      decide]

/-- **`%or14.i` is the mask unit's backslash word.** -/
theorem fb54_or14_eq_bsW {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (h73 : bs73 = List.ofFn k.lo) (h74 : bs74 = List.ofFn k.hi) :
    (fusedValues c bs73 bs74).or14 = bsW k := by
  have h9 : (fusedValues c bs73 bs74).mask81
      = BitVec.ofNat 32 (lanesToNat (backLo k)) := fb54_mask81_eq k c bs73 bs74 h73
  have h10 : (fusedValues c bs73 bs74).mask82
      = BitVec.ofNat 32 (lanesToNat (backHi k)) := fb54_mask82_eq k c bs73 bs74 h74
  have h9c : (fusedValues c bs73 bs74).conv9 = conv9W k := by
    rw [fb54_conv9, h9, conv9W]
  have h12c : (fusedValues c bs73 bs74).conv12 = conv12W k := by
    rw [fb54_conv12, h10, conv12W]
  have h13 : (fusedValues c bs73 bs74).shl13 = shl13W k := by
    rw [fb54_shl13, h12c, shl13W, ofNat_toNat,
      show (0x0000000000000020#64 : BitVec 64).toNat
        = (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat from by decide]
  rw [fb54_or14, h13, h9c, bsW, bv_eq, or14W, ofNat_toNat, ofNat_toNat, ofNat_toNat]

/-! ### The escape chain -/

theorem fb54_escaped_eq {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (h14 : (fusedValues c bs73 bs74).or14 = bsW k)
    (h00 : (fusedValues c bs73 bs74).andII = escAnd00W k) :
    (fusedValues c bs73 bs74).or12II = escapedWord k := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hev : (0x5555555555555555#64 : BitVec 64) = evenC := by decide
  have hevn : (0xaaaaaaaaaaaaaaaa#64 : BitVec 64) = evenNotC := by decide
  have h4 : (fusedValues c bs73 bs74).not4II = escNotBsW k := by
    rw [fb54_not4II, h14, escNotBsW, bv_eq, hall]
  have hsh : (fusedValues c bs73 bs74).shlII = escShlW k := by
    rw [fb54_shlII, h14, escShlW, bv_eq,
      show (0x0000000000000001#64 : BitVec 64).toNat = 1 from by decide]
  have hN : (fusedValues c bs73 bs74).notII = escNotW k := by
    rw [fb54_notII, hsh, escNotW, bv_eq, hall]
  have h1 : (fusedValues c bs73 bs74).and1II = escStartsW k := by
    rw [fb54_and1II, h14, hN, escStartsW, bv_eq]
  have hX : (fusedValues c bs73 bs74).xorII = escEvenAltW k := by
    rw [fb54_xorII, h00, hev, escEvenAltW, bv_eq]
  have h2 : (fusedValues c bs73 bs74).and2II = escEvenClassW k := by
    rw [fb54_and2II, h1, hX, escEvenClassW, bv_eq, BitVec.and_comm]
  have h3 : (fusedValues c bs73 bs74).xor3II = escOddClassW k := by
    rw [fb54_xor3II, h2, h1, escOddClassW, bv_eq]
  have h6 : (fusedValues c bs73 bs74).and6II = escAnd6W k := by
    rw [fb54_and6II, h4, hevn, escAnd6W, bv_eq]
  have h8 : (fusedValues c bs73 bs74).and8II = escAnd8W k := by
    rw [fb54_and8II, h4, hev, escAnd8W, bv_eq]
  have hS : (fusedValues c bs73 bs74).addII = escSumEvenW k := by
    rw [fb54_addII, h2, h14, escSumEvenW, bv_eq]
  have hO : (fusedValues c bs73 bs74).add5II = escSumOddW k := by
    rw [fb54_add5II, h3, h14, escSumOddW, bv_eq]
  have h7 : (fusedValues c bs73 bs74).and7II = escAnd7W k := by
    rw [fb54_and7II, h6, hS, escAnd7W, bv_eq]
  have h9 : (fusedValues c bs73 bs74).and9II = escAnd9W k := by
    rw [fb54_and9II, h8, hO, escAnd9W, bv_eq]
  have h11b : (fusedValues c bs73 bs74).and11II = blkAnd11W k := by
    rw [fb54_and11II, h00, h4, blkAnd11W, bv_eq]
  have hor : (fusedValues c bs73 bs74).orII = blkOr62W k := by
    rw [fb54_orII, h7, h11b, blkOr62W, bv_eq]
  have hor12 : (fusedValues c bs73 bs74).or12II = blkEscapedW k := by
    rw [fb54_or12II, hor, h9, blkEscapedW, bv_eq]
  rw [hor12, blkEscapedW_eq_escapedWord]

/-- **`%and.i` is the classifier's unescaped quote.** -/
theorem fb54_andI_eq_specQuote {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
      unpackLanes 64 4 (bytesToNat bs74)) = blockLanes k)
    (h14 : (fusedValues c bs73 bs74).or14 = bsW k)
    (h00 : (fusedValues c bs73 bs74).andII = escAnd00W k)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (fusedValues c bs73 bs74).andI = specQuote64 k.lo k.hi k.st := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hq : (fusedValues c bs73 bs74).or297 = qrawW k := fb54_or297_eq_qrawW hjb
  have he : (fusedValues c bs73 bs74).or12II = escapedWord k := fb54_escaped_eq h14 h00
  have hn : (fusedValues c bs73 bs74).notI = notEscW k := by
    rw [fb54_notI, he, notEscW, bv_eq, hall]
  have hand : (fusedValues c bs73 bs74).andI = andQuoteW k := by
    rw [fb54_andI, hq, hn, andQuoteW, bv_eq]
  rw [hand, andQuoteW_spec k hst]

/-- `%andClass1` is the low half's class word. -/
theorem fb54_andClass1_eq_andWordLanes {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (h73 : bs73 = List.ofFn k.lo) :
    (fusedValues c bs73 bs74).andClass1 = andWordLanes k := by
  have hlow : (fusedValues c bs73 bs74).low85 = nibLanes (loLanes k) := by
    rw [fb54_low85, fb54_byte73, h73, byteView_lowNibble _ (by simp), byteLanes_ofFn]
    rfl
  have hhigh : (fusedValues c bs73 bs74).low88 = hiNibbleLanes (loWord k) := by
    rw [fb54_low88, fb54_byte87, fb54_shr84, fb54_half83, h73,
      byteView_highNibble' _ (by simp)]
    rfl
  rw [fb54_andClass1, fb54_shuf86, fb54_shuf89, hlow, hhigh,
    forBodyTableA_eq_loTabV, forBodyTableB_eq_hiTabV, andWordLanes, tabHiLanes,
    tabLoLanes]
  exact zipWith_eq_zip_map (fun x y : BitVec 8 => x &&& y)
    (pshufbLanes hiTabV (hiNibbleLanes (loWord k)))
    (pshufbLanes loTabV (nibLanes (loLanes k)))

/-- `%andClass2` is the high half's class word. -/
theorem fb54_andClass2_eq_andWordLanesHi {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (h74 : bs74 = List.ofFn k.hi) :
    (fusedValues c bs73 bs74).andClass2 = andWordLanesHi k := by
  have hlow : (fusedValues c bs73 bs74).low94 = nibLanes (hiLanes k) := by
    rw [fb54_low94, fb54_byte74, h74, byteView_lowNibble _ (by simp), byteLanes_ofFn]
    rfl
  have hhigh : (fusedValues c bs73 bs74).low97 = hiNibbleLanes (hiWord k) := by
    rw [fb54_low97, fb54_byte96, fb54_shr93, fb54_half92, h74,
      byteView_highNibble' _ (by simp)]
    rfl
  rw [fb54_andClass2, fb54_shuf95, fb54_shuf98, hlow, hhigh,
    forBodyTableA_eq_loTabV, forBodyTableB_eq_hiTabV, andWordLanesHi, tabHiLanesHi,
    tabLoLanesHi]
  exact zipWith_eq_zip_map (fun x y : BitVec 8 => x &&& y)
    (pshufbLanes hiTabV (hiNibbleLanes (hiWord k)))
    (pshufbLanes loTabV (nibLanes (hiLanes k)))

theorem xor_neg_one (x : BitVec 32) : x ^^^ BitVec.ofInt 32 (-1) = complW x := by
  rw [complW, ofNat32_toNat', ofNat_toNat]

theorem shift32_eq_shlUpW (x : BitVec 64) :
    x <<< (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat = shlUpW x := rfl

/-- **`%or19.i` is the classifier's delimiter word.** -/
theorem fb54_or19_eq_specDelimiter {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (h73 : bs73 = List.ofFn k.lo) (h74 : bs74 = List.ofFn k.hi) :
    (fusedValues c bs73 bs74).or19 = specDelimiter64 k.lo k.hi k.st := by
  have hac1 : (fusedValues c bs73 bs74).andClass1 = andWordLanes k :=
    fb54_andClass1_eq_andWordLanes h73
  have hac2 : (fusedValues c bs73 bs74).andClass2 = andWordLanesHi k :=
    fb54_andClass2_eq_andWordLanesHi h74
  have hc1 : (fusedValues c bs73 bs74).and90 = sWordLanes k := by
    rw [fb54_and90, hac1, sWordLanes, sLanes]
    rfl
  have hc2 : (fusedValues c bs73 bs74).and99 = sWordLanesHi k := by
    rw [fb54_and99, hac2, sWordLanesHi, sLanes]
    rfl
  have hcp1 : (fusedValues c bs73 bs74).cmp21 = cmpWordLanes k := by
    rw [fb54_cmp21, hc1, cmpWordLanes, eq0Lanes]
    rfl
  have hcp2 : (fusedValues c bs73 bs74).cmp48 = cmpWordLanesHi k := by
    rw [fb54_cmp48, hc2, cmpWordLanesHi, eq0Lanes]
    rfl
  have hm1 : (fusedValues c bs73 bs74).mask91
      = BitVec.ofNat 32 (lanesToNat (cmpWordLanes k)) := by
    rw [fb54_mask91, hcp1]
  have hm2 : (fusedValues c bs73 bs74).mask100
      = BitVec.ofNat 32 (lanesToNat (cmpWordLanesHi k)) := by
    rw [fb54_mask100, hcp2]
  have hc : (0xffffffff#32 : BitVec 32)
      = BitVec.ofNat 32 (BitVec.ofInt 32 (-1)).toNat := by decide
  have hn1 : (fusedValues c bs73 bs74).not46 = not46W k := by
    rw [fb54_not46, hm1, hc, not46W]
    rw [ofNat_toNat, ofNat_toNat]
    exact xor_neg_one _
  have hn2 : (fusedValues c bs73 bs74).not49 = not49W k := by
    rw [fb54_not49, hm2, hc, not49W]
    rw [ofNat_toNat, ofNat_toNat]
    exact xor_neg_one _
  have h16 : (fusedValues c bs73 bs74).conv16 = zext64W (not46W k) := by
    rw [fb54_conv16, hn1, zext64W]
  have h17 : (fusedValues c bs73 bs74).conv17 = zext64W (not49W k) := by
    rw [fb54_conv17, hn2, zext64W]
  have hor19 : (fusedValues c bs73 bs74).or19 = or5W k := by
    rw [fb54_or19, fb54_shl18, h16, h17, or5W_eq, joinW, ofNat_toNat, ofNat_toNat,
      show (0x0000000000000020#64 : BitVec 64).toNat
        = (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat from by decide,
      not46W_eq, not49W_eq, shift32_eq_shlUpW]
  rw [hor19, or5W_eq, specDelimiter64_eq_specMask]
  exact BitVec.eq_of_toNat_eq (s1_delimiter_eq k)

/-! ### The *neither* word

`%or23` is the lanes whose class byte is zero, and the class byte is zero exactly
at the bytes that are neither a delimiter nor whitespace.  The per-byte fact is
the tables' own (`tabAnd`), and the lane reading is `mask64`'s two halves. -/

/-- A `getD` inside the left summand of an append. -/
theorem getD_append_left {α : Type} (a b : List α) (d : α) {j : Nat}
    (h : j < a.length) : (a ++ b).getD j d = a.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

/-- A `getD` inside the right summand of an append. -/
theorem getD_append_right {α : Type} (a b : List α) (d : α) {j : Nat}
    (h : a.length ≤ j) : (a ++ b).getD j d = b.getD (j - a.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right h]

/-- The class byte is zero exactly away from the delimiters and whitespace. -/
theorem tabAnd_zero_iff_bv (x : BitVec 8) :
    (tabAnd x = 0) ↔ ¬ (LeanLLVM.Refinement.JsonScanSpec.IsDelimB (UInt8.ofNat x.toNat)
      = true ∨ LeanLLVM.JSON.IsSpaceB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

theorem tabAnd_zero_iff (b : UInt8) :
    (tabAnd b.toBitVec = 0) ↔
      ¬ (LeanLLVM.Refinement.JsonScanSpec.IsDelimB b = true ∨
        LeanLLVM.JSON.IsSpaceB b = true) := by
  have h := tabAnd_zero_iff_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl,
    show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- The class byte's zero test, as the emitted comparison and the `!` of the two
predicates: the two readings of one lane. -/
theorem decide_tabAnd_zero_bv (x : BitVec 8) :
    decide (tabAnd x = 0) = !(LeanLLVM.Refinement.JsonScanSpec.IsDelimB
      (UInt8.ofNat x.toNat) || LeanLLVM.JSON.IsSpaceB (UInt8.ofNat x.toNat)) := by
  revert x
  decide

theorem decide_tabAnd_zero (x : BitVec 8) (b : UInt8) (hx : x = b.toBitVec) :
    decide (tabAnd x = 0) = !(LeanLLVM.Refinement.JsonScanSpec.IsDelimB b ||
      LeanLLVM.JSON.IsSpaceB b) := by
  subst hx
  have h := decide_tabAnd_zero_bv b.toBitVec
  rwa [show b.toBitVec.toNat = b.toNat from rfl,
    show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h

/-- **`%or23` is the complement of the structural and whitespace words.** -/
theorem fb54_or23_eq_neither {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (hac1 : (fusedValues c bs73 bs74).andClass1 = andWordLanes k)
    (hac2 : (fusedValues c bs73 bs74).andClass2 = andWordLanesHi k) :
    (fusedValues c bs73 bs74).or23 =
      ~~~(specDelimiter64 k.lo k.hi k.st ||| specSpace64 k.lo k.hi k.st) := by
  rw [fb54_or23, fb54_cmp30, fb54_join64, hac1, hac2,
    specDelimiter64_eq_specMask, specSpace64_eq_specMask, specMask64, specMask64]
  have hlen : (andWordLanes k ++ andWordLanesHi k).length = 64 := by
    rw [List.length_append, andWordLanes_length, andWordLanesHi_length]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and,
    LeanLLVM.Refinement.BitLanes.getLsbD_not_of_lt _ hj, BitVec.getLsbD_or]
  by_cases hj32 : j < 32
  · rw [mask64_getLsbD_lo _ _ hj32, mask64_getLsbD_lo _ _ hj32,
      pack32_getLsbD LeanLLVM.Refinement.JsonScanSpec.IsDelimB k.lo ⟨j, hj32⟩,
      pack32_getLsbD LeanLLVM.JSON.IsSpaceB k.lo ⟨j, hj32⟩]
    have hlane : (andWordLanes k ++ andWordLanesHi k).getD j 0
        = tabAnd ((loLanes k).getD j 0) := by
      rw [getD_append_left (andWordLanes k) (andWordLanesHi k) (0 : BitVec 8)
          (j := j) (by rw [andWordLanes_length]; exact hj32),
        andWordLanes_getD k hj32, tabAnd, hiNibbleLanes_toNat_eq k hj32]
    have hbyte : ((loLanes k).getD j 0) = (k.lo ⟨j, hj32⟩).toBitVec := by
      rw [loLanes_getD_eq k hj32, loToBitVec]
    rw [lanesToNat_testBit_bool _ j
      (b := decide ((andWordLanes k ++ andWordLanesHi k).getD j 0 = 0x00#8))
      (zipReplicate_getElem? _ 0x00#8 (fun a b => evalICmp .eq a b) hlen hj),
      hlane]
    exact decide_tabAnd_zero _ _ hbyte
  · have hj32' : 32 ≤ j := by omega
    rw [show j = (j - 32) + 32 from by omega]
    rw [mask64_getLsbD_hi _ _ (by omega), mask64_getLsbD_hi _ _ (by omega),
      pack32_getLsbD LeanLLVM.Refinement.JsonScanSpec.IsDelimB k.hi ⟨j - 32, by omega⟩,
      pack32_getLsbD LeanLLVM.JSON.IsSpaceB k.hi ⟨j - 32, by omega⟩]
    have hlane : (andWordLanes k ++ andWordLanesHi k).getD (j - 32 + 32) 0
        = tabAnd ((hiLanes k).getD (j - 32) 0) := by
      rw [getD_append_right (andWordLanes k) (andWordLanesHi k) (0 : BitVec 8)
          (j := j - 32 + 32) (by rw [andWordLanes_length]; omega),
        show j - 32 + 32 - (andWordLanes k).length = j - 32 from by
          rw [andWordLanes_length]; omega,
        andWordLanesHi_getD k (by omega), tabAnd, hiNibbleLanes_toNat_eq_hi k (by omega)]
    have hbyte : ((hiLanes k).getD (j - 32) 0) = (k.hi ⟨j - 32, by omega⟩).toBitVec := by
      rw [hiLanes_getD_eq k (by omega), loToBitVec]
    rw [lanesToNat_testBit_bool _ (j - 32 + 32)
      (b := decide ((andWordLanes k ++ andWordLanesHi k).getD (j - 32 + 32) 0 = 0x00#8))
      (zipReplicate_getElem? _ 0x00#8 (fun a b => evalICmp .eq a b) hlen (by omega)),
      hlane]
    exact decide_tabAnd_zero _ _ hbyte

/-! ### The in-string word and the composition -/

/-- **`%xor.i` is the classifier's in-string word.** -/
theorem fb54_xorI_eq_specInString {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    (hq : (fusedValues c bs73 bs74).andI = andQuoteW k)
    (h15 : c.st15 = seedW k)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (fusedValues c bs73 bs74).xorI = specInString64 k.lo k.hi k.st := by
  have hve : (fusedValues c bs73 bs74).vecext = vecextW k := by
    rw [fb54_vecext, hq, vecextW, ofNat_toNat]
  have hx : (fusedValues c bs73 bs74).xorI = inStringWord k := by
    rw [fb54_xorI, hve, h15, inStringWord, bv_eq]
  rw [hx]
  exact BitVec.eq_of_toNat_eq (s1_instring_eq k hst)

/-- **The entry word of the page is `entryMask64`.** -/
theorem fb54_or84_eq_entryMask {k : Ctx} {c : FusedCarry} {bs73 bs74 : List UInt8}
    {p : Bool}
    (h73 : bs73 = List.ofFn k.lo) (h74 : bs74 = List.ofFn k.hi)
    (hst : k.st.oddRun = (k.opened && k.ppar))
    (h00 : (fusedValues c bs73 bs74).andII = escAnd00W k)
    (h15 : c.st15 = seedW k)
    (hprev : c.prevS = (if p then 1 else 0)) :
    (fusedValues c bs73 bs74).or84 = entryMask64 k.lo k.hi k.st p := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs73) ++
      unpackLanes 64 4 (bytesToNat bs74)) = blockLanes k :=
    fb54_joinBytes_eq_blockLanes k bs73 bs74 h73 h74
  have h14 : (fusedValues c bs73 bs74).or14 = bsW k := fb54_or14_eq_bsW h73 h74
  have hq : (fusedValues c bs73 bs74).andI = andQuoteW k := by
    rw [fb54_andI_eq_specQuote hjb h14 h00 hst, andQuoteW_spec k hst]
  have hac1 : (fusedValues c bs73 bs74).andClass1 = andWordLanes k :=
    fb54_andClass1_eq_andWordLanes h73
  have hac2 : (fusedValues c bs73 bs74).andClass2 = andWordLanesHi k :=
    fb54_andClass2_eq_andWordLanesHi h74
  have hd : (fusedValues c bs73 bs74).or19 = specDelimiter64 k.lo k.hi k.st :=
    fb54_or19_eq_specDelimiter h73 h74
  have hn : (fusedValues c bs73 bs74).or23 =
      ~~~(specDelimiter64 k.lo k.hi k.st ||| specSpace64 k.lo k.hi k.st) :=
    fb54_or23_eq_neither hac1 hac2
  have hx : (fusedValues c bs73 bs74).xorI = specInString64 k.lo k.hi k.st :=
    fb54_xorI_eq_specInString hq h15 hst
  have hnot : (fusedValues c bs73 bs74).not74 = ~~~(specInString64 k.lo k.hi k.st) := by
    rw [fb54_not74, hx, hall, xor_allOnes_eq_not]
  have hq64 : (fusedValues c bs73 bs74).andI = specQuote64 k.lo k.hi k.st := by
    rw [hq, andQuoteW_spec k hst]
  have hsc : (fusedValues c bs73 bs74).and75 = specScalar64 k.lo k.hi k.st := by
    rw [fb54_and75, fb54_v105, fb54_v104, hn, hq64, hx, hall, xor_allOnes_eq_not,
      show ~~~(specQuote64 k.lo k.hi k.st ||| specInString64 k.lo k.hi k.st)
        = ~~~specQuote64 k.lo k.hi k.st &&& ~~~specInString64 k.lo k.hi k.st
        from BitVec.not_or,
      ← BitVec.and_assoc]
    exact specScalar64_eq_neither k.lo k.hi k.st
  rw [fb54_or84, fb54_v106, fb54_and78, fb54_and83, fb54_not82, fb54_or81, fb54_shl80,
    hd, hnot, hsc, hprev, hq64, hall, xor_allOnes_eq_not,
    show (1#64 : BitVec 64).toNat = 1 from by decide,
    ← entry_eq_compose k.lo k.hi k.st p]
  ac_rfl

/-! ### The DFA arm's word

Both arms' half-computations are `JsonUtf8Steps`' expression at their own register
spellings: the two table lookups at the high and low nibbles of the loaded word,
the low table's at the carried control, the two saturating subtracts against
`0x60`/`0x70`, the high-bit mask and the xor.  `dfaHalf_eq_errRaw` is that
expression once, and the four arms instantiate it. -/

theorem map_and_replicate {w : Nat} (l : List (BitVec w)) (c : BitVec w) :
    l.map (fun x => x &&& c)
      = List.zipWith (fun x y => x &&& y) l (List.replicate l.length c) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.zipWith_cons_cons, List.length_cons,
        List.replicate_succ, ih]

theorem map_mask4 (l : List (BitVec 64)) (hl : l.length = 4) (c : BitVec 64) :
    l.map (fun x => x &&& c)
      = List.zipWith (fun x y => x &&& y) l (List.replicate 4 c) := by
  rw [map_and_replicate, hl]

theorem ifThen38TableHi_eq_t1V : ifThen38TableHi = t1V := by decide

theorem ifThen38TableMid_eq_t2V : ifThen38TableMid = t2V := by decide

theorem ifThen38TableLo_eq_t3V : ifThen38TableLo = t3V := by decide

theorem highLanes_eq : highLanes64 = List.replicate 4 0x8080808080808080#64 := by decide

/-- One DFA half's error word, at the fused arms' register spelling: the must
word's high-bit mask xor the structural word's three table lookups. -/
theorem dfaHalf_eq_errRaw {V1 Vc : Nat} {p2 p3 : List UInt8}
    (t1ctrl t2ctrl t3ctrl : List (BitVec 8))
    (h1 : t1ctrl = nibLanes (unpackLanes 8 32 V1))
    (h2 : t2ctrl = nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes V1))))
    (h3 : t3ctrl = nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes Vc)))) :
    List.zipWith (fun x y => x ^^^ y)
      ((bitcastVecLanes 64 4
        (List.zipWith (fun x y => x ||| y)
          (List.zipWith subsSat (byteLanes p3) (List.replicate 32 0x70#8))
          (List.zipWith subsSat (byteLanes p2) (List.replicate 32 0x60#8)))).map
        (fun x => x &&& 0x8080808080808080#64))
      (bitcastVecLanes 64 4
        (List.zipWith (fun x y => x &&& y)
          (List.zipWith (fun x y => x &&& y)
            (pshufbLanes ifThen38TableMid t2ctrl)
            (pshufbLanes ifThen38TableHi t1ctrl))
          (pshufbLanes ifThen38TableLo t3ctrl)))
    = errRaw (byteLanes p2) (byteLanes p3) V1 Vc := by
  rw [errRaw, mustHalf, scRaw,
    show (0x70#8 : BitVec 8) = BitVec.ofInt 8 0x70 from by decide,
    show (0x60#8 : BitVec 8) = BitVec.ofInt 8 0x60 from by decide,
    ifThen38TableHi_eq_t1V, ifThen38TableMid_eq_t2V, ifThen38TableLo_eq_t3V,
    h1, h2, h3, highLanes_eq,
    map_mask4 _ (by unfold bitcastVecLanes; simp [unpackLanes_length]) _]

/-- The low nibbles of a loaded word are the mask unit's `nibLanes`. -/
theorem lowNibbles_ctrl (B : List UInt8) (hB : B.length = 32) :
    (bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat B))).map (fun x => x &&& 0x0f#8)
      = nibLanes (unpackLanes 8 32 (bytesToNat B)) := by
  rw [byteView_lowNibble B hB, ← byteLanes_eq_unpackLanes hB]

/-- The high nibbles of a loaded word are the mask unit's shifted control. -/
theorem highNibbles_ctrl (B : List UInt8) (hB : B.length = 32) :
    (bitcastVecLanes 8 32 ((bitcastVecLanes 16 16
      (unpackLanes 64 4 (bytesToNat B))).map (fun x : BitVec 16 => x >>> 4))).map
        (fun x => x &&& 0x0f#8)
      = nibLanes (unpackLanes 8 32 (packLanes (shr4Lanes (bytesToNat B)))) := by
  rw [byteView_highNibble B hB, ← nibLanes_shr4]

/-- **The page's first DFA half is `errRaw`.** -/
theorem ifThen90_xor1_eq (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74 : List UInt8)
    (h41 : bs41.length = 32) (h73 : bs73.length = 32)
    (h88 : low88 = hiNibbleLanes (bytesToNat bs73)) :
    (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor1
      = errRaw (byteLanes bs42) (byteLanes bs43) (bytesToNat bs41) (bytesToNat bs73) := by
  rw [show (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor1
      = List.zipWith (fun x y => x ^^^ y)
          ((bitcastVecLanes 64 4
            (List.zipWith (fun x y => x ||| y)
              (List.zipWith subsSat (bs43.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x70#8))
              (List.zipWith subsSat (bs42.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x60#8)))).map
            (fun x => x &&& 0x8080808080808080#64))
          (bitcastVecLanes 64 4
            (List.zipWith (fun x y => x &&& y)
              (List.zipWith (fun x y => x &&& y)
                (pshufbLanes ifThen38TableMid
                  ((bitcastVecLanes 8 32 ((bitcastVecLanes 16 16
                    (unpackLanes 64 4 (bytesToNat bs41))).map
                      (fun x : BitVec 16 => x >>> 4))).map (fun x => x &&& 0x0f#8)))
                (pshufbLanes ifThen38TableHi
                  ((bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs41))).map
                    (fun x => x &&& 0x0f#8))))
              (pshufbLanes ifThen38TableLo low88))) from rfl]
  exact dfaHalf_eq_errRaw _ _ _
    (lowNibbles_ctrl bs41 h41) (highNibbles_ctrl bs41 h41)
    (by rw [h88, ← nibLanes_shr4])

/-- **The page's second DFA half is `errRaw`.** -/
theorem ifThen90_xor2_eq (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74 : List UInt8)
    (h57 : bs57.length = 32) (h74 : bs74.length = 32)
    (h97 : low97 = hiNibbleLanes (bytesToNat bs74)) :
    (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor2
      = errRaw (byteLanes bs58) (byteLanes bs59) (bytesToNat bs57) (bytesToNat bs74) := by
  rw [show (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor2
      = List.zipWith (fun x y => x ^^^ y)
          ((bitcastVecLanes 64 4
            (List.zipWith (fun x y => x ||| y)
              (List.zipWith subsSat (bs59.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x70#8))
              (List.zipWith subsSat (bs58.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x60#8)))).map
            (fun x => x &&& 0x8080808080808080#64))
          (bitcastVecLanes 64 4
            (List.zipWith (fun x y => x &&& y)
              (List.zipWith (fun x y => x &&& y)
                (pshufbLanes ifThen38TableMid
                  ((bitcastVecLanes 8 32 ((bitcastVecLanes 16 16
                    (unpackLanes 64 4 (bytesToNat bs57))).map
                      (fun x : BitVec 16 => x >>> 4))).map (fun x => x &&& 0x0f#8)))
                (pshufbLanes ifThen38TableHi
                  ((bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs57))).map
                    (fun x => x &&& 0x0f#8))))
              (pshufbLanes ifThen38TableLo low97))) from rfl]
  exact dfaHalf_eq_errRaw _ _ _
    (lowNibbles_ctrl bs57 h57) (highNibbles_ctrl bs57 h57)
    (by rw [h97, ← nibLanes_shr4])

/-- `zipWith`'s OR is commutative in the second and third arguments. -/
theorem zipWith_or_swap {a b c : List (BitVec 64)} (hb : b.length = c.length) :
    List.zipWith (· ||| ·) (List.zipWith (· ||| ·) a b) c
      = List.zipWith (· ||| ·) (List.zipWith (· ||| ·) a c) b := by
  induction a generalizing b c with
  | nil => cases b <;> cases c <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => cases c <;> rfl
      | cons y ys =>
          cases c with
          | nil => simp at hb
          | cons z zs =>
              simp only [List.zipWith_cons_cons, List.length_cons] at hb ⊢
              rw [show ((x ||| y) ||| z) = ((x ||| z) ||| y) from by
                rw [BitVec.or_assoc, BitVec.or_comm y z, ← BitVec.or_assoc],
                ih (by omega)]

/-- **The page's DFA arm accumulates `klErrBlk`'s word.** -/
theorem ifThen90_or281_def (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 : List UInt8) :
    (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or281
      = List.zipWith (fun x y => x ||| y)
          (List.zipWith (fun x y => x ||| y)
            (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor1
            (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).xor2)
          u8k := rfl

theorem ifThen90_or281_eq (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74 : List UInt8)
    (acc pre blk s : List UInt8)
    (h41 : bs41 = (s.drop 2).take 32) (h42 : bs42 = (s.drop 1).take 32)
    (h43 : bs43 = s.take 32)
    (h57 : bs57 = ((s.drop 32).drop 2).take 32)
    (h58 : bs58 = ((s.drop 32).drop 1).take 32) (h59 : bs59 = (s.drop 32).take 32)
    (h73 : bs73 = (s.drop 3).take 32) (h74 : bs74 = ((s.drop 32).drop 3).take 32)
    (h88 : low88 = hiNibbleLanes (bytesToNat bs73))
    (h97 : low97 = hiNibbleLanes (bytesToNat bs74))
    (hs : s = pre ++ blk) (h67 : 67 ≤ s.length)
    (hacc32 : acc.length = 32) (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hu8k : u8k.length = 4) (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or281
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk pre blk))) := by
  subst h41
  subst h42
  subst h43
  subst h57
  subst h58
  subst h59
  subst h73
  subst h74
  have l41 : ((s.drop 2).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l42 : ((s.drop 1).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l43 : (s.take 32).length = 32 := by
    rw [List.length_take, Nat.min_eq_left]; omega
  have l57 : (((s.drop 32).drop 2).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, Nat.min_eq_left]; omega
  have l58 : (((s.drop 32).drop 1).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, Nat.min_eq_left]; omega
  have l59 : ((s.drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l73 : ((s.drop 3).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l74 : (((s.drop 32).drop 3).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, Nat.min_eq_left]; omega
  rw [ifThen90_or281_def]
  rw [ifThen90_xor1_eq a low88 low97 u8k ((s.drop 2).take 32) ((s.drop 1).take 32)
        (s.take 32) (((s.drop 32).drop 2).take 32) (((s.drop 32).drop 1).take 32)
        ((s.drop 32).take 32) ((s.drop 3).take 32) (((s.drop 32).drop 3).take 32)
        l41 l73 h88,
      ifThen90_xor2_eq a low88 low97 u8k ((s.drop 2).take 32) ((s.drop 1).take 32)
        (s.take 32) (((s.drop 32).drop 2).take 32) (((s.drop 32).drop 1).take 32)
        ((s.drop 32).take 32) ((s.drop 3).take 32) (((s.drop 32).drop 3).take 32)
        l57 l74 h97]
  refine (zipWith_or_swap
      (a := errRaw (byteLanes ((s.drop 1).take 32)) (byteLanes (s.take 32))
        (bytesToNat ((s.drop 2).take 32)) (bytesToNat ((s.drop 3).take 32)))
      (b := errRaw (byteLanes (((s.drop 32).drop 1).take 32))
        (byteLanes ((s.drop 32).take 32)) (bytesToNat (((s.drop 32).drop 2).take 32))
        (bytesToNat (((s.drop 32).drop 3).take 32))) (c := u8k) ?_).trans ?_
  · rw [errRaw_length _ _ _ _ (by rw [byteLanes_length]; exact l58)
        (by rw [byteLanes_length]; exact l59), hu8k]
  · exact errRawBlk_word_eq s acc u8k pre blk hs h67 hacc32 hu8k hpre3 hblk64 hacc

/-- **The page's DFA step, at the accumulator's invariant.**  The carried word's
`klAcc` at block `i` becomes `klAcc` at `i + 1`: `klAcc_succ`'s own step. -/
theorem packLanes_or281_eq (bs : List UInt8) (a : Nat) (low88 low97 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74 : List UInt8)
    (s pre blk : List UInt8) (i : Nat)
    (h41 : bs41 = (s.drop 2).take 32) (h42 : bs42 = (s.drop 1).take 32)
    (h43 : bs43 = s.take 32)
    (h57 : bs57 = ((s.drop 32).drop 2).take 32)
    (h58 : bs58 = ((s.drop 32).drop 1).take 32) (h59 : bs59 = (s.drop 32).take 32)
    (h73 : bs73 = (s.drop 3).take 32) (h74 : bs74 = ((s.drop 32).drop 3).take 32)
    (h88 : low88 = hiNibbleLanes (bytesToNat bs73))
    (h97 : low97 = hiNibbleLanes (bytesToNat bs74))
    (hs : s = pre ++ blk) (h67 : 67 ≤ s.length)
    (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hpre : pre = klPre (0x00 :: 0x00 :: 0x00 :: bs) i)
    (hblk : blk = klBlk (0x00 :: 0x00 :: 0x00 :: bs) i)
    (hu8k : u8k.length = 4) (hacc : packLanes u8k = bytesToNat (klAcc bs i)) :
    packLanes (ifThen90Values a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59).or281
      = bytesToNat (klAcc bs (i + 1)) := by
  have hlen : (List.zipWith (· ||| ·) (klAcc bs i)
      (klErrBlk pre blk)).length = 32 := by
    rw [List.length_zipWith, klAcc_length, klErrBlk_length, Nat.min_self]
  rw [ifThen90_or281_eq a low88 low97 u8k bs41 bs42 bs43 bs57 bs58 bs59 bs73 bs74
      (klAcc bs i) pre blk s h41 h42 h43 h57 h58 h59 h73 h74 h88 h97 hs h67
      (klAcc_length bs i) hpre3 hblk64 hu8k hacc,
    packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt (by
      have h := bytesToNat_lt (List.zipWith (· ||| ·) (klAcc bs i) (klErrBlk pre blk))
      rw [hlen, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      exact h),
    hpre, hblk, klAcc_succ]

/-! ### The peeled tail's DFA word

`if.then144` is the same half-computation as `if.then90` at the peeled block's
windows: the words at `%add.ptr106 - 1` and `+ 31` and the three single-byte
windows around each, with the classifier's two carried low-nibble controls as the
third table's.  `ifThen144_xor448_eq` and `ifThen144_xor460_eq` are those halves,
and `%195`/`%or.i` are their join with the loop's accumulator. -/

theorem ifThen144_xor448_eq (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 : List UInt8)
    (h171 : bs171.length = 32) (h136 : bs136.length = 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136)) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor448
      = errRaw (byteLanes bs172) (byteLanes bs173) (bytesToNat bs171)
          (bytesToNat bs136) := by
  rw [show (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor448
      = List.zipWith (fun x y => x ^^^ y)
          ((bitcastVecLanes 64 4
            (List.zipWith (fun x y => x ||| y)
              (List.zipWith subsSat (bs173.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x70#8))
              (List.zipWith subsSat (bs172.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x60#8)))).map
            (fun x => x &&& 0x8080808080808080#64))
          (bitcastVecLanes 64 4
            (List.zipWith (fun x y => x &&& y)
              (List.zipWith (fun x y => x &&& y)
                (pshufbLanes ifThen38TableMid
                  ((bitcastVecLanes 8 32 ((bitcastVecLanes 16 16
                    (unpackLanes 64 4 (bytesToNat bs171))).map
                      (fun x : BitVec 16 => x >>> 4))).map (fun x => x &&& 0x0f#8)))
                (pshufbLanes ifThen38TableHi
                  ((bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs171))).map
                    (fun x => x &&& 0x0f#8))))
              (pshufbLanes ifThen38TableLo lo103))) from rfl]
  exact dfaHalf_eq_errRaw _ _ _
    (lowNibbles_ctrl bs171 h171) (highNibbles_ctrl bs171 h171)
    (by rw [h103, ← nibLanes_shr4])

theorem ifThen144_xor460_eq (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 : List UInt8)
    (h183 : bs183.length = 32) (h137 : bs137.length = 32)
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137)) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor460
      = errRaw (byteLanes bs184) (byteLanes bs185) (bytesToNat bs183)
          (bytesToNat bs137) := by
  rw [show (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor460
      = List.zipWith (fun x y => x ^^^ y)
          ((bitcastVecLanes 64 4
            (List.zipWith (fun x y => x ||| y)
              (List.zipWith subsSat (bs185.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x70#8))
              (List.zipWith subsSat (bs184.map fun b => BitVec.ofNat 8 b.toNat)
                (List.replicate 32 0x60#8)))).map
            (fun x => x &&& 0x8080808080808080#64))
          (bitcastVecLanes 64 4
            (List.zipWith (fun x y => x &&& y)
              (List.zipWith (fun x y => x &&& y)
                (pshufbLanes ifThen38TableMid
                  ((bitcastVecLanes 8 32 ((bitcastVecLanes 16 16
                    (unpackLanes 64 4 (bytesToNat bs183))).map
                      (fun x : BitVec 16 => x >>> 4))).map (fun x => x &&& 0x0f#8)))
                (pshufbLanes ifThen38TableHi
                  ((bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs183))).map
                    (fun x => x &&& 0x0f#8))))
              (pshufbLanes ifThen38TableLo lo161))) from rfl]
  exact dfaHalf_eq_errRaw _ _ _
    (lowNibbles_ctrl bs183 h183) (highNibbles_ctrl bs183 h183)
    (by rw [h161, ← nibLanes_shr4])

/-- `%195`'s two halves at the peel's registers. -/
theorem ifThen144_v195_def (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).v195
      = List.zipWith (fun x y => x ||| y)
          (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor448
          (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).xor460 := rfl

/-- `%or.i`'s accumulator join at the peel's registers. -/
theorem ifThen144_orI_def (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64)) (bs171 bs172 bs173 bs183 bs184 bs185 : List UInt8) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orI
      = List.zipWith (fun x y => x ||| y)
          (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).v195
          u8k := rfl

/-- **The peeled tail's accumulator step is `klErrBlk`'s word.** -/
theorem ifThen144_orI_eq (a : Nat) (lo103 lo161 : List (BitVec 8))
    (u8k : List (BitVec 64))
    (bs171 bs172 bs173 bs183 bs184 bs185 bs136 bs137 : List UInt8)
    (acc pre blk s : List UInt8)
    (h171 : bs171 = (s.drop 2).take 32) (h172 : bs172 = (s.drop 1).take 32)
    (h173 : bs173 = s.take 32)
    (h183 : bs183 = ((s.drop 32).drop 2).take 32)
    (h184 : bs184 = ((s.drop 32).drop 1).take 32) (h185 : bs185 = (s.drop 32).take 32)
    (h136 : bs136 = (s.drop 3).take 32) (h137 : bs137 = ((s.drop 32).drop 3).take 32)
    (h103 : lo103 = hiNibbleLanes (bytesToNat bs136))
    (h161 : lo161 = hiNibbleLanes (bytesToNat bs137))
    (hs : s = pre ++ blk) (h67 : 67 ≤ s.length)
    (hacc32 : acc.length = 32) (hpre3 : pre.length = 3) (hblk64 : blk.length = 64)
    (hu8k : u8k.length = 4) (hacc : packLanes u8k = bytesToNat acc) :
    (ifThen144Values a lo103 lo161 u8k bs171 bs172 bs173 bs183 bs184 bs185).orI
      = unpackLanes 64 4 (bytesToNat (List.zipWith (· ||| ·) acc
          (klErrBlk pre blk))) := by
  subst h171
  subst h172
  subst h173
  subst h183
  subst h184
  subst h185
  subst h136
  subst h137
  have l171 : ((s.drop 2).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l136 : ((s.drop 3).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left]; omega
  have l183 : (((s.drop 32).drop 2).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, Nat.min_eq_left]; omega
  have l137 : (((s.drop 32).drop 3).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, Nat.min_eq_left]; omega
  rw [ifThen144_orI_def, ifThen144_v195_def,
    ifThen144_xor448_eq a lo103 lo161 u8k ((s.drop 2).take 32) ((s.drop 1).take 32)
      (s.take 32) (((s.drop 32).drop 2).take 32) (((s.drop 32).drop 1).take 32)
      ((s.drop 32).take 32) ((s.drop 3).take 32) (((s.drop 32).drop 3).take 32)
      l171 l136 h103,
    ifThen144_xor460_eq a lo103 lo161 u8k ((s.drop 2).take 32) ((s.drop 1).take 32)
      (s.take 32) (((s.drop 32).drop 2).take 32) (((s.drop 32).drop 1).take 32)
      ((s.drop 32).take 32) ((s.drop 3).take 32) (((s.drop 32).drop 3).take 32)
      l183 l137 h161]
  refine (zipWith_or_swap
      (a := errRaw (byteLanes ((s.drop 1).take 32)) (byteLanes (s.take 32))
        (bytesToNat ((s.drop 2).take 32)) (bytesToNat ((s.drop 3).take 32)))
      (b := errRaw (byteLanes (((s.drop 32).drop 1).take 32))
        (byteLanes ((s.drop 32).take 32)) (bytesToNat (((s.drop 32).drop 2).take 32))
        (bytesToNat (((s.drop 32).drop 3).take 32))) (c := u8k) ?_).trans ?_
  · rw [errRaw_length _ _ _ _
        (by rw [byteLanes_length, List.length_take, List.length_drop,
          List.length_drop, Nat.min_eq_left]; omega)
        (by rw [byteLanes_length, List.length_take, List.length_drop,
          Nat.min_eq_left]; omega),
      hu8k]
  · exact errRawBlk_word_eq s acc u8k pre blk hs h67 hacc32 hu8k hpre3 hblk64 hacc

/-! ### The peeled accumulator and the staging

`klAcc` at the peeled index is one block short of the document's accumulator;
`klAll_eq_klAcc_succ` reads the stage's own accumulator as the fold's last step,
so the peel's word is the staging's `acc_pack`. -/

/-- **The stage's accumulator is the fold's last step.** -/
theorem klAll_eq_klAcc_succ (bs : List UInt8) (gate : Bool) {shr : Nat}
    (hsucc : shr + 1 = blocksOf bs.length) :
    klAll gate bs = List.zipWith (· ||| ·) (klAcc bs shr)
      (klErrBlk (klPre (0x00 :: 0x00 :: 0x00 :: bs) shr)
        (klBlk (0x00 :: 0x00 :: 0x00 :: bs) shr)) := by
  rw [← klAcc_eq_klAll, show (bs.length + 63) / 64 = shr + 1 from hsucc.symm,
    klAcc_succ]

/-- **The peeled arm's `acc_pack`.**  A word that packs to the stage's accumulator
is the staging's: `VerdictStaging.satisfies_post`'s `acc_pack` at the peel's exit. -/
theorem packLanes_unpackLanes_klAll (bs : List UInt8) (gate : Bool) :
    packLanes (unpackLanes 64 4 (bytesToNat (klAll gate bs)))
      = bytesToNat (klAll gate bs) := by
  have hlen : (klAll gate bs).length = 32 := klAll_length bs gate
  rw [packLanes_unpackLanes, show (4 * 64 : Nat) = 256 from by decide,
    Nat.mod_eq_of_lt (by
      have h := bytesToNat_lt (klAll gate bs)
      rw [hlen, show (256 : Nat) ^ 32 = 2 ^ 256 from by decide] at h
      exact h)]

/-- **The peel's `%u8k.3`, at the staging's field.**  The merge's word on the
peeled arm packs to `klAll`, so the staging's accumulator clause holds there. -/
theorem acc_pack_of_peel {bs : List UInt8} {gate : Bool} {shr : Nat}
    (hsucc : shr + 1 = blocksOf bs.length) (u8k3 : List (BitVec 64))
    (hword : u8k3 = unpackLanes 64 4 (bytesToNat (klAll gate bs))) :
    packLanes u8k3 = bytesToNat (klAll gate bs) := by
  rw [hword]
  exact packLanes_unpackLanes_klAll bs gate

/-! ### Axiom footprints

The entry identities are boolean algebra, lane arithmetic and the table
enumeration; the DFA identities are `JsonUtf8Steps`' own.  No statement carries
`sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.fb54_or84_eq_entryMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.fb54_or23_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.fb54_or19_eq_specDelimiter
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.ifThen90_or281_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.ifThen144_orI_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.packLanes_or281_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.klAll_eq_klAcc_succ
#print axioms LeanLLVM.Refinement.JsonS1BlocksWordIdentities.acc_pack_of_peel

end LeanLLVM.Refinement.JsonS1BlocksWordIdentities
