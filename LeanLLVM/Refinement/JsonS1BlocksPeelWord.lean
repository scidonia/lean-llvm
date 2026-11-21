/-
The peeled block's entry word, and its link to the document's entry words.

`JsonS1BlocksWordIdentities` states the page's store word, `%or84`, as
`entryMask64`, and leaves the peeled tail's `%or135` as the remaining link to
`PeelWordAtModel` and `stage1Word`.  This module states that identity.

The peel classifies the last whole block at `if.then103`'s registers: its two
window loads are the block's halves, its `%or.i385` is one sixty-four-lane quote
compare over their joined byte view, `%or14.i391` the backslash compare at the
same lanes, `%or19.i427` the class tables' delimiter word, `%or23.i431` the *neither*
word, `%vecext.i.i.i433` the carry-less product's in-string word, and `%or135` the
same `quote | (delim & ~in_string) | (S & ~((S <<< 1) | prevS))` chain the fused
page runs at `for.body54`.  The field accessors below are the block's own `let`
chain, so a line of the proof below matches the line of the block it names, and
`if103_or135_eq_entryMask` is the composition at `entryMask64`.

`if103_or135_eq_entryMask_docBlock` is the one-step instantiation the loop and
the peel use: the two loaded windows are the document's block halves
(`take32_blockLo`/`take32_blockHi` beneath `docBlock`), each thirty-two-byte
window read being the half the model names.  `if103_or135_peelWordAtModel` is
that statement in the record's vocabulary (`PeelWordAtModel`), and
`if103_and137_eq_stage1Word` applies the block's own clamp
(`ifThen103Values_and137_eq` with `limMask_tail_eq`) to reach the word the slot
stores, `stage1Word`.

What remains outside this module: the tie from the emitted run's six offset
windows (`%171`…`%173` at one, two and three bytes below the peel's aligned
address, and `%183`…`%185` at twenty-nine, thirty and thirty-one above it) to
the document.  The entry word reads only the block's two halves, so its identity
is complete at the halves; the DFA arm's six windows are the run's read
obligations, not the word's.
-/
import LeanLLVM.Refinement.JsonS1BlocksWordIdentities
import LeanLLVM.Refinement.JsonS1BlocksCompose
import LeanLLVM.Refinement.JsonS1BlocksLoopFacts

namespace LeanLLVM.Refinement.JsonS1BlocksPeelWord

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BitLanes
open LeanLLVM.Refinement.Pclmul (clmul)
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.BlockEvalVector
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonS1MasksSteps
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonS1BlocksLoopFacts
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksWordIdentities

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### `docBlock`'s halves, at the entry model's windows

`docBlock bs i` is sixty-four bytes; the two window loads the peel makes are its
two thirty-two-byte halves.  These two rewrites move between the block's
spelling and the halves', so `take32_blockLo`/`take32_blockHi` apply. -/

theorem docBlock_take32 (bs : List UInt8) (i : Nat) :
    (docBlock bs i).take 32 = ((padded bs).drop (64 * i)).take 32 := by
  unfold docBlock
  rw [List.take_take, show min 32 64 = 32 from by decide]

theorem docBlock_drop32 (bs : List UInt8) (i : Nat) :
    (docBlock bs i).drop 32 = ((padded bs).drop (64 * i + 32)).take 32 := by
  unfold docBlock
  rw [List.drop_take, List.drop_drop]

/-! ### One sixty-four-lane compare is a packed mask

`%or.i385` and `%or14.i391` are single sixty-four-lane comparisons over the
joined byte view, then one `bitcastMask`; the mask unit's words are two packed
thirty-two-lane halves joined.  `cmp64Lanes_eq_specMask` is that packing bridge —
once, for a predicate that decides one byte comparison — so both compares read
their halves' `pack32` words.  The per-byte test is the body's `icmp eq` lane. -/

/-- The backslash comparison at a byte, over `BitVec 8`. -/
theorem isBackslashB_iff_bv (x : BitVec 8) :
    (BitVec.ofNat 8 x.toNat = BitVec.ofInt 8 92) ↔
      (IsBackslashB (UInt8.ofNat x.toNat) = true) := by
  revert x
  decide

/-- The backslash comparison at a byte: `ofNat 8 b.toNat` against `ofInt 8 92` is
`IsBackslashB b`. -/
theorem isBackslashB_iff (b : UInt8) :
    (BitVec.ofNat 8 b.toNat = BitVec.ofInt 8 92) ↔ (IsBackslashB b = true) := by
  have h := isBackslashB_iff_bv b.toBitVec
  rw [show b.toBitVec.toNat = b.toNat from rfl,
    show UInt8.ofNat b.toNat = b from UInt8.ofNat_toNat] at h
  exact h

/-- **A sixty-four-lane compare is the specification's packed mask.**  Lane `j`
of the compare's bitcast is the predicate's decision on the block's byte `j`,
read through `pack32` on whichever half holds it. -/
theorem cmp64Lanes_eq_specMask (k : Ctx) (c : BitVec 8) (f : UInt8 → Bool)
    (hf : ∀ b : UInt8, (BitVec.ofNat 8 b.toNat = c) ↔ (f b = true)) :
    BitVec.ofNat 64 (lanesToNat
        (icmpLanes .eq (blockLanes k) (List.replicate 64 c)))
      = specMask64 f k.lo k.hi := by
  rw [specMask64]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_ofNat, decide_eq_true hj, Bool.true_and]
  have hq : (icmpLanes .eq (blockLanes k) (List.replicate 64 c))[j]? =
      some (evalICmp .eq ((blockLanes k).getD j 0) c) :=
    zipReplicate_getElem? (blockLanes k) c (fun x y => evalICmp .eq x y)
      (blockLanes_length k) hj
  by_cases hj32 : j < 32
  · have hgd : (blockLanes k).getD j 0 = (loLanes k).getD j 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_left (by omega : j < 32)]
    rw [mask64_getLsbD_lo _ _ hj32, pack32_getLsbD f k.lo ⟨j, hj32⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, hq, Option.some.injEq]
    simp only [evalICmp]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.ofBool_eq_one
      (p := ((blockLanes k).getD j 0 = c)), hgd]
    simp only [loLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dite_eq_left (by omega : j < 32)]
    exact hf _
  · have hgd : (blockLanes k).getD j 0 = (hiLanes k).getD (j - 32) 0 := by
      simp only [blockLanes, List.getD, List.getElem?_append, loLanes_length]
      rw [ite_eq_right (by omega : ¬ j < 32)]
    rw [show j = (j - 32) + 32 from by omega, mask64_getLsbD_hi _ _ (by omega),
      pack32_getLsbD f k.hi ⟨j - 32, by omega⟩]
    apply Bool.eq_iff_iff.mpr
    rw [lanesToNat_testBit, show (j - 32) + 32 = j from by omega, hq,
      Option.some.injEq]
    simp only [evalICmp]
    rw [LeanLLVM.Refinement.JsonS1MasksIR.ofBool_eq_one
      (p := ((blockLanes k).getD j 0 = c)), hgd]
    simp only [hiLanes, List.getD, List.getElem?_ofFn, Option.getD_some,
      dite_eq_left (by omega : j - 32 < 32)]
    exact hf _

/-! ### The peel's values, at the block's own names

Each accessor is the `if.then103` binding it names, at the two loaded halves and
the carried state; the proofs are `rfl`, because the values are that block's own
`let` chain.  They keep the identities below at the register spellings the
emission uses, so a reader can match a line of the proof to a line of the body. -/
section

variable {n : BitVec 64} {b : Nat} {bs136 bs137 : List UInt8}
  {ascii : List (BitVec 64)} {st0 st9 st15 prevS andv shr : BitVec 64}
  {ent : Nat} {conv prevAscii : BitVec 32}

local notation "V" =>
  (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
    prevAscii)

theorem if103_byte139 :
    (V).byte139 = bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs136)) := rfl

theorem if103_byte140 :
    (V).byte140 = bitcastVecLanes 8 32 (unpackLanes 64 4 (bytesToNat bs137)) := rfl

theorem if103_join141 :
    (V).join141 = unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137) := rfl

theorem if103_join142 :
    (V).join142 = bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) := rfl

theorem if103_cmp143 :
    (V).cmp143 = icmpLanes .eq
      (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
        unpackLanes 64 4 (bytesToNat bs137))) (List.replicate 64 0x22#8) := rfl

theorem if103_mask385 :
    (V).mask385 = BitVec.ofNat 64 (lanesToNat (icmpLanes .eq
      (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
        unpackLanes 64 4 (bytesToNat bs137))) (List.replicate 64 0x22#8))) := rfl

theorem if103_join144 :
    (V).join144 = unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137) := rfl

theorem if103_join145 :
    (V).join145 = bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) := rfl

theorem if103_cmp146 :
    (V).cmp146 = icmpLanes .eq
      (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
        unpackLanes 64 4 (bytesToNat bs137))) (List.replicate 64 0x5c#8) := rfl

theorem if103_mask391 :
    (V).mask391 = BitVec.ofNat 64 (lanesToNat (icmpLanes .eq
      (bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
        unpackLanes 64 4 (bytesToNat bs137))) (List.replicate 64 0x5c#8))) := rfl

theorem if103_andII : (V).andII = st0 &&& st9 := rfl

theorem if103_shlII :
    (V).shlII = (V).mask391 <<< (0x0000000000000001#64).toNat := rfl

theorem if103_notII :
    (V).notII = (V).shlII ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_and1II :
    (V).and1II = (V).mask391 &&& (V).notII := rfl

theorem if103_xorII :
    (V).xorII = (V).andII ^^^ 0x5555555555555555#64 := rfl

theorem if103_and2II :
    (V).and2II = (V).and1II &&& (V).xorII := rfl

theorem if103_xor3II :
    (V).xor3II = (V).and2II ^^^ (V).and1II := rfl

theorem if103_not4II :
    (V).not4II = (V).mask391 ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_addII :
    (V).addII = (V).and2II + (V).mask391 := rfl

theorem if103_add5II :
    (V).add5II = (V).xor3II + (V).mask391 := rfl

theorem if103_and6II :
    (V).and6II = (V).not4II &&& 0xaaaaaaaaaaaaaaaa#64 := rfl

theorem if103_and7II :
    (V).and7II = (V).and6II &&& (V).addII := rfl

theorem if103_and8II :
    (V).and8II = (V).not4II &&& 0x5555555555555555#64 := rfl

theorem if103_and9II :
    (V).and9II = (V).and8II &&& (V).add5II := rfl

theorem if103_and11II :
    (V).and11II = (V).andII &&& (V).not4II := rfl

theorem if103_orII :
    (V).orII = (V).and7II ||| (V).and11II := rfl

theorem if103_or12II :
    (V).or12II = (V).orII ||| (V).and9II := rfl

theorem if103_notI :
    (V).notI = (V).or12II ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_andI :
    (V).andI = (V).mask385 &&& (V).notI := rfl

theorem if103_half147 :
    (V).half147 = bitcastVecLanes 16 16
      (unpackLanes 64 4 (bytesToNat bs136)) := rfl

theorem if103_shr148 :
    (V).shr148 = (V).half147.map
      (fun x : BitVec 16 => x >>> (0x0004#16).toNat) := rfl

theorem if103_low149 :
    (V).low149 = (V).byte139.map (fun x => x &&& 0x0f#8) := rfl

theorem if103_shuf150 :
    (V).shuf150 = pshufbLanes forBodyTableA (V).low149 := rfl

theorem if103_byte151 :
    (V).byte151 = bitcastVecLanes 8 32 (V).shr148 := rfl

theorem if103_low152 :
    (V).low152 = (V).byte151.map (fun x => x &&& 0x0f#8) := rfl

theorem if103_shuf153 :
    (V).shuf153 = pshufbLanes forBodyTableB (V).low152 := rfl

theorem if103_and416 :
    (V).and416 = List.zipWith (fun x y => x &&& y) (V).shuf153 (V).shuf150 := rfl

theorem if103_and154 :
    (V).and154 = (V).and416.map (fun x => x &&& 0x3f#8) := rfl

theorem if103_cmp417 :
    (V).cmp417 = icmpLanes .eq (V).and154 (List.replicate 32 0x00#8) := rfl

theorem if103_mask155 :
    (V).mask155 = BitVec.ofNat 32 (lanesToNat (V).cmp417) := rfl

theorem if103_not418 :
    (V).not418 = (V).mask155 ^^^ 0xffffffff#32 := rfl

theorem if103_half156 :
    (V).half156 = bitcastVecLanes 16 16
      (unpackLanes 64 4 (bytesToNat bs137)) := rfl

theorem if103_shr157 :
    (V).shr157 = (V).half156.map
      (fun x : BitVec 16 => x >>> (0x0004#16).toNat) := rfl

theorem if103_low158 :
    (V).low158 = (V).byte140.map (fun x => x &&& 0x0f#8) := rfl

theorem if103_shuf159 :
    (V).shuf159 = pshufbLanes forBodyTableA (V).low158 := rfl

theorem if103_byte160 :
    (V).byte160 = bitcastVecLanes 8 32 (V).shr157 := rfl

theorem if103_low161 :
    (V).low161 = (V).byte160.map (fun x => x &&& 0x0f#8) := rfl

theorem if103_shuf162 :
    (V).shuf162 = pshufbLanes forBodyTableB (V).low161 := rfl

theorem if103_and420 :
    (V).and420 = List.zipWith (fun x y => x &&& y) (V).shuf162 (V).shuf159 := rfl

theorem if103_and163 :
    (V).and163 = (V).and420.map (fun x => x &&& 0x3f#8) := rfl

theorem if103_cmp421 :
    (V).cmp421 = icmpLanes .eq (V).and163 (List.replicate 32 0x00#8) := rfl

theorem if103_mask164 :
    (V).mask164 = BitVec.ofNat 32 (lanesToNat (V).cmp421) := rfl

theorem if103_not422 :
    (V).not422 = (V).mask164 ^^^ 0xffffffff#32 := rfl

theorem if103_conv16 :
    (V).conv16 = BitVec.ofNat 64 (V).not418.toNat := rfl

theorem if103_conv17 :
    (V).conv17 = BitVec.ofNat 64 (V).not422.toNat := rfl

theorem if103_shl18 :
    (V).shl18 = (V).conv17 <<< (0x0000000000000020#64).toNat := rfl

theorem if103_or19 :
    (V).or19 = (V).shl18 ||| (V).conv16 := rfl

theorem if103_join165 :
    (V).join165 = (V).and416 ++ (V).and420 := rfl

theorem if103_cmp166 :
    (V).cmp166 = icmpLanes .eq (V).join165 (List.replicate 64 0x00#8) := rfl

theorem if103_mask431 :
    (V).mask431 = BitVec.ofNat 64 (lanesToNat (V).cmp166) := rfl

theorem if103_vecext :
    (V).vecext = clmul (BitVec.ofNat 64 (V).andI.toNat) (BitVec.allOnes 64) := rfl

theorem if103_xorI :
    (V).xorI = (V).vecext ^^^ st15 := rfl

theorem if103_not125 :
    (V).not125 = (V).xorI ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_v168 :
    (V).v168 = (V).andI ||| (V).xorI := rfl

theorem if103_v169 :
    (V).v169 = (V).v168 ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_and126 :
    (V).and126 = (V).mask431 &&& (V).v169 := rfl

theorem if103_and129 :
    (V).and129 = (V).or19 &&& (V).not125 := rfl

theorem if103_shl131 :
    (V).shl131 = (V).and126 <<< (0x0000000000000001#64).toNat := rfl

theorem if103_or132 :
    (V).or132 = (V).shl131 ||| prevS := rfl

theorem if103_not133 :
    (V).not133 = (V).or132 ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_and134 :
    (V).and134 = (V).and126 &&& (V).not133 := rfl

theorem if103_v170 :
    (V).v170 = (V).and129 ||| (V).and134 := rfl

theorem if103_or135 :
    (V).or135 = (V).v170 ||| (V).andI := rfl

theorem if103_notmask :
    (V).notmask = 0xffffffffffffffff#64 <<< andv.toNat := rfl

theorem if103_sub :
    (V).sub = (V).notmask ^^^ 0xffffffffffffffff#64 := rfl

theorem if103_and137 :
    (V).and137 = (V).or135 &&& (V).sub := rfl

/-! ### The joined byte view is the block -/

theorem if103_join142_eq_blockLanes (k : Ctx)
    (h136 : bs136 = List.ofFn k.lo) (h137 : bs137 = List.ofFn k.hi) :
    bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) = blockLanes k := by
  rw [h136, h137, bitcastVecLanes]
  exact packLanes_join k

/-- **`%or.i385` is the mask unit's raw quote word.** -/
theorem if103_mask385_eq_qrawW {k : Ctx}
    (hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) = blockLanes k) :
    (V).mask385 = qrawW k := by
  rw [if103_mask385, hjb,
    show (List.replicate 64 0x22#8) = List.replicate 64 (BitVec.ofInt 8 34) from by
      decide,
    cmp64Lanes_eq_specMask k (BitVec.ofInt 8 34) IsQuoteB isQuoteB_iff,
    ← qrawW_eq]

/-- **`%or14.i391` is the mask unit's backslash word.** -/
theorem if103_mask391_eq_bsW {k : Ctx}
    (hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) = blockLanes k) :
    (V).mask391 = bsW k := by
  rw [if103_mask391, hjb,
    show (List.replicate 64 0x5c#8) = List.replicate 64 (BitVec.ofInt 8 92) from by
      decide,
    cmp64Lanes_eq_specMask k (BitVec.ofInt 8 92) IsBackslashB isBackslashB_iff,
    ← bsW_eq_spec]

/-! ### The class tables' words -/

/-- `%and.i416` is the low half's class word. -/
theorem if103_and416_eq_andWordLanes {k : Ctx}
    (h136 : bs136 = List.ofFn k.lo) :
    (V).and416 = andWordLanes k := by
  have hlow : (V).low149 = nibLanes (loLanes k) := by
    rw [if103_low149, if103_byte139, h136, byteView_lowNibble _ (by simp),
      byteLanes_ofFn]
    rfl
  have hhigh : (V).low152 = hiNibbleLanes (loWord k) := by
    rw [if103_low152, if103_byte151, if103_shr148, if103_half147, h136,
      byteView_highNibble' _ (by simp)]
    rfl
  rw [if103_and416, if103_shuf150, if103_shuf153, hlow, hhigh,
    forBodyTableA_eq_loTabV, forBodyTableB_eq_hiTabV, andWordLanes, tabHiLanes,
    tabLoLanes]
  exact zipWith_eq_zip_map (fun x y : BitVec 8 => x &&& y)
    (pshufbLanes hiTabV (hiNibbleLanes (loWord k)))
    (pshufbLanes loTabV (nibLanes (loLanes k)))

/-- `%and.i420` is the high half's class word. -/
theorem if103_and420_eq_andWordLanesHi {k : Ctx}
    (h137 : bs137 = List.ofFn k.hi) :
    (V).and420 = andWordLanesHi k := by
  have hlow : (V).low158 = nibLanes (hiLanes k) := by
    rw [if103_low158, if103_byte140, h137, byteView_lowNibble _ (by simp),
      byteLanes_ofFn]
    rfl
  have hhigh : (V).low161 = hiNibbleLanes (hiWord k) := by
    rw [if103_low161, if103_byte160, if103_shr157, if103_half156, h137,
      byteView_highNibble' _ (by simp)]
    rfl
  rw [if103_and420, if103_shuf159, if103_shuf162, hlow, hhigh,
    forBodyTableA_eq_loTabV, forBodyTableB_eq_hiTabV, andWordLanesHi, tabHiLanesHi,
    tabLoLanesHi]
  exact zipWith_eq_zip_map (fun x y : BitVec 8 => x &&& y)
    (pshufbLanes hiTabV (hiNibbleLanes (hiWord k)))
    (pshufbLanes loTabV (nibLanes (hiLanes k)))

theorem xor_neg_one_peel (x : BitVec 32) :
    x ^^^ BitVec.ofInt 32 (-1) = complW x := by
  rw [complW, ofNat32_toNat', ofNat_toNat]

/-- **`%or19.i427` is the classifier's delimiter word.** -/
theorem if103_or19_eq_specDelimiter {k : Ctx}
    (h136 : bs136 = List.ofFn k.lo) (h137 : bs137 = List.ofFn k.hi) :
    (V).or19 = specDelimiter64 k.lo k.hi k.st := by
  have hac1 : (V).and416 = andWordLanes k :=
    if103_and416_eq_andWordLanes (k := k) h136
  have hac2 : (V).and420 = andWordLanesHi k :=
    if103_and420_eq_andWordLanesHi (k := k) h137
  have hc1 : (V).and154 = sWordLanes k := by
    rw [if103_and154, hac1, sWordLanes, sLanes]
    rfl
  have hc2 : (V).and163 = sWordLanesHi k := by
    rw [if103_and163, hac2, sWordLanesHi, sLanes]
    rfl
  have hcp1 : (V).cmp417 = cmpWordLanes k := by
    rw [if103_cmp417, hc1, cmpWordLanes, eq0Lanes]
    rfl
  have hcp2 : (V).cmp421 = cmpWordLanesHi k := by
    rw [if103_cmp421, hc2, cmpWordLanesHi, eq0Lanes]
    rfl
  have hm1 : (V).mask155 = BitVec.ofNat 32 (lanesToNat (cmpWordLanes k)) := by
    rw [if103_mask155, hcp1]
  have hm2 : (V).mask164 = BitVec.ofNat 32 (lanesToNat (cmpWordLanesHi k)) := by
    rw [if103_mask164, hcp2]
  have hc : (0xffffffff#32 : BitVec 32)
      = BitVec.ofNat 32 (BitVec.ofInt 32 (-1)).toNat := by decide
  have hn1 : (V).not418 = not46W k := by
    rw [if103_not418, hm1, hc, not46W]
    rw [ofNat_toNat, ofNat_toNat]
    exact xor_neg_one_peel _
  have hn2 : (V).not422 = not49W k := by
    rw [if103_not422, hm2, hc, not49W]
    rw [ofNat_toNat, ofNat_toNat]
    exact xor_neg_one_peel _
  have h16 : (V).conv16 = zext64W (not46W k) := by
    rw [if103_conv16, hn1, zext64W]
  have h17 : (V).conv17 = zext64W (not49W k) := by
    rw [if103_conv17, hn2, zext64W]
  have hor19 : (V).or19 = or5W k := by
    rw [if103_or19, if103_shl18, h16, h17, or5W_eq, joinW, ofNat_toNat, ofNat_toNat,
      show (0x0000000000000020#64 : BitVec 64).toNat
        = (BitVec.ofNat 64 (BitVec.ofInt 64 32).toNat).toNat from by decide,
      not46W_eq, not49W_eq, shift32_eq_shlUpW]
  rw [hor19, or5W_eq, specDelimiter64_eq_specMask]
  exact BitVec.eq_of_toNat_eq (s1_delimiter_eq k)

/-! ### The *neither* word

`%or23.i431` is the lanes whose class byte is zero, and the class byte is zero
exactly at the bytes that are neither a delimiter nor whitespace.  The per-byte
fact is the tables' own (`tabAnd`) and the lane reading is `mask64`'s two
halves, as at the fused page's `%or23`. -/

/-- **`%or23.i431` is the complement of the structural and whitespace words.** -/
theorem if103_mask431_eq_neither {k : Ctx}
    (hac1 : (V).and416 = andWordLanes k)
    (hac2 : (V).and420 = andWordLanesHi k) :
    (V).mask431 =
      ~~~(specDelimiter64 k.lo k.hi k.st ||| specSpace64 k.lo k.hi k.st) := by
  rw [if103_mask431, if103_cmp166, if103_join165, hac1, hac2,
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

/-! ### The escape chain and the unescaped quote -/

/-- The escape word at `if.then103`'s registers is `s1f_escaped`'s.  The two
inputs are the block's carried conjunction (`%and.i393`) and its backslash word
(`%or14.i391`); the chain below is the fused body's own, at the peel's names. -/
theorem if103_escaped_eq {k : Ctx}
    (h14 : (V).mask391 = bsW k)
    (h00 : (V).andII = escAnd00W k) :
    (V).or12II = escapedWord k := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hev : (0x5555555555555555#64 : BitVec 64) = evenC := by decide
  have hevn : (0xaaaaaaaaaaaaaaaa#64 : BitVec 64) = evenNotC := by decide
  have h4 : (V).not4II = escNotBsW k := by
    rw [if103_not4II, h14, escNotBsW, bv_eq, hall]
  have hsh : (V).shlII = escShlW k := by
    rw [if103_shlII, h14, escShlW, bv_eq,
      show (0x0000000000000001#64 : BitVec 64).toNat = 1 from by decide]
  have hN : (V).notII = escNotW k := by
    rw [if103_notII, hsh, escNotW, bv_eq, hall]
  have h1 : (V).and1II = escStartsW k := by
    rw [if103_and1II, h14, hN, escStartsW, bv_eq]
  have hX : (V).xorII = escEvenAltW k := by
    rw [if103_xorII, h00, hev, escEvenAltW, bv_eq]
  have h2 : (V).and2II = escEvenClassW k := by
    rw [if103_and2II, h1, hX, escEvenClassW, bv_eq, BitVec.and_comm]
  have h3 : (V).xor3II = escOddClassW k := by
    rw [if103_xor3II, h2, h1, escOddClassW, bv_eq]
  have h6 : (V).and6II = escAnd6W k := by
    rw [if103_and6II, h4, hevn, escAnd6W, bv_eq]
  have h8 : (V).and8II = escAnd8W k := by
    rw [if103_and8II, h4, hev, escAnd8W, bv_eq]
  have hS : (V).addII = escSumEvenW k := by
    rw [if103_addII, h2, h14, escSumEvenW, bv_eq]
  have hO : (V).add5II = escSumOddW k := by
    rw [if103_add5II, h3, h14, escSumOddW, bv_eq]
  have h7 : (V).and7II = escAnd7W k := by
    rw [if103_and7II, h6, hS, escAnd7W, bv_eq]
  have h9 : (V).and9II = escAnd9W k := by
    rw [if103_and9II, h8, hO, escAnd9W, bv_eq]
  have h11b : (V).and11II = blkAnd11W k := by
    rw [if103_and11II, h00, h4, blkAnd11W, bv_eq]
  have hor : (V).orII = blkOr62W k := by
    rw [if103_orII, h7, h11b, blkOr62W, bv_eq]
  have hor12 : (V).or12II = blkEscapedW k := by
    rw [if103_or12II, hor, h9, blkEscapedW, bv_eq]
  rw [hor12, blkEscapedW_eq_escapedWord]

/-- **`%and.i415` is the classifier's unescaped quote.** -/
theorem if103_andI_eq_specQuote {k : Ctx}
    (hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) = blockLanes k)
    (h14 : (V).mask391 = bsW k)
    (h00 : (V).andII = escAnd00W k)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (V).andI = specQuote64 k.lo k.hi k.st := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hq : (V).mask385 = qrawW k := if103_mask385_eq_qrawW hjb
  have he : (V).or12II = escapedWord k := if103_escaped_eq h14 h00
  have hn : (V).notI = notEscW k := by
    rw [if103_notI, he, notEscW, bv_eq, hall]
  have hand : (V).andI = andQuoteW k := by
    rw [if103_andI, hq, hn, andQuoteW, bv_eq]
  rw [hand, andQuoteW_spec k hst]

/-- **`%xor.i435` is the classifier's in-string word.** -/
theorem if103_xorI_eq_specInString {k : Ctx}
    (hq : (V).andI = andQuoteW k)
    (h15 : st15 = seedW k)
    (hst : k.st.oddRun = (k.opened && k.ppar)) :
    (V).xorI = specInString64 k.lo k.hi k.st := by
  have hve : (V).vecext = vecextW k := by
    rw [if103_vecext, hq, vecextW, ofNat_toNat]
  have hx : (V).xorI = inStringWord k := by
    rw [if103_xorI, hve, h15, inStringWord, bv_eq]
  rw [hx]
  exact BitVec.eq_of_toNat_eq (s1_instring_eq k hst)

/-! ### The entry word

`%or135` is `quote | (delim & ~in_string) | (S & ~((S <<< 1) | prevS))`, which is
`entryMask64`'s composition.  Its three terms are the identities above, and
`entry_eq_compose` is the composition itself. -/

/-- **The peel's entry word is `entryMask64`.** -/
theorem if103_or135_eq_entryMask {k : Ctx} {p : Bool}
    (h136 : bs136 = List.ofFn k.lo) (h137 : bs137 = List.ofFn k.hi)
    (hst : k.st.oddRun = (k.opened && k.ppar))
    (h00 : (V).andII = escAnd00W k)
    (h15 : st15 = seedW k)
    (hprev : prevS = (if p then 1 else 0)) :
    (V).or135 = entryMask64 k.lo k.hi k.st p := by
  have hall : (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 := by decide
  have hjb : bitcastVecLanes 8 64 (unpackLanes 64 4 (bytesToNat bs136) ++
      unpackLanes 64 4 (bytesToNat bs137)) = blockLanes k :=
    if103_join142_eq_blockLanes (k := k) h136 h137
  have h14 : (V).mask391 = bsW k := if103_mask391_eq_bsW hjb
  have hq : (V).andI = andQuoteW k := by
    rw [if103_andI_eq_specQuote (k := k) hjb h14 h00 hst, andQuoteW_spec k hst]
  have hac1 : (V).and416 = andWordLanes k :=
    if103_and416_eq_andWordLanes (k := k) h136
  have hac2 : (V).and420 = andWordLanesHi k :=
    if103_and420_eq_andWordLanesHi (k := k) h137
  have hd : (V).or19 = specDelimiter64 k.lo k.hi k.st :=
    if103_or19_eq_specDelimiter (k := k) h136 h137
  have hn : (V).mask431 =
      ~~~(specDelimiter64 k.lo k.hi k.st ||| specSpace64 k.lo k.hi k.st) :=
    if103_mask431_eq_neither (k := k) hac1 hac2
  have hx : (V).xorI = specInString64 k.lo k.hi k.st :=
    if103_xorI_eq_specInString (k := k) hq h15 hst
  have hnot : (V).not125 = ~~~(specInString64 k.lo k.hi k.st) := by
    rw [if103_not125, hx, hall, xor_allOnes_eq_not]
  have hq64 : (V).andI = specQuote64 k.lo k.hi k.st := by
    rw [hq, andQuoteW_spec k hst]
  have hsc : (V).and126 = specScalar64 k.lo k.hi k.st := by
    rw [if103_and126, if103_v169, if103_v168, hn, hq64, hx, hall, xor_allOnes_eq_not,
      show ~~~(specQuote64 k.lo k.hi k.st ||| specInString64 k.lo k.hi k.st)
        = ~~~specQuote64 k.lo k.hi k.st &&& ~~~specInString64 k.lo k.hi k.st
        from BitVec.not_or,
      ← BitVec.and_assoc]
    exact specScalar64_eq_neither k.lo k.hi k.st
  rw [if103_or135, if103_v170, if103_and129, if103_and134, if103_not133, if103_or132,
    if103_shl131, hd, hnot, hsc, hq64, hall, xor_allOnes_eq_not,
    show (1#64 : BitVec 64).toNat = 1 from by decide, hprev,
    ← entry_eq_compose k.lo k.hi k.st p]
  ac_rfl

end

/-! ### The one-step instantiation from `docBlock`

The loop's page and the peel both load a document block's two halves.  These are
the word identities above at `bs136`/`bs137` (the peel's windows) and
`bs73`/`bs74` (the page's), with the halves supplied by `docBlock` and
`take32_blockLo`/`take32_blockHi`. -/

/-- **The page's entry word at the document's block `i`.** -/
theorem fb54_or84_eq_entryMask_docBlock (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) (k : Ctx)
    (hlo : k.lo = blockLo (padded bs) i) (hhi : k.hi = blockHi (padded bs) i)
    (hsti : k.st = classCarryAt (padded bs) ⟨false, false⟩ (64 * i))
    (c : FusedCarry) (bs73 bs74 : List UInt8)
    (h73 : bs73 = (docBlock bs i).take 32) (h74 : bs74 = (docBlock bs i).drop 32)
    (hst : k.st.oddRun = (k.opened && k.ppar))
    (h00 : (fusedValues c bs73 bs74).andII = escAnd00W k)
    (h13 : c.st15 = seedW k)
    (hprev : c.prevS = (if stage1PrevS bs i then 1 else 0)) :
    (fusedValues c bs73 bs74).or84 =
      entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i) := by
  have h73' : bs73 = List.ofFn k.lo := by
    rw [h73, docBlock_take32, take32_blockLo bs hi, hlo]
  have h74' : bs74 = List.ofFn k.hi := by
    rw [h74, docBlock_drop32, take32_blockHi bs hi, hhi]
  have h := fb54_or84_eq_entryMask (k := k) (p := stage1PrevS bs i)
    h73' h74' hst h00 h13 hprev
  rw [h, hlo, hhi, hsti]

/-- **The peel's entry word at the document's block `i`.**  The two window loads
are the block's halves (`docBlock_take32`/`docBlock_drop32` with
`take32_blockLo`/`take32_blockHi`). -/
theorem if103_or135_eq_entryMask_docBlock (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) (k : Ctx)
    (hlo : k.lo = blockLo (padded bs) i) (hhi : k.hi = blockHi (padded bs) i)
    (hsti : k.st = classCarryAt (padded bs) ⟨false, false⟩ (64 * i))
    (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64)
    (ent : Nat) (conv prevAscii : BitVec 32)
    (h136 : bs136 = (docBlock bs i).take 32)
    (h137 : bs137 = (docBlock bs i).drop 32)
    (hst : k.st.oddRun = (k.opened && k.ppar))
    (h00 : st0 &&& st9 = escAnd00W k)
    (h15 : st15 = seedW k)
    (hprev : prevS = (if stage1PrevS bs i then 1 else 0)) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).or135 =
      entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i) := by
  have h136' : bs136 = List.ofFn k.lo := by
    rw [h136, docBlock_take32, take32_blockLo bs hi, hlo]
  have h137' : bs137 = List.ofFn k.hi := by
    rw [h137, docBlock_drop32, take32_blockHi bs hi, hhi]
  have h : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
        conv prevAscii).or135 =
      entryMask64 k.lo k.hi k.st (stage1PrevS bs i) :=
    if103_or135_eq_entryMask (k := k) (p := stage1PrevS bs i)
      h136' h137' hst h00 h15 hprev
  rw [h, hlo, hhi, hsti]

/-- **`PeelWordAtModel` at the peel's own word.**  The record's residual is the
entry identity above, so the docBlock instantiation discharges it. -/
theorem if103_or135_peelWordAtModel (bs : List UInt8) {i : Nat}
    (hi : i < blocksOf bs.length) (k : Ctx)
    (hlo : k.lo = blockLo (padded bs) i) (hhi : k.hi = blockHi (padded bs) i)
    (hsti : k.st = classCarryAt (padded bs) ⟨false, false⟩ (64 * i))
    (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64)
    (ent : Nat) (conv prevAscii : BitVec 32)
    (h136 : bs136 = (docBlock bs i).take 32)
    (h137 : bs137 = (docBlock bs i).drop 32)
    (hst : k.st.oddRun = (k.opened && k.ppar))
    (h00 : st0 &&& st9 = escAnd00W k)
    (h15 : st15 = seedW k)
    (hprev : prevS = (if stage1PrevS bs i then 1 else 0)) :
    PeelWordAtModel
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 bs i :=
  peelWordAtModel_of_entryMask
    (if103_or135_eq_entryMask_docBlock bs hi k hlo hhi hsti n b bs136 bs137
      ascii st0 st9 st15 prevS andv shr ent conv prevAscii h136 h137 hst h00 h15
      hprev)

/-- **The peel's stored word is the model's.**  The block's clamp is
`ifThen103Values_and137_eq`'s `limMask andv.toNat`, `limMask_tail_eq` reads that
index as the document's remainder, and the model's word is `stage1Word`. -/
theorem if103_and137_eq_stage1Word (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat)
    (conv prevAscii : BitVec 32) (bs : List UInt8) (i : Nat)
    (hn : n.toNat = bs.length) (hshr : shr = n >>> 6)
    (hand : andv = n &&& 0x000000000000003f#64) (hi : shr.toNat = i)
    (hor : PeelWordAtModel
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 bs i) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).and137 = stage1Word bs i := by
  have hword : (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr
        ent conv prevAscii).or135 =
      entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i) :=
    hor
  have hlim : limMask andv.toNat = limMask (bs.length - 64 * i) := by
    rw [← limMask_tail_eq bs n andv shr hn hshr hand, hi]
  rw [ifThen103Values_and137_eq, hword]
  unfold stage1Word
  rw [hlim]

/-- **The peel's clamp, at the record's own spelling.**  `S1BlocksCallTail`'s
`w` is `or135 &&& limMask andv.toNat`; that word is `stage1Word`, the one the
slot stores. -/
theorem if103_or135_and_limMask_eq_stage1Word (n : BitVec 64) (b : Nat)
    (bs136 bs137 : List UInt8) (ascii : List (BitVec 64))
    (st0 st9 st15 prevS andv shr : BitVec 64) (ent : Nat) (conv prevAscii : BitVec 32)
    (bs : List UInt8) (i : Nat)
    (hn : n.toNat = bs.length) (hshr : shr = n >>> 6)
    (hand : andv = n &&& 0x000000000000003f#64) (hi : shr.toNat = i)
    (hor : PeelWordAtModel
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 bs i) :
    (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
      prevAscii).or135 &&& limMask andv.toNat = stage1Word bs i := by
  rw [← ifThen103Values_and137_eq]
  exact if103_and137_eq_stage1Word n b bs136 bs137 ascii st0 st9 st15 prevS andv
    shr ent conv prevAscii bs i hn hshr hand hi hor

/-! ### Axiom footprints

The entry identities are the mask unit's words, the two packing bridges and
`entry_eq_compose`; the model links are `PeelWordAtModel`'s definition and the
store's clamp.  No statement carries `sorryAx`. -/

#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.cmp64Lanes_eq_specMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_and416_eq_andWordLanes
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_or19_eq_specDelimiter
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_mask431_eq_neither
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_escaped_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_or135_eq_entryMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.fb54_or84_eq_entryMask_docBlock
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_or135_eq_entryMask_docBlock
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_or135_peelWordAtModel
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_and137_eq_stage1Word
#print axioms LeanLLVM.Refinement.JsonS1BlocksPeelWord.if103_or135_and_limMask_eq_stage1Word

end LeanLLVM.Refinement.JsonS1BlocksPeelWord
