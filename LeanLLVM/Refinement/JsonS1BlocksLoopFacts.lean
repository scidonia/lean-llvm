/-
The fused loop's model-side facts, at the loop's own registers.

`JsonS1BlocksRecordFrame` states the entry array's two stores (`EntryPrefix` and
the peel's slot), `JsonS1BlocksStaging` the verdict's three fields from three
carried words, and `JsonS1BlocksLoop` the fused loop's pages from `FusedInv`.
This module joins the loop to those: the facts `S1BlocksFacts` takes as the
loop's — the array's prefix, the loop's frame over it, the peel's `%or135` at
the model's last block, and the verdict carries — stated where the loop can
discharge them.

## What is proved

* **The array's prefix.**  `EntryPrefix` is a per-slot reading;
  `entryPrefix_store` appends one slot, `entryPrefix_mono` narrows,
  `entryPrefix_of_eq` moves a prefix across two memories that read the array
  alike, and `entryWords_of_loop_prefix` adds the peeled slot to the loop's
  prefix.  At the loop's own registers, `entryPrefix_of_fusedStore` is one
  page's step (the page's stored word is the model's, its own identity) and
  `entryFrame_of_fusedStore` places that store inside the array;
  `entryFrame_store`, `entryFrame_comp` and `entryFrame_refl` carry the loop's
  frame across its store and the escape call's own frame.
* **The peel's word at the model.**  `peelWordAtModel_of_entryMask` is the
  residual `PeelWordAtModel` at the mask-composition spelling, and
  `peel_slot_of_model` composes it with the clamp index
  (`limMask_tailNat`) to the slot's `stage1Word` — the shape the tail's store
  consumes.
* **The ASCII carry.**  `packLanes_blockAscii` is one page's ASCII step: the
  latch's lane OR advances the byte fold `asciiAcc` by one block, given the
  loop's carried word at the fold.  `packLanes_peelAscii` is the peeled arm's
  carry: the peel's `%or.i279` packs to the document's byte fold at the block
  count once the loop's `%ascii` is the fold at `shr`.
* **The verdict carries.**  `staging_of_loopExit` reads the loop's two carried
  words at the document's block count as a `VerdictStaging`, which is the
  aligned arm's staging, and `staging_of_exitFacts` is the same reading at
  `LoopExitFacts`; `packLanes_peelAscii` and `ascii_bytes_of_peelAscii` read the
  peeled arm's ASCII word the same way.
* **The seam.**  `LoopExitFacts` is the bundle's shape at the loop's exit;
  `tail_facts_of_exit` projects the tail's array facts from it,
  `entryWords_of_tail_peel` and `tail_peel_facts` add the peeled store and the
  loop's frame, and `entryPrefix_at_exit` reads the prefix at the bound.

## What remains

The per-page word identities the loop's *own* arithmetic owes, which no module
in the tree states yet (each is a pure identity at the page's carry, not a
memory or composition fact):

* the page store word — `(fusedValues c bs73 bs74).or84` is `entryMask64` at the
  block's model carry (`stage1Word`).  This is the fast-table classifier against
  the specification's six masks, at `for.body54`'s registers;
  `JsonS1BlocksIdentities` relates the mask unit's registers to the classifier's
  and `JsonS1BlocksSteps.entry_eq_compose` is the composition, but the transport
  from the fast tables (`forBodyTableA`/`forBodyTableB`, the `ifThen38Table*`
  family) to `specDelimiter64`/`specSpace64` is not stated, and neither is the
  peel's backslash word (`%or14.i391`) as the loop's two-half join
  (`%or14.i`).
* the accumulator step — the DFA arm's `%or.i281` packs to `klErrBlk`'s word,
  advancing `packLanes u8k = bytesToNat (klAcc bs i)` per block.
* the ASCII carry's *base*: the ASCII phase's blocks precede the fused loop and
  its `%ascii` is never accumulated (`%ascii.0` is the entry's zero), so the
  fused loop's `%ascii` is the fold from the hand-off's block, not from block
  zero.  Its high bits are the document's all the same, because the preceding
  blocks are ASCII; the exact `asciiAcc bs nb` identity holds only when the
  hand-off fires at block zero, and the peeled arm's staging needs the high-bit
  form.
* the peeled arm's accumulator: the loop stops at `shr = n >>> 6`, so its
  `%u8k` is `klAcc bs shr`, while the record's staging at `blocksOf` reads
  `klAll`, which folds one more block.  On the peeled arm (`shr + 1 = blocksOf`)
  the two differ by the last block's error word, so the staging's `acc_pack`
  field there needs that block's contribution, not the loop's word.

Nothing here is a weakening of a stated conclusion: the per-page identities are
inputs to the loop's induction, and every conclusion in this module is proved.
-/
import LeanLLVM.Refinement.JsonS1BlocksRecordFrame
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksLoop
import LeanLLVM.Refinement.JsonS1BlocksEntry
import LeanLLVM.Refinement.JsonS1BlocksExit

namespace LeanLLVM.Refinement.JsonS1BlocksLoopFacts

open LeanLLVM
open LeanLLVM.Refinement
open LeanLLVM.Refinement.BlockEval
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksLoop
open LeanLLVM.Refinement.JsonS1BlocksEntry
open LeanLLVM.Refinement.JsonS1BlocksExit
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksStaging
open LeanLLVM.Refinement.JsonS1BlocksVerdict
open LeanLLVM.Refinement.JsonS1BlocksRecordFrame
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonUtf8Steps
open LeanLLVM.Refinement.JsonUtf8Spec
open LeanLLVM.Refinement.BitLanes

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ### Reading a prefix out of a longer read

The loop hands the tail one memory, and the array's prefix is a sub-read of the
loop's own.  Two memories that return the same bytes over the whole array return
the same bytes over every window inside it, and so over every prefix.  These are
the two slices the transfer needs. -/

/-- **Equal present reads have equal sub-reads.**  If both memories return the
same `n` bytes, then at every window inside that range they return the same
bytes. -/
theorem readBytes_sub_of_eq {m M : Mem} {a n i w : Nat} {l : List UInt8}
    (hm : readBytes m a n = some l) (hM : readBytes M a n = some l)
    (hiw : i + w ≤ n) :
    readBytes M (a + i) w = readBytes m (a + i) w := by
  obtain ⟨_, hrest⟩ := readBytes_split m a i (n - i) (by
    rw [show i + (n - i) = n from by omega]; exact hm)
  obtain ⟨_, hrestM⟩ := readBytes_split M a i (n - i) (by
    rw [show i + (n - i) = n from by omega]; exact hM)
  obtain ⟨hx, _⟩ := readBytes_split m (a + i) w (n - i - w) (by
    rw [show w + (n - i - w) = n - i from by omega]; exact hrest)
  obtain ⟨hxM, _⟩ := readBytes_split M (a + i) w (n - i - w) (by
    rw [show w + (n - i - w) = n - i from by omega]; exact hrestM)
  rw [hx, hxM]

/-- **Equal present reads have equal prefixes.** -/
theorem readBytes_prefix_of_eq {m M : Mem} {a n k : Nat} {l : List UInt8}
    (hm : readBytes m a n = some l) (hM : readBytes M a n = some l)
    (hk : k ≤ n) :
    readBytes M a k = readBytes m a k := by
  obtain ⟨h1, _⟩ := readBytes_split m a k (n - k) (by
    rw [show k + (n - k) = n from by omega]; exact hm)
  obtain ⟨h2, _⟩ := readBytes_split M a k (n - k) (by
    rw [show k + (n - k) = n from by omega]; exact hM)
  rw [h1, h2]

/-! ### The entry array's prefix and frame

`EntryPrefix` is a per-slot reading of the array; the loop appends one slot per
page, and its frame says nothing outside the array.  These are the moves the
loop's array facts are made of. -/

/-- **One more slot.**  A prefix at `k` plus the slot `k`'s word at the slot's
own address is a prefix at `k + 1`. -/
theorem entryPrefix_store {mem : Mem} {ent : Nat} {bs : List UInt8} {k : Nat}
    {w : BitVec 64}
    (hp : EntryPrefix mem ent bs k)
    (hw : readBytes (writeBytes mem (ent + 8 * k) (natToBytes w.toNat 8))
      (ent + 8 * k) 8 = some (wordsOf [stage1Word bs k])) :
    EntryPrefix (writeBytes mem (ent + 8 * k) (natToBytes w.toNat 8)) ent bs (k + 1) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hik | hik
  · rw [readBytes_writeBytes_below mem (natToBytes w.toNat 8) 8 (ent + 8 * i)
      (ent + 8 * k) (by omega)]
    exact hp i hik
  · subst hik
    exact hw

/-- **A prefix at a longer extent is a prefix at a shorter one.** -/
theorem entryPrefix_mono {mem : Mem} {ent : Nat} {bs : List UInt8} {k k' : Nat}
    (hk : k' ≤ k) (hp : EntryPrefix mem ent bs k) : EntryPrefix mem ent bs k' :=
  fun i hi => hp i (by omega)

/-- **A prefix moves across memories that read the array alike.**  The loop's
prefix is a sub-read of the array's `8 * blocks` bytes, so a memory that returns
those bytes the same returns the prefix the same. -/
theorem entryPrefix_of_eq {mem M : Mem} {ent : Nat} {bs : List UInt8} {k : Nat}
    {l : List UInt8}
    (hm : readBytes mem ent (8 * blocksOf bs.length) = some l)
    (hM : readBytes M ent (8 * blocksOf bs.length) = some l)
    (hk : k ≤ blocksOf bs.length) (hp : EntryPrefix mem ent bs k) :
    EntryPrefix M ent bs k := by
  intro i hi
  have hsub := readBytes_sub_of_eq hm hM (i := 8 * i) (w := 8) (by omega)
  rw [hsub]
  exact hp i hi

/-- **The loop's frame survives a store inside the array.** -/
theorem entryFrame_store {mem0 mem : Mem} {ent blocks a : Nat} {bs : List UInt8}
    (hf : EntryFrame mem0 mem ent blocks)
    (ha : ent ≤ a) (hb : a + bs.length ≤ ent + 8 * blocks) :
    EntryFrame mem0 (writeBytes mem a bs) ent blocks :=
  frame_write_inside hf ha hb

/-- **The loop's frame composes with the escape call's.**  A call that leaves
every byte outside the array alone, after the loop's frame over it, is one frame
from the caller's memory to the call's. -/
theorem entryFrame_comp {mem0 mem1 mem2 : Mem} {ent blocks : Nat}
    (h1 : EntryFrame mem0 mem1 ent blocks)
    (h2 : EntryFrame mem1 mem2 ent blocks) :
    EntryFrame mem0 mem2 ent blocks :=
  frame_comp h1 h2 (fun _ hr => hr)

/-- The loop's frame is reflexive at any memory. -/
theorem entryFrame_refl (mem : Mem) (ent blocks : Nat) :
    EntryFrame mem mem ent blocks := fun _ _ => rfl

/-- **The entry array at the peel's memory, from the loop's prefix.**  Below the
slot the read is the loop's prefix (the store is above it); at the slot it is the
peel's word; `entryWords_of_prefix_store` joins them. -/
theorem entryWords_of_loop_prefix {mem : Mem} {ent shr : Nat} {bs : List UInt8}
    {w : BitVec 64}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hprefix : EntryPrefix mem ent bs shr)
    (hslot : readBytes (writeBytes mem (ent + 8 * shr) (natToBytes w.toNat 8))
      (ent + 8 * shr) 8 = some (wordsOf [stage1Word bs shr])) :
    readBytes (writeBytes mem (ent + 8 * shr) (natToBytes w.toNat 8)) ent
        (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) := by
  have hread : readBytes mem ent (8 * shr) = some (wordsOf ((stage1Words bs).take shr)) :=
    entryPrefix_read (by omega) hprefix
  exact entryWords_of_prefix_store hsucc hread hslot

/-! ### The peel's clamp index at its Nat slot

The peel's `%and` is the document's remainder and `%shr` its whole-block count,
so the model's tail index `bs.length - 64 * shr` is `%and`. -/
theorem limMask_tailNat {bs : List UInt8} {andv shr : BitVec 64} {i : Nat}
    (hand : andv.toNat = bs.length % 64) (hshr : shr.toNat = bs.length / 64)
    (hi : i = shr.toNat) :
    limMask andv.toNat = limMask (bs.length - 64 * i) := by
  subst hi
  have htail : bs.length - 64 * shr.toNat = andv.toNat := by
    rw [hand, hshr]
    have hdm := Nat.div_add_mod bs.length 64
    omega
  rw [htail]

/-! ### The peel's word at the model

`PeelWordAtModel` is the mask composition at the document's last block; the
peel's store word is that composition clamped at `%and`, which is the model's
`stage1Word`.  The two clauses below are the residual as the record states it
and the slot it feeds. -/

/-- **The peel's word at the model**, at the peeled index `shr`. -/
theorem peelWordAtModel_of_entryMask {or135 : BitVec 64} {bs : List UInt8} {i : Nat}
    (h : or135 = entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
      (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i)) :
    PeelWordAtModel or135 bs i :=
  h

/-- **The peel's slot is the model's word.**  `%or135 &&& limMask %and` at the
model's last block is `stage1Word`, and the store reads back as that word. -/
theorem peel_slot_of_model {mem : Mem} {ent shr : Nat} {bs : List UInt8}
    {or135 andv : BitVec 64}
    (hor : PeelWordAtModel or135 bs shr)
    (hlim : limMask andv.toNat = limMask (bs.length - 64 * shr)) :
    readBytes
      (writeBytes mem (ent + 8 * shr) (natToBytes (or135 &&& limMask andv.toNat).toNat 8))
      (ent + 8 * shr) 8 = some (wordsOf [stage1Word bs shr]) := by
  have hword : or135 &&& limMask andv.toNat = stage1Word bs shr := by
    unfold stage1Word
    rw [hor, hlim]
  rw [hword, ← wordsOf_singleton]
  have h := readBytes_writeBytes_same mem (wordsOf [stage1Word bs shr])
    (addr := ent + 8 * shr)
  simpa [wordsOf_singleton, natToBytes_length] using h

/-! ### One page's ASCII step

The latch ORs the page's two half-vectors lane for lane into the carried word
(`%or.i283`, then `%or.i282`), and the block's byte fold advances by the same
half-OR.  `packLanes_blockAscii` is that step at the four-lane carrier, so the
loop's invariant `packLanes ascii = bytesToNat (asciiAcc bs i)` is carried by
the page. -/

/-- `|||` on lane lists is commutative; the page writes the high half first. -/
theorem zipWith_or_comm (a b : List (BitVec 64)) :
    List.zipWith (fun x y => x ||| y) a b =
      List.zipWith (fun x y => x ||| y) b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
      cases b with
      | nil => rfl
      | cons y ys =>
          show (x ||| y) :: List.zipWith (fun x y => x ||| y) xs ys =
            (y ||| x) :: List.zipWith (fun x y => x ||| y) ys xs
          rw [BitVec.or_comm x y]
          exact congrArg _ (ih ys)

/-- Two ORs of naturals, reordered: `(a ||| b) ||| c = c ||| (b ||| a)`. -/
theorem or3_comm (a b c : Nat) : (a ||| b) ||| c = c ||| (b ||| a) := by
  rw [Nat.or_comm (a ||| b) c, Nat.or_comm a b]

/-- The lane OR of two four-lane words packs to the OR of their packings. -/
theorem packLanes_or4 {a b : List (BitVec 64)} (ha : a.length = 4)
    (hb : b.length = 4) :
    packLanes (List.zipWith (fun x y => x ||| y) a b) = packLanes a ||| packLanes b :=
  packLanes_zipWith_or (by rw [ha, hb])

/-- **One page's ASCII step.**  From the loop's carried word at the byte fold
`asciiAcc bs i`, the latch's join with the page's two halves packs to the fold at
`i + 1`. -/
theorem packLanes_blockAscii {bs : List UInt8} {i : Nat} {bs73 bs74 : List UInt8}
    {ascii : List (BitVec 64)}
    (hi : i < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs i).take 32)
    (h74 : bs74 = (docBlock bs i).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAcc bs i)) :
    packLanes (fb54Or (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
        (unpackLanes 64 4 (bytesToNat bs73))) ascii) =
      bytesToNat (asciiAcc bs (i + 1)) := by
  have hblen : (docBlock bs i).length = 64 := docBlock_length_of_lt bs hi
  have h73len : bs73.length = 32 := by simp [h73, hblen]
  have h74len : bs74.length = 32 := by simp [h74, hblen]
  have h73n : (unpackLanes 64 4 (bytesToNat bs73)).length = 4 := unpackLanes_length ..
  have h74n : (unpackLanes 64 4 (bytesToNat bs74)).length = 4 := unpackLanes_length ..
  have hw73 : packLanes (unpackLanes 64 4 (bytesToNat bs73)) = bytesToNat bs73 :=
    packLanes_unpackLanes_bytesToNat bs73 h73len
  have hw74 : packLanes (unpackLanes 64 4 (bytesToNat bs74)) = bytesToNat bs74 :=
    packLanes_unpackLanes_bytesToNat bs74 h74len
  unfold fb54Or
  rw [packLanes_or4 (by simp [List.length_zipWith, h74n, h73n]) hasciilen,
    packLanes_or4 h74n h73n, hw74, hw73, hacc]
  have hbh : blockHalfOr bs i = List.zipWith (fun x y => x ||| y) bs73 bs74 := by
    unfold blockHalfOr
    rw [h73, h74]
  rw [asciiAcc_succ,
    bytesToNat_zipWith_or _ _
      (by rw [asciiAcc_length bs (j := i) (by omega), blockHalfOr_length bs hi]),
    hbh, bytesToNat_zipWith_or _ _ (by rw [h73len, h74len])]
  exact or3_comm _ _ _

/-- **One page's ASCII step, at the successor carry.**  The fused loop's
successor word is `fusedAscii`; this names the step at it. -/
theorem fusedAscii_pack {c : FusedCarry} {bs : List UInt8} {bs73 bs74 : List UInt8}
    (hi : c.i.toNat < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hasciilen : c.ascii.length = 4)
    (hacc : packLanes c.ascii = bytesToNat (asciiAcc bs c.i.toNat)) :
    packLanes (fusedAscii c bs73 bs74) =
      bytesToNat (asciiAcc bs (c.i.toNat + 1)) := by
  show packLanes (fb54Or (fb54Or (unpackLanes 64 4 (bytesToNat bs74))
      (unpackLanes 64 4 (bytesToNat bs73))) c.ascii) =
    bytesToNat (asciiAcc bs (c.i.toNat + 1))
  exact packLanes_blockAscii hi h73 h74 hasciilen hacc

/-! ### The peeled arm's ASCII carry

The peel's `%or.i279` is its two windows' join OR-ed into the loop's carried
word.  When the loop's word is the byte fold at `shr` and the peel reads block
`shr`, the word packs to the fold at `shr + 1` — the document's block count on
the peeled arm. -/

/-- **The peel's ASCII word packs to the document's fold.** -/
theorem packLanes_peelAscii {n : BitVec 64} {b : Nat} {bs136 bs137 : List UInt8}
    {ascii : List (BitVec 64)} {st0 st9 st15 prevS andv shr : BitVec 64}
    {ent : Nat} {conv prevAscii : BitVec 32} {bs : List UInt8}
    (hsucc : shr.toNat + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs shr.toNat).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAcc bs shr.toNat)) :
    packLanes (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent
        conv prevAscii).or279 =
      bytesToNat (asciiAcc bs (blocksOf bs.length)) := by
  have hblen : (docBlock bs shr.toNat).length = 64 :=
    docBlock_length_of_lt bs (by omega)
  have h136len : bs136.length = 32 := by simp [h136, hblen]
  have h137len : bs137.length = 32 := by simp [h137, hblen]
  have h136n : (unpackLanes 64 4 (bytesToNat bs136)).length = 4 := unpackLanes_length ..
  have h137n : (unpackLanes 64 4 (bytesToNat bs137)).length = 4 := unpackLanes_length ..
  have hw136 : packLanes (unpackLanes 64 4 (bytesToNat bs136)) = bytesToNat bs136 :=
    packLanes_unpackLanes_bytesToNat bs136 h136len
  have hw137 : packLanes (unpackLanes 64 4 (bytesToNat bs137)) = bytesToNat bs137 :=
    packLanes_unpackLanes_bytesToNat bs137 h137len
  show packLanes (List.zipWith (fun x y => x ||| y)
      (List.zipWith (fun x y => x ||| y)
        (unpackLanes 64 4 (bytesToNat bs137))
        (unpackLanes 64 4 (bytesToNat bs136))) ascii) = _
  rw [packLanes_or4 (by simp [List.length_zipWith, h137n, h136n]) hasciilen,
    packLanes_or4 h137n h136n, hw137, hw136, hacc]
  have hbh : blockHalfOr bs shr.toNat =
      List.zipWith (fun x y => x ||| y) bs136 bs137 := by
    unfold blockHalfOr
    rw [h136, h137]
  rw [← hsucc, asciiAcc_succ,
    bytesToNat_zipWith_or _ _
      (by rw [asciiAcc_length bs (j := shr.toNat) (by omega),
        blockHalfOr_length bs (by omega)]),
    hbh, bytesToNat_zipWith_or _ _ (by rw [h136len, h137len])]
  exact or3_comm _ _ _

/-- **A store reads back as its word.**  Any eight-byte store at its own address
reads as that word, in `wordsOf`'s spelling. -/
theorem store_read_word (mem : Mem) (addr : Nat) (w : BitVec 64) :
    readBytes (writeBytes mem addr (natToBytes w.toNat 8)) addr 8 = some (wordsOf [w]) := by
  have h := readBytes_writeBytes_same mem (natToBytes w.toNat 8) (addr := addr)
  rw [natToBytes_length] at h
  simpa [wordsOf] using h

/-- **One page's prefix step, at the loop's own store.**  The page writes
`fusedValues.or84` at `%ent + 8 * i`; when that word is the model's
(`stage1Word` at the page's index), the loop's prefix gains the slot.  The word
identity is the page's own, named here rather than assumed anywhere else. -/
theorem entryPrefix_of_fusedStore {c : FusedCarry} {bs : List UInt8}
    {bs73 bs74 : List UInt8}
    (hp : EntryPrefix c.mem c.ent bs c.i.toNat)
    (hstore : (fusedValues c bs73 bs74).or84 = stage1Word bs c.i.toNat) :
    EntryPrefix (fusedStore c bs73 bs74) c.ent bs (c.i.toNat + 1) := by
  show EntryPrefix (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
    (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) c.ent bs (c.i.toNat + 1)
  rw [fusedValues_arrayidx]
  refine entryPrefix_store hp ?_
  rw [hstore]
  exact store_read_word _ _ _

/-- **One page's frame step, at the loop's own store.**  The page's store is
inside the entry array, so the loop's frame survives it. -/
theorem entryFrame_of_fusedStore {mem0 : Mem} {c : FusedCarry} {bs : List UInt8}
    {bs73 bs74 : List UInt8}
    (hf : EntryFrame mem0 c.mem c.ent (blocksOf bs.length))
    (hi : c.i.toNat < blocksOf bs.length) :
    EntryFrame mem0 (fusedStore c bs73 bs74) c.ent (blocksOf bs.length) := by
  show EntryFrame mem0 (writeBytes c.mem (fusedValues c bs73 bs74).arrayidx
    (natToBytes (fusedValues c bs73 bs74).or84.toNat 8)) c.ent (blocksOf bs.length)
  rw [fusedValues_arrayidx]
  refine frame_write_inside hf (by omega) ?_
  rw [natToBytes_length]
  omega

/-- **One page's prefix step, at the loop's carried ASCII word.**  The page's
successor is `fusedAscii`, whose packing this advances. -/
theorem ascii_of_fusedAscii {c : FusedCarry} {bs : List UInt8} {bs73 bs74 : List UInt8}
    (hi : c.i.toNat < blocksOf bs.length)
    (h73 : bs73 = (docBlock bs c.i.toNat).take 32)
    (h74 : bs74 = (docBlock bs c.i.toNat).drop 32)
    (hasciilen : c.ascii.length = 4)
    (hacc : packLanes c.ascii = bytesToNat (asciiAcc bs c.i.toNat)) :
    packLanes (fusedAscii c bs73 bs74) =
      bytesToNat (asciiAcc bs (c.i.toNat + 1)) :=
  fusedAscii_pack hi h73 h74 hasciilen hacc

/-! ### The verdict carries at the loop's exit

The record's staging is the loop's two carried words at the document's block
count.  On the aligned arm the count is the loop's bound (`shr`), so the
invariant's `packLanes u8k = bytesToNat (klAcc bs shr)` is the record's
`klAll`; on the peeled arm the ASCII word is the peel's, whose fold is one block
further. -/

/-- **The aligned arm's staging, from the loop's invariant.**  At the loop's
bound equal to the document's block count, the carried words are the record's
three fields. -/
theorem staging_of_loopExit {bs : List UInt8} {n nb : Nat} {gate : Bool}
    {ascii u8k : List (BitVec 64)} {err : BitVec 1} {i : Nat}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length) (hi : i = nb)
    (hasciilen : ascii.length = 4) (hu8klen : u8k.length = 4)
    (hascii : packLanes ascii = bytesToNat (asciiAcc bs i))
    (haccK : packLanes u8k = bytesToNat (klAcc bs i))
    (herr : err = 1 ↔ ¬ (u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging ascii u8k bs n nb gate err :=
  staging_of_loopAcc bs n nb gate ascii u8k err hasciilen hu8klen hn hnb
    (by rw [← hi]; exact hascii) (by rw [← hi]; exact haccK) herr

/-- **The peeled arm's ASCII field.**  The peel's `%or.i279` is the document's
byte fold at the block count, so the staging's `ascii_bytes` clause is the
document's. -/
theorem ascii_bytes_of_peelAscii {n : BitVec 64} {b : Nat} {bs136 bs137 : List UInt8}
    {ascii : List (BitVec 64)} {st0 st9 st15 prevS andv shr : BitVec 64}
    {ent : Nat} {conv prevAscii : BitVec 32} {bs : List UInt8}
    (hsucc : shr.toNat + 1 = blocksOf bs.length)
    (h136 : bs136 = (docBlock bs shr.toNat).take 32)
    (h137 : bs137 = (docBlock bs shr.toNat).drop 32)
    (hasciilen : ascii.length = 4)
    (hacc : packLanes ascii = bytesToNat (asciiAcc bs shr.toNat)) :
    (∀ b' ∈ asciiBytes (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv
        shr ent conv prevAscii).or279, b'.toNat < 0x80) ↔
      ∀ x ∈ bs, x.toNat < 0x80 := by
  have hpack := packLanes_peelAscii (n := n) (b := b)
    (bs136 := bs136) (bs137 := bs137) (ascii := ascii)
    (st0 := st0) (st9 := st9) (st15 := st15) (prevS := prevS) (andv := andv)
    (shr := shr) (ent := ent) (conv := conv) (prevAscii := prevAscii) (bs := bs)
    hsucc h136 h137 hasciilen hacc
  have hbytes : asciiBytes (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS
      andv shr ent conv prevAscii).or279 = asciiAcc bs (blocksOf bs.length) := by
    unfold asciiBytes
    rw [hpack, ← asciiAcc_length bs (j := blocksOf bs.length) (Nat.le_refl _),
      JsonUtf8Steps.natToBytes_bytesToNat]
  rw [hbytes, asciiAcc_high_iff]
  exact (ascii_padded_iff bs).symm

/-! ### The seam

The loop's exit facts, as the bundle reads them: the memory the loop hands the
tail, its array's prefix and frame, and the carried words. -/

/-- **The loop's exit facts.**  The seven carried words and the memory at
`for.end101`, with the array's per-slot prefix and the loop's frame. -/
structure LoopExitFacts (mem0 : Mem) (bs : List UInt8) (c : FusedCarry) : Prop where
  /-- The array's prefix, one word per block the loop passed. -/
  arrPrefix : EntryPrefix c.mem c.ent bs c.i.toNat
  /-- Every write the loop made is inside the array. -/
  arrFrame : EntryFrame mem0 c.mem c.ent (blocksOf bs.length)
  /-- The carried ASCII word at its fold. -/
  arrAscii : packLanes c.ascii = bytesToNat (asciiAcc bs c.i.toNat)
  /-- The carried accumulator at its fold. -/
  arrU8k : packLanes c.u8k = bytesToNat (klAcc bs c.i.toNat)
  /-- The ASCII word has four lanes. -/
  ascLen : c.ascii.length = 4
  /-- The accumulator has four lanes. -/
  accLen : c.u8k.length = 4

/-- **The tail's loop facts.**  The bundle reads the array's prefix at the
peel's index, the loop's frame over the whole array, and the carried words at the
document's block count.  `i` is the loop's bound: the aligned arm has it at the
block count, the peeled arm one short of it. -/
theorem tail_facts_of_exit {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    (h : LoopExitFacts mem0 bs c) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 c.mem c.ent (blocksOf bs.length) :=
  ⟨h.arrPrefix, h.arrFrame⟩

/-- **The peeled arm's array.**  The loop's prefix at `shr` plus the peel's
slot is the document's array. -/
theorem entryWords_of_tail_peel {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {w : BitVec 64}
    (h : LoopExitFacts mem0 bs c)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hslot : readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
      (c.ent + 8 * c.i.toNat) 8 = some (wordsOf [stage1Word bs c.i.toNat])) :
    readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8)) c.ent
        (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
  entryWords_of_loop_prefix hsucc h.arrPrefix hslot

/-- **The array at the loop's exit index.**  `FusedExit` pins the carried index
to the bound (`c.i = c.shr`), so the exit's prefix is the prefix at the bound the
peel reads. -/
theorem entryPrefix_at_exit {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {env : Env} {s : State}
    (h : LoopExitFacts mem0 bs c) (he : FusedExit env s c) :
    EntryPrefix c.mem c.ent bs c.shr.toNat := by
  have hi : c.i.toNat = c.shr.toNat := by rw [he.bound_reached]
  rw [← hi]
  exact h.arrPrefix

/-- **The loop's frame at the peel's store.**  The peel writes inside the array,
so the loop's frame is the tail's frame after the store. -/
theorem entryFrame_of_tail_peel {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {w : BitVec 64}
    (h : LoopExitFacts mem0 bs c)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length) :
    EntryFrame mem0 (writeBytes c.mem (c.ent + 8 * c.i.toNat)
      (natToBytes w.toNat 8)) c.ent (blocksOf bs.length) :=
  peelStore_frame h.arrFrame hsucc (natToBytes_length w.toNat 8)

/-- **The aligned arm's staging, from the loop's exit facts.**  At an exit whose
bound is the document's block count, the structure's two carried words are the
record's `VerdictStaging`. -/
theorem staging_of_exitFacts {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    (h : LoopExitFacts mem0 bs c)
    {n nb : Nat} {gate : Bool} {err : BitVec 1}
    (hn : n = bs.length) (hnb : nb = blocksOf bs.length)
    (hi : c.i.toNat = nb)
    (herr : err = 1 ↔ ¬ (c.u8k.all (fun x => decide (x = 0x00)) = true) ∨
      (n ≠ 0 ∧ klTailByte (klByte bs (n - 1)) = true)) :
    VerdictStaging c.ascii c.u8k bs n nb gate err :=
  staging_of_loopExit (i := c.i.toNat) hn hnb hi h.ascLen h.accLen h.arrAscii
    h.arrU8k herr

/-- **The peeled arm's array from the loop's exit facts.**  The loop's prefix, the
peel's slot read at the model's word, and the frame: the tail's three loop facts
in one statement. -/
theorem tail_peel_facts {mem0 : Mem} {bs : List UInt8} {c : FusedCarry}
    {w : BitVec 64}
    (h : LoopExitFacts mem0 bs c)
    (hsucc : c.i.toNat + 1 = blocksOf bs.length)
    (hslot : readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
      (c.ent + 8 * c.i.toNat) 8 = some (wordsOf [stage1Word bs c.i.toNat])) :
    EntryPrefix c.mem c.ent bs c.i.toNat ∧
      EntryFrame mem0 (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8))
        c.ent (blocksOf bs.length) ∧
      readBytes (writeBytes c.mem (c.ent + 8 * c.i.toNat) (natToBytes w.toNat 8)) c.ent
        (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
  ⟨h.arrPrefix, entryFrame_of_tail_peel h hsucc,
    entryWords_of_tail_peel h hsucc hslot⟩

/-! ### Axiom footprints

The memory moves are `readBytes`'s slicing, `writeBytes`'s below-store reads and
`UnchangedOutside`'s composition; the lane moves are `packLanes`'s OR
homomorphism, `unpackLanes`'s round trip and Staging's block fold.  No statement
carries `sorryAx`; the reports below name each carrier. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.readBytes_sub_of_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.readBytes_prefix_of_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryPrefix_store
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryPrefix_mono
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryPrefix_of_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryFrame_store
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryFrame_comp
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryFrame_refl
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryWords_of_loop_prefix
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.store_read_word
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryPrefix_of_fusedStore
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryFrame_of_fusedStore
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.ascii_of_fusedAscii
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.limMask_tailNat
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.peelWordAtModel_of_entryMask
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.peel_slot_of_model
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.zipWith_or_comm
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.or3_comm
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.packLanes_or4
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.packLanes_blockAscii
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.fusedAscii_pack
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.packLanes_peelAscii
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.staging_of_loopExit
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.ascii_bytes_of_peelAscii
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.LoopExitFacts
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.tail_facts_of_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryWords_of_tail_peel
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryPrefix_at_exit
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.entryFrame_of_tail_peel
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.tail_peel_facts
#print axioms LeanLLVM.Refinement.JsonS1BlocksLoopFacts.staging_of_exitFacts

end LeanLLVM.Refinement.JsonS1BlocksLoopFacts
