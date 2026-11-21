/-
The block unit's memory conjuncts, at the tail's own blocks.

`JsonS1BlocksCompose` leaves the peeled tail's memory obligations named but not
composed: the entry array (the loop's prefix words plus the peel's stored word),
the escape list's stream and count, and the four-region `UnchangedOutside` the
post claims.  This module composes them from the parts the tail's blocks prove,
and states in one place exactly which facts remain the loop's.

## The entry array

Two stores make the array, and neither is the block's whole claim:

* the fused loop writes one word at `ent + 8 * i` per block it passes
  (`EntryPrefix`), and
* the peel writes the last one at `ent + 8 * shr`, clamped by `limMask`.

`readBytes_slots_wordsOf` turns the loop's per-slot reads into one read of the
prefix `8 * shr` bytes — the loop's invariant is per slot, so this bridge is what
the composition needs and what the loop lane does not have to restate.
`entryWords_of_prefix_store` appends the peel's slot to that prefix: below the
slot the read is the prefix's (the store is above it), at the slot it is the
store's, and `wordsOf` distributes over the append.

`if_then103_store_stage1Word` is the peel's own contribution: `if_then103_store_model`
says the slot holds `%or135 &&& limMask %and`, and the only model-side work left is
the clamp's index.  `%and` is the length's remainder (`and_sixtythree_toNat`) and
`%shr` is its whole-block count (`ushr_six_toNat`), so
`bs.length - 64 * shr = andv` and the two `limMask`s agree.  What the block cannot
supply is `%or135` itself: that is the last block's mask composition at the loop's
carried words, stated as `PeelWordAtModel`.

## The escape list's clauses

`escapeClauses_of_reach` reads the record's `EscapeReach` for the post's three
clauses: the count is the caller's plus the block's positions, the segment this
call wrote is the position word's, and the carry's sixteen bytes are a flag pair.

The stream clause is the one place the record is narrower than the post: the
record states the *segment* this call wrote (`escapeSegment_of_reach`), at
`xp + 4 * xn`, while the post reads the whole stream at the run's count.  The
record's frame cannot supply the bytes below the cursor: its stream region starts
at `xp`, so it denies nothing there, while the run's stores start at the cursor.
So the stream's prefix is the caller's (`StreamPrefix`) and the prefix read is
taken at the run's memory; `escapeClauses_of_reach` composes the two.  A frame
naming the region from `xp + 4 * xn0` would make the prefix derivable, and until
the record is sharpened that way a call site has to supply the prefix itself.

## The frame

`frame_of_peel_call` is the four-region claim: the run's frame at the count the
peel's call is entered with (`escapeCallWriteRegions`), the peel's store inside
the entry array, and the call silent outside its three regions.  The three are
literally the tail of the post's region list, so the composition is membership
and `frame_comp`, with the call's segment widening the stream's region to the
count it left (`escapeCallWriteRegions_widen`).  The entry array's bytes are
outside the call's regions by the staging's separations at the extent the record
*touched*, which is `escapeReach_keepsEntry` and reduces the entry clause after
the call to the entry clause before it.

## What remains

`s1_blocks_satisfies` still takes, from the fused loop lane:

* `EntryPrefix memL ent bs shr` — each slot before the peel's holds the model's
  word (the loop's per-block tie, not a memory fact about this block);
* the run's frame — every write the loop and the peel's call made is inside the
  post's four regions; on a configuration whose pages keep silent that is
  `EntryFrame mem0 memL ent (blocksOf bs.length)`, and on one whose pages call it
  is the four-region frame at the count the pages left (`S1BlocksTail`'s third
  disjunct);
* `PeelWordAtModel v.or135 bs shr` — the peel's `%or135` is the last block's
  `entryMask64` at the loop's carried state and run start;
* `StreamPrefix` at the run's memory — the stream's prefix, which the caller
  staged and the record's frame does not restate;
* and, on the aligned arm, the entry array is wholly the loop's: no word is the
  peel's, and `entryWords_of_prefix_full` turns `EntryPrefix` at the document's
  block count into the post's read.
-/
import LeanLLVM.Refinement.JsonS1BlocksCompose
import LeanLLVM.Refinement.JsonS1BlocksStaging
import LeanLLVM.Refinement.JsonS1BlocksExit

namespace LeanLLVM.Refinement.JsonS1BlocksRecordFrame

open LeanLLVM
open LeanLLVM.JSON
open LeanLLVM.Refinement
open LeanLLVM.Refinement.JsonScanSpec
open LeanLLVM.Refinement.JsonS1MasksIR
open LeanLLVM.Refinement.JsonEntryIR (wordsOf)
open LeanLLVM.Refinement.JsonEntrySteps
open LeanLLVM.Refinement.JsonS1BlocksIR
open LeanLLVM.Refinement.JsonS1BlocksSteps
open LeanLLVM.Refinement.JsonS1BlocksRefine
open LeanLLVM.Refinement.JsonS1BlocksTail
open LeanLLVM.Refinement.JsonS1BlocksCompose
open LeanLLVM.Refinement.JsonS1BlocksExit

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ### Frame algebra

`UnchangedOutside` is a per-byte equality outside a region list; these are the
three moves the composition needs and no more.  (`JsonEscapeFinalCopy` states the
same three, but it is not in this module's import closure, so the statements are
here at the sizes this module composes with.) -/

/-- **A narrower frame implies a wider one.** -/
theorem frame_mono {m0 m : Mem} {R R' : List (Nat × Nat)}
    (h : UnchangedOutside m0 m R') (hsub : ∀ r ∈ R', r ∈ R) :
    UnchangedOutside m0 m R :=
  fun a ha => h a (fun r hr => ha r (hsub r hr))

/-- **Two frames compose when the first's regions contain the second's.**  A byte
outside the first list is outside the second's too, so the second leaves it as the
middle memory had it and the first leaves it as the caller did. -/
theorem frame_comp {m0 m1 m2 : Mem} {R₁ R₂ : List (Nat × Nat)}
    (h1 : UnchangedOutside m0 m1 R₁) (h2 : UnchangedOutside m1 m2 R₂)
    (hsub : ∀ r ∈ R₂, r ∈ R₁) : UnchangedOutside m0 m2 R₁ :=
  fun a ha => (h2 a (fun r hr => ha r (hsub r hr))).trans (h1 a ha)

/-- **A store inside a region leaves the frame over that region.** -/
theorem frame_write_inside {m0 m : Mem} {lo w a : Nat} {bs : List UInt8}
    (h : UnchangedOutside m0 m [(lo, w)]) (ha : lo ≤ a)
    (hb : a + bs.length ≤ lo + w) :
    UnchangedOutside m0 (writeBytes m a bs) [(lo, w)] := by
  intro x hx
  have hx' : ¬ (lo ≤ x ∧ x < lo + w) := hx (lo, w) List.mem_cons_self
  have hout : x < a ∨ a + bs.length ≤ x := by omega
  rw [readByte_writeBytes_outside m bs hout]
  exact h x hx

/-- **A store inside a list's head region leaves a frame over the list.**  The
head is the region the store lies in — the entry array, when the list is the
four-region frame — and the tail is unaffected. -/
theorem frame_write_in_region {m0 m : Mem} {R : List (Nat × Nat)} {lo w a : Nat}
    {bs : List UInt8}
    (h : UnchangedOutside m0 m ((lo, w) :: R))
    (ha : lo ≤ a) (hb : a + bs.length ≤ lo + w) :
    UnchangedOutside m0 (writeBytes m a bs) ((lo, w) :: R) := by
  intro x hx
  have hx' : ¬ (lo ≤ x ∧ x < lo + w) := fun hc => hx (lo, w) List.mem_cons_self hc
  have hout : x < a ∨ a + bs.length ≤ x := by omega
  rw [readByte_writeBytes_outside m bs hout]
  exact h x hx

/-- **A whole range read outside the frame is the caller's.** -/
theorem readBytes_frame {m0 m : Mem} {regions : List (Nat × Nat)} :
    ∀ (n : Nat) {a : Nat},
      (UnchangedOutside m0 m regions) →
      (∀ k, k < n → ∀ r ∈ regions, ¬ (r.1 ≤ a + k ∧ a + k < r.1 + r.2)) →
      readBytes m a n = readBytes m0 a n
  | 0, _, _, _ => rfl
  | n + 1, a, hframe, hout => by
      have hb : readByte m0 a = readByte m a := (hframe a (hout 0 (by omega))).symm
      simp only [readBytes]
      rw [hb]
      cases hc : readByte m a with
      | none => rfl
      | some b =>
          rw [readBytes_frame n (a := a + 1) hframe
            (fun k hk r hr => by
              have h := hout (k + 1) (by omega) r hr
              rw [show a + 1 + k = a + (k + 1) from by omega]
              exact h)]

/-- A range separated on one side of a single region reads through its store. -/
theorem readBytes_frame_single {m0 m : Mem} {lo w a n : Nat}
    (hframe : UnchangedOutside m0 m [(lo, w)])
    (hsep : lo + w ≤ a ∨ a + n ≤ lo) :
    readBytes m a n = readBytes m0 a n :=
  readBytes_frame n hframe (fun k hk r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain rfl := hr
    omega)

/-! ### Words and positions as bytes -/

/-- The entry stream distributes over an append. -/
theorem wordsOf_append (a b : List (BitVec 64)) :
    wordsOf (a ++ b) = wordsOf a ++ wordsOf b := by
  simp only [wordsOf, List.map_append, List.flatten_append]

/-- A one-word entry stream is the word's bytes. -/
theorem wordsOf_singleton (w : BitVec 64) :
    wordsOf [w] = natToBytes w.toNat 8 := by
  simp only [wordsOf, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]

/-- The position stream distributes over an append. -/
theorem positionsBytes_append (w : Nat) (a b : List Nat) :
    positionsBytes w (a ++ b) = positionsBytes w a ++ positionsBytes w b := by
  simp only [positionsBytes, List.map_append, List.flatten_append]

/-! ### The loop's prefix, spelled at its slots

The fused loop's invariant is per slot: each store leaves `ent + 8 * i` holding
the model's `i`th word.  `readBytes_slots_wordsOf` is the bridge from that
spelling to one read of the prefix, and `entryPrefix_read` names it at the
document's own list of words. -/

/-- **The loop's prefix, in the loop's own vocabulary.**  Each slot before the
peel's holds the model's word for that block.  This is the obligation the fused
loop's invariant discharges; nothing in this module can, because it is a fact
about the words the loop wrote. -/
def EntryPrefix (mem : Mem) (ent : Nat) (bs : List UInt8) (k : Nat) : Prop :=
  ∀ i, i < k → readBytes mem (ent + 8 * i) 8 = some (wordsOf [stage1Word bs i])

/-- **Every write the loop made is inside the entry array.**  The loop writes only
at `ent + 8 * i` for a block index below the document's block count, so every byte
outside `(ent, 8 * blocks)` is the caller's; this is the loop's frame obligation,
not the tail's. -/
def EntryFrame (mem0 mem : Mem) (ent blocks : Nat) : Prop :=
  UnchangedOutside mem0 mem [(ent, 8 * blocks)]

/-- **Per-slot reads compose into a prefix read.** -/
theorem readBytes_slots_wordsOf (m : Mem) (ent : Nat) (bs : List UInt8) :
    ∀ (k : Nat),
      (∀ i, i < k → readBytes m (ent + 8 * i) 8 = some (wordsOf [stage1Word bs i])) →
      readBytes m ent (8 * k) =
        some (wordsOf ((List.range k).map (stage1Word bs)))
  | 0, _ => rfl
  | k + 1, hslot => by
      have hpre := readBytes_slots_wordsOf m ent bs k (fun i hi => hslot i (by omega))
      have hlast := hslot k (by omega)
      have hcat := readBytes_append m (8 * k) ent
        (wordsOf ((List.range k).map (stage1Word bs))) 8 (wordsOf [stage1Word bs k])
        hpre hlast
      rw [show 8 * (k + 1) = 8 * k + 8 from by omega, hcat]
      have hstep : wordsOf (List.map (stage1Word bs) (List.range (k + 1))) =
          wordsOf (List.map (stage1Word bs) (List.range k)) ++
            wordsOf [stage1Word bs k] := by
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          wordsOf_append]
      rw [hstep]

/-- **The loop's prefix, as one read.**  `EntryPrefix` at `k` is one read of
`8 * k` bytes holding the model's first `k` words. -/
theorem entryPrefix_read {mem : Mem} {ent : Nat} {bs : List UInt8} {k : Nat}
    (hk : k ≤ blocksOf bs.length) (h : EntryPrefix mem ent bs k) :
    readBytes mem ent (8 * k) = some (wordsOf ((stage1Words bs).take k)) := by
  rw [stage1Words_take, Nat.min_eq_left hk]
  exact readBytes_slots_wordsOf mem ent bs k h

/-- **The entry array on the aligned arm.**  No word is the peel's, so the loop's
own prefix at the document's block count is the post's whole array. -/
theorem entryWords_of_prefix_full {mem : Mem} {ent : Nat} {bs : List UInt8}
    (h : EntryPrefix mem ent bs (blocksOf bs.length)) :
    readBytes mem ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) := by
  rw [entryPrefix_read (Nat.le_refl _) h,
    List.take_of_length_le (by simp [stage1Words_length])]

/-! ### The peel's word at the model

The peel's slot is the document's last block, and `%and` is its remainder: the
`limMask` the store applies is the model's, so only `%or135` remains the loop's. -/

/-- **The peel's clamp index is the model's.**  `%and` is the length's remainder
and `%shr` its whole-block count, so `bs.length - 64 * shr` is `%and`. -/
theorem limMask_tail_eq (bs : List UInt8) (n andv shr : BitVec 64)
    (hn : n.toNat = bs.length) (hshr : shr = n >>> 6)
    (hand : andv = n &&& 0x000000000000003f#64) :
    limMask (bs.length - 64 * shr.toNat) = limMask andv.toNat := by
  have hshrn : shr.toNat = n.toNat / 64 := by rw [hshr, ushr_six_toNat]
  have handn : andv.toNat = n.toNat % 64 := by rw [hand, and_sixtythree_toNat]
  have htail : bs.length - 64 * shr.toNat = andv.toNat := by
    rw [← hn, hshrn, handn]
    have hdm := Nat.div_add_mod n.toNat 64
    omega
  rw [htail]

/-- **The peel's `%or135`, at the model's last block.**  The mask composition the
loop's carried words feed the peel; the peel's own `if_then103_store_model` gives
everything but this, and the block cannot supply it, because it is a fact about the
state the loop hands over. -/
def PeelWordAtModel (or135 : BitVec 64) (bs : List UInt8) (i : Nat) : Prop :=
  or135 = entryMask64 (blockLo (padded bs) i) (blockHi (padded bs) i)
    (classCarryAt (padded bs) ⟨false, false⟩ (64 * i)) (stage1PrevS bs i)

/-- **The peel's stored word is the model's.**  `if_then103_store_model` gives the
slot's word as `%or135 &&& limMask %and`; the clamp's index is the model's, and
`%or135` is the loop's (`PeelWordAtModel`). -/
theorem if_then103_store_stage1Word
    (n : BitVec 64) (b : Nat) (bs136 bs137 : List UInt8)
    (ascii : List (BitVec 64)) (st0 st9 st15 prevS andv shr : BitVec 64)
    (ent : Nat) (conv prevAscii : BitVec 32) (mem : Mem) (bs : List UInt8)
    (hn : n.toNat = bs.length) (hshr : shr = n >>> 6)
    (hand : andv = n &&& 0x000000000000003f#64)
    (hor : PeelWordAtModel
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).or135 bs shr.toNat) :
    readBytes
      (writeBytes mem
        (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
          prevAscii).arrayidx
        (natToBytes
          (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
            prevAscii).and137.toNat 8))
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
        prevAscii).arrayidx 8 =
      some (wordsOf [stage1Word bs shr.toNat]) := by
  have hword :
      (ifThen103Values n b bs136 bs137 ascii st0 st9 st15 prevS andv shr ent conv
          prevAscii).or135 &&& limMask andv.toNat =
        stage1Word bs shr.toNat := by
    show _ = entryMask64 (blockLo (padded bs) shr.toNat) (blockHi (padded bs) shr.toNat)
        (classCarryAt (padded bs) ⟨false, false⟩ (64 * shr.toNat))
        (stage1PrevS bs shr.toNat) &&& limMask (bs.length - 64 * shr.toNat)
    rw [hor, limMask_tail_eq bs n andv shr hn hshr hand]
  rw [if_then103_store_model, hword]

/-! ### The entry array, composed

The prefix read plus the peel's slot read is the whole array: `shr + 1` blocks. -/

/-- **The entry array at the peel's memory.**  Below the slot the read is the
loop's prefix (the store is above it), the slot is the peel's word, and `wordsOf`
distributes over the append. -/
theorem entryWords_of_prefix_store {m : Mem} {ent shr : Nat} {bs : List UInt8}
    {stored : List UInt8}
    (hsucc : shr + 1 = blocksOf bs.length)
    (hprefix : readBytes m ent (8 * shr) =
      some (wordsOf ((stage1Words bs).take shr)))
    (hslot : readBytes (writeBytes m (ent + 8 * shr) stored) (ent + 8 * shr) 8 =
      some (wordsOf [stage1Word bs shr])) :
    readBytes (writeBytes m (ent + 8 * shr) stored) ent (8 * blocksOf bs.length) =
      some (wordsOf (stage1Words bs)) := by
  have hbelow : readBytes (writeBytes m (ent + 8 * shr) stored) ent (8 * shr) =
      readBytes m ent (8 * shr) :=
    readBytes_writeBytes_below m stored (8 * shr) ent (ent + 8 * shr) (by omega)
  have hcat := readBytes_append (writeBytes m (ent + 8 * shr) stored) (8 * shr) ent
    (wordsOf ((stage1Words bs).take shr)) 8 (wordsOf [stage1Word bs shr])
    (by rw [hbelow]; exact hprefix) hslot
  have hwords : wordsOf ((stage1Words bs).take shr) ++
      wordsOf [stage1Word bs shr] = wordsOf (stage1Words bs) := by
    have htake : (stage1Words bs).take shr = (List.range shr).map (stage1Word bs) := by
      rw [stage1Words_take, Nat.min_eq_left (by omega)]
    have hfull : wordsOf (stage1Words bs) =
        wordsOf ((List.range shr).map (stage1Word bs)) ++
          natToBytes (stage1Word bs shr).toNat 8 := by
      unfold stage1Words
      rw [show blocksOf bs.length = shr + 1 from hsucc.symm, List.range_succ,
        List.map_append, List.map_cons, List.map_nil, wordsOf_append,
        wordsOf_singleton]
    rw [htake, hfull, wordsOf_singleton]
  rw [show 8 * blocksOf bs.length = 8 * shr + 8 from by omega, hcat, hwords]

/-! ### The escape list's clauses, from the record

`EscapeReach` is the record's `post` read as one predicate.  These are the post's
three escape clauses at it, and the stream prefix it does not state. -/

/-- **The escape record's clauses at the block's post.**  The count is the caller's
plus the block's positions, the segment is the position word's, and the carry's
sixteen bytes are a flag pair.  `position` is lifted to the document by
`blockAddr`, which is where the record states it. -/
theorem escapeClauses_of_reach {blk0 : BitVec 64} {xp nxp xcarry xn0 : Nat}
    {position ps0 : List Nat} {opened ppar : Bool} {mem M : Mem}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar) mem M)
    (hprefix : readBytes M xp (4 * xn0) = some (positionsBytes 4 ps0)) :
    readBytes M nxp 8 = some (wordBytes 8 (xn0 + position.length)) ∧
    readBytes M xp (4 * (xn0 + position.length)) =
      some (positionsBytes 4 (ps0 ++ position.map fun k => blockAddr blk0 + k)) ∧
    (∃ (st : ClassState) (prevb prevs : Bool), carryPair M xcarry st prevb prevs) := by
  obtain ⟨hcount, hseg, hcarry, _hhas, _hframe⟩ := hreach
  refine ⟨hcount, ?_, ⟨⟨false, opened && ppar⟩, opened, ppar, hcarry, rfl⟩⟩
  have hcat := readBytes_append M (4 * xn0) xp (positionsBytes 4 ps0)
    (4 * position.length)
    (positionsBytes 4 (position.map fun k => blockAddr blk0 + k)) hprefix hseg
  rw [show 4 * (xn0 + position.length) = 4 * xn0 + 4 * position.length from by omega,
    hcat, positionsBytes_append]

/-- **What the record states about the stream, with no caller fact.**  The count,
the segment this call wrote (at the cursor, not from the stream's base) and the
carry pair.  This is the record's own content; the post's whole-stream read adds
the prefix below the cursor, which is `escapeClauses_of_reach`'s hypothesis. -/
theorem escapeSegment_of_reach {blk0 : BitVec 64} {xp nxp xcarry xn0 : Nat}
    {position : List Nat} {opened ppar : Bool} {mem M : Mem}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar) mem M) :
    readBytes M nxp 8 = some (wordBytes 8 (xn0 + position.length)) ∧
    readBytes M (xp + 4 * xn0) (4 * position.length) =
      some (positionsBytes 4 (position.map fun k => blockAddr blk0 + k)) ∧
    (∃ (st : ClassState) (prevb prevs : Bool), carryPair M xcarry st prevb prevs) := by
  obtain ⟨hcount, hseg, hcarry, _hhas, _hframe⟩ := hreach
  exact ⟨hcount, hseg, ⟨⟨false, opened && ppar⟩, opened, ppar, hcarry, rfl⟩⟩

/-- **The stream's prefix is the caller's**, not the record's.  The record states
the segment this call wrote; the post reads the whole stream.  The record's frame
names its stream region from `xp`, so it says nothing about the bytes below the
cursor, and this is the fact a call site has to supply from its own staging. -/
def StreamPrefix (mem : Mem) (xp xn : Nat) (ps : List Nat) : Prop :=
  readBytes mem xp (4 * xn) = some (positionsBytes 4 ps)

/-! ### The four-region frame

The post's region list is the entry array and the call's three regions; the loop's
frame, the peel's store and the call's frame compose to it. -/

/-- The post's four regions, as the entry array consed onto the call's three. -/
theorem escapeCallWriteRegions_eq_post (ent blocks xp nxp xcarry nxp' : Nat) :
    escapeCallWriteRegions ent blocks xp nxp xcarry nxp' =
      [(ent, 8 * blocks), (xp, 4 * (nxp' + batchReserve)), (nxp, 8), (xcarry, 16)] :=
  rfl

/-- **The four-region frame widens with the stream's count.**  A frame over the
list at `xnA` is a frame at `xnB ≥ xnA`: the stream region at `xnB` contains the
one at `xnA`, and the other three regions are the same pairs. -/
theorem escapeCallWriteRegions_widen {mem0 m : Mem} {ent blocks xp nxp xcarry xnA xnB : Nat}
    (h : UnchangedOutside mem0 m (escapeCallWriteRegions ent blocks xp nxp xcarry xnA))
    (hxn : xnA ≤ xnB) :
    UnchangedOutside mem0 m (escapeCallWriteRegions ent blocks xp nxp xcarry xnB) :=
  UnchangedOutside.widen h (fun a ha r hr => by
    simp only [escapeCallWriteRegions, escapeCallRegions, List.mem_cons,
      List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl | rfl | rfl
    · exact ha (ent, 8 * blocks)
        (by simp [escapeCallWriteRegions, escapeCallRegions])
    · exact fun hc => ha (xp, 4 * (xnB + batchReserve))
        (by simp [escapeCallWriteRegions, escapeCallRegions]) ⟨hc.1, by omega⟩
    · exact ha (nxp, 8) (by simp [escapeCallWriteRegions, escapeCallRegions])
    · exact ha (xcarry, 16) (by simp [escapeCallWriteRegions, escapeCallRegions]))

/-- **The peel's store is inside the entry array**, so it leaves the loop's frame
in place. -/
theorem peelStore_frame {mem0 mem : Mem} {ent blocks shr : Nat} {word : List UInt8}
    (hframe : EntryFrame mem0 mem ent blocks) (hsucc : shr + 1 = blocks)
    (hwlen : word.length = 8) :
    EntryFrame mem0 (writeBytes mem (ent + 8 * shr) word) ent blocks :=
  frame_write_inside hframe (by omega) (by omega)

/-- **The four-region frame, across the peel's store and the call.**  The frame is
over the four regions at the count the call was entered with, the peel's store is
inside the entry array, and the call's three regions are the tail of the post's
list — so the conclusion is the same list at the count the call left. -/
theorem frame_of_peel_call {mem0 memL M : Mem} {ent blocks shr : Nat}
    {word : List UInt8} {xp nxp xcarry xnA xnB : Nat}
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent blocks xp nxp xcarry xnA))
    (hsucc : shr + 1 = blocks)
    (hwlen : word.length = 8)
    (hcall : UnchangedOutside (writeBytes memL (ent + 8 * shr) word) M
      (escapeCallRegions xp nxp xcarry xnB))
    (hxn : xnA ≤ xnB) :
    UnchangedOutside mem0 M
      (escapeCallWriteRegions ent blocks xp nxp xcarry xnB) := by
  have hwide := escapeCallWriteRegions_widen hframe hxn
  have hstore : UnchangedOutside mem0 (writeBytes memL (ent + 8 * shr) word)
      (escapeCallWriteRegions ent blocks xp nxp xcarry xnB) :=
    frame_write_in_region hwide (by omega) (by omega)
  exact frame_comp hstore hcall (fun r hr => List.mem_cons_of_mem _ hr)

/-! ### The entry array across the call

The call may write only its three regions; the entry array is separate from each,
so the array the peel left is the array the post reads.  The separations are the
staging's, restated at the extent the record's frame names. -/

/-- **The call leaves the entry array alone.**  `escapeReach_keepsEntry` at the
staging's separations: the array the peel wrote is the array the post reads. -/
theorem entryWords_kept_by_escape {blk0 : BitVec 64} {xp nxp xcarry xn0 : Nat}
    {position : List Nat} {carryBytes : List UInt8} {mem M : Mem} {ent blocks : Nat}
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position carryBytes mem M)
    (hentXp : ent + 8 * blocks ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)
    (hentXn : ent + 8 * blocks ≤ nxp ∨ nxp + 8 ≤ ent)
    (hentCarry : ent + 8 * blocks ≤ xcarry ∨ xcarry + 16 ≤ ent) :
    readBytes M ent (8 * blocks) = readBytes mem ent (8 * blocks) :=
  escapeReach_keepsEntry hreach hentXp hentXn hentCarry

/-! ### The positions fit in one block

The escape record's frame names the touched extent; the staging separates at the
capacity, whose stream term is `64 * blocks` entries wide.  A block's escape
positions are a filter of its sixty-four lanes, so its list is at most sixty-four
long — the one bound the conversion needs. -/

/-- A block's escape positions number at most its sixty-four lanes. -/
theorem escapePositionsFrom_block_length_le (lo hi : Block32) (st : ClassState) :
    (escapePositionsFrom (block64 lo hi) st).length ≤ 64 := by
  unfold escapePositionsFrom
  calc ((List.range (block64 lo hi).length).filter _).length
      ≤ (List.range (block64 lo hi).length).length := List.length_filter_le _ _
    _ = (block64 lo hi).length := List.length_range
    _ = 64 := by simp [block64]

/-! ### The escape arm's memory conjuncts

The merge's escape branch: the peel's store, then the call.  Assembled, these are
the post's memory clauses at the call's outcome, with the loop's two residuals and
the caller's stream prefix as the only hypotheses about anything before the peel. -/

/-- **The escape arm's memory.**  The entry array (prefix, peel slot, kept across
the call), the count, the stream, the carry pair, and the four-region frame.

The run's frame is taken at the count the call was entered with — the count the
count's slot holds — and the call's own segment widens it to the count it left.
`shr` is the peel's slot index and `w` the word it stores, so `hslot` is
`if_then103_store_stage1Word`'s conclusion at `v.and137`; the array's separations
from the call's three regions are the staging's, at the extent the record's frame
*touched* rather than at a further block's capacity. -/
theorem escape_arm_memory {blk0 : BitVec 64} {bs : List UInt8}
    {ent shr xn0 xp nxp xcarry : Nat} {mem0 memL M : Mem} {w : BitVec 64}
    {position ps0 : List Nat} {opened ppar : Bool}
    (hframe : UnchangedOutside mem0 memL
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry xn0))
    (hprefix : EntryPrefix memL ent bs shr)
    (hsucc : shr + 1 = blocksOf bs.length)
    (hslot : readBytes
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) (ent + 8 * shr) 8 =
        some (wordsOf [stage1Word bs shr]))
    (hreach : EscapeReach blk0 xp nxp xcarry xn0 position
      (flagBytes opened ++ flagBytes ppar)
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) M)
    (hstream : StreamPrefix M xp xn0 ps0)
    (hxpSep : ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn0 + position.length + batchReserve) ≤ ent)
    (hxnSep : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent)
    (hxcSep : ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent) :
    readBytes M ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) ∧
    readBytes M nxp 8 = some (wordBytes 8 (xn0 + position.length)) ∧
    readBytes M xp (4 * (xn0 + position.length)) =
      some (positionsBytes 4 (ps0 ++ position.map fun k => blockAddr blk0 + k)) ∧
    (∃ (st : ClassState) (prevb prevs : Bool), carryPair M xcarry st prevb prevs) ∧
    UnchangedOutside mem0 M
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry
        (xn0 + position.length)) := by
  have hentP : readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8))
      ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) :=
    entryWords_of_prefix_store hsucc
      (entryPrefix_read (by omega) hprefix) hslot
  have hentM := entryWords_kept_by_escape hreach hxpSep hxnSep hxcSep
  obtain ⟨hcount, hstreamOut, hpair⟩ := escapeClauses_of_reach hreach hstream
  exact ⟨by rw [hentM]; exact hentP, hcount, hstreamOut, hpair,
    frame_of_peel_call hframe hsucc (natToBytes_length w.toNat 8)
      (escapeReach_callRegions hreach) (by omega)⟩

/-! ### The merge's other branch's memory conjuncts

The merge's `%arm & 2 = 0` branch: the peel's store is the run's last write.  The
count, the carry and the staged capacity read through the store from the caller,
and the frame is the loop's, widened to the post's four regions. -/

/-- **The peel-only arm's memory.**  The entry array (prefix and slot), the count,
the staged stream extent and the carry pair — all read through the peel's store at
the caller's values — and the four-region frame, at the post's own witness. -/
theorem peel_arm_memory {bs : List UInt8} {ent shr xn xp nxp xcarry : Nat}
    {mem0 memL : Mem} {w : BitVec 64} {nxp' : Nat} {staged : List UInt8}
    (hloopFrame : EntryFrame mem0 memL ent (blocksOf bs.length))
    (hprefix : EntryPrefix memL ent bs shr)
    (hsucc : shr + 1 = blocksOf bs.length)
    (hslot : readBytes
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) (ent + 8 * shr) 8 =
        some (wordsOf [stage1Word bs shr]))
    (hcount : readBytes mem0 nxp 8 = some (wordBytes 8 xn))
    (hstaged : readBytes mem0 xp
      (4 * (xn + 64 * blocksOf bs.length + batchReserve)) = some staged)
    (hflags : readBytes mem0 xcarry 16 =
      some (flagBytes false ++ flagBytes false))
    (hxpSep : ent + 8 * blocksOf bs.length ≤ xp ∨
      xp + 4 * (xn + 64 * blocksOf bs.length + batchReserve) ≤ ent)
    (hxnSep : ent + 8 * blocksOf bs.length ≤ nxp ∨ nxp + 8 ≤ ent)
    (hxcSep : ent + 8 * blocksOf bs.length ≤ xcarry ∨ xcarry + 16 ≤ ent) :
    readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8))
        ent (8 * blocksOf bs.length) = some (wordsOf (stage1Words bs)) ∧
    readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) nxp 8 =
      some (wordBytes 8 xn) ∧
    readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) xp
        (4 * (xn + 64 * blocksOf bs.length + batchReserve)) = some staged ∧
    readBytes (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) xcarry 16 =
      some (flagBytes false ++ flagBytes false) ∧
    UnchangedOutside mem0 (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8))
      (escapeCallWriteRegions ent (blocksOf bs.length) xp nxp xcarry nxp') := by
  have hpeelFrame : EntryFrame mem0
      (writeBytes memL (ent + 8 * shr) (natToBytes w.toNat 8)) ent
      (blocksOf bs.length) :=
    peelStore_frame hloopFrame hsucc (natToBytes_length w.toNat 8)
  refine ⟨?_, ?_, ?_, ?_, frame_mono hpeelFrame (fun r hr => by
    simp only [escapeCallWriteRegions, List.mem_cons, List.not_mem_nil,
      or_false] at hr ⊢
    exact Or.inl hr)⟩
  · exact entryWords_of_prefix_store hsucc (entryPrefix_read (by omega) hprefix) hslot
  · rw [readBytes_frame_single hpeelFrame hxnSep]; exact hcount
  · rw [readBytes_frame_single hpeelFrame hxpSep]; exact hstaged
  · rw [readBytes_frame_single hpeelFrame hxcSep]; exact hflags

/-! ### Axiom footprints

No statement carries `sorryAx`.  The region list, the reads and the store-free
frame moves report only `propext` and `Quot.sound` — `frame_mono`, `frame_comp`,
`readBytes_frame`, `readBytes_frame_single`, `entryWords_of_prefix_full`,
`entryWords_of_prefix_store`, `escapeClauses_of_reach`,
`escapeCallWriteRegions_widen`, `entryWords_kept_by_escape`
(`escapeCallWriteRegions_eq_post`, `EntryPrefix`, `EntryFrame` and `StreamPrefix`
are stated by nothing at all).  `Classical.choice` accompanies the address
arithmetic the store statements discharge with `omega` (`frame_write_inside`,
`frame_write_in_region`) and the peel's value projection (`limMask_tail_eq`,
`if_then103_store_stage1Word`) with the statements that rest on them
(`peelStore_frame`, `frame_of_peel_call`, `escape_arm_memory`,
`peel_arm_memory`) — the same carrier `JsonS1BlocksCompose` reports for the same
value structure. -/
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.frame_mono
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.frame_comp
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.frame_write_inside
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.frame_write_in_region
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.readBytes_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.readBytes_frame_single
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.wordsOf_append
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.wordsOf_singleton
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.positionsBytes_append
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.EntryPrefix
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.EntryFrame
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.readBytes_slots_wordsOf
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.entryPrefix_read
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.entryWords_of_prefix_full
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.limMask_tail_eq
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.PeelWordAtModel
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.if_then103_store_stage1Word
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.entryWords_of_prefix_store
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escapeClauses_of_reach
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escapeSegment_of_reach
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.StreamPrefix
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escapeCallWriteRegions_eq_post
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escapeCallWriteRegions_widen
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.peelStore_frame
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.frame_of_peel_call
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.entryWords_kept_by_escape
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escapePositionsFrom_block_length_le
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.escape_arm_memory
#print axioms LeanLLVM.Refinement.JsonS1BlocksRecordFrame.peel_arm_memory

end LeanLLVM.Refinement.JsonS1BlocksRecordFrame
